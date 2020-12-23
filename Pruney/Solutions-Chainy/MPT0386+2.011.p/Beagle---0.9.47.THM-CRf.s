%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:57:10 EST 2020

% Result     : Theorem 2.08s
% Output     : CNFRefutation 2.08s
% Verified   : 
% Statistics : Number of formulae       :   55 ( 157 expanded)
%              Number of leaves         :   21 (  62 expanded)
%              Depth                    :   10
%              Number of atoms          :   72 ( 290 expanded)
%              Number of equality atoms :   16 (  46 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k4_xboole_0 > #nlpp > k1_setfam_1 > k1_xboole_0 > #skF_7 > #skF_3 > #skF_6 > #skF_2 > #skF_1 > #skF_5 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_66,negated_conjecture,(
    ~ ! [A,B] :
        ( r2_hidden(A,B)
       => r1_tarski(k1_setfam_1(B),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_setfam_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_61,axiom,(
    ! [A,B] :
      ( ( A != k1_xboole_0
       => ( B = k1_setfam_1(A)
        <=> ! [C] :
              ( r2_hidden(C,B)
            <=> ! [D] :
                  ( r2_hidden(D,A)
                 => r2_hidden(C,D) ) ) ) )
      & ( A = k1_xboole_0
       => ( B = k1_setfam_1(A)
        <=> B = k1_xboole_0 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_setfam_1)).

tff(f_36,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_38,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_42,axiom,(
    ! [A] :
      ( r1_tarski(A,k1_xboole_0)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).

tff(c_38,plain,(
    ~ r1_tarski(k1_setfam_1('#skF_7'),'#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_140,plain,(
    ! [A_45,B_46] :
      ( ~ r2_hidden('#skF_1'(A_45,B_46),B_46)
      | r1_tarski(A_45,B_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_145,plain,(
    ! [A_1] : r1_tarski(A_1,A_1) ),
    inference(resolution,[status(thm)],[c_6,c_140])).

tff(c_40,plain,(
    r2_hidden('#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_245,plain,(
    ! [C_58,D_59,A_60] :
      ( r2_hidden(C_58,D_59)
      | ~ r2_hidden(D_59,A_60)
      | ~ r2_hidden(C_58,k1_setfam_1(A_60))
      | k1_xboole_0 = A_60 ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_254,plain,(
    ! [C_58] :
      ( r2_hidden(C_58,'#skF_6')
      | ~ r2_hidden(C_58,k1_setfam_1('#skF_7'))
      | k1_xboole_0 = '#skF_7' ) ),
    inference(resolution,[status(thm)],[c_40,c_245])).

tff(c_255,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(splitLeft,[status(thm)],[c_254])).

tff(c_154,plain,(
    ! [A_50] : r1_tarski(A_50,A_50) ),
    inference(resolution,[status(thm)],[c_6,c_140])).

tff(c_10,plain,(
    ! [A_6,B_7] :
      ( k4_xboole_0(A_6,B_7) = k1_xboole_0
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_165,plain,(
    ! [A_51] : k4_xboole_0(A_51,A_51) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_154,c_10])).

tff(c_12,plain,(
    ! [A_8,B_9] : r1_tarski(k4_xboole_0(A_8,B_9),A_8) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_182,plain,(
    ! [A_51] : r1_tarski(k1_xboole_0,A_51) ),
    inference(superposition,[status(thm),theory(equality)],[c_165,c_12])).

tff(c_146,plain,(
    ! [C_47,B_48,A_49] :
      ( r2_hidden(C_47,B_48)
      | ~ r2_hidden(C_47,A_49)
      | ~ r1_tarski(A_49,B_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_209,plain,(
    ! [B_53] :
      ( r2_hidden('#skF_6',B_53)
      | ~ r1_tarski('#skF_7',B_53) ) ),
    inference(resolution,[status(thm)],[c_40,c_146])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_213,plain,(
    ! [B_54,B_55] :
      ( r2_hidden('#skF_6',B_54)
      | ~ r1_tarski(B_55,B_54)
      | ~ r1_tarski('#skF_7',B_55) ) ),
    inference(resolution,[status(thm)],[c_209,c_2])).

tff(c_222,plain,(
    ! [A_51] :
      ( r2_hidden('#skF_6',A_51)
      | ~ r1_tarski('#skF_7',k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_182,c_213])).

tff(c_226,plain,(
    ~ r1_tarski('#skF_7',k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_222])).

tff(c_258,plain,(
    ~ r1_tarski('#skF_7','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_255,c_226])).

tff(c_271,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_145,c_258])).

tff(c_274,plain,(
    ! [C_61] :
      ( r2_hidden(C_61,'#skF_6')
      | ~ r2_hidden(C_61,k1_setfam_1('#skF_7')) ) ),
    inference(splitRight,[status(thm)],[c_254])).

tff(c_300,plain,(
    ! [B_64] :
      ( r2_hidden('#skF_1'(k1_setfam_1('#skF_7'),B_64),'#skF_6')
      | r1_tarski(k1_setfam_1('#skF_7'),B_64) ) ),
    inference(resolution,[status(thm)],[c_6,c_274])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_308,plain,(
    r1_tarski(k1_setfam_1('#skF_7'),'#skF_6') ),
    inference(resolution,[status(thm)],[c_300,c_4])).

tff(c_314,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_38,c_308])).

tff(c_316,plain,(
    r1_tarski('#skF_7',k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_222])).

tff(c_14,plain,(
    ! [A_10] :
      ( k1_xboole_0 = A_10
      | ~ r1_tarski(A_10,k1_xboole_0) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_345,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(resolution,[status(thm)],[c_316,c_14])).

tff(c_348,plain,(
    ! [A_51] : r1_tarski('#skF_7',A_51) ),
    inference(demodulation,[status(thm),theory(equality)],[c_345,c_182])).

tff(c_36,plain,(
    k1_setfam_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_357,plain,(
    k1_setfam_1('#skF_7') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_345,c_345,c_36])).

tff(c_364,plain,(
    ~ r1_tarski('#skF_7','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_357,c_38])).

tff(c_371,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_348,c_364])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n025.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 10:55:35 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.08/1.27  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.08/1.28  
% 2.08/1.28  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.08/1.28  %$ r2_hidden > r1_tarski > k4_xboole_0 > #nlpp > k1_setfam_1 > k1_xboole_0 > #skF_7 > #skF_3 > #skF_6 > #skF_2 > #skF_1 > #skF_5 > #skF_4
% 2.08/1.28  
% 2.08/1.28  %Foreground sorts:
% 2.08/1.28  
% 2.08/1.28  
% 2.08/1.28  %Background operators:
% 2.08/1.28  
% 2.08/1.28  
% 2.08/1.28  %Foreground operators:
% 2.08/1.28  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.08/1.28  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.08/1.28  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.08/1.28  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.08/1.28  tff('#skF_7', type, '#skF_7': $i).
% 2.08/1.28  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.08/1.28  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.08/1.28  tff('#skF_6', type, '#skF_6': $i).
% 2.08/1.28  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.08/1.28  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.08/1.28  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.08/1.28  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.08/1.28  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 2.08/1.28  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 2.08/1.28  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.08/1.28  
% 2.08/1.29  tff(f_66, negated_conjecture, ~(![A, B]: (r2_hidden(A, B) => r1_tarski(k1_setfam_1(B), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_setfam_1)).
% 2.08/1.29  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 2.08/1.29  tff(f_61, axiom, (![A, B]: ((~(A = k1_xboole_0) => ((B = k1_setfam_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (![D]: (r2_hidden(D, A) => r2_hidden(C, D))))))) & ((A = k1_xboole_0) => ((B = k1_setfam_1(A)) <=> (B = k1_xboole_0))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_setfam_1)).
% 2.08/1.29  tff(f_36, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 2.08/1.29  tff(f_38, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 2.08/1.29  tff(f_42, axiom, (![A]: (r1_tarski(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_1)).
% 2.08/1.29  tff(c_38, plain, (~r1_tarski(k1_setfam_1('#skF_7'), '#skF_6')), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.08/1.29  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.08/1.29  tff(c_140, plain, (![A_45, B_46]: (~r2_hidden('#skF_1'(A_45, B_46), B_46) | r1_tarski(A_45, B_46))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.08/1.29  tff(c_145, plain, (![A_1]: (r1_tarski(A_1, A_1))), inference(resolution, [status(thm)], [c_6, c_140])).
% 2.08/1.29  tff(c_40, plain, (r2_hidden('#skF_6', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.08/1.29  tff(c_245, plain, (![C_58, D_59, A_60]: (r2_hidden(C_58, D_59) | ~r2_hidden(D_59, A_60) | ~r2_hidden(C_58, k1_setfam_1(A_60)) | k1_xboole_0=A_60)), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.08/1.29  tff(c_254, plain, (![C_58]: (r2_hidden(C_58, '#skF_6') | ~r2_hidden(C_58, k1_setfam_1('#skF_7')) | k1_xboole_0='#skF_7')), inference(resolution, [status(thm)], [c_40, c_245])).
% 2.08/1.29  tff(c_255, plain, (k1_xboole_0='#skF_7'), inference(splitLeft, [status(thm)], [c_254])).
% 2.08/1.29  tff(c_154, plain, (![A_50]: (r1_tarski(A_50, A_50))), inference(resolution, [status(thm)], [c_6, c_140])).
% 2.08/1.29  tff(c_10, plain, (![A_6, B_7]: (k4_xboole_0(A_6, B_7)=k1_xboole_0 | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.08/1.29  tff(c_165, plain, (![A_51]: (k4_xboole_0(A_51, A_51)=k1_xboole_0)), inference(resolution, [status(thm)], [c_154, c_10])).
% 2.08/1.29  tff(c_12, plain, (![A_8, B_9]: (r1_tarski(k4_xboole_0(A_8, B_9), A_8))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.08/1.29  tff(c_182, plain, (![A_51]: (r1_tarski(k1_xboole_0, A_51))), inference(superposition, [status(thm), theory('equality')], [c_165, c_12])).
% 2.08/1.29  tff(c_146, plain, (![C_47, B_48, A_49]: (r2_hidden(C_47, B_48) | ~r2_hidden(C_47, A_49) | ~r1_tarski(A_49, B_48))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.08/1.29  tff(c_209, plain, (![B_53]: (r2_hidden('#skF_6', B_53) | ~r1_tarski('#skF_7', B_53))), inference(resolution, [status(thm)], [c_40, c_146])).
% 2.08/1.29  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.08/1.29  tff(c_213, plain, (![B_54, B_55]: (r2_hidden('#skF_6', B_54) | ~r1_tarski(B_55, B_54) | ~r1_tarski('#skF_7', B_55))), inference(resolution, [status(thm)], [c_209, c_2])).
% 2.08/1.29  tff(c_222, plain, (![A_51]: (r2_hidden('#skF_6', A_51) | ~r1_tarski('#skF_7', k1_xboole_0))), inference(resolution, [status(thm)], [c_182, c_213])).
% 2.08/1.29  tff(c_226, plain, (~r1_tarski('#skF_7', k1_xboole_0)), inference(splitLeft, [status(thm)], [c_222])).
% 2.08/1.29  tff(c_258, plain, (~r1_tarski('#skF_7', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_255, c_226])).
% 2.08/1.29  tff(c_271, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_145, c_258])).
% 2.08/1.29  tff(c_274, plain, (![C_61]: (r2_hidden(C_61, '#skF_6') | ~r2_hidden(C_61, k1_setfam_1('#skF_7')))), inference(splitRight, [status(thm)], [c_254])).
% 2.08/1.29  tff(c_300, plain, (![B_64]: (r2_hidden('#skF_1'(k1_setfam_1('#skF_7'), B_64), '#skF_6') | r1_tarski(k1_setfam_1('#skF_7'), B_64))), inference(resolution, [status(thm)], [c_6, c_274])).
% 2.08/1.29  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.08/1.29  tff(c_308, plain, (r1_tarski(k1_setfam_1('#skF_7'), '#skF_6')), inference(resolution, [status(thm)], [c_300, c_4])).
% 2.08/1.29  tff(c_314, plain, $false, inference(negUnitSimplification, [status(thm)], [c_38, c_38, c_308])).
% 2.08/1.29  tff(c_316, plain, (r1_tarski('#skF_7', k1_xboole_0)), inference(splitRight, [status(thm)], [c_222])).
% 2.08/1.29  tff(c_14, plain, (![A_10]: (k1_xboole_0=A_10 | ~r1_tarski(A_10, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.08/1.29  tff(c_345, plain, (k1_xboole_0='#skF_7'), inference(resolution, [status(thm)], [c_316, c_14])).
% 2.08/1.29  tff(c_348, plain, (![A_51]: (r1_tarski('#skF_7', A_51))), inference(demodulation, [status(thm), theory('equality')], [c_345, c_182])).
% 2.08/1.29  tff(c_36, plain, (k1_setfam_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.08/1.29  tff(c_357, plain, (k1_setfam_1('#skF_7')='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_345, c_345, c_36])).
% 2.08/1.29  tff(c_364, plain, (~r1_tarski('#skF_7', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_357, c_38])).
% 2.08/1.29  tff(c_371, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_348, c_364])).
% 2.08/1.29  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.08/1.29  
% 2.08/1.29  Inference rules
% 2.08/1.29  ----------------------
% 2.08/1.29  #Ref     : 0
% 2.08/1.29  #Sup     : 71
% 2.08/1.29  #Fact    : 0
% 2.08/1.29  #Define  : 0
% 2.08/1.29  #Split   : 3
% 2.08/1.29  #Chain   : 0
% 2.08/1.29  #Close   : 0
% 2.08/1.29  
% 2.08/1.29  Ordering : KBO
% 2.08/1.29  
% 2.08/1.29  Simplification rules
% 2.08/1.29  ----------------------
% 2.08/1.29  #Subsume      : 7
% 2.08/1.29  #Demod        : 59
% 2.08/1.29  #Tautology    : 40
% 2.08/1.29  #SimpNegUnit  : 1
% 2.08/1.29  #BackRed      : 26
% 2.08/1.29  
% 2.08/1.29  #Partial instantiations: 0
% 2.08/1.29  #Strategies tried      : 1
% 2.08/1.29  
% 2.08/1.29  Timing (in seconds)
% 2.08/1.29  ----------------------
% 2.08/1.30  Preprocessing        : 0.29
% 2.08/1.30  Parsing              : 0.15
% 2.08/1.30  CNF conversion       : 0.02
% 2.08/1.30  Main loop            : 0.24
% 2.08/1.30  Inferencing          : 0.08
% 2.08/1.30  Reduction            : 0.07
% 2.08/1.30  Demodulation         : 0.05
% 2.08/1.30  BG Simplification    : 0.02
% 2.08/1.30  Subsumption          : 0.05
% 2.08/1.30  Abstraction          : 0.01
% 2.08/1.30  MUC search           : 0.00
% 2.08/1.30  Cooper               : 0.00
% 2.08/1.30  Total                : 0.55
% 2.08/1.30  Index Insertion      : 0.00
% 2.08/1.30  Index Deletion       : 0.00
% 2.08/1.30  Index Matching       : 0.00
% 2.08/1.30  BG Taut test         : 0.00
%------------------------------------------------------------------------------
