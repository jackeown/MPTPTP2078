%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:57:10 EST 2020

% Result     : Theorem 1.87s
% Output     : CNFRefutation 2.09s
% Verified   : 
% Statistics : Number of formulae       :   51 ( 138 expanded)
%              Number of leaves         :   18 (  55 expanded)
%              Depth                    :   12
%              Number of atoms          :   73 ( 292 expanded)
%              Number of equality atoms :   15 (  52 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > #nlpp > k1_setfam_1 > k1_xboole_0 > #skF_7 > #skF_3 > #skF_6 > #skF_2 > #skF_1 > #skF_5 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

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

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_58,negated_conjecture,(
    ~ ! [A,B] :
        ( r2_hidden(A,B)
       => r1_tarski(k1_setfam_1(B),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_setfam_1)).

tff(f_53,axiom,(
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

tff(f_34,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_32,plain,(
    ~ r1_tarski(k1_setfam_1('#skF_7'),'#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_42,plain,(
    ! [A_29,B_30] :
      ( r2_hidden('#skF_1'(A_29,B_30),A_29)
      | r1_tarski(A_29,B_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_47,plain,(
    ! [A_29] : r1_tarski(A_29,A_29) ),
    inference(resolution,[status(thm)],[c_42,c_4])).

tff(c_34,plain,(
    r2_hidden('#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_77,plain,(
    ! [C_41,D_42,A_43] :
      ( r2_hidden(C_41,D_42)
      | ~ r2_hidden(D_42,A_43)
      | ~ r2_hidden(C_41,k1_setfam_1(A_43))
      | k1_xboole_0 = A_43 ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_89,plain,(
    ! [C_41] :
      ( r2_hidden(C_41,'#skF_6')
      | ~ r2_hidden(C_41,k1_setfam_1('#skF_7'))
      | k1_xboole_0 = '#skF_7' ) ),
    inference(resolution,[status(thm)],[c_34,c_77])).

tff(c_90,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(splitLeft,[status(thm)],[c_89])).

tff(c_8,plain,(
    ! [A_6] : r1_tarski(k1_xboole_0,A_6) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_49,plain,(
    ! [C_32,B_33,A_34] :
      ( r2_hidden(C_32,B_33)
      | ~ r2_hidden(C_32,A_34)
      | ~ r1_tarski(A_34,B_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_56,plain,(
    ! [B_35] :
      ( r2_hidden('#skF_6',B_35)
      | ~ r1_tarski('#skF_7',B_35) ) ),
    inference(resolution,[status(thm)],[c_34,c_49])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_60,plain,(
    ! [B_36,B_37] :
      ( r2_hidden('#skF_6',B_36)
      | ~ r1_tarski(B_37,B_36)
      | ~ r1_tarski('#skF_7',B_37) ) ),
    inference(resolution,[status(thm)],[c_56,c_2])).

tff(c_66,plain,(
    ! [A_6] :
      ( r2_hidden('#skF_6',A_6)
      | ~ r1_tarski('#skF_7',k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_8,c_60])).

tff(c_67,plain,(
    ~ r1_tarski('#skF_7',k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_66])).

tff(c_109,plain,(
    ~ r1_tarski('#skF_7','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_67])).

tff(c_114,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_47,c_109])).

tff(c_117,plain,(
    ! [C_46] :
      ( r2_hidden(C_46,'#skF_6')
      | ~ r2_hidden(C_46,k1_setfam_1('#skF_7')) ) ),
    inference(splitRight,[status(thm)],[c_89])).

tff(c_134,plain,(
    ! [B_47] :
      ( r2_hidden('#skF_1'(k1_setfam_1('#skF_7'),B_47),'#skF_6')
      | r1_tarski(k1_setfam_1('#skF_7'),B_47) ) ),
    inference(resolution,[status(thm)],[c_6,c_117])).

tff(c_142,plain,(
    r1_tarski(k1_setfam_1('#skF_7'),'#skF_6') ),
    inference(resolution,[status(thm)],[c_134,c_4])).

tff(c_148,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_32,c_142])).

tff(c_149,plain,(
    ! [A_6] : r2_hidden('#skF_6',A_6) ),
    inference(splitRight,[status(thm)],[c_66])).

tff(c_168,plain,(
    ! [C_52,D_53,A_54] :
      ( r2_hidden(C_52,D_53)
      | ~ r2_hidden(D_53,A_54)
      | ~ r2_hidden(C_52,k1_setfam_1(A_54))
      | k1_xboole_0 = A_54 ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_178,plain,(
    ! [C_55,A_56] :
      ( r2_hidden(C_55,'#skF_6')
      | ~ r2_hidden(C_55,k1_setfam_1(A_56))
      | k1_xboole_0 = A_56 ) ),
    inference(resolution,[status(thm)],[c_149,c_168])).

tff(c_199,plain,(
    ! [A_57,B_58] :
      ( r2_hidden('#skF_1'(k1_setfam_1(A_57),B_58),'#skF_6')
      | k1_xboole_0 = A_57
      | r1_tarski(k1_setfam_1(A_57),B_58) ) ),
    inference(resolution,[status(thm)],[c_6,c_178])).

tff(c_216,plain,(
    ! [A_59] :
      ( k1_xboole_0 = A_59
      | r1_tarski(k1_setfam_1(A_59),'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_199,c_4])).

tff(c_223,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(resolution,[status(thm)],[c_216,c_32])).

tff(c_231,plain,(
    ! [A_6] : r1_tarski('#skF_7',A_6) ),
    inference(demodulation,[status(thm),theory(equality)],[c_223,c_8])).

tff(c_30,plain,(
    k1_setfam_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_232,plain,(
    k1_setfam_1('#skF_7') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_223,c_223,c_30])).

tff(c_239,plain,(
    ~ r1_tarski('#skF_7','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_232,c_32])).

tff(c_242,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_231,c_239])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:48:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.87/1.22  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.87/1.22  
% 1.87/1.22  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.87/1.22  %$ r2_hidden > r1_tarski > #nlpp > k1_setfam_1 > k1_xboole_0 > #skF_7 > #skF_3 > #skF_6 > #skF_2 > #skF_1 > #skF_5 > #skF_4
% 1.87/1.22  
% 1.87/1.22  %Foreground sorts:
% 1.87/1.22  
% 1.87/1.22  
% 1.87/1.22  %Background operators:
% 1.87/1.22  
% 1.87/1.22  
% 1.87/1.22  %Foreground operators:
% 1.87/1.22  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.87/1.22  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.87/1.22  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.87/1.22  tff('#skF_7', type, '#skF_7': $i).
% 1.87/1.22  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 1.87/1.22  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.87/1.22  tff('#skF_6', type, '#skF_6': $i).
% 1.87/1.22  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 1.87/1.22  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.87/1.22  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.87/1.22  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.87/1.22  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 1.87/1.22  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 1.87/1.22  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 1.87/1.22  
% 2.09/1.24  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 2.09/1.24  tff(f_58, negated_conjecture, ~(![A, B]: (r2_hidden(A, B) => r1_tarski(k1_setfam_1(B), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_setfam_1)).
% 2.09/1.24  tff(f_53, axiom, (![A, B]: ((~(A = k1_xboole_0) => ((B = k1_setfam_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (![D]: (r2_hidden(D, A) => r2_hidden(C, D))))))) & ((A = k1_xboole_0) => ((B = k1_setfam_1(A)) <=> (B = k1_xboole_0))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_setfam_1)).
% 2.09/1.24  tff(f_34, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.09/1.24  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.09/1.24  tff(c_32, plain, (~r1_tarski(k1_setfam_1('#skF_7'), '#skF_6')), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.09/1.24  tff(c_42, plain, (![A_29, B_30]: (r2_hidden('#skF_1'(A_29, B_30), A_29) | r1_tarski(A_29, B_30))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.09/1.24  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.09/1.24  tff(c_47, plain, (![A_29]: (r1_tarski(A_29, A_29))), inference(resolution, [status(thm)], [c_42, c_4])).
% 2.09/1.24  tff(c_34, plain, (r2_hidden('#skF_6', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.09/1.24  tff(c_77, plain, (![C_41, D_42, A_43]: (r2_hidden(C_41, D_42) | ~r2_hidden(D_42, A_43) | ~r2_hidden(C_41, k1_setfam_1(A_43)) | k1_xboole_0=A_43)), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.09/1.24  tff(c_89, plain, (![C_41]: (r2_hidden(C_41, '#skF_6') | ~r2_hidden(C_41, k1_setfam_1('#skF_7')) | k1_xboole_0='#skF_7')), inference(resolution, [status(thm)], [c_34, c_77])).
% 2.09/1.24  tff(c_90, plain, (k1_xboole_0='#skF_7'), inference(splitLeft, [status(thm)], [c_89])).
% 2.09/1.24  tff(c_8, plain, (![A_6]: (r1_tarski(k1_xboole_0, A_6))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.09/1.24  tff(c_49, plain, (![C_32, B_33, A_34]: (r2_hidden(C_32, B_33) | ~r2_hidden(C_32, A_34) | ~r1_tarski(A_34, B_33))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.09/1.24  tff(c_56, plain, (![B_35]: (r2_hidden('#skF_6', B_35) | ~r1_tarski('#skF_7', B_35))), inference(resolution, [status(thm)], [c_34, c_49])).
% 2.09/1.24  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.09/1.24  tff(c_60, plain, (![B_36, B_37]: (r2_hidden('#skF_6', B_36) | ~r1_tarski(B_37, B_36) | ~r1_tarski('#skF_7', B_37))), inference(resolution, [status(thm)], [c_56, c_2])).
% 2.09/1.24  tff(c_66, plain, (![A_6]: (r2_hidden('#skF_6', A_6) | ~r1_tarski('#skF_7', k1_xboole_0))), inference(resolution, [status(thm)], [c_8, c_60])).
% 2.09/1.24  tff(c_67, plain, (~r1_tarski('#skF_7', k1_xboole_0)), inference(splitLeft, [status(thm)], [c_66])).
% 2.09/1.24  tff(c_109, plain, (~r1_tarski('#skF_7', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_90, c_67])).
% 2.09/1.24  tff(c_114, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_47, c_109])).
% 2.09/1.24  tff(c_117, plain, (![C_46]: (r2_hidden(C_46, '#skF_6') | ~r2_hidden(C_46, k1_setfam_1('#skF_7')))), inference(splitRight, [status(thm)], [c_89])).
% 2.09/1.24  tff(c_134, plain, (![B_47]: (r2_hidden('#skF_1'(k1_setfam_1('#skF_7'), B_47), '#skF_6') | r1_tarski(k1_setfam_1('#skF_7'), B_47))), inference(resolution, [status(thm)], [c_6, c_117])).
% 2.09/1.24  tff(c_142, plain, (r1_tarski(k1_setfam_1('#skF_7'), '#skF_6')), inference(resolution, [status(thm)], [c_134, c_4])).
% 2.09/1.24  tff(c_148, plain, $false, inference(negUnitSimplification, [status(thm)], [c_32, c_32, c_142])).
% 2.09/1.24  tff(c_149, plain, (![A_6]: (r2_hidden('#skF_6', A_6))), inference(splitRight, [status(thm)], [c_66])).
% 2.09/1.24  tff(c_168, plain, (![C_52, D_53, A_54]: (r2_hidden(C_52, D_53) | ~r2_hidden(D_53, A_54) | ~r2_hidden(C_52, k1_setfam_1(A_54)) | k1_xboole_0=A_54)), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.09/1.24  tff(c_178, plain, (![C_55, A_56]: (r2_hidden(C_55, '#skF_6') | ~r2_hidden(C_55, k1_setfam_1(A_56)) | k1_xboole_0=A_56)), inference(resolution, [status(thm)], [c_149, c_168])).
% 2.09/1.24  tff(c_199, plain, (![A_57, B_58]: (r2_hidden('#skF_1'(k1_setfam_1(A_57), B_58), '#skF_6') | k1_xboole_0=A_57 | r1_tarski(k1_setfam_1(A_57), B_58))), inference(resolution, [status(thm)], [c_6, c_178])).
% 2.09/1.24  tff(c_216, plain, (![A_59]: (k1_xboole_0=A_59 | r1_tarski(k1_setfam_1(A_59), '#skF_6'))), inference(resolution, [status(thm)], [c_199, c_4])).
% 2.09/1.24  tff(c_223, plain, (k1_xboole_0='#skF_7'), inference(resolution, [status(thm)], [c_216, c_32])).
% 2.09/1.24  tff(c_231, plain, (![A_6]: (r1_tarski('#skF_7', A_6))), inference(demodulation, [status(thm), theory('equality')], [c_223, c_8])).
% 2.09/1.24  tff(c_30, plain, (k1_setfam_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.09/1.24  tff(c_232, plain, (k1_setfam_1('#skF_7')='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_223, c_223, c_30])).
% 2.09/1.24  tff(c_239, plain, (~r1_tarski('#skF_7', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_232, c_32])).
% 2.09/1.24  tff(c_242, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_231, c_239])).
% 2.09/1.24  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.09/1.24  
% 2.09/1.24  Inference rules
% 2.09/1.24  ----------------------
% 2.09/1.24  #Ref     : 0
% 2.09/1.24  #Sup     : 41
% 2.09/1.24  #Fact    : 0
% 2.09/1.24  #Define  : 0
% 2.09/1.24  #Split   : 3
% 2.09/1.24  #Chain   : 0
% 2.09/1.24  #Close   : 0
% 2.09/1.24  
% 2.09/1.24  Ordering : KBO
% 2.09/1.24  
% 2.09/1.24  Simplification rules
% 2.09/1.24  ----------------------
% 2.09/1.24  #Subsume      : 1
% 2.09/1.24  #Demod        : 28
% 2.09/1.24  #Tautology    : 17
% 2.09/1.24  #SimpNegUnit  : 1
% 2.09/1.24  #BackRed      : 13
% 2.09/1.24  
% 2.09/1.24  #Partial instantiations: 0
% 2.09/1.24  #Strategies tried      : 1
% 2.09/1.24  
% 2.09/1.24  Timing (in seconds)
% 2.09/1.24  ----------------------
% 2.09/1.24  Preprocessing        : 0.27
% 2.09/1.24  Parsing              : 0.14
% 2.09/1.24  CNF conversion       : 0.02
% 2.09/1.24  Main loop            : 0.21
% 2.09/1.24  Inferencing          : 0.07
% 2.09/1.24  Reduction            : 0.06
% 2.09/1.24  Demodulation         : 0.04
% 2.09/1.24  BG Simplification    : 0.02
% 2.09/1.24  Subsumption          : 0.05
% 2.09/1.24  Abstraction          : 0.01
% 2.09/1.24  MUC search           : 0.00
% 2.09/1.24  Cooper               : 0.00
% 2.09/1.24  Total                : 0.51
% 2.09/1.24  Index Insertion      : 0.00
% 2.09/1.24  Index Deletion       : 0.00
% 2.09/1.24  Index Matching       : 0.00
% 2.09/1.24  BG Taut test         : 0.00
%------------------------------------------------------------------------------
