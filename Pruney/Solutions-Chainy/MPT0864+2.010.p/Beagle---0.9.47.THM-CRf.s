%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:09:10 EST 2020

% Result     : Theorem 2.45s
% Output     : CNFRefutation 2.45s
% Verified   : 
% Statistics : Number of formulae       :   73 ( 175 expanded)
%              Number of leaves         :   28 (  73 expanded)
%              Depth                    :   10
%              Number of atoms          :   86 ( 290 expanded)
%              Number of equality atoms :   63 ( 196 expanded)
%              Maximal formula depth    :   12 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_tarski > #nlpp > k2_mcart_1 > k1_tarski > k1_setfam_1 > k1_mcart_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_mcart_1,type,(
    k2_mcart_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_mcart_1,type,(
    k1_mcart_1: $i > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_33,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_37,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
    <=> A != B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_zfmisc_1)).

tff(f_79,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] :
            ~ ( r2_hidden(B,A)
              & ! [C,D] :
                  ~ ( ( r2_hidden(C,A)
                      | r2_hidden(D,A) )
                    & B = k4_tarski(C,D) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_mcart_1)).

tff(f_57,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k4_xboole_0(B,k1_tarski(C)))
    <=> ( r2_hidden(A,B)
        & A != C ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_zfmisc_1)).

tff(f_89,negated_conjecture,(
    ~ ! [A] :
        ( ? [B,C] : A = k4_tarski(B,C)
       => ( A != k1_mcart_1(A)
          & A != k2_mcart_1(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_mcart_1)).

tff(f_63,axiom,(
    ! [A,B] :
      ( k1_mcart_1(k4_tarski(A,B)) = A
      & k2_mcart_1(k4_tarski(A,B)) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_mcart_1)).

tff(c_8,plain,(
    ! [B_4] : r1_tarski(B_4,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_377,plain,(
    ! [A_92,B_93] :
      ( k4_xboole_0(A_92,B_93) = k1_xboole_0
      | ~ r1_tarski(A_92,B_93) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_385,plain,(
    ! [B_4] : k4_xboole_0(B_4,B_4) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_8,c_377])).

tff(c_22,plain,(
    ! [B_16] : k4_xboole_0(k1_tarski(B_16),k1_tarski(B_16)) != k1_tarski(B_16) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_399,plain,(
    ! [B_16] : k1_tarski(B_16) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_385,c_22])).

tff(c_38,plain,(
    ! [A_24] :
      ( r2_hidden('#skF_1'(A_24),A_24)
      | k1_xboole_0 = A_24 ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_458,plain,(
    ! [A_105,B_106] :
      ( k4_xboole_0(k1_tarski(A_105),k1_tarski(B_106)) = k1_tarski(A_105)
      | B_106 = A_105 ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_28,plain,(
    ! [C_19,B_18] : ~ r2_hidden(C_19,k4_xboole_0(B_18,k1_tarski(C_19))) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_482,plain,(
    ! [B_107,A_108] :
      ( ~ r2_hidden(B_107,k1_tarski(A_108))
      | B_107 = A_108 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_458,c_28])).

tff(c_486,plain,(
    ! [A_108] :
      ( '#skF_1'(k1_tarski(A_108)) = A_108
      | k1_tarski(A_108) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_38,c_482])).

tff(c_489,plain,(
    ! [A_108] : '#skF_1'(k1_tarski(A_108)) = A_108 ),
    inference(negUnitSimplification,[status(thm)],[c_399,c_486])).

tff(c_499,plain,(
    ! [A_112] : '#skF_1'(k1_tarski(A_112)) = A_112 ),
    inference(negUnitSimplification,[status(thm)],[c_399,c_486])).

tff(c_505,plain,(
    ! [A_112] :
      ( r2_hidden(A_112,k1_tarski(A_112))
      | k1_tarski(A_112) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_499,c_38])).

tff(c_510,plain,(
    ! [A_112] : r2_hidden(A_112,k1_tarski(A_112)) ),
    inference(negUnitSimplification,[status(thm)],[c_399,c_505])).

tff(c_552,plain,(
    ! [D_122,A_123,C_124] :
      ( ~ r2_hidden(D_122,A_123)
      | k4_tarski(C_124,D_122) != '#skF_1'(A_123)
      | k1_xboole_0 = A_123 ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_554,plain,(
    ! [C_124,A_112] :
      ( k4_tarski(C_124,A_112) != '#skF_1'(k1_tarski(A_112))
      | k1_tarski(A_112) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_510,c_552])).

tff(c_558,plain,(
    ! [C_124,A_112] :
      ( k4_tarski(C_124,A_112) != A_112
      | k1_tarski(A_112) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_489,c_554])).

tff(c_559,plain,(
    ! [C_124,A_112] : k4_tarski(C_124,A_112) != A_112 ),
    inference(negUnitSimplification,[status(thm)],[c_399,c_558])).

tff(c_167,plain,(
    ! [A_54,B_55] :
      ( k4_xboole_0(A_54,B_55) = k1_xboole_0
      | ~ r1_tarski(A_54,B_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_175,plain,(
    ! [B_4] : k4_xboole_0(B_4,B_4) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_8,c_167])).

tff(c_176,plain,(
    ! [B_16] : k1_tarski(B_16) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_175,c_22])).

tff(c_226,plain,(
    ! [A_64,B_65] :
      ( k4_xboole_0(k1_tarski(A_64),k1_tarski(B_65)) = k1_tarski(A_64)
      | B_65 = A_64 ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_250,plain,(
    ! [B_66,A_67] :
      ( ~ r2_hidden(B_66,k1_tarski(A_67))
      | B_66 = A_67 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_226,c_28])).

tff(c_254,plain,(
    ! [A_67] :
      ( '#skF_1'(k1_tarski(A_67)) = A_67
      | k1_tarski(A_67) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_38,c_250])).

tff(c_257,plain,(
    ! [A_67] : '#skF_1'(k1_tarski(A_67)) = A_67 ),
    inference(negUnitSimplification,[status(thm)],[c_176,c_254])).

tff(c_267,plain,(
    ! [A_71] : '#skF_1'(k1_tarski(A_71)) = A_71 ),
    inference(negUnitSimplification,[status(thm)],[c_176,c_254])).

tff(c_273,plain,(
    ! [A_71] :
      ( r2_hidden(A_71,k1_tarski(A_71))
      | k1_tarski(A_71) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_267,c_38])).

tff(c_278,plain,(
    ! [A_71] : r2_hidden(A_71,k1_tarski(A_71)) ),
    inference(negUnitSimplification,[status(thm)],[c_176,c_273])).

tff(c_320,plain,(
    ! [C_81,A_82,D_83] :
      ( ~ r2_hidden(C_81,A_82)
      | k4_tarski(C_81,D_83) != '#skF_1'(A_82)
      | k1_xboole_0 = A_82 ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_322,plain,(
    ! [A_71,D_83] :
      ( k4_tarski(A_71,D_83) != '#skF_1'(k1_tarski(A_71))
      | k1_tarski(A_71) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_278,c_320])).

tff(c_326,plain,(
    ! [A_71,D_83] :
      ( k4_tarski(A_71,D_83) != A_71
      | k1_tarski(A_71) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_257,c_322])).

tff(c_327,plain,(
    ! [A_71,D_83] : k4_tarski(A_71,D_83) != A_71 ),
    inference(negUnitSimplification,[status(thm)],[c_176,c_326])).

tff(c_46,plain,(
    k4_tarski('#skF_3','#skF_4') = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_83,plain,(
    ! [A_41,B_42] : k1_mcart_1(k4_tarski(A_41,B_42)) = A_41 ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_92,plain,(
    k1_mcart_1('#skF_2') = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_83])).

tff(c_71,plain,(
    ! [A_39,B_40] : k2_mcart_1(k4_tarski(A_39,B_40)) = B_40 ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_80,plain,(
    k2_mcart_1('#skF_2') = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_71])).

tff(c_44,plain,
    ( k2_mcart_1('#skF_2') = '#skF_2'
    | k1_mcart_1('#skF_2') = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_104,plain,
    ( '#skF_2' = '#skF_4'
    | '#skF_2' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_80,c_44])).

tff(c_105,plain,(
    '#skF_2' = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_104])).

tff(c_108,plain,(
    k4_tarski('#skF_3','#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_105,c_46])).

tff(c_334,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_327,c_108])).

tff(c_335,plain,(
    '#skF_2' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_104])).

tff(c_339,plain,(
    k4_tarski('#skF_3','#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_335,c_46])).

tff(c_566,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_559,c_339])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:14:34 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.45/1.38  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.45/1.39  
% 2.45/1.39  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.45/1.39  %$ r2_hidden > r1_tarski > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_tarski > #nlpp > k2_mcart_1 > k1_tarski > k1_setfam_1 > k1_mcart_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4
% 2.45/1.39  
% 2.45/1.39  %Foreground sorts:
% 2.45/1.39  
% 2.45/1.39  
% 2.45/1.39  %Background operators:
% 2.45/1.39  
% 2.45/1.39  
% 2.45/1.39  %Foreground operators:
% 2.45/1.39  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.45/1.39  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.45/1.39  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.45/1.39  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.45/1.39  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.45/1.39  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.45/1.39  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.45/1.39  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.45/1.39  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.45/1.39  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.45/1.39  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.45/1.39  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.45/1.39  tff('#skF_2', type, '#skF_2': $i).
% 2.45/1.39  tff('#skF_3', type, '#skF_3': $i).
% 2.45/1.39  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.45/1.39  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 2.45/1.39  tff('#skF_4', type, '#skF_4': $i).
% 2.45/1.39  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.45/1.39  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 2.45/1.39  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.45/1.39  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.45/1.39  
% 2.45/1.41  tff(f_33, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.45/1.41  tff(f_37, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 2.45/1.41  tff(f_50, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) <=> ~(A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_zfmisc_1)).
% 2.45/1.41  tff(f_79, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~(r2_hidden(B, A) & (![C, D]: ~((r2_hidden(C, A) | r2_hidden(D, A)) & (B = k4_tarski(C, D)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t9_mcart_1)).
% 2.45/1.41  tff(f_57, axiom, (![A, B, C]: (r2_hidden(A, k4_xboole_0(B, k1_tarski(C))) <=> (r2_hidden(A, B) & ~(A = C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_zfmisc_1)).
% 2.45/1.41  tff(f_89, negated_conjecture, ~(![A]: ((?[B, C]: (A = k4_tarski(B, C))) => (~(A = k1_mcart_1(A)) & ~(A = k2_mcart_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_mcart_1)).
% 2.45/1.41  tff(f_63, axiom, (![A, B]: ((k1_mcart_1(k4_tarski(A, B)) = A) & (k2_mcart_1(k4_tarski(A, B)) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_mcart_1)).
% 2.45/1.41  tff(c_8, plain, (![B_4]: (r1_tarski(B_4, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.45/1.41  tff(c_377, plain, (![A_92, B_93]: (k4_xboole_0(A_92, B_93)=k1_xboole_0 | ~r1_tarski(A_92, B_93))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.45/1.41  tff(c_385, plain, (![B_4]: (k4_xboole_0(B_4, B_4)=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_377])).
% 2.45/1.41  tff(c_22, plain, (![B_16]: (k4_xboole_0(k1_tarski(B_16), k1_tarski(B_16))!=k1_tarski(B_16))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.45/1.41  tff(c_399, plain, (![B_16]: (k1_tarski(B_16)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_385, c_22])).
% 2.45/1.41  tff(c_38, plain, (![A_24]: (r2_hidden('#skF_1'(A_24), A_24) | k1_xboole_0=A_24)), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.45/1.41  tff(c_458, plain, (![A_105, B_106]: (k4_xboole_0(k1_tarski(A_105), k1_tarski(B_106))=k1_tarski(A_105) | B_106=A_105)), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.45/1.41  tff(c_28, plain, (![C_19, B_18]: (~r2_hidden(C_19, k4_xboole_0(B_18, k1_tarski(C_19))))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.45/1.41  tff(c_482, plain, (![B_107, A_108]: (~r2_hidden(B_107, k1_tarski(A_108)) | B_107=A_108)), inference(superposition, [status(thm), theory('equality')], [c_458, c_28])).
% 2.45/1.41  tff(c_486, plain, (![A_108]: ('#skF_1'(k1_tarski(A_108))=A_108 | k1_tarski(A_108)=k1_xboole_0)), inference(resolution, [status(thm)], [c_38, c_482])).
% 2.45/1.41  tff(c_489, plain, (![A_108]: ('#skF_1'(k1_tarski(A_108))=A_108)), inference(negUnitSimplification, [status(thm)], [c_399, c_486])).
% 2.45/1.41  tff(c_499, plain, (![A_112]: ('#skF_1'(k1_tarski(A_112))=A_112)), inference(negUnitSimplification, [status(thm)], [c_399, c_486])).
% 2.45/1.41  tff(c_505, plain, (![A_112]: (r2_hidden(A_112, k1_tarski(A_112)) | k1_tarski(A_112)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_499, c_38])).
% 2.45/1.41  tff(c_510, plain, (![A_112]: (r2_hidden(A_112, k1_tarski(A_112)))), inference(negUnitSimplification, [status(thm)], [c_399, c_505])).
% 2.45/1.41  tff(c_552, plain, (![D_122, A_123, C_124]: (~r2_hidden(D_122, A_123) | k4_tarski(C_124, D_122)!='#skF_1'(A_123) | k1_xboole_0=A_123)), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.45/1.41  tff(c_554, plain, (![C_124, A_112]: (k4_tarski(C_124, A_112)!='#skF_1'(k1_tarski(A_112)) | k1_tarski(A_112)=k1_xboole_0)), inference(resolution, [status(thm)], [c_510, c_552])).
% 2.45/1.41  tff(c_558, plain, (![C_124, A_112]: (k4_tarski(C_124, A_112)!=A_112 | k1_tarski(A_112)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_489, c_554])).
% 2.45/1.41  tff(c_559, plain, (![C_124, A_112]: (k4_tarski(C_124, A_112)!=A_112)), inference(negUnitSimplification, [status(thm)], [c_399, c_558])).
% 2.45/1.41  tff(c_167, plain, (![A_54, B_55]: (k4_xboole_0(A_54, B_55)=k1_xboole_0 | ~r1_tarski(A_54, B_55))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.45/1.41  tff(c_175, plain, (![B_4]: (k4_xboole_0(B_4, B_4)=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_167])).
% 2.45/1.41  tff(c_176, plain, (![B_16]: (k1_tarski(B_16)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_175, c_22])).
% 2.45/1.41  tff(c_226, plain, (![A_64, B_65]: (k4_xboole_0(k1_tarski(A_64), k1_tarski(B_65))=k1_tarski(A_64) | B_65=A_64)), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.45/1.41  tff(c_250, plain, (![B_66, A_67]: (~r2_hidden(B_66, k1_tarski(A_67)) | B_66=A_67)), inference(superposition, [status(thm), theory('equality')], [c_226, c_28])).
% 2.45/1.41  tff(c_254, plain, (![A_67]: ('#skF_1'(k1_tarski(A_67))=A_67 | k1_tarski(A_67)=k1_xboole_0)), inference(resolution, [status(thm)], [c_38, c_250])).
% 2.45/1.41  tff(c_257, plain, (![A_67]: ('#skF_1'(k1_tarski(A_67))=A_67)), inference(negUnitSimplification, [status(thm)], [c_176, c_254])).
% 2.45/1.41  tff(c_267, plain, (![A_71]: ('#skF_1'(k1_tarski(A_71))=A_71)), inference(negUnitSimplification, [status(thm)], [c_176, c_254])).
% 2.45/1.41  tff(c_273, plain, (![A_71]: (r2_hidden(A_71, k1_tarski(A_71)) | k1_tarski(A_71)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_267, c_38])).
% 2.45/1.41  tff(c_278, plain, (![A_71]: (r2_hidden(A_71, k1_tarski(A_71)))), inference(negUnitSimplification, [status(thm)], [c_176, c_273])).
% 2.45/1.41  tff(c_320, plain, (![C_81, A_82, D_83]: (~r2_hidden(C_81, A_82) | k4_tarski(C_81, D_83)!='#skF_1'(A_82) | k1_xboole_0=A_82)), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.45/1.41  tff(c_322, plain, (![A_71, D_83]: (k4_tarski(A_71, D_83)!='#skF_1'(k1_tarski(A_71)) | k1_tarski(A_71)=k1_xboole_0)), inference(resolution, [status(thm)], [c_278, c_320])).
% 2.45/1.41  tff(c_326, plain, (![A_71, D_83]: (k4_tarski(A_71, D_83)!=A_71 | k1_tarski(A_71)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_257, c_322])).
% 2.45/1.41  tff(c_327, plain, (![A_71, D_83]: (k4_tarski(A_71, D_83)!=A_71)), inference(negUnitSimplification, [status(thm)], [c_176, c_326])).
% 2.45/1.41  tff(c_46, plain, (k4_tarski('#skF_3', '#skF_4')='#skF_2'), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.45/1.41  tff(c_83, plain, (![A_41, B_42]: (k1_mcart_1(k4_tarski(A_41, B_42))=A_41)), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.45/1.41  tff(c_92, plain, (k1_mcart_1('#skF_2')='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_46, c_83])).
% 2.45/1.41  tff(c_71, plain, (![A_39, B_40]: (k2_mcart_1(k4_tarski(A_39, B_40))=B_40)), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.45/1.41  tff(c_80, plain, (k2_mcart_1('#skF_2')='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_46, c_71])).
% 2.45/1.41  tff(c_44, plain, (k2_mcart_1('#skF_2')='#skF_2' | k1_mcart_1('#skF_2')='#skF_2'), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.45/1.41  tff(c_104, plain, ('#skF_2'='#skF_4' | '#skF_2'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_92, c_80, c_44])).
% 2.45/1.41  tff(c_105, plain, ('#skF_2'='#skF_3'), inference(splitLeft, [status(thm)], [c_104])).
% 2.45/1.41  tff(c_108, plain, (k4_tarski('#skF_3', '#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_105, c_46])).
% 2.45/1.41  tff(c_334, plain, $false, inference(negUnitSimplification, [status(thm)], [c_327, c_108])).
% 2.45/1.41  tff(c_335, plain, ('#skF_2'='#skF_4'), inference(splitRight, [status(thm)], [c_104])).
% 2.45/1.41  tff(c_339, plain, (k4_tarski('#skF_3', '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_335, c_46])).
% 2.45/1.41  tff(c_566, plain, $false, inference(negUnitSimplification, [status(thm)], [c_559, c_339])).
% 2.45/1.41  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.45/1.41  
% 2.45/1.41  Inference rules
% 2.45/1.41  ----------------------
% 2.45/1.41  #Ref     : 0
% 2.45/1.41  #Sup     : 120
% 2.45/1.41  #Fact    : 0
% 2.45/1.41  #Define  : 0
% 2.45/1.41  #Split   : 1
% 2.45/1.41  #Chain   : 0
% 2.45/1.41  #Close   : 0
% 2.45/1.41  
% 2.45/1.41  Ordering : KBO
% 2.45/1.41  
% 2.45/1.41  Simplification rules
% 2.45/1.41  ----------------------
% 2.45/1.41  #Subsume      : 3
% 2.45/1.41  #Demod        : 28
% 2.45/1.41  #Tautology    : 87
% 2.45/1.41  #SimpNegUnit  : 14
% 2.45/1.41  #BackRed      : 10
% 2.45/1.41  
% 2.45/1.41  #Partial instantiations: 0
% 2.45/1.41  #Strategies tried      : 1
% 2.45/1.41  
% 2.45/1.41  Timing (in seconds)
% 2.45/1.41  ----------------------
% 2.45/1.41  Preprocessing        : 0.34
% 2.45/1.41  Parsing              : 0.18
% 2.45/1.41  CNF conversion       : 0.02
% 2.45/1.41  Main loop            : 0.25
% 2.45/1.41  Inferencing          : 0.10
% 2.45/1.41  Reduction            : 0.07
% 2.45/1.41  Demodulation         : 0.05
% 2.45/1.41  BG Simplification    : 0.02
% 2.45/1.41  Subsumption          : 0.04
% 2.45/1.41  Abstraction          : 0.02
% 2.45/1.41  MUC search           : 0.00
% 2.45/1.41  Cooper               : 0.00
% 2.45/1.41  Total                : 0.62
% 2.45/1.41  Index Insertion      : 0.00
% 2.45/1.41  Index Deletion       : 0.00
% 2.45/1.41  Index Matching       : 0.00
% 2.45/1.41  BG Taut test         : 0.00
%------------------------------------------------------------------------------
