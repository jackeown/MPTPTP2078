%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:09:18 EST 2020

% Result     : Theorem 2.20s
% Output     : CNFRefutation 2.47s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 176 expanded)
%              Number of leaves         :   29 (  74 expanded)
%              Depth                    :   10
%              Number of atoms          :   81 ( 258 expanded)
%              Number of equality atoms :   64 ( 204 expanded)
%              Maximal formula depth    :   12 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k2_mcart_1 > k1_tarski > k1_setfam_1 > k1_mcart_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4

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

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_mcart_1,type,(
    k1_mcart_1: $i > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

tff(f_33,axiom,(
    ! [A,B] : k4_xboole_0(A,k2_xboole_0(A,B)) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).

tff(f_46,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
    <=> A != B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_zfmisc_1)).

tff(f_75,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] :
            ~ ( r2_hidden(B,A)
              & ! [C,D] :
                  ~ ( ( r2_hidden(C,A)
                      | r2_hidden(D,A) )
                    & B = k4_tarski(C,D) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_mcart_1)).

tff(f_53,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k4_xboole_0(B,k1_tarski(C)))
    <=> ( r2_hidden(A,B)
        & A != C ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_zfmisc_1)).

tff(f_85,negated_conjecture,(
    ~ ! [A] :
        ( ? [B,C] : A = k4_tarski(B,C)
       => ( A != k1_mcart_1(A)
          & A != k2_mcart_1(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_mcart_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( k1_mcart_1(k4_tarski(A,B)) = A
      & k2_mcart_1(k4_tarski(A,B)) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_mcart_1)).

tff(c_2,plain,(
    ! [A_1] : k2_xboole_0(A_1,A_1) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_367,plain,(
    ! [A_84,B_85] : k4_xboole_0(A_84,k2_xboole_0(A_84,B_85)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_374,plain,(
    ! [A_1] : k4_xboole_0(A_1,A_1) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_367])).

tff(c_18,plain,(
    ! [B_18] : k4_xboole_0(k1_tarski(B_18),k1_tarski(B_18)) != k1_tarski(B_18) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_404,plain,(
    ! [B_18] : k1_tarski(B_18) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_374,c_18])).

tff(c_34,plain,(
    ! [A_26] :
      ( r2_hidden('#skF_1'(A_26),A_26)
      | k1_xboole_0 = A_26 ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_464,plain,(
    ! [A_101,B_102] :
      ( k4_xboole_0(k1_tarski(A_101),k1_tarski(B_102)) = k1_tarski(A_101)
      | B_102 = A_101 ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_24,plain,(
    ! [C_21,B_20] : ~ r2_hidden(C_21,k4_xboole_0(B_20,k1_tarski(C_21))) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_495,plain,(
    ! [B_104,A_105] :
      ( ~ r2_hidden(B_104,k1_tarski(A_105))
      | B_104 = A_105 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_464,c_24])).

tff(c_499,plain,(
    ! [A_105] :
      ( '#skF_1'(k1_tarski(A_105)) = A_105
      | k1_tarski(A_105) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_34,c_495])).

tff(c_502,plain,(
    ! [A_105] : '#skF_1'(k1_tarski(A_105)) = A_105 ),
    inference(negUnitSimplification,[status(thm)],[c_404,c_499])).

tff(c_503,plain,(
    ! [A_106] : '#skF_1'(k1_tarski(A_106)) = A_106 ),
    inference(negUnitSimplification,[status(thm)],[c_404,c_499])).

tff(c_509,plain,(
    ! [A_106] :
      ( r2_hidden(A_106,k1_tarski(A_106))
      | k1_tarski(A_106) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_503,c_34])).

tff(c_514,plain,(
    ! [A_106] : r2_hidden(A_106,k1_tarski(A_106)) ),
    inference(negUnitSimplification,[status(thm)],[c_404,c_509])).

tff(c_557,plain,(
    ! [D_119,A_120,C_121] :
      ( ~ r2_hidden(D_119,A_120)
      | k4_tarski(C_121,D_119) != '#skF_1'(A_120)
      | k1_xboole_0 = A_120 ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_559,plain,(
    ! [C_121,A_106] :
      ( k4_tarski(C_121,A_106) != '#skF_1'(k1_tarski(A_106))
      | k1_tarski(A_106) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_514,c_557])).

tff(c_563,plain,(
    ! [C_121,A_106] :
      ( k4_tarski(C_121,A_106) != A_106
      | k1_tarski(A_106) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_502,c_559])).

tff(c_564,plain,(
    ! [C_121,A_106] : k4_tarski(C_121,A_106) != A_106 ),
    inference(negUnitSimplification,[status(thm)],[c_404,c_563])).

tff(c_136,plain,(
    ! [A_46,B_47] : k4_xboole_0(A_46,k2_xboole_0(A_46,B_47)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_143,plain,(
    ! [A_1] : k4_xboole_0(A_1,A_1) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_136])).

tff(c_217,plain,(
    ! [B_18] : k1_tarski(B_18) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_143,c_18])).

tff(c_233,plain,(
    ! [A_63,B_64] :
      ( k4_xboole_0(k1_tarski(A_63),k1_tarski(B_64)) = k1_tarski(A_63)
      | B_64 = A_63 ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_264,plain,(
    ! [B_66,A_67] :
      ( ~ r2_hidden(B_66,k1_tarski(A_67))
      | B_66 = A_67 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_233,c_24])).

tff(c_268,plain,(
    ! [A_67] :
      ( '#skF_1'(k1_tarski(A_67)) = A_67
      | k1_tarski(A_67) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_34,c_264])).

tff(c_271,plain,(
    ! [A_67] : '#skF_1'(k1_tarski(A_67)) = A_67 ),
    inference(negUnitSimplification,[status(thm)],[c_217,c_268])).

tff(c_272,plain,(
    ! [A_68] : '#skF_1'(k1_tarski(A_68)) = A_68 ),
    inference(negUnitSimplification,[status(thm)],[c_217,c_268])).

tff(c_278,plain,(
    ! [A_68] :
      ( r2_hidden(A_68,k1_tarski(A_68))
      | k1_tarski(A_68) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_272,c_34])).

tff(c_283,plain,(
    ! [A_68] : r2_hidden(A_68,k1_tarski(A_68)) ),
    inference(negUnitSimplification,[status(thm)],[c_217,c_278])).

tff(c_326,plain,(
    ! [C_81,A_82,D_83] :
      ( ~ r2_hidden(C_81,A_82)
      | k4_tarski(C_81,D_83) != '#skF_1'(A_82)
      | k1_xboole_0 = A_82 ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_328,plain,(
    ! [A_68,D_83] :
      ( k4_tarski(A_68,D_83) != '#skF_1'(k1_tarski(A_68))
      | k1_tarski(A_68) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_283,c_326])).

tff(c_332,plain,(
    ! [A_68,D_83] :
      ( k4_tarski(A_68,D_83) != A_68
      | k1_tarski(A_68) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_271,c_328])).

tff(c_333,plain,(
    ! [A_68,D_83] : k4_tarski(A_68,D_83) != A_68 ),
    inference(negUnitSimplification,[status(thm)],[c_217,c_332])).

tff(c_42,plain,(
    k4_tarski('#skF_3','#skF_4') = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_86,plain,(
    ! [A_43,B_44] : k1_mcart_1(k4_tarski(A_43,B_44)) = A_43 ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_95,plain,(
    k1_mcart_1('#skF_2') = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_86])).

tff(c_74,plain,(
    ! [A_41,B_42] : k2_mcart_1(k4_tarski(A_41,B_42)) = B_42 ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_83,plain,(
    k2_mcart_1('#skF_2') = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_74])).

tff(c_40,plain,
    ( k2_mcart_1('#skF_2') = '#skF_2'
    | k1_mcart_1('#skF_2') = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_107,plain,
    ( '#skF_2' = '#skF_4'
    | '#skF_2' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_95,c_83,c_40])).

tff(c_108,plain,(
    '#skF_2' = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_107])).

tff(c_111,plain,(
    k4_tarski('#skF_3','#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_108,c_42])).

tff(c_336,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_333,c_111])).

tff(c_337,plain,(
    '#skF_2' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_107])).

tff(c_341,plain,(
    k4_tarski('#skF_3','#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_337,c_42])).

tff(c_567,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_564,c_341])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.35  % Computer   : n023.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 14:38:06 EST 2020
% 0.15/0.36  % CPUTime    : 
% 0.15/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.20/1.32  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.20/1.32  
% 2.20/1.32  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.47/1.33  %$ r2_hidden > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k2_mcart_1 > k1_tarski > k1_setfam_1 > k1_mcart_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4
% 2.47/1.33  
% 2.47/1.33  %Foreground sorts:
% 2.47/1.33  
% 2.47/1.33  
% 2.47/1.33  %Background operators:
% 2.47/1.33  
% 2.47/1.33  
% 2.47/1.33  %Foreground operators:
% 2.47/1.33  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.47/1.33  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.47/1.33  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.47/1.33  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.47/1.33  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.47/1.33  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.47/1.33  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.47/1.33  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.47/1.33  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.47/1.33  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.47/1.33  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.47/1.33  tff('#skF_2', type, '#skF_2': $i).
% 2.47/1.33  tff('#skF_3', type, '#skF_3': $i).
% 2.47/1.33  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.47/1.33  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 2.47/1.33  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.47/1.33  tff('#skF_4', type, '#skF_4': $i).
% 2.47/1.33  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.47/1.33  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 2.47/1.33  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.47/1.33  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.47/1.33  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.47/1.33  
% 2.47/1.34  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k2_xboole_0)).
% 2.47/1.34  tff(f_33, axiom, (![A, B]: (k4_xboole_0(A, k2_xboole_0(A, B)) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_xboole_1)).
% 2.47/1.34  tff(f_46, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) <=> ~(A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_zfmisc_1)).
% 2.47/1.34  tff(f_75, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~(r2_hidden(B, A) & (![C, D]: ~((r2_hidden(C, A) | r2_hidden(D, A)) & (B = k4_tarski(C, D)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t9_mcart_1)).
% 2.47/1.34  tff(f_53, axiom, (![A, B, C]: (r2_hidden(A, k4_xboole_0(B, k1_tarski(C))) <=> (r2_hidden(A, B) & ~(A = C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_zfmisc_1)).
% 2.47/1.34  tff(f_85, negated_conjecture, ~(![A]: ((?[B, C]: (A = k4_tarski(B, C))) => (~(A = k1_mcart_1(A)) & ~(A = k2_mcart_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_mcart_1)).
% 2.47/1.34  tff(f_59, axiom, (![A, B]: ((k1_mcart_1(k4_tarski(A, B)) = A) & (k2_mcart_1(k4_tarski(A, B)) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_mcart_1)).
% 2.47/1.34  tff(c_2, plain, (![A_1]: (k2_xboole_0(A_1, A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.47/1.34  tff(c_367, plain, (![A_84, B_85]: (k4_xboole_0(A_84, k2_xboole_0(A_84, B_85))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.47/1.34  tff(c_374, plain, (![A_1]: (k4_xboole_0(A_1, A_1)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2, c_367])).
% 2.47/1.34  tff(c_18, plain, (![B_18]: (k4_xboole_0(k1_tarski(B_18), k1_tarski(B_18))!=k1_tarski(B_18))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.47/1.34  tff(c_404, plain, (![B_18]: (k1_tarski(B_18)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_374, c_18])).
% 2.47/1.34  tff(c_34, plain, (![A_26]: (r2_hidden('#skF_1'(A_26), A_26) | k1_xboole_0=A_26)), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.47/1.34  tff(c_464, plain, (![A_101, B_102]: (k4_xboole_0(k1_tarski(A_101), k1_tarski(B_102))=k1_tarski(A_101) | B_102=A_101)), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.47/1.34  tff(c_24, plain, (![C_21, B_20]: (~r2_hidden(C_21, k4_xboole_0(B_20, k1_tarski(C_21))))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.47/1.34  tff(c_495, plain, (![B_104, A_105]: (~r2_hidden(B_104, k1_tarski(A_105)) | B_104=A_105)), inference(superposition, [status(thm), theory('equality')], [c_464, c_24])).
% 2.47/1.34  tff(c_499, plain, (![A_105]: ('#skF_1'(k1_tarski(A_105))=A_105 | k1_tarski(A_105)=k1_xboole_0)), inference(resolution, [status(thm)], [c_34, c_495])).
% 2.47/1.34  tff(c_502, plain, (![A_105]: ('#skF_1'(k1_tarski(A_105))=A_105)), inference(negUnitSimplification, [status(thm)], [c_404, c_499])).
% 2.47/1.34  tff(c_503, plain, (![A_106]: ('#skF_1'(k1_tarski(A_106))=A_106)), inference(negUnitSimplification, [status(thm)], [c_404, c_499])).
% 2.47/1.34  tff(c_509, plain, (![A_106]: (r2_hidden(A_106, k1_tarski(A_106)) | k1_tarski(A_106)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_503, c_34])).
% 2.47/1.34  tff(c_514, plain, (![A_106]: (r2_hidden(A_106, k1_tarski(A_106)))), inference(negUnitSimplification, [status(thm)], [c_404, c_509])).
% 2.47/1.34  tff(c_557, plain, (![D_119, A_120, C_121]: (~r2_hidden(D_119, A_120) | k4_tarski(C_121, D_119)!='#skF_1'(A_120) | k1_xboole_0=A_120)), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.47/1.34  tff(c_559, plain, (![C_121, A_106]: (k4_tarski(C_121, A_106)!='#skF_1'(k1_tarski(A_106)) | k1_tarski(A_106)=k1_xboole_0)), inference(resolution, [status(thm)], [c_514, c_557])).
% 2.47/1.34  tff(c_563, plain, (![C_121, A_106]: (k4_tarski(C_121, A_106)!=A_106 | k1_tarski(A_106)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_502, c_559])).
% 2.47/1.34  tff(c_564, plain, (![C_121, A_106]: (k4_tarski(C_121, A_106)!=A_106)), inference(negUnitSimplification, [status(thm)], [c_404, c_563])).
% 2.47/1.34  tff(c_136, plain, (![A_46, B_47]: (k4_xboole_0(A_46, k2_xboole_0(A_46, B_47))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.47/1.34  tff(c_143, plain, (![A_1]: (k4_xboole_0(A_1, A_1)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2, c_136])).
% 2.47/1.34  tff(c_217, plain, (![B_18]: (k1_tarski(B_18)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_143, c_18])).
% 2.47/1.34  tff(c_233, plain, (![A_63, B_64]: (k4_xboole_0(k1_tarski(A_63), k1_tarski(B_64))=k1_tarski(A_63) | B_64=A_63)), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.47/1.34  tff(c_264, plain, (![B_66, A_67]: (~r2_hidden(B_66, k1_tarski(A_67)) | B_66=A_67)), inference(superposition, [status(thm), theory('equality')], [c_233, c_24])).
% 2.47/1.34  tff(c_268, plain, (![A_67]: ('#skF_1'(k1_tarski(A_67))=A_67 | k1_tarski(A_67)=k1_xboole_0)), inference(resolution, [status(thm)], [c_34, c_264])).
% 2.47/1.34  tff(c_271, plain, (![A_67]: ('#skF_1'(k1_tarski(A_67))=A_67)), inference(negUnitSimplification, [status(thm)], [c_217, c_268])).
% 2.47/1.34  tff(c_272, plain, (![A_68]: ('#skF_1'(k1_tarski(A_68))=A_68)), inference(negUnitSimplification, [status(thm)], [c_217, c_268])).
% 2.47/1.34  tff(c_278, plain, (![A_68]: (r2_hidden(A_68, k1_tarski(A_68)) | k1_tarski(A_68)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_272, c_34])).
% 2.47/1.34  tff(c_283, plain, (![A_68]: (r2_hidden(A_68, k1_tarski(A_68)))), inference(negUnitSimplification, [status(thm)], [c_217, c_278])).
% 2.47/1.34  tff(c_326, plain, (![C_81, A_82, D_83]: (~r2_hidden(C_81, A_82) | k4_tarski(C_81, D_83)!='#skF_1'(A_82) | k1_xboole_0=A_82)), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.47/1.34  tff(c_328, plain, (![A_68, D_83]: (k4_tarski(A_68, D_83)!='#skF_1'(k1_tarski(A_68)) | k1_tarski(A_68)=k1_xboole_0)), inference(resolution, [status(thm)], [c_283, c_326])).
% 2.47/1.34  tff(c_332, plain, (![A_68, D_83]: (k4_tarski(A_68, D_83)!=A_68 | k1_tarski(A_68)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_271, c_328])).
% 2.47/1.34  tff(c_333, plain, (![A_68, D_83]: (k4_tarski(A_68, D_83)!=A_68)), inference(negUnitSimplification, [status(thm)], [c_217, c_332])).
% 2.47/1.34  tff(c_42, plain, (k4_tarski('#skF_3', '#skF_4')='#skF_2'), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.47/1.34  tff(c_86, plain, (![A_43, B_44]: (k1_mcart_1(k4_tarski(A_43, B_44))=A_43)), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.47/1.34  tff(c_95, plain, (k1_mcart_1('#skF_2')='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_42, c_86])).
% 2.47/1.34  tff(c_74, plain, (![A_41, B_42]: (k2_mcart_1(k4_tarski(A_41, B_42))=B_42)), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.47/1.34  tff(c_83, plain, (k2_mcart_1('#skF_2')='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_42, c_74])).
% 2.47/1.34  tff(c_40, plain, (k2_mcart_1('#skF_2')='#skF_2' | k1_mcart_1('#skF_2')='#skF_2'), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.47/1.34  tff(c_107, plain, ('#skF_2'='#skF_4' | '#skF_2'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_95, c_83, c_40])).
% 2.47/1.34  tff(c_108, plain, ('#skF_2'='#skF_3'), inference(splitLeft, [status(thm)], [c_107])).
% 2.47/1.34  tff(c_111, plain, (k4_tarski('#skF_3', '#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_108, c_42])).
% 2.47/1.34  tff(c_336, plain, $false, inference(negUnitSimplification, [status(thm)], [c_333, c_111])).
% 2.47/1.34  tff(c_337, plain, ('#skF_2'='#skF_4'), inference(splitRight, [status(thm)], [c_107])).
% 2.47/1.34  tff(c_341, plain, (k4_tarski('#skF_3', '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_337, c_42])).
% 2.47/1.34  tff(c_567, plain, $false, inference(negUnitSimplification, [status(thm)], [c_564, c_341])).
% 2.47/1.34  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.47/1.34  
% 2.47/1.34  Inference rules
% 2.47/1.34  ----------------------
% 2.47/1.34  #Ref     : 0
% 2.47/1.34  #Sup     : 126
% 2.47/1.34  #Fact    : 0
% 2.47/1.34  #Define  : 0
% 2.47/1.34  #Split   : 1
% 2.47/1.34  #Chain   : 0
% 2.47/1.34  #Close   : 0
% 2.47/1.34  
% 2.47/1.34  Ordering : KBO
% 2.47/1.34  
% 2.47/1.34  Simplification rules
% 2.47/1.34  ----------------------
% 2.47/1.34  #Subsume      : 4
% 2.47/1.34  #Demod        : 25
% 2.47/1.34  #Tautology    : 94
% 2.47/1.34  #SimpNegUnit  : 14
% 2.47/1.34  #BackRed      : 8
% 2.47/1.34  
% 2.47/1.34  #Partial instantiations: 0
% 2.47/1.34  #Strategies tried      : 1
% 2.47/1.34  
% 2.47/1.34  Timing (in seconds)
% 2.47/1.34  ----------------------
% 2.47/1.34  Preprocessing        : 0.32
% 2.47/1.34  Parsing              : 0.17
% 2.47/1.34  CNF conversion       : 0.02
% 2.47/1.34  Main loop            : 0.25
% 2.47/1.34  Inferencing          : 0.10
% 2.47/1.34  Reduction            : 0.07
% 2.47/1.34  Demodulation         : 0.05
% 2.47/1.34  BG Simplification    : 0.02
% 2.47/1.34  Subsumption          : 0.03
% 2.47/1.34  Abstraction          : 0.02
% 2.47/1.34  MUC search           : 0.00
% 2.47/1.34  Cooper               : 0.00
% 2.47/1.35  Total                : 0.60
% 2.47/1.35  Index Insertion      : 0.00
% 2.47/1.35  Index Deletion       : 0.00
% 2.47/1.35  Index Matching       : 0.00
% 2.47/1.35  BG Taut test         : 0.00
%------------------------------------------------------------------------------
