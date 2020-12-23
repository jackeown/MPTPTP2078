%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:09:12 EST 2020

% Result     : Theorem 2.35s
% Output     : CNFRefutation 2.35s
% Verified   : 
% Statistics : Number of formulae       :   69 ( 119 expanded)
%              Number of leaves         :   32 (  57 expanded)
%              Depth                    :    7
%              Number of atoms          :   69 ( 160 expanded)
%              Number of equality atoms :   57 ( 134 expanded)
%              Maximal formula depth    :   12 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k2_mcart_1 > k1_tarski > k1_setfam_1 > k1_mcart_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_4 > #skF_3 > #skF_2 > #skF_1

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

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_mcart_1,type,(
    k2_mcart_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k1_mcart_1,type,(
    k1_mcart_1: $i > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

tff(f_33,axiom,(
    ! [A,B] : k4_xboole_0(A,k2_xboole_0(A,B)) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).

tff(f_57,axiom,(
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

tff(f_42,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

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

tff(c_2,plain,(
    ! [A_1] : k2_xboole_0(A_1,A_1) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_339,plain,(
    ! [A_89,B_90] : k4_xboole_0(A_89,k2_xboole_0(A_89,B_90)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_346,plain,(
    ! [A_1] : k4_xboole_0(A_1,A_1) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_339])).

tff(c_34,plain,(
    ! [B_32] : k4_xboole_0(k1_tarski(B_32),k1_tarski(B_32)) != k1_tarski(B_32) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_406,plain,(
    ! [B_32] : k1_tarski(B_32) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_346,c_34])).

tff(c_378,plain,(
    ! [A_94] :
      ( r2_hidden('#skF_3'(A_94),A_94)
      | k1_xboole_0 = A_94 ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_12,plain,(
    ! [C_15,A_11] :
      ( C_15 = A_11
      | ~ r2_hidden(C_15,k1_tarski(A_11)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_383,plain,(
    ! [A_11] :
      ( '#skF_3'(k1_tarski(A_11)) = A_11
      | k1_tarski(A_11) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_378,c_12])).

tff(c_437,plain,(
    ! [A_11] : '#skF_3'(k1_tarski(A_11)) = A_11 ),
    inference(negUnitSimplification,[status(thm)],[c_406,c_383])).

tff(c_14,plain,(
    ! [C_15] : r2_hidden(C_15,k1_tarski(C_15)) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_534,plain,(
    ! [D_118,A_119,C_120] :
      ( ~ r2_hidden(D_118,A_119)
      | k4_tarski(C_120,D_118) != '#skF_3'(A_119)
      | k1_xboole_0 = A_119 ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_538,plain,(
    ! [C_120,C_15] :
      ( k4_tarski(C_120,C_15) != '#skF_3'(k1_tarski(C_15))
      | k1_tarski(C_15) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_14,c_534])).

tff(c_541,plain,(
    ! [C_120,C_15] :
      ( k4_tarski(C_120,C_15) != C_15
      | k1_tarski(C_15) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_437,c_538])).

tff(c_542,plain,(
    ! [C_120,C_15] : k4_tarski(C_120,C_15) != C_15 ),
    inference(negUnitSimplification,[status(thm)],[c_406,c_541])).

tff(c_147,plain,(
    ! [A_59,B_60] : k4_xboole_0(A_59,k2_xboole_0(A_59,B_60)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_154,plain,(
    ! [A_1] : k4_xboole_0(A_1,A_1) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_147])).

tff(c_179,plain,(
    ! [B_32] : k1_tarski(B_32) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_154,c_34])).

tff(c_157,plain,(
    ! [A_61] :
      ( r2_hidden('#skF_3'(A_61),A_61)
      | k1_xboole_0 = A_61 ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_162,plain,(
    ! [A_11] :
      ( '#skF_3'(k1_tarski(A_11)) = A_11
      | k1_tarski(A_11) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_157,c_12])).

tff(c_203,plain,(
    ! [A_11] : '#skF_3'(k1_tarski(A_11)) = A_11 ),
    inference(negUnitSimplification,[status(thm)],[c_179,c_162])).

tff(c_316,plain,(
    ! [C_84,A_85,D_86] :
      ( ~ r2_hidden(C_84,A_85)
      | k4_tarski(C_84,D_86) != '#skF_3'(A_85)
      | k1_xboole_0 = A_85 ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_320,plain,(
    ! [C_15,D_86] :
      ( k4_tarski(C_15,D_86) != '#skF_3'(k1_tarski(C_15))
      | k1_tarski(C_15) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_14,c_316])).

tff(c_323,plain,(
    ! [C_15,D_86] :
      ( k4_tarski(C_15,D_86) != C_15
      | k1_tarski(C_15) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_203,c_320])).

tff(c_324,plain,(
    ! [C_15,D_86] : k4_tarski(C_15,D_86) != C_15 ),
    inference(negUnitSimplification,[status(thm)],[c_179,c_323])).

tff(c_52,plain,(
    k4_tarski('#skF_5','#skF_6') = '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_88,plain,(
    ! [A_54,B_55] : k1_mcart_1(k4_tarski(A_54,B_55)) = A_54 ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_97,plain,(
    k1_mcart_1('#skF_4') = '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_52,c_88])).

tff(c_76,plain,(
    ! [A_52,B_53] : k2_mcart_1(k4_tarski(A_52,B_53)) = B_53 ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_85,plain,(
    k2_mcart_1('#skF_4') = '#skF_6' ),
    inference(superposition,[status(thm),theory(equality)],[c_52,c_76])).

tff(c_50,plain,
    ( k2_mcart_1('#skF_4') = '#skF_4'
    | k1_mcart_1('#skF_4') = '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_117,plain,
    ( '#skF_6' = '#skF_4'
    | '#skF_5' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_97,c_85,c_50])).

tff(c_118,plain,(
    '#skF_5' = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_117])).

tff(c_120,plain,(
    k4_tarski('#skF_4','#skF_6') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_118,c_52])).

tff(c_330,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_324,c_120])).

tff(c_331,plain,(
    '#skF_6' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_117])).

tff(c_334,plain,(
    k4_tarski('#skF_5','#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_331,c_52])).

tff(c_544,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_542,c_334])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:39:32 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.35/1.42  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.35/1.42  
% 2.35/1.42  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.35/1.43  %$ r2_hidden > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k2_mcart_1 > k1_tarski > k1_setfam_1 > k1_mcart_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_4 > #skF_3 > #skF_2 > #skF_1
% 2.35/1.43  
% 2.35/1.43  %Foreground sorts:
% 2.35/1.43  
% 2.35/1.43  
% 2.35/1.43  %Background operators:
% 2.35/1.43  
% 2.35/1.43  
% 2.35/1.43  %Foreground operators:
% 2.35/1.43  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.35/1.43  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.35/1.43  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.35/1.43  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.35/1.43  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.35/1.43  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.35/1.43  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.35/1.43  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.35/1.43  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.35/1.43  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.35/1.43  tff('#skF_5', type, '#skF_5': $i).
% 2.35/1.43  tff('#skF_6', type, '#skF_6': $i).
% 2.35/1.43  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.35/1.43  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.35/1.43  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.35/1.43  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 2.35/1.43  tff('#skF_4', type, '#skF_4': $i).
% 2.35/1.43  tff('#skF_3', type, '#skF_3': $i > $i).
% 2.35/1.43  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.35/1.43  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.35/1.43  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 2.35/1.43  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.35/1.43  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.35/1.43  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.35/1.43  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.35/1.43  
% 2.35/1.44  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k2_xboole_0)).
% 2.35/1.44  tff(f_33, axiom, (![A, B]: (k4_xboole_0(A, k2_xboole_0(A, B)) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_xboole_1)).
% 2.35/1.44  tff(f_57, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) <=> ~(A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_zfmisc_1)).
% 2.35/1.44  tff(f_79, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~(r2_hidden(B, A) & (![C, D]: ~((r2_hidden(C, A) | r2_hidden(D, A)) & (B = k4_tarski(C, D)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t9_mcart_1)).
% 2.35/1.44  tff(f_42, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 2.35/1.44  tff(f_89, negated_conjecture, ~(![A]: ((?[B, C]: (A = k4_tarski(B, C))) => (~(A = k1_mcart_1(A)) & ~(A = k2_mcart_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_mcart_1)).
% 2.35/1.44  tff(f_63, axiom, (![A, B]: ((k1_mcart_1(k4_tarski(A, B)) = A) & (k2_mcart_1(k4_tarski(A, B)) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_mcart_1)).
% 2.35/1.44  tff(c_2, plain, (![A_1]: (k2_xboole_0(A_1, A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.35/1.44  tff(c_339, plain, (![A_89, B_90]: (k4_xboole_0(A_89, k2_xboole_0(A_89, B_90))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.35/1.44  tff(c_346, plain, (![A_1]: (k4_xboole_0(A_1, A_1)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2, c_339])).
% 2.35/1.44  tff(c_34, plain, (![B_32]: (k4_xboole_0(k1_tarski(B_32), k1_tarski(B_32))!=k1_tarski(B_32))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.35/1.44  tff(c_406, plain, (![B_32]: (k1_tarski(B_32)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_346, c_34])).
% 2.35/1.44  tff(c_378, plain, (![A_94]: (r2_hidden('#skF_3'(A_94), A_94) | k1_xboole_0=A_94)), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.35/1.44  tff(c_12, plain, (![C_15, A_11]: (C_15=A_11 | ~r2_hidden(C_15, k1_tarski(A_11)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.35/1.44  tff(c_383, plain, (![A_11]: ('#skF_3'(k1_tarski(A_11))=A_11 | k1_tarski(A_11)=k1_xboole_0)), inference(resolution, [status(thm)], [c_378, c_12])).
% 2.35/1.44  tff(c_437, plain, (![A_11]: ('#skF_3'(k1_tarski(A_11))=A_11)), inference(negUnitSimplification, [status(thm)], [c_406, c_383])).
% 2.35/1.44  tff(c_14, plain, (![C_15]: (r2_hidden(C_15, k1_tarski(C_15)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.35/1.44  tff(c_534, plain, (![D_118, A_119, C_120]: (~r2_hidden(D_118, A_119) | k4_tarski(C_120, D_118)!='#skF_3'(A_119) | k1_xboole_0=A_119)), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.35/1.44  tff(c_538, plain, (![C_120, C_15]: (k4_tarski(C_120, C_15)!='#skF_3'(k1_tarski(C_15)) | k1_tarski(C_15)=k1_xboole_0)), inference(resolution, [status(thm)], [c_14, c_534])).
% 2.35/1.44  tff(c_541, plain, (![C_120, C_15]: (k4_tarski(C_120, C_15)!=C_15 | k1_tarski(C_15)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_437, c_538])).
% 2.35/1.44  tff(c_542, plain, (![C_120, C_15]: (k4_tarski(C_120, C_15)!=C_15)), inference(negUnitSimplification, [status(thm)], [c_406, c_541])).
% 2.35/1.44  tff(c_147, plain, (![A_59, B_60]: (k4_xboole_0(A_59, k2_xboole_0(A_59, B_60))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.35/1.44  tff(c_154, plain, (![A_1]: (k4_xboole_0(A_1, A_1)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2, c_147])).
% 2.35/1.44  tff(c_179, plain, (![B_32]: (k1_tarski(B_32)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_154, c_34])).
% 2.35/1.44  tff(c_157, plain, (![A_61]: (r2_hidden('#skF_3'(A_61), A_61) | k1_xboole_0=A_61)), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.35/1.44  tff(c_162, plain, (![A_11]: ('#skF_3'(k1_tarski(A_11))=A_11 | k1_tarski(A_11)=k1_xboole_0)), inference(resolution, [status(thm)], [c_157, c_12])).
% 2.35/1.44  tff(c_203, plain, (![A_11]: ('#skF_3'(k1_tarski(A_11))=A_11)), inference(negUnitSimplification, [status(thm)], [c_179, c_162])).
% 2.35/1.44  tff(c_316, plain, (![C_84, A_85, D_86]: (~r2_hidden(C_84, A_85) | k4_tarski(C_84, D_86)!='#skF_3'(A_85) | k1_xboole_0=A_85)), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.35/1.44  tff(c_320, plain, (![C_15, D_86]: (k4_tarski(C_15, D_86)!='#skF_3'(k1_tarski(C_15)) | k1_tarski(C_15)=k1_xboole_0)), inference(resolution, [status(thm)], [c_14, c_316])).
% 2.35/1.44  tff(c_323, plain, (![C_15, D_86]: (k4_tarski(C_15, D_86)!=C_15 | k1_tarski(C_15)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_203, c_320])).
% 2.35/1.44  tff(c_324, plain, (![C_15, D_86]: (k4_tarski(C_15, D_86)!=C_15)), inference(negUnitSimplification, [status(thm)], [c_179, c_323])).
% 2.35/1.44  tff(c_52, plain, (k4_tarski('#skF_5', '#skF_6')='#skF_4'), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.35/1.44  tff(c_88, plain, (![A_54, B_55]: (k1_mcart_1(k4_tarski(A_54, B_55))=A_54)), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.35/1.44  tff(c_97, plain, (k1_mcart_1('#skF_4')='#skF_5'), inference(superposition, [status(thm), theory('equality')], [c_52, c_88])).
% 2.35/1.44  tff(c_76, plain, (![A_52, B_53]: (k2_mcart_1(k4_tarski(A_52, B_53))=B_53)), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.35/1.44  tff(c_85, plain, (k2_mcart_1('#skF_4')='#skF_6'), inference(superposition, [status(thm), theory('equality')], [c_52, c_76])).
% 2.35/1.44  tff(c_50, plain, (k2_mcart_1('#skF_4')='#skF_4' | k1_mcart_1('#skF_4')='#skF_4'), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.35/1.44  tff(c_117, plain, ('#skF_6'='#skF_4' | '#skF_5'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_97, c_85, c_50])).
% 2.35/1.44  tff(c_118, plain, ('#skF_5'='#skF_4'), inference(splitLeft, [status(thm)], [c_117])).
% 2.35/1.44  tff(c_120, plain, (k4_tarski('#skF_4', '#skF_6')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_118, c_52])).
% 2.35/1.44  tff(c_330, plain, $false, inference(negUnitSimplification, [status(thm)], [c_324, c_120])).
% 2.35/1.44  tff(c_331, plain, ('#skF_6'='#skF_4'), inference(splitRight, [status(thm)], [c_117])).
% 2.35/1.44  tff(c_334, plain, (k4_tarski('#skF_5', '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_331, c_52])).
% 2.35/1.44  tff(c_544, plain, $false, inference(negUnitSimplification, [status(thm)], [c_542, c_334])).
% 2.35/1.44  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.35/1.44  
% 2.35/1.44  Inference rules
% 2.35/1.44  ----------------------
% 2.35/1.44  #Ref     : 0
% 2.35/1.44  #Sup     : 118
% 2.35/1.44  #Fact    : 0
% 2.35/1.44  #Define  : 0
% 2.35/1.44  #Split   : 1
% 2.35/1.44  #Chain   : 0
% 2.35/1.44  #Close   : 0
% 2.35/1.44  
% 2.35/1.44  Ordering : KBO
% 2.35/1.44  
% 2.35/1.44  Simplification rules
% 2.35/1.44  ----------------------
% 2.35/1.44  #Subsume      : 2
% 2.35/1.44  #Demod        : 24
% 2.35/1.44  #Tautology    : 92
% 2.35/1.44  #SimpNegUnit  : 14
% 2.35/1.44  #BackRed      : 6
% 2.35/1.44  
% 2.35/1.44  #Partial instantiations: 0
% 2.35/1.44  #Strategies tried      : 1
% 2.35/1.44  
% 2.35/1.44  Timing (in seconds)
% 2.35/1.44  ----------------------
% 2.35/1.44  Preprocessing        : 0.31
% 2.35/1.44  Parsing              : 0.16
% 2.35/1.44  CNF conversion       : 0.02
% 2.35/1.45  Main loop            : 0.30
% 2.35/1.45  Inferencing          : 0.12
% 2.35/1.45  Reduction            : 0.10
% 2.35/1.45  Demodulation         : 0.06
% 2.35/1.45  BG Simplification    : 0.02
% 2.35/1.45  Subsumption          : 0.04
% 2.35/1.45  Abstraction          : 0.02
% 2.35/1.45  MUC search           : 0.00
% 2.35/1.45  Cooper               : 0.00
% 2.35/1.45  Total                : 0.65
% 2.35/1.45  Index Insertion      : 0.00
% 2.35/1.45  Index Deletion       : 0.00
% 2.35/1.45  Index Matching       : 0.00
% 2.35/1.45  BG Taut test         : 0.00
%------------------------------------------------------------------------------
