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
% DateTime   : Thu Dec  3 09:51:04 EST 2020

% Result     : Theorem 7.31s
% Output     : CNFRefutation 7.46s
% Verified   : 
% Statistics : Number of formulae       :   64 (  75 expanded)
%              Number of leaves         :   35 (  41 expanded)
%              Depth                    :    9
%              Number of atoms          :   55 (  73 expanded)
%              Number of equality atoms :   29 (  37 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(f_86,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r1_tarski(k2_xboole_0(k2_tarski(A,B),C),C)
       => r2_hidden(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_zfmisc_1)).

tff(f_69,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_67,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

tff(f_48,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_52,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_46,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k5_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

tff(f_50,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_38,axiom,(
    ! [A,B,C] :
      ( C = k2_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            | r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).

tff(c_76,plain,(
    ~ r2_hidden('#skF_5','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_160,plain,(
    ! [A_76,B_77] : k1_enumset1(A_76,A_76,B_77) = k2_tarski(A_76,B_77) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_42,plain,(
    ! [E_28,A_22,C_24] : r2_hidden(E_28,k1_enumset1(A_22,E_28,C_24)) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_169,plain,(
    ! [A_76,B_77] : r2_hidden(A_76,k2_tarski(A_76,B_77)) ),
    inference(superposition,[status(thm),theory(equality)],[c_160,c_42])).

tff(c_32,plain,(
    ! [A_15,B_16] : r1_tarski(A_15,k2_xboole_0(A_15,B_16)) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_36,plain,(
    ! [A_20,B_21] : k5_xboole_0(A_20,k4_xboole_0(B_21,A_20)) = k2_xboole_0(A_20,B_21) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_204,plain,(
    ! [A_89,B_90] : k5_xboole_0(A_89,k3_xboole_0(A_89,B_90)) = k4_xboole_0(A_89,B_90) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_213,plain,(
    ! [A_1,B_2] : k5_xboole_0(A_1,k3_xboole_0(B_2,A_1)) = k4_xboole_0(A_1,B_2) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_204])).

tff(c_4,plain,(
    ! [B_4,A_3] : k5_xboole_0(B_4,A_3) = k5_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_30,plain,(
    ! [A_13,B_14] : k5_xboole_0(A_13,k3_xboole_0(A_13,B_14)) = k4_xboole_0(A_13,B_14) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_259,plain,(
    ! [A_101,B_102,C_103] : k5_xboole_0(k5_xboole_0(A_101,B_102),C_103) = k5_xboole_0(A_101,k5_xboole_0(B_102,C_103)) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_2790,plain,(
    ! [A_188,B_189,C_190] : k5_xboole_0(A_188,k5_xboole_0(k3_xboole_0(A_188,B_189),C_190)) = k5_xboole_0(k4_xboole_0(A_188,B_189),C_190) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_259])).

tff(c_3559,plain,(
    ! [A_200,A_201,B_202] : k5_xboole_0(A_200,k5_xboole_0(A_201,k3_xboole_0(A_200,B_202))) = k5_xboole_0(k4_xboole_0(A_200,B_202),A_201) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_2790])).

tff(c_3729,plain,(
    ! [B_2,A_1] : k5_xboole_0(k4_xboole_0(B_2,A_1),A_1) = k5_xboole_0(B_2,k4_xboole_0(A_1,B_2)) ),
    inference(superposition,[status(thm),theory(equality)],[c_213,c_3559])).

tff(c_3776,plain,(
    ! [B_203,A_204] : k5_xboole_0(k4_xboole_0(B_203,A_204),A_204) = k2_xboole_0(B_203,A_204) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_3729])).

tff(c_4008,plain,(
    ! [A_208,B_209] : k5_xboole_0(A_208,k4_xboole_0(B_209,A_208)) = k2_xboole_0(B_209,A_208) ),
    inference(superposition,[status(thm),theory(equality)],[c_3776,c_4])).

tff(c_4080,plain,(
    ! [B_209,A_208] : k2_xboole_0(B_209,A_208) = k2_xboole_0(A_208,B_209) ),
    inference(superposition,[status(thm),theory(equality)],[c_4008,c_36])).

tff(c_78,plain,(
    r1_tarski(k2_xboole_0(k2_tarski('#skF_5','#skF_6'),'#skF_7'),'#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_191,plain,(
    ! [B_87,A_88] :
      ( B_87 = A_88
      | ~ r1_tarski(B_87,A_88)
      | ~ r1_tarski(A_88,B_87) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_198,plain,
    ( k2_xboole_0(k2_tarski('#skF_5','#skF_6'),'#skF_7') = '#skF_7'
    | ~ r1_tarski('#skF_7',k2_xboole_0(k2_tarski('#skF_5','#skF_6'),'#skF_7')) ),
    inference(resolution,[status(thm)],[c_78,c_191])).

tff(c_220,plain,(
    ~ r1_tarski('#skF_7',k2_xboole_0(k2_tarski('#skF_5','#skF_6'),'#skF_7')) ),
    inference(splitLeft,[status(thm)],[c_198])).

tff(c_4111,plain,(
    ~ r1_tarski('#skF_7',k2_xboole_0('#skF_7',k2_tarski('#skF_5','#skF_6'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4080,c_220])).

tff(c_4115,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_4111])).

tff(c_4116,plain,(
    k2_xboole_0(k2_tarski('#skF_5','#skF_6'),'#skF_7') = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_198])).

tff(c_10,plain,(
    ! [D_10,A_5,B_6] :
      ( ~ r2_hidden(D_10,A_5)
      | r2_hidden(D_10,k2_xboole_0(A_5,B_6)) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_4174,plain,(
    ! [D_215] :
      ( ~ r2_hidden(D_215,k2_tarski('#skF_5','#skF_6'))
      | r2_hidden(D_215,'#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4116,c_10])).

tff(c_4178,plain,(
    r2_hidden('#skF_5','#skF_7') ),
    inference(resolution,[status(thm)],[c_169,c_4174])).

tff(c_4186,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_4178])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n023.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.36  % CPULimit   : 60
% 0.14/0.36  % DateTime   : Tue Dec  1 19:50:50 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.21/0.37  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.31/2.51  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.31/2.51  
% 7.31/2.51  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.31/2.52  %$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3
% 7.31/2.52  
% 7.31/2.52  %Foreground sorts:
% 7.31/2.52  
% 7.31/2.52  
% 7.31/2.52  %Background operators:
% 7.31/2.52  
% 7.31/2.52  
% 7.31/2.52  %Foreground operators:
% 7.31/2.52  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 7.31/2.52  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.31/2.52  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 7.31/2.52  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 7.31/2.52  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 7.31/2.52  tff('#skF_7', type, '#skF_7': $i).
% 7.31/2.52  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 7.31/2.52  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.31/2.52  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 7.31/2.52  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 7.31/2.52  tff('#skF_5', type, '#skF_5': $i).
% 7.31/2.52  tff('#skF_6', type, '#skF_6': $i).
% 7.31/2.52  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 7.31/2.52  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 7.31/2.52  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 7.31/2.52  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i) > $i).
% 7.31/2.52  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 7.31/2.52  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.31/2.52  tff(k3_tarski, type, k3_tarski: $i > $i).
% 7.31/2.52  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.31/2.52  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 7.31/2.52  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 7.31/2.52  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 7.31/2.52  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 7.31/2.52  
% 7.46/2.53  tff(f_86, negated_conjecture, ~(![A, B, C]: (r1_tarski(k2_xboole_0(k2_tarski(A, B), C), C) => r2_hidden(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_zfmisc_1)).
% 7.46/2.53  tff(f_69, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 7.46/2.53  tff(f_67, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_enumset1)).
% 7.46/2.53  tff(f_48, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 7.46/2.53  tff(f_52, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_xboole_1)).
% 7.46/2.53  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 7.46/2.53  tff(f_46, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 7.46/2.53  tff(f_29, axiom, (![A, B]: (k5_xboole_0(A, B) = k5_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 7.46/2.53  tff(f_50, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_xboole_1)).
% 7.46/2.53  tff(f_44, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 7.46/2.53  tff(f_38, axiom, (![A, B, C]: ((C = k2_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) | r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_xboole_0)).
% 7.46/2.53  tff(c_76, plain, (~r2_hidden('#skF_5', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_86])).
% 7.46/2.53  tff(c_160, plain, (![A_76, B_77]: (k1_enumset1(A_76, A_76, B_77)=k2_tarski(A_76, B_77))), inference(cnfTransformation, [status(thm)], [f_69])).
% 7.46/2.53  tff(c_42, plain, (![E_28, A_22, C_24]: (r2_hidden(E_28, k1_enumset1(A_22, E_28, C_24)))), inference(cnfTransformation, [status(thm)], [f_67])).
% 7.46/2.53  tff(c_169, plain, (![A_76, B_77]: (r2_hidden(A_76, k2_tarski(A_76, B_77)))), inference(superposition, [status(thm), theory('equality')], [c_160, c_42])).
% 7.46/2.53  tff(c_32, plain, (![A_15, B_16]: (r1_tarski(A_15, k2_xboole_0(A_15, B_16)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 7.46/2.53  tff(c_36, plain, (![A_20, B_21]: (k5_xboole_0(A_20, k4_xboole_0(B_21, A_20))=k2_xboole_0(A_20, B_21))), inference(cnfTransformation, [status(thm)], [f_52])).
% 7.46/2.53  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 7.46/2.53  tff(c_204, plain, (![A_89, B_90]: (k5_xboole_0(A_89, k3_xboole_0(A_89, B_90))=k4_xboole_0(A_89, B_90))), inference(cnfTransformation, [status(thm)], [f_46])).
% 7.46/2.53  tff(c_213, plain, (![A_1, B_2]: (k5_xboole_0(A_1, k3_xboole_0(B_2, A_1))=k4_xboole_0(A_1, B_2))), inference(superposition, [status(thm), theory('equality')], [c_2, c_204])).
% 7.46/2.53  tff(c_4, plain, (![B_4, A_3]: (k5_xboole_0(B_4, A_3)=k5_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 7.46/2.53  tff(c_30, plain, (![A_13, B_14]: (k5_xboole_0(A_13, k3_xboole_0(A_13, B_14))=k4_xboole_0(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_46])).
% 7.46/2.53  tff(c_259, plain, (![A_101, B_102, C_103]: (k5_xboole_0(k5_xboole_0(A_101, B_102), C_103)=k5_xboole_0(A_101, k5_xboole_0(B_102, C_103)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 7.46/2.53  tff(c_2790, plain, (![A_188, B_189, C_190]: (k5_xboole_0(A_188, k5_xboole_0(k3_xboole_0(A_188, B_189), C_190))=k5_xboole_0(k4_xboole_0(A_188, B_189), C_190))), inference(superposition, [status(thm), theory('equality')], [c_30, c_259])).
% 7.46/2.53  tff(c_3559, plain, (![A_200, A_201, B_202]: (k5_xboole_0(A_200, k5_xboole_0(A_201, k3_xboole_0(A_200, B_202)))=k5_xboole_0(k4_xboole_0(A_200, B_202), A_201))), inference(superposition, [status(thm), theory('equality')], [c_4, c_2790])).
% 7.46/2.53  tff(c_3729, plain, (![B_2, A_1]: (k5_xboole_0(k4_xboole_0(B_2, A_1), A_1)=k5_xboole_0(B_2, k4_xboole_0(A_1, B_2)))), inference(superposition, [status(thm), theory('equality')], [c_213, c_3559])).
% 7.46/2.53  tff(c_3776, plain, (![B_203, A_204]: (k5_xboole_0(k4_xboole_0(B_203, A_204), A_204)=k2_xboole_0(B_203, A_204))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_3729])).
% 7.46/2.53  tff(c_4008, plain, (![A_208, B_209]: (k5_xboole_0(A_208, k4_xboole_0(B_209, A_208))=k2_xboole_0(B_209, A_208))), inference(superposition, [status(thm), theory('equality')], [c_3776, c_4])).
% 7.46/2.53  tff(c_4080, plain, (![B_209, A_208]: (k2_xboole_0(B_209, A_208)=k2_xboole_0(A_208, B_209))), inference(superposition, [status(thm), theory('equality')], [c_4008, c_36])).
% 7.46/2.53  tff(c_78, plain, (r1_tarski(k2_xboole_0(k2_tarski('#skF_5', '#skF_6'), '#skF_7'), '#skF_7')), inference(cnfTransformation, [status(thm)], [f_86])).
% 7.46/2.53  tff(c_191, plain, (![B_87, A_88]: (B_87=A_88 | ~r1_tarski(B_87, A_88) | ~r1_tarski(A_88, B_87))), inference(cnfTransformation, [status(thm)], [f_44])).
% 7.46/2.53  tff(c_198, plain, (k2_xboole_0(k2_tarski('#skF_5', '#skF_6'), '#skF_7')='#skF_7' | ~r1_tarski('#skF_7', k2_xboole_0(k2_tarski('#skF_5', '#skF_6'), '#skF_7'))), inference(resolution, [status(thm)], [c_78, c_191])).
% 7.46/2.53  tff(c_220, plain, (~r1_tarski('#skF_7', k2_xboole_0(k2_tarski('#skF_5', '#skF_6'), '#skF_7'))), inference(splitLeft, [status(thm)], [c_198])).
% 7.46/2.53  tff(c_4111, plain, (~r1_tarski('#skF_7', k2_xboole_0('#skF_7', k2_tarski('#skF_5', '#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_4080, c_220])).
% 7.46/2.53  tff(c_4115, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_32, c_4111])).
% 7.46/2.53  tff(c_4116, plain, (k2_xboole_0(k2_tarski('#skF_5', '#skF_6'), '#skF_7')='#skF_7'), inference(splitRight, [status(thm)], [c_198])).
% 7.46/2.53  tff(c_10, plain, (![D_10, A_5, B_6]: (~r2_hidden(D_10, A_5) | r2_hidden(D_10, k2_xboole_0(A_5, B_6)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 7.46/2.53  tff(c_4174, plain, (![D_215]: (~r2_hidden(D_215, k2_tarski('#skF_5', '#skF_6')) | r2_hidden(D_215, '#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_4116, c_10])).
% 7.46/2.53  tff(c_4178, plain, (r2_hidden('#skF_5', '#skF_7')), inference(resolution, [status(thm)], [c_169, c_4174])).
% 7.46/2.53  tff(c_4186, plain, $false, inference(negUnitSimplification, [status(thm)], [c_76, c_4178])).
% 7.46/2.53  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.46/2.53  
% 7.46/2.53  Inference rules
% 7.46/2.53  ----------------------
% 7.46/2.53  #Ref     : 0
% 7.46/2.53  #Sup     : 1054
% 7.46/2.53  #Fact    : 4
% 7.46/2.53  #Define  : 0
% 7.46/2.53  #Split   : 1
% 7.46/2.53  #Chain   : 0
% 7.46/2.53  #Close   : 0
% 7.46/2.53  
% 7.46/2.53  Ordering : KBO
% 7.46/2.53  
% 7.46/2.53  Simplification rules
% 7.46/2.53  ----------------------
% 7.46/2.53  #Subsume      : 160
% 7.46/2.53  #Demod        : 555
% 7.46/2.53  #Tautology    : 196
% 7.46/2.53  #SimpNegUnit  : 1
% 7.46/2.53  #BackRed      : 3
% 7.46/2.53  
% 7.46/2.53  #Partial instantiations: 0
% 7.46/2.53  #Strategies tried      : 1
% 7.46/2.53  
% 7.46/2.53  Timing (in seconds)
% 7.46/2.53  ----------------------
% 7.46/2.53  Preprocessing        : 0.34
% 7.46/2.53  Parsing              : 0.18
% 7.46/2.53  CNF conversion       : 0.03
% 7.46/2.53  Main loop            : 1.36
% 7.46/2.53  Inferencing          : 0.31
% 7.46/2.53  Reduction            : 0.80
% 7.46/2.53  Demodulation         : 0.73
% 7.46/2.53  BG Simplification    : 0.06
% 7.46/2.53  Subsumption          : 0.15
% 7.46/2.53  Abstraction          : 0.07
% 7.46/2.53  MUC search           : 0.00
% 7.46/2.53  Cooper               : 0.00
% 7.46/2.53  Total                : 1.73
% 7.46/2.53  Index Insertion      : 0.00
% 7.46/2.53  Index Deletion       : 0.00
% 7.46/2.53  Index Matching       : 0.00
% 7.46/2.53  BG Taut test         : 0.00
%------------------------------------------------------------------------------
