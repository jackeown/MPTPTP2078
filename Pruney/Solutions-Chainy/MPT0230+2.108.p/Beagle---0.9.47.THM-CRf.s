%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:49:09 EST 2020

% Result     : Theorem 3.26s
% Output     : CNFRefutation 3.31s
% Verified   : 
% Statistics : Number of formulae       :   68 (  82 expanded)
%              Number of leaves         :   35 (  44 expanded)
%              Depth                    :   10
%              Number of atoms          :   60 (  84 expanded)
%              Number of equality atoms :   50 (  70 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1

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

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i ) > $i )).

tff(f_88,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( r1_tarski(k1_tarski(A),k2_tarski(B,C))
          & A != B
          & A != C ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_zfmisc_1)).

tff(f_68,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_66,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_62,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k1_enumset1(A,B,C),k1_tarski(D)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_enumset1)).

tff(f_39,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

tff(f_35,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_29,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_33,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_41,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_56,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

tff(c_64,plain,(
    '#skF_3' != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_62,plain,(
    '#skF_5' != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_50,plain,(
    ! [A_38,B_39,C_40] : k2_enumset1(A_38,A_38,B_39,C_40) = k1_enumset1(A_38,B_39,C_40) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_48,plain,(
    ! [A_36,B_37] : k1_enumset1(A_36,A_36,B_37) = k2_tarski(A_36,B_37) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_1114,plain,(
    ! [A_135,B_136,C_137,D_138] : k2_xboole_0(k1_enumset1(A_135,B_136,C_137),k1_tarski(D_138)) = k2_enumset1(A_135,B_136,C_137,D_138) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_1153,plain,(
    ! [A_36,B_37,D_138] : k2_xboole_0(k2_tarski(A_36,B_37),k1_tarski(D_138)) = k2_enumset1(A_36,A_36,B_37,D_138) ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_1114])).

tff(c_1157,plain,(
    ! [A_139,B_140,D_141] : k2_xboole_0(k2_tarski(A_139,B_140),k1_tarski(D_141)) = k1_enumset1(A_139,B_140,D_141) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_1153])).

tff(c_12,plain,(
    ! [A_10] : k5_xboole_0(A_10,k1_xboole_0) = A_10 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_8,plain,(
    ! [A_7] : k3_xboole_0(A_7,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_157,plain,(
    ! [A_90,B_91] : k5_xboole_0(A_90,k3_xboole_0(A_90,B_91)) = k4_xboole_0(A_90,B_91) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_166,plain,(
    ! [A_7] : k5_xboole_0(A_7,k1_xboole_0) = k4_xboole_0(A_7,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_157])).

tff(c_172,plain,(
    ! [A_7] : k4_xboole_0(A_7,k1_xboole_0) = A_7 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_166])).

tff(c_394,plain,(
    ! [A_100,B_101] : k4_xboole_0(A_100,k4_xboole_0(A_100,B_101)) = k3_xboole_0(A_100,B_101) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_415,plain,(
    ! [A_7] : k4_xboole_0(A_7,A_7) = k3_xboole_0(A_7,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_172,c_394])).

tff(c_419,plain,(
    ! [A_7] : k4_xboole_0(A_7,A_7) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_415])).

tff(c_2,plain,(
    ! [A_1] : k3_xboole_0(A_1,A_1) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_169,plain,(
    ! [A_1] : k5_xboole_0(A_1,A_1) = k4_xboole_0(A_1,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_157])).

tff(c_66,plain,(
    r1_tarski(k1_tarski('#skF_3'),k2_tarski('#skF_4','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_114,plain,(
    ! [A_79,B_80] :
      ( k3_xboole_0(A_79,B_80) = A_79
      | ~ r1_tarski(A_79,B_80) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_118,plain,(
    k3_xboole_0(k1_tarski('#skF_3'),k2_tarski('#skF_4','#skF_5')) = k1_tarski('#skF_3') ),
    inference(resolution,[status(thm)],[c_66,c_114])).

tff(c_4,plain,(
    ! [A_3,B_4] : k5_xboole_0(A_3,k3_xboole_0(A_3,B_4)) = k4_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_188,plain,(
    k5_xboole_0(k1_tarski('#skF_3'),k1_tarski('#skF_3')) = k4_xboole_0(k1_tarski('#skF_3'),k2_tarski('#skF_4','#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_118,c_4])).

tff(c_384,plain,(
    k4_xboole_0(k1_tarski('#skF_3'),k2_tarski('#skF_4','#skF_5')) = k4_xboole_0(k1_tarski('#skF_3'),k1_tarski('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_169,c_188])).

tff(c_14,plain,(
    ! [A_11,B_12] : k5_xboole_0(A_11,k4_xboole_0(B_12,A_11)) = k2_xboole_0(A_11,B_12) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_388,plain,(
    k5_xboole_0(k2_tarski('#skF_4','#skF_5'),k4_xboole_0(k1_tarski('#skF_3'),k1_tarski('#skF_3'))) = k2_xboole_0(k2_tarski('#skF_4','#skF_5'),k1_tarski('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_384,c_14])).

tff(c_817,plain,(
    k2_xboole_0(k2_tarski('#skF_4','#skF_5'),k1_tarski('#skF_3')) = k2_tarski('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_419,c_388])).

tff(c_1163,plain,(
    k1_enumset1('#skF_4','#skF_5','#skF_3') = k2_tarski('#skF_4','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_1157,c_817])).

tff(c_18,plain,(
    ! [E_19,A_13,B_14] : r2_hidden(E_19,k1_enumset1(A_13,B_14,E_19)) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_1197,plain,(
    r2_hidden('#skF_3',k2_tarski('#skF_4','#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1163,c_18])).

tff(c_1044,plain,(
    ! [E_126,C_127,B_128,A_129] :
      ( E_126 = C_127
      | E_126 = B_128
      | E_126 = A_129
      | ~ r2_hidden(E_126,k1_enumset1(A_129,B_128,C_127)) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_1077,plain,(
    ! [E_126,B_37,A_36] :
      ( E_126 = B_37
      | E_126 = A_36
      | E_126 = A_36
      | ~ r2_hidden(E_126,k2_tarski(A_36,B_37)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_1044])).

tff(c_1212,plain,
    ( '#skF_5' = '#skF_3'
    | '#skF_3' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_1197,c_1077])).

tff(c_1216,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_64,c_62,c_1212])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n006.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 14:58:07 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.26/1.46  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.26/1.46  
% 3.26/1.47  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.31/1.47  %$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 3.31/1.47  
% 3.31/1.47  %Foreground sorts:
% 3.31/1.47  
% 3.31/1.47  
% 3.31/1.47  %Background operators:
% 3.31/1.47  
% 3.31/1.47  
% 3.31/1.47  %Foreground operators:
% 3.31/1.47  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.31/1.47  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.31/1.47  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.31/1.47  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.31/1.47  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.31/1.47  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.31/1.47  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.31/1.47  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.31/1.47  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.31/1.47  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.31/1.47  tff('#skF_5', type, '#skF_5': $i).
% 3.31/1.47  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 3.31/1.47  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.31/1.47  tff('#skF_3', type, '#skF_3': $i).
% 3.31/1.47  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.31/1.47  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.31/1.47  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.31/1.47  tff('#skF_4', type, '#skF_4': $i).
% 3.31/1.47  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.31/1.47  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.31/1.47  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.31/1.47  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.31/1.47  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 3.31/1.47  
% 3.31/1.48  tff(f_88, negated_conjecture, ~(![A, B, C]: ~((r1_tarski(k1_tarski(A), k2_tarski(B, C)) & ~(A = B)) & ~(A = C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t25_zfmisc_1)).
% 3.31/1.48  tff(f_68, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 3.31/1.48  tff(f_66, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 3.31/1.48  tff(f_62, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k1_enumset1(A, B, C), k1_tarski(D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_enumset1)).
% 3.31/1.48  tff(f_39, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 3.31/1.48  tff(f_35, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 3.31/1.48  tff(f_29, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 3.31/1.48  tff(f_37, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 3.31/1.48  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 3.31/1.48  tff(f_33, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 3.31/1.48  tff(f_41, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_xboole_1)).
% 3.31/1.48  tff(f_56, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_enumset1)).
% 3.31/1.48  tff(c_64, plain, ('#skF_3'!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.31/1.48  tff(c_62, plain, ('#skF_5'!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.31/1.48  tff(c_50, plain, (![A_38, B_39, C_40]: (k2_enumset1(A_38, A_38, B_39, C_40)=k1_enumset1(A_38, B_39, C_40))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.31/1.48  tff(c_48, plain, (![A_36, B_37]: (k1_enumset1(A_36, A_36, B_37)=k2_tarski(A_36, B_37))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.31/1.48  tff(c_1114, plain, (![A_135, B_136, C_137, D_138]: (k2_xboole_0(k1_enumset1(A_135, B_136, C_137), k1_tarski(D_138))=k2_enumset1(A_135, B_136, C_137, D_138))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.31/1.48  tff(c_1153, plain, (![A_36, B_37, D_138]: (k2_xboole_0(k2_tarski(A_36, B_37), k1_tarski(D_138))=k2_enumset1(A_36, A_36, B_37, D_138))), inference(superposition, [status(thm), theory('equality')], [c_48, c_1114])).
% 3.31/1.48  tff(c_1157, plain, (![A_139, B_140, D_141]: (k2_xboole_0(k2_tarski(A_139, B_140), k1_tarski(D_141))=k1_enumset1(A_139, B_140, D_141))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_1153])).
% 3.31/1.48  tff(c_12, plain, (![A_10]: (k5_xboole_0(A_10, k1_xboole_0)=A_10)), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.31/1.48  tff(c_8, plain, (![A_7]: (k3_xboole_0(A_7, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.31/1.48  tff(c_157, plain, (![A_90, B_91]: (k5_xboole_0(A_90, k3_xboole_0(A_90, B_91))=k4_xboole_0(A_90, B_91))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.31/1.48  tff(c_166, plain, (![A_7]: (k5_xboole_0(A_7, k1_xboole_0)=k4_xboole_0(A_7, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_8, c_157])).
% 3.31/1.48  tff(c_172, plain, (![A_7]: (k4_xboole_0(A_7, k1_xboole_0)=A_7)), inference(demodulation, [status(thm), theory('equality')], [c_12, c_166])).
% 3.31/1.48  tff(c_394, plain, (![A_100, B_101]: (k4_xboole_0(A_100, k4_xboole_0(A_100, B_101))=k3_xboole_0(A_100, B_101))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.31/1.48  tff(c_415, plain, (![A_7]: (k4_xboole_0(A_7, A_7)=k3_xboole_0(A_7, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_172, c_394])).
% 3.31/1.48  tff(c_419, plain, (![A_7]: (k4_xboole_0(A_7, A_7)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_8, c_415])).
% 3.31/1.48  tff(c_2, plain, (![A_1]: (k3_xboole_0(A_1, A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.31/1.48  tff(c_169, plain, (![A_1]: (k5_xboole_0(A_1, A_1)=k4_xboole_0(A_1, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_157])).
% 3.31/1.48  tff(c_66, plain, (r1_tarski(k1_tarski('#skF_3'), k2_tarski('#skF_4', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.31/1.48  tff(c_114, plain, (![A_79, B_80]: (k3_xboole_0(A_79, B_80)=A_79 | ~r1_tarski(A_79, B_80))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.31/1.48  tff(c_118, plain, (k3_xboole_0(k1_tarski('#skF_3'), k2_tarski('#skF_4', '#skF_5'))=k1_tarski('#skF_3')), inference(resolution, [status(thm)], [c_66, c_114])).
% 3.31/1.48  tff(c_4, plain, (![A_3, B_4]: (k5_xboole_0(A_3, k3_xboole_0(A_3, B_4))=k4_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.31/1.48  tff(c_188, plain, (k5_xboole_0(k1_tarski('#skF_3'), k1_tarski('#skF_3'))=k4_xboole_0(k1_tarski('#skF_3'), k2_tarski('#skF_4', '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_118, c_4])).
% 3.31/1.48  tff(c_384, plain, (k4_xboole_0(k1_tarski('#skF_3'), k2_tarski('#skF_4', '#skF_5'))=k4_xboole_0(k1_tarski('#skF_3'), k1_tarski('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_169, c_188])).
% 3.31/1.48  tff(c_14, plain, (![A_11, B_12]: (k5_xboole_0(A_11, k4_xboole_0(B_12, A_11))=k2_xboole_0(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.31/1.48  tff(c_388, plain, (k5_xboole_0(k2_tarski('#skF_4', '#skF_5'), k4_xboole_0(k1_tarski('#skF_3'), k1_tarski('#skF_3')))=k2_xboole_0(k2_tarski('#skF_4', '#skF_5'), k1_tarski('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_384, c_14])).
% 3.31/1.48  tff(c_817, plain, (k2_xboole_0(k2_tarski('#skF_4', '#skF_5'), k1_tarski('#skF_3'))=k2_tarski('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_12, c_419, c_388])).
% 3.31/1.48  tff(c_1163, plain, (k1_enumset1('#skF_4', '#skF_5', '#skF_3')=k2_tarski('#skF_4', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_1157, c_817])).
% 3.31/1.48  tff(c_18, plain, (![E_19, A_13, B_14]: (r2_hidden(E_19, k1_enumset1(A_13, B_14, E_19)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.31/1.48  tff(c_1197, plain, (r2_hidden('#skF_3', k2_tarski('#skF_4', '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_1163, c_18])).
% 3.31/1.48  tff(c_1044, plain, (![E_126, C_127, B_128, A_129]: (E_126=C_127 | E_126=B_128 | E_126=A_129 | ~r2_hidden(E_126, k1_enumset1(A_129, B_128, C_127)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.31/1.48  tff(c_1077, plain, (![E_126, B_37, A_36]: (E_126=B_37 | E_126=A_36 | E_126=A_36 | ~r2_hidden(E_126, k2_tarski(A_36, B_37)))), inference(superposition, [status(thm), theory('equality')], [c_48, c_1044])).
% 3.31/1.48  tff(c_1212, plain, ('#skF_5'='#skF_3' | '#skF_3'='#skF_4'), inference(resolution, [status(thm)], [c_1197, c_1077])).
% 3.31/1.48  tff(c_1216, plain, $false, inference(negUnitSimplification, [status(thm)], [c_64, c_64, c_62, c_1212])).
% 3.31/1.48  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.31/1.48  
% 3.31/1.48  Inference rules
% 3.31/1.48  ----------------------
% 3.31/1.48  #Ref     : 0
% 3.31/1.48  #Sup     : 295
% 3.31/1.48  #Fact    : 0
% 3.31/1.48  #Define  : 0
% 3.31/1.48  #Split   : 0
% 3.31/1.48  #Chain   : 0
% 3.31/1.48  #Close   : 0
% 3.31/1.48  
% 3.31/1.48  Ordering : KBO
% 3.31/1.48  
% 3.31/1.48  Simplification rules
% 3.31/1.48  ----------------------
% 3.31/1.48  #Subsume      : 50
% 3.31/1.48  #Demod        : 127
% 3.31/1.48  #Tautology    : 191
% 3.31/1.48  #SimpNegUnit  : 1
% 3.31/1.48  #BackRed      : 2
% 3.31/1.48  
% 3.31/1.48  #Partial instantiations: 0
% 3.31/1.48  #Strategies tried      : 1
% 3.31/1.48  
% 3.31/1.48  Timing (in seconds)
% 3.31/1.48  ----------------------
% 3.31/1.48  Preprocessing        : 0.33
% 3.31/1.48  Parsing              : 0.17
% 3.31/1.48  CNF conversion       : 0.02
% 3.31/1.48  Main loop            : 0.38
% 3.31/1.48  Inferencing          : 0.13
% 3.31/1.48  Reduction            : 0.15
% 3.31/1.48  Demodulation         : 0.12
% 3.31/1.48  BG Simplification    : 0.02
% 3.31/1.48  Subsumption          : 0.06
% 3.31/1.48  Abstraction          : 0.02
% 3.31/1.48  MUC search           : 0.00
% 3.31/1.48  Cooper               : 0.00
% 3.31/1.49  Total                : 0.74
% 3.31/1.49  Index Insertion      : 0.00
% 3.31/1.49  Index Deletion       : 0.00
% 3.31/1.49  Index Matching       : 0.00
% 3.31/1.49  BG Taut test         : 0.00
%------------------------------------------------------------------------------
