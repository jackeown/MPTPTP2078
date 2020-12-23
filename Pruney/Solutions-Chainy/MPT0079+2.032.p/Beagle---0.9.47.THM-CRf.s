%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:43:46 EST 2020

% Result     : Theorem 12.40s
% Output     : CNFRefutation 12.54s
% Verified   : 
% Statistics : Number of formulae       :   83 ( 162 expanded)
%              Number of leaves         :   25 (  64 expanded)
%              Depth                    :   12
%              Number of atoms          :   79 ( 174 expanded)
%              Number of equality atoms :   60 ( 142 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

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

tff(f_86,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( k2_xboole_0(A,B) = k2_xboole_0(C,D)
          & r1_xboole_0(C,A)
          & r1_xboole_0(D,B) )
       => C = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_41,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

tff(f_47,axiom,(
    ! [A,B] : k4_xboole_0(A,k2_xboole_0(A,B)) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).

tff(f_45,axiom,(
    ! [A,B,C] : k4_xboole_0(k4_xboole_0(A,B),C) = k4_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_49,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_77,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_51,axiom,(
    ! [A,B,C] : k2_xboole_0(k2_xboole_0(A,B),C) = k2_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_1)).

tff(c_34,plain,(
    '#skF_2' != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_12,plain,(
    ! [A_9] : k2_xboole_0(A_9,k1_xboole_0) = A_9 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_180,plain,(
    ! [A_40,B_41] : k4_xboole_0(A_40,k2_xboole_0(A_40,B_41)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_193,plain,(
    ! [A_1,B_2] : k4_xboole_0(A_1,k2_xboole_0(B_2,A_1)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_180])).

tff(c_1358,plain,(
    ! [A_90,B_91,C_92] : k4_xboole_0(k4_xboole_0(A_90,B_91),C_92) = k4_xboole_0(A_90,k2_xboole_0(B_91,C_92)) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_14,plain,(
    ! [A_10,B_11] : k2_xboole_0(A_10,k4_xboole_0(B_11,A_10)) = k2_xboole_0(A_10,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_19541,plain,(
    ! [C_274,A_275,B_276] : k2_xboole_0(C_274,k4_xboole_0(A_275,k2_xboole_0(B_276,C_274))) = k2_xboole_0(C_274,k4_xboole_0(A_275,B_276)) ),
    inference(superposition,[status(thm),theory(equality)],[c_1358,c_14])).

tff(c_19949,plain,(
    ! [A_1,B_2] : k2_xboole_0(A_1,k4_xboole_0(A_1,B_2)) = k2_xboole_0(A_1,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_193,c_19541])).

tff(c_20074,plain,(
    ! [A_1,B_2] : k2_xboole_0(A_1,k4_xboole_0(A_1,B_2)) = A_1 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_19949])).

tff(c_38,plain,(
    r1_xboole_0('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_390,plain,(
    ! [A_51,B_52] :
      ( k3_xboole_0(A_51,B_52) = k1_xboole_0
      | ~ r1_xboole_0(A_51,B_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_406,plain,(
    k3_xboole_0('#skF_3','#skF_1') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_38,c_390])).

tff(c_769,plain,(
    ! [A_69,B_70] : k4_xboole_0(A_69,k4_xboole_0(A_69,B_70)) = k3_xboole_0(A_69,B_70) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_778,plain,(
    ! [A_69,B_70] : k2_xboole_0(k4_xboole_0(A_69,B_70),k3_xboole_0(A_69,B_70)) = k2_xboole_0(k4_xboole_0(A_69,B_70),A_69) ),
    inference(superposition,[status(thm),theory(equality)],[c_769,c_14])).

tff(c_18424,plain,(
    ! [A_268,B_269] : k2_xboole_0(k4_xboole_0(A_268,B_269),k3_xboole_0(A_268,B_269)) = k2_xboole_0(A_268,k4_xboole_0(A_268,B_269)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_778])).

tff(c_18734,plain,(
    k2_xboole_0(k4_xboole_0('#skF_3','#skF_1'),k1_xboole_0) = k2_xboole_0('#skF_3',k4_xboole_0('#skF_3','#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_406,c_18424])).

tff(c_18831,plain,(
    k2_xboole_0('#skF_3',k4_xboole_0('#skF_3','#skF_1')) = k4_xboole_0('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_18734])).

tff(c_22628,plain,(
    k4_xboole_0('#skF_3','#skF_1') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_20074,c_18831])).

tff(c_40,plain,(
    k2_xboole_0('#skF_3','#skF_4') = k2_xboole_0('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_41,plain,(
    k2_xboole_0('#skF_1','#skF_2') = k2_xboole_0('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_40])).

tff(c_20696,plain,(
    ! [A_279] : k2_xboole_0('#skF_2',k4_xboole_0(A_279,k2_xboole_0('#skF_4','#skF_3'))) = k2_xboole_0('#skF_2',k4_xboole_0(A_279,'#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_41,c_19541])).

tff(c_20916,plain,(
    k2_xboole_0('#skF_2',k4_xboole_0('#skF_3','#skF_1')) = k2_xboole_0('#skF_2',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_193,c_20696])).

tff(c_20973,plain,(
    k2_xboole_0('#skF_2',k4_xboole_0('#skF_3','#skF_1')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_20916])).

tff(c_22699,plain,(
    k2_xboole_0('#skF_3','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_22628,c_20973])).

tff(c_55,plain,(
    ! [B_33,A_34] : k2_xboole_0(B_33,A_34) = k2_xboole_0(A_34,B_33) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_77,plain,(
    ! [A_34] : k2_xboole_0(k1_xboole_0,A_34) = A_34 ),
    inference(superposition,[status(thm),theory(equality)],[c_55,c_12])).

tff(c_190,plain,(
    ! [A_34] : k4_xboole_0(k1_xboole_0,A_34) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_77,c_180])).

tff(c_36,plain,(
    r1_xboole_0('#skF_4','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_233,plain,(
    ! [B_44,A_45] :
      ( r1_xboole_0(B_44,A_45)
      | ~ r1_xboole_0(A_45,B_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_238,plain,(
    r1_xboole_0('#skF_2','#skF_4') ),
    inference(resolution,[status(thm)],[c_36,c_233])).

tff(c_404,plain,(
    k3_xboole_0('#skF_2','#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_238,c_390])).

tff(c_51,plain,(
    ! [A_31,B_32] : r1_tarski(A_31,k2_xboole_0(A_31,B_32)) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_54,plain,(
    ! [A_9] : r1_tarski(A_9,A_9) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_51])).

tff(c_291,plain,(
    ! [A_48,B_49] :
      ( k2_xboole_0(A_48,B_49) = B_49
      | ~ r1_tarski(A_48,B_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_315,plain,(
    ! [A_9] : k2_xboole_0(A_9,A_9) = A_9 ),
    inference(resolution,[status(thm)],[c_54,c_291])).

tff(c_248,plain,(
    ! [A_46,B_47] : k4_xboole_0(A_46,k2_xboole_0(B_47,A_46)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_180])).

tff(c_267,plain,(
    k4_xboole_0('#skF_2',k2_xboole_0('#skF_4','#skF_3')) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_41,c_248])).

tff(c_19940,plain,(
    k2_xboole_0('#skF_3',k4_xboole_0('#skF_2','#skF_4')) = k2_xboole_0('#skF_3',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_267,c_19541])).

tff(c_20071,plain,(
    k2_xboole_0('#skF_3',k4_xboole_0('#skF_2','#skF_4')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_19940])).

tff(c_32,plain,(
    ! [A_28,B_29] : r1_tarski(A_28,k2_xboole_0(A_28,B_29)) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_70,plain,(
    ! [A_34,B_33] : r1_tarski(A_34,k2_xboole_0(B_33,A_34)) ),
    inference(superposition,[status(thm),theory(equality)],[c_55,c_32])).

tff(c_6166,plain,(
    ! [A_181,B_182] : k2_xboole_0(A_181,k2_xboole_0(B_182,A_181)) = k2_xboole_0(B_182,A_181) ),
    inference(resolution,[status(thm)],[c_70,c_291])).

tff(c_6465,plain,(
    ! [A_1,B_2] : k2_xboole_0(A_1,k2_xboole_0(A_1,B_2)) = k2_xboole_0(B_2,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_6166])).

tff(c_25154,plain,(
    k2_xboole_0(k4_xboole_0('#skF_2','#skF_4'),'#skF_3') = k2_xboole_0('#skF_3','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_20071,c_6465])).

tff(c_25297,plain,(
    k2_xboole_0(k4_xboole_0('#skF_2','#skF_4'),'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_315,c_25154])).

tff(c_20,plain,(
    ! [A_17,B_18] : k4_xboole_0(A_17,k4_xboole_0(A_17,B_18)) = k3_xboole_0(A_17,B_18) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_1402,plain,(
    ! [A_17,B_18,C_92] : k4_xboole_0(A_17,k2_xboole_0(k4_xboole_0(A_17,B_18),C_92)) = k4_xboole_0(k3_xboole_0(A_17,B_18),C_92) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_1358])).

tff(c_26362,plain,(
    k4_xboole_0(k3_xboole_0('#skF_2','#skF_4'),'#skF_3') = k4_xboole_0('#skF_2','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_25297,c_1402])).

tff(c_26541,plain,(
    k4_xboole_0('#skF_2','#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_190,c_404,c_26362])).

tff(c_1009,plain,(
    ! [A_79,B_80,C_81] : k2_xboole_0(k2_xboole_0(A_79,B_80),C_81) = k2_xboole_0(A_79,k2_xboole_0(B_80,C_81)) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_3606,plain,(
    ! [A_148,A_146,B_147] : k2_xboole_0(A_148,k2_xboole_0(A_146,B_147)) = k2_xboole_0(A_146,k2_xboole_0(B_147,A_148)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_1009])).

tff(c_5859,plain,(
    ! [A_179,A_180] : k2_xboole_0(k1_xboole_0,k2_xboole_0(A_179,A_180)) = k2_xboole_0(A_180,A_179) ),
    inference(superposition,[status(thm),theory(equality)],[c_77,c_3606])).

tff(c_6075,plain,(
    ! [B_11,A_10] : k2_xboole_0(k4_xboole_0(B_11,A_10),A_10) = k2_xboole_0(k1_xboole_0,k2_xboole_0(A_10,B_11)) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_5859])).

tff(c_6157,plain,(
    ! [B_11,A_10] : k2_xboole_0(k4_xboole_0(B_11,A_10),A_10) = k2_xboole_0(A_10,B_11) ),
    inference(demodulation,[status(thm),theory(equality)],[c_77,c_6075])).

tff(c_26617,plain,(
    k2_xboole_0(k1_xboole_0,'#skF_3') = k2_xboole_0('#skF_3','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_26541,c_6157])).

tff(c_26656,plain,(
    '#skF_2' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_22699,c_77,c_26617])).

tff(c_26658,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_26656])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n002.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 19:32:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 12.40/5.14  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 12.40/5.15  
% 12.40/5.15  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 12.40/5.15  %$ r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 12.40/5.15  
% 12.40/5.15  %Foreground sorts:
% 12.40/5.15  
% 12.40/5.15  
% 12.40/5.15  %Background operators:
% 12.40/5.15  
% 12.40/5.15  
% 12.40/5.15  %Foreground operators:
% 12.40/5.15  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 12.40/5.15  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 12.40/5.15  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 12.40/5.15  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 12.40/5.15  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 12.40/5.15  tff('#skF_2', type, '#skF_2': $i).
% 12.40/5.15  tff('#skF_3', type, '#skF_3': $i).
% 12.40/5.15  tff('#skF_1', type, '#skF_1': $i).
% 12.40/5.15  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 12.40/5.15  tff('#skF_4', type, '#skF_4': $i).
% 12.40/5.15  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 12.40/5.15  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 12.40/5.15  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 12.40/5.15  
% 12.54/5.17  tff(f_86, negated_conjecture, ~(![A, B, C, D]: ((((k2_xboole_0(A, B) = k2_xboole_0(C, D)) & r1_xboole_0(C, A)) & r1_xboole_0(D, B)) => (C = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_xboole_1)).
% 12.54/5.17  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 12.54/5.17  tff(f_41, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 12.54/5.17  tff(f_47, axiom, (![A, B]: (k4_xboole_0(A, k2_xboole_0(A, B)) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_xboole_1)).
% 12.54/5.17  tff(f_45, axiom, (![A, B, C]: (k4_xboole_0(k4_xboole_0(A, B), C) = k4_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_xboole_1)).
% 12.54/5.17  tff(f_43, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 12.54/5.17  tff(f_31, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 12.54/5.17  tff(f_49, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 12.54/5.17  tff(f_35, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 12.54/5.17  tff(f_77, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 12.54/5.17  tff(f_39, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 12.54/5.17  tff(f_51, axiom, (![A, B, C]: (k2_xboole_0(k2_xboole_0(A, B), C) = k2_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_1)).
% 12.54/5.17  tff(c_34, plain, ('#skF_2'!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_86])).
% 12.54/5.17  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 12.54/5.17  tff(c_12, plain, (![A_9]: (k2_xboole_0(A_9, k1_xboole_0)=A_9)), inference(cnfTransformation, [status(thm)], [f_41])).
% 12.54/5.17  tff(c_180, plain, (![A_40, B_41]: (k4_xboole_0(A_40, k2_xboole_0(A_40, B_41))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_47])).
% 12.54/5.17  tff(c_193, plain, (![A_1, B_2]: (k4_xboole_0(A_1, k2_xboole_0(B_2, A_1))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2, c_180])).
% 12.54/5.17  tff(c_1358, plain, (![A_90, B_91, C_92]: (k4_xboole_0(k4_xboole_0(A_90, B_91), C_92)=k4_xboole_0(A_90, k2_xboole_0(B_91, C_92)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 12.54/5.17  tff(c_14, plain, (![A_10, B_11]: (k2_xboole_0(A_10, k4_xboole_0(B_11, A_10))=k2_xboole_0(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_43])).
% 12.54/5.17  tff(c_19541, plain, (![C_274, A_275, B_276]: (k2_xboole_0(C_274, k4_xboole_0(A_275, k2_xboole_0(B_276, C_274)))=k2_xboole_0(C_274, k4_xboole_0(A_275, B_276)))), inference(superposition, [status(thm), theory('equality')], [c_1358, c_14])).
% 12.54/5.17  tff(c_19949, plain, (![A_1, B_2]: (k2_xboole_0(A_1, k4_xboole_0(A_1, B_2))=k2_xboole_0(A_1, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_193, c_19541])).
% 12.54/5.17  tff(c_20074, plain, (![A_1, B_2]: (k2_xboole_0(A_1, k4_xboole_0(A_1, B_2))=A_1)), inference(demodulation, [status(thm), theory('equality')], [c_12, c_19949])).
% 12.54/5.17  tff(c_38, plain, (r1_xboole_0('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_86])).
% 12.54/5.17  tff(c_390, plain, (![A_51, B_52]: (k3_xboole_0(A_51, B_52)=k1_xboole_0 | ~r1_xboole_0(A_51, B_52))), inference(cnfTransformation, [status(thm)], [f_31])).
% 12.54/5.17  tff(c_406, plain, (k3_xboole_0('#skF_3', '#skF_1')=k1_xboole_0), inference(resolution, [status(thm)], [c_38, c_390])).
% 12.54/5.17  tff(c_769, plain, (![A_69, B_70]: (k4_xboole_0(A_69, k4_xboole_0(A_69, B_70))=k3_xboole_0(A_69, B_70))), inference(cnfTransformation, [status(thm)], [f_49])).
% 12.54/5.17  tff(c_778, plain, (![A_69, B_70]: (k2_xboole_0(k4_xboole_0(A_69, B_70), k3_xboole_0(A_69, B_70))=k2_xboole_0(k4_xboole_0(A_69, B_70), A_69))), inference(superposition, [status(thm), theory('equality')], [c_769, c_14])).
% 12.54/5.17  tff(c_18424, plain, (![A_268, B_269]: (k2_xboole_0(k4_xboole_0(A_268, B_269), k3_xboole_0(A_268, B_269))=k2_xboole_0(A_268, k4_xboole_0(A_268, B_269)))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_778])).
% 12.54/5.17  tff(c_18734, plain, (k2_xboole_0(k4_xboole_0('#skF_3', '#skF_1'), k1_xboole_0)=k2_xboole_0('#skF_3', k4_xboole_0('#skF_3', '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_406, c_18424])).
% 12.54/5.17  tff(c_18831, plain, (k2_xboole_0('#skF_3', k4_xboole_0('#skF_3', '#skF_1'))=k4_xboole_0('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_12, c_18734])).
% 12.54/5.17  tff(c_22628, plain, (k4_xboole_0('#skF_3', '#skF_1')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_20074, c_18831])).
% 12.54/5.17  tff(c_40, plain, (k2_xboole_0('#skF_3', '#skF_4')=k2_xboole_0('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_86])).
% 12.54/5.17  tff(c_41, plain, (k2_xboole_0('#skF_1', '#skF_2')=k2_xboole_0('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_40])).
% 12.54/5.17  tff(c_20696, plain, (![A_279]: (k2_xboole_0('#skF_2', k4_xboole_0(A_279, k2_xboole_0('#skF_4', '#skF_3')))=k2_xboole_0('#skF_2', k4_xboole_0(A_279, '#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_41, c_19541])).
% 12.54/5.17  tff(c_20916, plain, (k2_xboole_0('#skF_2', k4_xboole_0('#skF_3', '#skF_1'))=k2_xboole_0('#skF_2', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_193, c_20696])).
% 12.54/5.17  tff(c_20973, plain, (k2_xboole_0('#skF_2', k4_xboole_0('#skF_3', '#skF_1'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_12, c_20916])).
% 12.54/5.17  tff(c_22699, plain, (k2_xboole_0('#skF_3', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_2, c_22628, c_20973])).
% 12.54/5.17  tff(c_55, plain, (![B_33, A_34]: (k2_xboole_0(B_33, A_34)=k2_xboole_0(A_34, B_33))), inference(cnfTransformation, [status(thm)], [f_27])).
% 12.54/5.17  tff(c_77, plain, (![A_34]: (k2_xboole_0(k1_xboole_0, A_34)=A_34)), inference(superposition, [status(thm), theory('equality')], [c_55, c_12])).
% 12.54/5.17  tff(c_190, plain, (![A_34]: (k4_xboole_0(k1_xboole_0, A_34)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_77, c_180])).
% 12.54/5.17  tff(c_36, plain, (r1_xboole_0('#skF_4', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_86])).
% 12.54/5.17  tff(c_233, plain, (![B_44, A_45]: (r1_xboole_0(B_44, A_45) | ~r1_xboole_0(A_45, B_44))), inference(cnfTransformation, [status(thm)], [f_35])).
% 12.54/5.17  tff(c_238, plain, (r1_xboole_0('#skF_2', '#skF_4')), inference(resolution, [status(thm)], [c_36, c_233])).
% 12.54/5.17  tff(c_404, plain, (k3_xboole_0('#skF_2', '#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_238, c_390])).
% 12.54/5.17  tff(c_51, plain, (![A_31, B_32]: (r1_tarski(A_31, k2_xboole_0(A_31, B_32)))), inference(cnfTransformation, [status(thm)], [f_77])).
% 12.54/5.17  tff(c_54, plain, (![A_9]: (r1_tarski(A_9, A_9))), inference(superposition, [status(thm), theory('equality')], [c_12, c_51])).
% 12.54/5.17  tff(c_291, plain, (![A_48, B_49]: (k2_xboole_0(A_48, B_49)=B_49 | ~r1_tarski(A_48, B_49))), inference(cnfTransformation, [status(thm)], [f_39])).
% 12.54/5.17  tff(c_315, plain, (![A_9]: (k2_xboole_0(A_9, A_9)=A_9)), inference(resolution, [status(thm)], [c_54, c_291])).
% 12.54/5.17  tff(c_248, plain, (![A_46, B_47]: (k4_xboole_0(A_46, k2_xboole_0(B_47, A_46))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2, c_180])).
% 12.54/5.17  tff(c_267, plain, (k4_xboole_0('#skF_2', k2_xboole_0('#skF_4', '#skF_3'))=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_41, c_248])).
% 12.54/5.17  tff(c_19940, plain, (k2_xboole_0('#skF_3', k4_xboole_0('#skF_2', '#skF_4'))=k2_xboole_0('#skF_3', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_267, c_19541])).
% 12.54/5.17  tff(c_20071, plain, (k2_xboole_0('#skF_3', k4_xboole_0('#skF_2', '#skF_4'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_12, c_19940])).
% 12.54/5.17  tff(c_32, plain, (![A_28, B_29]: (r1_tarski(A_28, k2_xboole_0(A_28, B_29)))), inference(cnfTransformation, [status(thm)], [f_77])).
% 12.54/5.17  tff(c_70, plain, (![A_34, B_33]: (r1_tarski(A_34, k2_xboole_0(B_33, A_34)))), inference(superposition, [status(thm), theory('equality')], [c_55, c_32])).
% 12.54/5.17  tff(c_6166, plain, (![A_181, B_182]: (k2_xboole_0(A_181, k2_xboole_0(B_182, A_181))=k2_xboole_0(B_182, A_181))), inference(resolution, [status(thm)], [c_70, c_291])).
% 12.54/5.17  tff(c_6465, plain, (![A_1, B_2]: (k2_xboole_0(A_1, k2_xboole_0(A_1, B_2))=k2_xboole_0(B_2, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_6166])).
% 12.54/5.17  tff(c_25154, plain, (k2_xboole_0(k4_xboole_0('#skF_2', '#skF_4'), '#skF_3')=k2_xboole_0('#skF_3', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_20071, c_6465])).
% 12.54/5.17  tff(c_25297, plain, (k2_xboole_0(k4_xboole_0('#skF_2', '#skF_4'), '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_315, c_25154])).
% 12.54/5.17  tff(c_20, plain, (![A_17, B_18]: (k4_xboole_0(A_17, k4_xboole_0(A_17, B_18))=k3_xboole_0(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_49])).
% 12.54/5.17  tff(c_1402, plain, (![A_17, B_18, C_92]: (k4_xboole_0(A_17, k2_xboole_0(k4_xboole_0(A_17, B_18), C_92))=k4_xboole_0(k3_xboole_0(A_17, B_18), C_92))), inference(superposition, [status(thm), theory('equality')], [c_20, c_1358])).
% 12.54/5.17  tff(c_26362, plain, (k4_xboole_0(k3_xboole_0('#skF_2', '#skF_4'), '#skF_3')=k4_xboole_0('#skF_2', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_25297, c_1402])).
% 12.54/5.17  tff(c_26541, plain, (k4_xboole_0('#skF_2', '#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_190, c_404, c_26362])).
% 12.54/5.17  tff(c_1009, plain, (![A_79, B_80, C_81]: (k2_xboole_0(k2_xboole_0(A_79, B_80), C_81)=k2_xboole_0(A_79, k2_xboole_0(B_80, C_81)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 12.54/5.17  tff(c_3606, plain, (![A_148, A_146, B_147]: (k2_xboole_0(A_148, k2_xboole_0(A_146, B_147))=k2_xboole_0(A_146, k2_xboole_0(B_147, A_148)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_1009])).
% 12.54/5.17  tff(c_5859, plain, (![A_179, A_180]: (k2_xboole_0(k1_xboole_0, k2_xboole_0(A_179, A_180))=k2_xboole_0(A_180, A_179))), inference(superposition, [status(thm), theory('equality')], [c_77, c_3606])).
% 12.54/5.17  tff(c_6075, plain, (![B_11, A_10]: (k2_xboole_0(k4_xboole_0(B_11, A_10), A_10)=k2_xboole_0(k1_xboole_0, k2_xboole_0(A_10, B_11)))), inference(superposition, [status(thm), theory('equality')], [c_14, c_5859])).
% 12.54/5.17  tff(c_6157, plain, (![B_11, A_10]: (k2_xboole_0(k4_xboole_0(B_11, A_10), A_10)=k2_xboole_0(A_10, B_11))), inference(demodulation, [status(thm), theory('equality')], [c_77, c_6075])).
% 12.54/5.17  tff(c_26617, plain, (k2_xboole_0(k1_xboole_0, '#skF_3')=k2_xboole_0('#skF_3', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_26541, c_6157])).
% 12.54/5.17  tff(c_26656, plain, ('#skF_2'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_22699, c_77, c_26617])).
% 12.54/5.17  tff(c_26658, plain, $false, inference(negUnitSimplification, [status(thm)], [c_34, c_26656])).
% 12.54/5.17  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 12.54/5.17  
% 12.54/5.17  Inference rules
% 12.54/5.17  ----------------------
% 12.54/5.17  #Ref     : 1
% 12.54/5.17  #Sup     : 6813
% 12.54/5.17  #Fact    : 0
% 12.54/5.17  #Define  : 0
% 12.54/5.17  #Split   : 11
% 12.54/5.17  #Chain   : 0
% 12.54/5.17  #Close   : 0
% 12.54/5.17  
% 12.54/5.17  Ordering : KBO
% 12.54/5.17  
% 12.54/5.17  Simplification rules
% 12.54/5.17  ----------------------
% 12.54/5.17  #Subsume      : 661
% 12.54/5.17  #Demod        : 6954
% 12.54/5.17  #Tautology    : 3527
% 12.54/5.17  #SimpNegUnit  : 56
% 12.54/5.17  #BackRed      : 26
% 12.54/5.17  
% 12.54/5.17  #Partial instantiations: 0
% 12.54/5.17  #Strategies tried      : 1
% 12.54/5.17  
% 12.54/5.17  Timing (in seconds)
% 12.54/5.17  ----------------------
% 12.54/5.17  Preprocessing        : 0.32
% 12.54/5.17  Parsing              : 0.18
% 12.54/5.17  CNF conversion       : 0.02
% 12.54/5.17  Main loop            : 4.05
% 12.54/5.17  Inferencing          : 0.67
% 12.54/5.17  Reduction            : 2.43
% 12.54/5.17  Demodulation         : 2.14
% 12.54/5.17  BG Simplification    : 0.08
% 12.54/5.17  Subsumption          : 0.66
% 12.54/5.17  Abstraction          : 0.12
% 12.54/5.17  MUC search           : 0.00
% 12.54/5.17  Cooper               : 0.00
% 12.54/5.17  Total                : 4.40
% 12.54/5.17  Index Insertion      : 0.00
% 12.54/5.17  Index Deletion       : 0.00
% 12.54/5.17  Index Matching       : 0.00
% 12.54/5.17  BG Taut test         : 0.00
%------------------------------------------------------------------------------
