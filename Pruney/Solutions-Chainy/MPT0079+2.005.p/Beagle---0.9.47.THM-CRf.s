%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:43:43 EST 2020

% Result     : Theorem 8.77s
% Output     : CNFRefutation 8.77s
% Verified   : 
% Statistics : Number of formulae       :   88 ( 377 expanded)
%              Number of leaves         :   30 ( 144 expanded)
%              Depth                    :   15
%              Number of atoms          :   82 ( 439 expanded)
%              Number of equality atoms :   68 ( 354 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_82,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( k2_xboole_0(A,B) = k2_xboole_0(C,D)
          & r1_xboole_0(C,A)
          & r1_xboole_0(D,B) )
       => C = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_xboole_1)).

tff(f_61,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_53,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_45,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_67,axiom,(
    ! [A,B] : k4_xboole_0(A,k3_xboole_0(A,B)) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).

tff(f_63,axiom,(
    ! [A,B] : k4_xboole_0(k2_xboole_0(A,B),B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_73,axiom,(
    ! [A,B] : k2_xboole_0(k3_xboole_0(A,B),k4_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_xboole_1)).

tff(f_59,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_69,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] : k2_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

tff(f_71,axiom,(
    ! [A,B,C] : k2_xboole_0(k2_xboole_0(A,B),C) = k2_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_1)).

tff(f_65,axiom,(
    ! [A,B,C] : k4_xboole_0(k4_xboole_0(A,B),C) = k4_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

tff(c_34,plain,(
    '#skF_5' != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_20,plain,(
    ! [A_18] : k4_xboole_0(A_18,k1_xboole_0) = A_18 ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_36,plain,(
    r1_xboole_0('#skF_6','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_12,plain,(
    ! [A_12] :
      ( r2_hidden('#skF_2'(A_12),A_12)
      | k1_xboole_0 = A_12 ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_728,plain,(
    ! [A_61,B_62,C_63] :
      ( ~ r1_xboole_0(A_61,B_62)
      | ~ r2_hidden(C_63,k3_xboole_0(A_61,B_62)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_1194,plain,(
    ! [A_75,B_76] :
      ( ~ r1_xboole_0(A_75,B_76)
      | k3_xboole_0(A_75,B_76) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_12,c_728])).

tff(c_1206,plain,(
    k3_xboole_0('#skF_6','#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_36,c_1194])).

tff(c_1269,plain,(
    ! [A_77,B_78] : k4_xboole_0(A_77,k3_xboole_0(A_77,B_78)) = k4_xboole_0(A_77,B_78) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_1297,plain,(
    k4_xboole_0('#skF_6',k1_xboole_0) = k4_xboole_0('#skF_6','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1206,c_1269])).

tff(c_1318,plain,(
    k4_xboole_0('#skF_6','#skF_4') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_1297])).

tff(c_156,plain,(
    ! [A_44,B_45] : k4_xboole_0(k2_xboole_0(A_44,B_45),B_45) = k4_xboole_0(A_44,B_45) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_163,plain,(
    ! [A_44] : k4_xboole_0(A_44,k1_xboole_0) = k2_xboole_0(A_44,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_156,c_20])).

tff(c_187,plain,(
    ! [A_44] : k2_xboole_0(A_44,k1_xboole_0) = A_44 ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_163])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_40,plain,(
    k2_xboole_0('#skF_5','#skF_6') = k2_xboole_0('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_41,plain,(
    k2_xboole_0('#skF_5','#skF_6') = k2_xboole_0('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_40])).

tff(c_32,plain,(
    ! [A_31,B_32] : k2_xboole_0(k3_xboole_0(A_31,B_32),k4_xboole_0(A_31,B_32)) = A_31 ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_18,plain,(
    ! [A_16,B_17] : k2_xboole_0(A_16,k4_xboole_0(B_17,A_16)) = k2_xboole_0(A_16,B_17) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_1282,plain,(
    ! [A_77,B_78] : k2_xboole_0(k3_xboole_0(A_77,B_78),k4_xboole_0(A_77,B_78)) = k2_xboole_0(k3_xboole_0(A_77,B_78),A_77) ),
    inference(superposition,[status(thm),theory(equality)],[c_1269,c_18])).

tff(c_1897,plain,(
    ! [A_85,B_86] : k2_xboole_0(A_85,k3_xboole_0(A_85,B_86)) = A_85 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_32,c_1282])).

tff(c_191,plain,(
    ! [A_46] : k2_xboole_0(A_46,k1_xboole_0) = A_46 ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_163])).

tff(c_214,plain,(
    ! [A_1] : k2_xboole_0(k1_xboole_0,A_1) = A_1 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_191])).

tff(c_1915,plain,(
    ! [B_86] : k3_xboole_0(k1_xboole_0,B_86) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_1897,c_214])).

tff(c_4,plain,(
    ! [B_4,A_3] : k3_xboole_0(B_4,A_3) = k3_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_303,plain,(
    ! [A_49,B_50] : k4_xboole_0(A_49,k4_xboole_0(A_49,B_50)) = k3_xboole_0(A_49,B_50) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_330,plain,(
    ! [A_18] : k4_xboole_0(A_18,A_18) = k3_xboole_0(A_18,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_303])).

tff(c_6,plain,(
    ! [A_5] : k2_xboole_0(A_5,A_5) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_1674,plain,(
    ! [A_82,B_83,C_84] : k2_xboole_0(k2_xboole_0(A_82,B_83),C_84) = k2_xboole_0(A_82,k2_xboole_0(B_83,C_84)) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_2147,plain,(
    ! [A_91,C_92] : k2_xboole_0(A_91,k2_xboole_0(A_91,C_92)) = k2_xboole_0(A_91,C_92) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_1674])).

tff(c_22,plain,(
    ! [A_19,B_20] : k4_xboole_0(k2_xboole_0(A_19,B_20),B_20) = k4_xboole_0(A_19,B_20) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_2167,plain,(
    ! [A_91,C_92] : k4_xboole_0(k2_xboole_0(A_91,C_92),k2_xboole_0(A_91,C_92)) = k4_xboole_0(A_91,k2_xboole_0(A_91,C_92)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2147,c_22])).

tff(c_2707,plain,(
    ! [A_102,C_103] : k4_xboole_0(A_102,k2_xboole_0(A_102,C_103)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1915,c_4,c_330,c_2167])).

tff(c_2922,plain,(
    ! [B_106,A_107] : k4_xboole_0(B_106,k2_xboole_0(A_107,B_106)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_2707])).

tff(c_3006,plain,(
    k4_xboole_0('#skF_6',k2_xboole_0('#skF_4','#skF_3')) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_41,c_2922])).

tff(c_1423,plain,(
    ! [A_79,B_80,C_81] : k4_xboole_0(k4_xboole_0(A_79,B_80),C_81) = k4_xboole_0(A_79,k2_xboole_0(B_80,C_81)) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_13928,plain,(
    ! [C_226,A_227,B_228] : k2_xboole_0(C_226,k4_xboole_0(A_227,k2_xboole_0(B_228,C_226))) = k2_xboole_0(C_226,k4_xboole_0(A_227,B_228)) ),
    inference(superposition,[status(thm),theory(equality)],[c_1423,c_18])).

tff(c_14100,plain,(
    k2_xboole_0('#skF_3',k4_xboole_0('#skF_6','#skF_4')) = k2_xboole_0('#skF_3',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_3006,c_13928])).

tff(c_14223,plain,(
    k2_xboole_0('#skF_3','#skF_6') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1318,c_187,c_14100])).

tff(c_38,plain,(
    r1_xboole_0('#skF_5','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_1207,plain,(
    k3_xboole_0('#skF_5','#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_38,c_1194])).

tff(c_1241,plain,(
    k3_xboole_0('#skF_3','#skF_5') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_1207,c_4])).

tff(c_26,plain,(
    ! [A_24,B_25] : k4_xboole_0(A_24,k3_xboole_0(A_24,B_25)) = k4_xboole_0(A_24,B_25) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_1324,plain,(
    k4_xboole_0('#skF_3',k1_xboole_0) = k4_xboole_0('#skF_3','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_1241,c_26])).

tff(c_1333,plain,(
    k4_xboole_0('#skF_3','#skF_5') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_1324])).

tff(c_2782,plain,(
    ! [B_2,A_1] : k4_xboole_0(B_2,k2_xboole_0(A_1,B_2)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_2707])).

tff(c_14419,plain,(
    ! [A_229] : k2_xboole_0('#skF_6',k4_xboole_0(A_229,k2_xboole_0('#skF_4','#skF_3'))) = k2_xboole_0('#skF_6',k4_xboole_0(A_229,'#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_41,c_13928])).

tff(c_14510,plain,(
    k2_xboole_0('#skF_6',k4_xboole_0('#skF_3','#skF_5')) = k2_xboole_0('#skF_6',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_2782,c_14419])).

tff(c_14553,plain,(
    '#skF_6' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_14223,c_2,c_1333,c_187,c_14510])).

tff(c_1217,plain,(
    k3_xboole_0('#skF_4','#skF_6') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_1206,c_4])).

tff(c_1291,plain,(
    k4_xboole_0('#skF_4',k1_xboole_0) = k4_xboole_0('#skF_4','#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_1217,c_1269])).

tff(c_1316,plain,(
    k4_xboole_0('#skF_4','#skF_6') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_1291])).

tff(c_14577,plain,(
    k4_xboole_0('#skF_4','#skF_3') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_14553,c_1316])).

tff(c_1294,plain,(
    k4_xboole_0('#skF_5',k1_xboole_0) = k4_xboole_0('#skF_5','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1207,c_1269])).

tff(c_1317,plain,(
    k4_xboole_0('#skF_5','#skF_3') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_1294])).

tff(c_14584,plain,(
    k2_xboole_0('#skF_5','#skF_3') = k2_xboole_0('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14553,c_41])).

tff(c_15757,plain,(
    k4_xboole_0(k2_xboole_0('#skF_4','#skF_3'),'#skF_3') = k4_xboole_0('#skF_5','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_14584,c_22])).

tff(c_15787,plain,(
    '#skF_5' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_14577,c_1317,c_22,c_15757])).

tff(c_15789,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_15787])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:40:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.77/3.33  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.77/3.34  
% 8.77/3.34  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.77/3.34  %$ r2_hidden > r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_1
% 8.77/3.34  
% 8.77/3.34  %Foreground sorts:
% 8.77/3.34  
% 8.77/3.34  
% 8.77/3.34  %Background operators:
% 8.77/3.34  
% 8.77/3.34  
% 8.77/3.34  %Foreground operators:
% 8.77/3.34  tff('#skF_2', type, '#skF_2': $i > $i).
% 8.77/3.34  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.77/3.34  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 8.77/3.34  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 8.77/3.34  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 8.77/3.34  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 8.77/3.34  tff('#skF_5', type, '#skF_5': $i).
% 8.77/3.34  tff('#skF_6', type, '#skF_6': $i).
% 8.77/3.34  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 8.77/3.34  tff('#skF_3', type, '#skF_3': $i).
% 8.77/3.34  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.77/3.34  tff('#skF_4', type, '#skF_4': $i).
% 8.77/3.34  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.77/3.34  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 8.77/3.34  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 8.77/3.34  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 8.77/3.34  
% 8.77/3.36  tff(f_82, negated_conjecture, ~(![A, B, C, D]: ((((k2_xboole_0(A, B) = k2_xboole_0(C, D)) & r1_xboole_0(C, A)) & r1_xboole_0(D, B)) => (C = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_xboole_1)).
% 8.77/3.36  tff(f_61, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 8.77/3.36  tff(f_53, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 8.77/3.36  tff(f_45, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 8.77/3.36  tff(f_67, axiom, (![A, B]: (k4_xboole_0(A, k3_xboole_0(A, B)) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_xboole_1)).
% 8.77/3.36  tff(f_63, axiom, (![A, B]: (k4_xboole_0(k2_xboole_0(A, B), B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t40_xboole_1)).
% 8.77/3.36  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 8.77/3.36  tff(f_73, axiom, (![A, B]: (k2_xboole_0(k3_xboole_0(A, B), k4_xboole_0(A, B)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t51_xboole_1)).
% 8.77/3.36  tff(f_59, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_xboole_1)).
% 8.77/3.36  tff(f_29, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 8.77/3.36  tff(f_69, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 8.77/3.36  tff(f_31, axiom, (![A, B]: (k2_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k2_xboole_0)).
% 8.77/3.36  tff(f_71, axiom, (![A, B, C]: (k2_xboole_0(k2_xboole_0(A, B), C) = k2_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_1)).
% 8.77/3.36  tff(f_65, axiom, (![A, B, C]: (k4_xboole_0(k4_xboole_0(A, B), C) = k4_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_xboole_1)).
% 8.77/3.36  tff(c_34, plain, ('#skF_5'!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_82])).
% 8.77/3.36  tff(c_20, plain, (![A_18]: (k4_xboole_0(A_18, k1_xboole_0)=A_18)), inference(cnfTransformation, [status(thm)], [f_61])).
% 8.77/3.36  tff(c_36, plain, (r1_xboole_0('#skF_6', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_82])).
% 8.77/3.36  tff(c_12, plain, (![A_12]: (r2_hidden('#skF_2'(A_12), A_12) | k1_xboole_0=A_12)), inference(cnfTransformation, [status(thm)], [f_53])).
% 8.77/3.36  tff(c_728, plain, (![A_61, B_62, C_63]: (~r1_xboole_0(A_61, B_62) | ~r2_hidden(C_63, k3_xboole_0(A_61, B_62)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 8.77/3.36  tff(c_1194, plain, (![A_75, B_76]: (~r1_xboole_0(A_75, B_76) | k3_xboole_0(A_75, B_76)=k1_xboole_0)), inference(resolution, [status(thm)], [c_12, c_728])).
% 8.77/3.36  tff(c_1206, plain, (k3_xboole_0('#skF_6', '#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_36, c_1194])).
% 8.77/3.36  tff(c_1269, plain, (![A_77, B_78]: (k4_xboole_0(A_77, k3_xboole_0(A_77, B_78))=k4_xboole_0(A_77, B_78))), inference(cnfTransformation, [status(thm)], [f_67])).
% 8.77/3.36  tff(c_1297, plain, (k4_xboole_0('#skF_6', k1_xboole_0)=k4_xboole_0('#skF_6', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1206, c_1269])).
% 8.77/3.36  tff(c_1318, plain, (k4_xboole_0('#skF_6', '#skF_4')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_20, c_1297])).
% 8.77/3.36  tff(c_156, plain, (![A_44, B_45]: (k4_xboole_0(k2_xboole_0(A_44, B_45), B_45)=k4_xboole_0(A_44, B_45))), inference(cnfTransformation, [status(thm)], [f_63])).
% 8.77/3.36  tff(c_163, plain, (![A_44]: (k4_xboole_0(A_44, k1_xboole_0)=k2_xboole_0(A_44, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_156, c_20])).
% 8.77/3.36  tff(c_187, plain, (![A_44]: (k2_xboole_0(A_44, k1_xboole_0)=A_44)), inference(demodulation, [status(thm), theory('equality')], [c_20, c_163])).
% 8.77/3.36  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 8.77/3.36  tff(c_40, plain, (k2_xboole_0('#skF_5', '#skF_6')=k2_xboole_0('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_82])).
% 8.77/3.36  tff(c_41, plain, (k2_xboole_0('#skF_5', '#skF_6')=k2_xboole_0('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_40])).
% 8.77/3.36  tff(c_32, plain, (![A_31, B_32]: (k2_xboole_0(k3_xboole_0(A_31, B_32), k4_xboole_0(A_31, B_32))=A_31)), inference(cnfTransformation, [status(thm)], [f_73])).
% 8.77/3.36  tff(c_18, plain, (![A_16, B_17]: (k2_xboole_0(A_16, k4_xboole_0(B_17, A_16))=k2_xboole_0(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_59])).
% 8.77/3.36  tff(c_1282, plain, (![A_77, B_78]: (k2_xboole_0(k3_xboole_0(A_77, B_78), k4_xboole_0(A_77, B_78))=k2_xboole_0(k3_xboole_0(A_77, B_78), A_77))), inference(superposition, [status(thm), theory('equality')], [c_1269, c_18])).
% 8.77/3.36  tff(c_1897, plain, (![A_85, B_86]: (k2_xboole_0(A_85, k3_xboole_0(A_85, B_86))=A_85)), inference(demodulation, [status(thm), theory('equality')], [c_2, c_32, c_1282])).
% 8.77/3.36  tff(c_191, plain, (![A_46]: (k2_xboole_0(A_46, k1_xboole_0)=A_46)), inference(demodulation, [status(thm), theory('equality')], [c_20, c_163])).
% 8.77/3.36  tff(c_214, plain, (![A_1]: (k2_xboole_0(k1_xboole_0, A_1)=A_1)), inference(superposition, [status(thm), theory('equality')], [c_2, c_191])).
% 8.77/3.36  tff(c_1915, plain, (![B_86]: (k3_xboole_0(k1_xboole_0, B_86)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_1897, c_214])).
% 8.77/3.36  tff(c_4, plain, (![B_4, A_3]: (k3_xboole_0(B_4, A_3)=k3_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 8.77/3.36  tff(c_303, plain, (![A_49, B_50]: (k4_xboole_0(A_49, k4_xboole_0(A_49, B_50))=k3_xboole_0(A_49, B_50))), inference(cnfTransformation, [status(thm)], [f_69])).
% 8.77/3.36  tff(c_330, plain, (![A_18]: (k4_xboole_0(A_18, A_18)=k3_xboole_0(A_18, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_20, c_303])).
% 8.77/3.36  tff(c_6, plain, (![A_5]: (k2_xboole_0(A_5, A_5)=A_5)), inference(cnfTransformation, [status(thm)], [f_31])).
% 8.77/3.36  tff(c_1674, plain, (![A_82, B_83, C_84]: (k2_xboole_0(k2_xboole_0(A_82, B_83), C_84)=k2_xboole_0(A_82, k2_xboole_0(B_83, C_84)))), inference(cnfTransformation, [status(thm)], [f_71])).
% 8.77/3.36  tff(c_2147, plain, (![A_91, C_92]: (k2_xboole_0(A_91, k2_xboole_0(A_91, C_92))=k2_xboole_0(A_91, C_92))), inference(superposition, [status(thm), theory('equality')], [c_6, c_1674])).
% 8.77/3.36  tff(c_22, plain, (![A_19, B_20]: (k4_xboole_0(k2_xboole_0(A_19, B_20), B_20)=k4_xboole_0(A_19, B_20))), inference(cnfTransformation, [status(thm)], [f_63])).
% 8.77/3.36  tff(c_2167, plain, (![A_91, C_92]: (k4_xboole_0(k2_xboole_0(A_91, C_92), k2_xboole_0(A_91, C_92))=k4_xboole_0(A_91, k2_xboole_0(A_91, C_92)))), inference(superposition, [status(thm), theory('equality')], [c_2147, c_22])).
% 8.77/3.36  tff(c_2707, plain, (![A_102, C_103]: (k4_xboole_0(A_102, k2_xboole_0(A_102, C_103))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_1915, c_4, c_330, c_2167])).
% 8.77/3.36  tff(c_2922, plain, (![B_106, A_107]: (k4_xboole_0(B_106, k2_xboole_0(A_107, B_106))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2, c_2707])).
% 8.77/3.36  tff(c_3006, plain, (k4_xboole_0('#skF_6', k2_xboole_0('#skF_4', '#skF_3'))=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_41, c_2922])).
% 8.77/3.36  tff(c_1423, plain, (![A_79, B_80, C_81]: (k4_xboole_0(k4_xboole_0(A_79, B_80), C_81)=k4_xboole_0(A_79, k2_xboole_0(B_80, C_81)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 8.77/3.36  tff(c_13928, plain, (![C_226, A_227, B_228]: (k2_xboole_0(C_226, k4_xboole_0(A_227, k2_xboole_0(B_228, C_226)))=k2_xboole_0(C_226, k4_xboole_0(A_227, B_228)))), inference(superposition, [status(thm), theory('equality')], [c_1423, c_18])).
% 8.77/3.36  tff(c_14100, plain, (k2_xboole_0('#skF_3', k4_xboole_0('#skF_6', '#skF_4'))=k2_xboole_0('#skF_3', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_3006, c_13928])).
% 8.77/3.36  tff(c_14223, plain, (k2_xboole_0('#skF_3', '#skF_6')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1318, c_187, c_14100])).
% 8.77/3.36  tff(c_38, plain, (r1_xboole_0('#skF_5', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_82])).
% 8.77/3.36  tff(c_1207, plain, (k3_xboole_0('#skF_5', '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_38, c_1194])).
% 8.77/3.36  tff(c_1241, plain, (k3_xboole_0('#skF_3', '#skF_5')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_1207, c_4])).
% 8.77/3.36  tff(c_26, plain, (![A_24, B_25]: (k4_xboole_0(A_24, k3_xboole_0(A_24, B_25))=k4_xboole_0(A_24, B_25))), inference(cnfTransformation, [status(thm)], [f_67])).
% 8.77/3.36  tff(c_1324, plain, (k4_xboole_0('#skF_3', k1_xboole_0)=k4_xboole_0('#skF_3', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_1241, c_26])).
% 8.77/3.36  tff(c_1333, plain, (k4_xboole_0('#skF_3', '#skF_5')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_20, c_1324])).
% 8.77/3.36  tff(c_2782, plain, (![B_2, A_1]: (k4_xboole_0(B_2, k2_xboole_0(A_1, B_2))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2, c_2707])).
% 8.77/3.36  tff(c_14419, plain, (![A_229]: (k2_xboole_0('#skF_6', k4_xboole_0(A_229, k2_xboole_0('#skF_4', '#skF_3')))=k2_xboole_0('#skF_6', k4_xboole_0(A_229, '#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_41, c_13928])).
% 8.77/3.36  tff(c_14510, plain, (k2_xboole_0('#skF_6', k4_xboole_0('#skF_3', '#skF_5'))=k2_xboole_0('#skF_6', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2782, c_14419])).
% 8.77/3.36  tff(c_14553, plain, ('#skF_6'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_14223, c_2, c_1333, c_187, c_14510])).
% 8.77/3.36  tff(c_1217, plain, (k3_xboole_0('#skF_4', '#skF_6')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_1206, c_4])).
% 8.77/3.36  tff(c_1291, plain, (k4_xboole_0('#skF_4', k1_xboole_0)=k4_xboole_0('#skF_4', '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_1217, c_1269])).
% 8.77/3.36  tff(c_1316, plain, (k4_xboole_0('#skF_4', '#skF_6')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_20, c_1291])).
% 8.77/3.36  tff(c_14577, plain, (k4_xboole_0('#skF_4', '#skF_3')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_14553, c_1316])).
% 8.77/3.36  tff(c_1294, plain, (k4_xboole_0('#skF_5', k1_xboole_0)=k4_xboole_0('#skF_5', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1207, c_1269])).
% 8.77/3.36  tff(c_1317, plain, (k4_xboole_0('#skF_5', '#skF_3')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_20, c_1294])).
% 8.77/3.36  tff(c_14584, plain, (k2_xboole_0('#skF_5', '#skF_3')=k2_xboole_0('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_14553, c_41])).
% 8.77/3.36  tff(c_15757, plain, (k4_xboole_0(k2_xboole_0('#skF_4', '#skF_3'), '#skF_3')=k4_xboole_0('#skF_5', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_14584, c_22])).
% 8.77/3.36  tff(c_15787, plain, ('#skF_5'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_14577, c_1317, c_22, c_15757])).
% 8.77/3.36  tff(c_15789, plain, $false, inference(negUnitSimplification, [status(thm)], [c_34, c_15787])).
% 8.77/3.36  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.77/3.36  
% 8.77/3.36  Inference rules
% 8.77/3.36  ----------------------
% 8.77/3.36  #Ref     : 0
% 8.77/3.36  #Sup     : 3962
% 8.77/3.36  #Fact    : 0
% 8.77/3.36  #Define  : 0
% 8.77/3.36  #Split   : 3
% 8.77/3.36  #Chain   : 0
% 8.77/3.36  #Close   : 0
% 8.77/3.36  
% 8.77/3.36  Ordering : KBO
% 8.77/3.36  
% 8.77/3.36  Simplification rules
% 8.77/3.36  ----------------------
% 8.77/3.36  #Subsume      : 104
% 8.77/3.36  #Demod        : 4213
% 8.77/3.36  #Tautology    : 2739
% 8.77/3.36  #SimpNegUnit  : 57
% 8.77/3.36  #BackRed      : 35
% 8.77/3.36  
% 8.77/3.36  #Partial instantiations: 0
% 8.77/3.36  #Strategies tried      : 1
% 8.77/3.36  
% 8.77/3.36  Timing (in seconds)
% 8.77/3.36  ----------------------
% 8.77/3.36  Preprocessing        : 0.32
% 8.77/3.36  Parsing              : 0.18
% 8.77/3.36  CNF conversion       : 0.02
% 8.77/3.36  Main loop            : 2.20
% 8.77/3.36  Inferencing          : 0.49
% 8.77/3.36  Reduction            : 1.23
% 8.77/3.36  Demodulation         : 1.08
% 8.77/3.36  BG Simplification    : 0.06
% 8.77/3.36  Subsumption          : 0.31
% 8.77/3.36  Abstraction          : 0.08
% 8.77/3.36  MUC search           : 0.00
% 8.77/3.36  Cooper               : 0.00
% 8.77/3.36  Total                : 2.56
% 8.77/3.36  Index Insertion      : 0.00
% 8.77/3.36  Index Deletion       : 0.00
% 8.77/3.36  Index Matching       : 0.00
% 8.77/3.36  BG Taut test         : 0.00
%------------------------------------------------------------------------------
