%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:44:27 EST 2020

% Result     : Theorem 4.89s
% Output     : CNFRefutation 4.89s
% Verified   : 
% Statistics : Number of formulae       :   67 ( 191 expanded)
%              Number of leaves         :   21 (  72 expanded)
%              Depth                    :   16
%              Number of atoms          :   66 ( 200 expanded)
%              Number of equality atoms :   43 ( 159 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

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

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_56,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( ~ r1_xboole_0(A,B)
          & r1_xboole_0(A,C)
          & r1_xboole_0(A,k4_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t84_xboole_1)).

tff(f_29,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_47,axiom,(
    ! [A,B,C] :
      ( r1_xboole_0(A,k4_xboole_0(B,C))
     => r1_xboole_0(B,k4_xboole_0(A,C)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_xboole_1)).

tff(f_37,axiom,(
    ! [A] : k4_xboole_0(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).

tff(f_35,axiom,(
    ! [A,B,C] : k3_xboole_0(A,k4_xboole_0(B,C)) = k4_xboole_0(k3_xboole_0(A,B),C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_xboole_1)).

tff(f_31,axiom,(
    ! [A,B,C] : k4_xboole_0(k4_xboole_0(A,B),C) = k4_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] : k4_xboole_0(A,k2_xboole_0(A,B)) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_39,axiom,(
    ! [A,B,C] : k4_xboole_0(A,k3_xboole_0(B,C)) = k2_xboole_0(k4_xboole_0(A,B),k4_xboole_0(A,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t54_xboole_1)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( r1_xboole_0(A,B)
     => k3_xboole_0(A,k2_xboole_0(B,C)) = k3_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t78_xboole_1)).

tff(c_24,plain,(
    ~ r1_xboole_0('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_4,plain,(
    ! [A_3] : k4_xboole_0(A_3,k1_xboole_0) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_22,plain,(
    r1_xboole_0('#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_137,plain,(
    ! [B_30,A_31,C_32] :
      ( r1_xboole_0(B_30,k4_xboole_0(A_31,C_32))
      | ~ r1_xboole_0(A_31,k4_xboole_0(B_30,C_32)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_147,plain,(
    ! [A_3,A_31] :
      ( r1_xboole_0(A_3,k4_xboole_0(A_31,k1_xboole_0))
      | ~ r1_xboole_0(A_31,A_3) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_137])).

tff(c_154,plain,(
    ! [A_33,A_34] :
      ( r1_xboole_0(A_33,A_34)
      | ~ r1_xboole_0(A_34,A_33) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_147])).

tff(c_163,plain,(
    r1_xboole_0('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_22,c_154])).

tff(c_12,plain,(
    ! [A_12] : k4_xboole_0(k1_xboole_0,A_12) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_10,plain,(
    ! [A_9,B_10,C_11] : k4_xboole_0(k3_xboole_0(A_9,B_10),C_11) = k3_xboole_0(A_9,k4_xboole_0(B_10,C_11)) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_238,plain,(
    ! [A_41,B_42,C_43] : k4_xboole_0(k4_xboole_0(A_41,B_42),C_43) = k4_xboole_0(A_41,k2_xboole_0(B_42,C_43)) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_301,plain,(
    ! [A_44,B_45] : k4_xboole_0(A_44,k2_xboole_0(B_45,k1_xboole_0)) = k4_xboole_0(A_44,B_45) ),
    inference(superposition,[status(thm),theory(equality)],[c_238,c_4])).

tff(c_8,plain,(
    ! [A_7,B_8] : k4_xboole_0(A_7,k2_xboole_0(A_7,B_8)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_373,plain,(
    ! [B_46] : k4_xboole_0(B_46,B_46) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_301,c_8])).

tff(c_1079,plain,(
    ! [A_66,B_67] : k3_xboole_0(A_66,k4_xboole_0(B_67,k3_xboole_0(A_66,B_67))) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_373])).

tff(c_1106,plain,(
    ! [A_66] : k3_xboole_0(A_66,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_1079])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_277,plain,(
    ! [A_7,B_8,C_43] : k4_xboole_0(A_7,k2_xboole_0(k2_xboole_0(A_7,B_8),C_43)) = k4_xboole_0(k1_xboole_0,C_43) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_238])).

tff(c_796,plain,(
    ! [A_57,B_58,C_59] : k4_xboole_0(A_57,k2_xboole_0(k2_xboole_0(A_57,B_58),C_59)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_277])).

tff(c_974,plain,(
    ! [A_63,A_64,B_65] : k4_xboole_0(A_63,k2_xboole_0(A_64,k2_xboole_0(A_63,B_65))) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_796])).

tff(c_1047,plain,(
    ! [B_2,A_64,A_1] : k4_xboole_0(B_2,k2_xboole_0(A_64,k2_xboole_0(A_1,B_2))) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_974])).

tff(c_258,plain,(
    ! [A_41,B_42] : k4_xboole_0(A_41,k2_xboole_0(B_42,k1_xboole_0)) = k4_xboole_0(A_41,B_42) ),
    inference(superposition,[status(thm),theory(equality)],[c_238,c_4])).

tff(c_325,plain,(
    ! [B_45] : k4_xboole_0(B_45,B_45) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_301,c_8])).

tff(c_512,plain,(
    ! [A_51,B_52,C_53] : k2_xboole_0(k4_xboole_0(A_51,B_52),k4_xboole_0(A_51,C_53)) = k4_xboole_0(A_51,k3_xboole_0(B_52,C_53)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_1620,plain,(
    ! [A_78,C_79] : k4_xboole_0(A_78,k3_xboole_0(k1_xboole_0,C_79)) = k2_xboole_0(A_78,k4_xboole_0(A_78,C_79)) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_512])).

tff(c_413,plain,(
    ! [A_9,B_10] : k3_xboole_0(A_9,k4_xboole_0(B_10,k3_xboole_0(A_9,B_10))) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_373])).

tff(c_1650,plain,(
    ! [C_79] : k3_xboole_0(k1_xboole_0,k2_xboole_0(C_79,k4_xboole_0(C_79,C_79))) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_1620,c_413])).

tff(c_1882,plain,(
    ! [C_81] : k3_xboole_0(k1_xboole_0,k2_xboole_0(C_81,k1_xboole_0)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_325,c_1650])).

tff(c_590,plain,(
    ! [A_3,C_53] : k4_xboole_0(A_3,k3_xboole_0(k1_xboole_0,C_53)) = k2_xboole_0(A_3,k4_xboole_0(A_3,C_53)) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_512])).

tff(c_1887,plain,(
    ! [A_3,C_81] : k2_xboole_0(A_3,k4_xboole_0(A_3,k2_xboole_0(C_81,k1_xboole_0))) = k4_xboole_0(A_3,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_1882,c_590])).

tff(c_1974,plain,(
    ! [A_83,C_84] : k2_xboole_0(A_83,k4_xboole_0(A_83,C_84)) = A_83 ),
    inference(demodulation,[status(thm),theory(equality)],[c_258,c_4,c_1887])).

tff(c_2109,plain,(
    ! [B_85] : k2_xboole_0(B_85,k1_xboole_0) = B_85 ),
    inference(superposition,[status(thm),theory(equality)],[c_1047,c_1974])).

tff(c_16,plain,(
    ! [A_16,B_17,C_18] :
      ( k3_xboole_0(A_16,k2_xboole_0(B_17,C_18)) = k3_xboole_0(A_16,C_18)
      | ~ r1_xboole_0(A_16,B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_2159,plain,(
    ! [A_16,B_85] :
      ( k3_xboole_0(A_16,k1_xboole_0) = k3_xboole_0(A_16,B_85)
      | ~ r1_xboole_0(A_16,B_85) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2109,c_16])).

tff(c_2586,plain,(
    ! [A_93,B_94] :
      ( k3_xboole_0(A_93,B_94) = k1_xboole_0
      | ~ r1_xboole_0(A_93,B_94) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1106,c_2159])).

tff(c_2607,plain,(
    k3_xboole_0('#skF_3','#skF_1') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_163,c_2586])).

tff(c_2186,plain,(
    ! [B_2] : k2_xboole_0(k1_xboole_0,B_2) = B_2 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_2109])).

tff(c_4848,plain,(
    ! [A_130,C_131,B_132] : k2_xboole_0(k4_xboole_0(A_130,C_131),k4_xboole_0(A_130,B_132)) = k4_xboole_0(A_130,k3_xboole_0(B_132,C_131)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_512])).

tff(c_4992,plain,(
    ! [B_45,B_132] : k4_xboole_0(B_45,k3_xboole_0(B_132,B_45)) = k2_xboole_0(k1_xboole_0,k4_xboole_0(B_45,B_132)) ),
    inference(superposition,[status(thm),theory(equality)],[c_325,c_4848])).

tff(c_5492,plain,(
    ! [B_138,B_139] : k4_xboole_0(B_138,k3_xboole_0(B_139,B_138)) = k4_xboole_0(B_138,B_139) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2186,c_4992])).

tff(c_5643,plain,(
    k4_xboole_0('#skF_1',k1_xboole_0) = k4_xboole_0('#skF_1','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_2607,c_5492])).

tff(c_5707,plain,(
    k4_xboole_0('#skF_1','#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_5643])).

tff(c_20,plain,(
    r1_xboole_0('#skF_1',k4_xboole_0('#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_148,plain,(
    r1_xboole_0('#skF_2',k4_xboole_0('#skF_1','#skF_3')) ),
    inference(resolution,[status(thm)],[c_20,c_137])).

tff(c_161,plain,(
    r1_xboole_0(k4_xboole_0('#skF_1','#skF_3'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_148,c_154])).

tff(c_5871,plain,(
    r1_xboole_0('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5707,c_161])).

tff(c_5874,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_5871])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:35:00 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.89/1.93  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.89/1.93  
% 4.89/1.93  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.89/1.93  %$ r1_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 4.89/1.93  
% 4.89/1.93  %Foreground sorts:
% 4.89/1.93  
% 4.89/1.93  
% 4.89/1.93  %Background operators:
% 4.89/1.93  
% 4.89/1.93  
% 4.89/1.93  %Foreground operators:
% 4.89/1.93  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.89/1.93  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.89/1.93  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.89/1.93  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 4.89/1.93  tff('#skF_2', type, '#skF_2': $i).
% 4.89/1.93  tff('#skF_3', type, '#skF_3': $i).
% 4.89/1.93  tff('#skF_1', type, '#skF_1': $i).
% 4.89/1.93  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.89/1.93  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.89/1.93  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.89/1.93  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.89/1.94  
% 4.89/1.95  tff(f_56, negated_conjecture, ~(![A, B, C]: ~((~r1_xboole_0(A, B) & r1_xboole_0(A, C)) & r1_xboole_0(A, k4_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t84_xboole_1)).
% 4.89/1.95  tff(f_29, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 4.89/1.95  tff(f_47, axiom, (![A, B, C]: (r1_xboole_0(A, k4_xboole_0(B, C)) => r1_xboole_0(B, k4_xboole_0(A, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t81_xboole_1)).
% 4.89/1.95  tff(f_37, axiom, (![A]: (k4_xboole_0(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_boole)).
% 4.89/1.95  tff(f_35, axiom, (![A, B, C]: (k3_xboole_0(A, k4_xboole_0(B, C)) = k4_xboole_0(k3_xboole_0(A, B), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_xboole_1)).
% 4.89/1.95  tff(f_31, axiom, (![A, B, C]: (k4_xboole_0(k4_xboole_0(A, B), C) = k4_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_xboole_1)).
% 4.89/1.95  tff(f_33, axiom, (![A, B]: (k4_xboole_0(A, k2_xboole_0(A, B)) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_xboole_1)).
% 4.89/1.95  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 4.89/1.95  tff(f_39, axiom, (![A, B, C]: (k4_xboole_0(A, k3_xboole_0(B, C)) = k2_xboole_0(k4_xboole_0(A, B), k4_xboole_0(A, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t54_xboole_1)).
% 4.89/1.95  tff(f_43, axiom, (![A, B, C]: (r1_xboole_0(A, B) => (k3_xboole_0(A, k2_xboole_0(B, C)) = k3_xboole_0(A, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t78_xboole_1)).
% 4.89/1.95  tff(c_24, plain, (~r1_xboole_0('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_56])).
% 4.89/1.95  tff(c_4, plain, (![A_3]: (k4_xboole_0(A_3, k1_xboole_0)=A_3)), inference(cnfTransformation, [status(thm)], [f_29])).
% 4.89/1.95  tff(c_22, plain, (r1_xboole_0('#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_56])).
% 4.89/1.95  tff(c_137, plain, (![B_30, A_31, C_32]: (r1_xboole_0(B_30, k4_xboole_0(A_31, C_32)) | ~r1_xboole_0(A_31, k4_xboole_0(B_30, C_32)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 4.89/1.95  tff(c_147, plain, (![A_3, A_31]: (r1_xboole_0(A_3, k4_xboole_0(A_31, k1_xboole_0)) | ~r1_xboole_0(A_31, A_3))), inference(superposition, [status(thm), theory('equality')], [c_4, c_137])).
% 4.89/1.95  tff(c_154, plain, (![A_33, A_34]: (r1_xboole_0(A_33, A_34) | ~r1_xboole_0(A_34, A_33))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_147])).
% 4.89/1.95  tff(c_163, plain, (r1_xboole_0('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_22, c_154])).
% 4.89/1.95  tff(c_12, plain, (![A_12]: (k4_xboole_0(k1_xboole_0, A_12)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.89/1.95  tff(c_10, plain, (![A_9, B_10, C_11]: (k4_xboole_0(k3_xboole_0(A_9, B_10), C_11)=k3_xboole_0(A_9, k4_xboole_0(B_10, C_11)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.89/1.95  tff(c_238, plain, (![A_41, B_42, C_43]: (k4_xboole_0(k4_xboole_0(A_41, B_42), C_43)=k4_xboole_0(A_41, k2_xboole_0(B_42, C_43)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.89/1.95  tff(c_301, plain, (![A_44, B_45]: (k4_xboole_0(A_44, k2_xboole_0(B_45, k1_xboole_0))=k4_xboole_0(A_44, B_45))), inference(superposition, [status(thm), theory('equality')], [c_238, c_4])).
% 4.89/1.95  tff(c_8, plain, (![A_7, B_8]: (k4_xboole_0(A_7, k2_xboole_0(A_7, B_8))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.89/1.95  tff(c_373, plain, (![B_46]: (k4_xboole_0(B_46, B_46)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_301, c_8])).
% 4.89/1.95  tff(c_1079, plain, (![A_66, B_67]: (k3_xboole_0(A_66, k4_xboole_0(B_67, k3_xboole_0(A_66, B_67)))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_10, c_373])).
% 4.89/1.95  tff(c_1106, plain, (![A_66]: (k3_xboole_0(A_66, k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_12, c_1079])).
% 4.89/1.95  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.89/1.95  tff(c_277, plain, (![A_7, B_8, C_43]: (k4_xboole_0(A_7, k2_xboole_0(k2_xboole_0(A_7, B_8), C_43))=k4_xboole_0(k1_xboole_0, C_43))), inference(superposition, [status(thm), theory('equality')], [c_8, c_238])).
% 4.89/1.95  tff(c_796, plain, (![A_57, B_58, C_59]: (k4_xboole_0(A_57, k2_xboole_0(k2_xboole_0(A_57, B_58), C_59))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_12, c_277])).
% 4.89/1.95  tff(c_974, plain, (![A_63, A_64, B_65]: (k4_xboole_0(A_63, k2_xboole_0(A_64, k2_xboole_0(A_63, B_65)))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2, c_796])).
% 4.89/1.95  tff(c_1047, plain, (![B_2, A_64, A_1]: (k4_xboole_0(B_2, k2_xboole_0(A_64, k2_xboole_0(A_1, B_2)))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2, c_974])).
% 4.89/1.95  tff(c_258, plain, (![A_41, B_42]: (k4_xboole_0(A_41, k2_xboole_0(B_42, k1_xboole_0))=k4_xboole_0(A_41, B_42))), inference(superposition, [status(thm), theory('equality')], [c_238, c_4])).
% 4.89/1.95  tff(c_325, plain, (![B_45]: (k4_xboole_0(B_45, B_45)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_301, c_8])).
% 4.89/1.95  tff(c_512, plain, (![A_51, B_52, C_53]: (k2_xboole_0(k4_xboole_0(A_51, B_52), k4_xboole_0(A_51, C_53))=k4_xboole_0(A_51, k3_xboole_0(B_52, C_53)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.89/1.95  tff(c_1620, plain, (![A_78, C_79]: (k4_xboole_0(A_78, k3_xboole_0(k1_xboole_0, C_79))=k2_xboole_0(A_78, k4_xboole_0(A_78, C_79)))), inference(superposition, [status(thm), theory('equality')], [c_4, c_512])).
% 4.89/1.95  tff(c_413, plain, (![A_9, B_10]: (k3_xboole_0(A_9, k4_xboole_0(B_10, k3_xboole_0(A_9, B_10)))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_10, c_373])).
% 4.89/1.95  tff(c_1650, plain, (![C_79]: (k3_xboole_0(k1_xboole_0, k2_xboole_0(C_79, k4_xboole_0(C_79, C_79)))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_1620, c_413])).
% 4.89/1.95  tff(c_1882, plain, (![C_81]: (k3_xboole_0(k1_xboole_0, k2_xboole_0(C_81, k1_xboole_0))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_325, c_1650])).
% 4.89/1.95  tff(c_590, plain, (![A_3, C_53]: (k4_xboole_0(A_3, k3_xboole_0(k1_xboole_0, C_53))=k2_xboole_0(A_3, k4_xboole_0(A_3, C_53)))), inference(superposition, [status(thm), theory('equality')], [c_4, c_512])).
% 4.89/1.95  tff(c_1887, plain, (![A_3, C_81]: (k2_xboole_0(A_3, k4_xboole_0(A_3, k2_xboole_0(C_81, k1_xboole_0)))=k4_xboole_0(A_3, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_1882, c_590])).
% 4.89/1.95  tff(c_1974, plain, (![A_83, C_84]: (k2_xboole_0(A_83, k4_xboole_0(A_83, C_84))=A_83)), inference(demodulation, [status(thm), theory('equality')], [c_258, c_4, c_1887])).
% 4.89/1.95  tff(c_2109, plain, (![B_85]: (k2_xboole_0(B_85, k1_xboole_0)=B_85)), inference(superposition, [status(thm), theory('equality')], [c_1047, c_1974])).
% 4.89/1.95  tff(c_16, plain, (![A_16, B_17, C_18]: (k3_xboole_0(A_16, k2_xboole_0(B_17, C_18))=k3_xboole_0(A_16, C_18) | ~r1_xboole_0(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.89/1.95  tff(c_2159, plain, (![A_16, B_85]: (k3_xboole_0(A_16, k1_xboole_0)=k3_xboole_0(A_16, B_85) | ~r1_xboole_0(A_16, B_85))), inference(superposition, [status(thm), theory('equality')], [c_2109, c_16])).
% 4.89/1.95  tff(c_2586, plain, (![A_93, B_94]: (k3_xboole_0(A_93, B_94)=k1_xboole_0 | ~r1_xboole_0(A_93, B_94))), inference(demodulation, [status(thm), theory('equality')], [c_1106, c_2159])).
% 4.89/1.95  tff(c_2607, plain, (k3_xboole_0('#skF_3', '#skF_1')=k1_xboole_0), inference(resolution, [status(thm)], [c_163, c_2586])).
% 4.89/1.95  tff(c_2186, plain, (![B_2]: (k2_xboole_0(k1_xboole_0, B_2)=B_2)), inference(superposition, [status(thm), theory('equality')], [c_2, c_2109])).
% 4.89/1.95  tff(c_4848, plain, (![A_130, C_131, B_132]: (k2_xboole_0(k4_xboole_0(A_130, C_131), k4_xboole_0(A_130, B_132))=k4_xboole_0(A_130, k3_xboole_0(B_132, C_131)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_512])).
% 4.89/1.95  tff(c_4992, plain, (![B_45, B_132]: (k4_xboole_0(B_45, k3_xboole_0(B_132, B_45))=k2_xboole_0(k1_xboole_0, k4_xboole_0(B_45, B_132)))), inference(superposition, [status(thm), theory('equality')], [c_325, c_4848])).
% 4.89/1.95  tff(c_5492, plain, (![B_138, B_139]: (k4_xboole_0(B_138, k3_xboole_0(B_139, B_138))=k4_xboole_0(B_138, B_139))), inference(demodulation, [status(thm), theory('equality')], [c_2186, c_4992])).
% 4.89/1.95  tff(c_5643, plain, (k4_xboole_0('#skF_1', k1_xboole_0)=k4_xboole_0('#skF_1', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_2607, c_5492])).
% 4.89/1.95  tff(c_5707, plain, (k4_xboole_0('#skF_1', '#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_4, c_5643])).
% 4.89/1.95  tff(c_20, plain, (r1_xboole_0('#skF_1', k4_xboole_0('#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_56])).
% 4.89/1.95  tff(c_148, plain, (r1_xboole_0('#skF_2', k4_xboole_0('#skF_1', '#skF_3'))), inference(resolution, [status(thm)], [c_20, c_137])).
% 4.89/1.95  tff(c_161, plain, (r1_xboole_0(k4_xboole_0('#skF_1', '#skF_3'), '#skF_2')), inference(resolution, [status(thm)], [c_148, c_154])).
% 4.89/1.95  tff(c_5871, plain, (r1_xboole_0('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_5707, c_161])).
% 4.89/1.95  tff(c_5874, plain, $false, inference(negUnitSimplification, [status(thm)], [c_24, c_5871])).
% 4.89/1.95  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.89/1.95  
% 4.89/1.95  Inference rules
% 4.89/1.95  ----------------------
% 4.89/1.95  #Ref     : 0
% 4.89/1.95  #Sup     : 1466
% 4.89/1.95  #Fact    : 0
% 4.89/1.95  #Define  : 0
% 4.89/1.95  #Split   : 1
% 4.89/1.95  #Chain   : 0
% 4.89/1.95  #Close   : 0
% 4.89/1.95  
% 4.89/1.95  Ordering : KBO
% 4.89/1.95  
% 4.89/1.95  Simplification rules
% 4.89/1.95  ----------------------
% 4.89/1.95  #Subsume      : 34
% 4.89/1.95  #Demod        : 1333
% 4.89/1.95  #Tautology    : 1006
% 4.89/1.95  #SimpNegUnit  : 3
% 4.89/1.95  #BackRed      : 10
% 4.89/1.95  
% 4.89/1.95  #Partial instantiations: 0
% 4.89/1.95  #Strategies tried      : 1
% 4.89/1.95  
% 4.89/1.95  Timing (in seconds)
% 4.89/1.95  ----------------------
% 4.89/1.95  Preprocessing        : 0.29
% 4.89/1.95  Parsing              : 0.16
% 4.89/1.95  CNF conversion       : 0.02
% 4.89/1.95  Main loop            : 0.90
% 4.89/1.95  Inferencing          : 0.25
% 4.89/1.95  Reduction            : 0.42
% 4.89/1.95  Demodulation         : 0.35
% 4.89/1.95  BG Simplification    : 0.03
% 4.89/1.95  Subsumption          : 0.13
% 4.89/1.95  Abstraction          : 0.05
% 4.89/1.95  MUC search           : 0.00
% 4.89/1.95  Cooper               : 0.00
% 4.89/1.95  Total                : 1.22
% 4.89/1.95  Index Insertion      : 0.00
% 4.89/1.95  Index Deletion       : 0.00
% 4.89/1.95  Index Matching       : 0.00
% 4.89/1.95  BG Taut test         : 0.00
%------------------------------------------------------------------------------
