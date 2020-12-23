%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:43:47 EST 2020

% Result     : Theorem 5.67s
% Output     : CNFRefutation 5.67s
% Verified   : 
% Statistics : Number of formulae       :   89 ( 412 expanded)
%              Number of leaves         :   24 ( 150 expanded)
%              Depth                    :   20
%              Number of atoms          :   84 ( 453 expanded)
%              Number of equality atoms :   72 ( 401 expanded)
%              Maximal formula depth    :    9 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_60,negated_conjecture,(
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
    ! [A,B] : k4_xboole_0(k2_xboole_0(A,B),B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_xboole_1)).

tff(f_39,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_45,axiom,(
    ! [A,B] : k4_xboole_0(A,k3_xboole_0(A,B)) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_43,axiom,(
    ! [A,B,C] : k4_xboole_0(k4_xboole_0(A,B),C) = k4_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

tff(f_51,axiom,(
    ! [A,B] : k2_xboole_0(k3_xboole_0(A,B),k4_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_xboole_1)).

tff(f_47,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_49,axiom,(
    ! [A,B,C] : k2_xboole_0(k2_xboole_0(A,B),C) = k2_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_1)).

tff(c_26,plain,(
    '#skF_2' != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_232,plain,(
    ! [A_41,B_42] : k4_xboole_0(k2_xboole_0(A_41,B_42),B_42) = k4_xboole_0(A_41,B_42) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_275,plain,(
    ! [B_2,A_1] : k4_xboole_0(k2_xboole_0(B_2,A_1),B_2) = k4_xboole_0(A_1,B_2) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_232])).

tff(c_12,plain,(
    ! [A_9] : k4_xboole_0(A_9,k1_xboole_0) = A_9 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_28,plain,(
    r1_xboole_0('#skF_4','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_47,plain,(
    ! [B_25,A_26] :
      ( r1_xboole_0(B_25,A_26)
      | ~ r1_xboole_0(A_26,B_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_52,plain,(
    r1_xboole_0('#skF_2','#skF_4') ),
    inference(resolution,[status(thm)],[c_28,c_47])).

tff(c_99,plain,(
    ! [A_31,B_32] :
      ( k3_xboole_0(A_31,B_32) = k1_xboole_0
      | ~ r1_xboole_0(A_31,B_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_117,plain,(
    k3_xboole_0('#skF_2','#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_52,c_99])).

tff(c_439,plain,(
    ! [A_45,B_46] : k4_xboole_0(A_45,k3_xboole_0(A_45,B_46)) = k4_xboole_0(A_45,B_46) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_457,plain,(
    k4_xboole_0('#skF_2',k1_xboole_0) = k4_xboole_0('#skF_2','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_117,c_439])).

tff(c_471,plain,(
    k4_xboole_0('#skF_2','#skF_4') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_457])).

tff(c_245,plain,(
    ! [A_41] : k4_xboole_0(A_41,k1_xboole_0) = k2_xboole_0(A_41,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_232,c_12])).

tff(c_288,plain,(
    ! [A_41] : k2_xboole_0(A_41,k1_xboole_0) = A_41 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_245])).

tff(c_10,plain,(
    ! [A_7,B_8] : k2_xboole_0(A_7,k4_xboole_0(B_8,A_7)) = k2_xboole_0(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_16,plain,(
    ! [A_12,B_13,C_14] : k4_xboole_0(k4_xboole_0(A_12,B_13),C_14) = k4_xboole_0(A_12,k2_xboole_0(B_13,C_14)) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_24,plain,(
    ! [A_22,B_23] : k2_xboole_0(k3_xboole_0(A_22,B_23),k4_xboole_0(A_22,B_23)) = A_22 ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_445,plain,(
    ! [A_45,B_46] : k2_xboole_0(k3_xboole_0(A_45,B_46),k4_xboole_0(A_45,B_46)) = k2_xboole_0(k3_xboole_0(A_45,B_46),A_45) ),
    inference(superposition,[status(thm),theory(equality)],[c_439,c_10])).

tff(c_1046,plain,(
    ! [A_56,B_57] : k2_xboole_0(A_56,k3_xboole_0(A_56,B_57)) = A_56 ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_2,c_445])).

tff(c_292,plain,(
    ! [A_43] : k2_xboole_0(A_43,k1_xboole_0) = A_43 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_245])).

tff(c_319,plain,(
    ! [A_1] : k2_xboole_0(k1_xboole_0,A_1) = A_1 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_292])).

tff(c_1130,plain,(
    ! [B_58] : k3_xboole_0(k1_xboole_0,B_58) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_1046,c_319])).

tff(c_18,plain,(
    ! [A_15,B_16] : k4_xboole_0(A_15,k3_xboole_0(A_15,B_16)) = k4_xboole_0(A_15,B_16) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_1138,plain,(
    ! [B_58] : k4_xboole_0(k1_xboole_0,k1_xboole_0) = k4_xboole_0(k1_xboole_0,B_58) ),
    inference(superposition,[status(thm),theory(equality)],[c_1130,c_18])).

tff(c_1150,plain,(
    ! [B_58] : k4_xboole_0(k1_xboole_0,B_58) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_1138])).

tff(c_523,plain,(
    ! [A_47,B_48] : k4_xboole_0(A_47,k4_xboole_0(A_47,B_48)) = k3_xboole_0(A_47,B_48) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_562,plain,(
    ! [A_9] : k4_xboole_0(A_9,A_9) = k3_xboole_0(A_9,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_523])).

tff(c_339,plain,(
    ! [A_44] : k2_xboole_0(k1_xboole_0,A_44) = A_44 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_292])).

tff(c_14,plain,(
    ! [A_10,B_11] : k4_xboole_0(k2_xboole_0(A_10,B_11),B_11) = k4_xboole_0(A_10,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_349,plain,(
    ! [A_44] : k4_xboole_0(k1_xboole_0,A_44) = k4_xboole_0(A_44,A_44) ),
    inference(superposition,[status(thm),theory(equality)],[c_339,c_14])).

tff(c_1553,plain,(
    ! [A_44] : k3_xboole_0(A_44,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1150,c_562,c_349])).

tff(c_1611,plain,(
    ! [A_65] : k4_xboole_0(A_65,A_65) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1553,c_562])).

tff(c_1645,plain,(
    ! [A_12,B_13] : k4_xboole_0(A_12,k2_xboole_0(B_13,k4_xboole_0(A_12,B_13))) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_1611])).

tff(c_1659,plain,(
    ! [A_12,B_13] : k4_xboole_0(A_12,k2_xboole_0(B_13,A_12)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_1645])).

tff(c_32,plain,(
    k2_xboole_0('#skF_3','#skF_4') = k2_xboole_0('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_33,plain,(
    k2_xboole_0('#skF_1','#skF_2') = k2_xboole_0('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_32])).

tff(c_30,plain,(
    r1_xboole_0('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_119,plain,(
    k3_xboole_0('#skF_3','#skF_1') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_30,c_99])).

tff(c_463,plain,(
    k4_xboole_0('#skF_3',k1_xboole_0) = k4_xboole_0('#skF_3','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_119,c_439])).

tff(c_473,plain,(
    k4_xboole_0('#skF_3','#skF_1') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_463])).

tff(c_862,plain,(
    ! [A_53,B_54,C_55] : k4_xboole_0(k4_xboole_0(A_53,B_54),C_55) = k4_xboole_0(A_53,k2_xboole_0(B_54,C_55)) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_6067,plain,(
    ! [C_117] : k4_xboole_0('#skF_3',k2_xboole_0('#skF_1',C_117)) = k4_xboole_0('#skF_3',C_117) ),
    inference(superposition,[status(thm),theory(equality)],[c_473,c_862])).

tff(c_6169,plain,(
    k4_xboole_0('#skF_3',k2_xboole_0('#skF_4','#skF_3')) = k4_xboole_0('#skF_3','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_33,c_6067])).

tff(c_6191,plain,(
    k4_xboole_0('#skF_3','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1659,c_6169])).

tff(c_6213,plain,(
    k2_xboole_0('#skF_2',k1_xboole_0) = k2_xboole_0('#skF_2','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_6191,c_10])).

tff(c_6225,plain,(
    k2_xboole_0('#skF_3','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_288,c_2,c_6213])).

tff(c_659,plain,(
    ! [A_49,B_50,C_51] : k2_xboole_0(k2_xboole_0(A_49,B_50),C_51) = k2_xboole_0(A_49,k2_xboole_0(B_50,C_51)) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_3033,plain,(
    ! [B_91,A_92,B_93] : k2_xboole_0(B_91,k2_xboole_0(A_92,B_93)) = k2_xboole_0(A_92,k2_xboole_0(B_93,B_91)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_659])).

tff(c_238,plain,(
    ! [B_42,A_41] : k2_xboole_0(B_42,k4_xboole_0(A_41,B_42)) = k2_xboole_0(B_42,k2_xboole_0(A_41,B_42)) ),
    inference(superposition,[status(thm),theory(equality)],[c_232,c_10])).

tff(c_1424,plain,(
    ! [B_62,A_63] : k2_xboole_0(B_62,k2_xboole_0(A_63,B_62)) = k2_xboole_0(B_62,A_63) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_238])).

tff(c_1509,plain,(
    k2_xboole_0('#skF_2',k2_xboole_0('#skF_4','#skF_3')) = k2_xboole_0('#skF_2','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_33,c_1424])).

tff(c_1531,plain,(
    k2_xboole_0('#skF_2',k2_xboole_0('#skF_4','#skF_3')) = k2_xboole_0('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_33,c_2,c_1509])).

tff(c_3107,plain,(
    k2_xboole_0('#skF_4',k2_xboole_0('#skF_3','#skF_2')) = k2_xboole_0('#skF_4','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_3033,c_1531])).

tff(c_6387,plain,(
    k2_xboole_0('#skF_4','#skF_2') = k2_xboole_0('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6225,c_3107])).

tff(c_7027,plain,(
    k4_xboole_0(k2_xboole_0('#skF_4','#skF_3'),'#skF_4') = k4_xboole_0('#skF_2','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_6387,c_275])).

tff(c_7052,plain,(
    k4_xboole_0('#skF_3','#skF_4') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_275,c_471,c_7027])).

tff(c_20,plain,(
    ! [A_17,B_18] : k4_xboole_0(A_17,k4_xboole_0(A_17,B_18)) = k3_xboole_0(A_17,B_18) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_6210,plain,(
    k4_xboole_0('#skF_3',k1_xboole_0) = k3_xboole_0('#skF_3','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_6191,c_20])).

tff(c_6224,plain,(
    k3_xboole_0('#skF_3','#skF_2') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_6210])).

tff(c_526,plain,(
    ! [A_47,B_48] : k4_xboole_0(A_47,k3_xboole_0(A_47,B_48)) = k3_xboole_0(A_47,k4_xboole_0(A_47,B_48)) ),
    inference(superposition,[status(thm),theory(equality)],[c_523,c_20])).

tff(c_563,plain,(
    ! [A_47,B_48] : k3_xboole_0(A_47,k4_xboole_0(A_47,B_48)) = k4_xboole_0(A_47,B_48) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_526])).

tff(c_7068,plain,(
    k4_xboole_0('#skF_3','#skF_4') = k3_xboole_0('#skF_3','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_7052,c_563])).

tff(c_7086,plain,(
    '#skF_2' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_7052,c_6224,c_7068])).

tff(c_7088,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_7086])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n023.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 11:49:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.67/2.28  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.67/2.29  
% 5.67/2.29  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.67/2.29  %$ r1_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 5.67/2.29  
% 5.67/2.29  %Foreground sorts:
% 5.67/2.29  
% 5.67/2.29  
% 5.67/2.29  %Background operators:
% 5.67/2.29  
% 5.67/2.29  
% 5.67/2.29  %Foreground operators:
% 5.67/2.29  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.67/2.29  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 5.67/2.29  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.67/2.29  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 5.67/2.29  tff('#skF_2', type, '#skF_2': $i).
% 5.67/2.29  tff('#skF_3', type, '#skF_3': $i).
% 5.67/2.29  tff('#skF_1', type, '#skF_1': $i).
% 5.67/2.29  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.67/2.29  tff('#skF_4', type, '#skF_4': $i).
% 5.67/2.29  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.67/2.29  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 5.67/2.29  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 5.67/2.29  
% 5.67/2.31  tff(f_60, negated_conjecture, ~(![A, B, C, D]: ((((k2_xboole_0(A, B) = k2_xboole_0(C, D)) & r1_xboole_0(C, A)) & r1_xboole_0(D, B)) => (C = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_xboole_1)).
% 5.67/2.31  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 5.67/2.31  tff(f_41, axiom, (![A, B]: (k4_xboole_0(k2_xboole_0(A, B), B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t40_xboole_1)).
% 5.67/2.31  tff(f_39, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 5.67/2.31  tff(f_35, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 5.67/2.31  tff(f_31, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 5.67/2.31  tff(f_45, axiom, (![A, B]: (k4_xboole_0(A, k3_xboole_0(A, B)) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_xboole_1)).
% 5.67/2.31  tff(f_37, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 5.67/2.31  tff(f_43, axiom, (![A, B, C]: (k4_xboole_0(k4_xboole_0(A, B), C) = k4_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_xboole_1)).
% 5.67/2.31  tff(f_51, axiom, (![A, B]: (k2_xboole_0(k3_xboole_0(A, B), k4_xboole_0(A, B)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t51_xboole_1)).
% 5.67/2.31  tff(f_47, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 5.67/2.31  tff(f_49, axiom, (![A, B, C]: (k2_xboole_0(k2_xboole_0(A, B), C) = k2_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_1)).
% 5.67/2.31  tff(c_26, plain, ('#skF_2'!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_60])).
% 5.67/2.31  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 5.67/2.31  tff(c_232, plain, (![A_41, B_42]: (k4_xboole_0(k2_xboole_0(A_41, B_42), B_42)=k4_xboole_0(A_41, B_42))), inference(cnfTransformation, [status(thm)], [f_41])).
% 5.67/2.31  tff(c_275, plain, (![B_2, A_1]: (k4_xboole_0(k2_xboole_0(B_2, A_1), B_2)=k4_xboole_0(A_1, B_2))), inference(superposition, [status(thm), theory('equality')], [c_2, c_232])).
% 5.67/2.31  tff(c_12, plain, (![A_9]: (k4_xboole_0(A_9, k1_xboole_0)=A_9)), inference(cnfTransformation, [status(thm)], [f_39])).
% 5.67/2.31  tff(c_28, plain, (r1_xboole_0('#skF_4', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_60])).
% 5.67/2.31  tff(c_47, plain, (![B_25, A_26]: (r1_xboole_0(B_25, A_26) | ~r1_xboole_0(A_26, B_25))), inference(cnfTransformation, [status(thm)], [f_35])).
% 5.67/2.31  tff(c_52, plain, (r1_xboole_0('#skF_2', '#skF_4')), inference(resolution, [status(thm)], [c_28, c_47])).
% 5.67/2.31  tff(c_99, plain, (![A_31, B_32]: (k3_xboole_0(A_31, B_32)=k1_xboole_0 | ~r1_xboole_0(A_31, B_32))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.67/2.31  tff(c_117, plain, (k3_xboole_0('#skF_2', '#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_52, c_99])).
% 5.67/2.31  tff(c_439, plain, (![A_45, B_46]: (k4_xboole_0(A_45, k3_xboole_0(A_45, B_46))=k4_xboole_0(A_45, B_46))), inference(cnfTransformation, [status(thm)], [f_45])).
% 5.67/2.31  tff(c_457, plain, (k4_xboole_0('#skF_2', k1_xboole_0)=k4_xboole_0('#skF_2', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_117, c_439])).
% 5.67/2.31  tff(c_471, plain, (k4_xboole_0('#skF_2', '#skF_4')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_12, c_457])).
% 5.67/2.31  tff(c_245, plain, (![A_41]: (k4_xboole_0(A_41, k1_xboole_0)=k2_xboole_0(A_41, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_232, c_12])).
% 5.67/2.31  tff(c_288, plain, (![A_41]: (k2_xboole_0(A_41, k1_xboole_0)=A_41)), inference(demodulation, [status(thm), theory('equality')], [c_12, c_245])).
% 5.67/2.31  tff(c_10, plain, (![A_7, B_8]: (k2_xboole_0(A_7, k4_xboole_0(B_8, A_7))=k2_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_37])).
% 5.67/2.31  tff(c_16, plain, (![A_12, B_13, C_14]: (k4_xboole_0(k4_xboole_0(A_12, B_13), C_14)=k4_xboole_0(A_12, k2_xboole_0(B_13, C_14)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 5.67/2.31  tff(c_24, plain, (![A_22, B_23]: (k2_xboole_0(k3_xboole_0(A_22, B_23), k4_xboole_0(A_22, B_23))=A_22)), inference(cnfTransformation, [status(thm)], [f_51])).
% 5.67/2.31  tff(c_445, plain, (![A_45, B_46]: (k2_xboole_0(k3_xboole_0(A_45, B_46), k4_xboole_0(A_45, B_46))=k2_xboole_0(k3_xboole_0(A_45, B_46), A_45))), inference(superposition, [status(thm), theory('equality')], [c_439, c_10])).
% 5.67/2.31  tff(c_1046, plain, (![A_56, B_57]: (k2_xboole_0(A_56, k3_xboole_0(A_56, B_57))=A_56)), inference(demodulation, [status(thm), theory('equality')], [c_24, c_2, c_445])).
% 5.67/2.31  tff(c_292, plain, (![A_43]: (k2_xboole_0(A_43, k1_xboole_0)=A_43)), inference(demodulation, [status(thm), theory('equality')], [c_12, c_245])).
% 5.67/2.31  tff(c_319, plain, (![A_1]: (k2_xboole_0(k1_xboole_0, A_1)=A_1)), inference(superposition, [status(thm), theory('equality')], [c_2, c_292])).
% 5.67/2.31  tff(c_1130, plain, (![B_58]: (k3_xboole_0(k1_xboole_0, B_58)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_1046, c_319])).
% 5.67/2.31  tff(c_18, plain, (![A_15, B_16]: (k4_xboole_0(A_15, k3_xboole_0(A_15, B_16))=k4_xboole_0(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_45])).
% 5.67/2.31  tff(c_1138, plain, (![B_58]: (k4_xboole_0(k1_xboole_0, k1_xboole_0)=k4_xboole_0(k1_xboole_0, B_58))), inference(superposition, [status(thm), theory('equality')], [c_1130, c_18])).
% 5.67/2.31  tff(c_1150, plain, (![B_58]: (k4_xboole_0(k1_xboole_0, B_58)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_12, c_1138])).
% 5.67/2.31  tff(c_523, plain, (![A_47, B_48]: (k4_xboole_0(A_47, k4_xboole_0(A_47, B_48))=k3_xboole_0(A_47, B_48))), inference(cnfTransformation, [status(thm)], [f_47])).
% 5.67/2.31  tff(c_562, plain, (![A_9]: (k4_xboole_0(A_9, A_9)=k3_xboole_0(A_9, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_12, c_523])).
% 5.67/2.31  tff(c_339, plain, (![A_44]: (k2_xboole_0(k1_xboole_0, A_44)=A_44)), inference(superposition, [status(thm), theory('equality')], [c_2, c_292])).
% 5.67/2.31  tff(c_14, plain, (![A_10, B_11]: (k4_xboole_0(k2_xboole_0(A_10, B_11), B_11)=k4_xboole_0(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_41])).
% 5.67/2.31  tff(c_349, plain, (![A_44]: (k4_xboole_0(k1_xboole_0, A_44)=k4_xboole_0(A_44, A_44))), inference(superposition, [status(thm), theory('equality')], [c_339, c_14])).
% 5.67/2.31  tff(c_1553, plain, (![A_44]: (k3_xboole_0(A_44, k1_xboole_0)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_1150, c_562, c_349])).
% 5.67/2.31  tff(c_1611, plain, (![A_65]: (k4_xboole_0(A_65, A_65)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_1553, c_562])).
% 5.67/2.31  tff(c_1645, plain, (![A_12, B_13]: (k4_xboole_0(A_12, k2_xboole_0(B_13, k4_xboole_0(A_12, B_13)))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_16, c_1611])).
% 5.67/2.31  tff(c_1659, plain, (![A_12, B_13]: (k4_xboole_0(A_12, k2_xboole_0(B_13, A_12))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_10, c_1645])).
% 5.67/2.31  tff(c_32, plain, (k2_xboole_0('#skF_3', '#skF_4')=k2_xboole_0('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_60])).
% 5.67/2.31  tff(c_33, plain, (k2_xboole_0('#skF_1', '#skF_2')=k2_xboole_0('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_32])).
% 5.67/2.31  tff(c_30, plain, (r1_xboole_0('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_60])).
% 5.67/2.31  tff(c_119, plain, (k3_xboole_0('#skF_3', '#skF_1')=k1_xboole_0), inference(resolution, [status(thm)], [c_30, c_99])).
% 5.67/2.31  tff(c_463, plain, (k4_xboole_0('#skF_3', k1_xboole_0)=k4_xboole_0('#skF_3', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_119, c_439])).
% 5.67/2.31  tff(c_473, plain, (k4_xboole_0('#skF_3', '#skF_1')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_12, c_463])).
% 5.67/2.31  tff(c_862, plain, (![A_53, B_54, C_55]: (k4_xboole_0(k4_xboole_0(A_53, B_54), C_55)=k4_xboole_0(A_53, k2_xboole_0(B_54, C_55)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 5.67/2.31  tff(c_6067, plain, (![C_117]: (k4_xboole_0('#skF_3', k2_xboole_0('#skF_1', C_117))=k4_xboole_0('#skF_3', C_117))), inference(superposition, [status(thm), theory('equality')], [c_473, c_862])).
% 5.67/2.31  tff(c_6169, plain, (k4_xboole_0('#skF_3', k2_xboole_0('#skF_4', '#skF_3'))=k4_xboole_0('#skF_3', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_33, c_6067])).
% 5.67/2.31  tff(c_6191, plain, (k4_xboole_0('#skF_3', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_1659, c_6169])).
% 5.67/2.31  tff(c_6213, plain, (k2_xboole_0('#skF_2', k1_xboole_0)=k2_xboole_0('#skF_2', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_6191, c_10])).
% 5.67/2.31  tff(c_6225, plain, (k2_xboole_0('#skF_3', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_288, c_2, c_6213])).
% 5.67/2.31  tff(c_659, plain, (![A_49, B_50, C_51]: (k2_xboole_0(k2_xboole_0(A_49, B_50), C_51)=k2_xboole_0(A_49, k2_xboole_0(B_50, C_51)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 5.67/2.31  tff(c_3033, plain, (![B_91, A_92, B_93]: (k2_xboole_0(B_91, k2_xboole_0(A_92, B_93))=k2_xboole_0(A_92, k2_xboole_0(B_93, B_91)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_659])).
% 5.67/2.31  tff(c_238, plain, (![B_42, A_41]: (k2_xboole_0(B_42, k4_xboole_0(A_41, B_42))=k2_xboole_0(B_42, k2_xboole_0(A_41, B_42)))), inference(superposition, [status(thm), theory('equality')], [c_232, c_10])).
% 5.67/2.31  tff(c_1424, plain, (![B_62, A_63]: (k2_xboole_0(B_62, k2_xboole_0(A_63, B_62))=k2_xboole_0(B_62, A_63))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_238])).
% 5.67/2.31  tff(c_1509, plain, (k2_xboole_0('#skF_2', k2_xboole_0('#skF_4', '#skF_3'))=k2_xboole_0('#skF_2', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_33, c_1424])).
% 5.67/2.31  tff(c_1531, plain, (k2_xboole_0('#skF_2', k2_xboole_0('#skF_4', '#skF_3'))=k2_xboole_0('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_33, c_2, c_1509])).
% 5.67/2.31  tff(c_3107, plain, (k2_xboole_0('#skF_4', k2_xboole_0('#skF_3', '#skF_2'))=k2_xboole_0('#skF_4', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_3033, c_1531])).
% 5.67/2.31  tff(c_6387, plain, (k2_xboole_0('#skF_4', '#skF_2')=k2_xboole_0('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_6225, c_3107])).
% 5.67/2.31  tff(c_7027, plain, (k4_xboole_0(k2_xboole_0('#skF_4', '#skF_3'), '#skF_4')=k4_xboole_0('#skF_2', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_6387, c_275])).
% 5.67/2.31  tff(c_7052, plain, (k4_xboole_0('#skF_3', '#skF_4')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_275, c_471, c_7027])).
% 5.67/2.31  tff(c_20, plain, (![A_17, B_18]: (k4_xboole_0(A_17, k4_xboole_0(A_17, B_18))=k3_xboole_0(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_47])).
% 5.67/2.31  tff(c_6210, plain, (k4_xboole_0('#skF_3', k1_xboole_0)=k3_xboole_0('#skF_3', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_6191, c_20])).
% 5.67/2.31  tff(c_6224, plain, (k3_xboole_0('#skF_3', '#skF_2')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_12, c_6210])).
% 5.67/2.31  tff(c_526, plain, (![A_47, B_48]: (k4_xboole_0(A_47, k3_xboole_0(A_47, B_48))=k3_xboole_0(A_47, k4_xboole_0(A_47, B_48)))), inference(superposition, [status(thm), theory('equality')], [c_523, c_20])).
% 5.67/2.31  tff(c_563, plain, (![A_47, B_48]: (k3_xboole_0(A_47, k4_xboole_0(A_47, B_48))=k4_xboole_0(A_47, B_48))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_526])).
% 5.67/2.31  tff(c_7068, plain, (k4_xboole_0('#skF_3', '#skF_4')=k3_xboole_0('#skF_3', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_7052, c_563])).
% 5.67/2.31  tff(c_7086, plain, ('#skF_2'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_7052, c_6224, c_7068])).
% 5.67/2.31  tff(c_7088, plain, $false, inference(negUnitSimplification, [status(thm)], [c_26, c_7086])).
% 5.67/2.31  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.67/2.31  
% 5.67/2.31  Inference rules
% 5.67/2.31  ----------------------
% 5.67/2.31  #Ref     : 0
% 5.67/2.31  #Sup     : 1801
% 5.67/2.31  #Fact    : 0
% 5.67/2.31  #Define  : 0
% 5.67/2.31  #Split   : 0
% 5.67/2.31  #Chain   : 0
% 5.67/2.31  #Close   : 0
% 5.67/2.31  
% 5.67/2.31  Ordering : KBO
% 5.67/2.31  
% 5.67/2.31  Simplification rules
% 5.67/2.31  ----------------------
% 5.67/2.31  #Subsume      : 46
% 5.67/2.31  #Demod        : 1856
% 5.67/2.31  #Tautology    : 1125
% 5.67/2.31  #SimpNegUnit  : 1
% 5.67/2.31  #BackRed      : 7
% 5.67/2.31  
% 5.67/2.31  #Partial instantiations: 0
% 5.67/2.31  #Strategies tried      : 1
% 5.67/2.31  
% 5.67/2.31  Timing (in seconds)
% 5.67/2.31  ----------------------
% 5.67/2.32  Preprocessing        : 0.29
% 5.67/2.32  Parsing              : 0.16
% 5.67/2.32  CNF conversion       : 0.02
% 5.67/2.32  Main loop            : 1.15
% 5.67/2.32  Inferencing          : 0.31
% 5.67/2.32  Reduction            : 0.60
% 5.67/2.32  Demodulation         : 0.52
% 5.67/2.32  BG Simplification    : 0.04
% 5.67/2.32  Subsumption          : 0.14
% 5.67/2.32  Abstraction          : 0.05
% 5.67/2.32  MUC search           : 0.00
% 5.67/2.32  Cooper               : 0.00
% 5.67/2.32  Total                : 1.48
% 5.67/2.32  Index Insertion      : 0.00
% 5.67/2.32  Index Deletion       : 0.00
% 5.67/2.32  Index Matching       : 0.00
% 5.67/2.32  BG Taut test         : 0.00
%------------------------------------------------------------------------------
