%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:45:19 EST 2020

% Result     : Theorem 17.16s
% Output     : CNFRefutation 17.16s
% Verified   : 
% Statistics : Number of formulae       :   98 ( 325 expanded)
%              Number of leaves         :   26 ( 120 expanded)
%              Depth                    :   13
%              Number of atoms          :   99 ( 413 expanded)
%              Number of equality atoms :   72 ( 231 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

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

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_35,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_62,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r1_tarski(A,k4_xboole_0(B,C))
       => ( r1_tarski(A,B)
          & r1_xboole_0(A,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_45,axiom,(
    ! [A,B,C] : k3_xboole_0(A,k4_xboole_0(B,C)) = k4_xboole_0(k3_xboole_0(A,B),C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_xboole_1)).

tff(f_47,axiom,(
    ! [A,B,C] : k3_xboole_0(A,k4_xboole_0(B,C)) = k4_xboole_0(k3_xboole_0(A,B),k3_xboole_0(A,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_xboole_1)).

tff(f_49,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

tff(f_51,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_37,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k5_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

tff(f_55,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_53,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_39,axiom,(
    ! [A,B,C] : k3_xboole_0(A,k2_xboole_0(B,C)) = k2_xboole_0(k3_xboole_0(A,B),k3_xboole_0(A,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_xboole_1)).

tff(c_156,plain,(
    ! [A_33,B_34] :
      ( r1_tarski(A_33,B_34)
      | k4_xboole_0(A_33,B_34) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_30,plain,
    ( ~ r1_xboole_0('#skF_1','#skF_3')
    | ~ r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_60,plain,(
    ~ r1_tarski('#skF_1','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_30])).

tff(c_160,plain,(
    k4_xboole_0('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_156,c_60])).

tff(c_32,plain,(
    r1_tarski('#skF_1',k4_xboole_0('#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_163,plain,(
    ! [A_35,B_36] :
      ( k3_xboole_0(A_35,B_36) = A_35
      | ~ r1_tarski(A_35,B_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_171,plain,(
    k3_xboole_0('#skF_1',k4_xboole_0('#skF_2','#skF_3')) = '#skF_1' ),
    inference(resolution,[status(thm)],[c_32,c_163])).

tff(c_378,plain,(
    ! [A_55,B_56,C_57] : k4_xboole_0(k3_xboole_0(A_55,B_56),C_57) = k3_xboole_0(A_55,k4_xboole_0(B_56,C_57)) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_419,plain,(
    ! [C_57] : k3_xboole_0('#skF_1',k4_xboole_0(k4_xboole_0('#skF_2','#skF_3'),C_57)) = k4_xboole_0('#skF_1',C_57) ),
    inference(superposition,[status(thm),theory(equality)],[c_171,c_378])).

tff(c_702,plain,(
    ! [A_69,B_70,C_71] : k4_xboole_0(k3_xboole_0(A_69,B_70),k3_xboole_0(A_69,C_71)) = k3_xboole_0(A_69,k4_xboole_0(B_70,C_71)) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_760,plain,(
    ! [C_71] : k3_xboole_0('#skF_1',k4_xboole_0(k4_xboole_0('#skF_2','#skF_3'),C_71)) = k4_xboole_0('#skF_1',k3_xboole_0('#skF_1',C_71)) ),
    inference(superposition,[status(thm),theory(equality)],[c_171,c_702])).

tff(c_776,plain,(
    ! [C_71] : k4_xboole_0('#skF_1',k3_xboole_0('#skF_1',C_71)) = k4_xboole_0('#skF_1',C_71) ),
    inference(demodulation,[status(thm),theory(equality)],[c_419,c_760])).

tff(c_176,plain,(
    ! [A_37,B_38] :
      ( k4_xboole_0(A_37,B_38) = k1_xboole_0
      | ~ r1_tarski(A_37,B_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_184,plain,(
    k4_xboole_0('#skF_1',k4_xboole_0('#skF_2','#skF_3')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_32,c_176])).

tff(c_18,plain,(
    ! [A_14,B_15,C_16] : k4_xboole_0(k3_xboole_0(A_14,B_15),C_16) = k3_xboole_0(A_14,k4_xboole_0(B_15,C_16)) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_1664,plain,(
    ! [A_99,B_100,C_101] : k3_xboole_0(A_99,k4_xboole_0(B_100,k3_xboole_0(A_99,C_101))) = k3_xboole_0(A_99,k4_xboole_0(B_100,C_101)) ),
    inference(superposition,[status(thm),theory(equality)],[c_702,c_18])).

tff(c_1903,plain,(
    ! [B_104] : k3_xboole_0('#skF_1',k4_xboole_0(B_104,k4_xboole_0('#skF_2','#skF_3'))) = k3_xboole_0('#skF_1',k4_xboole_0(B_104,'#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_171,c_1664])).

tff(c_1944,plain,(
    k3_xboole_0('#skF_1',k4_xboole_0(k4_xboole_0('#skF_2','#skF_3'),'#skF_1')) = k4_xboole_0('#skF_1',k4_xboole_0('#skF_2','#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1903,c_419])).

tff(c_1981,plain,(
    k4_xboole_0('#skF_1','#skF_1') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_419,c_184,c_1944])).

tff(c_8,plain,(
    ! [A_5,B_6] :
      ( r1_tarski(A_5,B_6)
      | k4_xboole_0(A_5,B_6) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_170,plain,(
    ! [A_5,B_6] :
      ( k3_xboole_0(A_5,B_6) = A_5
      | k4_xboole_0(A_5,B_6) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_8,c_163])).

tff(c_2019,plain,(
    k3_xboole_0('#skF_1','#skF_1') = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_1981,c_170])).

tff(c_22,plain,(
    ! [A_20] : k5_xboole_0(A_20,k1_xboole_0) = A_20 ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_24,plain,(
    ! [A_21,B_22] : r1_xboole_0(k4_xboole_0(A_21,B_22),B_22) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_193,plain,(
    ! [A_41,B_42] :
      ( k3_xboole_0(A_41,B_42) = k1_xboole_0
      | ~ r1_xboole_0(A_41,B_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_205,plain,(
    ! [A_21,B_22] : k3_xboole_0(k4_xboole_0(A_21,B_22),B_22) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_24,c_193])).

tff(c_476,plain,(
    ! [A_59,B_60,C_61] : r1_xboole_0(k3_xboole_0(A_59,k4_xboole_0(B_60,C_61)),C_61) ),
    inference(superposition,[status(thm),theory(equality)],[c_378,c_24])).

tff(c_513,plain,(
    ! [C_62] : r1_xboole_0(k1_xboole_0,C_62) ),
    inference(superposition,[status(thm),theory(equality)],[c_205,c_476])).

tff(c_4,plain,(
    ! [A_3,B_4] :
      ( k3_xboole_0(A_3,B_4) = k1_xboole_0
      | ~ r1_xboole_0(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_517,plain,(
    ! [C_62] : k3_xboole_0(k1_xboole_0,C_62) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_513,c_4])).

tff(c_261,plain,(
    ! [A_48,B_49] : k5_xboole_0(A_48,k3_xboole_0(A_48,B_49)) = k4_xboole_0(A_48,B_49) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_61,plain,(
    ! [B_30,A_31] : k5_xboole_0(B_30,A_31) = k5_xboole_0(A_31,B_30) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_77,plain,(
    ! [A_31] : k5_xboole_0(k1_xboole_0,A_31) = A_31 ),
    inference(superposition,[status(thm),theory(equality)],[c_61,c_22])).

tff(c_268,plain,(
    ! [B_49] : k4_xboole_0(k1_xboole_0,B_49) = k3_xboole_0(k1_xboole_0,B_49) ),
    inference(superposition,[status(thm),theory(equality)],[c_261,c_77])).

tff(c_642,plain,(
    ! [B_68] : k4_xboole_0(k1_xboole_0,B_68) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_517,c_268])).

tff(c_28,plain,(
    ! [A_24,B_25] : k5_xboole_0(A_24,k4_xboole_0(B_25,A_24)) = k2_xboole_0(A_24,B_25) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_654,plain,(
    ! [B_68] : k5_xboole_0(B_68,k1_xboole_0) = k2_xboole_0(B_68,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_642,c_28])).

tff(c_668,plain,(
    ! [B_68] : k2_xboole_0(B_68,k1_xboole_0) = B_68 ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_654])).

tff(c_26,plain,(
    ! [A_23] : k5_xboole_0(A_23,A_23) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_14,plain,(
    ! [A_9,B_10,C_11] : k2_xboole_0(k3_xboole_0(A_9,B_10),k3_xboole_0(A_9,C_11)) = k3_xboole_0(A_9,k2_xboole_0(B_10,C_11)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_20,plain,(
    ! [A_17,B_18,C_19] : k4_xboole_0(k3_xboole_0(A_17,B_18),k3_xboole_0(A_17,C_19)) = k3_xboole_0(A_17,k4_xboole_0(B_18,C_19)) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_714,plain,(
    ! [A_69,C_71,B_70] : k5_xboole_0(k3_xboole_0(A_69,C_71),k3_xboole_0(A_69,k4_xboole_0(B_70,C_71))) = k2_xboole_0(k3_xboole_0(A_69,C_71),k3_xboole_0(A_69,B_70)) ),
    inference(superposition,[status(thm),theory(equality)],[c_702,c_28])).

tff(c_2506,plain,(
    ! [A_114,C_115,B_116] : k5_xboole_0(k3_xboole_0(A_114,C_115),k3_xboole_0(A_114,k4_xboole_0(B_116,C_115))) = k3_xboole_0(A_114,k2_xboole_0(C_115,B_116)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_714])).

tff(c_2583,plain,(
    ! [A_114,A_17,C_19,B_18] : k5_xboole_0(k3_xboole_0(A_114,k3_xboole_0(A_17,C_19)),k3_xboole_0(A_114,k3_xboole_0(A_17,k4_xboole_0(B_18,C_19)))) = k3_xboole_0(A_114,k2_xboole_0(k3_xboole_0(A_17,C_19),k3_xboole_0(A_17,B_18))) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_2506])).

tff(c_40305,plain,(
    ! [A_450,A_451,C_452,B_453] : k5_xboole_0(k3_xboole_0(A_450,k3_xboole_0(A_451,C_452)),k3_xboole_0(A_450,k3_xboole_0(A_451,k4_xboole_0(B_453,C_452)))) = k3_xboole_0(A_450,k3_xboole_0(A_451,k2_xboole_0(C_452,B_453))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_2583])).

tff(c_40809,plain,(
    ! [A_450,B_453,C_62] : k5_xboole_0(k3_xboole_0(A_450,k1_xboole_0),k3_xboole_0(A_450,k3_xboole_0(k1_xboole_0,k4_xboole_0(B_453,C_62)))) = k3_xboole_0(A_450,k3_xboole_0(k1_xboole_0,k2_xboole_0(C_62,B_453))) ),
    inference(superposition,[status(thm),theory(equality)],[c_517,c_40305])).

tff(c_40918,plain,(
    ! [A_450] : k3_xboole_0(A_450,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_517,c_26,c_517,c_40809])).

tff(c_221,plain,(
    ! [A_45,B_46] : k5_xboole_0(A_45,k4_xboole_0(B_46,A_45)) = k2_xboole_0(A_45,B_46) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_228,plain,(
    ! [B_46] : k4_xboole_0(B_46,k1_xboole_0) = k2_xboole_0(k1_xboole_0,B_46) ),
    inference(superposition,[status(thm),theory(equality)],[c_221,c_77])).

tff(c_578,plain,(
    ! [B_49] : k4_xboole_0(k1_xboole_0,B_49) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_517,c_268])).

tff(c_1368,plain,(
    ! [C_90,A_91,B_92] : k5_xboole_0(C_90,k3_xboole_0(A_91,k4_xboole_0(B_92,C_90))) = k2_xboole_0(C_90,k3_xboole_0(A_91,B_92)) ),
    inference(superposition,[status(thm),theory(equality)],[c_378,c_28])).

tff(c_12,plain,(
    ! [A_7,B_8] : k5_xboole_0(A_7,k3_xboole_0(A_7,B_8)) = k4_xboole_0(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_6331,plain,(
    ! [A_180,B_181] : k4_xboole_0(A_180,k4_xboole_0(B_181,A_180)) = k2_xboole_0(A_180,k3_xboole_0(A_180,B_181)) ),
    inference(superposition,[status(thm),theory(equality)],[c_1368,c_12])).

tff(c_6499,plain,(
    ! [B_49] : k2_xboole_0(B_49,k3_xboole_0(B_49,k1_xboole_0)) = k4_xboole_0(B_49,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_578,c_6331])).

tff(c_6534,plain,(
    ! [B_49] : k2_xboole_0(B_49,k3_xboole_0(B_49,k1_xboole_0)) = k2_xboole_0(k1_xboole_0,B_49) ),
    inference(demodulation,[status(thm),theory(equality)],[c_228,c_6499])).

tff(c_40944,plain,(
    ! [B_49] : k2_xboole_0(k1_xboole_0,B_49) = k2_xboole_0(B_49,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40918,c_6534])).

tff(c_40963,plain,(
    ! [B_49] : k2_xboole_0(k1_xboole_0,B_49) = B_49 ),
    inference(demodulation,[status(thm),theory(equality)],[c_668,c_40944])).

tff(c_509,plain,(
    r1_xboole_0('#skF_1','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_171,c_476])).

tff(c_521,plain,(
    k3_xboole_0('#skF_1','#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_509,c_4])).

tff(c_41863,plain,(
    ! [A_458,C_459,A_460,B_461] : k5_xboole_0(k3_xboole_0(A_458,C_459),k3_xboole_0(A_460,k3_xboole_0(A_458,k4_xboole_0(B_461,C_459)))) = k2_xboole_0(k3_xboole_0(A_458,C_459),k3_xboole_0(A_460,k3_xboole_0(A_458,B_461))) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_1368])).

tff(c_42255,plain,(
    ! [A_460] : k2_xboole_0(k3_xboole_0('#skF_1','#skF_3'),k3_xboole_0(A_460,k3_xboole_0('#skF_1','#skF_2'))) = k5_xboole_0(k3_xboole_0('#skF_1','#skF_3'),k3_xboole_0(A_460,'#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_171,c_41863])).

tff(c_42359,plain,(
    ! [A_462] : k3_xboole_0(A_462,k3_xboole_0('#skF_1','#skF_2')) = k3_xboole_0(A_462,'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40963,c_77,c_521,c_521,c_42255])).

tff(c_42526,plain,(
    k4_xboole_0('#skF_1',k3_xboole_0('#skF_1','#skF_2')) = k4_xboole_0('#skF_1',k3_xboole_0('#skF_1','#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_42359,c_776])).

tff(c_42629,plain,(
    k4_xboole_0('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_776,c_1981,c_2019,c_42526])).

tff(c_42631,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_160,c_42629])).

tff(c_42632,plain,(
    ~ r1_xboole_0('#skF_1','#skF_3') ),
    inference(splitRight,[status(thm)],[c_30])).

tff(c_42729,plain,(
    ! [A_466,B_467] :
      ( k3_xboole_0(A_466,B_467) = A_466
      | ~ r1_tarski(A_466,B_467) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_42737,plain,(
    k3_xboole_0('#skF_1',k4_xboole_0('#skF_2','#skF_3')) = '#skF_1' ),
    inference(resolution,[status(thm)],[c_32,c_42729])).

tff(c_42988,plain,(
    ! [A_486,B_487,C_488] : k4_xboole_0(k3_xboole_0(A_486,B_487),C_488) = k3_xboole_0(A_486,k4_xboole_0(B_487,C_488)) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_43234,plain,(
    ! [A_495,B_496,C_497] : r1_xboole_0(k3_xboole_0(A_495,k4_xboole_0(B_496,C_497)),C_497) ),
    inference(superposition,[status(thm),theory(equality)],[c_42988,c_24])).

tff(c_43276,plain,(
    r1_xboole_0('#skF_1','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_42737,c_43234])).

tff(c_43280,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_42632,c_43276])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n016.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 14:20:04 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 17.16/8.82  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 17.16/8.83  
% 17.16/8.83  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 17.16/8.83  %$ r1_xboole_0 > r1_tarski > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 17.16/8.83  
% 17.16/8.83  %Foreground sorts:
% 17.16/8.83  
% 17.16/8.83  
% 17.16/8.83  %Background operators:
% 17.16/8.83  
% 17.16/8.83  
% 17.16/8.83  %Foreground operators:
% 17.16/8.83  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 17.16/8.83  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 17.16/8.83  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 17.16/8.83  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 17.16/8.83  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 17.16/8.83  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 17.16/8.83  tff('#skF_2', type, '#skF_2': $i).
% 17.16/8.83  tff('#skF_3', type, '#skF_3': $i).
% 17.16/8.83  tff('#skF_1', type, '#skF_1': $i).
% 17.16/8.83  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 17.16/8.83  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 17.16/8.83  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 17.16/8.83  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 17.16/8.83  
% 17.16/8.85  tff(f_35, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 17.16/8.85  tff(f_62, negated_conjecture, ~(![A, B, C]: (r1_tarski(A, k4_xboole_0(B, C)) => (r1_tarski(A, B) & r1_xboole_0(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t106_xboole_1)).
% 17.16/8.85  tff(f_43, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 17.16/8.85  tff(f_45, axiom, (![A, B, C]: (k3_xboole_0(A, k4_xboole_0(B, C)) = k4_xboole_0(k3_xboole_0(A, B), C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_xboole_1)).
% 17.16/8.85  tff(f_47, axiom, (![A, B, C]: (k3_xboole_0(A, k4_xboole_0(B, C)) = k4_xboole_0(k3_xboole_0(A, B), k3_xboole_0(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t50_xboole_1)).
% 17.16/8.85  tff(f_49, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 17.16/8.85  tff(f_51, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_xboole_1)).
% 17.16/8.85  tff(f_31, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 17.16/8.85  tff(f_37, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 17.16/8.85  tff(f_27, axiom, (![A, B]: (k5_xboole_0(A, B) = k5_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 17.16/8.85  tff(f_55, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_xboole_1)).
% 17.16/8.85  tff(f_53, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t92_xboole_1)).
% 17.16/8.85  tff(f_39, axiom, (![A, B, C]: (k3_xboole_0(A, k2_xboole_0(B, C)) = k2_xboole_0(k3_xboole_0(A, B), k3_xboole_0(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t23_xboole_1)).
% 17.16/8.85  tff(c_156, plain, (![A_33, B_34]: (r1_tarski(A_33, B_34) | k4_xboole_0(A_33, B_34)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_35])).
% 17.16/8.85  tff(c_30, plain, (~r1_xboole_0('#skF_1', '#skF_3') | ~r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_62])).
% 17.16/8.85  tff(c_60, plain, (~r1_tarski('#skF_1', '#skF_2')), inference(splitLeft, [status(thm)], [c_30])).
% 17.16/8.85  tff(c_160, plain, (k4_xboole_0('#skF_1', '#skF_2')!=k1_xboole_0), inference(resolution, [status(thm)], [c_156, c_60])).
% 17.16/8.85  tff(c_32, plain, (r1_tarski('#skF_1', k4_xboole_0('#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_62])).
% 17.16/8.85  tff(c_163, plain, (![A_35, B_36]: (k3_xboole_0(A_35, B_36)=A_35 | ~r1_tarski(A_35, B_36))), inference(cnfTransformation, [status(thm)], [f_43])).
% 17.16/8.85  tff(c_171, plain, (k3_xboole_0('#skF_1', k4_xboole_0('#skF_2', '#skF_3'))='#skF_1'), inference(resolution, [status(thm)], [c_32, c_163])).
% 17.16/8.85  tff(c_378, plain, (![A_55, B_56, C_57]: (k4_xboole_0(k3_xboole_0(A_55, B_56), C_57)=k3_xboole_0(A_55, k4_xboole_0(B_56, C_57)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 17.16/8.85  tff(c_419, plain, (![C_57]: (k3_xboole_0('#skF_1', k4_xboole_0(k4_xboole_0('#skF_2', '#skF_3'), C_57))=k4_xboole_0('#skF_1', C_57))), inference(superposition, [status(thm), theory('equality')], [c_171, c_378])).
% 17.16/8.85  tff(c_702, plain, (![A_69, B_70, C_71]: (k4_xboole_0(k3_xboole_0(A_69, B_70), k3_xboole_0(A_69, C_71))=k3_xboole_0(A_69, k4_xboole_0(B_70, C_71)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 17.16/8.85  tff(c_760, plain, (![C_71]: (k3_xboole_0('#skF_1', k4_xboole_0(k4_xboole_0('#skF_2', '#skF_3'), C_71))=k4_xboole_0('#skF_1', k3_xboole_0('#skF_1', C_71)))), inference(superposition, [status(thm), theory('equality')], [c_171, c_702])).
% 17.16/8.85  tff(c_776, plain, (![C_71]: (k4_xboole_0('#skF_1', k3_xboole_0('#skF_1', C_71))=k4_xboole_0('#skF_1', C_71))), inference(demodulation, [status(thm), theory('equality')], [c_419, c_760])).
% 17.16/8.85  tff(c_176, plain, (![A_37, B_38]: (k4_xboole_0(A_37, B_38)=k1_xboole_0 | ~r1_tarski(A_37, B_38))), inference(cnfTransformation, [status(thm)], [f_35])).
% 17.16/8.85  tff(c_184, plain, (k4_xboole_0('#skF_1', k4_xboole_0('#skF_2', '#skF_3'))=k1_xboole_0), inference(resolution, [status(thm)], [c_32, c_176])).
% 17.16/8.85  tff(c_18, plain, (![A_14, B_15, C_16]: (k4_xboole_0(k3_xboole_0(A_14, B_15), C_16)=k3_xboole_0(A_14, k4_xboole_0(B_15, C_16)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 17.16/8.85  tff(c_1664, plain, (![A_99, B_100, C_101]: (k3_xboole_0(A_99, k4_xboole_0(B_100, k3_xboole_0(A_99, C_101)))=k3_xboole_0(A_99, k4_xboole_0(B_100, C_101)))), inference(superposition, [status(thm), theory('equality')], [c_702, c_18])).
% 17.16/8.85  tff(c_1903, plain, (![B_104]: (k3_xboole_0('#skF_1', k4_xboole_0(B_104, k4_xboole_0('#skF_2', '#skF_3')))=k3_xboole_0('#skF_1', k4_xboole_0(B_104, '#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_171, c_1664])).
% 17.16/8.85  tff(c_1944, plain, (k3_xboole_0('#skF_1', k4_xboole_0(k4_xboole_0('#skF_2', '#skF_3'), '#skF_1'))=k4_xboole_0('#skF_1', k4_xboole_0('#skF_2', '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_1903, c_419])).
% 17.16/8.85  tff(c_1981, plain, (k4_xboole_0('#skF_1', '#skF_1')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_419, c_184, c_1944])).
% 17.16/8.85  tff(c_8, plain, (![A_5, B_6]: (r1_tarski(A_5, B_6) | k4_xboole_0(A_5, B_6)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_35])).
% 17.16/8.85  tff(c_170, plain, (![A_5, B_6]: (k3_xboole_0(A_5, B_6)=A_5 | k4_xboole_0(A_5, B_6)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_163])).
% 17.16/8.85  tff(c_2019, plain, (k3_xboole_0('#skF_1', '#skF_1')='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_1981, c_170])).
% 17.16/8.85  tff(c_22, plain, (![A_20]: (k5_xboole_0(A_20, k1_xboole_0)=A_20)), inference(cnfTransformation, [status(thm)], [f_49])).
% 17.16/8.85  tff(c_24, plain, (![A_21, B_22]: (r1_xboole_0(k4_xboole_0(A_21, B_22), B_22))), inference(cnfTransformation, [status(thm)], [f_51])).
% 17.16/8.85  tff(c_193, plain, (![A_41, B_42]: (k3_xboole_0(A_41, B_42)=k1_xboole_0 | ~r1_xboole_0(A_41, B_42))), inference(cnfTransformation, [status(thm)], [f_31])).
% 17.16/8.85  tff(c_205, plain, (![A_21, B_22]: (k3_xboole_0(k4_xboole_0(A_21, B_22), B_22)=k1_xboole_0)), inference(resolution, [status(thm)], [c_24, c_193])).
% 17.16/8.85  tff(c_476, plain, (![A_59, B_60, C_61]: (r1_xboole_0(k3_xboole_0(A_59, k4_xboole_0(B_60, C_61)), C_61))), inference(superposition, [status(thm), theory('equality')], [c_378, c_24])).
% 17.16/8.85  tff(c_513, plain, (![C_62]: (r1_xboole_0(k1_xboole_0, C_62))), inference(superposition, [status(thm), theory('equality')], [c_205, c_476])).
% 17.16/8.85  tff(c_4, plain, (![A_3, B_4]: (k3_xboole_0(A_3, B_4)=k1_xboole_0 | ~r1_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 17.16/8.85  tff(c_517, plain, (![C_62]: (k3_xboole_0(k1_xboole_0, C_62)=k1_xboole_0)), inference(resolution, [status(thm)], [c_513, c_4])).
% 17.16/8.85  tff(c_261, plain, (![A_48, B_49]: (k5_xboole_0(A_48, k3_xboole_0(A_48, B_49))=k4_xboole_0(A_48, B_49))), inference(cnfTransformation, [status(thm)], [f_37])).
% 17.16/8.85  tff(c_61, plain, (![B_30, A_31]: (k5_xboole_0(B_30, A_31)=k5_xboole_0(A_31, B_30))), inference(cnfTransformation, [status(thm)], [f_27])).
% 17.16/8.85  tff(c_77, plain, (![A_31]: (k5_xboole_0(k1_xboole_0, A_31)=A_31)), inference(superposition, [status(thm), theory('equality')], [c_61, c_22])).
% 17.16/8.85  tff(c_268, plain, (![B_49]: (k4_xboole_0(k1_xboole_0, B_49)=k3_xboole_0(k1_xboole_0, B_49))), inference(superposition, [status(thm), theory('equality')], [c_261, c_77])).
% 17.16/8.85  tff(c_642, plain, (![B_68]: (k4_xboole_0(k1_xboole_0, B_68)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_517, c_268])).
% 17.16/8.85  tff(c_28, plain, (![A_24, B_25]: (k5_xboole_0(A_24, k4_xboole_0(B_25, A_24))=k2_xboole_0(A_24, B_25))), inference(cnfTransformation, [status(thm)], [f_55])).
% 17.16/8.85  tff(c_654, plain, (![B_68]: (k5_xboole_0(B_68, k1_xboole_0)=k2_xboole_0(B_68, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_642, c_28])).
% 17.16/8.85  tff(c_668, plain, (![B_68]: (k2_xboole_0(B_68, k1_xboole_0)=B_68)), inference(demodulation, [status(thm), theory('equality')], [c_22, c_654])).
% 17.16/8.85  tff(c_26, plain, (![A_23]: (k5_xboole_0(A_23, A_23)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_53])).
% 17.16/8.85  tff(c_14, plain, (![A_9, B_10, C_11]: (k2_xboole_0(k3_xboole_0(A_9, B_10), k3_xboole_0(A_9, C_11))=k3_xboole_0(A_9, k2_xboole_0(B_10, C_11)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 17.16/8.85  tff(c_20, plain, (![A_17, B_18, C_19]: (k4_xboole_0(k3_xboole_0(A_17, B_18), k3_xboole_0(A_17, C_19))=k3_xboole_0(A_17, k4_xboole_0(B_18, C_19)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 17.16/8.85  tff(c_714, plain, (![A_69, C_71, B_70]: (k5_xboole_0(k3_xboole_0(A_69, C_71), k3_xboole_0(A_69, k4_xboole_0(B_70, C_71)))=k2_xboole_0(k3_xboole_0(A_69, C_71), k3_xboole_0(A_69, B_70)))), inference(superposition, [status(thm), theory('equality')], [c_702, c_28])).
% 17.16/8.85  tff(c_2506, plain, (![A_114, C_115, B_116]: (k5_xboole_0(k3_xboole_0(A_114, C_115), k3_xboole_0(A_114, k4_xboole_0(B_116, C_115)))=k3_xboole_0(A_114, k2_xboole_0(C_115, B_116)))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_714])).
% 17.16/8.85  tff(c_2583, plain, (![A_114, A_17, C_19, B_18]: (k5_xboole_0(k3_xboole_0(A_114, k3_xboole_0(A_17, C_19)), k3_xboole_0(A_114, k3_xboole_0(A_17, k4_xboole_0(B_18, C_19))))=k3_xboole_0(A_114, k2_xboole_0(k3_xboole_0(A_17, C_19), k3_xboole_0(A_17, B_18))))), inference(superposition, [status(thm), theory('equality')], [c_20, c_2506])).
% 17.16/8.85  tff(c_40305, plain, (![A_450, A_451, C_452, B_453]: (k5_xboole_0(k3_xboole_0(A_450, k3_xboole_0(A_451, C_452)), k3_xboole_0(A_450, k3_xboole_0(A_451, k4_xboole_0(B_453, C_452))))=k3_xboole_0(A_450, k3_xboole_0(A_451, k2_xboole_0(C_452, B_453))))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_2583])).
% 17.16/8.85  tff(c_40809, plain, (![A_450, B_453, C_62]: (k5_xboole_0(k3_xboole_0(A_450, k1_xboole_0), k3_xboole_0(A_450, k3_xboole_0(k1_xboole_0, k4_xboole_0(B_453, C_62))))=k3_xboole_0(A_450, k3_xboole_0(k1_xboole_0, k2_xboole_0(C_62, B_453))))), inference(superposition, [status(thm), theory('equality')], [c_517, c_40305])).
% 17.16/8.85  tff(c_40918, plain, (![A_450]: (k3_xboole_0(A_450, k1_xboole_0)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_517, c_26, c_517, c_40809])).
% 17.16/8.85  tff(c_221, plain, (![A_45, B_46]: (k5_xboole_0(A_45, k4_xboole_0(B_46, A_45))=k2_xboole_0(A_45, B_46))), inference(cnfTransformation, [status(thm)], [f_55])).
% 17.16/8.85  tff(c_228, plain, (![B_46]: (k4_xboole_0(B_46, k1_xboole_0)=k2_xboole_0(k1_xboole_0, B_46))), inference(superposition, [status(thm), theory('equality')], [c_221, c_77])).
% 17.16/8.85  tff(c_578, plain, (![B_49]: (k4_xboole_0(k1_xboole_0, B_49)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_517, c_268])).
% 17.16/8.85  tff(c_1368, plain, (![C_90, A_91, B_92]: (k5_xboole_0(C_90, k3_xboole_0(A_91, k4_xboole_0(B_92, C_90)))=k2_xboole_0(C_90, k3_xboole_0(A_91, B_92)))), inference(superposition, [status(thm), theory('equality')], [c_378, c_28])).
% 17.16/8.85  tff(c_12, plain, (![A_7, B_8]: (k5_xboole_0(A_7, k3_xboole_0(A_7, B_8))=k4_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_37])).
% 17.16/8.85  tff(c_6331, plain, (![A_180, B_181]: (k4_xboole_0(A_180, k4_xboole_0(B_181, A_180))=k2_xboole_0(A_180, k3_xboole_0(A_180, B_181)))), inference(superposition, [status(thm), theory('equality')], [c_1368, c_12])).
% 17.16/8.85  tff(c_6499, plain, (![B_49]: (k2_xboole_0(B_49, k3_xboole_0(B_49, k1_xboole_0))=k4_xboole_0(B_49, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_578, c_6331])).
% 17.16/8.85  tff(c_6534, plain, (![B_49]: (k2_xboole_0(B_49, k3_xboole_0(B_49, k1_xboole_0))=k2_xboole_0(k1_xboole_0, B_49))), inference(demodulation, [status(thm), theory('equality')], [c_228, c_6499])).
% 17.16/8.85  tff(c_40944, plain, (![B_49]: (k2_xboole_0(k1_xboole_0, B_49)=k2_xboole_0(B_49, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_40918, c_6534])).
% 17.16/8.85  tff(c_40963, plain, (![B_49]: (k2_xboole_0(k1_xboole_0, B_49)=B_49)), inference(demodulation, [status(thm), theory('equality')], [c_668, c_40944])).
% 17.16/8.85  tff(c_509, plain, (r1_xboole_0('#skF_1', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_171, c_476])).
% 17.16/8.85  tff(c_521, plain, (k3_xboole_0('#skF_1', '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_509, c_4])).
% 17.16/8.85  tff(c_41863, plain, (![A_458, C_459, A_460, B_461]: (k5_xboole_0(k3_xboole_0(A_458, C_459), k3_xboole_0(A_460, k3_xboole_0(A_458, k4_xboole_0(B_461, C_459))))=k2_xboole_0(k3_xboole_0(A_458, C_459), k3_xboole_0(A_460, k3_xboole_0(A_458, B_461))))), inference(superposition, [status(thm), theory('equality')], [c_20, c_1368])).
% 17.16/8.85  tff(c_42255, plain, (![A_460]: (k2_xboole_0(k3_xboole_0('#skF_1', '#skF_3'), k3_xboole_0(A_460, k3_xboole_0('#skF_1', '#skF_2')))=k5_xboole_0(k3_xboole_0('#skF_1', '#skF_3'), k3_xboole_0(A_460, '#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_171, c_41863])).
% 17.16/8.85  tff(c_42359, plain, (![A_462]: (k3_xboole_0(A_462, k3_xboole_0('#skF_1', '#skF_2'))=k3_xboole_0(A_462, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_40963, c_77, c_521, c_521, c_42255])).
% 17.16/8.85  tff(c_42526, plain, (k4_xboole_0('#skF_1', k3_xboole_0('#skF_1', '#skF_2'))=k4_xboole_0('#skF_1', k3_xboole_0('#skF_1', '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_42359, c_776])).
% 17.16/8.85  tff(c_42629, plain, (k4_xboole_0('#skF_1', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_776, c_1981, c_2019, c_42526])).
% 17.16/8.85  tff(c_42631, plain, $false, inference(negUnitSimplification, [status(thm)], [c_160, c_42629])).
% 17.16/8.85  tff(c_42632, plain, (~r1_xboole_0('#skF_1', '#skF_3')), inference(splitRight, [status(thm)], [c_30])).
% 17.16/8.85  tff(c_42729, plain, (![A_466, B_467]: (k3_xboole_0(A_466, B_467)=A_466 | ~r1_tarski(A_466, B_467))), inference(cnfTransformation, [status(thm)], [f_43])).
% 17.16/8.85  tff(c_42737, plain, (k3_xboole_0('#skF_1', k4_xboole_0('#skF_2', '#skF_3'))='#skF_1'), inference(resolution, [status(thm)], [c_32, c_42729])).
% 17.16/8.85  tff(c_42988, plain, (![A_486, B_487, C_488]: (k4_xboole_0(k3_xboole_0(A_486, B_487), C_488)=k3_xboole_0(A_486, k4_xboole_0(B_487, C_488)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 17.16/8.85  tff(c_43234, plain, (![A_495, B_496, C_497]: (r1_xboole_0(k3_xboole_0(A_495, k4_xboole_0(B_496, C_497)), C_497))), inference(superposition, [status(thm), theory('equality')], [c_42988, c_24])).
% 17.16/8.85  tff(c_43276, plain, (r1_xboole_0('#skF_1', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_42737, c_43234])).
% 17.16/8.85  tff(c_43280, plain, $false, inference(negUnitSimplification, [status(thm)], [c_42632, c_43276])).
% 17.16/8.85  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 17.16/8.85  
% 17.16/8.85  Inference rules
% 17.16/8.85  ----------------------
% 17.16/8.85  #Ref     : 0
% 17.16/8.85  #Sup     : 11132
% 17.16/8.85  #Fact    : 0
% 17.16/8.85  #Define  : 0
% 17.16/8.85  #Split   : 3
% 17.16/8.85  #Chain   : 0
% 17.16/8.85  #Close   : 0
% 17.16/8.85  
% 17.16/8.85  Ordering : KBO
% 17.16/8.85  
% 17.16/8.85  Simplification rules
% 17.16/8.85  ----------------------
% 17.16/8.85  #Subsume      : 382
% 17.16/8.85  #Demod        : 13216
% 17.16/8.85  #Tautology    : 6403
% 17.16/8.85  #SimpNegUnit  : 43
% 17.16/8.85  #BackRed      : 84
% 17.16/8.85  
% 17.16/8.85  #Partial instantiations: 0
% 17.16/8.85  #Strategies tried      : 1
% 17.16/8.85  
% 17.16/8.85  Timing (in seconds)
% 17.16/8.85  ----------------------
% 17.16/8.85  Preprocessing        : 0.31
% 17.16/8.85  Parsing              : 0.17
% 17.16/8.85  CNF conversion       : 0.02
% 17.16/8.85  Main loop            : 7.77
% 17.16/8.85  Inferencing          : 1.12
% 17.16/8.85  Reduction            : 4.86
% 17.16/8.85  Demodulation         : 4.38
% 17.16/8.85  BG Simplification    : 0.15
% 17.16/8.85  Subsumption          : 1.32
% 17.16/8.85  Abstraction          : 0.25
% 17.16/8.85  MUC search           : 0.00
% 17.16/8.85  Cooper               : 0.00
% 17.16/8.85  Total                : 8.11
% 17.16/8.85  Index Insertion      : 0.00
% 17.16/8.85  Index Deletion       : 0.00
% 17.16/8.85  Index Matching       : 0.00
% 17.16/8.85  BG Taut test         : 0.00
%------------------------------------------------------------------------------
