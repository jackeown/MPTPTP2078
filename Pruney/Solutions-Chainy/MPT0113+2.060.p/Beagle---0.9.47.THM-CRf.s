%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:45:19 EST 2020

% Result     : Theorem 11.59s
% Output     : CNFRefutation 11.80s
% Verified   : 
% Statistics : Number of formulae       :  136 (4212 expanded)
%              Number of leaves         :   26 (1450 expanded)
%              Depth                    :   37
%              Number of atoms          :  138 (4799 expanded)
%              Number of equality atoms :  100 (3617 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    6 (   2 average)

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

tff(f_64,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r1_tarski(A,k4_xboole_0(B,C))
       => ( r1_tarski(A,B)
          & r1_xboole_0(A,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_xboole_1)).

tff(f_43,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

tff(f_55,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_53,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_51,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).

tff(f_49,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_xboole_0(B,C) )
     => r1_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_37,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_57,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k5_xboole_0(k5_xboole_0(A,B),k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_xboole_1)).

tff(f_41,axiom,(
    ! [A,B,C] : k4_xboole_0(A,k4_xboole_0(B,C)) = k2_xboole_0(k4_xboole_0(A,B),k3_xboole_0(A,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

tff(c_28,plain,
    ( ~ r1_xboole_0('#skF_1','#skF_3')
    | ~ r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_59,plain,(
    ~ r1_tarski('#skF_1','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_28])).

tff(c_16,plain,(
    ! [A_14] : k5_xboole_0(A_14,k1_xboole_0) = A_14 ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_24,plain,(
    ! [A_23] : k5_xboole_0(A_23,A_23) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_206,plain,(
    ! [A_56,B_57,C_58] : k5_xboole_0(k5_xboole_0(A_56,B_57),C_58) = k5_xboole_0(A_56,k5_xboole_0(B_57,C_58)) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_251,plain,(
    ! [A_56,B_57] : k5_xboole_0(A_56,k5_xboole_0(B_57,k5_xboole_0(A_56,B_57))) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_206])).

tff(c_418,plain,(
    ! [A_67,C_68] : k5_xboole_0(A_67,k5_xboole_0(A_67,C_68)) = k5_xboole_0(k1_xboole_0,C_68) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_206])).

tff(c_486,plain,(
    ! [A_23] : k5_xboole_0(k1_xboole_0,A_23) = k5_xboole_0(A_23,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_418])).

tff(c_502,plain,(
    ! [A_23] : k5_xboole_0(k1_xboole_0,A_23) = A_23 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_486])).

tff(c_247,plain,(
    ! [A_23,C_58] : k5_xboole_0(A_23,k5_xboole_0(A_23,C_58)) = k5_xboole_0(k1_xboole_0,C_58) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_206])).

tff(c_566,plain,(
    ! [A_70,C_71] : k5_xboole_0(A_70,k5_xboole_0(A_70,C_71)) = C_71 ),
    inference(demodulation,[status(thm),theory(equality)],[c_502,c_247])).

tff(c_610,plain,(
    ! [B_57,A_56] : k5_xboole_0(B_57,k5_xboole_0(A_56,B_57)) = k5_xboole_0(A_56,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_251,c_566])).

tff(c_643,plain,(
    ! [B_57,A_56] : k5_xboole_0(B_57,k5_xboole_0(A_56,B_57)) = A_56 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_610])).

tff(c_6,plain,(
    ! [A_3,B_4] : k5_xboole_0(A_3,k3_xboole_0(A_3,B_4)) = k4_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_506,plain,(
    ! [A_69] : k5_xboole_0(k1_xboole_0,A_69) = A_69 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_486])).

tff(c_546,plain,(
    ! [B_4] : k4_xboole_0(k1_xboole_0,B_4) = k3_xboole_0(k1_xboole_0,B_4) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_506])).

tff(c_30,plain,(
    r1_tarski('#skF_1',k4_xboole_0('#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_20,plain,(
    ! [A_18,B_19] : r1_xboole_0(k4_xboole_0(A_18,B_19),B_19) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_121,plain,(
    ! [A_46,C_47,B_48] :
      ( r1_xboole_0(A_46,C_47)
      | ~ r1_xboole_0(B_48,C_47)
      | ~ r1_tarski(A_46,B_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_128,plain,(
    ! [A_49,B_50,A_51] :
      ( r1_xboole_0(A_49,B_50)
      | ~ r1_tarski(A_49,k4_xboole_0(A_51,B_50)) ) ),
    inference(resolution,[status(thm)],[c_20,c_121])).

tff(c_137,plain,(
    r1_xboole_0('#skF_1','#skF_3') ),
    inference(resolution,[status(thm)],[c_30,c_128])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( k3_xboole_0(A_1,B_2) = k1_xboole_0
      | ~ r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_144,plain,(
    k3_xboole_0('#skF_1','#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_137,c_2])).

tff(c_148,plain,(
    k5_xboole_0('#skF_1',k1_xboole_0) = k4_xboole_0('#skF_1','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_144,c_6])).

tff(c_151,plain,(
    k4_xboole_0('#skF_1','#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_148])).

tff(c_10,plain,(
    ! [A_7,B_8] : r1_tarski(k4_xboole_0(A_7,B_8),A_7) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_70,plain,(
    ! [A_36,B_37] :
      ( k2_xboole_0(A_36,B_37) = B_37
      | ~ r1_tarski(A_36,B_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_77,plain,(
    ! [A_7,B_8] : k2_xboole_0(k4_xboole_0(A_7,B_8),A_7) = A_7 ),
    inference(resolution,[status(thm)],[c_10,c_70])).

tff(c_170,plain,(
    k2_xboole_0('#skF_1','#skF_1') = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_151,c_77])).

tff(c_648,plain,(
    ! [A_72,B_73] : k5_xboole_0(k5_xboole_0(A_72,B_73),k2_xboole_0(A_72,B_73)) = k3_xboole_0(A_72,B_73) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_691,plain,(
    k5_xboole_0(k5_xboole_0('#skF_1','#skF_1'),'#skF_1') = k3_xboole_0('#skF_1','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_170,c_648])).

tff(c_713,plain,(
    k3_xboole_0('#skF_1','#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_502,c_24,c_691])).

tff(c_718,plain,(
    k5_xboole_0('#skF_1','#skF_1') = k4_xboole_0('#skF_1','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_713,c_6])).

tff(c_721,plain,(
    k4_xboole_0('#skF_1','#skF_1') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_718])).

tff(c_828,plain,(
    ! [A_74,B_75,C_76] : k2_xboole_0(k4_xboole_0(A_74,B_75),k3_xboole_0(A_74,C_76)) = k4_xboole_0(A_74,k4_xboole_0(B_75,C_76)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_907,plain,(
    ! [B_77] : k4_xboole_0('#skF_1',k4_xboole_0(B_77,'#skF_3')) = k2_xboole_0(k4_xboole_0('#skF_1',B_77),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_144,c_828])).

tff(c_944,plain,(
    k2_xboole_0(k4_xboole_0('#skF_1','#skF_1'),k1_xboole_0) = k4_xboole_0('#skF_1','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_151,c_907])).

tff(c_947,plain,(
    k2_xboole_0(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_721,c_721,c_944])).

tff(c_26,plain,(
    ! [A_24,B_25] : k5_xboole_0(k5_xboole_0(A_24,B_25),k2_xboole_0(A_24,B_25)) = k3_xboole_0(A_24,B_25) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_960,plain,(
    k5_xboole_0(k5_xboole_0(k1_xboole_0,k1_xboole_0),k1_xboole_0) = k3_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_947,c_26])).

tff(c_963,plain,(
    k3_xboole_0(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_24,c_960])).

tff(c_971,plain,(
    k5_xboole_0(k1_xboole_0,k1_xboole_0) = k4_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_963,c_6])).

tff(c_975,plain,(
    k4_xboole_0(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_971])).

tff(c_136,plain,(
    ! [A_51,B_50,B_8] : r1_xboole_0(k4_xboole_0(k4_xboole_0(A_51,B_50),B_8),B_50) ),
    inference(resolution,[status(thm)],[c_10,c_128])).

tff(c_1254,plain,(
    ! [B_81] : r1_xboole_0(k4_xboole_0(k1_xboole_0,B_81),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_975,c_136])).

tff(c_1267,plain,(
    ! [B_81] : k3_xboole_0(k4_xboole_0(k1_xboole_0,B_81),k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1254,c_2])).

tff(c_3625,plain,(
    ! [B_81] : k3_xboole_0(k3_xboole_0(k1_xboole_0,B_81),k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_546,c_1267])).

tff(c_1341,plain,(
    ! [B_84] : k4_xboole_0(k1_xboole_0,B_84) = k3_xboole_0(k1_xboole_0,B_84) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_506])).

tff(c_1372,plain,(
    ! [B_84] : k2_xboole_0(k3_xboole_0(k1_xboole_0,B_84),k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_1341,c_77])).

tff(c_22,plain,(
    ! [A_20,B_21,C_22] : k5_xboole_0(k5_xboole_0(A_20,B_21),C_22) = k5_xboole_0(A_20,k5_xboole_0(B_21,C_22)) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_4096,plain,(
    ! [A_142,B_143,C_144] : k5_xboole_0(k5_xboole_0(A_142,B_143),k5_xboole_0(k2_xboole_0(A_142,B_143),C_144)) = k5_xboole_0(k3_xboole_0(A_142,B_143),C_144) ),
    inference(superposition,[status(thm),theory(equality)],[c_648,c_22])).

tff(c_4180,plain,(
    ! [B_84,C_144] : k5_xboole_0(k5_xboole_0(k3_xboole_0(k1_xboole_0,B_84),k1_xboole_0),k5_xboole_0(k1_xboole_0,C_144)) = k5_xboole_0(k3_xboole_0(k3_xboole_0(k1_xboole_0,B_84),k1_xboole_0),C_144) ),
    inference(superposition,[status(thm),theory(equality)],[c_1372,c_4096])).

tff(c_4327,plain,(
    ! [B_145,C_146] : k5_xboole_0(k3_xboole_0(k1_xboole_0,B_145),C_146) = C_146 ),
    inference(demodulation,[status(thm),theory(equality)],[c_502,c_3625,c_502,c_16,c_4180])).

tff(c_503,plain,(
    ! [A_23,C_58] : k5_xboole_0(A_23,k5_xboole_0(A_23,C_58)) = C_58 ),
    inference(demodulation,[status(thm),theory(equality)],[c_502,c_247])).

tff(c_1641,plain,(
    ! [B_92,A_93] : k5_xboole_0(B_92,k5_xboole_0(A_93,B_92)) = A_93 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_610])).

tff(c_1689,plain,(
    ! [A_23,C_58] : k5_xboole_0(k5_xboole_0(A_23,C_58),C_58) = A_23 ),
    inference(superposition,[status(thm),theory(equality)],[c_503,c_1641])).

tff(c_4367,plain,(
    ! [C_146,B_145] : k5_xboole_0(C_146,C_146) = k3_xboole_0(k1_xboole_0,B_145) ),
    inference(superposition,[status(thm),theory(equality)],[c_4327,c_1689])).

tff(c_4479,plain,(
    ! [B_145] : k3_xboole_0(k1_xboole_0,B_145) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_4367])).

tff(c_4675,plain,(
    ! [A_151,B_152,C_153] : k5_xboole_0(k5_xboole_0(A_151,k5_xboole_0(B_152,C_153)),k2_xboole_0(k5_xboole_0(A_151,B_152),C_153)) = k3_xboole_0(k5_xboole_0(A_151,B_152),C_153) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_648])).

tff(c_4921,plain,(
    ! [A_23,C_153] : k5_xboole_0(k5_xboole_0(A_23,k5_xboole_0(A_23,C_153)),k2_xboole_0(k1_xboole_0,C_153)) = k3_xboole_0(k5_xboole_0(A_23,A_23),C_153) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_4675])).

tff(c_5510,plain,(
    ! [C_160] : k5_xboole_0(C_160,k2_xboole_0(k1_xboole_0,C_160)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_4479,c_503,c_24,c_4921])).

tff(c_1671,plain,(
    ! [A_56,B_57] : k5_xboole_0(k5_xboole_0(A_56,B_57),A_56) = B_57 ),
    inference(superposition,[status(thm),theory(equality)],[c_643,c_1641])).

tff(c_5538,plain,(
    ! [C_160] : k5_xboole_0(k1_xboole_0,C_160) = k2_xboole_0(k1_xboole_0,C_160) ),
    inference(superposition,[status(thm),theory(equality)],[c_5510,c_1671])).

tff(c_5605,plain,(
    ! [C_160] : k2_xboole_0(k1_xboole_0,C_160) = C_160 ),
    inference(demodulation,[status(thm),theory(equality)],[c_502,c_5538])).

tff(c_5622,plain,(
    ! [C_161] : k2_xboole_0(k1_xboole_0,C_161) = C_161 ),
    inference(demodulation,[status(thm),theory(equality)],[c_502,c_5538])).

tff(c_12,plain,(
    ! [A_9,B_10] : k2_xboole_0(A_9,k4_xboole_0(B_10,A_9)) = k2_xboole_0(A_9,B_10) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_5652,plain,(
    ! [B_10] : k4_xboole_0(B_10,k1_xboole_0) = k2_xboole_0(k1_xboole_0,B_10) ),
    inference(superposition,[status(thm),theory(equality)],[c_5622,c_12])).

tff(c_5673,plain,(
    ! [B_162] : k4_xboole_0(B_162,k1_xboole_0) = B_162 ),
    inference(demodulation,[status(thm),theory(equality)],[c_5605,c_5652])).

tff(c_5740,plain,(
    ! [B_162] : k2_xboole_0(B_162,B_162) = B_162 ),
    inference(superposition,[status(thm),theory(equality)],[c_5673,c_77])).

tff(c_1653,plain,(
    ! [B_92,A_93] : k5_xboole_0(B_92,A_93) = k5_xboole_0(A_93,B_92) ),
    inference(superposition,[status(thm),theory(equality)],[c_1641,c_503])).

tff(c_5932,plain,(
    ! [B_167] : k2_xboole_0(B_167,B_167) = B_167 ),
    inference(superposition,[status(thm),theory(equality)],[c_5673,c_77])).

tff(c_651,plain,(
    ! [A_72,B_73] : k5_xboole_0(k3_xboole_0(A_72,B_73),k2_xboole_0(k5_xboole_0(A_72,B_73),k2_xboole_0(A_72,B_73))) = k3_xboole_0(k5_xboole_0(A_72,B_73),k2_xboole_0(A_72,B_73)) ),
    inference(superposition,[status(thm),theory(equality)],[c_648,c_26])).

tff(c_5942,plain,(
    ! [B_167] : k5_xboole_0(k3_xboole_0(B_167,B_167),k2_xboole_0(k5_xboole_0(B_167,B_167),B_167)) = k3_xboole_0(k5_xboole_0(B_167,B_167),k2_xboole_0(B_167,B_167)) ),
    inference(superposition,[status(thm),theory(equality)],[c_5932,c_651])).

tff(c_6223,plain,(
    ! [B_172] : k4_xboole_0(B_172,B_172) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_5605,c_4479,c_1653,c_24,c_24,c_5942])).

tff(c_6297,plain,(
    ! [B_172] : k2_xboole_0(B_172,k1_xboole_0) = k2_xboole_0(B_172,B_172) ),
    inference(superposition,[status(thm),theory(equality)],[c_6223,c_12])).

tff(c_6341,plain,(
    ! [B_172] : k2_xboole_0(B_172,k1_xboole_0) = B_172 ),
    inference(demodulation,[status(thm),theory(equality)],[c_5740,c_6297])).

tff(c_736,plain,(
    k2_xboole_0('#skF_1',k1_xboole_0) = k2_xboole_0('#skF_1','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_721,c_12])).

tff(c_751,plain,(
    k2_xboole_0('#skF_1',k1_xboole_0) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_170,c_736])).

tff(c_870,plain,(
    k5_xboole_0(k5_xboole_0('#skF_1',k1_xboole_0),'#skF_1') = k3_xboole_0('#skF_1',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_751,c_26])).

tff(c_873,plain,(
    k3_xboole_0('#skF_1',k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_16,c_870])).

tff(c_983,plain,(
    k5_xboole_0('#skF_1',k1_xboole_0) = k4_xboole_0('#skF_1',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_873,c_6])).

tff(c_986,plain,(
    k4_xboole_0('#skF_1',k1_xboole_0) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_983])).

tff(c_1271,plain,(
    ! [B_82] : r1_xboole_0(k4_xboole_0('#skF_1',B_82),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_986,c_136])).

tff(c_1286,plain,(
    ! [B_82] : k3_xboole_0(k4_xboole_0('#skF_1',B_82),k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1271,c_2])).

tff(c_858,plain,(
    ! [B_75] : k4_xboole_0('#skF_1',k4_xboole_0(B_75,'#skF_3')) = k2_xboole_0(k4_xboole_0('#skF_1',B_75),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_144,c_828])).

tff(c_78,plain,(
    k2_xboole_0('#skF_1',k4_xboole_0('#skF_2','#skF_3')) = k4_xboole_0('#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_30,c_70])).

tff(c_694,plain,(
    k5_xboole_0(k5_xboole_0('#skF_1',k4_xboole_0('#skF_2','#skF_3')),k4_xboole_0('#skF_2','#skF_3')) = k3_xboole_0('#skF_1',k4_xboole_0('#skF_2','#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_78,c_648])).

tff(c_769,plain,(
    k5_xboole_0(k5_xboole_0('#skF_1',k4_xboole_0('#skF_2','#skF_3')),k5_xboole_0(k4_xboole_0('#skF_2','#skF_3'),k3_xboole_0('#skF_1',k4_xboole_0('#skF_2','#skF_3')))) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_694,c_251])).

tff(c_1228,plain,(
    k5_xboole_0('#skF_1',k5_xboole_0(k4_xboole_0('#skF_2','#skF_3'),k5_xboole_0(k4_xboole_0('#skF_2','#skF_3'),k3_xboole_0('#skF_1',k4_xboole_0('#skF_2','#skF_3'))))) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_769])).

tff(c_1236,plain,(
    k2_xboole_0(k4_xboole_0('#skF_1','#skF_2'),k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_858,c_6,c_503,c_1228])).

tff(c_4203,plain,(
    ! [C_144] : k5_xboole_0(k5_xboole_0(k4_xboole_0('#skF_1','#skF_2'),k1_xboole_0),k5_xboole_0(k1_xboole_0,C_144)) = k5_xboole_0(k3_xboole_0(k4_xboole_0('#skF_1','#skF_2'),k1_xboole_0),C_144) ),
    inference(superposition,[status(thm),theory(equality)],[c_1236,c_4096])).

tff(c_5011,plain,(
    ! [C_156] : k5_xboole_0(k4_xboole_0('#skF_1','#skF_2'),C_156) = C_156 ),
    inference(demodulation,[status(thm),theory(equality)],[c_502,c_1286,c_502,c_16,c_4203])).

tff(c_5062,plain,(
    ! [C_156] : k5_xboole_0(C_156,C_156) = k4_xboole_0('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_5011,c_1689])).

tff(c_5163,plain,(
    k4_xboole_0('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_5062])).

tff(c_5212,plain,(
    k2_xboole_0('#skF_2',k1_xboole_0) = k2_xboole_0('#skF_2','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_5163,c_12])).

tff(c_7022,plain,(
    k2_xboole_0('#skF_2','#skF_1') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6341,c_5212])).

tff(c_666,plain,(
    ! [A_72,B_73] : k5_xboole_0(A_72,k5_xboole_0(B_73,k2_xboole_0(A_72,B_73))) = k3_xboole_0(A_72,B_73) ),
    inference(superposition,[status(thm),theory(equality)],[c_648,c_22])).

tff(c_7035,plain,(
    k5_xboole_0('#skF_2',k5_xboole_0('#skF_1','#skF_2')) = k3_xboole_0('#skF_2','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_7022,c_666])).

tff(c_7044,plain,(
    k3_xboole_0('#skF_2','#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_643,c_7035])).

tff(c_14,plain,(
    ! [A_11,B_12,C_13] : k2_xboole_0(k4_xboole_0(A_11,B_12),k3_xboole_0(A_11,C_13)) = k4_xboole_0(A_11,k4_xboole_0(B_12,C_13)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_6279,plain,(
    ! [B_172,C_13] : k4_xboole_0(B_172,k4_xboole_0(B_172,C_13)) = k2_xboole_0(k1_xboole_0,k3_xboole_0(B_172,C_13)) ),
    inference(superposition,[status(thm),theory(equality)],[c_6223,c_14])).

tff(c_28234,plain,(
    ! [B_407,C_408] : k4_xboole_0(B_407,k4_xboole_0(B_407,C_408)) = k3_xboole_0(B_407,C_408) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5605,c_6279])).

tff(c_28961,plain,(
    ! [B_410,C_411] : r1_tarski(k3_xboole_0(B_410,C_411),B_410) ),
    inference(superposition,[status(thm),theory(equality)],[c_28234,c_10])).

tff(c_29062,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_7044,c_28961])).

tff(c_29126,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_59,c_29062])).

tff(c_29127,plain,(
    ~ r1_xboole_0('#skF_1','#skF_3') ),
    inference(splitRight,[status(thm)],[c_28])).

tff(c_29237,plain,(
    ! [A_428,C_429,B_430] :
      ( r1_xboole_0(A_428,C_429)
      | ~ r1_xboole_0(B_430,C_429)
      | ~ r1_tarski(A_428,B_430) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_29257,plain,(
    ! [A_433,B_434,A_435] :
      ( r1_xboole_0(A_433,B_434)
      | ~ r1_tarski(A_433,k4_xboole_0(A_435,B_434)) ) ),
    inference(resolution,[status(thm)],[c_20,c_29237])).

tff(c_29270,plain,(
    r1_xboole_0('#skF_1','#skF_3') ),
    inference(resolution,[status(thm)],[c_30,c_29257])).

tff(c_29277,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_29127,c_29270])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:54:54 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 11.59/5.15  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.59/5.17  
% 11.59/5.17  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.59/5.17  %$ r1_xboole_0 > r1_tarski > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 11.59/5.17  
% 11.59/5.17  %Foreground sorts:
% 11.59/5.17  
% 11.59/5.17  
% 11.59/5.17  %Background operators:
% 11.59/5.17  
% 11.59/5.17  
% 11.59/5.17  %Foreground operators:
% 11.59/5.17  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 11.59/5.17  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 11.59/5.17  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 11.59/5.17  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 11.59/5.17  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 11.59/5.17  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 11.59/5.17  tff('#skF_2', type, '#skF_2': $i).
% 11.59/5.17  tff('#skF_3', type, '#skF_3': $i).
% 11.59/5.17  tff('#skF_1', type, '#skF_1': $i).
% 11.59/5.17  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 11.59/5.17  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 11.59/5.17  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 11.59/5.17  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 11.59/5.17  
% 11.80/5.19  tff(f_64, negated_conjecture, ~(![A, B, C]: (r1_tarski(A, k4_xboole_0(B, C)) => (r1_tarski(A, B) & r1_xboole_0(A, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t106_xboole_1)).
% 11.80/5.19  tff(f_43, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 11.80/5.19  tff(f_55, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t92_xboole_1)).
% 11.80/5.19  tff(f_53, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_xboole_1)).
% 11.80/5.19  tff(f_31, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 11.80/5.19  tff(f_51, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_xboole_1)).
% 11.80/5.19  tff(f_49, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_xboole_0(B, C)) => r1_xboole_0(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_xboole_1)).
% 11.80/5.19  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 11.80/5.19  tff(f_37, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 11.80/5.19  tff(f_35, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 11.80/5.19  tff(f_57, axiom, (![A, B]: (k3_xboole_0(A, B) = k5_xboole_0(k5_xboole_0(A, B), k2_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t95_xboole_1)).
% 11.80/5.19  tff(f_41, axiom, (![A, B, C]: (k4_xboole_0(A, k4_xboole_0(B, C)) = k2_xboole_0(k4_xboole_0(A, B), k3_xboole_0(A, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_xboole_1)).
% 11.80/5.19  tff(f_39, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_xboole_1)).
% 11.80/5.19  tff(c_28, plain, (~r1_xboole_0('#skF_1', '#skF_3') | ~r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_64])).
% 11.80/5.19  tff(c_59, plain, (~r1_tarski('#skF_1', '#skF_2')), inference(splitLeft, [status(thm)], [c_28])).
% 11.80/5.19  tff(c_16, plain, (![A_14]: (k5_xboole_0(A_14, k1_xboole_0)=A_14)), inference(cnfTransformation, [status(thm)], [f_43])).
% 11.80/5.19  tff(c_24, plain, (![A_23]: (k5_xboole_0(A_23, A_23)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_55])).
% 11.80/5.19  tff(c_206, plain, (![A_56, B_57, C_58]: (k5_xboole_0(k5_xboole_0(A_56, B_57), C_58)=k5_xboole_0(A_56, k5_xboole_0(B_57, C_58)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 11.80/5.19  tff(c_251, plain, (![A_56, B_57]: (k5_xboole_0(A_56, k5_xboole_0(B_57, k5_xboole_0(A_56, B_57)))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_24, c_206])).
% 11.80/5.19  tff(c_418, plain, (![A_67, C_68]: (k5_xboole_0(A_67, k5_xboole_0(A_67, C_68))=k5_xboole_0(k1_xboole_0, C_68))), inference(superposition, [status(thm), theory('equality')], [c_24, c_206])).
% 11.80/5.19  tff(c_486, plain, (![A_23]: (k5_xboole_0(k1_xboole_0, A_23)=k5_xboole_0(A_23, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_24, c_418])).
% 11.80/5.19  tff(c_502, plain, (![A_23]: (k5_xboole_0(k1_xboole_0, A_23)=A_23)), inference(demodulation, [status(thm), theory('equality')], [c_16, c_486])).
% 11.80/5.19  tff(c_247, plain, (![A_23, C_58]: (k5_xboole_0(A_23, k5_xboole_0(A_23, C_58))=k5_xboole_0(k1_xboole_0, C_58))), inference(superposition, [status(thm), theory('equality')], [c_24, c_206])).
% 11.80/5.19  tff(c_566, plain, (![A_70, C_71]: (k5_xboole_0(A_70, k5_xboole_0(A_70, C_71))=C_71)), inference(demodulation, [status(thm), theory('equality')], [c_502, c_247])).
% 11.80/5.19  tff(c_610, plain, (![B_57, A_56]: (k5_xboole_0(B_57, k5_xboole_0(A_56, B_57))=k5_xboole_0(A_56, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_251, c_566])).
% 11.80/5.19  tff(c_643, plain, (![B_57, A_56]: (k5_xboole_0(B_57, k5_xboole_0(A_56, B_57))=A_56)), inference(demodulation, [status(thm), theory('equality')], [c_16, c_610])).
% 11.80/5.19  tff(c_6, plain, (![A_3, B_4]: (k5_xboole_0(A_3, k3_xboole_0(A_3, B_4))=k4_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 11.80/5.19  tff(c_506, plain, (![A_69]: (k5_xboole_0(k1_xboole_0, A_69)=A_69)), inference(demodulation, [status(thm), theory('equality')], [c_16, c_486])).
% 11.80/5.19  tff(c_546, plain, (![B_4]: (k4_xboole_0(k1_xboole_0, B_4)=k3_xboole_0(k1_xboole_0, B_4))), inference(superposition, [status(thm), theory('equality')], [c_6, c_506])).
% 11.80/5.19  tff(c_30, plain, (r1_tarski('#skF_1', k4_xboole_0('#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_64])).
% 11.80/5.19  tff(c_20, plain, (![A_18, B_19]: (r1_xboole_0(k4_xboole_0(A_18, B_19), B_19))), inference(cnfTransformation, [status(thm)], [f_51])).
% 11.80/5.19  tff(c_121, plain, (![A_46, C_47, B_48]: (r1_xboole_0(A_46, C_47) | ~r1_xboole_0(B_48, C_47) | ~r1_tarski(A_46, B_48))), inference(cnfTransformation, [status(thm)], [f_49])).
% 11.80/5.19  tff(c_128, plain, (![A_49, B_50, A_51]: (r1_xboole_0(A_49, B_50) | ~r1_tarski(A_49, k4_xboole_0(A_51, B_50)))), inference(resolution, [status(thm)], [c_20, c_121])).
% 11.80/5.19  tff(c_137, plain, (r1_xboole_0('#skF_1', '#skF_3')), inference(resolution, [status(thm)], [c_30, c_128])).
% 11.80/5.19  tff(c_2, plain, (![A_1, B_2]: (k3_xboole_0(A_1, B_2)=k1_xboole_0 | ~r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 11.80/5.19  tff(c_144, plain, (k3_xboole_0('#skF_1', '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_137, c_2])).
% 11.80/5.19  tff(c_148, plain, (k5_xboole_0('#skF_1', k1_xboole_0)=k4_xboole_0('#skF_1', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_144, c_6])).
% 11.80/5.19  tff(c_151, plain, (k4_xboole_0('#skF_1', '#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_16, c_148])).
% 11.80/5.19  tff(c_10, plain, (![A_7, B_8]: (r1_tarski(k4_xboole_0(A_7, B_8), A_7))), inference(cnfTransformation, [status(thm)], [f_37])).
% 11.80/5.19  tff(c_70, plain, (![A_36, B_37]: (k2_xboole_0(A_36, B_37)=B_37 | ~r1_tarski(A_36, B_37))), inference(cnfTransformation, [status(thm)], [f_35])).
% 11.80/5.19  tff(c_77, plain, (![A_7, B_8]: (k2_xboole_0(k4_xboole_0(A_7, B_8), A_7)=A_7)), inference(resolution, [status(thm)], [c_10, c_70])).
% 11.80/5.19  tff(c_170, plain, (k2_xboole_0('#skF_1', '#skF_1')='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_151, c_77])).
% 11.80/5.19  tff(c_648, plain, (![A_72, B_73]: (k5_xboole_0(k5_xboole_0(A_72, B_73), k2_xboole_0(A_72, B_73))=k3_xboole_0(A_72, B_73))), inference(cnfTransformation, [status(thm)], [f_57])).
% 11.80/5.19  tff(c_691, plain, (k5_xboole_0(k5_xboole_0('#skF_1', '#skF_1'), '#skF_1')=k3_xboole_0('#skF_1', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_170, c_648])).
% 11.80/5.19  tff(c_713, plain, (k3_xboole_0('#skF_1', '#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_502, c_24, c_691])).
% 11.80/5.19  tff(c_718, plain, (k5_xboole_0('#skF_1', '#skF_1')=k4_xboole_0('#skF_1', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_713, c_6])).
% 11.80/5.19  tff(c_721, plain, (k4_xboole_0('#skF_1', '#skF_1')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_24, c_718])).
% 11.80/5.19  tff(c_828, plain, (![A_74, B_75, C_76]: (k2_xboole_0(k4_xboole_0(A_74, B_75), k3_xboole_0(A_74, C_76))=k4_xboole_0(A_74, k4_xboole_0(B_75, C_76)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 11.80/5.19  tff(c_907, plain, (![B_77]: (k4_xboole_0('#skF_1', k4_xboole_0(B_77, '#skF_3'))=k2_xboole_0(k4_xboole_0('#skF_1', B_77), k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_144, c_828])).
% 11.80/5.19  tff(c_944, plain, (k2_xboole_0(k4_xboole_0('#skF_1', '#skF_1'), k1_xboole_0)=k4_xboole_0('#skF_1', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_151, c_907])).
% 11.80/5.19  tff(c_947, plain, (k2_xboole_0(k1_xboole_0, k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_721, c_721, c_944])).
% 11.80/5.19  tff(c_26, plain, (![A_24, B_25]: (k5_xboole_0(k5_xboole_0(A_24, B_25), k2_xboole_0(A_24, B_25))=k3_xboole_0(A_24, B_25))), inference(cnfTransformation, [status(thm)], [f_57])).
% 11.80/5.19  tff(c_960, plain, (k5_xboole_0(k5_xboole_0(k1_xboole_0, k1_xboole_0), k1_xboole_0)=k3_xboole_0(k1_xboole_0, k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_947, c_26])).
% 11.80/5.19  tff(c_963, plain, (k3_xboole_0(k1_xboole_0, k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_24, c_24, c_960])).
% 11.80/5.19  tff(c_971, plain, (k5_xboole_0(k1_xboole_0, k1_xboole_0)=k4_xboole_0(k1_xboole_0, k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_963, c_6])).
% 11.80/5.19  tff(c_975, plain, (k4_xboole_0(k1_xboole_0, k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_24, c_971])).
% 11.80/5.19  tff(c_136, plain, (![A_51, B_50, B_8]: (r1_xboole_0(k4_xboole_0(k4_xboole_0(A_51, B_50), B_8), B_50))), inference(resolution, [status(thm)], [c_10, c_128])).
% 11.80/5.19  tff(c_1254, plain, (![B_81]: (r1_xboole_0(k4_xboole_0(k1_xboole_0, B_81), k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_975, c_136])).
% 11.80/5.19  tff(c_1267, plain, (![B_81]: (k3_xboole_0(k4_xboole_0(k1_xboole_0, B_81), k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_1254, c_2])).
% 11.80/5.19  tff(c_3625, plain, (![B_81]: (k3_xboole_0(k3_xboole_0(k1_xboole_0, B_81), k1_xboole_0)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_546, c_1267])).
% 11.80/5.19  tff(c_1341, plain, (![B_84]: (k4_xboole_0(k1_xboole_0, B_84)=k3_xboole_0(k1_xboole_0, B_84))), inference(superposition, [status(thm), theory('equality')], [c_6, c_506])).
% 11.80/5.19  tff(c_1372, plain, (![B_84]: (k2_xboole_0(k3_xboole_0(k1_xboole_0, B_84), k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_1341, c_77])).
% 11.80/5.19  tff(c_22, plain, (![A_20, B_21, C_22]: (k5_xboole_0(k5_xboole_0(A_20, B_21), C_22)=k5_xboole_0(A_20, k5_xboole_0(B_21, C_22)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 11.80/5.19  tff(c_4096, plain, (![A_142, B_143, C_144]: (k5_xboole_0(k5_xboole_0(A_142, B_143), k5_xboole_0(k2_xboole_0(A_142, B_143), C_144))=k5_xboole_0(k3_xboole_0(A_142, B_143), C_144))), inference(superposition, [status(thm), theory('equality')], [c_648, c_22])).
% 11.80/5.19  tff(c_4180, plain, (![B_84, C_144]: (k5_xboole_0(k5_xboole_0(k3_xboole_0(k1_xboole_0, B_84), k1_xboole_0), k5_xboole_0(k1_xboole_0, C_144))=k5_xboole_0(k3_xboole_0(k3_xboole_0(k1_xboole_0, B_84), k1_xboole_0), C_144))), inference(superposition, [status(thm), theory('equality')], [c_1372, c_4096])).
% 11.80/5.19  tff(c_4327, plain, (![B_145, C_146]: (k5_xboole_0(k3_xboole_0(k1_xboole_0, B_145), C_146)=C_146)), inference(demodulation, [status(thm), theory('equality')], [c_502, c_3625, c_502, c_16, c_4180])).
% 11.80/5.19  tff(c_503, plain, (![A_23, C_58]: (k5_xboole_0(A_23, k5_xboole_0(A_23, C_58))=C_58)), inference(demodulation, [status(thm), theory('equality')], [c_502, c_247])).
% 11.80/5.19  tff(c_1641, plain, (![B_92, A_93]: (k5_xboole_0(B_92, k5_xboole_0(A_93, B_92))=A_93)), inference(demodulation, [status(thm), theory('equality')], [c_16, c_610])).
% 11.80/5.19  tff(c_1689, plain, (![A_23, C_58]: (k5_xboole_0(k5_xboole_0(A_23, C_58), C_58)=A_23)), inference(superposition, [status(thm), theory('equality')], [c_503, c_1641])).
% 11.80/5.19  tff(c_4367, plain, (![C_146, B_145]: (k5_xboole_0(C_146, C_146)=k3_xboole_0(k1_xboole_0, B_145))), inference(superposition, [status(thm), theory('equality')], [c_4327, c_1689])).
% 11.80/5.19  tff(c_4479, plain, (![B_145]: (k3_xboole_0(k1_xboole_0, B_145)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_24, c_4367])).
% 11.80/5.19  tff(c_4675, plain, (![A_151, B_152, C_153]: (k5_xboole_0(k5_xboole_0(A_151, k5_xboole_0(B_152, C_153)), k2_xboole_0(k5_xboole_0(A_151, B_152), C_153))=k3_xboole_0(k5_xboole_0(A_151, B_152), C_153))), inference(superposition, [status(thm), theory('equality')], [c_22, c_648])).
% 11.80/5.19  tff(c_4921, plain, (![A_23, C_153]: (k5_xboole_0(k5_xboole_0(A_23, k5_xboole_0(A_23, C_153)), k2_xboole_0(k1_xboole_0, C_153))=k3_xboole_0(k5_xboole_0(A_23, A_23), C_153))), inference(superposition, [status(thm), theory('equality')], [c_24, c_4675])).
% 11.80/5.19  tff(c_5510, plain, (![C_160]: (k5_xboole_0(C_160, k2_xboole_0(k1_xboole_0, C_160))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_4479, c_503, c_24, c_4921])).
% 11.80/5.19  tff(c_1671, plain, (![A_56, B_57]: (k5_xboole_0(k5_xboole_0(A_56, B_57), A_56)=B_57)), inference(superposition, [status(thm), theory('equality')], [c_643, c_1641])).
% 11.80/5.19  tff(c_5538, plain, (![C_160]: (k5_xboole_0(k1_xboole_0, C_160)=k2_xboole_0(k1_xboole_0, C_160))), inference(superposition, [status(thm), theory('equality')], [c_5510, c_1671])).
% 11.80/5.19  tff(c_5605, plain, (![C_160]: (k2_xboole_0(k1_xboole_0, C_160)=C_160)), inference(demodulation, [status(thm), theory('equality')], [c_502, c_5538])).
% 11.80/5.19  tff(c_5622, plain, (![C_161]: (k2_xboole_0(k1_xboole_0, C_161)=C_161)), inference(demodulation, [status(thm), theory('equality')], [c_502, c_5538])).
% 11.80/5.19  tff(c_12, plain, (![A_9, B_10]: (k2_xboole_0(A_9, k4_xboole_0(B_10, A_9))=k2_xboole_0(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_39])).
% 11.80/5.19  tff(c_5652, plain, (![B_10]: (k4_xboole_0(B_10, k1_xboole_0)=k2_xboole_0(k1_xboole_0, B_10))), inference(superposition, [status(thm), theory('equality')], [c_5622, c_12])).
% 11.80/5.19  tff(c_5673, plain, (![B_162]: (k4_xboole_0(B_162, k1_xboole_0)=B_162)), inference(demodulation, [status(thm), theory('equality')], [c_5605, c_5652])).
% 11.80/5.19  tff(c_5740, plain, (![B_162]: (k2_xboole_0(B_162, B_162)=B_162)), inference(superposition, [status(thm), theory('equality')], [c_5673, c_77])).
% 11.80/5.19  tff(c_1653, plain, (![B_92, A_93]: (k5_xboole_0(B_92, A_93)=k5_xboole_0(A_93, B_92))), inference(superposition, [status(thm), theory('equality')], [c_1641, c_503])).
% 11.80/5.19  tff(c_5932, plain, (![B_167]: (k2_xboole_0(B_167, B_167)=B_167)), inference(superposition, [status(thm), theory('equality')], [c_5673, c_77])).
% 11.80/5.19  tff(c_651, plain, (![A_72, B_73]: (k5_xboole_0(k3_xboole_0(A_72, B_73), k2_xboole_0(k5_xboole_0(A_72, B_73), k2_xboole_0(A_72, B_73)))=k3_xboole_0(k5_xboole_0(A_72, B_73), k2_xboole_0(A_72, B_73)))), inference(superposition, [status(thm), theory('equality')], [c_648, c_26])).
% 11.80/5.19  tff(c_5942, plain, (![B_167]: (k5_xboole_0(k3_xboole_0(B_167, B_167), k2_xboole_0(k5_xboole_0(B_167, B_167), B_167))=k3_xboole_0(k5_xboole_0(B_167, B_167), k2_xboole_0(B_167, B_167)))), inference(superposition, [status(thm), theory('equality')], [c_5932, c_651])).
% 11.80/5.19  tff(c_6223, plain, (![B_172]: (k4_xboole_0(B_172, B_172)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_5605, c_4479, c_1653, c_24, c_24, c_5942])).
% 11.80/5.19  tff(c_6297, plain, (![B_172]: (k2_xboole_0(B_172, k1_xboole_0)=k2_xboole_0(B_172, B_172))), inference(superposition, [status(thm), theory('equality')], [c_6223, c_12])).
% 11.80/5.19  tff(c_6341, plain, (![B_172]: (k2_xboole_0(B_172, k1_xboole_0)=B_172)), inference(demodulation, [status(thm), theory('equality')], [c_5740, c_6297])).
% 11.80/5.19  tff(c_736, plain, (k2_xboole_0('#skF_1', k1_xboole_0)=k2_xboole_0('#skF_1', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_721, c_12])).
% 11.80/5.19  tff(c_751, plain, (k2_xboole_0('#skF_1', k1_xboole_0)='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_170, c_736])).
% 11.80/5.19  tff(c_870, plain, (k5_xboole_0(k5_xboole_0('#skF_1', k1_xboole_0), '#skF_1')=k3_xboole_0('#skF_1', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_751, c_26])).
% 11.80/5.19  tff(c_873, plain, (k3_xboole_0('#skF_1', k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_24, c_16, c_870])).
% 11.80/5.19  tff(c_983, plain, (k5_xboole_0('#skF_1', k1_xboole_0)=k4_xboole_0('#skF_1', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_873, c_6])).
% 11.80/5.19  tff(c_986, plain, (k4_xboole_0('#skF_1', k1_xboole_0)='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_16, c_983])).
% 11.80/5.19  tff(c_1271, plain, (![B_82]: (r1_xboole_0(k4_xboole_0('#skF_1', B_82), k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_986, c_136])).
% 11.80/5.19  tff(c_1286, plain, (![B_82]: (k3_xboole_0(k4_xboole_0('#skF_1', B_82), k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_1271, c_2])).
% 11.80/5.19  tff(c_858, plain, (![B_75]: (k4_xboole_0('#skF_1', k4_xboole_0(B_75, '#skF_3'))=k2_xboole_0(k4_xboole_0('#skF_1', B_75), k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_144, c_828])).
% 11.80/5.19  tff(c_78, plain, (k2_xboole_0('#skF_1', k4_xboole_0('#skF_2', '#skF_3'))=k4_xboole_0('#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_30, c_70])).
% 11.80/5.19  tff(c_694, plain, (k5_xboole_0(k5_xboole_0('#skF_1', k4_xboole_0('#skF_2', '#skF_3')), k4_xboole_0('#skF_2', '#skF_3'))=k3_xboole_0('#skF_1', k4_xboole_0('#skF_2', '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_78, c_648])).
% 11.80/5.19  tff(c_769, plain, (k5_xboole_0(k5_xboole_0('#skF_1', k4_xboole_0('#skF_2', '#skF_3')), k5_xboole_0(k4_xboole_0('#skF_2', '#skF_3'), k3_xboole_0('#skF_1', k4_xboole_0('#skF_2', '#skF_3'))))=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_694, c_251])).
% 11.80/5.19  tff(c_1228, plain, (k5_xboole_0('#skF_1', k5_xboole_0(k4_xboole_0('#skF_2', '#skF_3'), k5_xboole_0(k4_xboole_0('#skF_2', '#skF_3'), k3_xboole_0('#skF_1', k4_xboole_0('#skF_2', '#skF_3')))))=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_22, c_769])).
% 11.80/5.19  tff(c_1236, plain, (k2_xboole_0(k4_xboole_0('#skF_1', '#skF_2'), k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_858, c_6, c_503, c_1228])).
% 11.80/5.19  tff(c_4203, plain, (![C_144]: (k5_xboole_0(k5_xboole_0(k4_xboole_0('#skF_1', '#skF_2'), k1_xboole_0), k5_xboole_0(k1_xboole_0, C_144))=k5_xboole_0(k3_xboole_0(k4_xboole_0('#skF_1', '#skF_2'), k1_xboole_0), C_144))), inference(superposition, [status(thm), theory('equality')], [c_1236, c_4096])).
% 11.80/5.19  tff(c_5011, plain, (![C_156]: (k5_xboole_0(k4_xboole_0('#skF_1', '#skF_2'), C_156)=C_156)), inference(demodulation, [status(thm), theory('equality')], [c_502, c_1286, c_502, c_16, c_4203])).
% 11.80/5.19  tff(c_5062, plain, (![C_156]: (k5_xboole_0(C_156, C_156)=k4_xboole_0('#skF_1', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_5011, c_1689])).
% 11.80/5.19  tff(c_5163, plain, (k4_xboole_0('#skF_1', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_24, c_5062])).
% 11.80/5.19  tff(c_5212, plain, (k2_xboole_0('#skF_2', k1_xboole_0)=k2_xboole_0('#skF_2', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_5163, c_12])).
% 11.80/5.19  tff(c_7022, plain, (k2_xboole_0('#skF_2', '#skF_1')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_6341, c_5212])).
% 11.80/5.19  tff(c_666, plain, (![A_72, B_73]: (k5_xboole_0(A_72, k5_xboole_0(B_73, k2_xboole_0(A_72, B_73)))=k3_xboole_0(A_72, B_73))), inference(superposition, [status(thm), theory('equality')], [c_648, c_22])).
% 11.80/5.19  tff(c_7035, plain, (k5_xboole_0('#skF_2', k5_xboole_0('#skF_1', '#skF_2'))=k3_xboole_0('#skF_2', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_7022, c_666])).
% 11.80/5.19  tff(c_7044, plain, (k3_xboole_0('#skF_2', '#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_643, c_7035])).
% 11.80/5.19  tff(c_14, plain, (![A_11, B_12, C_13]: (k2_xboole_0(k4_xboole_0(A_11, B_12), k3_xboole_0(A_11, C_13))=k4_xboole_0(A_11, k4_xboole_0(B_12, C_13)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 11.80/5.19  tff(c_6279, plain, (![B_172, C_13]: (k4_xboole_0(B_172, k4_xboole_0(B_172, C_13))=k2_xboole_0(k1_xboole_0, k3_xboole_0(B_172, C_13)))), inference(superposition, [status(thm), theory('equality')], [c_6223, c_14])).
% 11.80/5.19  tff(c_28234, plain, (![B_407, C_408]: (k4_xboole_0(B_407, k4_xboole_0(B_407, C_408))=k3_xboole_0(B_407, C_408))), inference(demodulation, [status(thm), theory('equality')], [c_5605, c_6279])).
% 11.80/5.19  tff(c_28961, plain, (![B_410, C_411]: (r1_tarski(k3_xboole_0(B_410, C_411), B_410))), inference(superposition, [status(thm), theory('equality')], [c_28234, c_10])).
% 11.80/5.19  tff(c_29062, plain, (r1_tarski('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_7044, c_28961])).
% 11.80/5.19  tff(c_29126, plain, $false, inference(negUnitSimplification, [status(thm)], [c_59, c_29062])).
% 11.80/5.19  tff(c_29127, plain, (~r1_xboole_0('#skF_1', '#skF_3')), inference(splitRight, [status(thm)], [c_28])).
% 11.80/5.19  tff(c_29237, plain, (![A_428, C_429, B_430]: (r1_xboole_0(A_428, C_429) | ~r1_xboole_0(B_430, C_429) | ~r1_tarski(A_428, B_430))), inference(cnfTransformation, [status(thm)], [f_49])).
% 11.80/5.19  tff(c_29257, plain, (![A_433, B_434, A_435]: (r1_xboole_0(A_433, B_434) | ~r1_tarski(A_433, k4_xboole_0(A_435, B_434)))), inference(resolution, [status(thm)], [c_20, c_29237])).
% 11.80/5.19  tff(c_29270, plain, (r1_xboole_0('#skF_1', '#skF_3')), inference(resolution, [status(thm)], [c_30, c_29257])).
% 11.80/5.19  tff(c_29277, plain, $false, inference(negUnitSimplification, [status(thm)], [c_29127, c_29270])).
% 11.80/5.19  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.80/5.19  
% 11.80/5.19  Inference rules
% 11.80/5.19  ----------------------
% 11.80/5.19  #Ref     : 0
% 11.80/5.19  #Sup     : 7419
% 11.80/5.19  #Fact    : 0
% 11.80/5.19  #Define  : 0
% 11.80/5.19  #Split   : 3
% 11.80/5.19  #Chain   : 0
% 11.80/5.19  #Close   : 0
% 11.80/5.19  
% 11.80/5.19  Ordering : KBO
% 11.80/5.19  
% 11.80/5.19  Simplification rules
% 11.80/5.19  ----------------------
% 11.80/5.19  #Subsume      : 128
% 11.80/5.19  #Demod        : 10485
% 11.80/5.19  #Tautology    : 4674
% 11.80/5.19  #SimpNegUnit  : 2
% 11.80/5.19  #BackRed      : 45
% 11.80/5.19  
% 11.80/5.19  #Partial instantiations: 0
% 11.80/5.19  #Strategies tried      : 1
% 11.80/5.19  
% 11.80/5.19  Timing (in seconds)
% 11.80/5.19  ----------------------
% 11.80/5.20  Preprocessing        : 0.28
% 11.80/5.20  Parsing              : 0.16
% 11.80/5.20  CNF conversion       : 0.02
% 11.80/5.20  Main loop            : 4.11
% 11.80/5.20  Inferencing          : 0.76
% 11.80/5.20  Reduction            : 2.40
% 11.80/5.20  Demodulation         : 2.15
% 11.80/5.20  BG Simplification    : 0.10
% 11.80/5.20  Subsumption          : 0.63
% 11.80/5.20  Abstraction          : 0.16
% 11.80/5.20  MUC search           : 0.00
% 11.80/5.20  Cooper               : 0.00
% 11.80/5.20  Total                : 4.44
% 11.80/5.20  Index Insertion      : 0.00
% 11.80/5.20  Index Deletion       : 0.00
% 11.80/5.20  Index Matching       : 0.00
% 11.80/5.20  BG Taut test         : 0.00
%------------------------------------------------------------------------------
