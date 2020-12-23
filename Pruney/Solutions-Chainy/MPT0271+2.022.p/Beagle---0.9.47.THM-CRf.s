%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:53:04 EST 2020

% Result     : Theorem 3.37s
% Output     : CNFRefutation 3.61s
% Verified   : 
% Statistics : Number of formulae       :  112 ( 291 expanded)
%              Number of leaves         :   31 ( 108 expanded)
%              Depth                    :   14
%              Number of atoms          :  117 ( 316 expanded)
%              Number of equality atoms :   74 ( 247 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_2',type,(
    '#skF_2': $i > $i )).

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

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

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

tff(f_57,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

tff(f_55,axiom,(
    ! [A] : k4_xboole_0(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).

tff(f_59,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_75,axiom,(
    ! [A,B] : k2_xboole_0(k1_tarski(A),B) != k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_zfmisc_1)).

tff(f_49,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_80,negated_conjecture,(
    ~ ! [A,B] :
        ( k4_xboole_0(k1_tarski(A),B) = k1_xboole_0
      <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t68_zfmisc_1)).

tff(f_68,axiom,(
    ! [A,B] :
      ( ~ r2_hidden(A,B)
     => r1_xboole_0(k1_tarski(A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l27_zfmisc_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_53,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_51,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_72,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => k3_xboole_0(B,k1_tarski(A)) = k1_tarski(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l31_zfmisc_1)).

tff(c_16,plain,(
    ! [A_15] : k5_xboole_0(A_15,k1_xboole_0) = A_15 ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_14,plain,(
    ! [A_14] : k4_xboole_0(k1_xboole_0,A_14) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_113,plain,(
    ! [A_39,B_40] : k5_xboole_0(A_39,k4_xboole_0(B_40,A_39)) = k2_xboole_0(A_39,B_40) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_125,plain,(
    ! [A_14] : k5_xboole_0(A_14,k1_xboole_0) = k2_xboole_0(A_14,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_113])).

tff(c_130,plain,(
    ! [A_41] : k2_xboole_0(A_41,k1_xboole_0) = A_41 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_125])).

tff(c_28,plain,(
    ! [A_25,B_26] : k2_xboole_0(k1_tarski(A_25),B_26) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_137,plain,(
    ! [A_25] : k1_tarski(A_25) != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_130,c_28])).

tff(c_8,plain,(
    ! [A_8] :
      ( r2_hidden('#skF_2'(A_8),A_8)
      | k1_xboole_0 = A_8 ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_32,plain,
    ( r2_hidden('#skF_3','#skF_4')
    | ~ r2_hidden('#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_63,plain,(
    ~ r2_hidden('#skF_5','#skF_6') ),
    inference(splitLeft,[status(thm)],[c_32])).

tff(c_24,plain,(
    ! [A_21,B_22] :
      ( r1_xboole_0(k1_tarski(A_21),B_22)
      | r2_hidden(A_21,B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_163,plain,(
    ! [A_45,B_46] : k4_xboole_0(A_45,k4_xboole_0(A_45,B_46)) = k3_xboole_0(A_45,B_46) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_197,plain,(
    ! [B_47] : k3_xboole_0(k1_xboole_0,B_47) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_163,c_14])).

tff(c_224,plain,(
    ! [B_48] : k3_xboole_0(B_48,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_197])).

tff(c_10,plain,(
    ! [A_10,B_11] : k5_xboole_0(A_10,k3_xboole_0(A_10,B_11)) = k4_xboole_0(A_10,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_232,plain,(
    ! [B_48] : k5_xboole_0(B_48,k1_xboole_0) = k4_xboole_0(B_48,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_224,c_10])).

tff(c_254,plain,(
    ! [B_48] : k4_xboole_0(B_48,k1_xboole_0) = B_48 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_232])).

tff(c_36,plain,
    ( r2_hidden('#skF_3','#skF_4')
    | k4_xboole_0(k1_tarski('#skF_5'),'#skF_6') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_99,plain,(
    k4_xboole_0(k1_tarski('#skF_5'),'#skF_6') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_36])).

tff(c_185,plain,(
    k4_xboole_0(k1_tarski('#skF_5'),k1_xboole_0) = k3_xboole_0(k1_tarski('#skF_5'),'#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_99,c_163])).

tff(c_195,plain,(
    k4_xboole_0(k1_tarski('#skF_5'),k1_xboole_0) = k3_xboole_0('#skF_6',k1_tarski('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_185])).

tff(c_529,plain,(
    k3_xboole_0('#skF_6',k1_tarski('#skF_5')) = k1_tarski('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_254,c_195])).

tff(c_263,plain,(
    ! [A_49,B_50,C_51] :
      ( ~ r1_xboole_0(A_49,B_50)
      | ~ r2_hidden(C_51,k3_xboole_0(A_49,B_50)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_551,plain,(
    ! [B_65,A_66,C_67] :
      ( ~ r1_xboole_0(B_65,A_66)
      | ~ r2_hidden(C_67,k3_xboole_0(A_66,B_65)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_263])).

tff(c_554,plain,(
    ! [C_67] :
      ( ~ r1_xboole_0(k1_tarski('#skF_5'),'#skF_6')
      | ~ r2_hidden(C_67,k1_tarski('#skF_5')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_529,c_551])).

tff(c_715,plain,(
    ~ r1_xboole_0(k1_tarski('#skF_5'),'#skF_6') ),
    inference(splitLeft,[status(thm)],[c_554])).

tff(c_718,plain,(
    r2_hidden('#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_24,c_715])).

tff(c_722,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_63,c_718])).

tff(c_736,plain,(
    ! [C_78] : ~ r2_hidden(C_78,k1_tarski('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_554])).

tff(c_740,plain,(
    k1_tarski('#skF_5') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_8,c_736])).

tff(c_744,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_137,c_740])).

tff(c_745,plain,(
    r2_hidden('#skF_3','#skF_4') ),
    inference(splitRight,[status(thm)],[c_36])).

tff(c_773,plain,(
    ! [A_86,B_87] : k4_xboole_0(A_86,k4_xboole_0(A_86,B_87)) = k3_xboole_0(A_86,B_87) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_800,plain,(
    ! [B_88] : k3_xboole_0(k1_xboole_0,B_88) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_773,c_14])).

tff(c_817,plain,(
    ! [B_2] : k3_xboole_0(B_2,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_800])).

tff(c_863,plain,(
    ! [A_90,B_91] : k5_xboole_0(A_90,k3_xboole_0(A_90,B_91)) = k4_xboole_0(A_90,B_91) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_872,plain,(
    ! [B_2] : k5_xboole_0(B_2,k1_xboole_0) = k4_xboole_0(B_2,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_817,c_863])).

tff(c_888,plain,(
    ! [B_92] : k4_xboole_0(B_92,k1_xboole_0) = B_92 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_872])).

tff(c_12,plain,(
    ! [A_12,B_13] : k4_xboole_0(A_12,k4_xboole_0(A_12,B_13)) = k3_xboole_0(A_12,B_13) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_894,plain,(
    ! [B_92] : k4_xboole_0(B_92,B_92) = k3_xboole_0(B_92,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_888,c_12])).

tff(c_907,plain,(
    ! [B_92] : k4_xboole_0(B_92,B_92) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_817,c_894])).

tff(c_884,plain,(
    ! [B_2] : k4_xboole_0(B_2,k1_xboole_0) = B_2 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_872])).

tff(c_912,plain,(
    ! [B_93] : k4_xboole_0(B_93,B_93) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_817,c_894])).

tff(c_921,plain,(
    ! [B_93] : k4_xboole_0(B_93,k1_xboole_0) = k3_xboole_0(B_93,B_93) ),
    inference(superposition,[status(thm),theory(equality)],[c_912,c_12])).

tff(c_941,plain,(
    ! [B_94] : k3_xboole_0(B_94,B_94) = B_94 ),
    inference(demodulation,[status(thm),theory(equality)],[c_884,c_921])).

tff(c_947,plain,(
    ! [B_94] : k5_xboole_0(B_94,B_94) = k4_xboole_0(B_94,B_94) ),
    inference(superposition,[status(thm),theory(equality)],[c_941,c_10])).

tff(c_971,plain,(
    ! [B_94] : k5_xboole_0(B_94,B_94) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_907,c_947])).

tff(c_1062,plain,(
    ! [B_102,A_103] :
      ( k3_xboole_0(B_102,k1_tarski(A_103)) = k1_tarski(A_103)
      | ~ r2_hidden(A_103,B_102) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_1409,plain,(
    ! [A_125,B_126] :
      ( k3_xboole_0(k1_tarski(A_125),B_126) = k1_tarski(A_125)
      | ~ r2_hidden(A_125,B_126) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_1062])).

tff(c_1435,plain,(
    ! [A_125,B_126] :
      ( k5_xboole_0(k1_tarski(A_125),k1_tarski(A_125)) = k4_xboole_0(k1_tarski(A_125),B_126)
      | ~ r2_hidden(A_125,B_126) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1409,c_10])).

tff(c_1663,plain,(
    ! [A_136,B_137] :
      ( k4_xboole_0(k1_tarski(A_136),B_137) = k1_xboole_0
      | ~ r2_hidden(A_136,B_137) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_971,c_1435])).

tff(c_746,plain,(
    k4_xboole_0(k1_tarski('#skF_5'),'#skF_6') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_36])).

tff(c_34,plain,
    ( k4_xboole_0(k1_tarski('#skF_3'),'#skF_4') != k1_xboole_0
    | k4_xboole_0(k1_tarski('#skF_5'),'#skF_6') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_911,plain,(
    k4_xboole_0(k1_tarski('#skF_3'),'#skF_4') != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_746,c_34])).

tff(c_1680,plain,(
    ~ r2_hidden('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1663,c_911])).

tff(c_1723,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_745,c_1680])).

tff(c_1724,plain,(
    r2_hidden('#skF_3','#skF_4') ),
    inference(splitRight,[status(thm)],[c_32])).

tff(c_1830,plain,(
    ! [A_156,B_157] : k4_xboole_0(A_156,k4_xboole_0(A_156,B_157)) = k3_xboole_0(A_156,B_157) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_1862,plain,(
    ! [B_158] : k3_xboole_0(k1_xboole_0,B_158) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_1830,c_14])).

tff(c_1876,plain,(
    ! [B_158] : k3_xboole_0(B_158,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_1862,c_2])).

tff(c_1892,plain,(
    ! [B_159] : k3_xboole_0(B_159,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_1862,c_2])).

tff(c_1903,plain,(
    ! [B_159] : k5_xboole_0(B_159,k1_xboole_0) = k4_xboole_0(B_159,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_1892,c_10])).

tff(c_1981,plain,(
    ! [B_163] : k4_xboole_0(B_163,k1_xboole_0) = B_163 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_1903])).

tff(c_1987,plain,(
    ! [B_163] : k4_xboole_0(B_163,B_163) = k3_xboole_0(B_163,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_1981,c_12])).

tff(c_2003,plain,(
    ! [B_163] : k4_xboole_0(B_163,B_163) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1876,c_1987])).

tff(c_1925,plain,(
    ! [B_159] : k4_xboole_0(B_159,k1_xboole_0) = B_159 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_1903])).

tff(c_2007,plain,(
    ! [B_164] : k4_xboole_0(B_164,B_164) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1876,c_1987])).

tff(c_2016,plain,(
    ! [B_164] : k4_xboole_0(B_164,k1_xboole_0) = k3_xboole_0(B_164,B_164) ),
    inference(superposition,[status(thm),theory(equality)],[c_2007,c_12])).

tff(c_2040,plain,(
    ! [B_165] : k3_xboole_0(B_165,B_165) = B_165 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1925,c_2016])).

tff(c_2061,plain,(
    ! [B_165] : k5_xboole_0(B_165,B_165) = k4_xboole_0(B_165,B_165) ),
    inference(superposition,[status(thm),theory(equality)],[c_2040,c_10])).

tff(c_2081,plain,(
    ! [B_165] : k5_xboole_0(B_165,B_165) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2003,c_2061])).

tff(c_1933,plain,(
    ! [B_160,A_161] :
      ( k3_xboole_0(B_160,k1_tarski(A_161)) = k1_tarski(A_161)
      | ~ r2_hidden(A_161,B_160) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_2556,plain,(
    ! [A_193,A_194] :
      ( k3_xboole_0(k1_tarski(A_193),A_194) = k1_tarski(A_193)
      | ~ r2_hidden(A_193,A_194) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_1933])).

tff(c_2593,plain,(
    ! [A_193,A_194] :
      ( k5_xboole_0(k1_tarski(A_193),k1_tarski(A_193)) = k4_xboole_0(k1_tarski(A_193),A_194)
      | ~ r2_hidden(A_193,A_194) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2556,c_10])).

tff(c_2686,plain,(
    ! [A_200,A_201] :
      ( k4_xboole_0(k1_tarski(A_200),A_201) = k1_xboole_0
      | ~ r2_hidden(A_200,A_201) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2081,c_2593])).

tff(c_1725,plain,(
    r2_hidden('#skF_5','#skF_6') ),
    inference(splitRight,[status(thm)],[c_32])).

tff(c_30,plain,
    ( k4_xboole_0(k1_tarski('#skF_3'),'#skF_4') != k1_xboole_0
    | ~ r2_hidden('#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_1861,plain,(
    k4_xboole_0(k1_tarski('#skF_3'),'#skF_4') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1725,c_30])).

tff(c_2704,plain,(
    ~ r2_hidden('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_2686,c_1861])).

tff(c_2743,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1724,c_2704])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n022.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 13:14:56 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.37/1.66  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.37/1.66  
% 3.37/1.66  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.37/1.67  %$ r2_hidden > r1_xboole_0 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_1
% 3.37/1.67  
% 3.37/1.67  %Foreground sorts:
% 3.37/1.67  
% 3.37/1.67  
% 3.37/1.67  %Background operators:
% 3.37/1.67  
% 3.37/1.67  
% 3.37/1.67  %Foreground operators:
% 3.37/1.67  tff('#skF_2', type, '#skF_2': $i > $i).
% 3.37/1.67  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.37/1.67  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.37/1.67  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.37/1.67  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.37/1.67  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.37/1.67  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.37/1.67  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.37/1.67  tff('#skF_5', type, '#skF_5': $i).
% 3.37/1.67  tff('#skF_6', type, '#skF_6': $i).
% 3.37/1.67  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.37/1.67  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.37/1.67  tff('#skF_3', type, '#skF_3': $i).
% 3.37/1.67  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.37/1.67  tff('#skF_4', type, '#skF_4': $i).
% 3.37/1.67  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.37/1.67  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.37/1.67  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.37/1.67  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.37/1.67  
% 3.61/1.68  tff(f_57, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 3.61/1.68  tff(f_55, axiom, (![A]: (k4_xboole_0(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_boole)).
% 3.61/1.68  tff(f_59, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_xboole_1)).
% 3.61/1.68  tff(f_75, axiom, (![A, B]: ~(k2_xboole_0(k1_tarski(A), B) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_zfmisc_1)).
% 3.61/1.68  tff(f_49, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 3.61/1.68  tff(f_80, negated_conjecture, ~(![A, B]: ((k4_xboole_0(k1_tarski(A), B) = k1_xboole_0) <=> r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t68_zfmisc_1)).
% 3.61/1.68  tff(f_68, axiom, (![A, B]: (~r2_hidden(A, B) => r1_xboole_0(k1_tarski(A), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 3.61/1.68  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 3.61/1.68  tff(f_53, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 3.61/1.68  tff(f_51, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 3.61/1.68  tff(f_41, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 3.61/1.68  tff(f_72, axiom, (![A, B]: (r2_hidden(A, B) => (k3_xboole_0(B, k1_tarski(A)) = k1_tarski(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l31_zfmisc_1)).
% 3.61/1.68  tff(c_16, plain, (![A_15]: (k5_xboole_0(A_15, k1_xboole_0)=A_15)), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.61/1.68  tff(c_14, plain, (![A_14]: (k4_xboole_0(k1_xboole_0, A_14)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.61/1.68  tff(c_113, plain, (![A_39, B_40]: (k5_xboole_0(A_39, k4_xboole_0(B_40, A_39))=k2_xboole_0(A_39, B_40))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.61/1.68  tff(c_125, plain, (![A_14]: (k5_xboole_0(A_14, k1_xboole_0)=k2_xboole_0(A_14, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_14, c_113])).
% 3.61/1.68  tff(c_130, plain, (![A_41]: (k2_xboole_0(A_41, k1_xboole_0)=A_41)), inference(demodulation, [status(thm), theory('equality')], [c_16, c_125])).
% 3.61/1.68  tff(c_28, plain, (![A_25, B_26]: (k2_xboole_0(k1_tarski(A_25), B_26)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.61/1.68  tff(c_137, plain, (![A_25]: (k1_tarski(A_25)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_130, c_28])).
% 3.61/1.68  tff(c_8, plain, (![A_8]: (r2_hidden('#skF_2'(A_8), A_8) | k1_xboole_0=A_8)), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.61/1.68  tff(c_32, plain, (r2_hidden('#skF_3', '#skF_4') | ~r2_hidden('#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.61/1.68  tff(c_63, plain, (~r2_hidden('#skF_5', '#skF_6')), inference(splitLeft, [status(thm)], [c_32])).
% 3.61/1.68  tff(c_24, plain, (![A_21, B_22]: (r1_xboole_0(k1_tarski(A_21), B_22) | r2_hidden(A_21, B_22))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.61/1.68  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.61/1.68  tff(c_163, plain, (![A_45, B_46]: (k4_xboole_0(A_45, k4_xboole_0(A_45, B_46))=k3_xboole_0(A_45, B_46))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.61/1.68  tff(c_197, plain, (![B_47]: (k3_xboole_0(k1_xboole_0, B_47)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_163, c_14])).
% 3.61/1.68  tff(c_224, plain, (![B_48]: (k3_xboole_0(B_48, k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2, c_197])).
% 3.61/1.68  tff(c_10, plain, (![A_10, B_11]: (k5_xboole_0(A_10, k3_xboole_0(A_10, B_11))=k4_xboole_0(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.61/1.68  tff(c_232, plain, (![B_48]: (k5_xboole_0(B_48, k1_xboole_0)=k4_xboole_0(B_48, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_224, c_10])).
% 3.61/1.68  tff(c_254, plain, (![B_48]: (k4_xboole_0(B_48, k1_xboole_0)=B_48)), inference(demodulation, [status(thm), theory('equality')], [c_16, c_232])).
% 3.61/1.68  tff(c_36, plain, (r2_hidden('#skF_3', '#skF_4') | k4_xboole_0(k1_tarski('#skF_5'), '#skF_6')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.61/1.68  tff(c_99, plain, (k4_xboole_0(k1_tarski('#skF_5'), '#skF_6')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_36])).
% 3.61/1.68  tff(c_185, plain, (k4_xboole_0(k1_tarski('#skF_5'), k1_xboole_0)=k3_xboole_0(k1_tarski('#skF_5'), '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_99, c_163])).
% 3.61/1.68  tff(c_195, plain, (k4_xboole_0(k1_tarski('#skF_5'), k1_xboole_0)=k3_xboole_0('#skF_6', k1_tarski('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_185])).
% 3.61/1.68  tff(c_529, plain, (k3_xboole_0('#skF_6', k1_tarski('#skF_5'))=k1_tarski('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_254, c_195])).
% 3.61/1.68  tff(c_263, plain, (![A_49, B_50, C_51]: (~r1_xboole_0(A_49, B_50) | ~r2_hidden(C_51, k3_xboole_0(A_49, B_50)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.61/1.68  tff(c_551, plain, (![B_65, A_66, C_67]: (~r1_xboole_0(B_65, A_66) | ~r2_hidden(C_67, k3_xboole_0(A_66, B_65)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_263])).
% 3.61/1.68  tff(c_554, plain, (![C_67]: (~r1_xboole_0(k1_tarski('#skF_5'), '#skF_6') | ~r2_hidden(C_67, k1_tarski('#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_529, c_551])).
% 3.61/1.68  tff(c_715, plain, (~r1_xboole_0(k1_tarski('#skF_5'), '#skF_6')), inference(splitLeft, [status(thm)], [c_554])).
% 3.61/1.68  tff(c_718, plain, (r2_hidden('#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_24, c_715])).
% 3.61/1.68  tff(c_722, plain, $false, inference(negUnitSimplification, [status(thm)], [c_63, c_718])).
% 3.61/1.68  tff(c_736, plain, (![C_78]: (~r2_hidden(C_78, k1_tarski('#skF_5')))), inference(splitRight, [status(thm)], [c_554])).
% 3.61/1.68  tff(c_740, plain, (k1_tarski('#skF_5')=k1_xboole_0), inference(resolution, [status(thm)], [c_8, c_736])).
% 3.61/1.68  tff(c_744, plain, $false, inference(negUnitSimplification, [status(thm)], [c_137, c_740])).
% 3.61/1.68  tff(c_745, plain, (r2_hidden('#skF_3', '#skF_4')), inference(splitRight, [status(thm)], [c_36])).
% 3.61/1.68  tff(c_773, plain, (![A_86, B_87]: (k4_xboole_0(A_86, k4_xboole_0(A_86, B_87))=k3_xboole_0(A_86, B_87))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.61/1.68  tff(c_800, plain, (![B_88]: (k3_xboole_0(k1_xboole_0, B_88)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_773, c_14])).
% 3.61/1.68  tff(c_817, plain, (![B_2]: (k3_xboole_0(B_2, k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2, c_800])).
% 3.61/1.68  tff(c_863, plain, (![A_90, B_91]: (k5_xboole_0(A_90, k3_xboole_0(A_90, B_91))=k4_xboole_0(A_90, B_91))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.61/1.68  tff(c_872, plain, (![B_2]: (k5_xboole_0(B_2, k1_xboole_0)=k4_xboole_0(B_2, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_817, c_863])).
% 3.61/1.68  tff(c_888, plain, (![B_92]: (k4_xboole_0(B_92, k1_xboole_0)=B_92)), inference(demodulation, [status(thm), theory('equality')], [c_16, c_872])).
% 3.61/1.68  tff(c_12, plain, (![A_12, B_13]: (k4_xboole_0(A_12, k4_xboole_0(A_12, B_13))=k3_xboole_0(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.61/1.68  tff(c_894, plain, (![B_92]: (k4_xboole_0(B_92, B_92)=k3_xboole_0(B_92, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_888, c_12])).
% 3.61/1.68  tff(c_907, plain, (![B_92]: (k4_xboole_0(B_92, B_92)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_817, c_894])).
% 3.61/1.68  tff(c_884, plain, (![B_2]: (k4_xboole_0(B_2, k1_xboole_0)=B_2)), inference(demodulation, [status(thm), theory('equality')], [c_16, c_872])).
% 3.61/1.68  tff(c_912, plain, (![B_93]: (k4_xboole_0(B_93, B_93)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_817, c_894])).
% 3.61/1.68  tff(c_921, plain, (![B_93]: (k4_xboole_0(B_93, k1_xboole_0)=k3_xboole_0(B_93, B_93))), inference(superposition, [status(thm), theory('equality')], [c_912, c_12])).
% 3.61/1.68  tff(c_941, plain, (![B_94]: (k3_xboole_0(B_94, B_94)=B_94)), inference(demodulation, [status(thm), theory('equality')], [c_884, c_921])).
% 3.61/1.68  tff(c_947, plain, (![B_94]: (k5_xboole_0(B_94, B_94)=k4_xboole_0(B_94, B_94))), inference(superposition, [status(thm), theory('equality')], [c_941, c_10])).
% 3.61/1.68  tff(c_971, plain, (![B_94]: (k5_xboole_0(B_94, B_94)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_907, c_947])).
% 3.61/1.68  tff(c_1062, plain, (![B_102, A_103]: (k3_xboole_0(B_102, k1_tarski(A_103))=k1_tarski(A_103) | ~r2_hidden(A_103, B_102))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.61/1.68  tff(c_1409, plain, (![A_125, B_126]: (k3_xboole_0(k1_tarski(A_125), B_126)=k1_tarski(A_125) | ~r2_hidden(A_125, B_126))), inference(superposition, [status(thm), theory('equality')], [c_2, c_1062])).
% 3.61/1.68  tff(c_1435, plain, (![A_125, B_126]: (k5_xboole_0(k1_tarski(A_125), k1_tarski(A_125))=k4_xboole_0(k1_tarski(A_125), B_126) | ~r2_hidden(A_125, B_126))), inference(superposition, [status(thm), theory('equality')], [c_1409, c_10])).
% 3.61/1.68  tff(c_1663, plain, (![A_136, B_137]: (k4_xboole_0(k1_tarski(A_136), B_137)=k1_xboole_0 | ~r2_hidden(A_136, B_137))), inference(demodulation, [status(thm), theory('equality')], [c_971, c_1435])).
% 3.61/1.68  tff(c_746, plain, (k4_xboole_0(k1_tarski('#skF_5'), '#skF_6')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_36])).
% 3.61/1.68  tff(c_34, plain, (k4_xboole_0(k1_tarski('#skF_3'), '#skF_4')!=k1_xboole_0 | k4_xboole_0(k1_tarski('#skF_5'), '#skF_6')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.61/1.68  tff(c_911, plain, (k4_xboole_0(k1_tarski('#skF_3'), '#skF_4')!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_746, c_34])).
% 3.61/1.68  tff(c_1680, plain, (~r2_hidden('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1663, c_911])).
% 3.61/1.68  tff(c_1723, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_745, c_1680])).
% 3.61/1.68  tff(c_1724, plain, (r2_hidden('#skF_3', '#skF_4')), inference(splitRight, [status(thm)], [c_32])).
% 3.61/1.68  tff(c_1830, plain, (![A_156, B_157]: (k4_xboole_0(A_156, k4_xboole_0(A_156, B_157))=k3_xboole_0(A_156, B_157))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.61/1.68  tff(c_1862, plain, (![B_158]: (k3_xboole_0(k1_xboole_0, B_158)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_1830, c_14])).
% 3.61/1.68  tff(c_1876, plain, (![B_158]: (k3_xboole_0(B_158, k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_1862, c_2])).
% 3.61/1.68  tff(c_1892, plain, (![B_159]: (k3_xboole_0(B_159, k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_1862, c_2])).
% 3.61/1.68  tff(c_1903, plain, (![B_159]: (k5_xboole_0(B_159, k1_xboole_0)=k4_xboole_0(B_159, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_1892, c_10])).
% 3.61/1.68  tff(c_1981, plain, (![B_163]: (k4_xboole_0(B_163, k1_xboole_0)=B_163)), inference(demodulation, [status(thm), theory('equality')], [c_16, c_1903])).
% 3.61/1.68  tff(c_1987, plain, (![B_163]: (k4_xboole_0(B_163, B_163)=k3_xboole_0(B_163, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_1981, c_12])).
% 3.61/1.68  tff(c_2003, plain, (![B_163]: (k4_xboole_0(B_163, B_163)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_1876, c_1987])).
% 3.61/1.68  tff(c_1925, plain, (![B_159]: (k4_xboole_0(B_159, k1_xboole_0)=B_159)), inference(demodulation, [status(thm), theory('equality')], [c_16, c_1903])).
% 3.61/1.68  tff(c_2007, plain, (![B_164]: (k4_xboole_0(B_164, B_164)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_1876, c_1987])).
% 3.61/1.68  tff(c_2016, plain, (![B_164]: (k4_xboole_0(B_164, k1_xboole_0)=k3_xboole_0(B_164, B_164))), inference(superposition, [status(thm), theory('equality')], [c_2007, c_12])).
% 3.61/1.68  tff(c_2040, plain, (![B_165]: (k3_xboole_0(B_165, B_165)=B_165)), inference(demodulation, [status(thm), theory('equality')], [c_1925, c_2016])).
% 3.61/1.68  tff(c_2061, plain, (![B_165]: (k5_xboole_0(B_165, B_165)=k4_xboole_0(B_165, B_165))), inference(superposition, [status(thm), theory('equality')], [c_2040, c_10])).
% 3.61/1.68  tff(c_2081, plain, (![B_165]: (k5_xboole_0(B_165, B_165)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_2003, c_2061])).
% 3.61/1.68  tff(c_1933, plain, (![B_160, A_161]: (k3_xboole_0(B_160, k1_tarski(A_161))=k1_tarski(A_161) | ~r2_hidden(A_161, B_160))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.61/1.68  tff(c_2556, plain, (![A_193, A_194]: (k3_xboole_0(k1_tarski(A_193), A_194)=k1_tarski(A_193) | ~r2_hidden(A_193, A_194))), inference(superposition, [status(thm), theory('equality')], [c_2, c_1933])).
% 3.61/1.68  tff(c_2593, plain, (![A_193, A_194]: (k5_xboole_0(k1_tarski(A_193), k1_tarski(A_193))=k4_xboole_0(k1_tarski(A_193), A_194) | ~r2_hidden(A_193, A_194))), inference(superposition, [status(thm), theory('equality')], [c_2556, c_10])).
% 3.61/1.68  tff(c_2686, plain, (![A_200, A_201]: (k4_xboole_0(k1_tarski(A_200), A_201)=k1_xboole_0 | ~r2_hidden(A_200, A_201))), inference(demodulation, [status(thm), theory('equality')], [c_2081, c_2593])).
% 3.61/1.68  tff(c_1725, plain, (r2_hidden('#skF_5', '#skF_6')), inference(splitRight, [status(thm)], [c_32])).
% 3.61/1.68  tff(c_30, plain, (k4_xboole_0(k1_tarski('#skF_3'), '#skF_4')!=k1_xboole_0 | ~r2_hidden('#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.61/1.68  tff(c_1861, plain, (k4_xboole_0(k1_tarski('#skF_3'), '#skF_4')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_1725, c_30])).
% 3.61/1.68  tff(c_2704, plain, (~r2_hidden('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_2686, c_1861])).
% 3.61/1.68  tff(c_2743, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1724, c_2704])).
% 3.61/1.68  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.61/1.68  
% 3.61/1.68  Inference rules
% 3.61/1.68  ----------------------
% 3.61/1.68  #Ref     : 0
% 3.61/1.68  #Sup     : 625
% 3.61/1.68  #Fact    : 0
% 3.61/1.68  #Define  : 0
% 3.61/1.68  #Split   : 5
% 3.61/1.68  #Chain   : 0
% 3.61/1.68  #Close   : 0
% 3.61/1.68  
% 3.61/1.68  Ordering : KBO
% 3.61/1.68  
% 3.61/1.68  Simplification rules
% 3.61/1.68  ----------------------
% 3.61/1.68  #Subsume      : 101
% 3.61/1.68  #Demod        : 217
% 3.61/1.68  #Tautology    : 347
% 3.61/1.68  #SimpNegUnit  : 68
% 3.61/1.68  #BackRed      : 0
% 3.61/1.68  
% 3.61/1.68  #Partial instantiations: 0
% 3.61/1.68  #Strategies tried      : 1
% 3.61/1.68  
% 3.61/1.68  Timing (in seconds)
% 3.61/1.68  ----------------------
% 3.61/1.69  Preprocessing        : 0.31
% 3.61/1.69  Parsing              : 0.17
% 3.61/1.69  CNF conversion       : 0.02
% 3.61/1.69  Main loop            : 0.52
% 3.61/1.69  Inferencing          : 0.21
% 3.61/1.69  Reduction            : 0.18
% 3.61/1.69  Demodulation         : 0.13
% 3.61/1.69  BG Simplification    : 0.02
% 3.61/1.69  Subsumption          : 0.07
% 3.61/1.69  Abstraction          : 0.03
% 3.61/1.69  MUC search           : 0.00
% 3.61/1.69  Cooper               : 0.00
% 3.61/1.69  Total                : 0.87
% 3.61/1.69  Index Insertion      : 0.00
% 3.61/1.69  Index Deletion       : 0.00
% 3.61/1.69  Index Matching       : 0.00
% 3.61/1.69  BG Taut test         : 0.00
%------------------------------------------------------------------------------
