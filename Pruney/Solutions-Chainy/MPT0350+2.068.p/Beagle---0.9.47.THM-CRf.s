%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:55:34 EST 2020

% Result     : Theorem 9.91s
% Output     : CNFRefutation 9.91s
% Verified   : 
% Statistics : Number of formulae       :  107 ( 227 expanded)
%              Number of leaves         :   42 (  93 expanded)
%              Depth                    :   15
%              Number of atoms          :  113 ( 262 expanded)
%              Number of equality atoms :   70 ( 180 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k2_enumset1 > k4_subset_1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k2_subset_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_3 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff(k4_subset_1,type,(
    k4_subset_1: ( $i * $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_79,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_101,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => k4_subset_1(A,B,k3_subset_1(A,B)) = k2_subset_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_subset_1)).

tff(f_47,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

tff(f_83,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_51,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_90,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_77,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_62,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_35,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_49,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] : k2_xboole_0(A,k3_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_xboole_1)).

tff(f_45,axiom,(
    ! [A,B] : k4_xboole_0(A,k2_xboole_0(A,B)) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_37,axiom,(
    ! [A,B,C] : k5_xboole_0(k3_xboole_0(A,B),k3_xboole_0(C,B)) = k3_xboole_0(k5_xboole_0(A,C),B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t112_xboole_1)).

tff(f_87,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k3_subset_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).

tff(f_96,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(c_52,plain,(
    ! [A_36] : k2_subset_1(A_36) = A_36 ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_62,plain,(
    k4_subset_1('#skF_3','#skF_4',k3_subset_1('#skF_3','#skF_4')) != k2_subset_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_65,plain,(
    k4_subset_1('#skF_3','#skF_4',k3_subset_1('#skF_3','#skF_4')) != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_62])).

tff(c_20,plain,(
    ! [A_16] : k5_xboole_0(A_16,k1_xboole_0) = A_16 ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_64,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_397,plain,(
    ! [A_92,B_93] :
      ( k4_xboole_0(A_92,B_93) = k3_subset_1(A_92,B_93)
      | ~ m1_subset_1(B_93,k1_zfmisc_1(A_92)) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_410,plain,(
    k4_xboole_0('#skF_3','#skF_4') = k3_subset_1('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_64,c_397])).

tff(c_24,plain,(
    ! [A_20,B_21] : k5_xboole_0(A_20,k4_xboole_0(B_21,A_20)) = k2_xboole_0(A_20,B_21) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_416,plain,(
    k5_xboole_0('#skF_4',k3_subset_1('#skF_3','#skF_4')) = k2_xboole_0('#skF_4','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_410,c_24])).

tff(c_58,plain,(
    ! [A_41] : ~ v1_xboole_0(k1_zfmisc_1(A_41)) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_324,plain,(
    ! [B_85,A_86] :
      ( r2_hidden(B_85,A_86)
      | ~ m1_subset_1(B_85,A_86)
      | v1_xboole_0(A_86) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_30,plain,(
    ! [C_31,A_27] :
      ( r1_tarski(C_31,A_27)
      | ~ r2_hidden(C_31,k1_zfmisc_1(A_27)) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_331,plain,(
    ! [B_85,A_27] :
      ( r1_tarski(B_85,A_27)
      | ~ m1_subset_1(B_85,k1_zfmisc_1(A_27))
      | v1_xboole_0(k1_zfmisc_1(A_27)) ) ),
    inference(resolution,[status(thm)],[c_324,c_30])).

tff(c_345,plain,(
    ! [B_90,A_91] :
      ( r1_tarski(B_90,A_91)
      | ~ m1_subset_1(B_90,k1_zfmisc_1(A_91)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_331])).

tff(c_358,plain,(
    r1_tarski('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_64,c_345])).

tff(c_16,plain,(
    ! [A_12,B_13] :
      ( k3_xboole_0(A_12,B_13) = A_12
      | ~ r1_tarski(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_365,plain,(
    k3_xboole_0('#skF_4','#skF_3') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_358,c_16])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_288,plain,(
    ! [A_82,B_83] : k5_xboole_0(A_82,k3_xboole_0(A_82,B_83)) = k4_xboole_0(A_82,B_83) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_420,plain,(
    ! [A_94,B_95] : k5_xboole_0(A_94,k3_xboole_0(B_95,A_94)) = k4_xboole_0(A_94,B_95) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_288])).

tff(c_433,plain,(
    k5_xboole_0('#skF_3','#skF_4') = k4_xboole_0('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_365,c_420])).

tff(c_450,plain,(
    k5_xboole_0('#skF_3','#skF_4') = k3_subset_1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_410,c_433])).

tff(c_501,plain,(
    ! [A_98,B_99,C_100] : k5_xboole_0(k5_xboole_0(A_98,B_99),C_100) = k5_xboole_0(A_98,k5_xboole_0(B_99,C_100)) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_127,plain,(
    ! [A_53,B_54] : k2_xboole_0(A_53,k3_xboole_0(A_53,B_54)) = A_53 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_18,plain,(
    ! [A_14,B_15] : k4_xboole_0(A_14,k2_xboole_0(A_14,B_15)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_133,plain,(
    ! [A_53] : k4_xboole_0(A_53,A_53) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_127,c_18])).

tff(c_8,plain,(
    ! [B_4] : r1_tarski(B_4,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_189,plain,(
    ! [A_60,B_61] :
      ( k3_xboole_0(A_60,B_61) = A_60
      | ~ r1_tarski(A_60,B_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_193,plain,(
    ! [B_4] : k3_xboole_0(B_4,B_4) = B_4 ),
    inference(resolution,[status(thm)],[c_8,c_189])).

tff(c_297,plain,(
    ! [B_4] : k5_xboole_0(B_4,B_4) = k4_xboole_0(B_4,B_4) ),
    inference(superposition,[status(thm),theory(equality)],[c_193,c_288])).

tff(c_306,plain,(
    ! [B_4] : k5_xboole_0(B_4,B_4) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_133,c_297])).

tff(c_751,plain,(
    ! [A_105,B_106] : k5_xboole_0(A_105,k5_xboole_0(B_106,k5_xboole_0(A_105,B_106))) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_501,c_306])).

tff(c_830,plain,(
    k5_xboole_0('#skF_3',k5_xboole_0('#skF_4',k3_subset_1('#skF_3','#skF_4'))) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_450,c_751])).

tff(c_864,plain,(
    k5_xboole_0('#skF_3',k2_xboole_0('#skF_4','#skF_3')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_416,c_830])).

tff(c_972,plain,(
    ! [B_108,C_109] : k5_xboole_0(B_108,k5_xboole_0(B_108,C_109)) = k5_xboole_0(k1_xboole_0,C_109) ),
    inference(superposition,[status(thm),theory(equality)],[c_306,c_501])).

tff(c_1075,plain,(
    ! [B_4] : k5_xboole_0(k1_xboole_0,B_4) = k5_xboole_0(B_4,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_306,c_972])).

tff(c_1109,plain,(
    ! [B_4] : k5_xboole_0(k1_xboole_0,B_4) = B_4 ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_1075])).

tff(c_549,plain,(
    ! [B_4,C_100] : k5_xboole_0(B_4,k5_xboole_0(B_4,C_100)) = k5_xboole_0(k1_xboole_0,C_100) ),
    inference(superposition,[status(thm),theory(equality)],[c_306,c_501])).

tff(c_1206,plain,(
    ! [B_113,C_114] : k5_xboole_0(B_113,k5_xboole_0(B_113,C_114)) = C_114 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1109,c_549])).

tff(c_1254,plain,(
    k5_xboole_0('#skF_3',k1_xboole_0) = k2_xboole_0('#skF_4','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_864,c_1206])).

tff(c_1305,plain,(
    k2_xboole_0('#skF_4','#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_1254])).

tff(c_1313,plain,(
    k5_xboole_0('#skF_4',k3_subset_1('#skF_3','#skF_4')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1305,c_416])).

tff(c_300,plain,(
    ! [A_1,B_2] : k5_xboole_0(A_1,k3_xboole_0(B_2,A_1)) = k4_xboole_0(A_1,B_2) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_288])).

tff(c_139,plain,(
    ! [A_1,B_2] : k2_xboole_0(A_1,k3_xboole_0(B_2,A_1)) = A_1 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_127])).

tff(c_10,plain,(
    ! [A_5,B_6] : k5_xboole_0(A_5,k3_xboole_0(A_5,B_6)) = k4_xboole_0(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_1508,plain,(
    ! [A_119,B_120,C_121] : k5_xboole_0(k3_xboole_0(A_119,B_120),k3_xboole_0(C_121,B_120)) = k3_xboole_0(k5_xboole_0(A_119,C_121),B_120) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_1545,plain,(
    ! [A_119,B_6] : k3_xboole_0(k5_xboole_0(A_119,k3_xboole_0(A_119,B_6)),B_6) = k4_xboole_0(k3_xboole_0(A_119,B_6),B_6) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_1508])).

tff(c_2729,plain,(
    ! [A_150,B_151] : k4_xboole_0(k3_xboole_0(A_150,B_151),B_151) = k3_xboole_0(B_151,k4_xboole_0(A_150,B_151)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_10,c_1545])).

tff(c_2742,plain,(
    ! [B_151,A_150] : k5_xboole_0(B_151,k3_xboole_0(B_151,k4_xboole_0(A_150,B_151))) = k2_xboole_0(B_151,k3_xboole_0(A_150,B_151)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2729,c_24])).

tff(c_2784,plain,(
    ! [B_152,A_153] : k5_xboole_0(B_152,k3_xboole_0(B_152,k4_xboole_0(A_153,B_152))) = B_152 ),
    inference(demodulation,[status(thm),theory(equality)],[c_139,c_2742])).

tff(c_2884,plain,(
    ! [B_154,A_155] : k4_xboole_0(B_154,k4_xboole_0(A_155,B_154)) = B_154 ),
    inference(superposition,[status(thm),theory(equality)],[c_2784,c_10])).

tff(c_2776,plain,(
    ! [B_151,A_150] : k5_xboole_0(B_151,k3_xboole_0(B_151,k4_xboole_0(A_150,B_151))) = B_151 ),
    inference(demodulation,[status(thm),theory(equality)],[c_139,c_2742])).

tff(c_2893,plain,(
    ! [A_155,B_154] : k5_xboole_0(k4_xboole_0(A_155,B_154),k3_xboole_0(k4_xboole_0(A_155,B_154),B_154)) = k4_xboole_0(A_155,B_154) ),
    inference(superposition,[status(thm),theory(equality)],[c_2884,c_2776])).

tff(c_3639,plain,(
    ! [A_171,B_172] : k4_xboole_0(k4_xboole_0(A_171,B_172),B_172) = k4_xboole_0(A_171,B_172) ),
    inference(demodulation,[status(thm),theory(equality)],[c_300,c_2,c_2893])).

tff(c_3715,plain,(
    k4_xboole_0(k3_subset_1('#skF_3','#skF_4'),'#skF_4') = k4_xboole_0('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_410,c_3639])).

tff(c_3748,plain,(
    k4_xboole_0(k3_subset_1('#skF_3','#skF_4'),'#skF_4') = k3_subset_1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_410,c_3715])).

tff(c_3775,plain,(
    k5_xboole_0('#skF_4',k3_subset_1('#skF_3','#skF_4')) = k2_xboole_0('#skF_4',k3_subset_1('#skF_3','#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_3748,c_24])).

tff(c_3784,plain,(
    k2_xboole_0('#skF_4',k3_subset_1('#skF_3','#skF_4')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1313,c_3775])).

tff(c_56,plain,(
    ! [A_39,B_40] :
      ( m1_subset_1(k3_subset_1(A_39,B_40),k1_zfmisc_1(A_39))
      | ~ m1_subset_1(B_40,k1_zfmisc_1(A_39)) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_2641,plain,(
    ! [A_146,B_147,C_148] :
      ( k4_subset_1(A_146,B_147,C_148) = k2_xboole_0(B_147,C_148)
      | ~ m1_subset_1(C_148,k1_zfmisc_1(A_146))
      | ~ m1_subset_1(B_147,k1_zfmisc_1(A_146)) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_19354,plain,(
    ! [A_326,B_327,B_328] :
      ( k4_subset_1(A_326,B_327,k3_subset_1(A_326,B_328)) = k2_xboole_0(B_327,k3_subset_1(A_326,B_328))
      | ~ m1_subset_1(B_327,k1_zfmisc_1(A_326))
      | ~ m1_subset_1(B_328,k1_zfmisc_1(A_326)) ) ),
    inference(resolution,[status(thm)],[c_56,c_2641])).

tff(c_19639,plain,(
    ! [B_330] :
      ( k4_subset_1('#skF_3','#skF_4',k3_subset_1('#skF_3',B_330)) = k2_xboole_0('#skF_4',k3_subset_1('#skF_3',B_330))
      | ~ m1_subset_1(B_330,k1_zfmisc_1('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_64,c_19354])).

tff(c_19658,plain,(
    k4_subset_1('#skF_3','#skF_4',k3_subset_1('#skF_3','#skF_4')) = k2_xboole_0('#skF_4',k3_subset_1('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_64,c_19639])).

tff(c_19666,plain,(
    k4_subset_1('#skF_3','#skF_4',k3_subset_1('#skF_3','#skF_4')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3784,c_19658])).

tff(c_19668,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_65,c_19666])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:15:31 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 9.91/3.93  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.91/3.94  
% 9.91/3.94  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.91/3.94  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k2_enumset1 > k4_subset_1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k2_subset_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 9.91/3.94  
% 9.91/3.94  %Foreground sorts:
% 9.91/3.94  
% 9.91/3.94  
% 9.91/3.94  %Background operators:
% 9.91/3.94  
% 9.91/3.94  
% 9.91/3.94  %Foreground operators:
% 9.91/3.94  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 9.91/3.94  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 9.91/3.94  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 9.91/3.94  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 9.91/3.94  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 9.91/3.94  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 9.91/3.94  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 9.91/3.94  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 9.91/3.94  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 9.91/3.94  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 9.91/3.94  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 9.91/3.94  tff('#skF_3', type, '#skF_3': $i).
% 9.91/3.94  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 9.91/3.94  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 9.91/3.94  tff(k3_tarski, type, k3_tarski: $i > $i).
% 9.91/3.94  tff('#skF_4', type, '#skF_4': $i).
% 9.91/3.94  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 9.91/3.94  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 9.91/3.94  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 9.91/3.94  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 9.91/3.94  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 9.91/3.94  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 9.91/3.94  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 9.91/3.94  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 9.91/3.94  
% 9.91/3.96  tff(f_79, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 9.91/3.96  tff(f_101, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k4_subset_1(A, B, k3_subset_1(A, B)) = k2_subset_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t25_subset_1)).
% 9.91/3.96  tff(f_47, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 9.91/3.96  tff(f_83, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_subset_1)).
% 9.91/3.96  tff(f_51, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_xboole_1)).
% 9.91/3.96  tff(f_90, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_subset_1)).
% 9.91/3.96  tff(f_77, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 9.91/3.96  tff(f_62, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 9.91/3.96  tff(f_43, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 9.91/3.96  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 9.91/3.96  tff(f_35, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 9.91/3.96  tff(f_49, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_xboole_1)).
% 9.91/3.96  tff(f_39, axiom, (![A, B]: (k2_xboole_0(A, k3_xboole_0(A, B)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t22_xboole_1)).
% 9.91/3.96  tff(f_45, axiom, (![A, B]: (k4_xboole_0(A, k2_xboole_0(A, B)) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_xboole_1)).
% 9.91/3.96  tff(f_33, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 9.91/3.96  tff(f_37, axiom, (![A, B, C]: (k5_xboole_0(k3_xboole_0(A, B), k3_xboole_0(C, B)) = k3_xboole_0(k5_xboole_0(A, C), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t112_xboole_1)).
% 9.91/3.96  tff(f_87, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k3_subset_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 9.91/3.96  tff(f_96, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 9.91/3.96  tff(c_52, plain, (![A_36]: (k2_subset_1(A_36)=A_36)), inference(cnfTransformation, [status(thm)], [f_79])).
% 9.91/3.96  tff(c_62, plain, (k4_subset_1('#skF_3', '#skF_4', k3_subset_1('#skF_3', '#skF_4'))!=k2_subset_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_101])).
% 9.91/3.96  tff(c_65, plain, (k4_subset_1('#skF_3', '#skF_4', k3_subset_1('#skF_3', '#skF_4'))!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_52, c_62])).
% 9.91/3.96  tff(c_20, plain, (![A_16]: (k5_xboole_0(A_16, k1_xboole_0)=A_16)), inference(cnfTransformation, [status(thm)], [f_47])).
% 9.91/3.96  tff(c_64, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_101])).
% 9.91/3.96  tff(c_397, plain, (![A_92, B_93]: (k4_xboole_0(A_92, B_93)=k3_subset_1(A_92, B_93) | ~m1_subset_1(B_93, k1_zfmisc_1(A_92)))), inference(cnfTransformation, [status(thm)], [f_83])).
% 9.91/3.96  tff(c_410, plain, (k4_xboole_0('#skF_3', '#skF_4')=k3_subset_1('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_64, c_397])).
% 9.91/3.96  tff(c_24, plain, (![A_20, B_21]: (k5_xboole_0(A_20, k4_xboole_0(B_21, A_20))=k2_xboole_0(A_20, B_21))), inference(cnfTransformation, [status(thm)], [f_51])).
% 9.91/3.96  tff(c_416, plain, (k5_xboole_0('#skF_4', k3_subset_1('#skF_3', '#skF_4'))=k2_xboole_0('#skF_4', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_410, c_24])).
% 9.91/3.96  tff(c_58, plain, (![A_41]: (~v1_xboole_0(k1_zfmisc_1(A_41)))), inference(cnfTransformation, [status(thm)], [f_90])).
% 9.91/3.96  tff(c_324, plain, (![B_85, A_86]: (r2_hidden(B_85, A_86) | ~m1_subset_1(B_85, A_86) | v1_xboole_0(A_86))), inference(cnfTransformation, [status(thm)], [f_77])).
% 9.91/3.96  tff(c_30, plain, (![C_31, A_27]: (r1_tarski(C_31, A_27) | ~r2_hidden(C_31, k1_zfmisc_1(A_27)))), inference(cnfTransformation, [status(thm)], [f_62])).
% 9.91/3.96  tff(c_331, plain, (![B_85, A_27]: (r1_tarski(B_85, A_27) | ~m1_subset_1(B_85, k1_zfmisc_1(A_27)) | v1_xboole_0(k1_zfmisc_1(A_27)))), inference(resolution, [status(thm)], [c_324, c_30])).
% 9.91/3.96  tff(c_345, plain, (![B_90, A_91]: (r1_tarski(B_90, A_91) | ~m1_subset_1(B_90, k1_zfmisc_1(A_91)))), inference(negUnitSimplification, [status(thm)], [c_58, c_331])).
% 9.91/3.96  tff(c_358, plain, (r1_tarski('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_64, c_345])).
% 9.91/3.96  tff(c_16, plain, (![A_12, B_13]: (k3_xboole_0(A_12, B_13)=A_12 | ~r1_tarski(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_43])).
% 9.91/3.96  tff(c_365, plain, (k3_xboole_0('#skF_4', '#skF_3')='#skF_4'), inference(resolution, [status(thm)], [c_358, c_16])).
% 9.91/3.96  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 9.91/3.96  tff(c_288, plain, (![A_82, B_83]: (k5_xboole_0(A_82, k3_xboole_0(A_82, B_83))=k4_xboole_0(A_82, B_83))), inference(cnfTransformation, [status(thm)], [f_35])).
% 9.91/3.96  tff(c_420, plain, (![A_94, B_95]: (k5_xboole_0(A_94, k3_xboole_0(B_95, A_94))=k4_xboole_0(A_94, B_95))), inference(superposition, [status(thm), theory('equality')], [c_2, c_288])).
% 9.91/3.96  tff(c_433, plain, (k5_xboole_0('#skF_3', '#skF_4')=k4_xboole_0('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_365, c_420])).
% 9.91/3.96  tff(c_450, plain, (k5_xboole_0('#skF_3', '#skF_4')=k3_subset_1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_410, c_433])).
% 9.91/3.96  tff(c_501, plain, (![A_98, B_99, C_100]: (k5_xboole_0(k5_xboole_0(A_98, B_99), C_100)=k5_xboole_0(A_98, k5_xboole_0(B_99, C_100)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 9.91/3.96  tff(c_127, plain, (![A_53, B_54]: (k2_xboole_0(A_53, k3_xboole_0(A_53, B_54))=A_53)), inference(cnfTransformation, [status(thm)], [f_39])).
% 9.91/3.96  tff(c_18, plain, (![A_14, B_15]: (k4_xboole_0(A_14, k2_xboole_0(A_14, B_15))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_45])).
% 9.91/3.96  tff(c_133, plain, (![A_53]: (k4_xboole_0(A_53, A_53)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_127, c_18])).
% 9.91/3.96  tff(c_8, plain, (![B_4]: (r1_tarski(B_4, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 9.91/3.96  tff(c_189, plain, (![A_60, B_61]: (k3_xboole_0(A_60, B_61)=A_60 | ~r1_tarski(A_60, B_61))), inference(cnfTransformation, [status(thm)], [f_43])).
% 9.91/3.96  tff(c_193, plain, (![B_4]: (k3_xboole_0(B_4, B_4)=B_4)), inference(resolution, [status(thm)], [c_8, c_189])).
% 9.91/3.96  tff(c_297, plain, (![B_4]: (k5_xboole_0(B_4, B_4)=k4_xboole_0(B_4, B_4))), inference(superposition, [status(thm), theory('equality')], [c_193, c_288])).
% 9.91/3.96  tff(c_306, plain, (![B_4]: (k5_xboole_0(B_4, B_4)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_133, c_297])).
% 9.91/3.96  tff(c_751, plain, (![A_105, B_106]: (k5_xboole_0(A_105, k5_xboole_0(B_106, k5_xboole_0(A_105, B_106)))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_501, c_306])).
% 9.91/3.96  tff(c_830, plain, (k5_xboole_0('#skF_3', k5_xboole_0('#skF_4', k3_subset_1('#skF_3', '#skF_4')))=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_450, c_751])).
% 9.91/3.96  tff(c_864, plain, (k5_xboole_0('#skF_3', k2_xboole_0('#skF_4', '#skF_3'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_416, c_830])).
% 9.91/3.96  tff(c_972, plain, (![B_108, C_109]: (k5_xboole_0(B_108, k5_xboole_0(B_108, C_109))=k5_xboole_0(k1_xboole_0, C_109))), inference(superposition, [status(thm), theory('equality')], [c_306, c_501])).
% 9.91/3.96  tff(c_1075, plain, (![B_4]: (k5_xboole_0(k1_xboole_0, B_4)=k5_xboole_0(B_4, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_306, c_972])).
% 9.91/3.96  tff(c_1109, plain, (![B_4]: (k5_xboole_0(k1_xboole_0, B_4)=B_4)), inference(demodulation, [status(thm), theory('equality')], [c_20, c_1075])).
% 9.91/3.96  tff(c_549, plain, (![B_4, C_100]: (k5_xboole_0(B_4, k5_xboole_0(B_4, C_100))=k5_xboole_0(k1_xboole_0, C_100))), inference(superposition, [status(thm), theory('equality')], [c_306, c_501])).
% 9.91/3.96  tff(c_1206, plain, (![B_113, C_114]: (k5_xboole_0(B_113, k5_xboole_0(B_113, C_114))=C_114)), inference(demodulation, [status(thm), theory('equality')], [c_1109, c_549])).
% 9.91/3.96  tff(c_1254, plain, (k5_xboole_0('#skF_3', k1_xboole_0)=k2_xboole_0('#skF_4', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_864, c_1206])).
% 9.91/3.96  tff(c_1305, plain, (k2_xboole_0('#skF_4', '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_20, c_1254])).
% 9.91/3.96  tff(c_1313, plain, (k5_xboole_0('#skF_4', k3_subset_1('#skF_3', '#skF_4'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1305, c_416])).
% 9.91/3.96  tff(c_300, plain, (![A_1, B_2]: (k5_xboole_0(A_1, k3_xboole_0(B_2, A_1))=k4_xboole_0(A_1, B_2))), inference(superposition, [status(thm), theory('equality')], [c_2, c_288])).
% 9.91/3.96  tff(c_139, plain, (![A_1, B_2]: (k2_xboole_0(A_1, k3_xboole_0(B_2, A_1))=A_1)), inference(superposition, [status(thm), theory('equality')], [c_2, c_127])).
% 9.91/3.96  tff(c_10, plain, (![A_5, B_6]: (k5_xboole_0(A_5, k3_xboole_0(A_5, B_6))=k4_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_35])).
% 9.91/3.96  tff(c_1508, plain, (![A_119, B_120, C_121]: (k5_xboole_0(k3_xboole_0(A_119, B_120), k3_xboole_0(C_121, B_120))=k3_xboole_0(k5_xboole_0(A_119, C_121), B_120))), inference(cnfTransformation, [status(thm)], [f_37])).
% 9.91/3.96  tff(c_1545, plain, (![A_119, B_6]: (k3_xboole_0(k5_xboole_0(A_119, k3_xboole_0(A_119, B_6)), B_6)=k4_xboole_0(k3_xboole_0(A_119, B_6), B_6))), inference(superposition, [status(thm), theory('equality')], [c_10, c_1508])).
% 9.91/3.96  tff(c_2729, plain, (![A_150, B_151]: (k4_xboole_0(k3_xboole_0(A_150, B_151), B_151)=k3_xboole_0(B_151, k4_xboole_0(A_150, B_151)))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_10, c_1545])).
% 9.91/3.96  tff(c_2742, plain, (![B_151, A_150]: (k5_xboole_0(B_151, k3_xboole_0(B_151, k4_xboole_0(A_150, B_151)))=k2_xboole_0(B_151, k3_xboole_0(A_150, B_151)))), inference(superposition, [status(thm), theory('equality')], [c_2729, c_24])).
% 9.91/3.96  tff(c_2784, plain, (![B_152, A_153]: (k5_xboole_0(B_152, k3_xboole_0(B_152, k4_xboole_0(A_153, B_152)))=B_152)), inference(demodulation, [status(thm), theory('equality')], [c_139, c_2742])).
% 9.91/3.96  tff(c_2884, plain, (![B_154, A_155]: (k4_xboole_0(B_154, k4_xboole_0(A_155, B_154))=B_154)), inference(superposition, [status(thm), theory('equality')], [c_2784, c_10])).
% 9.91/3.96  tff(c_2776, plain, (![B_151, A_150]: (k5_xboole_0(B_151, k3_xboole_0(B_151, k4_xboole_0(A_150, B_151)))=B_151)), inference(demodulation, [status(thm), theory('equality')], [c_139, c_2742])).
% 9.91/3.96  tff(c_2893, plain, (![A_155, B_154]: (k5_xboole_0(k4_xboole_0(A_155, B_154), k3_xboole_0(k4_xboole_0(A_155, B_154), B_154))=k4_xboole_0(A_155, B_154))), inference(superposition, [status(thm), theory('equality')], [c_2884, c_2776])).
% 9.91/3.96  tff(c_3639, plain, (![A_171, B_172]: (k4_xboole_0(k4_xboole_0(A_171, B_172), B_172)=k4_xboole_0(A_171, B_172))), inference(demodulation, [status(thm), theory('equality')], [c_300, c_2, c_2893])).
% 9.91/3.96  tff(c_3715, plain, (k4_xboole_0(k3_subset_1('#skF_3', '#skF_4'), '#skF_4')=k4_xboole_0('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_410, c_3639])).
% 9.91/3.96  tff(c_3748, plain, (k4_xboole_0(k3_subset_1('#skF_3', '#skF_4'), '#skF_4')=k3_subset_1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_410, c_3715])).
% 9.91/3.96  tff(c_3775, plain, (k5_xboole_0('#skF_4', k3_subset_1('#skF_3', '#skF_4'))=k2_xboole_0('#skF_4', k3_subset_1('#skF_3', '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_3748, c_24])).
% 9.91/3.96  tff(c_3784, plain, (k2_xboole_0('#skF_4', k3_subset_1('#skF_3', '#skF_4'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1313, c_3775])).
% 9.91/3.96  tff(c_56, plain, (![A_39, B_40]: (m1_subset_1(k3_subset_1(A_39, B_40), k1_zfmisc_1(A_39)) | ~m1_subset_1(B_40, k1_zfmisc_1(A_39)))), inference(cnfTransformation, [status(thm)], [f_87])).
% 9.91/3.96  tff(c_2641, plain, (![A_146, B_147, C_148]: (k4_subset_1(A_146, B_147, C_148)=k2_xboole_0(B_147, C_148) | ~m1_subset_1(C_148, k1_zfmisc_1(A_146)) | ~m1_subset_1(B_147, k1_zfmisc_1(A_146)))), inference(cnfTransformation, [status(thm)], [f_96])).
% 9.91/3.96  tff(c_19354, plain, (![A_326, B_327, B_328]: (k4_subset_1(A_326, B_327, k3_subset_1(A_326, B_328))=k2_xboole_0(B_327, k3_subset_1(A_326, B_328)) | ~m1_subset_1(B_327, k1_zfmisc_1(A_326)) | ~m1_subset_1(B_328, k1_zfmisc_1(A_326)))), inference(resolution, [status(thm)], [c_56, c_2641])).
% 9.91/3.96  tff(c_19639, plain, (![B_330]: (k4_subset_1('#skF_3', '#skF_4', k3_subset_1('#skF_3', B_330))=k2_xboole_0('#skF_4', k3_subset_1('#skF_3', B_330)) | ~m1_subset_1(B_330, k1_zfmisc_1('#skF_3')))), inference(resolution, [status(thm)], [c_64, c_19354])).
% 9.91/3.96  tff(c_19658, plain, (k4_subset_1('#skF_3', '#skF_4', k3_subset_1('#skF_3', '#skF_4'))=k2_xboole_0('#skF_4', k3_subset_1('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_64, c_19639])).
% 9.91/3.96  tff(c_19666, plain, (k4_subset_1('#skF_3', '#skF_4', k3_subset_1('#skF_3', '#skF_4'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_3784, c_19658])).
% 9.91/3.96  tff(c_19668, plain, $false, inference(negUnitSimplification, [status(thm)], [c_65, c_19666])).
% 9.91/3.96  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.91/3.96  
% 9.91/3.96  Inference rules
% 9.91/3.96  ----------------------
% 9.91/3.96  #Ref     : 0
% 9.91/3.96  #Sup     : 4924
% 9.91/3.96  #Fact    : 0
% 9.91/3.96  #Define  : 0
% 9.91/3.96  #Split   : 1
% 9.91/3.96  #Chain   : 0
% 9.91/3.96  #Close   : 0
% 9.91/3.96  
% 9.91/3.96  Ordering : KBO
% 9.91/3.96  
% 9.91/3.96  Simplification rules
% 9.91/3.96  ----------------------
% 9.91/3.96  #Subsume      : 38
% 9.91/3.96  #Demod        : 5566
% 9.91/3.96  #Tautology    : 2874
% 9.91/3.96  #SimpNegUnit  : 14
% 9.91/3.96  #BackRed      : 17
% 9.91/3.96  
% 9.91/3.96  #Partial instantiations: 0
% 9.91/3.96  #Strategies tried      : 1
% 9.91/3.96  
% 9.91/3.96  Timing (in seconds)
% 9.91/3.96  ----------------------
% 9.91/3.96  Preprocessing        : 0.42
% 9.91/3.96  Parsing              : 0.22
% 9.91/3.96  CNF conversion       : 0.03
% 9.91/3.96  Main loop            : 2.72
% 9.91/3.96  Inferencing          : 0.58
% 9.91/3.96  Reduction            : 1.51
% 9.91/3.96  Demodulation         : 1.34
% 9.91/3.96  BG Simplification    : 0.08
% 9.91/3.96  Subsumption          : 0.42
% 9.91/3.96  Abstraction          : 0.12
% 9.91/3.96  MUC search           : 0.00
% 9.91/3.96  Cooper               : 0.00
% 9.91/3.96  Total                : 3.18
% 9.91/3.96  Index Insertion      : 0.00
% 9.91/3.96  Index Deletion       : 0.00
% 9.91/3.96  Index Matching       : 0.00
% 9.91/3.96  BG Taut test         : 0.00
%------------------------------------------------------------------------------
