%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:55:48 EST 2020

% Result     : Theorem 15.00s
% Output     : CNFRefutation 15.00s
% Verified   : 
% Statistics : Number of formulae       :  100 ( 147 expanded)
%              Number of leaves         :   34 (  60 expanded)
%              Depth                    :   11
%              Number of atoms          :  126 ( 229 expanded)
%              Number of equality atoms :   39 (  55 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1

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

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_100,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => ! [C] :
            ( m1_subset_1(C,k1_zfmisc_1(A))
           => ( r1_tarski(B,C)
            <=> r1_tarski(k3_subset_1(A,C),k3_subset_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_subset_1)).

tff(f_51,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_45,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_59,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k4_xboole_0(A,B),C)
     => r1_tarski(A,k2_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_xboole_1)).

tff(f_90,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_83,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_70,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_55,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k2_xboole_0(B,C))
     => r1_tarski(k4_xboole_0(A,B),C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_xboole_1)).

tff(f_61,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_87,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_63,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_49,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(k4_xboole_0(C,B),k4_xboole_0(C,A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_xboole_1)).

tff(c_64,plain,
    ( r1_tarski('#skF_4','#skF_5')
    | r1_tarski(k3_subset_1('#skF_3','#skF_5'),k3_subset_1('#skF_3','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_119,plain,(
    r1_tarski(k3_subset_1('#skF_3','#skF_5'),k3_subset_1('#skF_3','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_64])).

tff(c_58,plain,
    ( ~ r1_tarski(k3_subset_1('#skF_3','#skF_5'),k3_subset_1('#skF_3','#skF_4'))
    | ~ r1_tarski('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_253,plain,(
    ~ r1_tarski('#skF_4','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_58])).

tff(c_20,plain,(
    ! [A_16,B_17] : r1_tarski(k4_xboole_0(A_16,B_17),A_16) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_16,plain,(
    ! [A_12] : r1_tarski(k1_xboole_0,A_12) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_174,plain,(
    ! [A_60,B_61] :
      ( k2_xboole_0(A_60,B_61) = B_61
      | ~ r1_tarski(A_60,B_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_194,plain,(
    ! [A_12] : k2_xboole_0(k1_xboole_0,A_12) = A_12 ),
    inference(resolution,[status(thm)],[c_16,c_174])).

tff(c_10,plain,(
    ! [B_6] : r1_tarski(B_6,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_1566,plain,(
    ! [A_120,B_121,C_122] :
      ( r1_tarski(A_120,k2_xboole_0(B_121,C_122))
      | ~ r1_tarski(k4_xboole_0(A_120,B_121),C_122) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_2727,plain,(
    ! [A_154,B_155] : r1_tarski(A_154,k2_xboole_0(B_155,k4_xboole_0(A_154,B_155))) ),
    inference(resolution,[status(thm)],[c_10,c_1566])).

tff(c_2783,plain,(
    ! [A_156] : r1_tarski(A_156,k4_xboole_0(A_156,k1_xboole_0)) ),
    inference(superposition,[status(thm),theory(equality)],[c_194,c_2727])).

tff(c_6,plain,(
    ! [B_6,A_5] :
      ( B_6 = A_5
      | ~ r1_tarski(B_6,A_5)
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_2793,plain,(
    ! [A_156] :
      ( k4_xboole_0(A_156,k1_xboole_0) = A_156
      | ~ r1_tarski(k4_xboole_0(A_156,k1_xboole_0),A_156) ) ),
    inference(resolution,[status(thm)],[c_2783,c_6])).

tff(c_2809,plain,(
    ! [A_156] : k4_xboole_0(A_156,k1_xboole_0) = A_156 ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_2793])).

tff(c_56,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_52,plain,(
    ! [A_37] : ~ v1_xboole_0(k1_zfmisc_1(A_37)) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_1205,plain,(
    ! [B_108,A_109] :
      ( r2_hidden(B_108,A_109)
      | ~ m1_subset_1(B_108,A_109)
      | v1_xboole_0(A_109) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_30,plain,(
    ! [C_32,A_28] :
      ( r1_tarski(C_32,A_28)
      | ~ r2_hidden(C_32,k1_zfmisc_1(A_28)) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_1212,plain,(
    ! [B_108,A_28] :
      ( r1_tarski(B_108,A_28)
      | ~ m1_subset_1(B_108,k1_zfmisc_1(A_28))
      | v1_xboole_0(k1_zfmisc_1(A_28)) ) ),
    inference(resolution,[status(thm)],[c_1205,c_30])).

tff(c_1381,plain,(
    ! [B_116,A_117] :
      ( r1_tarski(B_116,A_117)
      | ~ m1_subset_1(B_116,k1_zfmisc_1(A_117)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_1212])).

tff(c_1398,plain,(
    r1_tarski('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_56,c_1381])).

tff(c_212,plain,(
    ! [A_63] : k2_xboole_0(k1_xboole_0,A_63) = A_63 ),
    inference(resolution,[status(thm)],[c_16,c_174])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_225,plain,(
    ! [A_63] : k2_xboole_0(A_63,k1_xboole_0) = A_63 ),
    inference(superposition,[status(thm),theory(equality)],[c_212,c_2])).

tff(c_1882,plain,(
    ! [A_129,B_130,C_131] :
      ( r1_tarski(k4_xboole_0(A_129,B_130),C_131)
      | ~ r1_tarski(A_129,k2_xboole_0(B_130,C_131)) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_865,plain,(
    ! [B_97,A_98] :
      ( B_97 = A_98
      | ~ r1_tarski(B_97,A_98)
      | ~ r1_tarski(A_98,B_97) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_907,plain,(
    ! [A_12] :
      ( k1_xboole_0 = A_12
      | ~ r1_tarski(A_12,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_16,c_865])).

tff(c_1889,plain,(
    ! [A_129,B_130] :
      ( k4_xboole_0(A_129,B_130) = k1_xboole_0
      | ~ r1_tarski(A_129,k2_xboole_0(B_130,k1_xboole_0)) ) ),
    inference(resolution,[status(thm)],[c_1882,c_907])).

tff(c_4306,plain,(
    ! [A_175,B_176] :
      ( k4_xboole_0(A_175,B_176) = k1_xboole_0
      | ~ r1_tarski(A_175,B_176) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_225,c_1889])).

tff(c_4445,plain,(
    k4_xboole_0('#skF_4','#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1398,c_4306])).

tff(c_26,plain,(
    ! [A_24,B_25] : k4_xboole_0(A_24,k4_xboole_0(A_24,B_25)) = k3_xboole_0(A_24,B_25) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_4489,plain,(
    k4_xboole_0('#skF_4',k1_xboole_0) = k3_xboole_0('#skF_4','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_4445,c_26])).

tff(c_4513,plain,(
    k3_xboole_0('#skF_4','#skF_3') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2809,c_4489])).

tff(c_4,plain,(
    ! [B_4,A_3] : k3_xboole_0(B_4,A_3) = k3_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_1481,plain,(
    ! [A_118,B_119] :
      ( k4_xboole_0(A_118,B_119) = k3_subset_1(A_118,B_119)
      | ~ m1_subset_1(B_119,k1_zfmisc_1(A_118)) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_1498,plain,(
    k4_xboole_0('#skF_3','#skF_4') = k3_subset_1('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_56,c_1481])).

tff(c_1702,plain,(
    k4_xboole_0('#skF_3',k3_subset_1('#skF_3','#skF_4')) = k3_xboole_0('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1498,c_26])).

tff(c_1717,plain,(
    k4_xboole_0('#skF_3',k3_subset_1('#skF_3','#skF_4')) = k3_xboole_0('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_1702])).

tff(c_18637,plain,(
    k4_xboole_0('#skF_3',k3_subset_1('#skF_3','#skF_4')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4513,c_1717])).

tff(c_14,plain,(
    ! [A_10,B_11] :
      ( k2_xboole_0(A_10,B_11) = B_11
      | ~ r1_tarski(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_315,plain,(
    k2_xboole_0(k3_subset_1('#skF_3','#skF_5'),k3_subset_1('#skF_3','#skF_4')) = k3_subset_1('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_119,c_14])).

tff(c_54,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_1497,plain,(
    k4_xboole_0('#skF_3','#skF_5') = k3_subset_1('#skF_3','#skF_5') ),
    inference(resolution,[status(thm)],[c_54,c_1481])).

tff(c_28,plain,(
    ! [A_26,B_27] : r1_tarski(A_26,k2_xboole_0(A_26,B_27)) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_4610,plain,(
    ! [A_177,B_178,B_179] : r1_tarski(A_177,k2_xboole_0(B_178,k2_xboole_0(k4_xboole_0(A_177,B_178),B_179))) ),
    inference(resolution,[status(thm)],[c_28,c_1566])).

tff(c_6260,plain,(
    ! [B_197] : r1_tarski('#skF_3',k2_xboole_0('#skF_5',k2_xboole_0(k3_subset_1('#skF_3','#skF_5'),B_197))) ),
    inference(superposition,[status(thm),theory(equality)],[c_1497,c_4610])).

tff(c_6291,plain,(
    r1_tarski('#skF_3',k2_xboole_0('#skF_5',k3_subset_1('#skF_3','#skF_4'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_315,c_6260])).

tff(c_8162,plain,(
    ! [A_216,B_217,C_218] :
      ( k2_xboole_0(k4_xboole_0(A_216,B_217),C_218) = C_218
      | ~ r1_tarski(A_216,k2_xboole_0(B_217,C_218)) ) ),
    inference(resolution,[status(thm)],[c_1882,c_14])).

tff(c_37541,plain,(
    ! [A_581,A_582,B_583] :
      ( k2_xboole_0(k4_xboole_0(A_581,A_582),B_583) = B_583
      | ~ r1_tarski(A_581,k2_xboole_0(B_583,A_582)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_8162])).

tff(c_37810,plain,(
    k2_xboole_0(k4_xboole_0('#skF_3',k3_subset_1('#skF_3','#skF_4')),'#skF_5') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_6291,c_37541])).

tff(c_38149,plain,(
    k2_xboole_0('#skF_4','#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_18637,c_37810])).

tff(c_38363,plain,(
    r1_tarski('#skF_4','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_38149,c_28])).

tff(c_38395,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_253,c_38363])).

tff(c_38396,plain,(
    ~ r1_tarski(k3_subset_1('#skF_3','#skF_5'),k3_subset_1('#skF_3','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_38516,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_119,c_38396])).

tff(c_38517,plain,(
    r1_tarski('#skF_4','#skF_5') ),
    inference(splitRight,[status(thm)],[c_64])).

tff(c_38554,plain,(
    ~ r1_tarski(k3_subset_1('#skF_3','#skF_5'),k3_subset_1('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38517,c_58])).

tff(c_39997,plain,(
    ! [A_657,B_658] :
      ( k4_xboole_0(A_657,B_658) = k3_subset_1(A_657,B_658)
      | ~ m1_subset_1(B_658,k1_zfmisc_1(A_657)) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_40013,plain,(
    k4_xboole_0('#skF_3','#skF_5') = k3_subset_1('#skF_3','#skF_5') ),
    inference(resolution,[status(thm)],[c_54,c_39997])).

tff(c_40014,plain,(
    k4_xboole_0('#skF_3','#skF_4') = k3_subset_1('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_56,c_39997])).

tff(c_18,plain,(
    ! [C_15,B_14,A_13] :
      ( r1_tarski(k4_xboole_0(C_15,B_14),k4_xboole_0(C_15,A_13))
      | ~ r1_tarski(A_13,B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_43002,plain,(
    ! [B_719] :
      ( r1_tarski(k4_xboole_0('#skF_3',B_719),k3_subset_1('#skF_3','#skF_4'))
      | ~ r1_tarski('#skF_4',B_719) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_40014,c_18])).

tff(c_43027,plain,
    ( r1_tarski(k3_subset_1('#skF_3','#skF_5'),k3_subset_1('#skF_3','#skF_4'))
    | ~ r1_tarski('#skF_4','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_40013,c_43002])).

tff(c_43041,plain,(
    r1_tarski(k3_subset_1('#skF_3','#skF_5'),k3_subset_1('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38517,c_43027])).

tff(c_43043,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_38554,c_43041])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 10:03:21 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 15.00/7.17  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 15.00/7.18  
% 15.00/7.18  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 15.00/7.18  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 15.00/7.18  
% 15.00/7.18  %Foreground sorts:
% 15.00/7.18  
% 15.00/7.18  
% 15.00/7.18  %Background operators:
% 15.00/7.18  
% 15.00/7.18  
% 15.00/7.18  %Foreground operators:
% 15.00/7.18  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 15.00/7.18  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 15.00/7.18  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 15.00/7.18  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 15.00/7.18  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 15.00/7.18  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 15.00/7.18  tff('#skF_5', type, '#skF_5': $i).
% 15.00/7.18  tff('#skF_3', type, '#skF_3': $i).
% 15.00/7.18  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 15.00/7.18  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 15.00/7.18  tff('#skF_4', type, '#skF_4': $i).
% 15.00/7.18  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 15.00/7.18  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 15.00/7.18  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 15.00/7.18  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 15.00/7.18  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 15.00/7.18  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 15.00/7.18  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 15.00/7.18  
% 15.00/7.19  tff(f_100, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (r1_tarski(B, C) <=> r1_tarski(k3_subset_1(A, C), k3_subset_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_subset_1)).
% 15.00/7.19  tff(f_51, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 15.00/7.19  tff(f_45, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 15.00/7.19  tff(f_43, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 15.00/7.19  tff(f_35, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 15.00/7.19  tff(f_59, axiom, (![A, B, C]: (r1_tarski(k4_xboole_0(A, B), C) => r1_tarski(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_xboole_1)).
% 15.00/7.19  tff(f_90, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_subset_1)).
% 15.00/7.19  tff(f_83, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 15.00/7.19  tff(f_70, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 15.00/7.19  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 15.00/7.19  tff(f_55, axiom, (![A, B, C]: (r1_tarski(A, k2_xboole_0(B, C)) => r1_tarski(k4_xboole_0(A, B), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_xboole_1)).
% 15.00/7.19  tff(f_61, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 15.00/7.19  tff(f_29, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 15.00/7.19  tff(f_87, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_subset_1)).
% 15.00/7.19  tff(f_63, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 15.00/7.19  tff(f_49, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(k4_xboole_0(C, B), k4_xboole_0(C, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t34_xboole_1)).
% 15.00/7.19  tff(c_64, plain, (r1_tarski('#skF_4', '#skF_5') | r1_tarski(k3_subset_1('#skF_3', '#skF_5'), k3_subset_1('#skF_3', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_100])).
% 15.00/7.19  tff(c_119, plain, (r1_tarski(k3_subset_1('#skF_3', '#skF_5'), k3_subset_1('#skF_3', '#skF_4'))), inference(splitLeft, [status(thm)], [c_64])).
% 15.00/7.19  tff(c_58, plain, (~r1_tarski(k3_subset_1('#skF_3', '#skF_5'), k3_subset_1('#skF_3', '#skF_4')) | ~r1_tarski('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_100])).
% 15.00/7.19  tff(c_253, plain, (~r1_tarski('#skF_4', '#skF_5')), inference(splitLeft, [status(thm)], [c_58])).
% 15.00/7.19  tff(c_20, plain, (![A_16, B_17]: (r1_tarski(k4_xboole_0(A_16, B_17), A_16))), inference(cnfTransformation, [status(thm)], [f_51])).
% 15.00/7.19  tff(c_16, plain, (![A_12]: (r1_tarski(k1_xboole_0, A_12))), inference(cnfTransformation, [status(thm)], [f_45])).
% 15.00/7.19  tff(c_174, plain, (![A_60, B_61]: (k2_xboole_0(A_60, B_61)=B_61 | ~r1_tarski(A_60, B_61))), inference(cnfTransformation, [status(thm)], [f_43])).
% 15.00/7.19  tff(c_194, plain, (![A_12]: (k2_xboole_0(k1_xboole_0, A_12)=A_12)), inference(resolution, [status(thm)], [c_16, c_174])).
% 15.00/7.19  tff(c_10, plain, (![B_6]: (r1_tarski(B_6, B_6))), inference(cnfTransformation, [status(thm)], [f_35])).
% 15.00/7.19  tff(c_1566, plain, (![A_120, B_121, C_122]: (r1_tarski(A_120, k2_xboole_0(B_121, C_122)) | ~r1_tarski(k4_xboole_0(A_120, B_121), C_122))), inference(cnfTransformation, [status(thm)], [f_59])).
% 15.00/7.19  tff(c_2727, plain, (![A_154, B_155]: (r1_tarski(A_154, k2_xboole_0(B_155, k4_xboole_0(A_154, B_155))))), inference(resolution, [status(thm)], [c_10, c_1566])).
% 15.00/7.19  tff(c_2783, plain, (![A_156]: (r1_tarski(A_156, k4_xboole_0(A_156, k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_194, c_2727])).
% 15.00/7.19  tff(c_6, plain, (![B_6, A_5]: (B_6=A_5 | ~r1_tarski(B_6, A_5) | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_35])).
% 15.00/7.19  tff(c_2793, plain, (![A_156]: (k4_xboole_0(A_156, k1_xboole_0)=A_156 | ~r1_tarski(k4_xboole_0(A_156, k1_xboole_0), A_156))), inference(resolution, [status(thm)], [c_2783, c_6])).
% 15.00/7.19  tff(c_2809, plain, (![A_156]: (k4_xboole_0(A_156, k1_xboole_0)=A_156)), inference(demodulation, [status(thm), theory('equality')], [c_20, c_2793])).
% 15.00/7.19  tff(c_56, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_100])).
% 15.00/7.19  tff(c_52, plain, (![A_37]: (~v1_xboole_0(k1_zfmisc_1(A_37)))), inference(cnfTransformation, [status(thm)], [f_90])).
% 15.00/7.19  tff(c_1205, plain, (![B_108, A_109]: (r2_hidden(B_108, A_109) | ~m1_subset_1(B_108, A_109) | v1_xboole_0(A_109))), inference(cnfTransformation, [status(thm)], [f_83])).
% 15.00/7.19  tff(c_30, plain, (![C_32, A_28]: (r1_tarski(C_32, A_28) | ~r2_hidden(C_32, k1_zfmisc_1(A_28)))), inference(cnfTransformation, [status(thm)], [f_70])).
% 15.00/7.19  tff(c_1212, plain, (![B_108, A_28]: (r1_tarski(B_108, A_28) | ~m1_subset_1(B_108, k1_zfmisc_1(A_28)) | v1_xboole_0(k1_zfmisc_1(A_28)))), inference(resolution, [status(thm)], [c_1205, c_30])).
% 15.00/7.19  tff(c_1381, plain, (![B_116, A_117]: (r1_tarski(B_116, A_117) | ~m1_subset_1(B_116, k1_zfmisc_1(A_117)))), inference(negUnitSimplification, [status(thm)], [c_52, c_1212])).
% 15.00/7.19  tff(c_1398, plain, (r1_tarski('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_56, c_1381])).
% 15.00/7.19  tff(c_212, plain, (![A_63]: (k2_xboole_0(k1_xboole_0, A_63)=A_63)), inference(resolution, [status(thm)], [c_16, c_174])).
% 15.00/7.19  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 15.00/7.19  tff(c_225, plain, (![A_63]: (k2_xboole_0(A_63, k1_xboole_0)=A_63)), inference(superposition, [status(thm), theory('equality')], [c_212, c_2])).
% 15.00/7.19  tff(c_1882, plain, (![A_129, B_130, C_131]: (r1_tarski(k4_xboole_0(A_129, B_130), C_131) | ~r1_tarski(A_129, k2_xboole_0(B_130, C_131)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 15.00/7.19  tff(c_865, plain, (![B_97, A_98]: (B_97=A_98 | ~r1_tarski(B_97, A_98) | ~r1_tarski(A_98, B_97))), inference(cnfTransformation, [status(thm)], [f_35])).
% 15.00/7.19  tff(c_907, plain, (![A_12]: (k1_xboole_0=A_12 | ~r1_tarski(A_12, k1_xboole_0))), inference(resolution, [status(thm)], [c_16, c_865])).
% 15.00/7.19  tff(c_1889, plain, (![A_129, B_130]: (k4_xboole_0(A_129, B_130)=k1_xboole_0 | ~r1_tarski(A_129, k2_xboole_0(B_130, k1_xboole_0)))), inference(resolution, [status(thm)], [c_1882, c_907])).
% 15.00/7.19  tff(c_4306, plain, (![A_175, B_176]: (k4_xboole_0(A_175, B_176)=k1_xboole_0 | ~r1_tarski(A_175, B_176))), inference(demodulation, [status(thm), theory('equality')], [c_225, c_1889])).
% 15.00/7.19  tff(c_4445, plain, (k4_xboole_0('#skF_4', '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_1398, c_4306])).
% 15.00/7.19  tff(c_26, plain, (![A_24, B_25]: (k4_xboole_0(A_24, k4_xboole_0(A_24, B_25))=k3_xboole_0(A_24, B_25))), inference(cnfTransformation, [status(thm)], [f_61])).
% 15.00/7.19  tff(c_4489, plain, (k4_xboole_0('#skF_4', k1_xboole_0)=k3_xboole_0('#skF_4', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_4445, c_26])).
% 15.00/7.19  tff(c_4513, plain, (k3_xboole_0('#skF_4', '#skF_3')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_2809, c_4489])).
% 15.00/7.19  tff(c_4, plain, (![B_4, A_3]: (k3_xboole_0(B_4, A_3)=k3_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 15.00/7.19  tff(c_1481, plain, (![A_118, B_119]: (k4_xboole_0(A_118, B_119)=k3_subset_1(A_118, B_119) | ~m1_subset_1(B_119, k1_zfmisc_1(A_118)))), inference(cnfTransformation, [status(thm)], [f_87])).
% 15.00/7.19  tff(c_1498, plain, (k4_xboole_0('#skF_3', '#skF_4')=k3_subset_1('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_56, c_1481])).
% 15.00/7.19  tff(c_1702, plain, (k4_xboole_0('#skF_3', k3_subset_1('#skF_3', '#skF_4'))=k3_xboole_0('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1498, c_26])).
% 15.00/7.19  tff(c_1717, plain, (k4_xboole_0('#skF_3', k3_subset_1('#skF_3', '#skF_4'))=k3_xboole_0('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_1702])).
% 15.00/7.19  tff(c_18637, plain, (k4_xboole_0('#skF_3', k3_subset_1('#skF_3', '#skF_4'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_4513, c_1717])).
% 15.00/7.19  tff(c_14, plain, (![A_10, B_11]: (k2_xboole_0(A_10, B_11)=B_11 | ~r1_tarski(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_43])).
% 15.00/7.19  tff(c_315, plain, (k2_xboole_0(k3_subset_1('#skF_3', '#skF_5'), k3_subset_1('#skF_3', '#skF_4'))=k3_subset_1('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_119, c_14])).
% 15.00/7.19  tff(c_54, plain, (m1_subset_1('#skF_5', k1_zfmisc_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_100])).
% 15.00/7.19  tff(c_1497, plain, (k4_xboole_0('#skF_3', '#skF_5')=k3_subset_1('#skF_3', '#skF_5')), inference(resolution, [status(thm)], [c_54, c_1481])).
% 15.00/7.19  tff(c_28, plain, (![A_26, B_27]: (r1_tarski(A_26, k2_xboole_0(A_26, B_27)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 15.00/7.19  tff(c_4610, plain, (![A_177, B_178, B_179]: (r1_tarski(A_177, k2_xboole_0(B_178, k2_xboole_0(k4_xboole_0(A_177, B_178), B_179))))), inference(resolution, [status(thm)], [c_28, c_1566])).
% 15.00/7.19  tff(c_6260, plain, (![B_197]: (r1_tarski('#skF_3', k2_xboole_0('#skF_5', k2_xboole_0(k3_subset_1('#skF_3', '#skF_5'), B_197))))), inference(superposition, [status(thm), theory('equality')], [c_1497, c_4610])).
% 15.00/7.19  tff(c_6291, plain, (r1_tarski('#skF_3', k2_xboole_0('#skF_5', k3_subset_1('#skF_3', '#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_315, c_6260])).
% 15.00/7.19  tff(c_8162, plain, (![A_216, B_217, C_218]: (k2_xboole_0(k4_xboole_0(A_216, B_217), C_218)=C_218 | ~r1_tarski(A_216, k2_xboole_0(B_217, C_218)))), inference(resolution, [status(thm)], [c_1882, c_14])).
% 15.00/7.19  tff(c_37541, plain, (![A_581, A_582, B_583]: (k2_xboole_0(k4_xboole_0(A_581, A_582), B_583)=B_583 | ~r1_tarski(A_581, k2_xboole_0(B_583, A_582)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_8162])).
% 15.00/7.19  tff(c_37810, plain, (k2_xboole_0(k4_xboole_0('#skF_3', k3_subset_1('#skF_3', '#skF_4')), '#skF_5')='#skF_5'), inference(resolution, [status(thm)], [c_6291, c_37541])).
% 15.00/7.19  tff(c_38149, plain, (k2_xboole_0('#skF_4', '#skF_5')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_18637, c_37810])).
% 15.00/7.19  tff(c_38363, plain, (r1_tarski('#skF_4', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_38149, c_28])).
% 15.00/7.19  tff(c_38395, plain, $false, inference(negUnitSimplification, [status(thm)], [c_253, c_38363])).
% 15.00/7.19  tff(c_38396, plain, (~r1_tarski(k3_subset_1('#skF_3', '#skF_5'), k3_subset_1('#skF_3', '#skF_4'))), inference(splitRight, [status(thm)], [c_58])).
% 15.00/7.19  tff(c_38516, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_119, c_38396])).
% 15.00/7.19  tff(c_38517, plain, (r1_tarski('#skF_4', '#skF_5')), inference(splitRight, [status(thm)], [c_64])).
% 15.00/7.19  tff(c_38554, plain, (~r1_tarski(k3_subset_1('#skF_3', '#skF_5'), k3_subset_1('#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_38517, c_58])).
% 15.00/7.19  tff(c_39997, plain, (![A_657, B_658]: (k4_xboole_0(A_657, B_658)=k3_subset_1(A_657, B_658) | ~m1_subset_1(B_658, k1_zfmisc_1(A_657)))), inference(cnfTransformation, [status(thm)], [f_87])).
% 15.00/7.19  tff(c_40013, plain, (k4_xboole_0('#skF_3', '#skF_5')=k3_subset_1('#skF_3', '#skF_5')), inference(resolution, [status(thm)], [c_54, c_39997])).
% 15.00/7.19  tff(c_40014, plain, (k4_xboole_0('#skF_3', '#skF_4')=k3_subset_1('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_56, c_39997])).
% 15.00/7.19  tff(c_18, plain, (![C_15, B_14, A_13]: (r1_tarski(k4_xboole_0(C_15, B_14), k4_xboole_0(C_15, A_13)) | ~r1_tarski(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_49])).
% 15.00/7.19  tff(c_43002, plain, (![B_719]: (r1_tarski(k4_xboole_0('#skF_3', B_719), k3_subset_1('#skF_3', '#skF_4')) | ~r1_tarski('#skF_4', B_719))), inference(superposition, [status(thm), theory('equality')], [c_40014, c_18])).
% 15.00/7.19  tff(c_43027, plain, (r1_tarski(k3_subset_1('#skF_3', '#skF_5'), k3_subset_1('#skF_3', '#skF_4')) | ~r1_tarski('#skF_4', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_40013, c_43002])).
% 15.00/7.19  tff(c_43041, plain, (r1_tarski(k3_subset_1('#skF_3', '#skF_5'), k3_subset_1('#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_38517, c_43027])).
% 15.00/7.19  tff(c_43043, plain, $false, inference(negUnitSimplification, [status(thm)], [c_38554, c_43041])).
% 15.00/7.19  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 15.00/7.19  
% 15.00/7.19  Inference rules
% 15.00/7.19  ----------------------
% 15.00/7.19  #Ref     : 0
% 15.00/7.19  #Sup     : 10609
% 15.00/7.19  #Fact    : 0
% 15.00/7.19  #Define  : 0
% 15.00/7.19  #Split   : 13
% 15.00/7.19  #Chain   : 0
% 15.00/7.19  #Close   : 0
% 15.00/7.19  
% 15.00/7.19  Ordering : KBO
% 15.00/7.19  
% 15.00/7.19  Simplification rules
% 15.00/7.19  ----------------------
% 15.00/7.19  #Subsume      : 1062
% 15.00/7.19  #Demod        : 8542
% 15.00/7.19  #Tautology    : 6159
% 15.00/7.19  #SimpNegUnit  : 103
% 15.00/7.19  #BackRed      : 4
% 15.00/7.19  
% 15.00/7.19  #Partial instantiations: 0
% 15.00/7.19  #Strategies tried      : 1
% 15.00/7.19  
% 15.00/7.19  Timing (in seconds)
% 15.00/7.19  ----------------------
% 15.00/7.20  Preprocessing        : 0.32
% 15.00/7.20  Parsing              : 0.17
% 15.00/7.20  CNF conversion       : 0.02
% 15.00/7.20  Main loop            : 6.10
% 15.00/7.20  Inferencing          : 0.97
% 15.00/7.20  Reduction            : 3.40
% 15.00/7.20  Demodulation         : 2.91
% 15.00/7.20  BG Simplification    : 0.10
% 15.00/7.20  Subsumption          : 1.28
% 15.00/7.20  Abstraction          : 0.14
% 15.00/7.20  MUC search           : 0.00
% 15.00/7.20  Cooper               : 0.00
% 15.00/7.20  Total                : 6.45
% 15.00/7.20  Index Insertion      : 0.00
% 15.00/7.20  Index Deletion       : 0.00
% 15.00/7.20  Index Matching       : 0.00
% 15.00/7.20  BG Taut test         : 0.00
%------------------------------------------------------------------------------
