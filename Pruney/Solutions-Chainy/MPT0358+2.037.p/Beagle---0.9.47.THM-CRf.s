%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:56:05 EST 2020

% Result     : Theorem 2.88s
% Output     : CNFRefutation 3.16s
% Verified   : 
% Statistics : Number of formulae       :   99 ( 211 expanded)
%              Number of leaves         :   32 (  82 expanded)
%              Depth                    :   12
%              Number of atoms          :  148 ( 384 expanded)
%              Number of equality atoms :   48 ( 120 expanded)
%              Maximal formula depth    :    6 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > k1_subset_1 > k1_xboole_0 > #skF_3 > #skF_4 > #skF_2 > #skF_1

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

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

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

tff(k1_subset_1,type,(
    k1_subset_1: $i > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_95,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => ( r1_tarski(B,k3_subset_1(A,B))
        <=> B = k1_subset_1(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_subset_1)).

tff(f_84,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_71,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_58,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_73,axiom,(
    ! [A] : k1_subset_1(A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_subset_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_77,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_88,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,k3_subset_1(A,B)) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

tff(f_81,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k3_subset_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).

tff(f_51,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ~ ( r1_tarski(B,A)
          & r1_xboole_0(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_xboole_1)).

tff(f_29,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(c_50,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_46,plain,(
    ! [A_24] : ~ v1_xboole_0(k1_zfmisc_1(A_24)) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_154,plain,(
    ! [B_55,A_56] :
      ( r2_hidden(B_55,A_56)
      | ~ m1_subset_1(B_55,A_56)
      | v1_xboole_0(A_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_20,plain,(
    ! [C_16,A_12] :
      ( r1_tarski(C_16,A_12)
      | ~ r2_hidden(C_16,k1_zfmisc_1(A_12)) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_161,plain,(
    ! [B_55,A_12] :
      ( r1_tarski(B_55,A_12)
      | ~ m1_subset_1(B_55,k1_zfmisc_1(A_12))
      | v1_xboole_0(k1_zfmisc_1(A_12)) ) ),
    inference(resolution,[status(thm)],[c_154,c_20])).

tff(c_166,plain,(
    ! [B_57,A_58] :
      ( r1_tarski(B_57,A_58)
      | ~ m1_subset_1(B_57,k1_zfmisc_1(A_58)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_161])).

tff(c_179,plain,(
    r1_tarski('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_50,c_166])).

tff(c_40,plain,(
    ! [A_19] : k1_subset_1(A_19) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_58,plain,
    ( r1_tarski('#skF_4',k3_subset_1('#skF_3','#skF_4'))
    | k1_subset_1('#skF_3') = '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_59,plain,
    ( r1_tarski('#skF_4',k3_subset_1('#skF_3','#skF_4'))
    | k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_58])).

tff(c_73,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_59])).

tff(c_12,plain,(
    ! [A_4,B_5] :
      ( k4_xboole_0(A_4,B_5) = k1_xboole_0
      | ~ r1_tarski(A_4,B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_95,plain,(
    ! [A_4,B_5] :
      ( k4_xboole_0(A_4,B_5) = '#skF_4'
      | ~ r1_tarski(A_4,B_5) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_73,c_12])).

tff(c_192,plain,(
    k4_xboole_0('#skF_4','#skF_3') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_179,c_95])).

tff(c_8,plain,(
    ! [B_3] : r1_tarski(B_3,B_3) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_96,plain,(
    ! [A_37,B_38] :
      ( k4_xboole_0(A_37,B_38) = '#skF_4'
      | ~ r1_tarski(A_37,B_38) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_73,c_12])).

tff(c_100,plain,(
    ! [B_3] : k4_xboole_0(B_3,B_3) = '#skF_4' ),
    inference(resolution,[status(thm)],[c_8,c_96])).

tff(c_22,plain,(
    ! [C_16,A_12] :
      ( r2_hidden(C_16,k1_zfmisc_1(A_12))
      | ~ r1_tarski(C_16,A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_142,plain,(
    ! [B_51,A_52] :
      ( m1_subset_1(B_51,A_52)
      | ~ r2_hidden(B_51,A_52)
      | v1_xboole_0(A_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_145,plain,(
    ! [C_16,A_12] :
      ( m1_subset_1(C_16,k1_zfmisc_1(A_12))
      | v1_xboole_0(k1_zfmisc_1(A_12))
      | ~ r1_tarski(C_16,A_12) ) ),
    inference(resolution,[status(thm)],[c_22,c_142])).

tff(c_148,plain,(
    ! [C_16,A_12] :
      ( m1_subset_1(C_16,k1_zfmisc_1(A_12))
      | ~ r1_tarski(C_16,A_12) ) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_145])).

tff(c_358,plain,(
    ! [A_77,B_78] :
      ( k4_xboole_0(A_77,B_78) = k3_subset_1(A_77,B_78)
      | ~ m1_subset_1(B_78,k1_zfmisc_1(A_77)) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_404,plain,(
    ! [A_81,C_82] :
      ( k4_xboole_0(A_81,C_82) = k3_subset_1(A_81,C_82)
      | ~ r1_tarski(C_82,A_81) ) ),
    inference(resolution,[status(thm)],[c_148,c_358])).

tff(c_416,plain,(
    ! [B_3] : k4_xboole_0(B_3,B_3) = k3_subset_1(B_3,B_3) ),
    inference(resolution,[status(thm)],[c_8,c_404])).

tff(c_423,plain,(
    ! [B_83] : k3_subset_1(B_83,B_83) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_416])).

tff(c_281,plain,(
    ! [A_71,B_72] :
      ( k3_subset_1(A_71,k3_subset_1(A_71,B_72)) = B_72
      | ~ m1_subset_1(B_72,k1_zfmisc_1(A_71)) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_292,plain,(
    ! [A_12,C_16] :
      ( k3_subset_1(A_12,k3_subset_1(A_12,C_16)) = C_16
      | ~ r1_tarski(C_16,A_12) ) ),
    inference(resolution,[status(thm)],[c_148,c_281])).

tff(c_428,plain,(
    ! [B_83] :
      ( k3_subset_1(B_83,'#skF_4') = B_83
      | ~ r1_tarski(B_83,B_83) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_423,c_292])).

tff(c_439,plain,(
    ! [B_83] : k3_subset_1(B_83,'#skF_4') = B_83 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_428])).

tff(c_10,plain,(
    ! [A_4,B_5] :
      ( r1_tarski(A_4,B_5)
      | k4_xboole_0(A_4,B_5) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_119,plain,(
    ! [A_45,B_46] :
      ( r1_tarski(A_45,B_46)
      | k4_xboole_0(A_45,B_46) != '#skF_4' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_73,c_10])).

tff(c_52,plain,
    ( k1_subset_1('#skF_3') != '#skF_4'
    | ~ r1_tarski('#skF_4',k3_subset_1('#skF_3','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_60,plain,
    ( k1_xboole_0 != '#skF_4'
    | ~ r1_tarski('#skF_4',k3_subset_1('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_52])).

tff(c_88,plain,(
    ~ r1_tarski('#skF_4',k3_subset_1('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_73,c_60])).

tff(c_127,plain,(
    k4_xboole_0('#skF_4',k3_subset_1('#skF_3','#skF_4')) != '#skF_4' ),
    inference(resolution,[status(thm)],[c_119,c_88])).

tff(c_457,plain,(
    k4_xboole_0('#skF_4','#skF_3') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_439,c_127])).

tff(c_462,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_192,c_457])).

tff(c_464,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_59])).

tff(c_463,plain,(
    r1_tarski('#skF_4',k3_subset_1('#skF_3','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_59])).

tff(c_467,plain,(
    ! [A_86,B_87] :
      ( k4_xboole_0(A_86,B_87) = k1_xboole_0
      | ~ r1_tarski(A_86,B_87) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_474,plain,(
    k4_xboole_0('#skF_4',k3_subset_1('#skF_3','#skF_4')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_463,c_467])).

tff(c_696,plain,(
    ! [A_125,B_126] :
      ( k3_subset_1(A_125,k3_subset_1(A_125,B_126)) = B_126
      | ~ m1_subset_1(B_126,k1_zfmisc_1(A_125)) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_709,plain,(
    k3_subset_1('#skF_3',k3_subset_1('#skF_3','#skF_4')) = '#skF_4' ),
    inference(resolution,[status(thm)],[c_50,c_696])).

tff(c_657,plain,(
    ! [A_119,B_120] :
      ( m1_subset_1(k3_subset_1(A_119,B_120),k1_zfmisc_1(A_119))
      | ~ m1_subset_1(B_120,k1_zfmisc_1(A_119)) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_541,plain,(
    ! [B_106,A_107] :
      ( r2_hidden(B_106,A_107)
      | ~ m1_subset_1(B_106,A_107)
      | v1_xboole_0(A_107) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_548,plain,(
    ! [B_106,A_12] :
      ( r1_tarski(B_106,A_12)
      | ~ m1_subset_1(B_106,k1_zfmisc_1(A_12))
      | v1_xboole_0(k1_zfmisc_1(A_12)) ) ),
    inference(resolution,[status(thm)],[c_541,c_20])).

tff(c_552,plain,(
    ! [B_106,A_12] :
      ( r1_tarski(B_106,A_12)
      | ~ m1_subset_1(B_106,k1_zfmisc_1(A_12)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_548])).

tff(c_684,plain,(
    ! [A_123,B_124] :
      ( r1_tarski(k3_subset_1(A_123,B_124),A_123)
      | ~ m1_subset_1(B_124,k1_zfmisc_1(A_123)) ) ),
    inference(resolution,[status(thm)],[c_657,c_552])).

tff(c_1492,plain,(
    ! [A_168,B_169] :
      ( k4_xboole_0(k3_subset_1(A_168,B_169),A_168) = k1_xboole_0
      | ~ m1_subset_1(B_169,k1_zfmisc_1(A_168)) ) ),
    inference(resolution,[status(thm)],[c_684,c_12])).

tff(c_1513,plain,(
    k4_xboole_0(k3_subset_1('#skF_3','#skF_4'),'#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_50,c_1492])).

tff(c_529,plain,(
    ! [B_102,A_103] :
      ( m1_subset_1(B_102,A_103)
      | ~ r2_hidden(B_102,A_103)
      | v1_xboole_0(A_103) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_532,plain,(
    ! [C_16,A_12] :
      ( m1_subset_1(C_16,k1_zfmisc_1(A_12))
      | v1_xboole_0(k1_zfmisc_1(A_12))
      | ~ r1_tarski(C_16,A_12) ) ),
    inference(resolution,[status(thm)],[c_22,c_529])).

tff(c_535,plain,(
    ! [C_16,A_12] :
      ( m1_subset_1(C_16,k1_zfmisc_1(A_12))
      | ~ r1_tarski(C_16,A_12) ) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_532])).

tff(c_761,plain,(
    ! [A_129,B_130] :
      ( k4_xboole_0(A_129,B_130) = k3_subset_1(A_129,B_130)
      | ~ m1_subset_1(B_130,k1_zfmisc_1(A_129)) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_816,plain,(
    ! [A_133,C_134] :
      ( k4_xboole_0(A_133,C_134) = k3_subset_1(A_133,C_134)
      | ~ r1_tarski(C_134,A_133) ) ),
    inference(resolution,[status(thm)],[c_535,c_761])).

tff(c_839,plain,(
    ! [B_5,A_4] :
      ( k4_xboole_0(B_5,A_4) = k3_subset_1(B_5,A_4)
      | k4_xboole_0(A_4,B_5) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_10,c_816])).

tff(c_1516,plain,(
    k4_xboole_0('#skF_3',k3_subset_1('#skF_3','#skF_4')) = k3_subset_1('#skF_3',k3_subset_1('#skF_3','#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1513,c_839])).

tff(c_1530,plain,(
    k4_xboole_0('#skF_3',k3_subset_1('#skF_3','#skF_4')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_709,c_1516])).

tff(c_18,plain,(
    ! [A_10,B_11] : r1_xboole_0(k4_xboole_0(A_10,B_11),B_11) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_601,plain,(
    ! [B_112,A_113] :
      ( ~ r1_xboole_0(B_112,A_113)
      | ~ r1_tarski(B_112,A_113)
      | v1_xboole_0(B_112) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_666,plain,(
    ! [A_121,B_122] :
      ( ~ r1_tarski(k4_xboole_0(A_121,B_122),B_122)
      | v1_xboole_0(k4_xboole_0(A_121,B_122)) ) ),
    inference(resolution,[status(thm)],[c_18,c_601])).

tff(c_681,plain,(
    ! [A_121,B_5] :
      ( v1_xboole_0(k4_xboole_0(A_121,B_5))
      | k4_xboole_0(k4_xboole_0(A_121,B_5),B_5) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_10,c_666])).

tff(c_1542,plain,
    ( v1_xboole_0(k4_xboole_0('#skF_3',k3_subset_1('#skF_3','#skF_4')))
    | k4_xboole_0('#skF_4',k3_subset_1('#skF_3','#skF_4')) != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_1530,c_681])).

tff(c_1555,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_474,c_1530,c_1542])).

tff(c_2,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_1564,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_1555,c_2])).

tff(c_1568,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_464,c_1564])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:16:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.88/1.63  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.16/1.64  
% 3.16/1.64  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.16/1.64  %$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > k1_subset_1 > k1_xboole_0 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 3.16/1.64  
% 3.16/1.64  %Foreground sorts:
% 3.16/1.64  
% 3.16/1.64  
% 3.16/1.64  %Background operators:
% 3.16/1.64  
% 3.16/1.64  
% 3.16/1.64  %Foreground operators:
% 3.16/1.64  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.16/1.64  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.16/1.64  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.16/1.64  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.16/1.64  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.16/1.64  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.16/1.64  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 3.16/1.64  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.16/1.64  tff('#skF_3', type, '#skF_3': $i).
% 3.16/1.64  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.16/1.64  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.16/1.64  tff('#skF_4', type, '#skF_4': $i).
% 3.16/1.64  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.16/1.64  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.16/1.64  tff(k1_subset_1, type, k1_subset_1: $i > $i).
% 3.16/1.64  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.16/1.64  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.16/1.64  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.16/1.64  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.16/1.64  
% 3.16/1.66  tff(f_95, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (r1_tarski(B, k3_subset_1(A, B)) <=> (B = k1_subset_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_subset_1)).
% 3.16/1.66  tff(f_84, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_subset_1)).
% 3.16/1.66  tff(f_71, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 3.16/1.66  tff(f_58, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 3.16/1.66  tff(f_73, axiom, (![A]: (k1_subset_1(A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_subset_1)).
% 3.16/1.66  tff(f_39, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 3.16/1.66  tff(f_35, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.16/1.66  tff(f_77, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_subset_1)).
% 3.16/1.66  tff(f_88, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, k3_subset_1(A, B)) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 3.16/1.66  tff(f_81, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k3_subset_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 3.16/1.66  tff(f_51, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_xboole_1)).
% 3.16/1.66  tff(f_49, axiom, (![A, B]: (~v1_xboole_0(B) => ~(r1_tarski(B, A) & r1_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_xboole_1)).
% 3.16/1.66  tff(f_29, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 3.16/1.66  tff(c_50, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_95])).
% 3.16/1.66  tff(c_46, plain, (![A_24]: (~v1_xboole_0(k1_zfmisc_1(A_24)))), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.16/1.66  tff(c_154, plain, (![B_55, A_56]: (r2_hidden(B_55, A_56) | ~m1_subset_1(B_55, A_56) | v1_xboole_0(A_56))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.16/1.66  tff(c_20, plain, (![C_16, A_12]: (r1_tarski(C_16, A_12) | ~r2_hidden(C_16, k1_zfmisc_1(A_12)))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.16/1.66  tff(c_161, plain, (![B_55, A_12]: (r1_tarski(B_55, A_12) | ~m1_subset_1(B_55, k1_zfmisc_1(A_12)) | v1_xboole_0(k1_zfmisc_1(A_12)))), inference(resolution, [status(thm)], [c_154, c_20])).
% 3.16/1.66  tff(c_166, plain, (![B_57, A_58]: (r1_tarski(B_57, A_58) | ~m1_subset_1(B_57, k1_zfmisc_1(A_58)))), inference(negUnitSimplification, [status(thm)], [c_46, c_161])).
% 3.16/1.66  tff(c_179, plain, (r1_tarski('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_50, c_166])).
% 3.16/1.66  tff(c_40, plain, (![A_19]: (k1_subset_1(A_19)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.16/1.66  tff(c_58, plain, (r1_tarski('#skF_4', k3_subset_1('#skF_3', '#skF_4')) | k1_subset_1('#skF_3')='#skF_4'), inference(cnfTransformation, [status(thm)], [f_95])).
% 3.16/1.66  tff(c_59, plain, (r1_tarski('#skF_4', k3_subset_1('#skF_3', '#skF_4')) | k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_40, c_58])).
% 3.16/1.66  tff(c_73, plain, (k1_xboole_0='#skF_4'), inference(splitLeft, [status(thm)], [c_59])).
% 3.16/1.66  tff(c_12, plain, (![A_4, B_5]: (k4_xboole_0(A_4, B_5)=k1_xboole_0 | ~r1_tarski(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.16/1.66  tff(c_95, plain, (![A_4, B_5]: (k4_xboole_0(A_4, B_5)='#skF_4' | ~r1_tarski(A_4, B_5))), inference(demodulation, [status(thm), theory('equality')], [c_73, c_12])).
% 3.16/1.66  tff(c_192, plain, (k4_xboole_0('#skF_4', '#skF_3')='#skF_4'), inference(resolution, [status(thm)], [c_179, c_95])).
% 3.16/1.66  tff(c_8, plain, (![B_3]: (r1_tarski(B_3, B_3))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.16/1.66  tff(c_96, plain, (![A_37, B_38]: (k4_xboole_0(A_37, B_38)='#skF_4' | ~r1_tarski(A_37, B_38))), inference(demodulation, [status(thm), theory('equality')], [c_73, c_12])).
% 3.16/1.66  tff(c_100, plain, (![B_3]: (k4_xboole_0(B_3, B_3)='#skF_4')), inference(resolution, [status(thm)], [c_8, c_96])).
% 3.16/1.66  tff(c_22, plain, (![C_16, A_12]: (r2_hidden(C_16, k1_zfmisc_1(A_12)) | ~r1_tarski(C_16, A_12))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.16/1.66  tff(c_142, plain, (![B_51, A_52]: (m1_subset_1(B_51, A_52) | ~r2_hidden(B_51, A_52) | v1_xboole_0(A_52))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.16/1.66  tff(c_145, plain, (![C_16, A_12]: (m1_subset_1(C_16, k1_zfmisc_1(A_12)) | v1_xboole_0(k1_zfmisc_1(A_12)) | ~r1_tarski(C_16, A_12))), inference(resolution, [status(thm)], [c_22, c_142])).
% 3.16/1.66  tff(c_148, plain, (![C_16, A_12]: (m1_subset_1(C_16, k1_zfmisc_1(A_12)) | ~r1_tarski(C_16, A_12))), inference(negUnitSimplification, [status(thm)], [c_46, c_145])).
% 3.16/1.66  tff(c_358, plain, (![A_77, B_78]: (k4_xboole_0(A_77, B_78)=k3_subset_1(A_77, B_78) | ~m1_subset_1(B_78, k1_zfmisc_1(A_77)))), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.16/1.66  tff(c_404, plain, (![A_81, C_82]: (k4_xboole_0(A_81, C_82)=k3_subset_1(A_81, C_82) | ~r1_tarski(C_82, A_81))), inference(resolution, [status(thm)], [c_148, c_358])).
% 3.16/1.66  tff(c_416, plain, (![B_3]: (k4_xboole_0(B_3, B_3)=k3_subset_1(B_3, B_3))), inference(resolution, [status(thm)], [c_8, c_404])).
% 3.16/1.66  tff(c_423, plain, (![B_83]: (k3_subset_1(B_83, B_83)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_100, c_416])).
% 3.16/1.66  tff(c_281, plain, (![A_71, B_72]: (k3_subset_1(A_71, k3_subset_1(A_71, B_72))=B_72 | ~m1_subset_1(B_72, k1_zfmisc_1(A_71)))), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.16/1.66  tff(c_292, plain, (![A_12, C_16]: (k3_subset_1(A_12, k3_subset_1(A_12, C_16))=C_16 | ~r1_tarski(C_16, A_12))), inference(resolution, [status(thm)], [c_148, c_281])).
% 3.16/1.66  tff(c_428, plain, (![B_83]: (k3_subset_1(B_83, '#skF_4')=B_83 | ~r1_tarski(B_83, B_83))), inference(superposition, [status(thm), theory('equality')], [c_423, c_292])).
% 3.16/1.66  tff(c_439, plain, (![B_83]: (k3_subset_1(B_83, '#skF_4')=B_83)), inference(demodulation, [status(thm), theory('equality')], [c_8, c_428])).
% 3.16/1.66  tff(c_10, plain, (![A_4, B_5]: (r1_tarski(A_4, B_5) | k4_xboole_0(A_4, B_5)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.16/1.66  tff(c_119, plain, (![A_45, B_46]: (r1_tarski(A_45, B_46) | k4_xboole_0(A_45, B_46)!='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_73, c_10])).
% 3.16/1.66  tff(c_52, plain, (k1_subset_1('#skF_3')!='#skF_4' | ~r1_tarski('#skF_4', k3_subset_1('#skF_3', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_95])).
% 3.16/1.66  tff(c_60, plain, (k1_xboole_0!='#skF_4' | ~r1_tarski('#skF_4', k3_subset_1('#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_52])).
% 3.16/1.66  tff(c_88, plain, (~r1_tarski('#skF_4', k3_subset_1('#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_73, c_60])).
% 3.16/1.66  tff(c_127, plain, (k4_xboole_0('#skF_4', k3_subset_1('#skF_3', '#skF_4'))!='#skF_4'), inference(resolution, [status(thm)], [c_119, c_88])).
% 3.16/1.66  tff(c_457, plain, (k4_xboole_0('#skF_4', '#skF_3')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_439, c_127])).
% 3.16/1.66  tff(c_462, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_192, c_457])).
% 3.16/1.66  tff(c_464, plain, (k1_xboole_0!='#skF_4'), inference(splitRight, [status(thm)], [c_59])).
% 3.16/1.66  tff(c_463, plain, (r1_tarski('#skF_4', k3_subset_1('#skF_3', '#skF_4'))), inference(splitRight, [status(thm)], [c_59])).
% 3.16/1.66  tff(c_467, plain, (![A_86, B_87]: (k4_xboole_0(A_86, B_87)=k1_xboole_0 | ~r1_tarski(A_86, B_87))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.16/1.66  tff(c_474, plain, (k4_xboole_0('#skF_4', k3_subset_1('#skF_3', '#skF_4'))=k1_xboole_0), inference(resolution, [status(thm)], [c_463, c_467])).
% 3.16/1.66  tff(c_696, plain, (![A_125, B_126]: (k3_subset_1(A_125, k3_subset_1(A_125, B_126))=B_126 | ~m1_subset_1(B_126, k1_zfmisc_1(A_125)))), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.16/1.66  tff(c_709, plain, (k3_subset_1('#skF_3', k3_subset_1('#skF_3', '#skF_4'))='#skF_4'), inference(resolution, [status(thm)], [c_50, c_696])).
% 3.16/1.66  tff(c_657, plain, (![A_119, B_120]: (m1_subset_1(k3_subset_1(A_119, B_120), k1_zfmisc_1(A_119)) | ~m1_subset_1(B_120, k1_zfmisc_1(A_119)))), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.16/1.66  tff(c_541, plain, (![B_106, A_107]: (r2_hidden(B_106, A_107) | ~m1_subset_1(B_106, A_107) | v1_xboole_0(A_107))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.16/1.66  tff(c_548, plain, (![B_106, A_12]: (r1_tarski(B_106, A_12) | ~m1_subset_1(B_106, k1_zfmisc_1(A_12)) | v1_xboole_0(k1_zfmisc_1(A_12)))), inference(resolution, [status(thm)], [c_541, c_20])).
% 3.16/1.66  tff(c_552, plain, (![B_106, A_12]: (r1_tarski(B_106, A_12) | ~m1_subset_1(B_106, k1_zfmisc_1(A_12)))), inference(negUnitSimplification, [status(thm)], [c_46, c_548])).
% 3.16/1.66  tff(c_684, plain, (![A_123, B_124]: (r1_tarski(k3_subset_1(A_123, B_124), A_123) | ~m1_subset_1(B_124, k1_zfmisc_1(A_123)))), inference(resolution, [status(thm)], [c_657, c_552])).
% 3.16/1.66  tff(c_1492, plain, (![A_168, B_169]: (k4_xboole_0(k3_subset_1(A_168, B_169), A_168)=k1_xboole_0 | ~m1_subset_1(B_169, k1_zfmisc_1(A_168)))), inference(resolution, [status(thm)], [c_684, c_12])).
% 3.16/1.66  tff(c_1513, plain, (k4_xboole_0(k3_subset_1('#skF_3', '#skF_4'), '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_50, c_1492])).
% 3.16/1.66  tff(c_529, plain, (![B_102, A_103]: (m1_subset_1(B_102, A_103) | ~r2_hidden(B_102, A_103) | v1_xboole_0(A_103))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.16/1.66  tff(c_532, plain, (![C_16, A_12]: (m1_subset_1(C_16, k1_zfmisc_1(A_12)) | v1_xboole_0(k1_zfmisc_1(A_12)) | ~r1_tarski(C_16, A_12))), inference(resolution, [status(thm)], [c_22, c_529])).
% 3.16/1.66  tff(c_535, plain, (![C_16, A_12]: (m1_subset_1(C_16, k1_zfmisc_1(A_12)) | ~r1_tarski(C_16, A_12))), inference(negUnitSimplification, [status(thm)], [c_46, c_532])).
% 3.16/1.66  tff(c_761, plain, (![A_129, B_130]: (k4_xboole_0(A_129, B_130)=k3_subset_1(A_129, B_130) | ~m1_subset_1(B_130, k1_zfmisc_1(A_129)))), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.16/1.66  tff(c_816, plain, (![A_133, C_134]: (k4_xboole_0(A_133, C_134)=k3_subset_1(A_133, C_134) | ~r1_tarski(C_134, A_133))), inference(resolution, [status(thm)], [c_535, c_761])).
% 3.16/1.66  tff(c_839, plain, (![B_5, A_4]: (k4_xboole_0(B_5, A_4)=k3_subset_1(B_5, A_4) | k4_xboole_0(A_4, B_5)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_10, c_816])).
% 3.16/1.66  tff(c_1516, plain, (k4_xboole_0('#skF_3', k3_subset_1('#skF_3', '#skF_4'))=k3_subset_1('#skF_3', k3_subset_1('#skF_3', '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_1513, c_839])).
% 3.16/1.66  tff(c_1530, plain, (k4_xboole_0('#skF_3', k3_subset_1('#skF_3', '#skF_4'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_709, c_1516])).
% 3.16/1.66  tff(c_18, plain, (![A_10, B_11]: (r1_xboole_0(k4_xboole_0(A_10, B_11), B_11))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.16/1.66  tff(c_601, plain, (![B_112, A_113]: (~r1_xboole_0(B_112, A_113) | ~r1_tarski(B_112, A_113) | v1_xboole_0(B_112))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.16/1.66  tff(c_666, plain, (![A_121, B_122]: (~r1_tarski(k4_xboole_0(A_121, B_122), B_122) | v1_xboole_0(k4_xboole_0(A_121, B_122)))), inference(resolution, [status(thm)], [c_18, c_601])).
% 3.16/1.66  tff(c_681, plain, (![A_121, B_5]: (v1_xboole_0(k4_xboole_0(A_121, B_5)) | k4_xboole_0(k4_xboole_0(A_121, B_5), B_5)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_10, c_666])).
% 3.16/1.66  tff(c_1542, plain, (v1_xboole_0(k4_xboole_0('#skF_3', k3_subset_1('#skF_3', '#skF_4'))) | k4_xboole_0('#skF_4', k3_subset_1('#skF_3', '#skF_4'))!=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_1530, c_681])).
% 3.16/1.66  tff(c_1555, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_474, c_1530, c_1542])).
% 3.16/1.66  tff(c_2, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.16/1.66  tff(c_1564, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_1555, c_2])).
% 3.16/1.66  tff(c_1568, plain, $false, inference(negUnitSimplification, [status(thm)], [c_464, c_1564])).
% 3.16/1.66  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.16/1.66  
% 3.16/1.66  Inference rules
% 3.16/1.66  ----------------------
% 3.16/1.66  #Ref     : 0
% 3.16/1.66  #Sup     : 335
% 3.16/1.66  #Fact    : 0
% 3.16/1.66  #Define  : 0
% 3.16/1.66  #Split   : 9
% 3.16/1.66  #Chain   : 0
% 3.16/1.66  #Close   : 0
% 3.16/1.66  
% 3.16/1.66  Ordering : KBO
% 3.16/1.66  
% 3.16/1.66  Simplification rules
% 3.16/1.66  ----------------------
% 3.16/1.66  #Subsume      : 59
% 3.16/1.66  #Demod        : 171
% 3.16/1.66  #Tautology    : 171
% 3.16/1.66  #SimpNegUnit  : 6
% 3.16/1.66  #BackRed      : 14
% 3.16/1.66  
% 3.16/1.66  #Partial instantiations: 0
% 3.16/1.66  #Strategies tried      : 1
% 3.16/1.66  
% 3.16/1.66  Timing (in seconds)
% 3.16/1.66  ----------------------
% 3.16/1.66  Preprocessing        : 0.32
% 3.16/1.66  Parsing              : 0.15
% 3.16/1.66  CNF conversion       : 0.03
% 3.16/1.66  Main loop            : 0.43
% 3.16/1.66  Inferencing          : 0.16
% 3.16/1.66  Reduction            : 0.14
% 3.16/1.66  Demodulation         : 0.09
% 3.16/1.66  BG Simplification    : 0.02
% 3.16/1.66  Subsumption          : 0.09
% 3.16/1.66  Abstraction          : 0.02
% 3.16/1.66  MUC search           : 0.00
% 3.16/1.66  Cooper               : 0.00
% 3.16/1.66  Total                : 0.79
% 3.16/1.66  Index Insertion      : 0.00
% 3.16/1.66  Index Deletion       : 0.00
% 3.16/1.66  Index Matching       : 0.00
% 3.16/1.66  BG Taut test         : 0.00
%------------------------------------------------------------------------------
