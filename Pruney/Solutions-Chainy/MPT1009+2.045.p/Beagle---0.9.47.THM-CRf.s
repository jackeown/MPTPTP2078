%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:14:48 EST 2020

% Result     : Theorem 5.44s
% Output     : CNFRefutation 5.44s
% Verified   : 
% Statistics : Number of formulae       :  108 ( 366 expanded)
%              Number of leaves         :   44 ( 141 expanded)
%              Depth                    :   15
%              Number of atoms          :  153 ( 750 expanded)
%              Number of equality atoms :   56 ( 184 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k3_enumset1 > k7_relset_1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k7_relset_1,type,(
    k7_relset_1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_122,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,k1_tarski(A),B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A),B))) )
       => ( B != k1_xboole_0
         => r1_tarski(k7_relset_1(k1_tarski(A),B,D,C),k1_tarski(k1_funct_1(D,A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_funct_2)).

tff(f_94,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_70,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k9_relat_1(B,A),k2_relat_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t144_relat_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_90,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( k1_relat_1(B) = k1_tarski(A)
       => k2_relat_1(B) = k1_tarski(k1_funct_1(B,A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_funct_1)).

tff(f_104,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_100,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_78,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_82,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k1_relat_1(k7_relat_1(B,A)),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_relat_1)).

tff(f_35,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_56,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k2_tarski(B,C))
    <=> ~ ( A != k1_xboole_0
          & A != k1_tarski(B)
          & A != k1_tarski(C)
          & A != k2_tarski(B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l45_zfmisc_1)).

tff(f_62,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_110,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,C)))
     => ( r1_tarski(k1_relat_1(D),B)
       => m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,C))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_relset_1)).

tff(f_66,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_33,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_72,axiom,(
    ! [A] : k9_relat_1(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t150_relat_1)).

tff(c_62,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_1'),'#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_139,plain,(
    ! [C_60,A_61,B_62] :
      ( v1_relat_1(C_60)
      | ~ m1_subset_1(C_60,k1_zfmisc_1(k2_zfmisc_1(A_61,B_62))) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_152,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_62,c_139])).

tff(c_38,plain,(
    ! [B_22,A_21] :
      ( r1_tarski(k9_relat_1(B_22,A_21),k2_relat_1(B_22))
      | ~ v1_relat_1(B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_66,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_713,plain,(
    ! [B_146,A_147] :
      ( k1_tarski(k1_funct_1(B_146,A_147)) = k2_relat_1(B_146)
      | k1_tarski(A_147) != k1_relat_1(B_146)
      | ~ v1_funct_1(B_146)
      | ~ v1_relat_1(B_146) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_572,plain,(
    ! [A_123,B_124,C_125,D_126] :
      ( k7_relset_1(A_123,B_124,C_125,D_126) = k9_relat_1(C_125,D_126)
      | ~ m1_subset_1(C_125,k1_zfmisc_1(k2_zfmisc_1(A_123,B_124))) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_583,plain,(
    ! [D_126] : k7_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4',D_126) = k9_relat_1('#skF_4',D_126) ),
    inference(resolution,[status(thm)],[c_62,c_572])).

tff(c_58,plain,(
    ~ r1_tarski(k7_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4','#skF_3'),k1_tarski(k1_funct_1('#skF_4','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_627,plain,(
    ~ r1_tarski(k9_relat_1('#skF_4','#skF_3'),k1_tarski(k1_funct_1('#skF_4','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_583,c_58])).

tff(c_719,plain,
    ( ~ r1_tarski(k9_relat_1('#skF_4','#skF_3'),k2_relat_1('#skF_4'))
    | k1_tarski('#skF_1') != k1_relat_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_713,c_627])).

tff(c_731,plain,
    ( ~ r1_tarski(k9_relat_1('#skF_4','#skF_3'),k2_relat_1('#skF_4'))
    | k1_tarski('#skF_1') != k1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_152,c_66,c_719])).

tff(c_794,plain,(
    k1_tarski('#skF_1') != k1_relat_1('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_731])).

tff(c_312,plain,(
    ! [C_86,A_87,B_88] :
      ( v4_relat_1(C_86,A_87)
      | ~ m1_subset_1(C_86,k1_zfmisc_1(k2_zfmisc_1(A_87,B_88))) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_327,plain,(
    v4_relat_1('#skF_4',k1_tarski('#skF_1')) ),
    inference(resolution,[status(thm)],[c_62,c_312])).

tff(c_377,plain,(
    ! [B_104,A_105] :
      ( k7_relat_1(B_104,A_105) = B_104
      | ~ v4_relat_1(B_104,A_105)
      | ~ v1_relat_1(B_104) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_386,plain,
    ( k7_relat_1('#skF_4',k1_tarski('#skF_1')) = '#skF_4'
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_327,c_377])).

tff(c_393,plain,(
    k7_relat_1('#skF_4',k1_tarski('#skF_1')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_152,c_386])).

tff(c_44,plain,(
    ! [B_27,A_26] :
      ( r1_tarski(k1_relat_1(k7_relat_1(B_27,A_26)),A_26)
      | ~ v1_relat_1(B_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_428,plain,
    ( r1_tarski(k1_relat_1('#skF_4'),k1_tarski('#skF_1'))
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_393,c_44])).

tff(c_432,plain,(
    r1_tarski(k1_relat_1('#skF_4'),k1_tarski('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_152,c_428])).

tff(c_10,plain,(
    ! [A_4] : k2_tarski(A_4,A_4) = k1_tarski(A_4) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_1516,plain,(
    ! [B_222,C_223,A_224] :
      ( k2_tarski(B_222,C_223) = A_224
      | k1_tarski(C_223) = A_224
      | k1_tarski(B_222) = A_224
      | k1_xboole_0 = A_224
      | ~ r1_tarski(A_224,k2_tarski(B_222,C_223)) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_1533,plain,(
    ! [A_4,A_224] :
      ( k2_tarski(A_4,A_4) = A_224
      | k1_tarski(A_4) = A_224
      | k1_tarski(A_4) = A_224
      | k1_xboole_0 = A_224
      | ~ r1_tarski(A_224,k1_tarski(A_4)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_1516])).

tff(c_3617,plain,(
    ! [A_332,A_333] :
      ( k1_tarski(A_332) = A_333
      | k1_tarski(A_332) = A_333
      | k1_tarski(A_332) = A_333
      | k1_xboole_0 = A_333
      | ~ r1_tarski(A_333,k1_tarski(A_332)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_1533])).

tff(c_3627,plain,
    ( k1_tarski('#skF_1') = k1_relat_1('#skF_4')
    | k1_relat_1('#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_432,c_3617])).

tff(c_3643,plain,(
    k1_relat_1('#skF_4') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_794,c_794,c_794,c_3627])).

tff(c_32,plain,(
    ! [B_18] : k2_zfmisc_1(k1_xboole_0,B_18) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_829,plain,(
    ! [D_161,B_162,C_163,A_164] :
      ( m1_subset_1(D_161,k1_zfmisc_1(k2_zfmisc_1(B_162,C_163)))
      | ~ r1_tarski(k1_relat_1(D_161),B_162)
      | ~ m1_subset_1(D_161,k1_zfmisc_1(k2_zfmisc_1(A_164,C_163))) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_842,plain,(
    ! [B_165] :
      ( m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(B_165,'#skF_2')))
      | ~ r1_tarski(k1_relat_1('#skF_4'),B_165) ) ),
    inference(resolution,[status(thm)],[c_62,c_829])).

tff(c_862,plain,
    ( m1_subset_1('#skF_4',k1_zfmisc_1(k1_xboole_0))
    | ~ r1_tarski(k1_relat_1('#skF_4'),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_842])).

tff(c_888,plain,(
    ~ r1_tarski(k1_relat_1('#skF_4'),k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_862])).

tff(c_3678,plain,(
    ~ r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3643,c_888])).

tff(c_3707,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_3678])).

tff(c_3708,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k1_xboole_0)) ),
    inference(splitRight,[status(thm)],[c_862])).

tff(c_34,plain,(
    ! [A_19,B_20] :
      ( r1_tarski(A_19,B_20)
      | ~ m1_subset_1(A_19,k1_zfmisc_1(B_20)) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_3724,plain,(
    r1_tarski('#skF_4',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_3708,c_34])).

tff(c_8,plain,(
    ! [A_3] : r1_tarski(k1_xboole_0,A_3) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_210,plain,(
    ! [B_72,A_73] :
      ( B_72 = A_73
      | ~ r1_tarski(B_72,A_73)
      | ~ r1_tarski(A_73,B_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_228,plain,(
    ! [A_3] :
      ( k1_xboole_0 = A_3
      | ~ r1_tarski(A_3,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_8,c_210])).

tff(c_3761,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_3724,c_228])).

tff(c_3790,plain,(
    ! [A_3] : r1_tarski('#skF_4',A_3) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3761,c_8])).

tff(c_40,plain,(
    ! [A_23] : k9_relat_1(k1_xboole_0,A_23) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_3787,plain,(
    ! [A_23] : k9_relat_1('#skF_4',A_23) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3761,c_3761,c_40])).

tff(c_4100,plain,(
    ~ r1_tarski('#skF_4',k1_tarski(k1_funct_1('#skF_4','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3787,c_627])).

tff(c_4103,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3790,c_4100])).

tff(c_4105,plain,(
    k1_tarski('#skF_1') = k1_relat_1('#skF_4') ),
    inference(splitRight,[status(thm)],[c_731])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_460,plain,
    ( k1_tarski('#skF_1') = k1_relat_1('#skF_4')
    | ~ r1_tarski(k1_tarski('#skF_1'),k1_relat_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_432,c_2])).

tff(c_488,plain,(
    ~ r1_tarski(k1_tarski('#skF_1'),k1_relat_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_460])).

tff(c_4107,plain,(
    ~ r1_tarski(k1_relat_1('#skF_4'),k1_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4105,c_488])).

tff(c_4117,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_4107])).

tff(c_4118,plain,(
    k1_tarski('#skF_1') = k1_relat_1('#skF_4') ),
    inference(splitRight,[status(thm)],[c_460])).

tff(c_46,plain,(
    ! [B_29,A_28] :
      ( k1_tarski(k1_funct_1(B_29,A_28)) = k2_relat_1(B_29)
      | k1_tarski(A_28) != k1_relat_1(B_29)
      | ~ v1_funct_1(B_29)
      | ~ v1_relat_1(B_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_4127,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'),'#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4118,c_62])).

tff(c_54,plain,(
    ! [A_36,B_37,C_38,D_39] :
      ( k7_relset_1(A_36,B_37,C_38,D_39) = k9_relat_1(C_38,D_39)
      | ~ m1_subset_1(C_38,k1_zfmisc_1(k2_zfmisc_1(A_36,B_37))) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_4189,plain,(
    ! [D_39] : k7_relset_1(k1_relat_1('#skF_4'),'#skF_2','#skF_4',D_39) = k9_relat_1('#skF_4',D_39) ),
    inference(resolution,[status(thm)],[c_4127,c_54])).

tff(c_4125,plain,(
    ~ r1_tarski(k7_relset_1(k1_relat_1('#skF_4'),'#skF_2','#skF_4','#skF_3'),k1_tarski(k1_funct_1('#skF_4','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4118,c_58])).

tff(c_4410,plain,(
    ~ r1_tarski(k9_relat_1('#skF_4','#skF_3'),k1_tarski(k1_funct_1('#skF_4','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4189,c_4125])).

tff(c_4435,plain,
    ( ~ r1_tarski(k9_relat_1('#skF_4','#skF_3'),k2_relat_1('#skF_4'))
    | k1_tarski('#skF_1') != k1_relat_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_4410])).

tff(c_4437,plain,(
    ~ r1_tarski(k9_relat_1('#skF_4','#skF_3'),k2_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_152,c_66,c_4118,c_4435])).

tff(c_4440,plain,(
    ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_38,c_4437])).

tff(c_4444,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_152,c_4440])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:07:45 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.44/2.01  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.44/2.01  
% 5.44/2.01  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.44/2.02  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k3_enumset1 > k7_relset_1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 5.44/2.02  
% 5.44/2.02  %Foreground sorts:
% 5.44/2.02  
% 5.44/2.02  
% 5.44/2.02  %Background operators:
% 5.44/2.02  
% 5.44/2.02  
% 5.44/2.02  %Foreground operators:
% 5.44/2.02  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 5.44/2.02  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.44/2.02  tff(k1_tarski, type, k1_tarski: $i > $i).
% 5.44/2.02  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 5.44/2.02  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.44/2.02  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 5.44/2.02  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.44/2.02  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 5.44/2.02  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 5.44/2.02  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 5.44/2.02  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 5.44/2.02  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 5.44/2.02  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 5.44/2.02  tff('#skF_2', type, '#skF_2': $i).
% 5.44/2.02  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 5.44/2.02  tff('#skF_3', type, '#skF_3': $i).
% 5.44/2.02  tff('#skF_1', type, '#skF_1': $i).
% 5.44/2.02  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 5.44/2.02  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.44/2.02  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 5.44/2.02  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.44/2.02  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.44/2.02  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 5.44/2.02  tff('#skF_4', type, '#skF_4': $i).
% 5.44/2.02  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.44/2.02  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 5.44/2.02  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 5.44/2.02  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.44/2.02  
% 5.44/2.03  tff(f_122, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, k1_tarski(A), B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A), B)))) => (~(B = k1_xboole_0) => r1_tarski(k7_relset_1(k1_tarski(A), B, D, C), k1_tarski(k1_funct_1(D, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_funct_2)).
% 5.44/2.03  tff(f_94, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 5.44/2.03  tff(f_70, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k9_relat_1(B, A), k2_relat_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t144_relat_1)).
% 5.44/2.03  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 5.44/2.03  tff(f_90, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((k1_relat_1(B) = k1_tarski(A)) => (k2_relat_1(B) = k1_tarski(k1_funct_1(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t14_funct_1)).
% 5.44/2.03  tff(f_104, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 5.44/2.03  tff(f_100, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 5.44/2.03  tff(f_78, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t209_relat_1)).
% 5.44/2.03  tff(f_82, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k7_relat_1(B, A)), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t87_relat_1)).
% 5.44/2.03  tff(f_35, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 5.44/2.03  tff(f_56, axiom, (![A, B, C]: (r1_tarski(A, k2_tarski(B, C)) <=> ~(((~(A = k1_xboole_0) & ~(A = k1_tarski(B))) & ~(A = k1_tarski(C))) & ~(A = k2_tarski(B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l45_zfmisc_1)).
% 5.44/2.03  tff(f_62, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 5.44/2.03  tff(f_110, axiom, (![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, C))) => (r1_tarski(k1_relat_1(D), B) => m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t13_relset_1)).
% 5.44/2.03  tff(f_66, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 5.44/2.03  tff(f_33, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 5.44/2.03  tff(f_72, axiom, (![A]: (k9_relat_1(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t150_relat_1)).
% 5.44/2.03  tff(c_62, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_1'), '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_122])).
% 5.44/2.03  tff(c_139, plain, (![C_60, A_61, B_62]: (v1_relat_1(C_60) | ~m1_subset_1(C_60, k1_zfmisc_1(k2_zfmisc_1(A_61, B_62))))), inference(cnfTransformation, [status(thm)], [f_94])).
% 5.44/2.03  tff(c_152, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_62, c_139])).
% 5.44/2.03  tff(c_38, plain, (![B_22, A_21]: (r1_tarski(k9_relat_1(B_22, A_21), k2_relat_1(B_22)) | ~v1_relat_1(B_22))), inference(cnfTransformation, [status(thm)], [f_70])).
% 5.44/2.03  tff(c_66, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_122])).
% 5.44/2.03  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.44/2.03  tff(c_713, plain, (![B_146, A_147]: (k1_tarski(k1_funct_1(B_146, A_147))=k2_relat_1(B_146) | k1_tarski(A_147)!=k1_relat_1(B_146) | ~v1_funct_1(B_146) | ~v1_relat_1(B_146))), inference(cnfTransformation, [status(thm)], [f_90])).
% 5.44/2.03  tff(c_572, plain, (![A_123, B_124, C_125, D_126]: (k7_relset_1(A_123, B_124, C_125, D_126)=k9_relat_1(C_125, D_126) | ~m1_subset_1(C_125, k1_zfmisc_1(k2_zfmisc_1(A_123, B_124))))), inference(cnfTransformation, [status(thm)], [f_104])).
% 5.44/2.03  tff(c_583, plain, (![D_126]: (k7_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4', D_126)=k9_relat_1('#skF_4', D_126))), inference(resolution, [status(thm)], [c_62, c_572])).
% 5.44/2.03  tff(c_58, plain, (~r1_tarski(k7_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4', '#skF_3'), k1_tarski(k1_funct_1('#skF_4', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_122])).
% 5.44/2.03  tff(c_627, plain, (~r1_tarski(k9_relat_1('#skF_4', '#skF_3'), k1_tarski(k1_funct_1('#skF_4', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_583, c_58])).
% 5.44/2.03  tff(c_719, plain, (~r1_tarski(k9_relat_1('#skF_4', '#skF_3'), k2_relat_1('#skF_4')) | k1_tarski('#skF_1')!=k1_relat_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_713, c_627])).
% 5.44/2.03  tff(c_731, plain, (~r1_tarski(k9_relat_1('#skF_4', '#skF_3'), k2_relat_1('#skF_4')) | k1_tarski('#skF_1')!=k1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_152, c_66, c_719])).
% 5.44/2.03  tff(c_794, plain, (k1_tarski('#skF_1')!=k1_relat_1('#skF_4')), inference(splitLeft, [status(thm)], [c_731])).
% 5.44/2.03  tff(c_312, plain, (![C_86, A_87, B_88]: (v4_relat_1(C_86, A_87) | ~m1_subset_1(C_86, k1_zfmisc_1(k2_zfmisc_1(A_87, B_88))))), inference(cnfTransformation, [status(thm)], [f_100])).
% 5.44/2.03  tff(c_327, plain, (v4_relat_1('#skF_4', k1_tarski('#skF_1'))), inference(resolution, [status(thm)], [c_62, c_312])).
% 5.44/2.03  tff(c_377, plain, (![B_104, A_105]: (k7_relat_1(B_104, A_105)=B_104 | ~v4_relat_1(B_104, A_105) | ~v1_relat_1(B_104))), inference(cnfTransformation, [status(thm)], [f_78])).
% 5.44/2.03  tff(c_386, plain, (k7_relat_1('#skF_4', k1_tarski('#skF_1'))='#skF_4' | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_327, c_377])).
% 5.44/2.03  tff(c_393, plain, (k7_relat_1('#skF_4', k1_tarski('#skF_1'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_152, c_386])).
% 5.44/2.03  tff(c_44, plain, (![B_27, A_26]: (r1_tarski(k1_relat_1(k7_relat_1(B_27, A_26)), A_26) | ~v1_relat_1(B_27))), inference(cnfTransformation, [status(thm)], [f_82])).
% 5.44/2.03  tff(c_428, plain, (r1_tarski(k1_relat_1('#skF_4'), k1_tarski('#skF_1')) | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_393, c_44])).
% 5.44/2.03  tff(c_432, plain, (r1_tarski(k1_relat_1('#skF_4'), k1_tarski('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_152, c_428])).
% 5.44/2.03  tff(c_10, plain, (![A_4]: (k2_tarski(A_4, A_4)=k1_tarski(A_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 5.44/2.03  tff(c_1516, plain, (![B_222, C_223, A_224]: (k2_tarski(B_222, C_223)=A_224 | k1_tarski(C_223)=A_224 | k1_tarski(B_222)=A_224 | k1_xboole_0=A_224 | ~r1_tarski(A_224, k2_tarski(B_222, C_223)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 5.44/2.03  tff(c_1533, plain, (![A_4, A_224]: (k2_tarski(A_4, A_4)=A_224 | k1_tarski(A_4)=A_224 | k1_tarski(A_4)=A_224 | k1_xboole_0=A_224 | ~r1_tarski(A_224, k1_tarski(A_4)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_1516])).
% 5.44/2.03  tff(c_3617, plain, (![A_332, A_333]: (k1_tarski(A_332)=A_333 | k1_tarski(A_332)=A_333 | k1_tarski(A_332)=A_333 | k1_xboole_0=A_333 | ~r1_tarski(A_333, k1_tarski(A_332)))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_1533])).
% 5.44/2.03  tff(c_3627, plain, (k1_tarski('#skF_1')=k1_relat_1('#skF_4') | k1_relat_1('#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_432, c_3617])).
% 5.44/2.03  tff(c_3643, plain, (k1_relat_1('#skF_4')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_794, c_794, c_794, c_3627])).
% 5.44/2.03  tff(c_32, plain, (![B_18]: (k2_zfmisc_1(k1_xboole_0, B_18)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_62])).
% 5.44/2.03  tff(c_829, plain, (![D_161, B_162, C_163, A_164]: (m1_subset_1(D_161, k1_zfmisc_1(k2_zfmisc_1(B_162, C_163))) | ~r1_tarski(k1_relat_1(D_161), B_162) | ~m1_subset_1(D_161, k1_zfmisc_1(k2_zfmisc_1(A_164, C_163))))), inference(cnfTransformation, [status(thm)], [f_110])).
% 5.44/2.03  tff(c_842, plain, (![B_165]: (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(B_165, '#skF_2'))) | ~r1_tarski(k1_relat_1('#skF_4'), B_165))), inference(resolution, [status(thm)], [c_62, c_829])).
% 5.44/2.03  tff(c_862, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k1_xboole_0)) | ~r1_tarski(k1_relat_1('#skF_4'), k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_32, c_842])).
% 5.44/2.03  tff(c_888, plain, (~r1_tarski(k1_relat_1('#skF_4'), k1_xboole_0)), inference(splitLeft, [status(thm)], [c_862])).
% 5.44/2.03  tff(c_3678, plain, (~r1_tarski(k1_xboole_0, k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_3643, c_888])).
% 5.44/2.03  tff(c_3707, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_3678])).
% 5.44/2.03  tff(c_3708, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k1_xboole_0))), inference(splitRight, [status(thm)], [c_862])).
% 5.44/2.03  tff(c_34, plain, (![A_19, B_20]: (r1_tarski(A_19, B_20) | ~m1_subset_1(A_19, k1_zfmisc_1(B_20)))), inference(cnfTransformation, [status(thm)], [f_66])).
% 5.44/2.03  tff(c_3724, plain, (r1_tarski('#skF_4', k1_xboole_0)), inference(resolution, [status(thm)], [c_3708, c_34])).
% 5.44/2.03  tff(c_8, plain, (![A_3]: (r1_tarski(k1_xboole_0, A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 5.44/2.03  tff(c_210, plain, (![B_72, A_73]: (B_72=A_73 | ~r1_tarski(B_72, A_73) | ~r1_tarski(A_73, B_72))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.44/2.03  tff(c_228, plain, (![A_3]: (k1_xboole_0=A_3 | ~r1_tarski(A_3, k1_xboole_0))), inference(resolution, [status(thm)], [c_8, c_210])).
% 5.44/2.03  tff(c_3761, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_3724, c_228])).
% 5.44/2.03  tff(c_3790, plain, (![A_3]: (r1_tarski('#skF_4', A_3))), inference(demodulation, [status(thm), theory('equality')], [c_3761, c_8])).
% 5.44/2.03  tff(c_40, plain, (![A_23]: (k9_relat_1(k1_xboole_0, A_23)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_72])).
% 5.44/2.03  tff(c_3787, plain, (![A_23]: (k9_relat_1('#skF_4', A_23)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_3761, c_3761, c_40])).
% 5.44/2.03  tff(c_4100, plain, (~r1_tarski('#skF_4', k1_tarski(k1_funct_1('#skF_4', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_3787, c_627])).
% 5.44/2.03  tff(c_4103, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3790, c_4100])).
% 5.44/2.03  tff(c_4105, plain, (k1_tarski('#skF_1')=k1_relat_1('#skF_4')), inference(splitRight, [status(thm)], [c_731])).
% 5.44/2.03  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.44/2.03  tff(c_460, plain, (k1_tarski('#skF_1')=k1_relat_1('#skF_4') | ~r1_tarski(k1_tarski('#skF_1'), k1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_432, c_2])).
% 5.44/2.03  tff(c_488, plain, (~r1_tarski(k1_tarski('#skF_1'), k1_relat_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_460])).
% 5.44/2.03  tff(c_4107, plain, (~r1_tarski(k1_relat_1('#skF_4'), k1_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_4105, c_488])).
% 5.44/2.03  tff(c_4117, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_4107])).
% 5.44/2.03  tff(c_4118, plain, (k1_tarski('#skF_1')=k1_relat_1('#skF_4')), inference(splitRight, [status(thm)], [c_460])).
% 5.44/2.03  tff(c_46, plain, (![B_29, A_28]: (k1_tarski(k1_funct_1(B_29, A_28))=k2_relat_1(B_29) | k1_tarski(A_28)!=k1_relat_1(B_29) | ~v1_funct_1(B_29) | ~v1_relat_1(B_29))), inference(cnfTransformation, [status(thm)], [f_90])).
% 5.44/2.03  tff(c_4127, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'), '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_4118, c_62])).
% 5.44/2.03  tff(c_54, plain, (![A_36, B_37, C_38, D_39]: (k7_relset_1(A_36, B_37, C_38, D_39)=k9_relat_1(C_38, D_39) | ~m1_subset_1(C_38, k1_zfmisc_1(k2_zfmisc_1(A_36, B_37))))), inference(cnfTransformation, [status(thm)], [f_104])).
% 5.44/2.03  tff(c_4189, plain, (![D_39]: (k7_relset_1(k1_relat_1('#skF_4'), '#skF_2', '#skF_4', D_39)=k9_relat_1('#skF_4', D_39))), inference(resolution, [status(thm)], [c_4127, c_54])).
% 5.44/2.03  tff(c_4125, plain, (~r1_tarski(k7_relset_1(k1_relat_1('#skF_4'), '#skF_2', '#skF_4', '#skF_3'), k1_tarski(k1_funct_1('#skF_4', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_4118, c_58])).
% 5.44/2.03  tff(c_4410, plain, (~r1_tarski(k9_relat_1('#skF_4', '#skF_3'), k1_tarski(k1_funct_1('#skF_4', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_4189, c_4125])).
% 5.44/2.03  tff(c_4435, plain, (~r1_tarski(k9_relat_1('#skF_4', '#skF_3'), k2_relat_1('#skF_4')) | k1_tarski('#skF_1')!=k1_relat_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_46, c_4410])).
% 5.44/2.03  tff(c_4437, plain, (~r1_tarski(k9_relat_1('#skF_4', '#skF_3'), k2_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_152, c_66, c_4118, c_4435])).
% 5.44/2.03  tff(c_4440, plain, (~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_38, c_4437])).
% 5.44/2.03  tff(c_4444, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_152, c_4440])).
% 5.44/2.03  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.44/2.03  
% 5.44/2.03  Inference rules
% 5.44/2.03  ----------------------
% 5.44/2.03  #Ref     : 0
% 5.44/2.03  #Sup     : 918
% 5.44/2.03  #Fact    : 0
% 5.44/2.03  #Define  : 0
% 5.44/2.03  #Split   : 14
% 5.44/2.03  #Chain   : 0
% 5.44/2.03  #Close   : 0
% 5.44/2.03  
% 5.44/2.03  Ordering : KBO
% 5.44/2.03  
% 5.44/2.03  Simplification rules
% 5.44/2.03  ----------------------
% 5.44/2.03  #Subsume      : 98
% 5.44/2.03  #Demod        : 1142
% 5.44/2.03  #Tautology    : 526
% 5.44/2.03  #SimpNegUnit  : 9
% 5.44/2.03  #BackRed      : 174
% 5.44/2.03  
% 5.44/2.03  #Partial instantiations: 0
% 5.44/2.03  #Strategies tried      : 1
% 5.44/2.03  
% 5.44/2.03  Timing (in seconds)
% 5.44/2.03  ----------------------
% 5.44/2.04  Preprocessing        : 0.33
% 5.44/2.04  Parsing              : 0.17
% 5.44/2.04  CNF conversion       : 0.02
% 5.44/2.04  Main loop            : 0.93
% 5.44/2.04  Inferencing          : 0.30
% 5.44/2.04  Reduction            : 0.36
% 5.44/2.04  Demodulation         : 0.27
% 5.44/2.04  BG Simplification    : 0.03
% 5.44/2.04  Subsumption          : 0.17
% 5.44/2.04  Abstraction          : 0.04
% 5.44/2.04  MUC search           : 0.00
% 5.44/2.04  Cooper               : 0.00
% 5.44/2.04  Total                : 1.29
% 5.44/2.04  Index Insertion      : 0.00
% 5.44/2.04  Index Deletion       : 0.00
% 5.44/2.04  Index Matching       : 0.00
% 5.44/2.04  BG Taut test         : 0.00
%------------------------------------------------------------------------------
