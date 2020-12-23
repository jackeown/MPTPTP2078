%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:16:13 EST 2020

% Result     : Theorem 2.58s
% Output     : CNFRefutation 2.58s
% Verified   : 
% Statistics : Number of formulae       :  105 ( 188 expanded)
%              Number of leaves         :   41 (  84 expanded)
%              Depth                    :   10
%              Number of atoms          :  162 ( 469 expanded)
%              Number of equality atoms :   58 ( 135 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k8_relset_1 > k7_relset_1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k3_xboole_0 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff(v2_funct_1,type,(
    v2_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k8_relset_1,type,(
    k8_relset_1: ( $i * $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k7_relset_1,type,(
    k7_relset_1: ( $i * $i * $i * $i ) > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(v2_funct_2,type,(
    v2_funct_2: ( $i * $i ) > $o )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(v3_funct_2,type,(
    v3_funct_2: ( $i * $i * $i ) > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_120,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,A,A)
          & v3_funct_2(C,A,A)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
       => ( r1_tarski(B,A)
         => ( k7_relset_1(A,A,C,k8_relset_1(A,A,C,B)) = B
            & k8_relset_1(A,A,C,k7_relset_1(A,A,C,B)) = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_funct_2)).

tff(f_49,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_89,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( ( v1_funct_1(C)
          & v3_funct_2(C,A,B) )
       => ( v1_funct_1(C)
          & v2_funct_1(C)
          & v2_funct_2(C,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_funct_2)).

tff(f_59,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_105,axiom,(
    ! [A,B] :
      ( ( v1_funct_1(B)
        & v1_funct_2(B,A,A)
        & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
     => k1_relset_1(A,A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_funct_2)).

tff(f_45,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( ( r1_tarski(A,k1_relat_1(B))
          & v2_funct_1(B) )
       => k10_relat_1(B,k9_relat_1(B,A)) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t164_funct_1)).

tff(f_71,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k8_relset_1(A,B,C,D) = k10_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

tff(f_67,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_55,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_97,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A) )
     => ( v2_funct_2(B,A)
      <=> k2_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_funct_2)).

tff(f_63,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_77,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( k7_relset_1(A,B,C,A) = k2_relset_1(A,B,C)
        & k8_relset_1(A,B,C,B) = k1_relset_1(A,B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_relset_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => k9_relat_1(B,k10_relat_1(B,A)) = k3_xboole_0(A,k9_relat_1(B,k1_relat_1(B))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_funct_1)).

tff(c_40,plain,(
    r1_tarski('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_42,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_58,plain,(
    ! [C_39,A_40,B_41] :
      ( v1_relat_1(C_39)
      | ~ m1_subset_1(C_39,k1_zfmisc_1(k2_zfmisc_1(A_40,B_41))) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_62,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_42,c_58])).

tff(c_48,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_44,plain,(
    v3_funct_2('#skF_3','#skF_1','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_484,plain,(
    ! [C_162,A_163,B_164] :
      ( v2_funct_1(C_162)
      | ~ v3_funct_2(C_162,A_163,B_164)
      | ~ v1_funct_1(C_162)
      | ~ m1_subset_1(C_162,k1_zfmisc_1(k2_zfmisc_1(A_163,B_164))) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_487,plain,
    ( v2_funct_1('#skF_3')
    | ~ v3_funct_2('#skF_3','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_42,c_484])).

tff(c_490,plain,(
    v2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_44,c_487])).

tff(c_46,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_439,plain,(
    ! [A_151,B_152,C_153] :
      ( k1_relset_1(A_151,B_152,C_153) = k1_relat_1(C_153)
      | ~ m1_subset_1(C_153,k1_zfmisc_1(k2_zfmisc_1(A_151,B_152))) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_443,plain,(
    k1_relset_1('#skF_1','#skF_1','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_42,c_439])).

tff(c_558,plain,(
    ! [A_183,B_184] :
      ( k1_relset_1(A_183,A_183,B_184) = A_183
      | ~ m1_subset_1(B_184,k1_zfmisc_1(k2_zfmisc_1(A_183,A_183)))
      | ~ v1_funct_2(B_184,A_183,A_183)
      | ~ v1_funct_1(B_184) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_561,plain,
    ( k1_relset_1('#skF_1','#skF_1','#skF_3') = '#skF_1'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_42,c_558])).

tff(c_564,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_443,c_561])).

tff(c_6,plain,(
    ! [B_6,A_5] :
      ( k10_relat_1(B_6,k9_relat_1(B_6,A_5)) = A_5
      | ~ v2_funct_1(B_6)
      | ~ r1_tarski(A_5,k1_relat_1(B_6))
      | ~ v1_funct_1(B_6)
      | ~ v1_relat_1(B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_569,plain,(
    ! [A_5] :
      ( k10_relat_1('#skF_3',k9_relat_1('#skF_3',A_5)) = A_5
      | ~ v2_funct_1('#skF_3')
      | ~ r1_tarski(A_5,'#skF_1')
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_564,c_6])).

tff(c_613,plain,(
    ! [A_186] :
      ( k10_relat_1('#skF_3',k9_relat_1('#skF_3',A_186)) = A_186
      | ~ r1_tarski(A_186,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_48,c_490,c_569])).

tff(c_491,plain,(
    ! [A_165,B_166,C_167,D_168] :
      ( k8_relset_1(A_165,B_166,C_167,D_168) = k10_relat_1(C_167,D_168)
      | ~ m1_subset_1(C_167,k1_zfmisc_1(k2_zfmisc_1(A_165,B_166))) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_494,plain,(
    ! [D_168] : k8_relset_1('#skF_1','#skF_1','#skF_3',D_168) = k10_relat_1('#skF_3',D_168) ),
    inference(resolution,[status(thm)],[c_42,c_491])).

tff(c_459,plain,(
    ! [A_157,B_158,C_159,D_160] :
      ( k7_relset_1(A_157,B_158,C_159,D_160) = k9_relat_1(C_159,D_160)
      | ~ m1_subset_1(C_159,k1_zfmisc_1(k2_zfmisc_1(A_157,B_158))) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_462,plain,(
    ! [D_160] : k7_relset_1('#skF_1','#skF_1','#skF_3',D_160) = k9_relat_1('#skF_3',D_160) ),
    inference(resolution,[status(thm)],[c_42,c_459])).

tff(c_49,plain,(
    ! [A_37,B_38] :
      ( k3_xboole_0(A_37,B_38) = A_37
      | ~ r1_tarski(A_37,B_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_53,plain,(
    k3_xboole_0('#skF_2','#skF_1') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_40,c_49])).

tff(c_194,plain,(
    ! [A_84,B_85,C_86,D_87] :
      ( k7_relset_1(A_84,B_85,C_86,D_87) = k9_relat_1(C_86,D_87)
      | ~ m1_subset_1(C_86,k1_zfmisc_1(k2_zfmisc_1(A_84,B_85))) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_197,plain,(
    ! [D_87] : k7_relset_1('#skF_1','#skF_1','#skF_3',D_87) = k9_relat_1('#skF_3',D_87) ),
    inference(resolution,[status(thm)],[c_42,c_194])).

tff(c_64,plain,(
    ! [C_42,B_43,A_44] :
      ( v5_relat_1(C_42,B_43)
      | ~ m1_subset_1(C_42,k1_zfmisc_1(k2_zfmisc_1(A_44,B_43))) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_68,plain,(
    v5_relat_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_42,c_64])).

tff(c_75,plain,(
    ! [B_49,A_50] :
      ( k2_relat_1(B_49) = A_50
      | ~ v2_funct_2(B_49,A_50)
      | ~ v5_relat_1(B_49,A_50)
      | ~ v1_relat_1(B_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_78,plain,
    ( k2_relat_1('#skF_3') = '#skF_1'
    | ~ v2_funct_2('#skF_3','#skF_1')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_68,c_75])).

tff(c_81,plain,
    ( k2_relat_1('#skF_3') = '#skF_1'
    | ~ v2_funct_2('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_78])).

tff(c_82,plain,(
    ~ v2_funct_2('#skF_3','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_81])).

tff(c_154,plain,(
    ! [C_75,B_76,A_77] :
      ( v2_funct_2(C_75,B_76)
      | ~ v3_funct_2(C_75,A_77,B_76)
      | ~ v1_funct_1(C_75)
      | ~ m1_subset_1(C_75,k1_zfmisc_1(k2_zfmisc_1(A_77,B_76))) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_157,plain,
    ( v2_funct_2('#skF_3','#skF_1')
    | ~ v3_funct_2('#skF_3','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_42,c_154])).

tff(c_160,plain,(
    v2_funct_2('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_44,c_157])).

tff(c_162,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_160])).

tff(c_163,plain,(
    k2_relat_1('#skF_3') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_81])).

tff(c_165,plain,(
    ! [A_78,B_79,C_80] :
      ( k2_relset_1(A_78,B_79,C_80) = k2_relat_1(C_80)
      | ~ m1_subset_1(C_80,k1_zfmisc_1(k2_zfmisc_1(A_78,B_79))) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_169,plain,(
    k2_relset_1('#skF_1','#skF_1','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_42,c_165])).

tff(c_180,plain,(
    k2_relset_1('#skF_1','#skF_1','#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_163,c_169])).

tff(c_238,plain,(
    ! [A_99,B_100,C_101] :
      ( k7_relset_1(A_99,B_100,C_101,A_99) = k2_relset_1(A_99,B_100,C_101)
      | ~ m1_subset_1(C_101,k1_zfmisc_1(k2_zfmisc_1(A_99,B_100))) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_240,plain,(
    k7_relset_1('#skF_1','#skF_1','#skF_3','#skF_1') = k2_relset_1('#skF_1','#skF_1','#skF_3') ),
    inference(resolution,[status(thm)],[c_42,c_238])).

tff(c_242,plain,(
    k9_relat_1('#skF_3','#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_197,c_180,c_240])).

tff(c_185,plain,(
    ! [A_81,B_82,C_83] :
      ( k1_relset_1(A_81,B_82,C_83) = k1_relat_1(C_83)
      | ~ m1_subset_1(C_83,k1_zfmisc_1(k2_zfmisc_1(A_81,B_82))) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_189,plain,(
    k1_relset_1('#skF_1','#skF_1','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_42,c_185])).

tff(c_264,plain,(
    ! [A_110,B_111] :
      ( k1_relset_1(A_110,A_110,B_111) = A_110
      | ~ m1_subset_1(B_111,k1_zfmisc_1(k2_zfmisc_1(A_110,A_110)))
      | ~ v1_funct_2(B_111,A_110,A_110)
      | ~ v1_funct_1(B_111) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_267,plain,
    ( k1_relset_1('#skF_1','#skF_1','#skF_3') = '#skF_1'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_42,c_264])).

tff(c_270,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_189,c_267])).

tff(c_4,plain,(
    ! [A_3,B_4] :
      ( k3_xboole_0(A_3,k9_relat_1(B_4,k1_relat_1(B_4))) = k9_relat_1(B_4,k10_relat_1(B_4,A_3))
      | ~ v1_funct_1(B_4)
      | ~ v1_relat_1(B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_278,plain,(
    ! [A_3] :
      ( k9_relat_1('#skF_3',k10_relat_1('#skF_3',A_3)) = k3_xboole_0(A_3,k9_relat_1('#skF_3','#skF_1'))
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_270,c_4])).

tff(c_284,plain,(
    ! [A_3] : k9_relat_1('#skF_3',k10_relat_1('#skF_3',A_3)) = k3_xboole_0(A_3,'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_48,c_242,c_278])).

tff(c_208,plain,(
    ! [A_89,B_90,C_91,D_92] :
      ( k8_relset_1(A_89,B_90,C_91,D_92) = k10_relat_1(C_91,D_92)
      | ~ m1_subset_1(C_91,k1_zfmisc_1(k2_zfmisc_1(A_89,B_90))) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_211,plain,(
    ! [D_92] : k8_relset_1('#skF_1','#skF_1','#skF_3',D_92) = k10_relat_1('#skF_3',D_92) ),
    inference(resolution,[status(thm)],[c_42,c_208])).

tff(c_38,plain,
    ( k8_relset_1('#skF_1','#skF_1','#skF_3',k7_relset_1('#skF_1','#skF_1','#skF_3','#skF_2')) != '#skF_2'
    | k7_relset_1('#skF_1','#skF_1','#skF_3',k8_relset_1('#skF_1','#skF_1','#skF_3','#skF_2')) != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_63,plain,(
    k7_relset_1('#skF_1','#skF_1','#skF_3',k8_relset_1('#skF_1','#skF_1','#skF_3','#skF_2')) != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_38])).

tff(c_198,plain,(
    k9_relat_1('#skF_3',k8_relset_1('#skF_1','#skF_1','#skF_3','#skF_2')) != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_197,c_63])).

tff(c_212,plain,(
    k9_relat_1('#skF_3',k10_relat_1('#skF_3','#skF_2')) != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_211,c_198])).

tff(c_294,plain,(
    k3_xboole_0('#skF_2','#skF_1') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_284,c_212])).

tff(c_297,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_53,c_294])).

tff(c_298,plain,(
    k8_relset_1('#skF_1','#skF_1','#skF_3',k7_relset_1('#skF_1','#skF_1','#skF_3','#skF_2')) != '#skF_2' ),
    inference(splitRight,[status(thm)],[c_38])).

tff(c_463,plain,(
    k8_relset_1('#skF_1','#skF_1','#skF_3',k9_relat_1('#skF_3','#skF_2')) != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_462,c_298])).

tff(c_496,plain,(
    k10_relat_1('#skF_3',k9_relat_1('#skF_3','#skF_2')) != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_494,c_463])).

tff(c_622,plain,(
    ~ r1_tarski('#skF_2','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_613,c_496])).

tff(c_639,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_622])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.34  % Computer   : n018.cluster.edu
% 0.15/0.34  % Model      : x86_64 x86_64
% 0.15/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.34  % Memory     : 8042.1875MB
% 0.15/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.34  % CPULimit   : 60
% 0.15/0.34  % DateTime   : Tue Dec  1 17:37:57 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.58/1.29  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.58/1.30  
% 2.58/1.30  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.58/1.30  %$ v3_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k8_relset_1 > k7_relset_1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k3_xboole_0 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 2.58/1.30  
% 2.58/1.30  %Foreground sorts:
% 2.58/1.30  
% 2.58/1.30  
% 2.58/1.30  %Background operators:
% 2.58/1.30  
% 2.58/1.30  
% 2.58/1.30  %Foreground operators:
% 2.58/1.30  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 2.58/1.30  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.58/1.30  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 2.58/1.30  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.58/1.30  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 2.58/1.30  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.58/1.30  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.58/1.30  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 2.58/1.30  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.58/1.30  tff('#skF_2', type, '#skF_2': $i).
% 2.58/1.30  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.58/1.30  tff('#skF_3', type, '#skF_3': $i).
% 2.58/1.30  tff('#skF_1', type, '#skF_1': $i).
% 2.58/1.30  tff(v2_funct_2, type, v2_funct_2: ($i * $i) > $o).
% 2.58/1.30  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.58/1.30  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.58/1.30  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.58/1.30  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.58/1.30  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 2.58/1.30  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.58/1.30  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.58/1.30  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.58/1.30  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.58/1.30  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.58/1.30  tff(v3_funct_2, type, v3_funct_2: ($i * $i * $i) > $o).
% 2.58/1.30  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.58/1.30  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.58/1.30  
% 2.58/1.32  tff(f_120, negated_conjecture, ~(![A, B, C]: ((((v1_funct_1(C) & v1_funct_2(C, A, A)) & v3_funct_2(C, A, A)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (r1_tarski(B, A) => ((k7_relset_1(A, A, C, k8_relset_1(A, A, C, B)) = B) & (k8_relset_1(A, A, C, k7_relset_1(A, A, C, B)) = B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t92_funct_2)).
% 2.58/1.32  tff(f_49, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.58/1.32  tff(f_89, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v3_funct_2(C, A, B)) => ((v1_funct_1(C) & v2_funct_1(C)) & v2_funct_2(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_funct_2)).
% 2.58/1.32  tff(f_59, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.58/1.32  tff(f_105, axiom, (![A, B]: (((v1_funct_1(B) & v1_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (k1_relset_1(A, A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t67_funct_2)).
% 2.58/1.32  tff(f_45, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((r1_tarski(A, k1_relat_1(B)) & v2_funct_1(B)) => (k10_relat_1(B, k9_relat_1(B, A)) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t164_funct_1)).
% 2.58/1.32  tff(f_71, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k8_relset_1(A, B, C, D) = k10_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k8_relset_1)).
% 2.58/1.32  tff(f_67, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 2.58/1.32  tff(f_29, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 2.58/1.32  tff(f_55, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.58/1.32  tff(f_97, axiom, (![A, B]: ((v1_relat_1(B) & v5_relat_1(B, A)) => (v2_funct_2(B, A) <=> (k2_relat_1(B) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_funct_2)).
% 2.58/1.32  tff(f_63, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 2.58/1.32  tff(f_77, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((k7_relset_1(A, B, C, A) = k2_relset_1(A, B, C)) & (k8_relset_1(A, B, C, B) = k1_relset_1(A, B, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_relset_1)).
% 2.58/1.32  tff(f_35, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (k9_relat_1(B, k10_relat_1(B, A)) = k3_xboole_0(A, k9_relat_1(B, k1_relat_1(B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_funct_1)).
% 2.58/1.32  tff(c_40, plain, (r1_tarski('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_120])).
% 2.58/1.32  tff(c_42, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_120])).
% 2.58/1.32  tff(c_58, plain, (![C_39, A_40, B_41]: (v1_relat_1(C_39) | ~m1_subset_1(C_39, k1_zfmisc_1(k2_zfmisc_1(A_40, B_41))))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.58/1.32  tff(c_62, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_42, c_58])).
% 2.58/1.32  tff(c_48, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_120])).
% 2.58/1.32  tff(c_44, plain, (v3_funct_2('#skF_3', '#skF_1', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_120])).
% 2.58/1.32  tff(c_484, plain, (![C_162, A_163, B_164]: (v2_funct_1(C_162) | ~v3_funct_2(C_162, A_163, B_164) | ~v1_funct_1(C_162) | ~m1_subset_1(C_162, k1_zfmisc_1(k2_zfmisc_1(A_163, B_164))))), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.58/1.32  tff(c_487, plain, (v2_funct_1('#skF_3') | ~v3_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_42, c_484])).
% 2.58/1.32  tff(c_490, plain, (v2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_44, c_487])).
% 2.58/1.32  tff(c_46, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_120])).
% 2.58/1.32  tff(c_439, plain, (![A_151, B_152, C_153]: (k1_relset_1(A_151, B_152, C_153)=k1_relat_1(C_153) | ~m1_subset_1(C_153, k1_zfmisc_1(k2_zfmisc_1(A_151, B_152))))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.58/1.32  tff(c_443, plain, (k1_relset_1('#skF_1', '#skF_1', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_42, c_439])).
% 2.58/1.32  tff(c_558, plain, (![A_183, B_184]: (k1_relset_1(A_183, A_183, B_184)=A_183 | ~m1_subset_1(B_184, k1_zfmisc_1(k2_zfmisc_1(A_183, A_183))) | ~v1_funct_2(B_184, A_183, A_183) | ~v1_funct_1(B_184))), inference(cnfTransformation, [status(thm)], [f_105])).
% 2.58/1.32  tff(c_561, plain, (k1_relset_1('#skF_1', '#skF_1', '#skF_3')='#skF_1' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_42, c_558])).
% 2.58/1.32  tff(c_564, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_443, c_561])).
% 2.58/1.32  tff(c_6, plain, (![B_6, A_5]: (k10_relat_1(B_6, k9_relat_1(B_6, A_5))=A_5 | ~v2_funct_1(B_6) | ~r1_tarski(A_5, k1_relat_1(B_6)) | ~v1_funct_1(B_6) | ~v1_relat_1(B_6))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.58/1.32  tff(c_569, plain, (![A_5]: (k10_relat_1('#skF_3', k9_relat_1('#skF_3', A_5))=A_5 | ~v2_funct_1('#skF_3') | ~r1_tarski(A_5, '#skF_1') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_564, c_6])).
% 2.58/1.32  tff(c_613, plain, (![A_186]: (k10_relat_1('#skF_3', k9_relat_1('#skF_3', A_186))=A_186 | ~r1_tarski(A_186, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_48, c_490, c_569])).
% 2.58/1.32  tff(c_491, plain, (![A_165, B_166, C_167, D_168]: (k8_relset_1(A_165, B_166, C_167, D_168)=k10_relat_1(C_167, D_168) | ~m1_subset_1(C_167, k1_zfmisc_1(k2_zfmisc_1(A_165, B_166))))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.58/1.32  tff(c_494, plain, (![D_168]: (k8_relset_1('#skF_1', '#skF_1', '#skF_3', D_168)=k10_relat_1('#skF_3', D_168))), inference(resolution, [status(thm)], [c_42, c_491])).
% 2.58/1.32  tff(c_459, plain, (![A_157, B_158, C_159, D_160]: (k7_relset_1(A_157, B_158, C_159, D_160)=k9_relat_1(C_159, D_160) | ~m1_subset_1(C_159, k1_zfmisc_1(k2_zfmisc_1(A_157, B_158))))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.58/1.32  tff(c_462, plain, (![D_160]: (k7_relset_1('#skF_1', '#skF_1', '#skF_3', D_160)=k9_relat_1('#skF_3', D_160))), inference(resolution, [status(thm)], [c_42, c_459])).
% 2.58/1.32  tff(c_49, plain, (![A_37, B_38]: (k3_xboole_0(A_37, B_38)=A_37 | ~r1_tarski(A_37, B_38))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.58/1.32  tff(c_53, plain, (k3_xboole_0('#skF_2', '#skF_1')='#skF_2'), inference(resolution, [status(thm)], [c_40, c_49])).
% 2.58/1.32  tff(c_194, plain, (![A_84, B_85, C_86, D_87]: (k7_relset_1(A_84, B_85, C_86, D_87)=k9_relat_1(C_86, D_87) | ~m1_subset_1(C_86, k1_zfmisc_1(k2_zfmisc_1(A_84, B_85))))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.58/1.32  tff(c_197, plain, (![D_87]: (k7_relset_1('#skF_1', '#skF_1', '#skF_3', D_87)=k9_relat_1('#skF_3', D_87))), inference(resolution, [status(thm)], [c_42, c_194])).
% 2.58/1.32  tff(c_64, plain, (![C_42, B_43, A_44]: (v5_relat_1(C_42, B_43) | ~m1_subset_1(C_42, k1_zfmisc_1(k2_zfmisc_1(A_44, B_43))))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.58/1.32  tff(c_68, plain, (v5_relat_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_42, c_64])).
% 2.58/1.32  tff(c_75, plain, (![B_49, A_50]: (k2_relat_1(B_49)=A_50 | ~v2_funct_2(B_49, A_50) | ~v5_relat_1(B_49, A_50) | ~v1_relat_1(B_49))), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.58/1.32  tff(c_78, plain, (k2_relat_1('#skF_3')='#skF_1' | ~v2_funct_2('#skF_3', '#skF_1') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_68, c_75])).
% 2.58/1.32  tff(c_81, plain, (k2_relat_1('#skF_3')='#skF_1' | ~v2_funct_2('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_78])).
% 2.58/1.32  tff(c_82, plain, (~v2_funct_2('#skF_3', '#skF_1')), inference(splitLeft, [status(thm)], [c_81])).
% 2.58/1.32  tff(c_154, plain, (![C_75, B_76, A_77]: (v2_funct_2(C_75, B_76) | ~v3_funct_2(C_75, A_77, B_76) | ~v1_funct_1(C_75) | ~m1_subset_1(C_75, k1_zfmisc_1(k2_zfmisc_1(A_77, B_76))))), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.58/1.32  tff(c_157, plain, (v2_funct_2('#skF_3', '#skF_1') | ~v3_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_42, c_154])).
% 2.58/1.32  tff(c_160, plain, (v2_funct_2('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_44, c_157])).
% 2.58/1.32  tff(c_162, plain, $false, inference(negUnitSimplification, [status(thm)], [c_82, c_160])).
% 2.58/1.32  tff(c_163, plain, (k2_relat_1('#skF_3')='#skF_1'), inference(splitRight, [status(thm)], [c_81])).
% 2.58/1.32  tff(c_165, plain, (![A_78, B_79, C_80]: (k2_relset_1(A_78, B_79, C_80)=k2_relat_1(C_80) | ~m1_subset_1(C_80, k1_zfmisc_1(k2_zfmisc_1(A_78, B_79))))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.58/1.32  tff(c_169, plain, (k2_relset_1('#skF_1', '#skF_1', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_42, c_165])).
% 2.58/1.32  tff(c_180, plain, (k2_relset_1('#skF_1', '#skF_1', '#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_163, c_169])).
% 2.58/1.32  tff(c_238, plain, (![A_99, B_100, C_101]: (k7_relset_1(A_99, B_100, C_101, A_99)=k2_relset_1(A_99, B_100, C_101) | ~m1_subset_1(C_101, k1_zfmisc_1(k2_zfmisc_1(A_99, B_100))))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.58/1.32  tff(c_240, plain, (k7_relset_1('#skF_1', '#skF_1', '#skF_3', '#skF_1')=k2_relset_1('#skF_1', '#skF_1', '#skF_3')), inference(resolution, [status(thm)], [c_42, c_238])).
% 2.58/1.32  tff(c_242, plain, (k9_relat_1('#skF_3', '#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_197, c_180, c_240])).
% 2.58/1.32  tff(c_185, plain, (![A_81, B_82, C_83]: (k1_relset_1(A_81, B_82, C_83)=k1_relat_1(C_83) | ~m1_subset_1(C_83, k1_zfmisc_1(k2_zfmisc_1(A_81, B_82))))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.58/1.32  tff(c_189, plain, (k1_relset_1('#skF_1', '#skF_1', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_42, c_185])).
% 2.58/1.32  tff(c_264, plain, (![A_110, B_111]: (k1_relset_1(A_110, A_110, B_111)=A_110 | ~m1_subset_1(B_111, k1_zfmisc_1(k2_zfmisc_1(A_110, A_110))) | ~v1_funct_2(B_111, A_110, A_110) | ~v1_funct_1(B_111))), inference(cnfTransformation, [status(thm)], [f_105])).
% 2.58/1.32  tff(c_267, plain, (k1_relset_1('#skF_1', '#skF_1', '#skF_3')='#skF_1' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_42, c_264])).
% 2.58/1.32  tff(c_270, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_189, c_267])).
% 2.58/1.32  tff(c_4, plain, (![A_3, B_4]: (k3_xboole_0(A_3, k9_relat_1(B_4, k1_relat_1(B_4)))=k9_relat_1(B_4, k10_relat_1(B_4, A_3)) | ~v1_funct_1(B_4) | ~v1_relat_1(B_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.58/1.32  tff(c_278, plain, (![A_3]: (k9_relat_1('#skF_3', k10_relat_1('#skF_3', A_3))=k3_xboole_0(A_3, k9_relat_1('#skF_3', '#skF_1')) | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_270, c_4])).
% 2.58/1.32  tff(c_284, plain, (![A_3]: (k9_relat_1('#skF_3', k10_relat_1('#skF_3', A_3))=k3_xboole_0(A_3, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_48, c_242, c_278])).
% 2.58/1.32  tff(c_208, plain, (![A_89, B_90, C_91, D_92]: (k8_relset_1(A_89, B_90, C_91, D_92)=k10_relat_1(C_91, D_92) | ~m1_subset_1(C_91, k1_zfmisc_1(k2_zfmisc_1(A_89, B_90))))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.58/1.32  tff(c_211, plain, (![D_92]: (k8_relset_1('#skF_1', '#skF_1', '#skF_3', D_92)=k10_relat_1('#skF_3', D_92))), inference(resolution, [status(thm)], [c_42, c_208])).
% 2.58/1.32  tff(c_38, plain, (k8_relset_1('#skF_1', '#skF_1', '#skF_3', k7_relset_1('#skF_1', '#skF_1', '#skF_3', '#skF_2'))!='#skF_2' | k7_relset_1('#skF_1', '#skF_1', '#skF_3', k8_relset_1('#skF_1', '#skF_1', '#skF_3', '#skF_2'))!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_120])).
% 2.58/1.32  tff(c_63, plain, (k7_relset_1('#skF_1', '#skF_1', '#skF_3', k8_relset_1('#skF_1', '#skF_1', '#skF_3', '#skF_2'))!='#skF_2'), inference(splitLeft, [status(thm)], [c_38])).
% 2.58/1.32  tff(c_198, plain, (k9_relat_1('#skF_3', k8_relset_1('#skF_1', '#skF_1', '#skF_3', '#skF_2'))!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_197, c_63])).
% 2.58/1.32  tff(c_212, plain, (k9_relat_1('#skF_3', k10_relat_1('#skF_3', '#skF_2'))!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_211, c_198])).
% 2.58/1.32  tff(c_294, plain, (k3_xboole_0('#skF_2', '#skF_1')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_284, c_212])).
% 2.58/1.32  tff(c_297, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_53, c_294])).
% 2.58/1.32  tff(c_298, plain, (k8_relset_1('#skF_1', '#skF_1', '#skF_3', k7_relset_1('#skF_1', '#skF_1', '#skF_3', '#skF_2'))!='#skF_2'), inference(splitRight, [status(thm)], [c_38])).
% 2.58/1.32  tff(c_463, plain, (k8_relset_1('#skF_1', '#skF_1', '#skF_3', k9_relat_1('#skF_3', '#skF_2'))!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_462, c_298])).
% 2.58/1.32  tff(c_496, plain, (k10_relat_1('#skF_3', k9_relat_1('#skF_3', '#skF_2'))!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_494, c_463])).
% 2.58/1.32  tff(c_622, plain, (~r1_tarski('#skF_2', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_613, c_496])).
% 2.58/1.32  tff(c_639, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_40, c_622])).
% 2.58/1.32  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.58/1.32  
% 2.58/1.32  Inference rules
% 2.58/1.32  ----------------------
% 2.58/1.32  #Ref     : 0
% 2.58/1.32  #Sup     : 151
% 2.58/1.32  #Fact    : 0
% 2.58/1.32  #Define  : 0
% 2.58/1.32  #Split   : 3
% 2.58/1.32  #Chain   : 0
% 2.58/1.32  #Close   : 0
% 2.58/1.32  
% 2.58/1.32  Ordering : KBO
% 2.58/1.32  
% 2.58/1.32  Simplification rules
% 2.58/1.32  ----------------------
% 2.58/1.32  #Subsume      : 0
% 2.58/1.32  #Demod        : 87
% 2.58/1.32  #Tautology    : 100
% 2.58/1.32  #SimpNegUnit  : 2
% 2.58/1.32  #BackRed      : 16
% 2.58/1.32  
% 2.58/1.32  #Partial instantiations: 0
% 2.58/1.32  #Strategies tried      : 1
% 2.58/1.32  
% 2.58/1.32  Timing (in seconds)
% 2.58/1.32  ----------------------
% 2.58/1.32  Preprocessing        : 0.30
% 2.58/1.32  Parsing              : 0.16
% 2.58/1.32  CNF conversion       : 0.02
% 2.58/1.32  Main loop            : 0.29
% 2.58/1.32  Inferencing          : 0.12
% 2.58/1.32  Reduction            : 0.09
% 2.58/1.32  Demodulation         : 0.06
% 2.58/1.32  BG Simplification    : 0.02
% 2.58/1.32  Subsumption          : 0.03
% 2.58/1.32  Abstraction          : 0.02
% 2.58/1.32  MUC search           : 0.00
% 2.58/1.32  Cooper               : 0.00
% 2.58/1.32  Total                : 0.62
% 2.58/1.32  Index Insertion      : 0.00
% 2.58/1.32  Index Deletion       : 0.00
% 2.58/1.32  Index Matching       : 0.00
% 2.58/1.32  BG Taut test         : 0.00
%------------------------------------------------------------------------------
