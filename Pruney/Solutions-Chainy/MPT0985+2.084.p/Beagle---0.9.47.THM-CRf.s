%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:12:39 EST 2020

% Result     : Theorem 5.32s
% Output     : CNFRefutation 5.66s
% Verified   : 
% Statistics : Number of formulae       :  176 ( 783 expanded)
%              Number of leaves         :   41 ( 270 expanded)
%              Depth                    :   13
%              Number of atoms          :  312 (2200 expanded)
%              Number of equality atoms :  121 ( 665 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v5_ordinal1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k7_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff(k2_funct_1,type,(
    k2_funct_1: $i > $i )).

tff(v2_funct_1,type,(
    v2_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(v5_ordinal1,type,(
    v5_ordinal1: $i > $o )).

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

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_159,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( ( v2_funct_1(C)
            & k2_relset_1(A,B,C) = B )
         => ( v1_funct_1(k2_funct_1(C))
            & v1_funct_2(k2_funct_1(C),B,A)
            & m1_subset_1(k2_funct_1(C),k1_zfmisc_1(k2_zfmisc_1(B,A))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_funct_2)).

tff(f_98,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_112,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_86,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k2_relat_1(A) = k1_relat_1(k2_funct_1(A))
          & k1_relat_1(A) = k2_relat_1(k2_funct_1(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_55,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ( k1_relat_1(A) = k1_xboole_0
          | k2_relat_1(A) = k1_xboole_0 )
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).

tff(f_108,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_130,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( ( ( B = k1_xboole_0
           => A = k1_xboole_0 )
         => ( v1_funct_2(C,A,B)
          <=> A = k1_relset_1(A,B,C) ) )
        & ( B = k1_xboole_0
         => ( A = k1_xboole_0
            | ( v1_funct_2(C,A,B)
            <=> C = k1_xboole_0 ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).

tff(f_68,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).

tff(f_41,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k10_relat_1(A,k2_relat_1(A)) = k1_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_relat_1)).

tff(f_142,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r1_tarski(k2_relat_1(B),A)
       => ( v1_funct_1(B)
          & v1_funct_2(B,k1_relat_1(B),A)
          & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B),A))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_funct_2)).

tff(f_33,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_60,axiom,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_relat_1)).

tff(f_59,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

tff(c_78,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_2384,plain,(
    ! [C_230,A_231,B_232] :
      ( v1_relat_1(C_230)
      | ~ m1_subset_1(C_230,k1_zfmisc_1(k2_zfmisc_1(A_231,B_232))) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_2392,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_78,c_2384])).

tff(c_82,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_76,plain,(
    v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_74,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_2558,plain,(
    ! [A_254,B_255,C_256] :
      ( k2_relset_1(A_254,B_255,C_256) = k2_relat_1(C_256)
      | ~ m1_subset_1(C_256,k1_zfmisc_1(k2_zfmisc_1(A_254,B_255))) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_2564,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_78,c_2558])).

tff(c_2567,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_2564])).

tff(c_34,plain,(
    ! [A_14] :
      ( k1_relat_1(k2_funct_1(A_14)) = k2_relat_1(A_14)
      | ~ v2_funct_1(A_14)
      | ~ v1_funct_1(A_14)
      | ~ v1_relat_1(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_216,plain,(
    ! [C_48,A_49,B_50] :
      ( v1_relat_1(C_48)
      | ~ m1_subset_1(C_48,k1_zfmisc_1(k2_zfmisc_1(A_49,B_50))) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_220,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_78,c_216])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_339,plain,(
    ! [A_72,B_73,C_74] :
      ( k2_relset_1(A_72,B_73,C_74) = k2_relat_1(C_74)
      | ~ m1_subset_1(C_74,k1_zfmisc_1(k2_zfmisc_1(A_72,B_73))) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_342,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_78,c_339])).

tff(c_344,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_342])).

tff(c_16,plain,(
    ! [A_9] :
      ( k2_relat_1(A_9) != k1_xboole_0
      | k1_xboole_0 = A_9
      | ~ v1_relat_1(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_227,plain,
    ( k2_relat_1('#skF_3') != k1_xboole_0
    | k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_220,c_16])).

tff(c_229,plain,(
    k2_relat_1('#skF_3') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_227])).

tff(c_346,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_344,c_229])).

tff(c_80,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_330,plain,(
    ! [A_69,B_70,C_71] :
      ( k1_relset_1(A_69,B_70,C_71) = k1_relat_1(C_71)
      | ~ m1_subset_1(C_71,k1_zfmisc_1(k2_zfmisc_1(A_69,B_70))) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_334,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_78,c_330])).

tff(c_582,plain,(
    ! [B_97,A_98,C_99] :
      ( k1_xboole_0 = B_97
      | k1_relset_1(A_98,B_97,C_99) = A_98
      | ~ v1_funct_2(C_99,A_98,B_97)
      | ~ m1_subset_1(C_99,k1_zfmisc_1(k2_zfmisc_1(A_98,B_97))) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_591,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_1'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_78,c_582])).

tff(c_598,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_334,c_591])).

tff(c_599,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_346,c_598])).

tff(c_32,plain,(
    ! [A_14] :
      ( k2_relat_1(k2_funct_1(A_14)) = k1_relat_1(A_14)
      | ~ v2_funct_1(A_14)
      | ~ v1_funct_1(A_14)
      | ~ v1_relat_1(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_28,plain,(
    ! [A_11] :
      ( v1_relat_1(k2_funct_1(A_11))
      | ~ v1_funct_1(A_11)
      | ~ v1_relat_1(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_301,plain,(
    ! [A_65] :
      ( k2_relat_1(k2_funct_1(A_65)) = k1_relat_1(A_65)
      | ~ v2_funct_1(A_65)
      | ~ v1_funct_1(A_65)
      | ~ v1_relat_1(A_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_12,plain,(
    ! [A_6] :
      ( k10_relat_1(A_6,k2_relat_1(A_6)) = k1_relat_1(A_6)
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_1096,plain,(
    ! [A_138] :
      ( k10_relat_1(k2_funct_1(A_138),k1_relat_1(A_138)) = k1_relat_1(k2_funct_1(A_138))
      | ~ v1_relat_1(k2_funct_1(A_138))
      | ~ v2_funct_1(A_138)
      | ~ v1_funct_1(A_138)
      | ~ v1_relat_1(A_138) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_301,c_12])).

tff(c_1108,plain,
    ( k10_relat_1(k2_funct_1('#skF_3'),'#skF_1') = k1_relat_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_599,c_1096])).

tff(c_1125,plain,
    ( k10_relat_1(k2_funct_1('#skF_3'),'#skF_1') = k1_relat_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_220,c_82,c_76,c_1108])).

tff(c_1128,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_1125])).

tff(c_1131,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_28,c_1128])).

tff(c_1135,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_220,c_82,c_1131])).

tff(c_1137,plain,(
    v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_1125])).

tff(c_153,plain,(
    ! [A_41] :
      ( v1_funct_1(k2_funct_1(A_41))
      | ~ v1_funct_1(A_41)
      | ~ v1_relat_1(A_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_72,plain,
    ( ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_152,plain,(
    ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_72])).

tff(c_156,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_153,c_152])).

tff(c_159,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_156])).

tff(c_182,plain,(
    ! [C_43,A_44,B_45] :
      ( v1_relat_1(C_43)
      | ~ m1_subset_1(C_43,k1_zfmisc_1(k2_zfmisc_1(A_44,B_45))) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_185,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_78,c_182])).

tff(c_189,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_159,c_185])).

tff(c_191,plain,(
    v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_72])).

tff(c_397,plain,(
    ! [B_83,A_84] :
      ( m1_subset_1(B_83,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B_83),A_84)))
      | ~ r1_tarski(k2_relat_1(B_83),A_84)
      | ~ v1_funct_1(B_83)
      | ~ v1_relat_1(B_83) ) ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_1429,plain,(
    ! [A_144,A_145] :
      ( m1_subset_1(k2_funct_1(A_144),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(A_144),A_145)))
      | ~ r1_tarski(k2_relat_1(k2_funct_1(A_144)),A_145)
      | ~ v1_funct_1(k2_funct_1(A_144))
      | ~ v1_relat_1(k2_funct_1(A_144))
      | ~ v2_funct_1(A_144)
      | ~ v1_funct_1(A_144)
      | ~ v1_relat_1(A_144) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_397])).

tff(c_1457,plain,(
    ! [A_145] :
      ( m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2',A_145)))
      | ~ r1_tarski(k2_relat_1(k2_funct_1('#skF_3')),A_145)
      | ~ v1_funct_1(k2_funct_1('#skF_3'))
      | ~ v1_relat_1(k2_funct_1('#skF_3'))
      | ~ v2_funct_1('#skF_3')
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_344,c_1429])).

tff(c_1482,plain,(
    ! [A_146] :
      ( m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2',A_146)))
      | ~ r1_tarski(k2_relat_1(k2_funct_1('#skF_3')),A_146) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_220,c_82,c_76,c_1137,c_191,c_1457])).

tff(c_190,plain,
    ( ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_72])).

tff(c_211,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_190])).

tff(c_1523,plain,(
    ~ r1_tarski(k2_relat_1(k2_funct_1('#skF_3')),'#skF_1') ),
    inference(resolution,[status(thm)],[c_1482,c_211])).

tff(c_1526,plain,
    ( ~ r1_tarski(k1_relat_1('#skF_3'),'#skF_1')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_1523])).

tff(c_1529,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_220,c_82,c_76,c_6,c_599,c_1526])).

tff(c_1530,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_227])).

tff(c_8,plain,(
    ! [A_3] : r1_tarski(k1_xboole_0,A_3) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_1594,plain,(
    ! [A_3] : r1_tarski('#skF_3',A_3) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1530,c_8])).

tff(c_1531,plain,(
    k2_relat_1('#skF_3') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_227])).

tff(c_1606,plain,(
    k2_relat_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1530,c_1531])).

tff(c_24,plain,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_91,plain,(
    ! [A_36] : k1_relat_1(k6_relat_1(A_36)) = A_36 ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_100,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_91])).

tff(c_1591,plain,(
    k1_relat_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1530,c_1530,c_100])).

tff(c_1880,plain,(
    ! [B_190,A_191] :
      ( m1_subset_1(B_190,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B_190),A_191)))
      | ~ r1_tarski(k2_relat_1(B_190),A_191)
      | ~ v1_funct_1(B_190)
      | ~ v1_relat_1(B_190) ) ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_1909,plain,(
    ! [A_191] :
      ( m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_3',A_191)))
      | ~ r1_tarski(k2_relat_1('#skF_3'),A_191)
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1591,c_1880])).

tff(c_1923,plain,(
    ! [A_191] : m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_3',A_191))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_220,c_82,c_1594,c_1606,c_1909])).

tff(c_143,plain,(
    ! [A_40] :
      ( v1_relat_1(k2_funct_1(A_40))
      | ~ v1_funct_1(A_40)
      | ~ v1_relat_1(A_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_150,plain,(
    ! [A_40] :
      ( k2_relat_1(k2_funct_1(A_40)) != k1_xboole_0
      | k2_funct_1(A_40) = k1_xboole_0
      | ~ v1_funct_1(A_40)
      | ~ v1_relat_1(A_40) ) ),
    inference(resolution,[status(thm)],[c_143,c_16])).

tff(c_1758,plain,(
    ! [A_170] :
      ( k2_relat_1(k2_funct_1(A_170)) != '#skF_3'
      | k2_funct_1(A_170) = '#skF_3'
      | ~ v1_funct_1(A_170)
      | ~ v1_relat_1(A_170) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1530,c_1530,c_150])).

tff(c_2366,plain,(
    ! [A_229] :
      ( k1_relat_1(A_229) != '#skF_3'
      | k2_funct_1(A_229) = '#skF_3'
      | ~ v1_funct_1(A_229)
      | ~ v1_relat_1(A_229)
      | ~ v2_funct_1(A_229)
      | ~ v1_funct_1(A_229)
      | ~ v1_relat_1(A_229) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_1758])).

tff(c_2369,plain,
    ( k1_relat_1('#skF_3') != '#skF_3'
    | k2_funct_1('#skF_3') = '#skF_3'
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_76,c_2366])).

tff(c_2372,plain,(
    k2_funct_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_220,c_82,c_1591,c_2369])).

tff(c_1779,plain,(
    ! [A_176,B_177,C_178] :
      ( k2_relset_1(A_176,B_177,C_178) = k2_relat_1(C_178)
      | ~ m1_subset_1(C_178,k1_zfmisc_1(k2_zfmisc_1(A_176,B_177))) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_1782,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_78,c_1779])).

tff(c_1784,plain,(
    '#skF_2' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1606,c_74,c_1782])).

tff(c_1786,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1784,c_211])).

tff(c_2373,plain,(
    ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2372,c_1786])).

tff(c_2377,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1923,c_2373])).

tff(c_2378,plain,(
    ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_190])).

tff(c_2379,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_190])).

tff(c_2549,plain,(
    ! [A_251,B_252,C_253] :
      ( k1_relset_1(A_251,B_252,C_253) = k1_relat_1(C_253)
      | ~ m1_subset_1(C_253,k1_zfmisc_1(k2_zfmisc_1(A_251,B_252))) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_2556,plain,(
    k1_relset_1('#skF_2','#skF_1',k2_funct_1('#skF_3')) = k1_relat_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_2379,c_2549])).

tff(c_2770,plain,(
    ! [B_276,C_277,A_278] :
      ( k1_xboole_0 = B_276
      | v1_funct_2(C_277,A_278,B_276)
      | k1_relset_1(A_278,B_276,C_277) != A_278
      | ~ m1_subset_1(C_277,k1_zfmisc_1(k2_zfmisc_1(A_278,B_276))) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_2779,plain,
    ( k1_xboole_0 = '#skF_1'
    | v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | k1_relset_1('#skF_2','#skF_1',k2_funct_1('#skF_3')) != '#skF_2' ),
    inference(resolution,[status(thm)],[c_2379,c_2770])).

tff(c_2788,plain,
    ( k1_xboole_0 = '#skF_1'
    | v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | k1_relat_1(k2_funct_1('#skF_3')) != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2556,c_2779])).

tff(c_2789,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_relat_1(k2_funct_1('#skF_3')) != '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_2378,c_2788])).

tff(c_2793,plain,(
    k1_relat_1(k2_funct_1('#skF_3')) != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_2789])).

tff(c_2796,plain,
    ( k2_relat_1('#skF_3') != '#skF_2'
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_2793])).

tff(c_2799,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2392,c_82,c_76,c_2567,c_2796])).

tff(c_2800,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_2789])).

tff(c_2409,plain,
    ( k2_relat_1('#skF_3') != k1_xboole_0
    | k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_2392,c_16])).

tff(c_2432,plain,(
    k2_relat_1('#skF_3') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_2409])).

tff(c_2569,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2567,c_2432])).

tff(c_2814,plain,(
    '#skF_2' != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2800,c_2569])).

tff(c_2557,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_78,c_2549])).

tff(c_64,plain,(
    ! [B_29,A_28,C_30] :
      ( k1_xboole_0 = B_29
      | k1_relset_1(A_28,B_29,C_30) = A_28
      | ~ v1_funct_2(C_30,A_28,B_29)
      | ~ m1_subset_1(C_30,k1_zfmisc_1(k2_zfmisc_1(A_28,B_29))) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_2837,plain,(
    ! [B_279,A_280,C_281] :
      ( B_279 = '#skF_1'
      | k1_relset_1(A_280,B_279,C_281) = A_280
      | ~ v1_funct_2(C_281,A_280,B_279)
      | ~ m1_subset_1(C_281,k1_zfmisc_1(k2_zfmisc_1(A_280,B_279))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2800,c_64])).

tff(c_2846,plain,
    ( '#skF_2' = '#skF_1'
    | k1_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_1'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_78,c_2837])).

tff(c_2852,plain,
    ( '#skF_2' = '#skF_1'
    | k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_2557,c_2846])).

tff(c_2867,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_2814,c_2852])).

tff(c_18,plain,(
    ! [A_9] :
      ( k1_relat_1(A_9) != k1_xboole_0
      | k1_xboole_0 = A_9
      | ~ v1_relat_1(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_2410,plain,
    ( k1_relat_1('#skF_3') != k1_xboole_0
    | k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_2392,c_18])).

tff(c_2433,plain,(
    k1_relat_1('#skF_3') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_2410])).

tff(c_2819,plain,(
    k1_relat_1('#skF_3') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2800,c_2433])).

tff(c_2945,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2867,c_2819])).

tff(c_2946,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_2410])).

tff(c_107,plain,(
    ! [A_37] : k2_relat_1(k6_relat_1(A_37)) = A_37 ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_116,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_107])).

tff(c_2953,plain,(
    k2_relat_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2946,c_2946,c_116])).

tff(c_2948,plain,(
    k2_relat_1('#skF_3') != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2946,c_2432])).

tff(c_2998,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2953,c_2948])).

tff(c_2999,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_2409])).

tff(c_3021,plain,(
    ! [A_3] : r1_tarski('#skF_3',A_3) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2999,c_8])).

tff(c_3000,plain,(
    k2_relat_1('#skF_3') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_2409])).

tff(c_3031,plain,(
    k2_relat_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2999,c_3000])).

tff(c_3018,plain,(
    k1_relat_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2999,c_2999,c_100])).

tff(c_3557,plain,(
    ! [B_324,A_325] :
      ( v1_funct_2(B_324,k1_relat_1(B_324),A_325)
      | ~ r1_tarski(k2_relat_1(B_324),A_325)
      | ~ v1_funct_1(B_324)
      | ~ v1_relat_1(B_324) ) ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_3563,plain,(
    ! [A_325] :
      ( v1_funct_2('#skF_3','#skF_3',A_325)
      | ~ r1_tarski(k2_relat_1('#skF_3'),A_325)
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3018,c_3557])).

tff(c_3568,plain,(
    ! [A_325] : v1_funct_2('#skF_3','#skF_3',A_325) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2392,c_82,c_3021,c_3031,c_3563])).

tff(c_3389,plain,(
    ! [A_318,B_319,C_320] :
      ( k2_relset_1(A_318,B_319,C_320) = k2_relat_1(C_320)
      | ~ m1_subset_1(C_320,k1_zfmisc_1(k2_zfmisc_1(A_318,B_319))) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_3395,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_78,c_3389])).

tff(c_3399,plain,(
    '#skF_2' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_3031,c_3395])).

tff(c_3172,plain,(
    ! [A_300] :
      ( k2_relat_1(k2_funct_1(A_300)) = k1_relat_1(A_300)
      | ~ v2_funct_1(A_300)
      | ~ v1_funct_1(A_300)
      | ~ v1_relat_1(A_300) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_2391,plain,(
    v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_2379,c_2384])).

tff(c_2417,plain,
    ( k2_relat_1(k2_funct_1('#skF_3')) != k1_xboole_0
    | k2_funct_1('#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2391,c_16])).

tff(c_3078,plain,
    ( k2_relat_1(k2_funct_1('#skF_3')) != '#skF_3'
    | k2_funct_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2999,c_2999,c_2417])).

tff(c_3079,plain,(
    k2_relat_1(k2_funct_1('#skF_3')) != '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_3078])).

tff(c_3178,plain,
    ( k1_relat_1('#skF_3') != '#skF_3'
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_3172,c_3079])).

tff(c_3188,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2392,c_82,c_76,c_3018,c_3178])).

tff(c_3189,plain,(
    k2_funct_1('#skF_3') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_3078])).

tff(c_3194,plain,(
    ~ v1_funct_2('#skF_3','#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3189,c_2378])).

tff(c_3406,plain,(
    ~ v1_funct_2('#skF_3','#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3399,c_3194])).

tff(c_3581,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3568,c_3406])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:53:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.32/2.03  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.32/2.04  
% 5.32/2.04  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.32/2.05  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v5_ordinal1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k7_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 5.32/2.05  
% 5.32/2.05  %Foreground sorts:
% 5.32/2.05  
% 5.32/2.05  
% 5.32/2.05  %Background operators:
% 5.32/2.05  
% 5.32/2.05  
% 5.32/2.05  %Foreground operators:
% 5.32/2.05  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 5.32/2.05  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 5.32/2.05  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 5.32/2.05  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 5.32/2.05  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.32/2.05  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 5.32/2.05  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.32/2.05  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.32/2.05  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 5.32/2.05  tff(v5_ordinal1, type, v5_ordinal1: $i > $o).
% 5.32/2.05  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 5.32/2.05  tff('#skF_2', type, '#skF_2': $i).
% 5.32/2.05  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 5.32/2.05  tff('#skF_3', type, '#skF_3': $i).
% 5.32/2.05  tff('#skF_1', type, '#skF_1': $i).
% 5.32/2.05  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 5.32/2.05  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 5.32/2.05  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.32/2.05  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.32/2.05  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 5.32/2.05  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.32/2.05  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 5.32/2.05  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 5.32/2.05  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.32/2.05  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 5.32/2.05  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 5.32/2.05  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.32/2.05  
% 5.66/2.07  tff(f_159, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((v2_funct_1(C) & (k2_relset_1(A, B, C) = B)) => ((v1_funct_1(k2_funct_1(C)) & v1_funct_2(k2_funct_1(C), B, A)) & m1_subset_1(k2_funct_1(C), k1_zfmisc_1(k2_zfmisc_1(B, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_funct_2)).
% 5.66/2.07  tff(f_98, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 5.66/2.07  tff(f_112, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 5.66/2.07  tff(f_86, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k2_relat_1(A) = k1_relat_1(k2_funct_1(A))) & (k1_relat_1(A) = k2_relat_1(k2_funct_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_funct_1)).
% 5.66/2.07  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 5.66/2.07  tff(f_55, axiom, (![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_relat_1)).
% 5.66/2.07  tff(f_108, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 5.66/2.07  tff(f_130, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 5.66/2.07  tff(f_68, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 5.66/2.07  tff(f_41, axiom, (![A]: (v1_relat_1(A) => (k10_relat_1(A, k2_relat_1(A)) = k1_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t169_relat_1)).
% 5.66/2.07  tff(f_142, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r1_tarski(k2_relat_1(B), A) => ((v1_funct_1(B) & v1_funct_2(B, k1_relat_1(B), A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B), A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_funct_2)).
% 5.66/2.07  tff(f_33, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 5.66/2.07  tff(f_60, axiom, (k6_relat_1(k1_xboole_0) = k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t81_relat_1)).
% 5.66/2.07  tff(f_59, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 5.66/2.07  tff(c_78, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_159])).
% 5.66/2.07  tff(c_2384, plain, (![C_230, A_231, B_232]: (v1_relat_1(C_230) | ~m1_subset_1(C_230, k1_zfmisc_1(k2_zfmisc_1(A_231, B_232))))), inference(cnfTransformation, [status(thm)], [f_98])).
% 5.66/2.07  tff(c_2392, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_78, c_2384])).
% 5.66/2.07  tff(c_82, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_159])).
% 5.66/2.07  tff(c_76, plain, (v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_159])).
% 5.66/2.07  tff(c_74, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_2'), inference(cnfTransformation, [status(thm)], [f_159])).
% 5.66/2.07  tff(c_2558, plain, (![A_254, B_255, C_256]: (k2_relset_1(A_254, B_255, C_256)=k2_relat_1(C_256) | ~m1_subset_1(C_256, k1_zfmisc_1(k2_zfmisc_1(A_254, B_255))))), inference(cnfTransformation, [status(thm)], [f_112])).
% 5.66/2.07  tff(c_2564, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_78, c_2558])).
% 5.66/2.07  tff(c_2567, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_74, c_2564])).
% 5.66/2.07  tff(c_34, plain, (![A_14]: (k1_relat_1(k2_funct_1(A_14))=k2_relat_1(A_14) | ~v2_funct_1(A_14) | ~v1_funct_1(A_14) | ~v1_relat_1(A_14))), inference(cnfTransformation, [status(thm)], [f_86])).
% 5.66/2.07  tff(c_216, plain, (![C_48, A_49, B_50]: (v1_relat_1(C_48) | ~m1_subset_1(C_48, k1_zfmisc_1(k2_zfmisc_1(A_49, B_50))))), inference(cnfTransformation, [status(thm)], [f_98])).
% 5.66/2.07  tff(c_220, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_78, c_216])).
% 5.66/2.07  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.66/2.07  tff(c_339, plain, (![A_72, B_73, C_74]: (k2_relset_1(A_72, B_73, C_74)=k2_relat_1(C_74) | ~m1_subset_1(C_74, k1_zfmisc_1(k2_zfmisc_1(A_72, B_73))))), inference(cnfTransformation, [status(thm)], [f_112])).
% 5.66/2.07  tff(c_342, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_78, c_339])).
% 5.66/2.07  tff(c_344, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_74, c_342])).
% 5.66/2.07  tff(c_16, plain, (![A_9]: (k2_relat_1(A_9)!=k1_xboole_0 | k1_xboole_0=A_9 | ~v1_relat_1(A_9))), inference(cnfTransformation, [status(thm)], [f_55])).
% 5.66/2.07  tff(c_227, plain, (k2_relat_1('#skF_3')!=k1_xboole_0 | k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_220, c_16])).
% 5.66/2.07  tff(c_229, plain, (k2_relat_1('#skF_3')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_227])).
% 5.66/2.07  tff(c_346, plain, (k1_xboole_0!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_344, c_229])).
% 5.66/2.07  tff(c_80, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_159])).
% 5.66/2.07  tff(c_330, plain, (![A_69, B_70, C_71]: (k1_relset_1(A_69, B_70, C_71)=k1_relat_1(C_71) | ~m1_subset_1(C_71, k1_zfmisc_1(k2_zfmisc_1(A_69, B_70))))), inference(cnfTransformation, [status(thm)], [f_108])).
% 5.66/2.07  tff(c_334, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_78, c_330])).
% 5.66/2.07  tff(c_582, plain, (![B_97, A_98, C_99]: (k1_xboole_0=B_97 | k1_relset_1(A_98, B_97, C_99)=A_98 | ~v1_funct_2(C_99, A_98, B_97) | ~m1_subset_1(C_99, k1_zfmisc_1(k2_zfmisc_1(A_98, B_97))))), inference(cnfTransformation, [status(thm)], [f_130])).
% 5.66/2.07  tff(c_591, plain, (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_1' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_78, c_582])).
% 5.66/2.07  tff(c_598, plain, (k1_xboole_0='#skF_2' | k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_80, c_334, c_591])).
% 5.66/2.07  tff(c_599, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_346, c_598])).
% 5.66/2.07  tff(c_32, plain, (![A_14]: (k2_relat_1(k2_funct_1(A_14))=k1_relat_1(A_14) | ~v2_funct_1(A_14) | ~v1_funct_1(A_14) | ~v1_relat_1(A_14))), inference(cnfTransformation, [status(thm)], [f_86])).
% 5.66/2.07  tff(c_28, plain, (![A_11]: (v1_relat_1(k2_funct_1(A_11)) | ~v1_funct_1(A_11) | ~v1_relat_1(A_11))), inference(cnfTransformation, [status(thm)], [f_68])).
% 5.66/2.07  tff(c_301, plain, (![A_65]: (k2_relat_1(k2_funct_1(A_65))=k1_relat_1(A_65) | ~v2_funct_1(A_65) | ~v1_funct_1(A_65) | ~v1_relat_1(A_65))), inference(cnfTransformation, [status(thm)], [f_86])).
% 5.66/2.07  tff(c_12, plain, (![A_6]: (k10_relat_1(A_6, k2_relat_1(A_6))=k1_relat_1(A_6) | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_41])).
% 5.66/2.07  tff(c_1096, plain, (![A_138]: (k10_relat_1(k2_funct_1(A_138), k1_relat_1(A_138))=k1_relat_1(k2_funct_1(A_138)) | ~v1_relat_1(k2_funct_1(A_138)) | ~v2_funct_1(A_138) | ~v1_funct_1(A_138) | ~v1_relat_1(A_138))), inference(superposition, [status(thm), theory('equality')], [c_301, c_12])).
% 5.66/2.07  tff(c_1108, plain, (k10_relat_1(k2_funct_1('#skF_3'), '#skF_1')=k1_relat_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_599, c_1096])).
% 5.66/2.07  tff(c_1125, plain, (k10_relat_1(k2_funct_1('#skF_3'), '#skF_1')=k1_relat_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_220, c_82, c_76, c_1108])).
% 5.66/2.07  tff(c_1128, plain, (~v1_relat_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_1125])).
% 5.66/2.07  tff(c_1131, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_28, c_1128])).
% 5.66/2.07  tff(c_1135, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_220, c_82, c_1131])).
% 5.66/2.07  tff(c_1137, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_1125])).
% 5.66/2.07  tff(c_153, plain, (![A_41]: (v1_funct_1(k2_funct_1(A_41)) | ~v1_funct_1(A_41) | ~v1_relat_1(A_41))), inference(cnfTransformation, [status(thm)], [f_68])).
% 5.66/2.07  tff(c_72, plain, (~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | ~v1_funct_1(k2_funct_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_159])).
% 5.66/2.07  tff(c_152, plain, (~v1_funct_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_72])).
% 5.66/2.07  tff(c_156, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_153, c_152])).
% 5.66/2.07  tff(c_159, plain, (~v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_82, c_156])).
% 5.66/2.07  tff(c_182, plain, (![C_43, A_44, B_45]: (v1_relat_1(C_43) | ~m1_subset_1(C_43, k1_zfmisc_1(k2_zfmisc_1(A_44, B_45))))), inference(cnfTransformation, [status(thm)], [f_98])).
% 5.66/2.07  tff(c_185, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_78, c_182])).
% 5.66/2.07  tff(c_189, plain, $false, inference(negUnitSimplification, [status(thm)], [c_159, c_185])).
% 5.66/2.07  tff(c_191, plain, (v1_funct_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_72])).
% 5.66/2.07  tff(c_397, plain, (![B_83, A_84]: (m1_subset_1(B_83, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B_83), A_84))) | ~r1_tarski(k2_relat_1(B_83), A_84) | ~v1_funct_1(B_83) | ~v1_relat_1(B_83))), inference(cnfTransformation, [status(thm)], [f_142])).
% 5.66/2.07  tff(c_1429, plain, (![A_144, A_145]: (m1_subset_1(k2_funct_1(A_144), k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(A_144), A_145))) | ~r1_tarski(k2_relat_1(k2_funct_1(A_144)), A_145) | ~v1_funct_1(k2_funct_1(A_144)) | ~v1_relat_1(k2_funct_1(A_144)) | ~v2_funct_1(A_144) | ~v1_funct_1(A_144) | ~v1_relat_1(A_144))), inference(superposition, [status(thm), theory('equality')], [c_34, c_397])).
% 5.66/2.07  tff(c_1457, plain, (![A_145]: (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', A_145))) | ~r1_tarski(k2_relat_1(k2_funct_1('#skF_3')), A_145) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_344, c_1429])).
% 5.66/2.07  tff(c_1482, plain, (![A_146]: (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', A_146))) | ~r1_tarski(k2_relat_1(k2_funct_1('#skF_3')), A_146))), inference(demodulation, [status(thm), theory('equality')], [c_220, c_82, c_76, c_1137, c_191, c_1457])).
% 5.66/2.07  tff(c_190, plain, (~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | ~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(splitRight, [status(thm)], [c_72])).
% 5.66/2.07  tff(c_211, plain, (~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(splitLeft, [status(thm)], [c_190])).
% 5.66/2.07  tff(c_1523, plain, (~r1_tarski(k2_relat_1(k2_funct_1('#skF_3')), '#skF_1')), inference(resolution, [status(thm)], [c_1482, c_211])).
% 5.66/2.07  tff(c_1526, plain, (~r1_tarski(k1_relat_1('#skF_3'), '#skF_1') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_32, c_1523])).
% 5.66/2.07  tff(c_1529, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_220, c_82, c_76, c_6, c_599, c_1526])).
% 5.66/2.07  tff(c_1530, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_227])).
% 5.66/2.07  tff(c_8, plain, (![A_3]: (r1_tarski(k1_xboole_0, A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 5.66/2.07  tff(c_1594, plain, (![A_3]: (r1_tarski('#skF_3', A_3))), inference(demodulation, [status(thm), theory('equality')], [c_1530, c_8])).
% 5.66/2.07  tff(c_1531, plain, (k2_relat_1('#skF_3')=k1_xboole_0), inference(splitRight, [status(thm)], [c_227])).
% 5.66/2.07  tff(c_1606, plain, (k2_relat_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1530, c_1531])).
% 5.66/2.07  tff(c_24, plain, (k6_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_60])).
% 5.66/2.07  tff(c_91, plain, (![A_36]: (k1_relat_1(k6_relat_1(A_36))=A_36)), inference(cnfTransformation, [status(thm)], [f_59])).
% 5.66/2.07  tff(c_100, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_24, c_91])).
% 5.66/2.07  tff(c_1591, plain, (k1_relat_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1530, c_1530, c_100])).
% 5.66/2.07  tff(c_1880, plain, (![B_190, A_191]: (m1_subset_1(B_190, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B_190), A_191))) | ~r1_tarski(k2_relat_1(B_190), A_191) | ~v1_funct_1(B_190) | ~v1_relat_1(B_190))), inference(cnfTransformation, [status(thm)], [f_142])).
% 5.66/2.07  tff(c_1909, plain, (![A_191]: (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_3', A_191))) | ~r1_tarski(k2_relat_1('#skF_3'), A_191) | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_1591, c_1880])).
% 5.66/2.07  tff(c_1923, plain, (![A_191]: (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_3', A_191))))), inference(demodulation, [status(thm), theory('equality')], [c_220, c_82, c_1594, c_1606, c_1909])).
% 5.66/2.07  tff(c_143, plain, (![A_40]: (v1_relat_1(k2_funct_1(A_40)) | ~v1_funct_1(A_40) | ~v1_relat_1(A_40))), inference(cnfTransformation, [status(thm)], [f_68])).
% 5.66/2.07  tff(c_150, plain, (![A_40]: (k2_relat_1(k2_funct_1(A_40))!=k1_xboole_0 | k2_funct_1(A_40)=k1_xboole_0 | ~v1_funct_1(A_40) | ~v1_relat_1(A_40))), inference(resolution, [status(thm)], [c_143, c_16])).
% 5.66/2.07  tff(c_1758, plain, (![A_170]: (k2_relat_1(k2_funct_1(A_170))!='#skF_3' | k2_funct_1(A_170)='#skF_3' | ~v1_funct_1(A_170) | ~v1_relat_1(A_170))), inference(demodulation, [status(thm), theory('equality')], [c_1530, c_1530, c_150])).
% 5.66/2.07  tff(c_2366, plain, (![A_229]: (k1_relat_1(A_229)!='#skF_3' | k2_funct_1(A_229)='#skF_3' | ~v1_funct_1(A_229) | ~v1_relat_1(A_229) | ~v2_funct_1(A_229) | ~v1_funct_1(A_229) | ~v1_relat_1(A_229))), inference(superposition, [status(thm), theory('equality')], [c_32, c_1758])).
% 5.66/2.07  tff(c_2369, plain, (k1_relat_1('#skF_3')!='#skF_3' | k2_funct_1('#skF_3')='#skF_3' | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_76, c_2366])).
% 5.66/2.07  tff(c_2372, plain, (k2_funct_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_220, c_82, c_1591, c_2369])).
% 5.66/2.07  tff(c_1779, plain, (![A_176, B_177, C_178]: (k2_relset_1(A_176, B_177, C_178)=k2_relat_1(C_178) | ~m1_subset_1(C_178, k1_zfmisc_1(k2_zfmisc_1(A_176, B_177))))), inference(cnfTransformation, [status(thm)], [f_112])).
% 5.66/2.07  tff(c_1782, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_78, c_1779])).
% 5.66/2.07  tff(c_1784, plain, ('#skF_2'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1606, c_74, c_1782])).
% 5.66/2.07  tff(c_1786, plain, (~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_1784, c_211])).
% 5.66/2.07  tff(c_2373, plain, (~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_2372, c_1786])).
% 5.66/2.07  tff(c_2377, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1923, c_2373])).
% 5.66/2.07  tff(c_2378, plain, (~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_190])).
% 5.66/2.07  tff(c_2379, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(splitRight, [status(thm)], [c_190])).
% 5.66/2.07  tff(c_2549, plain, (![A_251, B_252, C_253]: (k1_relset_1(A_251, B_252, C_253)=k1_relat_1(C_253) | ~m1_subset_1(C_253, k1_zfmisc_1(k2_zfmisc_1(A_251, B_252))))), inference(cnfTransformation, [status(thm)], [f_108])).
% 5.66/2.07  tff(c_2556, plain, (k1_relset_1('#skF_2', '#skF_1', k2_funct_1('#skF_3'))=k1_relat_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_2379, c_2549])).
% 5.66/2.07  tff(c_2770, plain, (![B_276, C_277, A_278]: (k1_xboole_0=B_276 | v1_funct_2(C_277, A_278, B_276) | k1_relset_1(A_278, B_276, C_277)!=A_278 | ~m1_subset_1(C_277, k1_zfmisc_1(k2_zfmisc_1(A_278, B_276))))), inference(cnfTransformation, [status(thm)], [f_130])).
% 5.66/2.07  tff(c_2779, plain, (k1_xboole_0='#skF_1' | v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | k1_relset_1('#skF_2', '#skF_1', k2_funct_1('#skF_3'))!='#skF_2'), inference(resolution, [status(thm)], [c_2379, c_2770])).
% 5.66/2.07  tff(c_2788, plain, (k1_xboole_0='#skF_1' | v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | k1_relat_1(k2_funct_1('#skF_3'))!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_2556, c_2779])).
% 5.66/2.07  tff(c_2789, plain, (k1_xboole_0='#skF_1' | k1_relat_1(k2_funct_1('#skF_3'))!='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_2378, c_2788])).
% 5.66/2.07  tff(c_2793, plain, (k1_relat_1(k2_funct_1('#skF_3'))!='#skF_2'), inference(splitLeft, [status(thm)], [c_2789])).
% 5.66/2.07  tff(c_2796, plain, (k2_relat_1('#skF_3')!='#skF_2' | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_34, c_2793])).
% 5.66/2.07  tff(c_2799, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2392, c_82, c_76, c_2567, c_2796])).
% 5.66/2.07  tff(c_2800, plain, (k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_2789])).
% 5.66/2.07  tff(c_2409, plain, (k2_relat_1('#skF_3')!=k1_xboole_0 | k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_2392, c_16])).
% 5.66/2.07  tff(c_2432, plain, (k2_relat_1('#skF_3')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_2409])).
% 5.66/2.07  tff(c_2569, plain, (k1_xboole_0!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_2567, c_2432])).
% 5.66/2.07  tff(c_2814, plain, ('#skF_2'!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_2800, c_2569])).
% 5.66/2.07  tff(c_2557, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_78, c_2549])).
% 5.66/2.07  tff(c_64, plain, (![B_29, A_28, C_30]: (k1_xboole_0=B_29 | k1_relset_1(A_28, B_29, C_30)=A_28 | ~v1_funct_2(C_30, A_28, B_29) | ~m1_subset_1(C_30, k1_zfmisc_1(k2_zfmisc_1(A_28, B_29))))), inference(cnfTransformation, [status(thm)], [f_130])).
% 5.66/2.07  tff(c_2837, plain, (![B_279, A_280, C_281]: (B_279='#skF_1' | k1_relset_1(A_280, B_279, C_281)=A_280 | ~v1_funct_2(C_281, A_280, B_279) | ~m1_subset_1(C_281, k1_zfmisc_1(k2_zfmisc_1(A_280, B_279))))), inference(demodulation, [status(thm), theory('equality')], [c_2800, c_64])).
% 5.66/2.07  tff(c_2846, plain, ('#skF_2'='#skF_1' | k1_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_1' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_78, c_2837])).
% 5.66/2.07  tff(c_2852, plain, ('#skF_2'='#skF_1' | k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_80, c_2557, c_2846])).
% 5.66/2.07  tff(c_2867, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_2814, c_2852])).
% 5.66/2.07  tff(c_18, plain, (![A_9]: (k1_relat_1(A_9)!=k1_xboole_0 | k1_xboole_0=A_9 | ~v1_relat_1(A_9))), inference(cnfTransformation, [status(thm)], [f_55])).
% 5.66/2.07  tff(c_2410, plain, (k1_relat_1('#skF_3')!=k1_xboole_0 | k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_2392, c_18])).
% 5.66/2.07  tff(c_2433, plain, (k1_relat_1('#skF_3')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_2410])).
% 5.66/2.07  tff(c_2819, plain, (k1_relat_1('#skF_3')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_2800, c_2433])).
% 5.66/2.07  tff(c_2945, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2867, c_2819])).
% 5.66/2.07  tff(c_2946, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_2410])).
% 5.66/2.07  tff(c_107, plain, (![A_37]: (k2_relat_1(k6_relat_1(A_37))=A_37)), inference(cnfTransformation, [status(thm)], [f_59])).
% 5.66/2.07  tff(c_116, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_24, c_107])).
% 5.66/2.07  tff(c_2953, plain, (k2_relat_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_2946, c_2946, c_116])).
% 5.66/2.07  tff(c_2948, plain, (k2_relat_1('#skF_3')!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_2946, c_2432])).
% 5.66/2.07  tff(c_2998, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2953, c_2948])).
% 5.66/2.07  tff(c_2999, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_2409])).
% 5.66/2.07  tff(c_3021, plain, (![A_3]: (r1_tarski('#skF_3', A_3))), inference(demodulation, [status(thm), theory('equality')], [c_2999, c_8])).
% 5.66/2.07  tff(c_3000, plain, (k2_relat_1('#skF_3')=k1_xboole_0), inference(splitRight, [status(thm)], [c_2409])).
% 5.66/2.07  tff(c_3031, plain, (k2_relat_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_2999, c_3000])).
% 5.66/2.07  tff(c_3018, plain, (k1_relat_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_2999, c_2999, c_100])).
% 5.66/2.07  tff(c_3557, plain, (![B_324, A_325]: (v1_funct_2(B_324, k1_relat_1(B_324), A_325) | ~r1_tarski(k2_relat_1(B_324), A_325) | ~v1_funct_1(B_324) | ~v1_relat_1(B_324))), inference(cnfTransformation, [status(thm)], [f_142])).
% 5.66/2.07  tff(c_3563, plain, (![A_325]: (v1_funct_2('#skF_3', '#skF_3', A_325) | ~r1_tarski(k2_relat_1('#skF_3'), A_325) | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_3018, c_3557])).
% 5.66/2.07  tff(c_3568, plain, (![A_325]: (v1_funct_2('#skF_3', '#skF_3', A_325))), inference(demodulation, [status(thm), theory('equality')], [c_2392, c_82, c_3021, c_3031, c_3563])).
% 5.66/2.07  tff(c_3389, plain, (![A_318, B_319, C_320]: (k2_relset_1(A_318, B_319, C_320)=k2_relat_1(C_320) | ~m1_subset_1(C_320, k1_zfmisc_1(k2_zfmisc_1(A_318, B_319))))), inference(cnfTransformation, [status(thm)], [f_112])).
% 5.66/2.07  tff(c_3395, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_78, c_3389])).
% 5.66/2.07  tff(c_3399, plain, ('#skF_2'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_74, c_3031, c_3395])).
% 5.66/2.07  tff(c_3172, plain, (![A_300]: (k2_relat_1(k2_funct_1(A_300))=k1_relat_1(A_300) | ~v2_funct_1(A_300) | ~v1_funct_1(A_300) | ~v1_relat_1(A_300))), inference(cnfTransformation, [status(thm)], [f_86])).
% 5.66/2.07  tff(c_2391, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_2379, c_2384])).
% 5.66/2.07  tff(c_2417, plain, (k2_relat_1(k2_funct_1('#skF_3'))!=k1_xboole_0 | k2_funct_1('#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_2391, c_16])).
% 5.66/2.07  tff(c_3078, plain, (k2_relat_1(k2_funct_1('#skF_3'))!='#skF_3' | k2_funct_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_2999, c_2999, c_2417])).
% 5.66/2.07  tff(c_3079, plain, (k2_relat_1(k2_funct_1('#skF_3'))!='#skF_3'), inference(splitLeft, [status(thm)], [c_3078])).
% 5.66/2.07  tff(c_3178, plain, (k1_relat_1('#skF_3')!='#skF_3' | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_3172, c_3079])).
% 5.66/2.07  tff(c_3188, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2392, c_82, c_76, c_3018, c_3178])).
% 5.66/2.07  tff(c_3189, plain, (k2_funct_1('#skF_3')='#skF_3'), inference(splitRight, [status(thm)], [c_3078])).
% 5.66/2.07  tff(c_3194, plain, (~v1_funct_2('#skF_3', '#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_3189, c_2378])).
% 5.66/2.07  tff(c_3406, plain, (~v1_funct_2('#skF_3', '#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_3399, c_3194])).
% 5.66/2.07  tff(c_3581, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3568, c_3406])).
% 5.66/2.07  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.66/2.07  
% 5.66/2.07  Inference rules
% 5.66/2.07  ----------------------
% 5.66/2.07  #Ref     : 0
% 5.66/2.07  #Sup     : 799
% 5.66/2.07  #Fact    : 0
% 5.66/2.07  #Define  : 0
% 5.66/2.07  #Split   : 17
% 5.66/2.07  #Chain   : 0
% 5.66/2.07  #Close   : 0
% 5.66/2.07  
% 5.66/2.07  Ordering : KBO
% 5.66/2.07  
% 5.66/2.07  Simplification rules
% 5.66/2.07  ----------------------
% 5.66/2.07  #Subsume      : 55
% 5.66/2.07  #Demod        : 1127
% 5.66/2.07  #Tautology    : 471
% 5.66/2.07  #SimpNegUnit  : 11
% 5.66/2.07  #BackRed      : 111
% 5.66/2.07  
% 5.66/2.07  #Partial instantiations: 0
% 5.66/2.07  #Strategies tried      : 1
% 5.66/2.07  
% 5.66/2.07  Timing (in seconds)
% 5.66/2.07  ----------------------
% 5.66/2.08  Preprocessing        : 0.37
% 5.66/2.08  Parsing              : 0.19
% 5.66/2.08  CNF conversion       : 0.02
% 5.66/2.08  Main loop            : 0.92
% 5.66/2.08  Inferencing          : 0.33
% 5.66/2.08  Reduction            : 0.32
% 5.66/2.08  Demodulation         : 0.23
% 5.66/2.08  BG Simplification    : 0.04
% 5.66/2.08  Subsumption          : 0.15
% 5.66/2.08  Abstraction          : 0.04
% 5.66/2.08  MUC search           : 0.00
% 5.66/2.08  Cooper               : 0.00
% 5.66/2.08  Total                : 1.34
% 5.66/2.08  Index Insertion      : 0.00
% 5.66/2.08  Index Deletion       : 0.00
% 5.66/2.08  Index Matching       : 0.00
% 5.66/2.08  BG Taut test         : 0.00
%------------------------------------------------------------------------------
