%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:12:52 EST 2020

% Result     : Theorem 4.44s
% Output     : CNFRefutation 4.84s
% Verified   : 
% Statistics : Number of formulae       :  133 (2544 expanded)
%              Number of leaves         :   33 ( 790 expanded)
%              Depth                    :   22
%              Number of atoms          :  222 (7574 expanded)
%              Number of equality atoms :   78 (1833 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k3_relset_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k4_relat_1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_relset_1,type,(
    k3_relset_1: ( $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k4_relat_1,type,(
    k4_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_119,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( ( v2_funct_1(C)
            & k2_relset_1(A,B,C) = B )
         => ( v1_funct_1(k2_funct_1(C))
            & v1_funct_2(k2_funct_1(C),B,A)
            & m1_subset_1(k2_funct_1(C),k1_zfmisc_1(k2_zfmisc_1(B,A))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_funct_2)).

tff(f_56,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).

tff(f_34,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_32,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_48,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => k2_funct_1(A) = k4_relat_1(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_funct_1)).

tff(f_68,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k3_relset_1(A,B,C) = k4_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k3_relset_1)).

tff(f_60,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k3_relset_1(A,B,C),k1_zfmisc_1(k2_zfmisc_1(B,A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_relset_1)).

tff(f_64,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_40,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( k2_relat_1(A) = k1_relat_1(k4_relat_1(A))
        & k1_relat_1(A) = k2_relat_1(k4_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_relat_1)).

tff(f_92,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).

tff(f_74,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( k1_relset_1(B,A,k3_relset_1(A,B,C)) = k2_relset_1(A,B,C)
        & k2_relset_1(B,A,k3_relset_1(A,B,C)) = k1_relset_1(A,B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_relset_1)).

tff(f_102,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_funct_1(A)
        & v1_funct_2(A,k1_relat_1(A),k2_relat_1(A))
        & m1_subset_1(A,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A)))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_funct_2)).

tff(c_54,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_12,plain,(
    ! [A_8] :
      ( v1_funct_1(k2_funct_1(A_8))
      | ~ v1_funct_1(A_8)
      | ~ v1_relat_1(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_44,plain,
    ( ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_79,plain,(
    ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_44])).

tff(c_82,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_12,c_79])).

tff(c_85,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_82])).

tff(c_4,plain,(
    ! [A_4,B_5] : v1_relat_1(k2_zfmisc_1(A_4,B_5)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_50,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_87,plain,(
    ! [B_31,A_32] :
      ( v1_relat_1(B_31)
      | ~ m1_subset_1(B_31,k1_zfmisc_1(A_32))
      | ~ v1_relat_1(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_90,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_50,c_87])).

tff(c_93,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_90])).

tff(c_95,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_85,c_93])).

tff(c_96,plain,
    ( ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_113,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_96])).

tff(c_99,plain,(
    ! [B_34,A_35] :
      ( v1_relat_1(B_34)
      | ~ m1_subset_1(B_34,k1_zfmisc_1(A_35))
      | ~ v1_relat_1(A_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_102,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_50,c_99])).

tff(c_105,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_102])).

tff(c_48,plain,(
    v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_114,plain,(
    ! [A_37] :
      ( k4_relat_1(A_37) = k2_funct_1(A_37)
      | ~ v2_funct_1(A_37)
      | ~ v1_funct_1(A_37)
      | ~ v1_relat_1(A_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_117,plain,
    ( k4_relat_1('#skF_3') = k2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_48,c_114])).

tff(c_120,plain,(
    k4_relat_1('#skF_3') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_105,c_54,c_117])).

tff(c_153,plain,(
    ! [A_38,B_39,C_40] :
      ( k3_relset_1(A_38,B_39,C_40) = k4_relat_1(C_40)
      | ~ m1_subset_1(C_40,k1_zfmisc_1(k2_zfmisc_1(A_38,B_39))) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_156,plain,(
    k3_relset_1('#skF_1','#skF_2','#skF_3') = k4_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_50,c_153])).

tff(c_158,plain,(
    k3_relset_1('#skF_1','#skF_2','#skF_3') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_120,c_156])).

tff(c_299,plain,(
    ! [A_54,B_55,C_56] :
      ( m1_subset_1(k3_relset_1(A_54,B_55,C_56),k1_zfmisc_1(k2_zfmisc_1(B_55,A_54)))
      | ~ m1_subset_1(C_56,k1_zfmisc_1(k2_zfmisc_1(A_54,B_55))) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_329,plain,
    ( m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_158,c_299])).

tff(c_341,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_329])).

tff(c_343,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_113,c_341])).

tff(c_344,plain,(
    ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_96])).

tff(c_52,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_453,plain,(
    ! [A_63,B_64,C_65] :
      ( k1_relset_1(A_63,B_64,C_65) = k1_relat_1(C_65)
      | ~ m1_subset_1(C_65,k1_zfmisc_1(k2_zfmisc_1(A_63,B_64))) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_471,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_50,c_453])).

tff(c_352,plain,(
    ! [A_57] :
      ( k4_relat_1(A_57) = k2_funct_1(A_57)
      | ~ v2_funct_1(A_57)
      | ~ v1_funct_1(A_57)
      | ~ v1_relat_1(A_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_355,plain,
    ( k4_relat_1('#skF_3') = k2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_48,c_352])).

tff(c_358,plain,(
    k4_relat_1('#skF_3') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_105,c_54,c_355])).

tff(c_8,plain,(
    ! [A_6] :
      ( k1_relat_1(k4_relat_1(A_6)) = k2_relat_1(A_6)
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_362,plain,
    ( k1_relat_1(k2_funct_1('#skF_3')) = k2_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_358,c_8])).

tff(c_369,plain,(
    k1_relat_1(k2_funct_1('#skF_3')) = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_105,c_362])).

tff(c_345,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_96])).

tff(c_462,plain,(
    k1_relset_1('#skF_2','#skF_1',k2_funct_1('#skF_3')) = k1_relat_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_345,c_453])).

tff(c_470,plain,(
    k1_relset_1('#skF_2','#skF_1',k2_funct_1('#skF_3')) = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_369,c_462])).

tff(c_739,plain,(
    ! [B_82,C_83,A_84] :
      ( k1_xboole_0 = B_82
      | v1_funct_2(C_83,A_84,B_82)
      | k1_relset_1(A_84,B_82,C_83) != A_84
      | ~ m1_subset_1(C_83,k1_zfmisc_1(k2_zfmisc_1(A_84,B_82))) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_763,plain,
    ( k1_xboole_0 = '#skF_1'
    | v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | k1_relset_1('#skF_2','#skF_1',k2_funct_1('#skF_3')) != '#skF_2' ),
    inference(resolution,[status(thm)],[c_345,c_739])).

tff(c_780,plain,
    ( k1_xboole_0 = '#skF_1'
    | v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | k2_relat_1('#skF_3') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_470,c_763])).

tff(c_781,plain,
    ( k1_xboole_0 = '#skF_1'
    | k2_relat_1('#skF_3') != '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_344,c_780])).

tff(c_784,plain,(
    k2_relat_1('#skF_3') != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_781])).

tff(c_373,plain,(
    ! [A_58,B_59,C_60] :
      ( k3_relset_1(A_58,B_59,C_60) = k4_relat_1(C_60)
      | ~ m1_subset_1(C_60,k1_zfmisc_1(k2_zfmisc_1(A_58,B_59))) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_379,plain,(
    k3_relset_1('#skF_1','#skF_2','#skF_3') = k4_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_50,c_373])).

tff(c_382,plain,(
    k3_relset_1('#skF_1','#skF_2','#skF_3') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_358,c_379])).

tff(c_46,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_1029,plain,(
    ! [B_95,A_96,C_97] :
      ( k1_relset_1(B_95,A_96,k3_relset_1(A_96,B_95,C_97)) = k2_relset_1(A_96,B_95,C_97)
      | ~ m1_subset_1(C_97,k1_zfmisc_1(k2_zfmisc_1(A_96,B_95))) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_1051,plain,(
    k1_relset_1('#skF_2','#skF_1',k3_relset_1('#skF_1','#skF_2','#skF_3')) = k2_relset_1('#skF_1','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_50,c_1029])).

tff(c_1070,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_470,c_382,c_46,c_1051])).

tff(c_1072,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_784,c_1070])).

tff(c_1073,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_781])).

tff(c_36,plain,(
    ! [B_22,A_21,C_23] :
      ( k1_xboole_0 = B_22
      | k1_relset_1(A_21,B_22,C_23) = A_21
      | ~ v1_funct_2(C_23,A_21,B_22)
      | ~ m1_subset_1(C_23,k1_zfmisc_1(k2_zfmisc_1(A_21,B_22))) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_1177,plain,(
    ! [B_98,A_99,C_100] :
      ( B_98 = '#skF_1'
      | k1_relset_1(A_99,B_98,C_100) = A_99
      | ~ v1_funct_2(C_100,A_99,B_98)
      | ~ m1_subset_1(C_100,k1_zfmisc_1(k2_zfmisc_1(A_99,B_98))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1073,c_36])).

tff(c_1201,plain,
    ( '#skF_2' = '#skF_1'
    | k1_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_1'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_50,c_1177])).

tff(c_1217,plain,
    ( '#skF_2' = '#skF_1'
    | k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_471,c_1201])).

tff(c_1218,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_1217])).

tff(c_2,plain,(
    ! [B_3,A_1] :
      ( v1_relat_1(B_3)
      | ~ m1_subset_1(B_3,k1_zfmisc_1(A_1))
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_348,plain,
    ( v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_1')) ),
    inference(resolution,[status(thm)],[c_345,c_2])).

tff(c_351,plain,(
    v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_348])).

tff(c_97,plain,(
    v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_6,plain,(
    ! [A_6] :
      ( k2_relat_1(k4_relat_1(A_6)) = k1_relat_1(A_6)
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_365,plain,
    ( k2_relat_1(k2_funct_1('#skF_3')) = k1_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_358,c_6])).

tff(c_371,plain,(
    k2_relat_1(k2_funct_1('#skF_3')) = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_105,c_365])).

tff(c_1074,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_781])).

tff(c_1092,plain,(
    k1_relat_1(k2_funct_1('#skF_3')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1074,c_369])).

tff(c_40,plain,(
    ! [A_24] :
      ( v1_funct_2(A_24,k1_relat_1(A_24),k2_relat_1(A_24))
      | ~ v1_funct_1(A_24)
      | ~ v1_relat_1(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_1137,plain,
    ( v1_funct_2(k2_funct_1('#skF_3'),'#skF_2',k2_relat_1(k2_funct_1('#skF_3')))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1092,c_40])).

tff(c_1149,plain,(
    v1_funct_2(k2_funct_1('#skF_3'),'#skF_2',k1_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_351,c_97,c_371,c_1137])).

tff(c_1221,plain,(
    v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1218,c_1149])).

tff(c_1228,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_344,c_1221])).

tff(c_1230,plain,(
    k1_relat_1('#skF_3') != '#skF_1' ),
    inference(splitRight,[status(thm)],[c_1217])).

tff(c_1229,plain,(
    '#skF_2' = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_1217])).

tff(c_1108,plain,
    ( v1_funct_2('#skF_3',k1_relat_1('#skF_3'),'#skF_2')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1074,c_40])).

tff(c_1120,plain,(
    v1_funct_2('#skF_3',k1_relat_1('#skF_3'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_105,c_54,c_1108])).

tff(c_1234,plain,(
    v1_funct_2('#skF_3',k1_relat_1('#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1229,c_1120])).

tff(c_38,plain,(
    ! [A_24] :
      ( m1_subset_1(A_24,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_24),k2_relat_1(A_24))))
      | ~ v1_funct_1(A_24)
      | ~ v1_relat_1(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_1105,plain,
    ( m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),'#skF_2')))
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1074,c_38])).

tff(c_1118,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),'#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_105,c_54,c_1105])).

tff(c_1231,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),'#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1229,c_1118])).

tff(c_28,plain,(
    ! [C_23,A_21] :
      ( k1_xboole_0 = C_23
      | ~ v1_funct_2(C_23,A_21,k1_xboole_0)
      | k1_xboole_0 = A_21
      | ~ m1_subset_1(C_23,k1_zfmisc_1(k2_zfmisc_1(A_21,k1_xboole_0))) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_2274,plain,(
    ! [C_123,A_124] :
      ( C_123 = '#skF_1'
      | ~ v1_funct_2(C_123,A_124,'#skF_1')
      | A_124 = '#skF_1'
      | ~ m1_subset_1(C_123,k1_zfmisc_1(k2_zfmisc_1(A_124,'#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1073,c_1073,c_1073,c_1073,c_28])).

tff(c_2292,plain,
    ( '#skF_3' = '#skF_1'
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),'#skF_1')
    | k1_relat_1('#skF_3') = '#skF_1' ),
    inference(resolution,[status(thm)],[c_1231,c_2274])).

tff(c_2314,plain,
    ( '#skF_3' = '#skF_1'
    | k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1234,c_2292])).

tff(c_2315,plain,(
    '#skF_3' = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_1230,c_2314])).

tff(c_1250,plain,(
    ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1229,c_344])).

tff(c_2364,plain,(
    ~ v1_funct_2(k2_funct_1('#skF_1'),'#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2315,c_1250])).

tff(c_1088,plain,(
    k1_relset_1('#skF_2','#skF_1',k2_funct_1('#skF_3')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1074,c_470])).

tff(c_1235,plain,(
    k1_relset_1('#skF_1','#skF_1',k2_funct_1('#skF_3')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1229,c_1229,c_1088])).

tff(c_2358,plain,(
    k1_relset_1('#skF_1','#skF_1',k2_funct_1('#skF_1')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2315,c_1235])).

tff(c_1249,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1229,c_345])).

tff(c_2355,plain,(
    m1_subset_1(k2_funct_1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2315,c_1249])).

tff(c_30,plain,(
    ! [C_23,B_22] :
      ( v1_funct_2(C_23,k1_xboole_0,B_22)
      | k1_relset_1(k1_xboole_0,B_22,C_23) != k1_xboole_0
      | ~ m1_subset_1(C_23,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_22))) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_3096,plain,(
    ! [C_140,B_141] :
      ( v1_funct_2(C_140,'#skF_1',B_141)
      | k1_relset_1('#skF_1',B_141,C_140) != '#skF_1'
      | ~ m1_subset_1(C_140,k1_zfmisc_1(k2_zfmisc_1('#skF_1',B_141))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1073,c_1073,c_1073,c_1073,c_30])).

tff(c_3099,plain,
    ( v1_funct_2(k2_funct_1('#skF_1'),'#skF_1','#skF_1')
    | k1_relset_1('#skF_1','#skF_1',k2_funct_1('#skF_1')) != '#skF_1' ),
    inference(resolution,[status(thm)],[c_2355,c_3096])).

tff(c_3109,plain,(
    v1_funct_2(k2_funct_1('#skF_1'),'#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2358,c_3099])).

tff(c_3111,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2364,c_3109])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n006.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 12:31:52 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.44/1.88  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.44/1.89  
% 4.44/1.89  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.44/1.89  %$ v1_funct_2 > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k3_relset_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k4_relat_1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 4.44/1.89  
% 4.44/1.89  %Foreground sorts:
% 4.44/1.89  
% 4.44/1.89  
% 4.44/1.89  %Background operators:
% 4.44/1.89  
% 4.44/1.89  
% 4.44/1.89  %Foreground operators:
% 4.44/1.89  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 4.44/1.89  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.44/1.89  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 4.44/1.89  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 4.44/1.89  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.44/1.89  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.44/1.89  tff(k3_relset_1, type, k3_relset_1: ($i * $i * $i) > $i).
% 4.44/1.89  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 4.44/1.89  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.44/1.89  tff('#skF_2', type, '#skF_2': $i).
% 4.44/1.89  tff('#skF_3', type, '#skF_3': $i).
% 4.44/1.89  tff('#skF_1', type, '#skF_1': $i).
% 4.44/1.89  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 4.44/1.89  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.44/1.89  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.44/1.89  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.44/1.89  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.44/1.89  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.44/1.89  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.44/1.89  tff(k4_relat_1, type, k4_relat_1: $i > $i).
% 4.44/1.89  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.44/1.89  
% 4.84/1.91  tff(f_119, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((v2_funct_1(C) & (k2_relset_1(A, B, C) = B)) => ((v1_funct_1(k2_funct_1(C)) & v1_funct_2(k2_funct_1(C), B, A)) & m1_subset_1(k2_funct_1(C), k1_zfmisc_1(k2_zfmisc_1(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_funct_2)).
% 4.84/1.91  tff(f_56, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 4.84/1.91  tff(f_34, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 4.84/1.91  tff(f_32, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 4.84/1.91  tff(f_48, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => (k2_funct_1(A) = k4_relat_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d9_funct_1)).
% 4.84/1.91  tff(f_68, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k3_relset_1(A, B, C) = k4_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k3_relset_1)).
% 4.84/1.91  tff(f_60, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k3_relset_1(A, B, C), k1_zfmisc_1(k2_zfmisc_1(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k3_relset_1)).
% 4.84/1.91  tff(f_64, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 4.84/1.91  tff(f_40, axiom, (![A]: (v1_relat_1(A) => ((k2_relat_1(A) = k1_relat_1(k4_relat_1(A))) & (k1_relat_1(A) = k2_relat_1(k4_relat_1(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t37_relat_1)).
% 4.84/1.91  tff(f_92, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 4.84/1.91  tff(f_74, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((k1_relset_1(B, A, k3_relset_1(A, B, C)) = k2_relset_1(A, B, C)) & (k2_relset_1(B, A, k3_relset_1(A, B, C)) = k1_relset_1(A, B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t24_relset_1)).
% 4.84/1.91  tff(f_102, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => ((v1_funct_1(A) & v1_funct_2(A, k1_relat_1(A), k2_relat_1(A))) & m1_subset_1(A, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_funct_2)).
% 4.84/1.91  tff(c_54, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_119])).
% 4.84/1.91  tff(c_12, plain, (![A_8]: (v1_funct_1(k2_funct_1(A_8)) | ~v1_funct_1(A_8) | ~v1_relat_1(A_8))), inference(cnfTransformation, [status(thm)], [f_56])).
% 4.84/1.91  tff(c_44, plain, (~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | ~v1_funct_1(k2_funct_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_119])).
% 4.84/1.91  tff(c_79, plain, (~v1_funct_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_44])).
% 4.84/1.91  tff(c_82, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_12, c_79])).
% 4.84/1.91  tff(c_85, plain, (~v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_82])).
% 4.84/1.91  tff(c_4, plain, (![A_4, B_5]: (v1_relat_1(k2_zfmisc_1(A_4, B_5)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 4.84/1.91  tff(c_50, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_119])).
% 4.84/1.91  tff(c_87, plain, (![B_31, A_32]: (v1_relat_1(B_31) | ~m1_subset_1(B_31, k1_zfmisc_1(A_32)) | ~v1_relat_1(A_32))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.84/1.91  tff(c_90, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_50, c_87])).
% 4.84/1.91  tff(c_93, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_90])).
% 4.84/1.91  tff(c_95, plain, $false, inference(negUnitSimplification, [status(thm)], [c_85, c_93])).
% 4.84/1.91  tff(c_96, plain, (~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | ~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(splitRight, [status(thm)], [c_44])).
% 4.84/1.91  tff(c_113, plain, (~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(splitLeft, [status(thm)], [c_96])).
% 4.84/1.91  tff(c_99, plain, (![B_34, A_35]: (v1_relat_1(B_34) | ~m1_subset_1(B_34, k1_zfmisc_1(A_35)) | ~v1_relat_1(A_35))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.84/1.91  tff(c_102, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_50, c_99])).
% 4.84/1.91  tff(c_105, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_102])).
% 4.84/1.91  tff(c_48, plain, (v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_119])).
% 4.84/1.91  tff(c_114, plain, (![A_37]: (k4_relat_1(A_37)=k2_funct_1(A_37) | ~v2_funct_1(A_37) | ~v1_funct_1(A_37) | ~v1_relat_1(A_37))), inference(cnfTransformation, [status(thm)], [f_48])).
% 4.84/1.91  tff(c_117, plain, (k4_relat_1('#skF_3')=k2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_48, c_114])).
% 4.84/1.91  tff(c_120, plain, (k4_relat_1('#skF_3')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_105, c_54, c_117])).
% 4.84/1.91  tff(c_153, plain, (![A_38, B_39, C_40]: (k3_relset_1(A_38, B_39, C_40)=k4_relat_1(C_40) | ~m1_subset_1(C_40, k1_zfmisc_1(k2_zfmisc_1(A_38, B_39))))), inference(cnfTransformation, [status(thm)], [f_68])).
% 4.84/1.91  tff(c_156, plain, (k3_relset_1('#skF_1', '#skF_2', '#skF_3')=k4_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_50, c_153])).
% 4.84/1.91  tff(c_158, plain, (k3_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_120, c_156])).
% 4.84/1.91  tff(c_299, plain, (![A_54, B_55, C_56]: (m1_subset_1(k3_relset_1(A_54, B_55, C_56), k1_zfmisc_1(k2_zfmisc_1(B_55, A_54))) | ~m1_subset_1(C_56, k1_zfmisc_1(k2_zfmisc_1(A_54, B_55))))), inference(cnfTransformation, [status(thm)], [f_60])).
% 4.84/1.91  tff(c_329, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_158, c_299])).
% 4.84/1.91  tff(c_341, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_329])).
% 4.84/1.91  tff(c_343, plain, $false, inference(negUnitSimplification, [status(thm)], [c_113, c_341])).
% 4.84/1.91  tff(c_344, plain, (~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_96])).
% 4.84/1.91  tff(c_52, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_119])).
% 4.84/1.91  tff(c_453, plain, (![A_63, B_64, C_65]: (k1_relset_1(A_63, B_64, C_65)=k1_relat_1(C_65) | ~m1_subset_1(C_65, k1_zfmisc_1(k2_zfmisc_1(A_63, B_64))))), inference(cnfTransformation, [status(thm)], [f_64])).
% 4.84/1.91  tff(c_471, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_50, c_453])).
% 4.84/1.91  tff(c_352, plain, (![A_57]: (k4_relat_1(A_57)=k2_funct_1(A_57) | ~v2_funct_1(A_57) | ~v1_funct_1(A_57) | ~v1_relat_1(A_57))), inference(cnfTransformation, [status(thm)], [f_48])).
% 4.84/1.91  tff(c_355, plain, (k4_relat_1('#skF_3')=k2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_48, c_352])).
% 4.84/1.91  tff(c_358, plain, (k4_relat_1('#skF_3')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_105, c_54, c_355])).
% 4.84/1.91  tff(c_8, plain, (![A_6]: (k1_relat_1(k4_relat_1(A_6))=k2_relat_1(A_6) | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_40])).
% 4.84/1.91  tff(c_362, plain, (k1_relat_1(k2_funct_1('#skF_3'))=k2_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_358, c_8])).
% 4.84/1.91  tff(c_369, plain, (k1_relat_1(k2_funct_1('#skF_3'))=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_105, c_362])).
% 4.84/1.91  tff(c_345, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(splitRight, [status(thm)], [c_96])).
% 4.84/1.91  tff(c_462, plain, (k1_relset_1('#skF_2', '#skF_1', k2_funct_1('#skF_3'))=k1_relat_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_345, c_453])).
% 4.84/1.91  tff(c_470, plain, (k1_relset_1('#skF_2', '#skF_1', k2_funct_1('#skF_3'))=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_369, c_462])).
% 4.84/1.91  tff(c_739, plain, (![B_82, C_83, A_84]: (k1_xboole_0=B_82 | v1_funct_2(C_83, A_84, B_82) | k1_relset_1(A_84, B_82, C_83)!=A_84 | ~m1_subset_1(C_83, k1_zfmisc_1(k2_zfmisc_1(A_84, B_82))))), inference(cnfTransformation, [status(thm)], [f_92])).
% 4.84/1.91  tff(c_763, plain, (k1_xboole_0='#skF_1' | v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | k1_relset_1('#skF_2', '#skF_1', k2_funct_1('#skF_3'))!='#skF_2'), inference(resolution, [status(thm)], [c_345, c_739])).
% 4.84/1.91  tff(c_780, plain, (k1_xboole_0='#skF_1' | v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | k2_relat_1('#skF_3')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_470, c_763])).
% 4.84/1.91  tff(c_781, plain, (k1_xboole_0='#skF_1' | k2_relat_1('#skF_3')!='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_344, c_780])).
% 4.84/1.91  tff(c_784, plain, (k2_relat_1('#skF_3')!='#skF_2'), inference(splitLeft, [status(thm)], [c_781])).
% 4.84/1.91  tff(c_373, plain, (![A_58, B_59, C_60]: (k3_relset_1(A_58, B_59, C_60)=k4_relat_1(C_60) | ~m1_subset_1(C_60, k1_zfmisc_1(k2_zfmisc_1(A_58, B_59))))), inference(cnfTransformation, [status(thm)], [f_68])).
% 4.84/1.91  tff(c_379, plain, (k3_relset_1('#skF_1', '#skF_2', '#skF_3')=k4_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_50, c_373])).
% 4.84/1.91  tff(c_382, plain, (k3_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_358, c_379])).
% 4.84/1.91  tff(c_46, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_2'), inference(cnfTransformation, [status(thm)], [f_119])).
% 4.84/1.91  tff(c_1029, plain, (![B_95, A_96, C_97]: (k1_relset_1(B_95, A_96, k3_relset_1(A_96, B_95, C_97))=k2_relset_1(A_96, B_95, C_97) | ~m1_subset_1(C_97, k1_zfmisc_1(k2_zfmisc_1(A_96, B_95))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 4.84/1.91  tff(c_1051, plain, (k1_relset_1('#skF_2', '#skF_1', k3_relset_1('#skF_1', '#skF_2', '#skF_3'))=k2_relset_1('#skF_1', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_50, c_1029])).
% 4.84/1.91  tff(c_1070, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_470, c_382, c_46, c_1051])).
% 4.84/1.91  tff(c_1072, plain, $false, inference(negUnitSimplification, [status(thm)], [c_784, c_1070])).
% 4.84/1.91  tff(c_1073, plain, (k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_781])).
% 4.84/1.91  tff(c_36, plain, (![B_22, A_21, C_23]: (k1_xboole_0=B_22 | k1_relset_1(A_21, B_22, C_23)=A_21 | ~v1_funct_2(C_23, A_21, B_22) | ~m1_subset_1(C_23, k1_zfmisc_1(k2_zfmisc_1(A_21, B_22))))), inference(cnfTransformation, [status(thm)], [f_92])).
% 4.84/1.91  tff(c_1177, plain, (![B_98, A_99, C_100]: (B_98='#skF_1' | k1_relset_1(A_99, B_98, C_100)=A_99 | ~v1_funct_2(C_100, A_99, B_98) | ~m1_subset_1(C_100, k1_zfmisc_1(k2_zfmisc_1(A_99, B_98))))), inference(demodulation, [status(thm), theory('equality')], [c_1073, c_36])).
% 4.84/1.91  tff(c_1201, plain, ('#skF_2'='#skF_1' | k1_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_1' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_50, c_1177])).
% 4.84/1.91  tff(c_1217, plain, ('#skF_2'='#skF_1' | k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_52, c_471, c_1201])).
% 4.84/1.91  tff(c_1218, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(splitLeft, [status(thm)], [c_1217])).
% 4.84/1.91  tff(c_2, plain, (![B_3, A_1]: (v1_relat_1(B_3) | ~m1_subset_1(B_3, k1_zfmisc_1(A_1)) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.84/1.91  tff(c_348, plain, (v1_relat_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_1'))), inference(resolution, [status(thm)], [c_345, c_2])).
% 4.84/1.91  tff(c_351, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_348])).
% 4.84/1.91  tff(c_97, plain, (v1_funct_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_44])).
% 4.84/1.91  tff(c_6, plain, (![A_6]: (k2_relat_1(k4_relat_1(A_6))=k1_relat_1(A_6) | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_40])).
% 4.84/1.91  tff(c_365, plain, (k2_relat_1(k2_funct_1('#skF_3'))=k1_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_358, c_6])).
% 4.84/1.91  tff(c_371, plain, (k2_relat_1(k2_funct_1('#skF_3'))=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_105, c_365])).
% 4.84/1.91  tff(c_1074, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(splitRight, [status(thm)], [c_781])).
% 4.84/1.91  tff(c_1092, plain, (k1_relat_1(k2_funct_1('#skF_3'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_1074, c_369])).
% 4.84/1.91  tff(c_40, plain, (![A_24]: (v1_funct_2(A_24, k1_relat_1(A_24), k2_relat_1(A_24)) | ~v1_funct_1(A_24) | ~v1_relat_1(A_24))), inference(cnfTransformation, [status(thm)], [f_102])).
% 4.84/1.91  tff(c_1137, plain, (v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', k2_relat_1(k2_funct_1('#skF_3'))) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_1092, c_40])).
% 4.84/1.91  tff(c_1149, plain, (v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', k1_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_351, c_97, c_371, c_1137])).
% 4.84/1.91  tff(c_1221, plain, (v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1218, c_1149])).
% 4.84/1.91  tff(c_1228, plain, $false, inference(negUnitSimplification, [status(thm)], [c_344, c_1221])).
% 4.84/1.91  tff(c_1230, plain, (k1_relat_1('#skF_3')!='#skF_1'), inference(splitRight, [status(thm)], [c_1217])).
% 4.84/1.91  tff(c_1229, plain, ('#skF_2'='#skF_1'), inference(splitRight, [status(thm)], [c_1217])).
% 4.84/1.91  tff(c_1108, plain, (v1_funct_2('#skF_3', k1_relat_1('#skF_3'), '#skF_2') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1074, c_40])).
% 4.84/1.91  tff(c_1120, plain, (v1_funct_2('#skF_3', k1_relat_1('#skF_3'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_105, c_54, c_1108])).
% 4.84/1.91  tff(c_1234, plain, (v1_funct_2('#skF_3', k1_relat_1('#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1229, c_1120])).
% 4.84/1.91  tff(c_38, plain, (![A_24]: (m1_subset_1(A_24, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_24), k2_relat_1(A_24)))) | ~v1_funct_1(A_24) | ~v1_relat_1(A_24))), inference(cnfTransformation, [status(thm)], [f_102])).
% 4.84/1.91  tff(c_1105, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), '#skF_2'))) | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1074, c_38])).
% 4.84/1.91  tff(c_1118, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_105, c_54, c_1105])).
% 4.84/1.91  tff(c_1231, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_1229, c_1118])).
% 4.84/1.91  tff(c_28, plain, (![C_23, A_21]: (k1_xboole_0=C_23 | ~v1_funct_2(C_23, A_21, k1_xboole_0) | k1_xboole_0=A_21 | ~m1_subset_1(C_23, k1_zfmisc_1(k2_zfmisc_1(A_21, k1_xboole_0))))), inference(cnfTransformation, [status(thm)], [f_92])).
% 4.84/1.91  tff(c_2274, plain, (![C_123, A_124]: (C_123='#skF_1' | ~v1_funct_2(C_123, A_124, '#skF_1') | A_124='#skF_1' | ~m1_subset_1(C_123, k1_zfmisc_1(k2_zfmisc_1(A_124, '#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_1073, c_1073, c_1073, c_1073, c_28])).
% 4.84/1.91  tff(c_2292, plain, ('#skF_3'='#skF_1' | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), '#skF_1') | k1_relat_1('#skF_3')='#skF_1'), inference(resolution, [status(thm)], [c_1231, c_2274])).
% 4.84/1.91  tff(c_2314, plain, ('#skF_3'='#skF_1' | k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_1234, c_2292])).
% 4.84/1.91  tff(c_2315, plain, ('#skF_3'='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_1230, c_2314])).
% 4.84/1.91  tff(c_1250, plain, (~v1_funct_2(k2_funct_1('#skF_3'), '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1229, c_344])).
% 4.84/1.91  tff(c_2364, plain, (~v1_funct_2(k2_funct_1('#skF_1'), '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2315, c_1250])).
% 4.84/1.91  tff(c_1088, plain, (k1_relset_1('#skF_2', '#skF_1', k2_funct_1('#skF_3'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_1074, c_470])).
% 4.84/1.91  tff(c_1235, plain, (k1_relset_1('#skF_1', '#skF_1', k2_funct_1('#skF_3'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_1229, c_1229, c_1088])).
% 4.84/1.91  tff(c_2358, plain, (k1_relset_1('#skF_1', '#skF_1', k2_funct_1('#skF_1'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_2315, c_1235])).
% 4.84/1.91  tff(c_1249, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_1229, c_345])).
% 4.84/1.91  tff(c_2355, plain, (m1_subset_1(k2_funct_1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_2315, c_1249])).
% 4.84/1.91  tff(c_30, plain, (![C_23, B_22]: (v1_funct_2(C_23, k1_xboole_0, B_22) | k1_relset_1(k1_xboole_0, B_22, C_23)!=k1_xboole_0 | ~m1_subset_1(C_23, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_22))))), inference(cnfTransformation, [status(thm)], [f_92])).
% 4.84/1.91  tff(c_3096, plain, (![C_140, B_141]: (v1_funct_2(C_140, '#skF_1', B_141) | k1_relset_1('#skF_1', B_141, C_140)!='#skF_1' | ~m1_subset_1(C_140, k1_zfmisc_1(k2_zfmisc_1('#skF_1', B_141))))), inference(demodulation, [status(thm), theory('equality')], [c_1073, c_1073, c_1073, c_1073, c_30])).
% 4.84/1.91  tff(c_3099, plain, (v1_funct_2(k2_funct_1('#skF_1'), '#skF_1', '#skF_1') | k1_relset_1('#skF_1', '#skF_1', k2_funct_1('#skF_1'))!='#skF_1'), inference(resolution, [status(thm)], [c_2355, c_3096])).
% 4.84/1.91  tff(c_3109, plain, (v1_funct_2(k2_funct_1('#skF_1'), '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2358, c_3099])).
% 4.84/1.91  tff(c_3111, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2364, c_3109])).
% 4.84/1.91  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.84/1.91  
% 4.84/1.91  Inference rules
% 4.84/1.91  ----------------------
% 4.84/1.91  #Ref     : 0
% 4.84/1.91  #Sup     : 710
% 4.84/1.91  #Fact    : 0
% 4.84/1.91  #Define  : 0
% 4.84/1.91  #Split   : 12
% 4.84/1.91  #Chain   : 0
% 4.84/1.91  #Close   : 0
% 4.84/1.91  
% 4.84/1.91  Ordering : KBO
% 4.84/1.91  
% 4.84/1.91  Simplification rules
% 4.84/1.91  ----------------------
% 4.84/1.91  #Subsume      : 40
% 4.84/1.91  #Demod        : 1130
% 4.84/1.91  #Tautology    : 366
% 4.84/1.91  #SimpNegUnit  : 23
% 4.84/1.91  #BackRed      : 122
% 4.84/1.91  
% 4.84/1.91  #Partial instantiations: 0
% 4.84/1.91  #Strategies tried      : 1
% 4.84/1.91  
% 4.84/1.91  Timing (in seconds)
% 4.84/1.91  ----------------------
% 4.84/1.92  Preprocessing        : 0.34
% 4.84/1.92  Parsing              : 0.18
% 4.84/1.92  CNF conversion       : 0.02
% 4.84/1.92  Main loop            : 0.75
% 4.84/1.92  Inferencing          : 0.24
% 4.84/1.92  Reduction            : 0.28
% 4.84/1.92  Demodulation         : 0.21
% 4.84/1.92  BG Simplification    : 0.03
% 4.84/1.92  Subsumption          : 0.12
% 4.84/1.92  Abstraction          : 0.04
% 4.84/1.92  MUC search           : 0.00
% 4.84/1.92  Cooper               : 0.00
% 4.84/1.92  Total                : 1.13
% 4.84/1.92  Index Insertion      : 0.00
% 4.84/1.92  Index Deletion       : 0.00
% 4.84/1.92  Index Matching       : 0.00
% 4.84/1.92  BG Taut test         : 0.00
%------------------------------------------------------------------------------
