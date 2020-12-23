%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:12:40 EST 2020

% Result     : Theorem 3.02s
% Output     : CNFRefutation 3.42s
% Verified   : 
% Statistics : Number of formulae       :  111 (1304 expanded)
%              Number of leaves         :   37 ( 437 expanded)
%              Depth                    :   14
%              Number of atoms          :  157 (3947 expanded)
%              Number of equality atoms :   59 ( 984 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k3_relset_1 > k2_relset_1 > k1_relset_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k4_relat_1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

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

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k4_relat_1,type,(
    k4_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_117,negated_conjecture,(
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

tff(f_54,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).

tff(f_58,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_46,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => k2_funct_1(A) = k4_relat_1(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_funct_1)).

tff(f_76,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k3_relset_1(A,B,C) = k4_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k3_relset_1)).

tff(f_68,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k3_relset_1(A,B,C),k1_zfmisc_1(k2_zfmisc_1(B,A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_relset_1)).

tff(f_82,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( k1_relset_1(B,A,k3_relset_1(A,B,C)) = k2_relset_1(A,B,C)
        & k2_relset_1(B,A,k3_relset_1(A,B,C)) = k1_relset_1(A,B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_relset_1)).

tff(f_100,axiom,(
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

tff(f_38,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_29,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k7_relat_1(A,k1_xboole_0) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t110_relat_1)).

tff(f_64,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_72,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(c_54,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_12,plain,(
    ! [A_5] :
      ( v1_funct_1(k2_funct_1(A_5))
      | ~ v1_funct_1(A_5)
      | ~ v1_relat_1(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_44,plain,
    ( ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_69,plain,(
    ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_44])).

tff(c_72,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_12,c_69])).

tff(c_75,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_72])).

tff(c_50,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_81,plain,(
    ! [C_30,A_31,B_32] :
      ( v1_relat_1(C_30)
      | ~ m1_subset_1(C_30,k1_zfmisc_1(k2_zfmisc_1(A_31,B_32))) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_84,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_50,c_81])).

tff(c_88,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_75,c_84])).

tff(c_89,plain,
    ( ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_109,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_89])).

tff(c_96,plain,(
    ! [C_34,A_35,B_36] :
      ( v1_relat_1(C_34)
      | ~ m1_subset_1(C_34,k1_zfmisc_1(k2_zfmisc_1(A_35,B_36))) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_100,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_50,c_96])).

tff(c_48,plain,(
    v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_121,plain,(
    ! [A_45] :
      ( k4_relat_1(A_45) = k2_funct_1(A_45)
      | ~ v2_funct_1(A_45)
      | ~ v1_funct_1(A_45)
      | ~ v1_relat_1(A_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_124,plain,
    ( k4_relat_1('#skF_3') = k2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_48,c_121])).

tff(c_127,plain,(
    k4_relat_1('#skF_3') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_54,c_124])).

tff(c_142,plain,(
    ! [A_46,B_47,C_48] :
      ( k3_relset_1(A_46,B_47,C_48) = k4_relat_1(C_48)
      | ~ m1_subset_1(C_48,k1_zfmisc_1(k2_zfmisc_1(A_46,B_47))) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_145,plain,(
    k3_relset_1('#skF_1','#skF_2','#skF_3') = k4_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_50,c_142])).

tff(c_147,plain,(
    k3_relset_1('#skF_1','#skF_2','#skF_3') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_127,c_145])).

tff(c_173,plain,(
    ! [A_56,B_57,C_58] :
      ( m1_subset_1(k3_relset_1(A_56,B_57,C_58),k1_zfmisc_1(k2_zfmisc_1(B_57,A_56)))
      | ~ m1_subset_1(C_58,k1_zfmisc_1(k2_zfmisc_1(A_56,B_57))) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_195,plain,
    ( m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_147,c_173])).

tff(c_203,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_195])).

tff(c_205,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_109,c_203])).

tff(c_206,plain,(
    ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_89])).

tff(c_280,plain,(
    ! [A_68] :
      ( k4_relat_1(A_68) = k2_funct_1(A_68)
      | ~ v2_funct_1(A_68)
      | ~ v1_funct_1(A_68)
      | ~ v1_relat_1(A_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_283,plain,
    ( k4_relat_1('#skF_3') = k2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_48,c_280])).

tff(c_286,plain,(
    k4_relat_1('#skF_3') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_54,c_283])).

tff(c_292,plain,(
    ! [A_70,B_71,C_72] :
      ( k3_relset_1(A_70,B_71,C_72) = k4_relat_1(C_72)
      | ~ m1_subset_1(C_72,k1_zfmisc_1(k2_zfmisc_1(A_70,B_71))) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_298,plain,(
    k3_relset_1('#skF_1','#skF_2','#skF_3') = k4_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_50,c_292])).

tff(c_301,plain,(
    k3_relset_1('#skF_1','#skF_2','#skF_3') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_286,c_298])).

tff(c_46,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_452,plain,(
    ! [B_88,A_89,C_90] :
      ( k1_relset_1(B_88,A_89,k3_relset_1(A_89,B_88,C_90)) = k2_relset_1(A_89,B_88,C_90)
      | ~ m1_subset_1(C_90,k1_zfmisc_1(k2_zfmisc_1(A_89,B_88))) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_460,plain,(
    k1_relset_1('#skF_2','#skF_1',k3_relset_1('#skF_1','#skF_2','#skF_3')) = k2_relset_1('#skF_1','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_50,c_452])).

tff(c_467,plain,(
    k1_relset_1('#skF_2','#skF_1',k2_funct_1('#skF_3')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_301,c_46,c_460])).

tff(c_207,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_89])).

tff(c_519,plain,(
    ! [B_91,C_92,A_93] :
      ( k1_xboole_0 = B_91
      | v1_funct_2(C_92,A_93,B_91)
      | k1_relset_1(A_93,B_91,C_92) != A_93
      | ~ m1_subset_1(C_92,k1_zfmisc_1(k2_zfmisc_1(A_93,B_91))) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_531,plain,
    ( k1_xboole_0 = '#skF_1'
    | v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | k1_relset_1('#skF_2','#skF_1',k2_funct_1('#skF_3')) != '#skF_2' ),
    inference(resolution,[status(thm)],[c_207,c_519])).

tff(c_542,plain,
    ( k1_xboole_0 = '#skF_1'
    | v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_467,c_531])).

tff(c_543,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_206,c_542])).

tff(c_6,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_559,plain,(
    k2_relat_1('#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_543,c_543,c_6])).

tff(c_2,plain,(
    ! [A_1] :
      ( k7_relat_1(A_1,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_104,plain,(
    k7_relat_1('#skF_3',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_100,c_2])).

tff(c_557,plain,(
    k7_relat_1('#skF_3','#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_543,c_543,c_104])).

tff(c_220,plain,(
    ! [C_59,A_60,B_61] :
      ( v4_relat_1(C_59,A_60)
      | ~ m1_subset_1(C_59,k1_zfmisc_1(k2_zfmisc_1(A_60,B_61))) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_228,plain,(
    v4_relat_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_50,c_220])).

tff(c_238,plain,(
    ! [B_65,A_66] :
      ( k7_relat_1(B_65,A_66) = B_65
      | ~ v4_relat_1(B_65,A_66)
      | ~ v1_relat_1(B_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_244,plain,
    ( k7_relat_1('#skF_3','#skF_1') = '#skF_3'
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_228,c_238])).

tff(c_250,plain,(
    k7_relat_1('#skF_3','#skF_1') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_244])).

tff(c_573,plain,(
    '#skF_3' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_557,c_250])).

tff(c_302,plain,(
    ! [A_73,B_74,C_75] :
      ( k2_relset_1(A_73,B_74,C_75) = k2_relat_1(C_75)
      | ~ m1_subset_1(C_75,k1_zfmisc_1(k2_zfmisc_1(A_73,B_74))) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_308,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_50,c_302])).

tff(c_311,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_308])).

tff(c_597,plain,(
    k2_relat_1('#skF_1') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_573,c_311])).

tff(c_614,plain,(
    '#skF_2' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_559,c_597])).

tff(c_52,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_611,plain,(
    v1_funct_2('#skF_1','#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_573,c_52])).

tff(c_638,plain,(
    v1_funct_2('#skF_1','#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_614,c_611])).

tff(c_16,plain,(
    ! [C_8,A_6,B_7] :
      ( v1_relat_1(C_8)
      | ~ m1_subset_1(C_8,k1_zfmisc_1(k2_zfmisc_1(A_6,B_7))) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_211,plain,(
    v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_207,c_16])).

tff(c_215,plain,(
    k7_relat_1(k2_funct_1('#skF_3'),k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_211,c_2])).

tff(c_556,plain,(
    k7_relat_1(k2_funct_1('#skF_3'),'#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_543,c_543,c_215])).

tff(c_712,plain,(
    k7_relat_1(k2_funct_1('#skF_1'),'#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_573,c_556])).

tff(c_227,plain,(
    v4_relat_1(k2_funct_1('#skF_3'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_207,c_220])).

tff(c_241,plain,
    ( k7_relat_1(k2_funct_1('#skF_3'),'#skF_2') = k2_funct_1('#skF_3')
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_227,c_238])).

tff(c_247,plain,(
    k7_relat_1(k2_funct_1('#skF_3'),'#skF_2') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_211,c_241])).

tff(c_599,plain,(
    k7_relat_1(k2_funct_1('#skF_1'),'#skF_2') = k2_funct_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_573,c_573,c_247])).

tff(c_772,plain,(
    k2_funct_1('#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_712,c_614,c_599])).

tff(c_606,plain,(
    ~ v1_funct_2(k2_funct_1('#skF_1'),'#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_573,c_206])).

tff(c_711,plain,(
    ~ v1_funct_2(k2_funct_1('#skF_1'),'#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_614,c_606])).

tff(c_779,plain,(
    ~ v1_funct_2('#skF_1','#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_772,c_711])).

tff(c_790,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_638,c_779])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:45:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.02/1.64  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.02/1.65  
% 3.02/1.65  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.02/1.66  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k3_relset_1 > k2_relset_1 > k1_relset_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k4_relat_1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 3.02/1.66  
% 3.02/1.66  %Foreground sorts:
% 3.02/1.66  
% 3.02/1.66  
% 3.02/1.66  %Background operators:
% 3.02/1.66  
% 3.02/1.66  
% 3.02/1.66  %Foreground operators:
% 3.02/1.66  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 3.02/1.66  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.02/1.66  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 3.02/1.66  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 3.02/1.66  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.02/1.66  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 3.02/1.66  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.02/1.66  tff(k3_relset_1, type, k3_relset_1: ($i * $i * $i) > $i).
% 3.02/1.66  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.02/1.66  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.02/1.66  tff('#skF_2', type, '#skF_2': $i).
% 3.02/1.66  tff('#skF_3', type, '#skF_3': $i).
% 3.02/1.66  tff('#skF_1', type, '#skF_1': $i).
% 3.02/1.66  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.02/1.66  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.02/1.66  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.02/1.66  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.02/1.66  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.02/1.66  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.02/1.66  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.02/1.66  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.02/1.66  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.02/1.66  tff(k4_relat_1, type, k4_relat_1: $i > $i).
% 3.02/1.66  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.02/1.66  
% 3.42/1.68  tff(f_117, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((v2_funct_1(C) & (k2_relset_1(A, B, C) = B)) => ((v1_funct_1(k2_funct_1(C)) & v1_funct_2(k2_funct_1(C), B, A)) & m1_subset_1(k2_funct_1(C), k1_zfmisc_1(k2_zfmisc_1(B, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_funct_2)).
% 3.42/1.68  tff(f_54, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 3.42/1.68  tff(f_58, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.42/1.68  tff(f_46, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => (k2_funct_1(A) = k4_relat_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d9_funct_1)).
% 3.42/1.68  tff(f_76, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k3_relset_1(A, B, C) = k4_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k3_relset_1)).
% 3.42/1.68  tff(f_68, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k3_relset_1(A, B, C), k1_zfmisc_1(k2_zfmisc_1(B, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k3_relset_1)).
% 3.42/1.68  tff(f_82, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((k1_relset_1(B, A, k3_relset_1(A, B, C)) = k2_relset_1(A, B, C)) & (k2_relset_1(B, A, k3_relset_1(A, B, C)) = k1_relset_1(A, B, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t24_relset_1)).
% 3.42/1.68  tff(f_100, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 3.42/1.68  tff(f_38, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 3.42/1.68  tff(f_29, axiom, (![A]: (v1_relat_1(A) => (k7_relat_1(A, k1_xboole_0) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t110_relat_1)).
% 3.42/1.68  tff(f_64, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.42/1.68  tff(f_35, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t209_relat_1)).
% 3.42/1.68  tff(f_72, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 3.42/1.68  tff(c_54, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_117])).
% 3.42/1.68  tff(c_12, plain, (![A_5]: (v1_funct_1(k2_funct_1(A_5)) | ~v1_funct_1(A_5) | ~v1_relat_1(A_5))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.42/1.68  tff(c_44, plain, (~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | ~v1_funct_1(k2_funct_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_117])).
% 3.42/1.68  tff(c_69, plain, (~v1_funct_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_44])).
% 3.42/1.68  tff(c_72, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_12, c_69])).
% 3.42/1.68  tff(c_75, plain, (~v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_72])).
% 3.42/1.68  tff(c_50, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_117])).
% 3.42/1.68  tff(c_81, plain, (![C_30, A_31, B_32]: (v1_relat_1(C_30) | ~m1_subset_1(C_30, k1_zfmisc_1(k2_zfmisc_1(A_31, B_32))))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.42/1.68  tff(c_84, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_50, c_81])).
% 3.42/1.68  tff(c_88, plain, $false, inference(negUnitSimplification, [status(thm)], [c_75, c_84])).
% 3.42/1.68  tff(c_89, plain, (~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | ~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(splitRight, [status(thm)], [c_44])).
% 3.42/1.68  tff(c_109, plain, (~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(splitLeft, [status(thm)], [c_89])).
% 3.42/1.68  tff(c_96, plain, (![C_34, A_35, B_36]: (v1_relat_1(C_34) | ~m1_subset_1(C_34, k1_zfmisc_1(k2_zfmisc_1(A_35, B_36))))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.42/1.68  tff(c_100, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_50, c_96])).
% 3.42/1.68  tff(c_48, plain, (v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_117])).
% 3.42/1.68  tff(c_121, plain, (![A_45]: (k4_relat_1(A_45)=k2_funct_1(A_45) | ~v2_funct_1(A_45) | ~v1_funct_1(A_45) | ~v1_relat_1(A_45))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.42/1.68  tff(c_124, plain, (k4_relat_1('#skF_3')=k2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_48, c_121])).
% 3.42/1.68  tff(c_127, plain, (k4_relat_1('#skF_3')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_100, c_54, c_124])).
% 3.42/1.68  tff(c_142, plain, (![A_46, B_47, C_48]: (k3_relset_1(A_46, B_47, C_48)=k4_relat_1(C_48) | ~m1_subset_1(C_48, k1_zfmisc_1(k2_zfmisc_1(A_46, B_47))))), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.42/1.68  tff(c_145, plain, (k3_relset_1('#skF_1', '#skF_2', '#skF_3')=k4_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_50, c_142])).
% 3.42/1.68  tff(c_147, plain, (k3_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_127, c_145])).
% 3.42/1.68  tff(c_173, plain, (![A_56, B_57, C_58]: (m1_subset_1(k3_relset_1(A_56, B_57, C_58), k1_zfmisc_1(k2_zfmisc_1(B_57, A_56))) | ~m1_subset_1(C_58, k1_zfmisc_1(k2_zfmisc_1(A_56, B_57))))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.42/1.68  tff(c_195, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_147, c_173])).
% 3.42/1.68  tff(c_203, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_195])).
% 3.42/1.68  tff(c_205, plain, $false, inference(negUnitSimplification, [status(thm)], [c_109, c_203])).
% 3.42/1.68  tff(c_206, plain, (~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_89])).
% 3.42/1.68  tff(c_280, plain, (![A_68]: (k4_relat_1(A_68)=k2_funct_1(A_68) | ~v2_funct_1(A_68) | ~v1_funct_1(A_68) | ~v1_relat_1(A_68))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.42/1.68  tff(c_283, plain, (k4_relat_1('#skF_3')=k2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_48, c_280])).
% 3.42/1.68  tff(c_286, plain, (k4_relat_1('#skF_3')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_100, c_54, c_283])).
% 3.42/1.68  tff(c_292, plain, (![A_70, B_71, C_72]: (k3_relset_1(A_70, B_71, C_72)=k4_relat_1(C_72) | ~m1_subset_1(C_72, k1_zfmisc_1(k2_zfmisc_1(A_70, B_71))))), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.42/1.68  tff(c_298, plain, (k3_relset_1('#skF_1', '#skF_2', '#skF_3')=k4_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_50, c_292])).
% 3.42/1.68  tff(c_301, plain, (k3_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_286, c_298])).
% 3.42/1.68  tff(c_46, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_2'), inference(cnfTransformation, [status(thm)], [f_117])).
% 3.42/1.68  tff(c_452, plain, (![B_88, A_89, C_90]: (k1_relset_1(B_88, A_89, k3_relset_1(A_89, B_88, C_90))=k2_relset_1(A_89, B_88, C_90) | ~m1_subset_1(C_90, k1_zfmisc_1(k2_zfmisc_1(A_89, B_88))))), inference(cnfTransformation, [status(thm)], [f_82])).
% 3.42/1.68  tff(c_460, plain, (k1_relset_1('#skF_2', '#skF_1', k3_relset_1('#skF_1', '#skF_2', '#skF_3'))=k2_relset_1('#skF_1', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_50, c_452])).
% 3.42/1.68  tff(c_467, plain, (k1_relset_1('#skF_2', '#skF_1', k2_funct_1('#skF_3'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_301, c_46, c_460])).
% 3.42/1.68  tff(c_207, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(splitRight, [status(thm)], [c_89])).
% 3.42/1.68  tff(c_519, plain, (![B_91, C_92, A_93]: (k1_xboole_0=B_91 | v1_funct_2(C_92, A_93, B_91) | k1_relset_1(A_93, B_91, C_92)!=A_93 | ~m1_subset_1(C_92, k1_zfmisc_1(k2_zfmisc_1(A_93, B_91))))), inference(cnfTransformation, [status(thm)], [f_100])).
% 3.42/1.68  tff(c_531, plain, (k1_xboole_0='#skF_1' | v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | k1_relset_1('#skF_2', '#skF_1', k2_funct_1('#skF_3'))!='#skF_2'), inference(resolution, [status(thm)], [c_207, c_519])).
% 3.42/1.68  tff(c_542, plain, (k1_xboole_0='#skF_1' | v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_467, c_531])).
% 3.42/1.68  tff(c_543, plain, (k1_xboole_0='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_206, c_542])).
% 3.42/1.68  tff(c_6, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.42/1.68  tff(c_559, plain, (k2_relat_1('#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_543, c_543, c_6])).
% 3.42/1.68  tff(c_2, plain, (![A_1]: (k7_relat_1(A_1, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.42/1.68  tff(c_104, plain, (k7_relat_1('#skF_3', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_100, c_2])).
% 3.42/1.68  tff(c_557, plain, (k7_relat_1('#skF_3', '#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_543, c_543, c_104])).
% 3.42/1.68  tff(c_220, plain, (![C_59, A_60, B_61]: (v4_relat_1(C_59, A_60) | ~m1_subset_1(C_59, k1_zfmisc_1(k2_zfmisc_1(A_60, B_61))))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.42/1.68  tff(c_228, plain, (v4_relat_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_50, c_220])).
% 3.42/1.68  tff(c_238, plain, (![B_65, A_66]: (k7_relat_1(B_65, A_66)=B_65 | ~v4_relat_1(B_65, A_66) | ~v1_relat_1(B_65))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.42/1.68  tff(c_244, plain, (k7_relat_1('#skF_3', '#skF_1')='#skF_3' | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_228, c_238])).
% 3.42/1.68  tff(c_250, plain, (k7_relat_1('#skF_3', '#skF_1')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_100, c_244])).
% 3.42/1.68  tff(c_573, plain, ('#skF_3'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_557, c_250])).
% 3.42/1.68  tff(c_302, plain, (![A_73, B_74, C_75]: (k2_relset_1(A_73, B_74, C_75)=k2_relat_1(C_75) | ~m1_subset_1(C_75, k1_zfmisc_1(k2_zfmisc_1(A_73, B_74))))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.42/1.68  tff(c_308, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_50, c_302])).
% 3.42/1.68  tff(c_311, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_46, c_308])).
% 3.42/1.68  tff(c_597, plain, (k2_relat_1('#skF_1')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_573, c_311])).
% 3.42/1.68  tff(c_614, plain, ('#skF_2'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_559, c_597])).
% 3.42/1.68  tff(c_52, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_117])).
% 3.42/1.68  tff(c_611, plain, (v1_funct_2('#skF_1', '#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_573, c_52])).
% 3.42/1.68  tff(c_638, plain, (v1_funct_2('#skF_1', '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_614, c_611])).
% 3.42/1.68  tff(c_16, plain, (![C_8, A_6, B_7]: (v1_relat_1(C_8) | ~m1_subset_1(C_8, k1_zfmisc_1(k2_zfmisc_1(A_6, B_7))))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.42/1.68  tff(c_211, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_207, c_16])).
% 3.42/1.68  tff(c_215, plain, (k7_relat_1(k2_funct_1('#skF_3'), k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_211, c_2])).
% 3.42/1.68  tff(c_556, plain, (k7_relat_1(k2_funct_1('#skF_3'), '#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_543, c_543, c_215])).
% 3.42/1.68  tff(c_712, plain, (k7_relat_1(k2_funct_1('#skF_1'), '#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_573, c_556])).
% 3.42/1.68  tff(c_227, plain, (v4_relat_1(k2_funct_1('#skF_3'), '#skF_2')), inference(resolution, [status(thm)], [c_207, c_220])).
% 3.42/1.68  tff(c_241, plain, (k7_relat_1(k2_funct_1('#skF_3'), '#skF_2')=k2_funct_1('#skF_3') | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_227, c_238])).
% 3.42/1.68  tff(c_247, plain, (k7_relat_1(k2_funct_1('#skF_3'), '#skF_2')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_211, c_241])).
% 3.42/1.68  tff(c_599, plain, (k7_relat_1(k2_funct_1('#skF_1'), '#skF_2')=k2_funct_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_573, c_573, c_247])).
% 3.42/1.68  tff(c_772, plain, (k2_funct_1('#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_712, c_614, c_599])).
% 3.42/1.68  tff(c_606, plain, (~v1_funct_2(k2_funct_1('#skF_1'), '#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_573, c_206])).
% 3.42/1.68  tff(c_711, plain, (~v1_funct_2(k2_funct_1('#skF_1'), '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_614, c_606])).
% 3.42/1.68  tff(c_779, plain, (~v1_funct_2('#skF_1', '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_772, c_711])).
% 3.42/1.68  tff(c_790, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_638, c_779])).
% 3.42/1.68  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.42/1.68  
% 3.42/1.68  Inference rules
% 3.42/1.68  ----------------------
% 3.42/1.68  #Ref     : 0
% 3.42/1.68  #Sup     : 174
% 3.42/1.68  #Fact    : 0
% 3.42/1.68  #Define  : 0
% 3.42/1.68  #Split   : 4
% 3.42/1.68  #Chain   : 0
% 3.42/1.68  #Close   : 0
% 3.42/1.68  
% 3.42/1.68  Ordering : KBO
% 3.42/1.68  
% 3.42/1.68  Simplification rules
% 3.42/1.68  ----------------------
% 3.42/1.68  #Subsume      : 1
% 3.42/1.68  #Demod        : 169
% 3.42/1.68  #Tautology    : 96
% 3.42/1.68  #SimpNegUnit  : 4
% 3.42/1.68  #BackRed      : 64
% 3.42/1.68  
% 3.42/1.68  #Partial instantiations: 0
% 3.42/1.68  #Strategies tried      : 1
% 3.42/1.68  
% 3.42/1.68  Timing (in seconds)
% 3.42/1.68  ----------------------
% 3.42/1.68  Preprocessing        : 0.39
% 3.42/1.68  Parsing              : 0.21
% 3.42/1.68  CNF conversion       : 0.02
% 3.42/1.68  Main loop            : 0.37
% 3.42/1.68  Inferencing          : 0.12
% 3.42/1.68  Reduction            : 0.12
% 3.42/1.68  Demodulation         : 0.09
% 3.42/1.68  BG Simplification    : 0.02
% 3.42/1.68  Subsumption          : 0.07
% 3.42/1.68  Abstraction          : 0.02
% 3.42/1.68  MUC search           : 0.00
% 3.42/1.68  Cooper               : 0.00
% 3.42/1.68  Total                : 0.81
% 3.42/1.68  Index Insertion      : 0.00
% 3.42/1.68  Index Deletion       : 0.00
% 3.42/1.68  Index Matching       : 0.00
% 3.42/1.68  BG Taut test         : 0.00
%------------------------------------------------------------------------------
