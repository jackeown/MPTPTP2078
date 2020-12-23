%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:12:32 EST 2020

% Result     : Theorem 5.17s
% Output     : CNFRefutation 5.60s
% Verified   : 
% Statistics : Number of formulae       :  233 (1800 expanded)
%              Number of leaves         :   40 ( 593 expanded)
%              Depth                    :   13
%              Number of atoms          :  441 (4606 expanded)
%              Number of equality atoms :   98 ( 828 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v1_partfun1 > r2_hidden > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(v1_partfun1,type,(
    v1_partfun1: ( $i * $i ) > $o )).

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

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_172,negated_conjecture,(
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

tff(f_95,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => v1_xboole_0(C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc3_relset_1)).

tff(f_57,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_55,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_110,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_88,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k2_relat_1(A) = k1_relat_1(k2_funct_1(A))
          & k1_relat_1(A) = k2_relat_1(k2_funct_1(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).

tff(f_102,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(B,A)))
         => v1_xboole_0(C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc4_relset_1)).

tff(f_74,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).

tff(f_106,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_145,axiom,(
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

tff(f_155,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_funct_1(A)
        & v1_funct_2(A,k1_relat_1(A),k2_relat_1(A))
        & m1_subset_1(A,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A)))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_funct_2)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_34,axiom,(
    ! [A,B] :
      ~ ( v1_xboole_0(A)
        & A != B
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_boole)).

tff(f_42,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_40,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_127,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => v1_partfun1(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_partfun1)).

tff(f_120,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( ( v1_funct_1(C)
          & v1_partfun1(C,A) )
       => ( v1_funct_1(C)
          & v1_funct_2(C,A,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_funct_2)).

tff(c_72,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_172])).

tff(c_210,plain,(
    ! [C_67,A_68,B_69] :
      ( v1_xboole_0(C_67)
      | ~ m1_subset_1(C_67,k1_zfmisc_1(k2_zfmisc_1(A_68,B_69)))
      | ~ v1_xboole_0(A_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_224,plain,
    ( v1_xboole_0('#skF_4')
    | ~ v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_72,c_210])).

tff(c_229,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_224])).

tff(c_18,plain,(
    ! [A_12,B_13] : v1_relat_1(k2_zfmisc_1(A_12,B_13)) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_171,plain,(
    ! [B_61,A_62] :
      ( v1_relat_1(B_61)
      | ~ m1_subset_1(B_61,k1_zfmisc_1(A_62))
      | ~ v1_relat_1(A_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_174,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_72,c_171])).

tff(c_180,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_174])).

tff(c_76,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_172])).

tff(c_70,plain,(
    v2_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_172])).

tff(c_68,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_4') = '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_172])).

tff(c_1375,plain,(
    ! [A_179,B_180,C_181] :
      ( k2_relset_1(A_179,B_180,C_181) = k2_relat_1(C_181)
      | ~ m1_subset_1(C_181,k1_zfmisc_1(k2_zfmisc_1(A_179,B_180))) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_1381,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_72,c_1375])).

tff(c_1394,plain,(
    k2_relat_1('#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_1381])).

tff(c_32,plain,(
    ! [A_18] :
      ( k1_relat_1(k2_funct_1(A_18)) = k2_relat_1(A_18)
      | ~ v2_funct_1(A_18)
      | ~ v1_funct_1(A_18)
      | ~ v1_relat_1(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_183,plain,(
    ! [C_63,B_64,A_65] :
      ( v1_xboole_0(C_63)
      | ~ m1_subset_1(C_63,k1_zfmisc_1(k2_zfmisc_1(B_64,A_65)))
      | ~ v1_xboole_0(A_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_197,plain,
    ( v1_xboole_0('#skF_4')
    | ~ v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_72,c_183])).

tff(c_202,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_197])).

tff(c_22,plain,(
    ! [A_17] :
      ( v1_funct_1(k2_funct_1(A_17))
      | ~ v1_funct_1(A_17)
      | ~ v1_relat_1(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_66,plain,
    ( ~ m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2')))
    | ~ v1_funct_2(k2_funct_1('#skF_4'),'#skF_3','#skF_2')
    | ~ v1_funct_1(k2_funct_1('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_172])).

tff(c_128,plain,(
    ~ v1_funct_1(k2_funct_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_66])).

tff(c_131,plain,
    ( ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_22,c_128])).

tff(c_134,plain,(
    ~ v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_131])).

tff(c_146,plain,(
    ! [B_57,A_58] :
      ( v1_relat_1(B_57)
      | ~ m1_subset_1(B_57,k1_zfmisc_1(A_58))
      | ~ v1_relat_1(A_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_149,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_72,c_146])).

tff(c_155,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_149])).

tff(c_157,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_134,c_155])).

tff(c_158,plain,
    ( ~ v1_funct_2(k2_funct_1('#skF_4'),'#skF_3','#skF_2')
    | ~ m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_66])).

tff(c_260,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_158])).

tff(c_74,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_172])).

tff(c_451,plain,(
    ! [A_97,B_98,C_99] :
      ( k1_relset_1(A_97,B_98,C_99) = k1_relat_1(C_99)
      | ~ m1_subset_1(C_99,k1_zfmisc_1(k2_zfmisc_1(A_97,B_98))) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_473,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_72,c_451])).

tff(c_729,plain,(
    ! [B_130,A_131,C_132] :
      ( k1_xboole_0 = B_130
      | k1_relset_1(A_131,B_130,C_132) = A_131
      | ~ v1_funct_2(C_132,A_131,B_130)
      | ~ m1_subset_1(C_132,k1_zfmisc_1(k2_zfmisc_1(A_131,B_130))) ) ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_738,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relset_1('#skF_2','#skF_3','#skF_4') = '#skF_2'
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_72,c_729])).

tff(c_755,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relat_1('#skF_4') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_473,c_738])).

tff(c_759,plain,(
    k1_relat_1('#skF_4') = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_755])).

tff(c_30,plain,(
    ! [A_18] :
      ( k2_relat_1(k2_funct_1(A_18)) = k1_relat_1(A_18)
      | ~ v2_funct_1(A_18)
      | ~ v1_funct_1(A_18)
      | ~ v1_relat_1(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_24,plain,(
    ! [A_17] :
      ( v1_relat_1(k2_funct_1(A_17))
      | ~ v1_funct_1(A_17)
      | ~ v1_relat_1(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_159,plain,(
    v1_funct_1(k2_funct_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_66])).

tff(c_362,plain,(
    ! [A_90,B_91,C_92] :
      ( k2_relset_1(A_90,B_91,C_92) = k2_relat_1(C_92)
      | ~ m1_subset_1(C_92,k1_zfmisc_1(k2_zfmisc_1(A_90,B_91))) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_368,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_72,c_362])).

tff(c_381,plain,(
    k2_relat_1('#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_368])).

tff(c_283,plain,(
    ! [A_81] :
      ( k1_relat_1(k2_funct_1(A_81)) = k2_relat_1(A_81)
      | ~ v2_funct_1(A_81)
      | ~ v1_funct_1(A_81)
      | ~ v1_relat_1(A_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_62,plain,(
    ! [A_43] :
      ( v1_funct_2(A_43,k1_relat_1(A_43),k2_relat_1(A_43))
      | ~ v1_funct_1(A_43)
      | ~ v1_relat_1(A_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_976,plain,(
    ! [A_152] :
      ( v1_funct_2(k2_funct_1(A_152),k2_relat_1(A_152),k2_relat_1(k2_funct_1(A_152)))
      | ~ v1_funct_1(k2_funct_1(A_152))
      | ~ v1_relat_1(k2_funct_1(A_152))
      | ~ v2_funct_1(A_152)
      | ~ v1_funct_1(A_152)
      | ~ v1_relat_1(A_152) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_283,c_62])).

tff(c_979,plain,
    ( v1_funct_2(k2_funct_1('#skF_4'),'#skF_3',k2_relat_1(k2_funct_1('#skF_4')))
    | ~ v1_funct_1(k2_funct_1('#skF_4'))
    | ~ v1_relat_1(k2_funct_1('#skF_4'))
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_381,c_976])).

tff(c_987,plain,
    ( v1_funct_2(k2_funct_1('#skF_4'),'#skF_3',k2_relat_1(k2_funct_1('#skF_4')))
    | ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_180,c_76,c_70,c_159,c_979])).

tff(c_988,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_987])).

tff(c_991,plain,
    ( ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_24,c_988])).

tff(c_995,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_180,c_76,c_991])).

tff(c_997,plain,(
    v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_987])).

tff(c_313,plain,(
    ! [A_85] :
      ( m1_subset_1(A_85,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_85),k2_relat_1(A_85))))
      | ~ v1_funct_1(A_85)
      | ~ v1_relat_1(A_85) ) ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_1112,plain,(
    ! [A_158] :
      ( m1_subset_1(k2_funct_1(A_158),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(A_158),k2_relat_1(k2_funct_1(A_158)))))
      | ~ v1_funct_1(k2_funct_1(A_158))
      | ~ v1_relat_1(k2_funct_1(A_158))
      | ~ v2_funct_1(A_158)
      | ~ v1_funct_1(A_158)
      | ~ v1_relat_1(A_158) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_313])).

tff(c_1147,plain,
    ( m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_3',k2_relat_1(k2_funct_1('#skF_4')))))
    | ~ v1_funct_1(k2_funct_1('#skF_4'))
    | ~ v1_relat_1(k2_funct_1('#skF_4'))
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_381,c_1112])).

tff(c_1170,plain,(
    m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_3',k2_relat_1(k2_funct_1('#skF_4'))))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_180,c_76,c_70,c_997,c_159,c_1147])).

tff(c_1205,plain,
    ( m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_3',k1_relat_1('#skF_4'))))
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_1170])).

tff(c_1227,plain,(
    m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_180,c_76,c_70,c_759,c_1205])).

tff(c_1229,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_260,c_1227])).

tff(c_1230,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_755])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_1258,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1230,c_2])).

tff(c_1260,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_202,c_1258])).

tff(c_1261,plain,(
    ~ v1_funct_2(k2_funct_1('#skF_4'),'#skF_3','#skF_2') ),
    inference(splitRight,[status(thm)],[c_158])).

tff(c_1262,plain,(
    m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_158])).

tff(c_1355,plain,(
    ! [A_176,B_177,C_178] :
      ( k1_relset_1(A_176,B_177,C_178) = k1_relat_1(C_178)
      | ~ m1_subset_1(C_178,k1_zfmisc_1(k2_zfmisc_1(A_176,B_177))) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_1372,plain,(
    k1_relset_1('#skF_3','#skF_2',k2_funct_1('#skF_4')) = k1_relat_1(k2_funct_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_1262,c_1355])).

tff(c_1726,plain,(
    ! [B_214,C_215,A_216] :
      ( k1_xboole_0 = B_214
      | v1_funct_2(C_215,A_216,B_214)
      | k1_relset_1(A_216,B_214,C_215) != A_216
      | ~ m1_subset_1(C_215,k1_zfmisc_1(k2_zfmisc_1(A_216,B_214))) ) ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_1735,plain,
    ( k1_xboole_0 = '#skF_2'
    | v1_funct_2(k2_funct_1('#skF_4'),'#skF_3','#skF_2')
    | k1_relset_1('#skF_3','#skF_2',k2_funct_1('#skF_4')) != '#skF_3' ),
    inference(resolution,[status(thm)],[c_1262,c_1726])).

tff(c_1754,plain,
    ( k1_xboole_0 = '#skF_2'
    | v1_funct_2(k2_funct_1('#skF_4'),'#skF_3','#skF_2')
    | k1_relat_1(k2_funct_1('#skF_4')) != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1372,c_1735])).

tff(c_1755,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1(k2_funct_1('#skF_4')) != '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_1261,c_1754])).

tff(c_1761,plain,(
    k1_relat_1(k2_funct_1('#skF_4')) != '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_1755])).

tff(c_1764,plain,
    ( k2_relat_1('#skF_4') != '#skF_3'
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_1761])).

tff(c_1767,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_180,c_76,c_70,c_1394,c_1764])).

tff(c_1768,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_1755])).

tff(c_1797,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1768,c_2])).

tff(c_1799,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_229,c_1797])).

tff(c_1800,plain,(
    v1_xboole_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_224])).

tff(c_115,plain,(
    ! [B_49,A_50] :
      ( ~ v1_xboole_0(B_49)
      | B_49 = A_50
      | ~ v1_xboole_0(A_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_118,plain,(
    ! [A_50] :
      ( k1_xboole_0 = A_50
      | ~ v1_xboole_0(A_50) ) ),
    inference(resolution,[status(thm)],[c_2,c_115])).

tff(c_1807,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_1800,c_118])).

tff(c_12,plain,(
    ! [A_5] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_5)) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_48,plain,(
    ! [A_40] :
      ( v1_funct_2(k1_xboole_0,A_40,k1_xboole_0)
      | k1_xboole_0 = A_40
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(A_40,k1_xboole_0))) ) ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_78,plain,(
    ! [A_40] :
      ( v1_funct_2(k1_xboole_0,A_40,k1_xboole_0)
      | k1_xboole_0 = A_40 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_48])).

tff(c_1825,plain,(
    ! [A_40] :
      ( v1_funct_2('#skF_4',A_40,'#skF_4')
      | A_40 = '#skF_4' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1807,c_1807,c_1807,c_78])).

tff(c_1829,plain,(
    ! [A_5] : m1_subset_1('#skF_4',k1_zfmisc_1(A_5)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1807,c_12])).

tff(c_2039,plain,(
    ! [A_242,B_243,C_244] :
      ( k1_relset_1(A_242,B_243,C_244) = k1_relat_1(C_244)
      | ~ m1_subset_1(C_244,k1_zfmisc_1(k2_zfmisc_1(A_242,B_243))) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_2054,plain,(
    ! [A_242,B_243] : k1_relset_1(A_242,B_243,'#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_1829,c_2039])).

tff(c_10,plain,(
    ! [B_4] : k2_zfmisc_1(k1_xboole_0,B_4) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_52,plain,(
    ! [C_42,B_41] :
      ( v1_funct_2(C_42,k1_xboole_0,B_41)
      | k1_relset_1(k1_xboole_0,B_41,C_42) != k1_xboole_0
      | ~ m1_subset_1(C_42,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_41))) ) ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_80,plain,(
    ! [C_42,B_41] :
      ( v1_funct_2(C_42,k1_xboole_0,B_41)
      | k1_relset_1(k1_xboole_0,B_41,C_42) != k1_xboole_0
      | ~ m1_subset_1(C_42,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_52])).

tff(c_2164,plain,(
    ! [C_268,B_269] :
      ( v1_funct_2(C_268,'#skF_4',B_269)
      | k1_relset_1('#skF_4',B_269,C_268) != '#skF_4'
      | ~ m1_subset_1(C_268,k1_zfmisc_1('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1807,c_1807,c_1807,c_1807,c_80])).

tff(c_2167,plain,(
    ! [B_269] :
      ( v1_funct_2('#skF_4','#skF_4',B_269)
      | k1_relset_1('#skF_4',B_269,'#skF_4') != '#skF_4' ) ),
    inference(resolution,[status(thm)],[c_1829,c_2164])).

tff(c_2169,plain,(
    ! [B_269] :
      ( v1_funct_2('#skF_4','#skF_4',B_269)
      | k1_relat_1('#skF_4') != '#skF_4' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2054,c_2167])).

tff(c_2170,plain,(
    k1_relat_1('#skF_4') != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_2169])).

tff(c_1828,plain,(
    ! [B_4] : k2_zfmisc_1('#skF_4',B_4) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1807,c_1807,c_10])).

tff(c_1980,plain,(
    ! [C_235,A_236,B_237] :
      ( v1_partfun1(C_235,A_236)
      | ~ m1_subset_1(C_235,k1_zfmisc_1(k2_zfmisc_1(A_236,B_237)))
      | ~ v1_xboole_0(A_236) ) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_1983,plain,(
    ! [C_235] :
      ( v1_partfun1(C_235,'#skF_4')
      | ~ m1_subset_1(C_235,k1_zfmisc_1('#skF_4'))
      | ~ v1_xboole_0('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1828,c_1980])).

tff(c_2029,plain,(
    ! [C_240] :
      ( v1_partfun1(C_240,'#skF_4')
      | ~ m1_subset_1(C_240,k1_zfmisc_1('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1800,c_1983])).

tff(c_2034,plain,(
    v1_partfun1('#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_1829,c_2029])).

tff(c_2203,plain,(
    ! [C_271,A_272,B_273] :
      ( v1_funct_2(C_271,A_272,B_273)
      | ~ v1_partfun1(C_271,A_272)
      | ~ v1_funct_1(C_271)
      | ~ m1_subset_1(C_271,k1_zfmisc_1(k2_zfmisc_1(A_272,B_273))) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_2213,plain,(
    ! [A_272,B_273] :
      ( v1_funct_2('#skF_4',A_272,B_273)
      | ~ v1_partfun1('#skF_4',A_272)
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_1829,c_2203])).

tff(c_2220,plain,(
    ! [A_272,B_273] :
      ( v1_funct_2('#skF_4',A_272,B_273)
      | ~ v1_partfun1('#skF_4',A_272) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_2213])).

tff(c_56,plain,(
    ! [B_41,C_42] :
      ( k1_relset_1(k1_xboole_0,B_41,C_42) = k1_xboole_0
      | ~ v1_funct_2(C_42,k1_xboole_0,B_41)
      | ~ m1_subset_1(C_42,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_41))) ) ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_79,plain,(
    ! [B_41,C_42] :
      ( k1_relset_1(k1_xboole_0,B_41,C_42) = k1_xboole_0
      | ~ v1_funct_2(C_42,k1_xboole_0,B_41)
      | ~ m1_subset_1(C_42,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_56])).

tff(c_2264,plain,(
    ! [B_277,C_278] :
      ( k1_relset_1('#skF_4',B_277,C_278) = '#skF_4'
      | ~ v1_funct_2(C_278,'#skF_4',B_277)
      | ~ m1_subset_1(C_278,k1_zfmisc_1('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1807,c_1807,c_1807,c_1807,c_79])).

tff(c_2267,plain,(
    ! [B_273] :
      ( k1_relset_1('#skF_4',B_273,'#skF_4') = '#skF_4'
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_4'))
      | ~ v1_partfun1('#skF_4','#skF_4') ) ),
    inference(resolution,[status(thm)],[c_2220,c_2264])).

tff(c_2275,plain,(
    k1_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2034,c_1829,c_2054,c_2267])).

tff(c_2277,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2170,c_2275])).

tff(c_2279,plain,(
    k1_relat_1('#skF_4') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_2169])).

tff(c_1995,plain,(
    ! [A_239] :
      ( m1_subset_1(A_239,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_239),k2_relat_1(A_239))))
      | ~ v1_funct_1(A_239)
      | ~ v1_relat_1(A_239) ) ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_36,plain,(
    ! [C_26,B_24,A_23] :
      ( v1_xboole_0(C_26)
      | ~ m1_subset_1(C_26,k1_zfmisc_1(k2_zfmisc_1(B_24,A_23)))
      | ~ v1_xboole_0(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_2035,plain,(
    ! [A_241] :
      ( v1_xboole_0(A_241)
      | ~ v1_xboole_0(k2_relat_1(A_241))
      | ~ v1_funct_1(A_241)
      | ~ v1_relat_1(A_241) ) ),
    inference(resolution,[status(thm)],[c_1995,c_36])).

tff(c_2554,plain,(
    ! [A_307] :
      ( v1_xboole_0(k2_funct_1(A_307))
      | ~ v1_xboole_0(k1_relat_1(A_307))
      | ~ v1_funct_1(k2_funct_1(A_307))
      | ~ v1_relat_1(k2_funct_1(A_307))
      | ~ v2_funct_1(A_307)
      | ~ v1_funct_1(A_307)
      | ~ v1_relat_1(A_307) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_2035])).

tff(c_1801,plain,(
    v1_xboole_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_224])).

tff(c_1814,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_1801,c_118])).

tff(c_1838,plain,(
    '#skF_2' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1807,c_1814])).

tff(c_4,plain,(
    ! [B_2,A_1] :
      ( ~ v1_xboole_0(B_2)
      | B_2 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_1815,plain,(
    ! [A_1] :
      ( A_1 = '#skF_2'
      | ~ v1_xboole_0(A_1) ) ),
    inference(resolution,[status(thm)],[c_1801,c_4])).

tff(c_1866,plain,(
    ! [A_1] :
      ( A_1 = '#skF_4'
      | ~ v1_xboole_0(A_1) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1838,c_1815])).

tff(c_2589,plain,(
    ! [A_310] :
      ( k2_funct_1(A_310) = '#skF_4'
      | ~ v1_xboole_0(k1_relat_1(A_310))
      | ~ v1_funct_1(k2_funct_1(A_310))
      | ~ v1_relat_1(k2_funct_1(A_310))
      | ~ v2_funct_1(A_310)
      | ~ v1_funct_1(A_310)
      | ~ v1_relat_1(A_310) ) ),
    inference(resolution,[status(thm)],[c_2554,c_1866])).

tff(c_2592,plain,
    ( k2_funct_1('#skF_4') = '#skF_4'
    | ~ v1_xboole_0('#skF_4')
    | ~ v1_funct_1(k2_funct_1('#skF_4'))
    | ~ v1_relat_1(k2_funct_1('#skF_4'))
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_2279,c_2589])).

tff(c_2597,plain,
    ( k2_funct_1('#skF_4') = '#skF_4'
    | ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_180,c_76,c_70,c_159,c_1800,c_2592])).

tff(c_2598,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_2597])).

tff(c_2613,plain,
    ( ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_24,c_2598])).

tff(c_2617,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_180,c_76,c_2613])).

tff(c_2618,plain,(
    k2_funct_1('#skF_4') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_2597])).

tff(c_8,plain,(
    ! [A_3] : k2_zfmisc_1(A_3,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_1830,plain,(
    ! [A_3] : k2_zfmisc_1(A_3,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1807,c_1807,c_8])).

tff(c_1954,plain,
    ( ~ v1_funct_2(k2_funct_1('#skF_4'),'#skF_3','#skF_4')
    | ~ m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1830,c_1838,c_1838,c_158])).

tff(c_1955,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_1954])).

tff(c_2621,plain,(
    ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2618,c_1955])).

tff(c_2626,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1829,c_2621])).

tff(c_2628,plain,(
    m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_1954])).

tff(c_196,plain,(
    ! [C_63] :
      ( v1_xboole_0(C_63)
      | ~ m1_subset_1(C_63,k1_zfmisc_1(k1_xboole_0))
      | ~ v1_xboole_0(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_183])).

tff(c_201,plain,(
    ! [C_63] :
      ( v1_xboole_0(C_63)
      | ~ m1_subset_1(C_63,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_196])).

tff(c_1823,plain,(
    ! [C_63] :
      ( v1_xboole_0(C_63)
      | ~ m1_subset_1(C_63,k1_zfmisc_1('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1807,c_201])).

tff(c_2640,plain,(
    v1_xboole_0(k2_funct_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_2628,c_1823])).

tff(c_2653,plain,(
    k2_funct_1('#skF_4') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_2640,c_1866])).

tff(c_2627,plain,(
    ~ v1_funct_2(k2_funct_1('#skF_4'),'#skF_3','#skF_4') ),
    inference(splitRight,[status(thm)],[c_1954])).

tff(c_2658,plain,(
    ~ v1_funct_2('#skF_4','#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2653,c_2627])).

tff(c_2681,plain,(
    '#skF_3' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_1825,c_2658])).

tff(c_2702,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2681,c_202])).

tff(c_2705,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1800,c_2702])).

tff(c_2706,plain,(
    v1_xboole_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_197])).

tff(c_2713,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_2706,c_118])).

tff(c_3472,plain,(
    ! [A_5] : m1_subset_1('#skF_4',k1_zfmisc_1(A_5)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2713,c_12])).

tff(c_3471,plain,(
    ! [B_4] : k2_zfmisc_1('#skF_4',B_4) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2713,c_2713,c_10])).

tff(c_3668,plain,(
    ! [C_423,A_424,B_425] :
      ( v1_partfun1(C_423,A_424)
      | ~ m1_subset_1(C_423,k1_zfmisc_1(k2_zfmisc_1(A_424,B_425)))
      | ~ v1_xboole_0(A_424) ) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_3678,plain,(
    ! [C_423] :
      ( v1_partfun1(C_423,'#skF_4')
      | ~ m1_subset_1(C_423,k1_zfmisc_1('#skF_4'))
      | ~ v1_xboole_0('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3471,c_3668])).

tff(c_3683,plain,(
    ! [C_427] :
      ( v1_partfun1(C_427,'#skF_4')
      | ~ m1_subset_1(C_427,k1_zfmisc_1('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2706,c_3678])).

tff(c_3688,plain,(
    v1_partfun1('#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_3472,c_3683])).

tff(c_3952,plain,(
    ! [C_458,A_459,B_460] :
      ( v1_funct_2(C_458,A_459,B_460)
      | ~ v1_partfun1(C_458,A_459)
      | ~ v1_funct_1(C_458)
      | ~ m1_subset_1(C_458,k1_zfmisc_1(k2_zfmisc_1(A_459,B_460))) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_3959,plain,(
    ! [A_459,B_460] :
      ( v1_funct_2('#skF_4',A_459,B_460)
      | ~ v1_partfun1('#skF_4',A_459)
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_3472,c_3952])).

tff(c_3970,plain,(
    ! [A_461,B_462] :
      ( v1_funct_2('#skF_4',A_461,B_462)
      | ~ v1_partfun1('#skF_4',A_461) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_3959])).

tff(c_2707,plain,(
    v1_xboole_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_197])).

tff(c_2720,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_2707,c_118])).

tff(c_3481,plain,(
    '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2713,c_2720])).

tff(c_2728,plain,(
    ! [A_5] : m1_subset_1('#skF_4',k1_zfmisc_1(A_5)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2713,c_12])).

tff(c_2988,plain,(
    ! [A_354,B_355,C_356] :
      ( k2_relset_1(A_354,B_355,C_356) = k2_relat_1(C_356)
      | ~ m1_subset_1(C_356,k1_zfmisc_1(k2_zfmisc_1(A_354,B_355))) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_3004,plain,(
    ! [A_357,B_358] : k2_relset_1(A_357,B_358,'#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_2728,c_2988])).

tff(c_2737,plain,(
    '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2713,c_2720])).

tff(c_2740,plain,(
    k2_relset_1('#skF_2','#skF_4','#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2737,c_2737,c_68])).

tff(c_3008,plain,(
    k2_relat_1('#skF_4') = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_3004,c_2740])).

tff(c_2938,plain,(
    ! [A_350] :
      ( m1_subset_1(A_350,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_350),k2_relat_1(A_350))))
      | ~ v1_funct_1(A_350)
      | ~ v1_relat_1(A_350) ) ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_34,plain,(
    ! [C_22,A_19,B_20] :
      ( v1_xboole_0(C_22)
      | ~ m1_subset_1(C_22,k1_zfmisc_1(k2_zfmisc_1(A_19,B_20)))
      | ~ v1_xboole_0(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_2976,plain,(
    ! [A_351] :
      ( v1_xboole_0(A_351)
      | ~ v1_xboole_0(k1_relat_1(A_351))
      | ~ v1_funct_1(A_351)
      | ~ v1_relat_1(A_351) ) ),
    inference(resolution,[status(thm)],[c_2938,c_34])).

tff(c_3418,plain,(
    ! [A_401] :
      ( v1_xboole_0(k2_funct_1(A_401))
      | ~ v1_xboole_0(k2_relat_1(A_401))
      | ~ v1_funct_1(k2_funct_1(A_401))
      | ~ v1_relat_1(k2_funct_1(A_401))
      | ~ v2_funct_1(A_401)
      | ~ v1_funct_1(A_401)
      | ~ v1_relat_1(A_401) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_2976])).

tff(c_3421,plain,
    ( v1_xboole_0(k2_funct_1('#skF_4'))
    | ~ v1_xboole_0('#skF_4')
    | ~ v1_funct_1(k2_funct_1('#skF_4'))
    | ~ v1_relat_1(k2_funct_1('#skF_4'))
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_3008,c_3418])).

tff(c_3426,plain,
    ( v1_xboole_0(k2_funct_1('#skF_4'))
    | ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_180,c_76,c_70,c_159,c_2706,c_3421])).

tff(c_3427,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_3426])).

tff(c_3442,plain,
    ( ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_24,c_3427])).

tff(c_3446,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_180,c_76,c_3442])).

tff(c_3447,plain,(
    v1_xboole_0(k2_funct_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_3426])).

tff(c_2721,plain,(
    ! [A_1] :
      ( A_1 = '#skF_3'
      | ~ v1_xboole_0(A_1) ) ),
    inference(resolution,[status(thm)],[c_2707,c_4])).

tff(c_2747,plain,(
    ! [A_1] :
      ( A_1 = '#skF_4'
      | ~ v1_xboole_0(A_1) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2737,c_2721])).

tff(c_3454,plain,(
    k2_funct_1('#skF_4') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_3447,c_2747])).

tff(c_2727,plain,(
    ! [B_4] : k2_zfmisc_1('#skF_4',B_4) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2713,c_2713,c_10])).

tff(c_2722,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_158])).

tff(c_2754,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2737,c_2722])).

tff(c_2755,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2727,c_2754])).

tff(c_3458,plain,(
    ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3454,c_2755])).

tff(c_3464,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2728,c_3458])).

tff(c_3466,plain,(
    m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_158])).

tff(c_3561,plain,(
    m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3471,c_3481,c_3466])).

tff(c_3551,plain,(
    ! [C_63] :
      ( v1_xboole_0(C_63)
      | ~ m1_subset_1(C_63,k1_zfmisc_1('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2713,c_201])).

tff(c_3568,plain,(
    v1_xboole_0(k2_funct_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_3561,c_3551])).

tff(c_3491,plain,(
    ! [A_1] :
      ( A_1 = '#skF_4'
      | ~ v1_xboole_0(A_1) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3481,c_2721])).

tff(c_3577,plain,(
    k2_funct_1('#skF_4') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_3568,c_3491])).

tff(c_3465,plain,(
    ~ v1_funct_2(k2_funct_1('#skF_4'),'#skF_3','#skF_2') ),
    inference(splitRight,[status(thm)],[c_158])).

tff(c_3498,plain,(
    ~ v1_funct_2(k2_funct_1('#skF_4'),'#skF_4','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3481,c_3465])).

tff(c_3582,plain,(
    ~ v1_funct_2('#skF_4','#skF_4','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3577,c_3498])).

tff(c_3976,plain,(
    ~ v1_partfun1('#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_3970,c_3582])).

tff(c_3984,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3688,c_3976])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:16:56 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.17/2.02  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.17/2.05  
% 5.17/2.05  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.17/2.06  %$ v1_funct_2 > v1_partfun1 > r2_hidden > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 5.17/2.06  
% 5.17/2.06  %Foreground sorts:
% 5.17/2.06  
% 5.17/2.06  
% 5.17/2.06  %Background operators:
% 5.17/2.06  
% 5.17/2.06  
% 5.17/2.06  %Foreground operators:
% 5.17/2.06  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 5.17/2.06  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 5.17/2.06  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 5.17/2.06  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 5.17/2.06  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.17/2.06  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.17/2.06  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.17/2.06  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 5.17/2.06  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 5.17/2.06  tff('#skF_2', type, '#skF_2': $i).
% 5.17/2.06  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 5.17/2.06  tff('#skF_3', type, '#skF_3': $i).
% 5.17/2.06  tff('#skF_1', type, '#skF_1': $i).
% 5.17/2.06  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 5.17/2.06  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.17/2.06  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.17/2.06  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.17/2.06  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 5.17/2.06  tff('#skF_4', type, '#skF_4': $i).
% 5.17/2.06  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.17/2.06  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 5.17/2.06  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 5.17/2.06  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.17/2.06  
% 5.60/2.08  tff(f_172, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((v2_funct_1(C) & (k2_relset_1(A, B, C) = B)) => ((v1_funct_1(k2_funct_1(C)) & v1_funct_2(k2_funct_1(C), B, A)) & m1_subset_1(k2_funct_1(C), k1_zfmisc_1(k2_zfmisc_1(B, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_funct_2)).
% 5.60/2.08  tff(f_95, axiom, (![A, B]: (v1_xboole_0(A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_xboole_0(C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc3_relset_1)).
% 5.60/2.08  tff(f_57, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 5.60/2.08  tff(f_55, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 5.60/2.08  tff(f_110, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 5.60/2.08  tff(f_88, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k2_relat_1(A) = k1_relat_1(k2_funct_1(A))) & (k1_relat_1(A) = k2_relat_1(k2_funct_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_funct_1)).
% 5.60/2.08  tff(f_102, axiom, (![A, B]: (v1_xboole_0(A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => v1_xboole_0(C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc4_relset_1)).
% 5.60/2.08  tff(f_74, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 5.60/2.08  tff(f_106, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 5.60/2.08  tff(f_145, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 5.60/2.08  tff(f_155, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => ((v1_funct_1(A) & v1_funct_2(A, k1_relat_1(A), k2_relat_1(A))) & m1_subset_1(A, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_funct_2)).
% 5.60/2.08  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 5.60/2.08  tff(f_34, axiom, (![A, B]: ~((v1_xboole_0(A) & ~(A = B)) & v1_xboole_0(B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_boole)).
% 5.60/2.08  tff(f_42, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 5.60/2.08  tff(f_40, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 5.60/2.08  tff(f_127, axiom, (![A, B]: (v1_xboole_0(A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_partfun1(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_partfun1)).
% 5.60/2.08  tff(f_120, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v1_partfun1(C, A)) => (v1_funct_1(C) & v1_funct_2(C, A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_funct_2)).
% 5.60/2.08  tff(c_72, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_172])).
% 5.60/2.08  tff(c_210, plain, (![C_67, A_68, B_69]: (v1_xboole_0(C_67) | ~m1_subset_1(C_67, k1_zfmisc_1(k2_zfmisc_1(A_68, B_69))) | ~v1_xboole_0(A_68))), inference(cnfTransformation, [status(thm)], [f_95])).
% 5.60/2.08  tff(c_224, plain, (v1_xboole_0('#skF_4') | ~v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_72, c_210])).
% 5.60/2.08  tff(c_229, plain, (~v1_xboole_0('#skF_2')), inference(splitLeft, [status(thm)], [c_224])).
% 5.60/2.08  tff(c_18, plain, (![A_12, B_13]: (v1_relat_1(k2_zfmisc_1(A_12, B_13)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 5.60/2.08  tff(c_171, plain, (![B_61, A_62]: (v1_relat_1(B_61) | ~m1_subset_1(B_61, k1_zfmisc_1(A_62)) | ~v1_relat_1(A_62))), inference(cnfTransformation, [status(thm)], [f_55])).
% 5.60/2.08  tff(c_174, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_72, c_171])).
% 5.60/2.08  tff(c_180, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_18, c_174])).
% 5.60/2.08  tff(c_76, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_172])).
% 5.60/2.08  tff(c_70, plain, (v2_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_172])).
% 5.60/2.08  tff(c_68, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_4')='#skF_3'), inference(cnfTransformation, [status(thm)], [f_172])).
% 5.60/2.08  tff(c_1375, plain, (![A_179, B_180, C_181]: (k2_relset_1(A_179, B_180, C_181)=k2_relat_1(C_181) | ~m1_subset_1(C_181, k1_zfmisc_1(k2_zfmisc_1(A_179, B_180))))), inference(cnfTransformation, [status(thm)], [f_110])).
% 5.60/2.08  tff(c_1381, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_72, c_1375])).
% 5.60/2.08  tff(c_1394, plain, (k2_relat_1('#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_68, c_1381])).
% 5.60/2.08  tff(c_32, plain, (![A_18]: (k1_relat_1(k2_funct_1(A_18))=k2_relat_1(A_18) | ~v2_funct_1(A_18) | ~v1_funct_1(A_18) | ~v1_relat_1(A_18))), inference(cnfTransformation, [status(thm)], [f_88])).
% 5.60/2.08  tff(c_183, plain, (![C_63, B_64, A_65]: (v1_xboole_0(C_63) | ~m1_subset_1(C_63, k1_zfmisc_1(k2_zfmisc_1(B_64, A_65))) | ~v1_xboole_0(A_65))), inference(cnfTransformation, [status(thm)], [f_102])).
% 5.60/2.08  tff(c_197, plain, (v1_xboole_0('#skF_4') | ~v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_72, c_183])).
% 5.60/2.08  tff(c_202, plain, (~v1_xboole_0('#skF_3')), inference(splitLeft, [status(thm)], [c_197])).
% 5.60/2.08  tff(c_22, plain, (![A_17]: (v1_funct_1(k2_funct_1(A_17)) | ~v1_funct_1(A_17) | ~v1_relat_1(A_17))), inference(cnfTransformation, [status(thm)], [f_74])).
% 5.60/2.08  tff(c_66, plain, (~m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2'))) | ~v1_funct_2(k2_funct_1('#skF_4'), '#skF_3', '#skF_2') | ~v1_funct_1(k2_funct_1('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_172])).
% 5.60/2.08  tff(c_128, plain, (~v1_funct_1(k2_funct_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_66])).
% 5.60/2.08  tff(c_131, plain, (~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_22, c_128])).
% 5.60/2.08  tff(c_134, plain, (~v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_131])).
% 5.60/2.08  tff(c_146, plain, (![B_57, A_58]: (v1_relat_1(B_57) | ~m1_subset_1(B_57, k1_zfmisc_1(A_58)) | ~v1_relat_1(A_58))), inference(cnfTransformation, [status(thm)], [f_55])).
% 5.60/2.08  tff(c_149, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_72, c_146])).
% 5.60/2.08  tff(c_155, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_18, c_149])).
% 5.60/2.08  tff(c_157, plain, $false, inference(negUnitSimplification, [status(thm)], [c_134, c_155])).
% 5.60/2.08  tff(c_158, plain, (~v1_funct_2(k2_funct_1('#skF_4'), '#skF_3', '#skF_2') | ~m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(splitRight, [status(thm)], [c_66])).
% 5.60/2.08  tff(c_260, plain, (~m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(splitLeft, [status(thm)], [c_158])).
% 5.60/2.08  tff(c_74, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_172])).
% 5.60/2.08  tff(c_451, plain, (![A_97, B_98, C_99]: (k1_relset_1(A_97, B_98, C_99)=k1_relat_1(C_99) | ~m1_subset_1(C_99, k1_zfmisc_1(k2_zfmisc_1(A_97, B_98))))), inference(cnfTransformation, [status(thm)], [f_106])).
% 5.60/2.08  tff(c_473, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_72, c_451])).
% 5.60/2.08  tff(c_729, plain, (![B_130, A_131, C_132]: (k1_xboole_0=B_130 | k1_relset_1(A_131, B_130, C_132)=A_131 | ~v1_funct_2(C_132, A_131, B_130) | ~m1_subset_1(C_132, k1_zfmisc_1(k2_zfmisc_1(A_131, B_130))))), inference(cnfTransformation, [status(thm)], [f_145])).
% 5.60/2.08  tff(c_738, plain, (k1_xboole_0='#skF_3' | k1_relset_1('#skF_2', '#skF_3', '#skF_4')='#skF_2' | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_72, c_729])).
% 5.60/2.08  tff(c_755, plain, (k1_xboole_0='#skF_3' | k1_relat_1('#skF_4')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_74, c_473, c_738])).
% 5.60/2.08  tff(c_759, plain, (k1_relat_1('#skF_4')='#skF_2'), inference(splitLeft, [status(thm)], [c_755])).
% 5.60/2.08  tff(c_30, plain, (![A_18]: (k2_relat_1(k2_funct_1(A_18))=k1_relat_1(A_18) | ~v2_funct_1(A_18) | ~v1_funct_1(A_18) | ~v1_relat_1(A_18))), inference(cnfTransformation, [status(thm)], [f_88])).
% 5.60/2.08  tff(c_24, plain, (![A_17]: (v1_relat_1(k2_funct_1(A_17)) | ~v1_funct_1(A_17) | ~v1_relat_1(A_17))), inference(cnfTransformation, [status(thm)], [f_74])).
% 5.60/2.08  tff(c_159, plain, (v1_funct_1(k2_funct_1('#skF_4'))), inference(splitRight, [status(thm)], [c_66])).
% 5.60/2.08  tff(c_362, plain, (![A_90, B_91, C_92]: (k2_relset_1(A_90, B_91, C_92)=k2_relat_1(C_92) | ~m1_subset_1(C_92, k1_zfmisc_1(k2_zfmisc_1(A_90, B_91))))), inference(cnfTransformation, [status(thm)], [f_110])).
% 5.60/2.08  tff(c_368, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_72, c_362])).
% 5.60/2.08  tff(c_381, plain, (k2_relat_1('#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_68, c_368])).
% 5.60/2.08  tff(c_283, plain, (![A_81]: (k1_relat_1(k2_funct_1(A_81))=k2_relat_1(A_81) | ~v2_funct_1(A_81) | ~v1_funct_1(A_81) | ~v1_relat_1(A_81))), inference(cnfTransformation, [status(thm)], [f_88])).
% 5.60/2.08  tff(c_62, plain, (![A_43]: (v1_funct_2(A_43, k1_relat_1(A_43), k2_relat_1(A_43)) | ~v1_funct_1(A_43) | ~v1_relat_1(A_43))), inference(cnfTransformation, [status(thm)], [f_155])).
% 5.60/2.08  tff(c_976, plain, (![A_152]: (v1_funct_2(k2_funct_1(A_152), k2_relat_1(A_152), k2_relat_1(k2_funct_1(A_152))) | ~v1_funct_1(k2_funct_1(A_152)) | ~v1_relat_1(k2_funct_1(A_152)) | ~v2_funct_1(A_152) | ~v1_funct_1(A_152) | ~v1_relat_1(A_152))), inference(superposition, [status(thm), theory('equality')], [c_283, c_62])).
% 5.60/2.08  tff(c_979, plain, (v1_funct_2(k2_funct_1('#skF_4'), '#skF_3', k2_relat_1(k2_funct_1('#skF_4'))) | ~v1_funct_1(k2_funct_1('#skF_4')) | ~v1_relat_1(k2_funct_1('#skF_4')) | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_381, c_976])).
% 5.60/2.08  tff(c_987, plain, (v1_funct_2(k2_funct_1('#skF_4'), '#skF_3', k2_relat_1(k2_funct_1('#skF_4'))) | ~v1_relat_1(k2_funct_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_180, c_76, c_70, c_159, c_979])).
% 5.60/2.08  tff(c_988, plain, (~v1_relat_1(k2_funct_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_987])).
% 5.60/2.08  tff(c_991, plain, (~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_24, c_988])).
% 5.60/2.08  tff(c_995, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_180, c_76, c_991])).
% 5.60/2.08  tff(c_997, plain, (v1_relat_1(k2_funct_1('#skF_4'))), inference(splitRight, [status(thm)], [c_987])).
% 5.60/2.08  tff(c_313, plain, (![A_85]: (m1_subset_1(A_85, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_85), k2_relat_1(A_85)))) | ~v1_funct_1(A_85) | ~v1_relat_1(A_85))), inference(cnfTransformation, [status(thm)], [f_155])).
% 5.60/2.08  tff(c_1112, plain, (![A_158]: (m1_subset_1(k2_funct_1(A_158), k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(A_158), k2_relat_1(k2_funct_1(A_158))))) | ~v1_funct_1(k2_funct_1(A_158)) | ~v1_relat_1(k2_funct_1(A_158)) | ~v2_funct_1(A_158) | ~v1_funct_1(A_158) | ~v1_relat_1(A_158))), inference(superposition, [status(thm), theory('equality')], [c_32, c_313])).
% 5.60/2.08  tff(c_1147, plain, (m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', k2_relat_1(k2_funct_1('#skF_4'))))) | ~v1_funct_1(k2_funct_1('#skF_4')) | ~v1_relat_1(k2_funct_1('#skF_4')) | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_381, c_1112])).
% 5.60/2.08  tff(c_1170, plain, (m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', k2_relat_1(k2_funct_1('#skF_4')))))), inference(demodulation, [status(thm), theory('equality')], [c_180, c_76, c_70, c_997, c_159, c_1147])).
% 5.60/2.08  tff(c_1205, plain, (m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', k1_relat_1('#skF_4')))) | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_30, c_1170])).
% 5.60/2.08  tff(c_1227, plain, (m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_180, c_76, c_70, c_759, c_1205])).
% 5.60/2.08  tff(c_1229, plain, $false, inference(negUnitSimplification, [status(thm)], [c_260, c_1227])).
% 5.60/2.08  tff(c_1230, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_755])).
% 5.60/2.08  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 5.60/2.08  tff(c_1258, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1230, c_2])).
% 5.60/2.08  tff(c_1260, plain, $false, inference(negUnitSimplification, [status(thm)], [c_202, c_1258])).
% 5.60/2.08  tff(c_1261, plain, (~v1_funct_2(k2_funct_1('#skF_4'), '#skF_3', '#skF_2')), inference(splitRight, [status(thm)], [c_158])).
% 5.60/2.08  tff(c_1262, plain, (m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(splitRight, [status(thm)], [c_158])).
% 5.60/2.08  tff(c_1355, plain, (![A_176, B_177, C_178]: (k1_relset_1(A_176, B_177, C_178)=k1_relat_1(C_178) | ~m1_subset_1(C_178, k1_zfmisc_1(k2_zfmisc_1(A_176, B_177))))), inference(cnfTransformation, [status(thm)], [f_106])).
% 5.60/2.08  tff(c_1372, plain, (k1_relset_1('#skF_3', '#skF_2', k2_funct_1('#skF_4'))=k1_relat_1(k2_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_1262, c_1355])).
% 5.60/2.08  tff(c_1726, plain, (![B_214, C_215, A_216]: (k1_xboole_0=B_214 | v1_funct_2(C_215, A_216, B_214) | k1_relset_1(A_216, B_214, C_215)!=A_216 | ~m1_subset_1(C_215, k1_zfmisc_1(k2_zfmisc_1(A_216, B_214))))), inference(cnfTransformation, [status(thm)], [f_145])).
% 5.60/2.08  tff(c_1735, plain, (k1_xboole_0='#skF_2' | v1_funct_2(k2_funct_1('#skF_4'), '#skF_3', '#skF_2') | k1_relset_1('#skF_3', '#skF_2', k2_funct_1('#skF_4'))!='#skF_3'), inference(resolution, [status(thm)], [c_1262, c_1726])).
% 5.60/2.08  tff(c_1754, plain, (k1_xboole_0='#skF_2' | v1_funct_2(k2_funct_1('#skF_4'), '#skF_3', '#skF_2') | k1_relat_1(k2_funct_1('#skF_4'))!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1372, c_1735])).
% 5.60/2.08  tff(c_1755, plain, (k1_xboole_0='#skF_2' | k1_relat_1(k2_funct_1('#skF_4'))!='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_1261, c_1754])).
% 5.60/2.08  tff(c_1761, plain, (k1_relat_1(k2_funct_1('#skF_4'))!='#skF_3'), inference(splitLeft, [status(thm)], [c_1755])).
% 5.60/2.08  tff(c_1764, plain, (k2_relat_1('#skF_4')!='#skF_3' | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_32, c_1761])).
% 5.60/2.08  tff(c_1767, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_180, c_76, c_70, c_1394, c_1764])).
% 5.60/2.08  tff(c_1768, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_1755])).
% 5.60/2.08  tff(c_1797, plain, (v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1768, c_2])).
% 5.60/2.08  tff(c_1799, plain, $false, inference(negUnitSimplification, [status(thm)], [c_229, c_1797])).
% 5.60/2.08  tff(c_1800, plain, (v1_xboole_0('#skF_4')), inference(splitRight, [status(thm)], [c_224])).
% 5.60/2.08  tff(c_115, plain, (![B_49, A_50]: (~v1_xboole_0(B_49) | B_49=A_50 | ~v1_xboole_0(A_50))), inference(cnfTransformation, [status(thm)], [f_34])).
% 5.60/2.08  tff(c_118, plain, (![A_50]: (k1_xboole_0=A_50 | ~v1_xboole_0(A_50))), inference(resolution, [status(thm)], [c_2, c_115])).
% 5.60/2.08  tff(c_1807, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_1800, c_118])).
% 5.60/2.08  tff(c_12, plain, (![A_5]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_5)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 5.60/2.08  tff(c_48, plain, (![A_40]: (v1_funct_2(k1_xboole_0, A_40, k1_xboole_0) | k1_xboole_0=A_40 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k2_zfmisc_1(A_40, k1_xboole_0))))), inference(cnfTransformation, [status(thm)], [f_145])).
% 5.60/2.08  tff(c_78, plain, (![A_40]: (v1_funct_2(k1_xboole_0, A_40, k1_xboole_0) | k1_xboole_0=A_40)), inference(demodulation, [status(thm), theory('equality')], [c_12, c_48])).
% 5.60/2.08  tff(c_1825, plain, (![A_40]: (v1_funct_2('#skF_4', A_40, '#skF_4') | A_40='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1807, c_1807, c_1807, c_78])).
% 5.60/2.08  tff(c_1829, plain, (![A_5]: (m1_subset_1('#skF_4', k1_zfmisc_1(A_5)))), inference(demodulation, [status(thm), theory('equality')], [c_1807, c_12])).
% 5.60/2.08  tff(c_2039, plain, (![A_242, B_243, C_244]: (k1_relset_1(A_242, B_243, C_244)=k1_relat_1(C_244) | ~m1_subset_1(C_244, k1_zfmisc_1(k2_zfmisc_1(A_242, B_243))))), inference(cnfTransformation, [status(thm)], [f_106])).
% 5.60/2.08  tff(c_2054, plain, (![A_242, B_243]: (k1_relset_1(A_242, B_243, '#skF_4')=k1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_1829, c_2039])).
% 5.60/2.08  tff(c_10, plain, (![B_4]: (k2_zfmisc_1(k1_xboole_0, B_4)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_40])).
% 5.60/2.08  tff(c_52, plain, (![C_42, B_41]: (v1_funct_2(C_42, k1_xboole_0, B_41) | k1_relset_1(k1_xboole_0, B_41, C_42)!=k1_xboole_0 | ~m1_subset_1(C_42, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_41))))), inference(cnfTransformation, [status(thm)], [f_145])).
% 5.60/2.08  tff(c_80, plain, (![C_42, B_41]: (v1_funct_2(C_42, k1_xboole_0, B_41) | k1_relset_1(k1_xboole_0, B_41, C_42)!=k1_xboole_0 | ~m1_subset_1(C_42, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_52])).
% 5.60/2.08  tff(c_2164, plain, (![C_268, B_269]: (v1_funct_2(C_268, '#skF_4', B_269) | k1_relset_1('#skF_4', B_269, C_268)!='#skF_4' | ~m1_subset_1(C_268, k1_zfmisc_1('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_1807, c_1807, c_1807, c_1807, c_80])).
% 5.60/2.08  tff(c_2167, plain, (![B_269]: (v1_funct_2('#skF_4', '#skF_4', B_269) | k1_relset_1('#skF_4', B_269, '#skF_4')!='#skF_4')), inference(resolution, [status(thm)], [c_1829, c_2164])).
% 5.60/2.08  tff(c_2169, plain, (![B_269]: (v1_funct_2('#skF_4', '#skF_4', B_269) | k1_relat_1('#skF_4')!='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2054, c_2167])).
% 5.60/2.08  tff(c_2170, plain, (k1_relat_1('#skF_4')!='#skF_4'), inference(splitLeft, [status(thm)], [c_2169])).
% 5.60/2.08  tff(c_1828, plain, (![B_4]: (k2_zfmisc_1('#skF_4', B_4)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1807, c_1807, c_10])).
% 5.60/2.08  tff(c_1980, plain, (![C_235, A_236, B_237]: (v1_partfun1(C_235, A_236) | ~m1_subset_1(C_235, k1_zfmisc_1(k2_zfmisc_1(A_236, B_237))) | ~v1_xboole_0(A_236))), inference(cnfTransformation, [status(thm)], [f_127])).
% 5.60/2.08  tff(c_1983, plain, (![C_235]: (v1_partfun1(C_235, '#skF_4') | ~m1_subset_1(C_235, k1_zfmisc_1('#skF_4')) | ~v1_xboole_0('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_1828, c_1980])).
% 5.60/2.08  tff(c_2029, plain, (![C_240]: (v1_partfun1(C_240, '#skF_4') | ~m1_subset_1(C_240, k1_zfmisc_1('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_1800, c_1983])).
% 5.60/2.08  tff(c_2034, plain, (v1_partfun1('#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_1829, c_2029])).
% 5.60/2.08  tff(c_2203, plain, (![C_271, A_272, B_273]: (v1_funct_2(C_271, A_272, B_273) | ~v1_partfun1(C_271, A_272) | ~v1_funct_1(C_271) | ~m1_subset_1(C_271, k1_zfmisc_1(k2_zfmisc_1(A_272, B_273))))), inference(cnfTransformation, [status(thm)], [f_120])).
% 5.60/2.08  tff(c_2213, plain, (![A_272, B_273]: (v1_funct_2('#skF_4', A_272, B_273) | ~v1_partfun1('#skF_4', A_272) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_1829, c_2203])).
% 5.60/2.08  tff(c_2220, plain, (![A_272, B_273]: (v1_funct_2('#skF_4', A_272, B_273) | ~v1_partfun1('#skF_4', A_272))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_2213])).
% 5.60/2.08  tff(c_56, plain, (![B_41, C_42]: (k1_relset_1(k1_xboole_0, B_41, C_42)=k1_xboole_0 | ~v1_funct_2(C_42, k1_xboole_0, B_41) | ~m1_subset_1(C_42, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_41))))), inference(cnfTransformation, [status(thm)], [f_145])).
% 5.60/2.08  tff(c_79, plain, (![B_41, C_42]: (k1_relset_1(k1_xboole_0, B_41, C_42)=k1_xboole_0 | ~v1_funct_2(C_42, k1_xboole_0, B_41) | ~m1_subset_1(C_42, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_56])).
% 5.60/2.08  tff(c_2264, plain, (![B_277, C_278]: (k1_relset_1('#skF_4', B_277, C_278)='#skF_4' | ~v1_funct_2(C_278, '#skF_4', B_277) | ~m1_subset_1(C_278, k1_zfmisc_1('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_1807, c_1807, c_1807, c_1807, c_79])).
% 5.60/2.08  tff(c_2267, plain, (![B_273]: (k1_relset_1('#skF_4', B_273, '#skF_4')='#skF_4' | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_4')) | ~v1_partfun1('#skF_4', '#skF_4'))), inference(resolution, [status(thm)], [c_2220, c_2264])).
% 5.60/2.08  tff(c_2275, plain, (k1_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_2034, c_1829, c_2054, c_2267])).
% 5.60/2.08  tff(c_2277, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2170, c_2275])).
% 5.60/2.08  tff(c_2279, plain, (k1_relat_1('#skF_4')='#skF_4'), inference(splitRight, [status(thm)], [c_2169])).
% 5.60/2.08  tff(c_1995, plain, (![A_239]: (m1_subset_1(A_239, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_239), k2_relat_1(A_239)))) | ~v1_funct_1(A_239) | ~v1_relat_1(A_239))), inference(cnfTransformation, [status(thm)], [f_155])).
% 5.60/2.08  tff(c_36, plain, (![C_26, B_24, A_23]: (v1_xboole_0(C_26) | ~m1_subset_1(C_26, k1_zfmisc_1(k2_zfmisc_1(B_24, A_23))) | ~v1_xboole_0(A_23))), inference(cnfTransformation, [status(thm)], [f_102])).
% 5.60/2.08  tff(c_2035, plain, (![A_241]: (v1_xboole_0(A_241) | ~v1_xboole_0(k2_relat_1(A_241)) | ~v1_funct_1(A_241) | ~v1_relat_1(A_241))), inference(resolution, [status(thm)], [c_1995, c_36])).
% 5.60/2.08  tff(c_2554, plain, (![A_307]: (v1_xboole_0(k2_funct_1(A_307)) | ~v1_xboole_0(k1_relat_1(A_307)) | ~v1_funct_1(k2_funct_1(A_307)) | ~v1_relat_1(k2_funct_1(A_307)) | ~v2_funct_1(A_307) | ~v1_funct_1(A_307) | ~v1_relat_1(A_307))), inference(superposition, [status(thm), theory('equality')], [c_30, c_2035])).
% 5.60/2.08  tff(c_1801, plain, (v1_xboole_0('#skF_2')), inference(splitRight, [status(thm)], [c_224])).
% 5.60/2.08  tff(c_1814, plain, (k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_1801, c_118])).
% 5.60/2.08  tff(c_1838, plain, ('#skF_2'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_1807, c_1814])).
% 5.60/2.08  tff(c_4, plain, (![B_2, A_1]: (~v1_xboole_0(B_2) | B_2=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_34])).
% 5.60/2.08  tff(c_1815, plain, (![A_1]: (A_1='#skF_2' | ~v1_xboole_0(A_1))), inference(resolution, [status(thm)], [c_1801, c_4])).
% 5.60/2.08  tff(c_1866, plain, (![A_1]: (A_1='#skF_4' | ~v1_xboole_0(A_1))), inference(demodulation, [status(thm), theory('equality')], [c_1838, c_1815])).
% 5.60/2.08  tff(c_2589, plain, (![A_310]: (k2_funct_1(A_310)='#skF_4' | ~v1_xboole_0(k1_relat_1(A_310)) | ~v1_funct_1(k2_funct_1(A_310)) | ~v1_relat_1(k2_funct_1(A_310)) | ~v2_funct_1(A_310) | ~v1_funct_1(A_310) | ~v1_relat_1(A_310))), inference(resolution, [status(thm)], [c_2554, c_1866])).
% 5.60/2.08  tff(c_2592, plain, (k2_funct_1('#skF_4')='#skF_4' | ~v1_xboole_0('#skF_4') | ~v1_funct_1(k2_funct_1('#skF_4')) | ~v1_relat_1(k2_funct_1('#skF_4')) | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_2279, c_2589])).
% 5.60/2.08  tff(c_2597, plain, (k2_funct_1('#skF_4')='#skF_4' | ~v1_relat_1(k2_funct_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_180, c_76, c_70, c_159, c_1800, c_2592])).
% 5.60/2.08  tff(c_2598, plain, (~v1_relat_1(k2_funct_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_2597])).
% 5.60/2.08  tff(c_2613, plain, (~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_24, c_2598])).
% 5.60/2.08  tff(c_2617, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_180, c_76, c_2613])).
% 5.60/2.08  tff(c_2618, plain, (k2_funct_1('#skF_4')='#skF_4'), inference(splitRight, [status(thm)], [c_2597])).
% 5.60/2.08  tff(c_8, plain, (![A_3]: (k2_zfmisc_1(A_3, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_40])).
% 5.60/2.08  tff(c_1830, plain, (![A_3]: (k2_zfmisc_1(A_3, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1807, c_1807, c_8])).
% 5.60/2.08  tff(c_1954, plain, (~v1_funct_2(k2_funct_1('#skF_4'), '#skF_3', '#skF_4') | ~m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_1830, c_1838, c_1838, c_158])).
% 5.60/2.08  tff(c_1955, plain, (~m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_1954])).
% 5.60/2.08  tff(c_2621, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_2618, c_1955])).
% 5.60/2.08  tff(c_2626, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1829, c_2621])).
% 5.60/2.08  tff(c_2628, plain, (m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1('#skF_4'))), inference(splitRight, [status(thm)], [c_1954])).
% 5.60/2.08  tff(c_196, plain, (![C_63]: (v1_xboole_0(C_63) | ~m1_subset_1(C_63, k1_zfmisc_1(k1_xboole_0)) | ~v1_xboole_0(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_8, c_183])).
% 5.60/2.09  tff(c_201, plain, (![C_63]: (v1_xboole_0(C_63) | ~m1_subset_1(C_63, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_196])).
% 5.60/2.09  tff(c_1823, plain, (![C_63]: (v1_xboole_0(C_63) | ~m1_subset_1(C_63, k1_zfmisc_1('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_1807, c_201])).
% 5.60/2.09  tff(c_2640, plain, (v1_xboole_0(k2_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_2628, c_1823])).
% 5.60/2.09  tff(c_2653, plain, (k2_funct_1('#skF_4')='#skF_4'), inference(resolution, [status(thm)], [c_2640, c_1866])).
% 5.60/2.09  tff(c_2627, plain, (~v1_funct_2(k2_funct_1('#skF_4'), '#skF_3', '#skF_4')), inference(splitRight, [status(thm)], [c_1954])).
% 5.60/2.09  tff(c_2658, plain, (~v1_funct_2('#skF_4', '#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2653, c_2627])).
% 5.60/2.09  tff(c_2681, plain, ('#skF_3'='#skF_4'), inference(resolution, [status(thm)], [c_1825, c_2658])).
% 5.60/2.09  tff(c_2702, plain, (~v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2681, c_202])).
% 5.60/2.09  tff(c_2705, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1800, c_2702])).
% 5.60/2.09  tff(c_2706, plain, (v1_xboole_0('#skF_4')), inference(splitRight, [status(thm)], [c_197])).
% 5.60/2.09  tff(c_2713, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_2706, c_118])).
% 5.60/2.09  tff(c_3472, plain, (![A_5]: (m1_subset_1('#skF_4', k1_zfmisc_1(A_5)))), inference(demodulation, [status(thm), theory('equality')], [c_2713, c_12])).
% 5.60/2.09  tff(c_3471, plain, (![B_4]: (k2_zfmisc_1('#skF_4', B_4)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2713, c_2713, c_10])).
% 5.60/2.09  tff(c_3668, plain, (![C_423, A_424, B_425]: (v1_partfun1(C_423, A_424) | ~m1_subset_1(C_423, k1_zfmisc_1(k2_zfmisc_1(A_424, B_425))) | ~v1_xboole_0(A_424))), inference(cnfTransformation, [status(thm)], [f_127])).
% 5.60/2.09  tff(c_3678, plain, (![C_423]: (v1_partfun1(C_423, '#skF_4') | ~m1_subset_1(C_423, k1_zfmisc_1('#skF_4')) | ~v1_xboole_0('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_3471, c_3668])).
% 5.60/2.09  tff(c_3683, plain, (![C_427]: (v1_partfun1(C_427, '#skF_4') | ~m1_subset_1(C_427, k1_zfmisc_1('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_2706, c_3678])).
% 5.60/2.09  tff(c_3688, plain, (v1_partfun1('#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_3472, c_3683])).
% 5.60/2.09  tff(c_3952, plain, (![C_458, A_459, B_460]: (v1_funct_2(C_458, A_459, B_460) | ~v1_partfun1(C_458, A_459) | ~v1_funct_1(C_458) | ~m1_subset_1(C_458, k1_zfmisc_1(k2_zfmisc_1(A_459, B_460))))), inference(cnfTransformation, [status(thm)], [f_120])).
% 5.60/2.09  tff(c_3959, plain, (![A_459, B_460]: (v1_funct_2('#skF_4', A_459, B_460) | ~v1_partfun1('#skF_4', A_459) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_3472, c_3952])).
% 5.60/2.09  tff(c_3970, plain, (![A_461, B_462]: (v1_funct_2('#skF_4', A_461, B_462) | ~v1_partfun1('#skF_4', A_461))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_3959])).
% 5.60/2.09  tff(c_2707, plain, (v1_xboole_0('#skF_3')), inference(splitRight, [status(thm)], [c_197])).
% 5.60/2.09  tff(c_2720, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_2707, c_118])).
% 5.60/2.09  tff(c_3481, plain, ('#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_2713, c_2720])).
% 5.60/2.09  tff(c_2728, plain, (![A_5]: (m1_subset_1('#skF_4', k1_zfmisc_1(A_5)))), inference(demodulation, [status(thm), theory('equality')], [c_2713, c_12])).
% 5.60/2.09  tff(c_2988, plain, (![A_354, B_355, C_356]: (k2_relset_1(A_354, B_355, C_356)=k2_relat_1(C_356) | ~m1_subset_1(C_356, k1_zfmisc_1(k2_zfmisc_1(A_354, B_355))))), inference(cnfTransformation, [status(thm)], [f_110])).
% 5.60/2.09  tff(c_3004, plain, (![A_357, B_358]: (k2_relset_1(A_357, B_358, '#skF_4')=k2_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_2728, c_2988])).
% 5.60/2.09  tff(c_2737, plain, ('#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_2713, c_2720])).
% 5.60/2.09  tff(c_2740, plain, (k2_relset_1('#skF_2', '#skF_4', '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_2737, c_2737, c_68])).
% 5.60/2.09  tff(c_3008, plain, (k2_relat_1('#skF_4')='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_3004, c_2740])).
% 5.60/2.09  tff(c_2938, plain, (![A_350]: (m1_subset_1(A_350, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_350), k2_relat_1(A_350)))) | ~v1_funct_1(A_350) | ~v1_relat_1(A_350))), inference(cnfTransformation, [status(thm)], [f_155])).
% 5.60/2.09  tff(c_34, plain, (![C_22, A_19, B_20]: (v1_xboole_0(C_22) | ~m1_subset_1(C_22, k1_zfmisc_1(k2_zfmisc_1(A_19, B_20))) | ~v1_xboole_0(A_19))), inference(cnfTransformation, [status(thm)], [f_95])).
% 5.60/2.09  tff(c_2976, plain, (![A_351]: (v1_xboole_0(A_351) | ~v1_xboole_0(k1_relat_1(A_351)) | ~v1_funct_1(A_351) | ~v1_relat_1(A_351))), inference(resolution, [status(thm)], [c_2938, c_34])).
% 5.60/2.09  tff(c_3418, plain, (![A_401]: (v1_xboole_0(k2_funct_1(A_401)) | ~v1_xboole_0(k2_relat_1(A_401)) | ~v1_funct_1(k2_funct_1(A_401)) | ~v1_relat_1(k2_funct_1(A_401)) | ~v2_funct_1(A_401) | ~v1_funct_1(A_401) | ~v1_relat_1(A_401))), inference(superposition, [status(thm), theory('equality')], [c_32, c_2976])).
% 5.60/2.09  tff(c_3421, plain, (v1_xboole_0(k2_funct_1('#skF_4')) | ~v1_xboole_0('#skF_4') | ~v1_funct_1(k2_funct_1('#skF_4')) | ~v1_relat_1(k2_funct_1('#skF_4')) | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_3008, c_3418])).
% 5.60/2.09  tff(c_3426, plain, (v1_xboole_0(k2_funct_1('#skF_4')) | ~v1_relat_1(k2_funct_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_180, c_76, c_70, c_159, c_2706, c_3421])).
% 5.60/2.09  tff(c_3427, plain, (~v1_relat_1(k2_funct_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_3426])).
% 5.60/2.09  tff(c_3442, plain, (~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_24, c_3427])).
% 5.60/2.09  tff(c_3446, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_180, c_76, c_3442])).
% 5.60/2.09  tff(c_3447, plain, (v1_xboole_0(k2_funct_1('#skF_4'))), inference(splitRight, [status(thm)], [c_3426])).
% 5.60/2.09  tff(c_2721, plain, (![A_1]: (A_1='#skF_3' | ~v1_xboole_0(A_1))), inference(resolution, [status(thm)], [c_2707, c_4])).
% 5.60/2.09  tff(c_2747, plain, (![A_1]: (A_1='#skF_4' | ~v1_xboole_0(A_1))), inference(demodulation, [status(thm), theory('equality')], [c_2737, c_2721])).
% 5.60/2.09  tff(c_3454, plain, (k2_funct_1('#skF_4')='#skF_4'), inference(resolution, [status(thm)], [c_3447, c_2747])).
% 5.60/2.09  tff(c_2727, plain, (![B_4]: (k2_zfmisc_1('#skF_4', B_4)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2713, c_2713, c_10])).
% 5.60/2.09  tff(c_2722, plain, (~m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(splitLeft, [status(thm)], [c_158])).
% 5.60/2.09  tff(c_2754, plain, (~m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_2737, c_2722])).
% 5.60/2.09  tff(c_2755, plain, (~m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_2727, c_2754])).
% 5.60/2.09  tff(c_3458, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_3454, c_2755])).
% 5.60/2.09  tff(c_3464, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2728, c_3458])).
% 5.60/2.09  tff(c_3466, plain, (m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(splitRight, [status(thm)], [c_158])).
% 5.60/2.09  tff(c_3561, plain, (m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_3471, c_3481, c_3466])).
% 5.60/2.09  tff(c_3551, plain, (![C_63]: (v1_xboole_0(C_63) | ~m1_subset_1(C_63, k1_zfmisc_1('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_2713, c_201])).
% 5.60/2.09  tff(c_3568, plain, (v1_xboole_0(k2_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_3561, c_3551])).
% 5.60/2.09  tff(c_3491, plain, (![A_1]: (A_1='#skF_4' | ~v1_xboole_0(A_1))), inference(demodulation, [status(thm), theory('equality')], [c_3481, c_2721])).
% 5.60/2.09  tff(c_3577, plain, (k2_funct_1('#skF_4')='#skF_4'), inference(resolution, [status(thm)], [c_3568, c_3491])).
% 5.60/2.09  tff(c_3465, plain, (~v1_funct_2(k2_funct_1('#skF_4'), '#skF_3', '#skF_2')), inference(splitRight, [status(thm)], [c_158])).
% 5.60/2.09  tff(c_3498, plain, (~v1_funct_2(k2_funct_1('#skF_4'), '#skF_4', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_3481, c_3465])).
% 5.60/2.09  tff(c_3582, plain, (~v1_funct_2('#skF_4', '#skF_4', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_3577, c_3498])).
% 5.60/2.09  tff(c_3976, plain, (~v1_partfun1('#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_3970, c_3582])).
% 5.60/2.09  tff(c_3984, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3688, c_3976])).
% 5.60/2.09  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.60/2.09  
% 5.60/2.09  Inference rules
% 5.60/2.09  ----------------------
% 5.60/2.09  #Ref     : 0
% 5.60/2.09  #Sup     : 805
% 5.60/2.09  #Fact    : 0
% 5.60/2.09  #Define  : 0
% 5.60/2.09  #Split   : 22
% 5.60/2.09  #Chain   : 0
% 5.60/2.09  #Close   : 0
% 5.60/2.09  
% 5.60/2.09  Ordering : KBO
% 5.60/2.09  
% 5.60/2.09  Simplification rules
% 5.60/2.09  ----------------------
% 5.60/2.09  #Subsume      : 105
% 5.60/2.09  #Demod        : 996
% 5.60/2.09  #Tautology    : 439
% 5.60/2.09  #SimpNegUnit  : 9
% 5.60/2.09  #BackRed      : 132
% 5.60/2.09  
% 5.60/2.09  #Partial instantiations: 0
% 5.60/2.09  #Strategies tried      : 1
% 5.60/2.09  
% 5.60/2.09  Timing (in seconds)
% 5.60/2.09  ----------------------
% 5.60/2.09  Preprocessing        : 0.39
% 5.60/2.09  Parsing              : 0.21
% 5.60/2.09  CNF conversion       : 0.02
% 5.60/2.09  Main loop            : 0.84
% 5.60/2.09  Inferencing          : 0.31
% 5.60/2.09  Reduction            : 0.28
% 5.60/2.09  Demodulation         : 0.20
% 5.60/2.09  BG Simplification    : 0.04
% 5.60/2.09  Subsumption          : 0.14
% 5.60/2.09  Abstraction          : 0.04
% 5.60/2.09  MUC search           : 0.00
% 5.60/2.09  Cooper               : 0.00
% 5.60/2.09  Total                : 1.30
% 5.60/2.09  Index Insertion      : 0.00
% 5.60/2.09  Index Deletion       : 0.00
% 5.60/2.09  Index Matching       : 0.00
% 5.60/2.09  BG Taut test         : 0.00
%------------------------------------------------------------------------------
