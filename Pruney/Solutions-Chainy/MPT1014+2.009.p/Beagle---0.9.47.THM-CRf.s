%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:15:37 EST 2020

% Result     : Theorem 3.16s
% Output     : CNFRefutation 3.16s
% Verified   : 
% Statistics : Number of formulae       :   88 ( 160 expanded)
%              Number of leaves         :   34 (  72 expanded)
%              Depth                    :    9
%              Number of atoms          :  160 ( 510 expanded)
%              Number of equality atoms :   47 (  91 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > m1_subset_1 > v1_relat_1 > v1_funct_1 > k4_relset_1 > k1_partfun1 > k2_relset_1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_relset_1,type,(
    r2_relset_1: ( $i * $i * $i * $i ) > $o )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(k4_relset_1,type,(
    k4_relset_1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k1_partfun1,type,(
    k1_partfun1: ( $i * $i * $i * $i * $i * $i ) > $i )).

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

tff(k6_partfun1,type,(
    k6_partfun1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_117,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_funct_1(B)
          & v1_funct_2(B,A,A)
          & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
       => ! [C] :
            ( ( v1_funct_1(C)
              & v1_funct_2(C,A,A)
              & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
           => ( ( r2_relset_1(A,A,k1_partfun1(A,A,A,A,B,C),B)
                & k2_relset_1(A,A,B) = A )
             => r2_relset_1(A,A,C,k6_partfun1(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_funct_2)).

tff(f_77,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

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

tff(f_63,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_59,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_97,axiom,(
    ! [A,B] :
      ( ( v1_funct_1(B)
        & v1_funct_2(B,A,A)
        & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
     => k1_relset_1(A,A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_funct_2)).

tff(f_69,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k4_relset_1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_relset_1)).

tff(f_55,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => m1_subset_1(k4_relset_1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_relset_1)).

tff(f_87,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_89,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_49,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( ( v1_relat_1(B)
            & v1_funct_1(B) )
         => ( ( k2_relat_1(A) = k1_relat_1(B)
              & k5_relat_1(A,B) = A )
           => B = k6_relat_1(k1_relat_1(B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_funct_1)).

tff(c_32,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_71,plain,(
    ! [A_46,B_47,D_48] :
      ( r2_relset_1(A_46,B_47,D_48,D_48)
      | ~ m1_subset_1(D_48,k1_zfmisc_1(k2_zfmisc_1(A_46,B_47))) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_77,plain,(
    r2_relset_1('#skF_1','#skF_1','#skF_3','#skF_3') ),
    inference(resolution,[status(thm)],[c_32,c_71])).

tff(c_4,plain,(
    ! [A_4,B_5] : v1_relat_1(k2_zfmisc_1(A_4,B_5)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_38,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_58,plain,(
    ! [B_44,A_45] :
      ( v1_relat_1(B_44)
      | ~ m1_subset_1(B_44,k1_zfmisc_1(A_45))
      | ~ v1_relat_1(A_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_61,plain,
    ( v1_relat_1('#skF_2')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_1')) ),
    inference(resolution,[status(thm)],[c_38,c_58])).

tff(c_67,plain,(
    v1_relat_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_61])).

tff(c_42,plain,(
    v1_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_64,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_1')) ),
    inference(resolution,[status(thm)],[c_32,c_58])).

tff(c_70,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_64])).

tff(c_36,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_28,plain,(
    k2_relset_1('#skF_1','#skF_1','#skF_2') = '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_78,plain,(
    ! [A_49,B_50,C_51] :
      ( k2_relset_1(A_49,B_50,C_51) = k2_relat_1(C_51)
      | ~ m1_subset_1(C_51,k1_zfmisc_1(k2_zfmisc_1(A_49,B_50))) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_81,plain,(
    k2_relset_1('#skF_1','#skF_1','#skF_2') = k2_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_38,c_78])).

tff(c_86,plain,(
    k2_relat_1('#skF_2') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_81])).

tff(c_34,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_96,plain,(
    ! [A_52,B_53,C_54] :
      ( k1_relset_1(A_52,B_53,C_54) = k1_relat_1(C_54)
      | ~ m1_subset_1(C_54,k1_zfmisc_1(k2_zfmisc_1(A_52,B_53))) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_104,plain,(
    k1_relset_1('#skF_1','#skF_1','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_32,c_96])).

tff(c_113,plain,(
    ! [A_55,B_56] :
      ( k1_relset_1(A_55,A_55,B_56) = A_55
      | ~ m1_subset_1(B_56,k1_zfmisc_1(k2_zfmisc_1(A_55,A_55)))
      | ~ v1_funct_2(B_56,A_55,A_55)
      | ~ v1_funct_1(B_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_119,plain,
    ( k1_relset_1('#skF_1','#skF_1','#skF_3') = '#skF_1'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_32,c_113])).

tff(c_125,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_104,c_119])).

tff(c_164,plain,(
    ! [B_67,C_65,D_64,A_63,F_66,E_68] :
      ( k4_relset_1(A_63,B_67,C_65,D_64,E_68,F_66) = k5_relat_1(E_68,F_66)
      | ~ m1_subset_1(F_66,k1_zfmisc_1(k2_zfmisc_1(C_65,D_64)))
      | ~ m1_subset_1(E_68,k1_zfmisc_1(k2_zfmisc_1(A_63,B_67))) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_341,plain,(
    ! [A_84,B_85,E_86] :
      ( k4_relset_1(A_84,B_85,'#skF_1','#skF_1',E_86,'#skF_3') = k5_relat_1(E_86,'#skF_3')
      | ~ m1_subset_1(E_86,k1_zfmisc_1(k2_zfmisc_1(A_84,B_85))) ) ),
    inference(resolution,[status(thm)],[c_32,c_164])).

tff(c_360,plain,(
    k4_relset_1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2','#skF_3') = k5_relat_1('#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_38,c_341])).

tff(c_8,plain,(
    ! [C_11,E_13,B_10,F_14,D_12,A_9] :
      ( m1_subset_1(k4_relset_1(A_9,B_10,C_11,D_12,E_13,F_14),k1_zfmisc_1(k2_zfmisc_1(A_9,D_12)))
      | ~ m1_subset_1(F_14,k1_zfmisc_1(k2_zfmisc_1(C_11,D_12)))
      | ~ m1_subset_1(E_13,k1_zfmisc_1(k2_zfmisc_1(A_9,B_10))) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_365,plain,
    ( m1_subset_1(k5_relat_1('#skF_2','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_360,c_8])).

tff(c_369,plain,(
    m1_subset_1(k5_relat_1('#skF_2','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_32,c_365])).

tff(c_304,plain,(
    ! [E_80,A_81,D_78,B_79,C_83,F_82] :
      ( k1_partfun1(A_81,B_79,C_83,D_78,E_80,F_82) = k5_relat_1(E_80,F_82)
      | ~ m1_subset_1(F_82,k1_zfmisc_1(k2_zfmisc_1(C_83,D_78)))
      | ~ v1_funct_1(F_82)
      | ~ m1_subset_1(E_80,k1_zfmisc_1(k2_zfmisc_1(A_81,B_79)))
      | ~ v1_funct_1(E_80) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_314,plain,(
    ! [A_81,B_79,E_80] :
      ( k1_partfun1(A_81,B_79,'#skF_1','#skF_1',E_80,'#skF_3') = k5_relat_1(E_80,'#skF_3')
      | ~ v1_funct_1('#skF_3')
      | ~ m1_subset_1(E_80,k1_zfmisc_1(k2_zfmisc_1(A_81,B_79)))
      | ~ v1_funct_1(E_80) ) ),
    inference(resolution,[status(thm)],[c_32,c_304])).

tff(c_421,plain,(
    ! [A_87,B_88,E_89] :
      ( k1_partfun1(A_87,B_88,'#skF_1','#skF_1',E_89,'#skF_3') = k5_relat_1(E_89,'#skF_3')
      | ~ m1_subset_1(E_89,k1_zfmisc_1(k2_zfmisc_1(A_87,B_88)))
      | ~ v1_funct_1(E_89) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_314])).

tff(c_436,plain,
    ( k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2','#skF_3') = k5_relat_1('#skF_2','#skF_3')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_38,c_421])).

tff(c_446,plain,(
    k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2','#skF_3') = k5_relat_1('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_436])).

tff(c_30,plain,(
    r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2','#skF_3'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_131,plain,(
    ! [D_57,C_58,A_59,B_60] :
      ( D_57 = C_58
      | ~ r2_relset_1(A_59,B_60,C_58,D_57)
      | ~ m1_subset_1(D_57,k1_zfmisc_1(k2_zfmisc_1(A_59,B_60)))
      | ~ m1_subset_1(C_58,k1_zfmisc_1(k2_zfmisc_1(A_59,B_60))) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_135,plain,
    ( k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2','#skF_3') = '#skF_2'
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_30,c_131])).

tff(c_144,plain,
    ( k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2','#skF_3') = '#skF_2'
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_135])).

tff(c_162,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_144])).

tff(c_495,plain,(
    ~ m1_subset_1(k5_relat_1('#skF_2','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_446,c_162])).

tff(c_499,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_369,c_495])).

tff(c_500,plain,(
    k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2','#skF_3') = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_144])).

tff(c_646,plain,(
    ! [A_110,B_108,D_107,E_109,C_112,F_111] :
      ( k1_partfun1(A_110,B_108,C_112,D_107,E_109,F_111) = k5_relat_1(E_109,F_111)
      | ~ m1_subset_1(F_111,k1_zfmisc_1(k2_zfmisc_1(C_112,D_107)))
      | ~ v1_funct_1(F_111)
      | ~ m1_subset_1(E_109,k1_zfmisc_1(k2_zfmisc_1(A_110,B_108)))
      | ~ v1_funct_1(E_109) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_656,plain,(
    ! [A_110,B_108,E_109] :
      ( k1_partfun1(A_110,B_108,'#skF_1','#skF_1',E_109,'#skF_3') = k5_relat_1(E_109,'#skF_3')
      | ~ v1_funct_1('#skF_3')
      | ~ m1_subset_1(E_109,k1_zfmisc_1(k2_zfmisc_1(A_110,B_108)))
      | ~ v1_funct_1(E_109) ) ),
    inference(resolution,[status(thm)],[c_32,c_646])).

tff(c_758,plain,(
    ! [A_116,B_117,E_118] :
      ( k1_partfun1(A_116,B_117,'#skF_1','#skF_1',E_118,'#skF_3') = k5_relat_1(E_118,'#skF_3')
      | ~ m1_subset_1(E_118,k1_zfmisc_1(k2_zfmisc_1(A_116,B_117)))
      | ~ v1_funct_1(E_118) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_656])).

tff(c_773,plain,
    ( k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2','#skF_3') = k5_relat_1('#skF_2','#skF_3')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_38,c_758])).

tff(c_783,plain,(
    k5_relat_1('#skF_2','#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_500,c_773])).

tff(c_22,plain,(
    ! [A_37] : k6_relat_1(A_37) = k6_partfun1(A_37) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_6,plain,(
    ! [B_8,A_6] :
      ( k6_relat_1(k1_relat_1(B_8)) = B_8
      | k5_relat_1(A_6,B_8) != A_6
      | k2_relat_1(A_6) != k1_relat_1(B_8)
      | ~ v1_funct_1(B_8)
      | ~ v1_relat_1(B_8)
      | ~ v1_funct_1(A_6)
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_43,plain,(
    ! [B_8,A_6] :
      ( k6_partfun1(k1_relat_1(B_8)) = B_8
      | k5_relat_1(A_6,B_8) != A_6
      | k2_relat_1(A_6) != k1_relat_1(B_8)
      | ~ v1_funct_1(B_8)
      | ~ v1_relat_1(B_8)
      | ~ v1_funct_1(A_6)
      | ~ v1_relat_1(A_6) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_6])).

tff(c_796,plain,
    ( k6_partfun1(k1_relat_1('#skF_3')) = '#skF_3'
    | k2_relat_1('#skF_2') != k1_relat_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3')
    | ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_783,c_43])).

tff(c_801,plain,(
    k6_partfun1('#skF_1') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_67,c_42,c_70,c_36,c_86,c_125,c_125,c_796])).

tff(c_26,plain,(
    ~ r2_relset_1('#skF_1','#skF_1','#skF_3',k6_partfun1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_803,plain,(
    ~ r2_relset_1('#skF_1','#skF_1','#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_801,c_26])).

tff(c_806,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_77,c_803])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 11:07:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.16/1.53  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.16/1.54  
% 3.16/1.54  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.16/1.54  %$ r2_relset_1 > v1_funct_2 > m1_subset_1 > v1_relat_1 > v1_funct_1 > k4_relset_1 > k1_partfun1 > k2_relset_1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 3.16/1.54  
% 3.16/1.54  %Foreground sorts:
% 3.16/1.54  
% 3.16/1.54  
% 3.16/1.54  %Background operators:
% 3.16/1.54  
% 3.16/1.54  
% 3.16/1.54  %Foreground operators:
% 3.16/1.54  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 3.16/1.54  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.16/1.54  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.16/1.54  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 3.16/1.54  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 3.16/1.54  tff(k4_relset_1, type, k4_relset_1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.16/1.54  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.16/1.54  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.16/1.54  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.16/1.54  tff('#skF_2', type, '#skF_2': $i).
% 3.16/1.54  tff('#skF_3', type, '#skF_3': $i).
% 3.16/1.54  tff('#skF_1', type, '#skF_1': $i).
% 3.16/1.54  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.16/1.54  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.16/1.54  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 3.16/1.54  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.16/1.54  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.16/1.54  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.16/1.54  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 3.16/1.54  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.16/1.54  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.16/1.54  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.16/1.54  
% 3.16/1.56  tff(f_117, negated_conjecture, ~(![A, B]: (((v1_funct_1(B) & v1_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, A, A)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => ((r2_relset_1(A, A, k1_partfun1(A, A, A, A, B, C), B) & (k2_relset_1(A, A, B) = A)) => r2_relset_1(A, A, C, k6_partfun1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t75_funct_2)).
% 3.16/1.56  tff(f_77, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 3.16/1.56  tff(f_34, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 3.16/1.56  tff(f_32, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 3.16/1.56  tff(f_63, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 3.16/1.56  tff(f_59, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.16/1.56  tff(f_97, axiom, (![A, B]: (((v1_funct_1(B) & v1_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (k1_relset_1(A, A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t67_funct_2)).
% 3.16/1.56  tff(f_69, axiom, (![A, B, C, D, E, F]: ((m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k4_relset_1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k4_relset_1)).
% 3.16/1.56  tff(f_55, axiom, (![A, B, C, D, E, F]: ((m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => m1_subset_1(k4_relset_1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k4_relset_1)).
% 3.16/1.56  tff(f_87, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 3.16/1.56  tff(f_89, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 3.16/1.56  tff(f_49, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (((k2_relat_1(A) = k1_relat_1(B)) & (k5_relat_1(A, B) = A)) => (B = k6_relat_1(k1_relat_1(B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_funct_1)).
% 3.16/1.56  tff(c_32, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_117])).
% 3.16/1.56  tff(c_71, plain, (![A_46, B_47, D_48]: (r2_relset_1(A_46, B_47, D_48, D_48) | ~m1_subset_1(D_48, k1_zfmisc_1(k2_zfmisc_1(A_46, B_47))))), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.16/1.56  tff(c_77, plain, (r2_relset_1('#skF_1', '#skF_1', '#skF_3', '#skF_3')), inference(resolution, [status(thm)], [c_32, c_71])).
% 3.16/1.56  tff(c_4, plain, (![A_4, B_5]: (v1_relat_1(k2_zfmisc_1(A_4, B_5)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.16/1.56  tff(c_38, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_117])).
% 3.16/1.56  tff(c_58, plain, (![B_44, A_45]: (v1_relat_1(B_44) | ~m1_subset_1(B_44, k1_zfmisc_1(A_45)) | ~v1_relat_1(A_45))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.16/1.56  tff(c_61, plain, (v1_relat_1('#skF_2') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_1'))), inference(resolution, [status(thm)], [c_38, c_58])).
% 3.16/1.56  tff(c_67, plain, (v1_relat_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_61])).
% 3.16/1.56  tff(c_42, plain, (v1_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_117])).
% 3.16/1.56  tff(c_64, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_1'))), inference(resolution, [status(thm)], [c_32, c_58])).
% 3.16/1.56  tff(c_70, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_64])).
% 3.16/1.56  tff(c_36, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_117])).
% 3.16/1.56  tff(c_28, plain, (k2_relset_1('#skF_1', '#skF_1', '#skF_2')='#skF_1'), inference(cnfTransformation, [status(thm)], [f_117])).
% 3.16/1.56  tff(c_78, plain, (![A_49, B_50, C_51]: (k2_relset_1(A_49, B_50, C_51)=k2_relat_1(C_51) | ~m1_subset_1(C_51, k1_zfmisc_1(k2_zfmisc_1(A_49, B_50))))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.16/1.56  tff(c_81, plain, (k2_relset_1('#skF_1', '#skF_1', '#skF_2')=k2_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_38, c_78])).
% 3.16/1.56  tff(c_86, plain, (k2_relat_1('#skF_2')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_28, c_81])).
% 3.16/1.56  tff(c_34, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_117])).
% 3.16/1.56  tff(c_96, plain, (![A_52, B_53, C_54]: (k1_relset_1(A_52, B_53, C_54)=k1_relat_1(C_54) | ~m1_subset_1(C_54, k1_zfmisc_1(k2_zfmisc_1(A_52, B_53))))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.16/1.56  tff(c_104, plain, (k1_relset_1('#skF_1', '#skF_1', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_32, c_96])).
% 3.16/1.56  tff(c_113, plain, (![A_55, B_56]: (k1_relset_1(A_55, A_55, B_56)=A_55 | ~m1_subset_1(B_56, k1_zfmisc_1(k2_zfmisc_1(A_55, A_55))) | ~v1_funct_2(B_56, A_55, A_55) | ~v1_funct_1(B_56))), inference(cnfTransformation, [status(thm)], [f_97])).
% 3.16/1.56  tff(c_119, plain, (k1_relset_1('#skF_1', '#skF_1', '#skF_3')='#skF_1' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_32, c_113])).
% 3.16/1.56  tff(c_125, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_104, c_119])).
% 3.16/1.56  tff(c_164, plain, (![B_67, C_65, D_64, A_63, F_66, E_68]: (k4_relset_1(A_63, B_67, C_65, D_64, E_68, F_66)=k5_relat_1(E_68, F_66) | ~m1_subset_1(F_66, k1_zfmisc_1(k2_zfmisc_1(C_65, D_64))) | ~m1_subset_1(E_68, k1_zfmisc_1(k2_zfmisc_1(A_63, B_67))))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.16/1.56  tff(c_341, plain, (![A_84, B_85, E_86]: (k4_relset_1(A_84, B_85, '#skF_1', '#skF_1', E_86, '#skF_3')=k5_relat_1(E_86, '#skF_3') | ~m1_subset_1(E_86, k1_zfmisc_1(k2_zfmisc_1(A_84, B_85))))), inference(resolution, [status(thm)], [c_32, c_164])).
% 3.16/1.56  tff(c_360, plain, (k4_relset_1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', '#skF_3')=k5_relat_1('#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_38, c_341])).
% 3.16/1.56  tff(c_8, plain, (![C_11, E_13, B_10, F_14, D_12, A_9]: (m1_subset_1(k4_relset_1(A_9, B_10, C_11, D_12, E_13, F_14), k1_zfmisc_1(k2_zfmisc_1(A_9, D_12))) | ~m1_subset_1(F_14, k1_zfmisc_1(k2_zfmisc_1(C_11, D_12))) | ~m1_subset_1(E_13, k1_zfmisc_1(k2_zfmisc_1(A_9, B_10))))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.16/1.56  tff(c_365, plain, (m1_subset_1(k5_relat_1('#skF_2', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_360, c_8])).
% 3.16/1.56  tff(c_369, plain, (m1_subset_1(k5_relat_1('#skF_2', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_32, c_365])).
% 3.16/1.56  tff(c_304, plain, (![E_80, A_81, D_78, B_79, C_83, F_82]: (k1_partfun1(A_81, B_79, C_83, D_78, E_80, F_82)=k5_relat_1(E_80, F_82) | ~m1_subset_1(F_82, k1_zfmisc_1(k2_zfmisc_1(C_83, D_78))) | ~v1_funct_1(F_82) | ~m1_subset_1(E_80, k1_zfmisc_1(k2_zfmisc_1(A_81, B_79))) | ~v1_funct_1(E_80))), inference(cnfTransformation, [status(thm)], [f_87])).
% 3.16/1.56  tff(c_314, plain, (![A_81, B_79, E_80]: (k1_partfun1(A_81, B_79, '#skF_1', '#skF_1', E_80, '#skF_3')=k5_relat_1(E_80, '#skF_3') | ~v1_funct_1('#skF_3') | ~m1_subset_1(E_80, k1_zfmisc_1(k2_zfmisc_1(A_81, B_79))) | ~v1_funct_1(E_80))), inference(resolution, [status(thm)], [c_32, c_304])).
% 3.16/1.56  tff(c_421, plain, (![A_87, B_88, E_89]: (k1_partfun1(A_87, B_88, '#skF_1', '#skF_1', E_89, '#skF_3')=k5_relat_1(E_89, '#skF_3') | ~m1_subset_1(E_89, k1_zfmisc_1(k2_zfmisc_1(A_87, B_88))) | ~v1_funct_1(E_89))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_314])).
% 3.16/1.56  tff(c_436, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', '#skF_3')=k5_relat_1('#skF_2', '#skF_3') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_38, c_421])).
% 3.16/1.56  tff(c_446, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', '#skF_3')=k5_relat_1('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_436])).
% 3.16/1.56  tff(c_30, plain, (r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', '#skF_3'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_117])).
% 3.16/1.56  tff(c_131, plain, (![D_57, C_58, A_59, B_60]: (D_57=C_58 | ~r2_relset_1(A_59, B_60, C_58, D_57) | ~m1_subset_1(D_57, k1_zfmisc_1(k2_zfmisc_1(A_59, B_60))) | ~m1_subset_1(C_58, k1_zfmisc_1(k2_zfmisc_1(A_59, B_60))))), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.16/1.56  tff(c_135, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', '#skF_3')='#skF_2' | ~m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_30, c_131])).
% 3.16/1.56  tff(c_144, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', '#skF_3')='#skF_2' | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_135])).
% 3.16/1.56  tff(c_162, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_144])).
% 3.16/1.56  tff(c_495, plain, (~m1_subset_1(k5_relat_1('#skF_2', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_446, c_162])).
% 3.16/1.56  tff(c_499, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_369, c_495])).
% 3.16/1.56  tff(c_500, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', '#skF_3')='#skF_2'), inference(splitRight, [status(thm)], [c_144])).
% 3.16/1.56  tff(c_646, plain, (![A_110, B_108, D_107, E_109, C_112, F_111]: (k1_partfun1(A_110, B_108, C_112, D_107, E_109, F_111)=k5_relat_1(E_109, F_111) | ~m1_subset_1(F_111, k1_zfmisc_1(k2_zfmisc_1(C_112, D_107))) | ~v1_funct_1(F_111) | ~m1_subset_1(E_109, k1_zfmisc_1(k2_zfmisc_1(A_110, B_108))) | ~v1_funct_1(E_109))), inference(cnfTransformation, [status(thm)], [f_87])).
% 3.16/1.56  tff(c_656, plain, (![A_110, B_108, E_109]: (k1_partfun1(A_110, B_108, '#skF_1', '#skF_1', E_109, '#skF_3')=k5_relat_1(E_109, '#skF_3') | ~v1_funct_1('#skF_3') | ~m1_subset_1(E_109, k1_zfmisc_1(k2_zfmisc_1(A_110, B_108))) | ~v1_funct_1(E_109))), inference(resolution, [status(thm)], [c_32, c_646])).
% 3.16/1.56  tff(c_758, plain, (![A_116, B_117, E_118]: (k1_partfun1(A_116, B_117, '#skF_1', '#skF_1', E_118, '#skF_3')=k5_relat_1(E_118, '#skF_3') | ~m1_subset_1(E_118, k1_zfmisc_1(k2_zfmisc_1(A_116, B_117))) | ~v1_funct_1(E_118))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_656])).
% 3.16/1.56  tff(c_773, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', '#skF_3')=k5_relat_1('#skF_2', '#skF_3') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_38, c_758])).
% 3.16/1.56  tff(c_783, plain, (k5_relat_1('#skF_2', '#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_42, c_500, c_773])).
% 3.16/1.56  tff(c_22, plain, (![A_37]: (k6_relat_1(A_37)=k6_partfun1(A_37))), inference(cnfTransformation, [status(thm)], [f_89])).
% 3.16/1.56  tff(c_6, plain, (![B_8, A_6]: (k6_relat_1(k1_relat_1(B_8))=B_8 | k5_relat_1(A_6, B_8)!=A_6 | k2_relat_1(A_6)!=k1_relat_1(B_8) | ~v1_funct_1(B_8) | ~v1_relat_1(B_8) | ~v1_funct_1(A_6) | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.16/1.56  tff(c_43, plain, (![B_8, A_6]: (k6_partfun1(k1_relat_1(B_8))=B_8 | k5_relat_1(A_6, B_8)!=A_6 | k2_relat_1(A_6)!=k1_relat_1(B_8) | ~v1_funct_1(B_8) | ~v1_relat_1(B_8) | ~v1_funct_1(A_6) | ~v1_relat_1(A_6))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_6])).
% 3.16/1.56  tff(c_796, plain, (k6_partfun1(k1_relat_1('#skF_3'))='#skF_3' | k2_relat_1('#skF_2')!=k1_relat_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3') | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_783, c_43])).
% 3.16/1.56  tff(c_801, plain, (k6_partfun1('#skF_1')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_67, c_42, c_70, c_36, c_86, c_125, c_125, c_796])).
% 3.16/1.56  tff(c_26, plain, (~r2_relset_1('#skF_1', '#skF_1', '#skF_3', k6_partfun1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_117])).
% 3.16/1.56  tff(c_803, plain, (~r2_relset_1('#skF_1', '#skF_1', '#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_801, c_26])).
% 3.16/1.56  tff(c_806, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_77, c_803])).
% 3.16/1.56  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.16/1.56  
% 3.16/1.56  Inference rules
% 3.16/1.56  ----------------------
% 3.16/1.56  #Ref     : 0
% 3.16/1.56  #Sup     : 198
% 3.16/1.56  #Fact    : 0
% 3.16/1.56  #Define  : 0
% 3.16/1.56  #Split   : 1
% 3.16/1.56  #Chain   : 0
% 3.16/1.56  #Close   : 0
% 3.16/1.56  
% 3.16/1.56  Ordering : KBO
% 3.16/1.56  
% 3.16/1.56  Simplification rules
% 3.16/1.56  ----------------------
% 3.16/1.56  #Subsume      : 0
% 3.16/1.56  #Demod        : 82
% 3.16/1.56  #Tautology    : 72
% 3.16/1.56  #SimpNegUnit  : 0
% 3.16/1.56  #BackRed      : 10
% 3.16/1.56  
% 3.16/1.56  #Partial instantiations: 0
% 3.16/1.56  #Strategies tried      : 1
% 3.16/1.56  
% 3.16/1.56  Timing (in seconds)
% 3.16/1.56  ----------------------
% 3.16/1.56  Preprocessing        : 0.34
% 3.16/1.56  Parsing              : 0.19
% 3.16/1.56  CNF conversion       : 0.02
% 3.16/1.56  Main loop            : 0.36
% 3.16/1.56  Inferencing          : 0.13
% 3.16/1.56  Reduction            : 0.11
% 3.16/1.56  Demodulation         : 0.08
% 3.16/1.56  BG Simplification    : 0.02
% 3.16/1.56  Subsumption          : 0.07
% 3.16/1.56  Abstraction          : 0.03
% 3.16/1.56  MUC search           : 0.00
% 3.16/1.56  Cooper               : 0.00
% 3.16/1.56  Total                : 0.74
% 3.16/1.56  Index Insertion      : 0.00
% 3.16/1.56  Index Deletion       : 0.00
% 3.16/1.56  Index Matching       : 0.00
% 3.16/1.56  BG Taut test         : 0.00
%------------------------------------------------------------------------------
