%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:15:37 EST 2020

% Result     : Theorem 2.77s
% Output     : CNFRefutation 3.11s
% Verified   : 
% Statistics : Number of formulae       :   84 ( 154 expanded)
%              Number of leaves         :   33 (  70 expanded)
%              Depth                    :    9
%              Number of atoms          :  152 ( 498 expanded)
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

tff(f_112,negated_conjecture,(
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

tff(f_72,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_44,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_58,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_54,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_92,axiom,(
    ! [A,B] :
      ( ( v1_funct_1(B)
        & v1_funct_2(B,A,A)
        & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
     => k1_relset_1(A,A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_funct_2)).

tff(f_64,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k4_relset_1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_relset_1)).

tff(f_50,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => m1_subset_1(k4_relset_1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_relset_1)).

tff(f_82,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_84,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_40,axiom,(
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

tff(c_30,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_64,plain,(
    ! [A_43,B_44,D_45] :
      ( r2_relset_1(A_43,B_44,D_45,D_45)
      | ~ m1_subset_1(D_45,k1_zfmisc_1(k2_zfmisc_1(A_43,B_44))) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_70,plain,(
    r2_relset_1('#skF_1','#skF_1','#skF_3','#skF_3') ),
    inference(resolution,[status(thm)],[c_30,c_64])).

tff(c_36,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_55,plain,(
    ! [C_40,A_41,B_42] :
      ( v1_relat_1(C_40)
      | ~ m1_subset_1(C_40,k1_zfmisc_1(k2_zfmisc_1(A_41,B_42))) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_62,plain,(
    v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_36,c_55])).

tff(c_40,plain,(
    v1_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_63,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_30,c_55])).

tff(c_34,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_26,plain,(
    k2_relset_1('#skF_1','#skF_1','#skF_2') = '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_71,plain,(
    ! [A_46,B_47,C_48] :
      ( k2_relset_1(A_46,B_47,C_48) = k2_relat_1(C_48)
      | ~ m1_subset_1(C_48,k1_zfmisc_1(k2_zfmisc_1(A_46,B_47))) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_74,plain,(
    k2_relset_1('#skF_1','#skF_1','#skF_2') = k2_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_36,c_71])).

tff(c_79,plain,(
    k2_relat_1('#skF_2') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_74])).

tff(c_32,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_89,plain,(
    ! [A_49,B_50,C_51] :
      ( k1_relset_1(A_49,B_50,C_51) = k1_relat_1(C_51)
      | ~ m1_subset_1(C_51,k1_zfmisc_1(k2_zfmisc_1(A_49,B_50))) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_97,plain,(
    k1_relset_1('#skF_1','#skF_1','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_30,c_89])).

tff(c_106,plain,(
    ! [A_52,B_53] :
      ( k1_relset_1(A_52,A_52,B_53) = A_52
      | ~ m1_subset_1(B_53,k1_zfmisc_1(k2_zfmisc_1(A_52,A_52)))
      | ~ v1_funct_2(B_53,A_52,A_52)
      | ~ v1_funct_1(B_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_112,plain,
    ( k1_relset_1('#skF_1','#skF_1','#skF_3') = '#skF_1'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_30,c_106])).

tff(c_118,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_97,c_112])).

tff(c_157,plain,(
    ! [E_61,B_62,F_64,A_63,D_65,C_60] :
      ( k4_relset_1(A_63,B_62,C_60,D_65,E_61,F_64) = k5_relat_1(E_61,F_64)
      | ~ m1_subset_1(F_64,k1_zfmisc_1(k2_zfmisc_1(C_60,D_65)))
      | ~ m1_subset_1(E_61,k1_zfmisc_1(k2_zfmisc_1(A_63,B_62))) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_271,plain,(
    ! [A_75,B_76,E_77] :
      ( k4_relset_1(A_75,B_76,'#skF_1','#skF_1',E_77,'#skF_3') = k5_relat_1(E_77,'#skF_3')
      | ~ m1_subset_1(E_77,k1_zfmisc_1(k2_zfmisc_1(A_75,B_76))) ) ),
    inference(resolution,[status(thm)],[c_30,c_157])).

tff(c_290,plain,(
    k4_relset_1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2','#skF_3') = k5_relat_1('#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_36,c_271])).

tff(c_6,plain,(
    ! [D_10,A_7,F_12,B_8,E_11,C_9] :
      ( m1_subset_1(k4_relset_1(A_7,B_8,C_9,D_10,E_11,F_12),k1_zfmisc_1(k2_zfmisc_1(A_7,D_10)))
      | ~ m1_subset_1(F_12,k1_zfmisc_1(k2_zfmisc_1(C_9,D_10)))
      | ~ m1_subset_1(E_11,k1_zfmisc_1(k2_zfmisc_1(A_7,B_8))) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_307,plain,
    ( m1_subset_1(k5_relat_1('#skF_2','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_290,c_6])).

tff(c_311,plain,(
    m1_subset_1(k5_relat_1('#skF_2','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_30,c_307])).

tff(c_343,plain,(
    ! [D_78,B_79,F_81,C_83,A_80,E_82] :
      ( k1_partfun1(A_80,B_79,C_83,D_78,E_82,F_81) = k5_relat_1(E_82,F_81)
      | ~ m1_subset_1(F_81,k1_zfmisc_1(k2_zfmisc_1(C_83,D_78)))
      | ~ v1_funct_1(F_81)
      | ~ m1_subset_1(E_82,k1_zfmisc_1(k2_zfmisc_1(A_80,B_79)))
      | ~ v1_funct_1(E_82) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_355,plain,(
    ! [A_80,B_79,E_82] :
      ( k1_partfun1(A_80,B_79,'#skF_1','#skF_1',E_82,'#skF_3') = k5_relat_1(E_82,'#skF_3')
      | ~ v1_funct_1('#skF_3')
      | ~ m1_subset_1(E_82,k1_zfmisc_1(k2_zfmisc_1(A_80,B_79)))
      | ~ v1_funct_1(E_82) ) ),
    inference(resolution,[status(thm)],[c_30,c_343])).

tff(c_437,plain,(
    ! [A_84,B_85,E_86] :
      ( k1_partfun1(A_84,B_85,'#skF_1','#skF_1',E_86,'#skF_3') = k5_relat_1(E_86,'#skF_3')
      | ~ m1_subset_1(E_86,k1_zfmisc_1(k2_zfmisc_1(A_84,B_85)))
      | ~ v1_funct_1(E_86) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_355])).

tff(c_455,plain,
    ( k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2','#skF_3') = k5_relat_1('#skF_2','#skF_3')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_36,c_437])).

tff(c_466,plain,(
    k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2','#skF_3') = k5_relat_1('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_455])).

tff(c_28,plain,(
    r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2','#skF_3'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_129,plain,(
    ! [D_54,C_55,A_56,B_57] :
      ( D_54 = C_55
      | ~ r2_relset_1(A_56,B_57,C_55,D_54)
      | ~ m1_subset_1(D_54,k1_zfmisc_1(k2_zfmisc_1(A_56,B_57)))
      | ~ m1_subset_1(C_55,k1_zfmisc_1(k2_zfmisc_1(A_56,B_57))) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_135,plain,
    ( k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2','#skF_3') = '#skF_2'
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_28,c_129])).

tff(c_146,plain,
    ( k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2','#skF_3') = '#skF_2'
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_135])).

tff(c_156,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_146])).

tff(c_470,plain,(
    ~ m1_subset_1(k5_relat_1('#skF_2','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_466,c_156])).

tff(c_474,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_311,c_470])).

tff(c_475,plain,(
    k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2','#skF_3') = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_146])).

tff(c_697,plain,(
    ! [C_110,F_108,A_107,E_109,D_105,B_106] :
      ( k1_partfun1(A_107,B_106,C_110,D_105,E_109,F_108) = k5_relat_1(E_109,F_108)
      | ~ m1_subset_1(F_108,k1_zfmisc_1(k2_zfmisc_1(C_110,D_105)))
      | ~ v1_funct_1(F_108)
      | ~ m1_subset_1(E_109,k1_zfmisc_1(k2_zfmisc_1(A_107,B_106)))
      | ~ v1_funct_1(E_109) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_711,plain,(
    ! [A_107,B_106,E_109] :
      ( k1_partfun1(A_107,B_106,'#skF_1','#skF_1',E_109,'#skF_3') = k5_relat_1(E_109,'#skF_3')
      | ~ v1_funct_1('#skF_3')
      | ~ m1_subset_1(E_109,k1_zfmisc_1(k2_zfmisc_1(A_107,B_106)))
      | ~ v1_funct_1(E_109) ) ),
    inference(resolution,[status(thm)],[c_30,c_697])).

tff(c_772,plain,(
    ! [A_111,B_112,E_113] :
      ( k1_partfun1(A_111,B_112,'#skF_1','#skF_1',E_113,'#skF_3') = k5_relat_1(E_113,'#skF_3')
      | ~ m1_subset_1(E_113,k1_zfmisc_1(k2_zfmisc_1(A_111,B_112)))
      | ~ v1_funct_1(E_113) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_711])).

tff(c_790,plain,
    ( k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2','#skF_3') = k5_relat_1('#skF_2','#skF_3')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_36,c_772])).

tff(c_801,plain,(
    k5_relat_1('#skF_2','#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_475,c_790])).

tff(c_20,plain,(
    ! [A_35] : k6_relat_1(A_35) = k6_partfun1(A_35) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_2,plain,(
    ! [B_3,A_1] :
      ( k6_relat_1(k1_relat_1(B_3)) = B_3
      | k5_relat_1(A_1,B_3) != A_1
      | k2_relat_1(A_1) != k1_relat_1(B_3)
      | ~ v1_funct_1(B_3)
      | ~ v1_relat_1(B_3)
      | ~ v1_funct_1(A_1)
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_41,plain,(
    ! [B_3,A_1] :
      ( k6_partfun1(k1_relat_1(B_3)) = B_3
      | k5_relat_1(A_1,B_3) != A_1
      | k2_relat_1(A_1) != k1_relat_1(B_3)
      | ~ v1_funct_1(B_3)
      | ~ v1_relat_1(B_3)
      | ~ v1_funct_1(A_1)
      | ~ v1_relat_1(A_1) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_2])).

tff(c_818,plain,
    ( k6_partfun1(k1_relat_1('#skF_3')) = '#skF_3'
    | k2_relat_1('#skF_2') != k1_relat_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3')
    | ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_801,c_41])).

tff(c_823,plain,(
    k6_partfun1('#skF_1') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_40,c_63,c_34,c_79,c_118,c_118,c_818])).

tff(c_24,plain,(
    ~ r2_relset_1('#skF_1','#skF_1','#skF_3',k6_partfun1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_825,plain,(
    ~ r2_relset_1('#skF_1','#skF_1','#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_823,c_24])).

tff(c_828,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_825])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n020.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 14:41:22 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.77/1.44  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.77/1.44  
% 2.77/1.44  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.77/1.45  %$ r2_relset_1 > v1_funct_2 > m1_subset_1 > v1_relat_1 > v1_funct_1 > k4_relset_1 > k1_partfun1 > k2_relset_1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 2.77/1.45  
% 2.77/1.45  %Foreground sorts:
% 2.77/1.45  
% 2.77/1.45  
% 2.77/1.45  %Background operators:
% 2.77/1.45  
% 2.77/1.45  
% 2.77/1.45  %Foreground operators:
% 2.77/1.45  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 2.77/1.45  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.77/1.45  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.77/1.45  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 2.77/1.45  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.77/1.45  tff(k4_relset_1, type, k4_relset_1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.77/1.45  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.77/1.45  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.77/1.45  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.77/1.45  tff('#skF_2', type, '#skF_2': $i).
% 2.77/1.45  tff('#skF_3', type, '#skF_3': $i).
% 2.77/1.45  tff('#skF_1', type, '#skF_1': $i).
% 2.77/1.45  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.77/1.45  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.77/1.45  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 2.77/1.45  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.77/1.45  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.77/1.45  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.77/1.45  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 2.77/1.45  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.77/1.45  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.77/1.45  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.77/1.45  
% 3.11/1.46  tff(f_112, negated_conjecture, ~(![A, B]: (((v1_funct_1(B) & v1_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, A, A)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => ((r2_relset_1(A, A, k1_partfun1(A, A, A, A, B, C), B) & (k2_relset_1(A, A, B) = A)) => r2_relset_1(A, A, C, k6_partfun1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t75_funct_2)).
% 3.11/1.46  tff(f_72, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 3.11/1.46  tff(f_44, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.11/1.46  tff(f_58, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 3.11/1.46  tff(f_54, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.11/1.46  tff(f_92, axiom, (![A, B]: (((v1_funct_1(B) & v1_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (k1_relset_1(A, A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t67_funct_2)).
% 3.11/1.46  tff(f_64, axiom, (![A, B, C, D, E, F]: ((m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k4_relset_1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k4_relset_1)).
% 3.11/1.46  tff(f_50, axiom, (![A, B, C, D, E, F]: ((m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => m1_subset_1(k4_relset_1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k4_relset_1)).
% 3.11/1.46  tff(f_82, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 3.11/1.46  tff(f_84, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 3.11/1.46  tff(f_40, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (((k2_relat_1(A) = k1_relat_1(B)) & (k5_relat_1(A, B) = A)) => (B = k6_relat_1(k1_relat_1(B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_funct_1)).
% 3.11/1.46  tff(c_30, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_112])).
% 3.11/1.46  tff(c_64, plain, (![A_43, B_44, D_45]: (r2_relset_1(A_43, B_44, D_45, D_45) | ~m1_subset_1(D_45, k1_zfmisc_1(k2_zfmisc_1(A_43, B_44))))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.11/1.46  tff(c_70, plain, (r2_relset_1('#skF_1', '#skF_1', '#skF_3', '#skF_3')), inference(resolution, [status(thm)], [c_30, c_64])).
% 3.11/1.46  tff(c_36, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_112])).
% 3.11/1.46  tff(c_55, plain, (![C_40, A_41, B_42]: (v1_relat_1(C_40) | ~m1_subset_1(C_40, k1_zfmisc_1(k2_zfmisc_1(A_41, B_42))))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.11/1.46  tff(c_62, plain, (v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_36, c_55])).
% 3.11/1.46  tff(c_40, plain, (v1_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_112])).
% 3.11/1.46  tff(c_63, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_30, c_55])).
% 3.11/1.46  tff(c_34, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_112])).
% 3.11/1.46  tff(c_26, plain, (k2_relset_1('#skF_1', '#skF_1', '#skF_2')='#skF_1'), inference(cnfTransformation, [status(thm)], [f_112])).
% 3.11/1.46  tff(c_71, plain, (![A_46, B_47, C_48]: (k2_relset_1(A_46, B_47, C_48)=k2_relat_1(C_48) | ~m1_subset_1(C_48, k1_zfmisc_1(k2_zfmisc_1(A_46, B_47))))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.11/1.46  tff(c_74, plain, (k2_relset_1('#skF_1', '#skF_1', '#skF_2')=k2_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_36, c_71])).
% 3.11/1.46  tff(c_79, plain, (k2_relat_1('#skF_2')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_26, c_74])).
% 3.11/1.46  tff(c_32, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_112])).
% 3.11/1.46  tff(c_89, plain, (![A_49, B_50, C_51]: (k1_relset_1(A_49, B_50, C_51)=k1_relat_1(C_51) | ~m1_subset_1(C_51, k1_zfmisc_1(k2_zfmisc_1(A_49, B_50))))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.11/1.46  tff(c_97, plain, (k1_relset_1('#skF_1', '#skF_1', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_30, c_89])).
% 3.11/1.46  tff(c_106, plain, (![A_52, B_53]: (k1_relset_1(A_52, A_52, B_53)=A_52 | ~m1_subset_1(B_53, k1_zfmisc_1(k2_zfmisc_1(A_52, A_52))) | ~v1_funct_2(B_53, A_52, A_52) | ~v1_funct_1(B_53))), inference(cnfTransformation, [status(thm)], [f_92])).
% 3.11/1.46  tff(c_112, plain, (k1_relset_1('#skF_1', '#skF_1', '#skF_3')='#skF_1' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_30, c_106])).
% 3.11/1.46  tff(c_118, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_97, c_112])).
% 3.11/1.46  tff(c_157, plain, (![E_61, B_62, F_64, A_63, D_65, C_60]: (k4_relset_1(A_63, B_62, C_60, D_65, E_61, F_64)=k5_relat_1(E_61, F_64) | ~m1_subset_1(F_64, k1_zfmisc_1(k2_zfmisc_1(C_60, D_65))) | ~m1_subset_1(E_61, k1_zfmisc_1(k2_zfmisc_1(A_63, B_62))))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.11/1.46  tff(c_271, plain, (![A_75, B_76, E_77]: (k4_relset_1(A_75, B_76, '#skF_1', '#skF_1', E_77, '#skF_3')=k5_relat_1(E_77, '#skF_3') | ~m1_subset_1(E_77, k1_zfmisc_1(k2_zfmisc_1(A_75, B_76))))), inference(resolution, [status(thm)], [c_30, c_157])).
% 3.11/1.46  tff(c_290, plain, (k4_relset_1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', '#skF_3')=k5_relat_1('#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_36, c_271])).
% 3.11/1.46  tff(c_6, plain, (![D_10, A_7, F_12, B_8, E_11, C_9]: (m1_subset_1(k4_relset_1(A_7, B_8, C_9, D_10, E_11, F_12), k1_zfmisc_1(k2_zfmisc_1(A_7, D_10))) | ~m1_subset_1(F_12, k1_zfmisc_1(k2_zfmisc_1(C_9, D_10))) | ~m1_subset_1(E_11, k1_zfmisc_1(k2_zfmisc_1(A_7, B_8))))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.11/1.46  tff(c_307, plain, (m1_subset_1(k5_relat_1('#skF_2', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_290, c_6])).
% 3.11/1.46  tff(c_311, plain, (m1_subset_1(k5_relat_1('#skF_2', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_30, c_307])).
% 3.11/1.46  tff(c_343, plain, (![D_78, B_79, F_81, C_83, A_80, E_82]: (k1_partfun1(A_80, B_79, C_83, D_78, E_82, F_81)=k5_relat_1(E_82, F_81) | ~m1_subset_1(F_81, k1_zfmisc_1(k2_zfmisc_1(C_83, D_78))) | ~v1_funct_1(F_81) | ~m1_subset_1(E_82, k1_zfmisc_1(k2_zfmisc_1(A_80, B_79))) | ~v1_funct_1(E_82))), inference(cnfTransformation, [status(thm)], [f_82])).
% 3.11/1.46  tff(c_355, plain, (![A_80, B_79, E_82]: (k1_partfun1(A_80, B_79, '#skF_1', '#skF_1', E_82, '#skF_3')=k5_relat_1(E_82, '#skF_3') | ~v1_funct_1('#skF_3') | ~m1_subset_1(E_82, k1_zfmisc_1(k2_zfmisc_1(A_80, B_79))) | ~v1_funct_1(E_82))), inference(resolution, [status(thm)], [c_30, c_343])).
% 3.11/1.46  tff(c_437, plain, (![A_84, B_85, E_86]: (k1_partfun1(A_84, B_85, '#skF_1', '#skF_1', E_86, '#skF_3')=k5_relat_1(E_86, '#skF_3') | ~m1_subset_1(E_86, k1_zfmisc_1(k2_zfmisc_1(A_84, B_85))) | ~v1_funct_1(E_86))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_355])).
% 3.11/1.46  tff(c_455, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', '#skF_3')=k5_relat_1('#skF_2', '#skF_3') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_36, c_437])).
% 3.11/1.46  tff(c_466, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', '#skF_3')=k5_relat_1('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_455])).
% 3.11/1.46  tff(c_28, plain, (r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', '#skF_3'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_112])).
% 3.11/1.46  tff(c_129, plain, (![D_54, C_55, A_56, B_57]: (D_54=C_55 | ~r2_relset_1(A_56, B_57, C_55, D_54) | ~m1_subset_1(D_54, k1_zfmisc_1(k2_zfmisc_1(A_56, B_57))) | ~m1_subset_1(C_55, k1_zfmisc_1(k2_zfmisc_1(A_56, B_57))))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.11/1.46  tff(c_135, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', '#skF_3')='#skF_2' | ~m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_28, c_129])).
% 3.11/1.46  tff(c_146, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', '#skF_3')='#skF_2' | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_135])).
% 3.11/1.46  tff(c_156, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_146])).
% 3.11/1.46  tff(c_470, plain, (~m1_subset_1(k5_relat_1('#skF_2', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_466, c_156])).
% 3.11/1.46  tff(c_474, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_311, c_470])).
% 3.11/1.46  tff(c_475, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', '#skF_3')='#skF_2'), inference(splitRight, [status(thm)], [c_146])).
% 3.11/1.46  tff(c_697, plain, (![C_110, F_108, A_107, E_109, D_105, B_106]: (k1_partfun1(A_107, B_106, C_110, D_105, E_109, F_108)=k5_relat_1(E_109, F_108) | ~m1_subset_1(F_108, k1_zfmisc_1(k2_zfmisc_1(C_110, D_105))) | ~v1_funct_1(F_108) | ~m1_subset_1(E_109, k1_zfmisc_1(k2_zfmisc_1(A_107, B_106))) | ~v1_funct_1(E_109))), inference(cnfTransformation, [status(thm)], [f_82])).
% 3.11/1.46  tff(c_711, plain, (![A_107, B_106, E_109]: (k1_partfun1(A_107, B_106, '#skF_1', '#skF_1', E_109, '#skF_3')=k5_relat_1(E_109, '#skF_3') | ~v1_funct_1('#skF_3') | ~m1_subset_1(E_109, k1_zfmisc_1(k2_zfmisc_1(A_107, B_106))) | ~v1_funct_1(E_109))), inference(resolution, [status(thm)], [c_30, c_697])).
% 3.11/1.46  tff(c_772, plain, (![A_111, B_112, E_113]: (k1_partfun1(A_111, B_112, '#skF_1', '#skF_1', E_113, '#skF_3')=k5_relat_1(E_113, '#skF_3') | ~m1_subset_1(E_113, k1_zfmisc_1(k2_zfmisc_1(A_111, B_112))) | ~v1_funct_1(E_113))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_711])).
% 3.11/1.46  tff(c_790, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', '#skF_3')=k5_relat_1('#skF_2', '#skF_3') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_36, c_772])).
% 3.11/1.46  tff(c_801, plain, (k5_relat_1('#skF_2', '#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_40, c_475, c_790])).
% 3.11/1.46  tff(c_20, plain, (![A_35]: (k6_relat_1(A_35)=k6_partfun1(A_35))), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.11/1.46  tff(c_2, plain, (![B_3, A_1]: (k6_relat_1(k1_relat_1(B_3))=B_3 | k5_relat_1(A_1, B_3)!=A_1 | k2_relat_1(A_1)!=k1_relat_1(B_3) | ~v1_funct_1(B_3) | ~v1_relat_1(B_3) | ~v1_funct_1(A_1) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.11/1.46  tff(c_41, plain, (![B_3, A_1]: (k6_partfun1(k1_relat_1(B_3))=B_3 | k5_relat_1(A_1, B_3)!=A_1 | k2_relat_1(A_1)!=k1_relat_1(B_3) | ~v1_funct_1(B_3) | ~v1_relat_1(B_3) | ~v1_funct_1(A_1) | ~v1_relat_1(A_1))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_2])).
% 3.11/1.46  tff(c_818, plain, (k6_partfun1(k1_relat_1('#skF_3'))='#skF_3' | k2_relat_1('#skF_2')!=k1_relat_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3') | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_801, c_41])).
% 3.11/1.46  tff(c_823, plain, (k6_partfun1('#skF_1')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_62, c_40, c_63, c_34, c_79, c_118, c_118, c_818])).
% 3.11/1.46  tff(c_24, plain, (~r2_relset_1('#skF_1', '#skF_1', '#skF_3', k6_partfun1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_112])).
% 3.11/1.46  tff(c_825, plain, (~r2_relset_1('#skF_1', '#skF_1', '#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_823, c_24])).
% 3.11/1.46  tff(c_828, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_70, c_825])).
% 3.11/1.46  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.11/1.46  
% 3.11/1.46  Inference rules
% 3.11/1.46  ----------------------
% 3.11/1.46  #Ref     : 0
% 3.11/1.46  #Sup     : 208
% 3.11/1.46  #Fact    : 0
% 3.11/1.46  #Define  : 0
% 3.11/1.46  #Split   : 1
% 3.11/1.46  #Chain   : 0
% 3.11/1.46  #Close   : 0
% 3.11/1.46  
% 3.11/1.46  Ordering : KBO
% 3.11/1.46  
% 3.11/1.46  Simplification rules
% 3.11/1.46  ----------------------
% 3.11/1.46  #Subsume      : 0
% 3.11/1.46  #Demod        : 82
% 3.11/1.46  #Tautology    : 73
% 3.11/1.46  #SimpNegUnit  : 0
% 3.11/1.46  #BackRed      : 12
% 3.11/1.46  
% 3.11/1.46  #Partial instantiations: 0
% 3.11/1.46  #Strategies tried      : 1
% 3.11/1.46  
% 3.11/1.46  Timing (in seconds)
% 3.11/1.46  ----------------------
% 3.11/1.47  Preprocessing        : 0.33
% 3.11/1.47  Parsing              : 0.18
% 3.11/1.47  CNF conversion       : 0.02
% 3.11/1.47  Main loop            : 0.37
% 3.11/1.47  Inferencing          : 0.14
% 3.11/1.47  Reduction            : 0.11
% 3.11/1.47  Demodulation         : 0.08
% 3.11/1.47  BG Simplification    : 0.02
% 3.11/1.47  Subsumption          : 0.06
% 3.11/1.47  Abstraction          : 0.03
% 3.11/1.47  MUC search           : 0.00
% 3.11/1.47  Cooper               : 0.00
% 3.11/1.47  Total                : 0.73
% 3.11/1.47  Index Insertion      : 0.00
% 3.11/1.47  Index Deletion       : 0.00
% 3.11/1.47  Index Matching       : 0.00
% 3.11/1.47  BG Taut test         : 0.00
%------------------------------------------------------------------------------
