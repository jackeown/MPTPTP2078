%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:15:37 EST 2020

% Result     : Theorem 2.66s
% Output     : CNFRefutation 2.66s
% Verified   : 
% Statistics : Number of formulae       :   79 ( 163 expanded)
%              Number of leaves         :   31 (  73 expanded)
%              Depth                    :    9
%              Number of atoms          :  150 ( 556 expanded)
%              Number of equality atoms :   43 (  97 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > m1_subset_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

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

tff(f_60,axiom,(
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

tff(f_52,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_48,axiom,(
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

tff(f_82,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_72,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( v1_funct_1(k1_partfun1(A,B,C,D,E,F))
        & m1_subset_1(k1_partfun1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).

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
    ! [A_37,B_38,D_39] :
      ( r2_relset_1(A_37,B_38,D_39,D_39)
      | ~ m1_subset_1(D_39,k1_zfmisc_1(k2_zfmisc_1(A_37,B_38))) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_70,plain,(
    r2_relset_1('#skF_1','#skF_1','#skF_3','#skF_3') ),
    inference(resolution,[status(thm)],[c_30,c_64])).

tff(c_36,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_55,plain,(
    ! [C_34,A_35,B_36] :
      ( v1_relat_1(C_34)
      | ~ m1_subset_1(C_34,k1_zfmisc_1(k2_zfmisc_1(A_35,B_36))) ) ),
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
    ! [A_40,B_41,C_42] :
      ( k2_relset_1(A_40,B_41,C_42) = k2_relat_1(C_42)
      | ~ m1_subset_1(C_42,k1_zfmisc_1(k2_zfmisc_1(A_40,B_41))) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

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
    ! [A_43,B_44,C_45] :
      ( k1_relset_1(A_43,B_44,C_45) = k1_relat_1(C_45)
      | ~ m1_subset_1(C_45,k1_zfmisc_1(k2_zfmisc_1(A_43,B_44))) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_97,plain,(
    k1_relset_1('#skF_1','#skF_1','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_30,c_89])).

tff(c_106,plain,(
    ! [A_46,B_47] :
      ( k1_relset_1(A_46,A_46,B_47) = A_46
      | ~ m1_subset_1(B_47,k1_zfmisc_1(k2_zfmisc_1(A_46,A_46)))
      | ~ v1_funct_2(B_47,A_46,A_46)
      | ~ v1_funct_1(B_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_112,plain,
    ( k1_relset_1('#skF_1','#skF_1','#skF_3') = '#skF_1'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_30,c_106])).

tff(c_118,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_97,c_112])).

tff(c_181,plain,(
    ! [B_66,F_64,D_67,E_65,C_63,A_68] :
      ( k1_partfun1(A_68,B_66,C_63,D_67,E_65,F_64) = k5_relat_1(E_65,F_64)
      | ~ m1_subset_1(F_64,k1_zfmisc_1(k2_zfmisc_1(C_63,D_67)))
      | ~ v1_funct_1(F_64)
      | ~ m1_subset_1(E_65,k1_zfmisc_1(k2_zfmisc_1(A_68,B_66)))
      | ~ v1_funct_1(E_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_185,plain,(
    ! [A_68,B_66,E_65] :
      ( k1_partfun1(A_68,B_66,'#skF_1','#skF_1',E_65,'#skF_3') = k5_relat_1(E_65,'#skF_3')
      | ~ v1_funct_1('#skF_3')
      | ~ m1_subset_1(E_65,k1_zfmisc_1(k2_zfmisc_1(A_68,B_66)))
      | ~ v1_funct_1(E_65) ) ),
    inference(resolution,[status(thm)],[c_30,c_181])).

tff(c_205,plain,(
    ! [A_72,B_73,E_74] :
      ( k1_partfun1(A_72,B_73,'#skF_1','#skF_1',E_74,'#skF_3') = k5_relat_1(E_74,'#skF_3')
      | ~ m1_subset_1(E_74,k1_zfmisc_1(k2_zfmisc_1(A_72,B_73)))
      | ~ v1_funct_1(E_74) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_185])).

tff(c_208,plain,
    ( k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2','#skF_3') = k5_relat_1('#skF_2','#skF_3')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_36,c_205])).

tff(c_214,plain,(
    k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2','#skF_3') = k5_relat_1('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_208])).

tff(c_28,plain,(
    r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2','#skF_3'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_129,plain,(
    ! [D_48,C_49,A_50,B_51] :
      ( D_48 = C_49
      | ~ r2_relset_1(A_50,B_51,C_49,D_48)
      | ~ m1_subset_1(D_48,k1_zfmisc_1(k2_zfmisc_1(A_50,B_51)))
      | ~ m1_subset_1(C_49,k1_zfmisc_1(k2_zfmisc_1(A_50,B_51))) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

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

tff(c_219,plain,(
    ~ m1_subset_1(k5_relat_1('#skF_2','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_214,c_156])).

tff(c_235,plain,(
    ! [B_77,A_76,C_75,E_80,F_78,D_79] :
      ( m1_subset_1(k1_partfun1(A_76,B_77,C_75,D_79,E_80,F_78),k1_zfmisc_1(k2_zfmisc_1(A_76,D_79)))
      | ~ m1_subset_1(F_78,k1_zfmisc_1(k2_zfmisc_1(C_75,D_79)))
      | ~ v1_funct_1(F_78)
      | ~ m1_subset_1(E_80,k1_zfmisc_1(k2_zfmisc_1(A_76,B_77)))
      | ~ v1_funct_1(E_80) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_269,plain,
    ( m1_subset_1(k5_relat_1('#skF_2','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ v1_funct_1('#skF_3')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ v1_funct_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_214,c_235])).

tff(c_283,plain,(
    m1_subset_1(k5_relat_1('#skF_2','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_36,c_34,c_30,c_269])).

tff(c_285,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_219,c_283])).

tff(c_286,plain,(
    k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2','#skF_3') = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_146])).

tff(c_332,plain,(
    ! [A_98,E_95,B_96,F_94,D_97,C_93] :
      ( k1_partfun1(A_98,B_96,C_93,D_97,E_95,F_94) = k5_relat_1(E_95,F_94)
      | ~ m1_subset_1(F_94,k1_zfmisc_1(k2_zfmisc_1(C_93,D_97)))
      | ~ v1_funct_1(F_94)
      | ~ m1_subset_1(E_95,k1_zfmisc_1(k2_zfmisc_1(A_98,B_96)))
      | ~ v1_funct_1(E_95) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_336,plain,(
    ! [A_98,B_96,E_95] :
      ( k1_partfun1(A_98,B_96,'#skF_1','#skF_1',E_95,'#skF_3') = k5_relat_1(E_95,'#skF_3')
      | ~ v1_funct_1('#skF_3')
      | ~ m1_subset_1(E_95,k1_zfmisc_1(k2_zfmisc_1(A_98,B_96)))
      | ~ v1_funct_1(E_95) ) ),
    inference(resolution,[status(thm)],[c_30,c_332])).

tff(c_518,plain,(
    ! [A_108,B_109,E_110] :
      ( k1_partfun1(A_108,B_109,'#skF_1','#skF_1',E_110,'#skF_3') = k5_relat_1(E_110,'#skF_3')
      | ~ m1_subset_1(E_110,k1_zfmisc_1(k2_zfmisc_1(A_108,B_109)))
      | ~ v1_funct_1(E_110) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_336])).

tff(c_530,plain,
    ( k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2','#skF_3') = k5_relat_1('#skF_2','#skF_3')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_36,c_518])).

tff(c_543,plain,(
    k5_relat_1('#skF_2','#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_286,c_530])).

tff(c_20,plain,(
    ! [A_29] : k6_relat_1(A_29) = k6_partfun1(A_29) ),
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

tff(c_549,plain,
    ( k6_partfun1(k1_relat_1('#skF_3')) = '#skF_3'
    | k2_relat_1('#skF_2') != k1_relat_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3')
    | ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_543,c_41])).

tff(c_554,plain,(
    k6_partfun1('#skF_1') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_40,c_63,c_34,c_79,c_118,c_118,c_549])).

tff(c_24,plain,(
    ~ r2_relset_1('#skF_1','#skF_1','#skF_3',k6_partfun1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_556,plain,(
    ~ r2_relset_1('#skF_1','#skF_1','#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_554,c_24])).

tff(c_559,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_556])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n022.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 13:36:26 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.66/1.35  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.66/1.35  
% 2.66/1.35  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.66/1.36  %$ r2_relset_1 > v1_funct_2 > m1_subset_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 2.66/1.36  
% 2.66/1.36  %Foreground sorts:
% 2.66/1.36  
% 2.66/1.36  
% 2.66/1.36  %Background operators:
% 2.66/1.36  
% 2.66/1.36  
% 2.66/1.36  %Foreground operators:
% 2.66/1.36  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 2.66/1.36  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.66/1.36  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.66/1.36  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 2.66/1.36  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.66/1.36  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.66/1.36  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.66/1.36  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.66/1.36  tff('#skF_2', type, '#skF_2': $i).
% 2.66/1.36  tff('#skF_3', type, '#skF_3': $i).
% 2.66/1.36  tff('#skF_1', type, '#skF_1': $i).
% 2.66/1.36  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.66/1.36  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.66/1.36  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 2.66/1.36  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.66/1.36  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.66/1.36  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.66/1.36  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 2.66/1.36  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.66/1.36  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.66/1.36  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.66/1.36  
% 2.66/1.37  tff(f_112, negated_conjecture, ~(![A, B]: (((v1_funct_1(B) & v1_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, A, A)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => ((r2_relset_1(A, A, k1_partfun1(A, A, A, A, B, C), B) & (k2_relset_1(A, A, B) = A)) => r2_relset_1(A, A, C, k6_partfun1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t75_funct_2)).
% 2.66/1.37  tff(f_60, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 2.66/1.37  tff(f_44, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.66/1.37  tff(f_52, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 2.66/1.37  tff(f_48, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.66/1.37  tff(f_92, axiom, (![A, B]: (((v1_funct_1(B) & v1_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (k1_relset_1(A, A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t67_funct_2)).
% 2.66/1.37  tff(f_82, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 2.66/1.37  tff(f_72, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (v1_funct_1(k1_partfun1(A, B, C, D, E, F)) & m1_subset_1(k1_partfun1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 2.66/1.37  tff(f_84, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 2.66/1.37  tff(f_40, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (((k2_relat_1(A) = k1_relat_1(B)) & (k5_relat_1(A, B) = A)) => (B = k6_relat_1(k1_relat_1(B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_funct_1)).
% 2.66/1.37  tff(c_30, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_112])).
% 2.66/1.37  tff(c_64, plain, (![A_37, B_38, D_39]: (r2_relset_1(A_37, B_38, D_39, D_39) | ~m1_subset_1(D_39, k1_zfmisc_1(k2_zfmisc_1(A_37, B_38))))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.66/1.37  tff(c_70, plain, (r2_relset_1('#skF_1', '#skF_1', '#skF_3', '#skF_3')), inference(resolution, [status(thm)], [c_30, c_64])).
% 2.66/1.37  tff(c_36, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_112])).
% 2.66/1.37  tff(c_55, plain, (![C_34, A_35, B_36]: (v1_relat_1(C_34) | ~m1_subset_1(C_34, k1_zfmisc_1(k2_zfmisc_1(A_35, B_36))))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.66/1.37  tff(c_62, plain, (v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_36, c_55])).
% 2.66/1.37  tff(c_40, plain, (v1_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_112])).
% 2.66/1.37  tff(c_63, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_30, c_55])).
% 2.66/1.37  tff(c_34, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_112])).
% 2.66/1.37  tff(c_26, plain, (k2_relset_1('#skF_1', '#skF_1', '#skF_2')='#skF_1'), inference(cnfTransformation, [status(thm)], [f_112])).
% 2.66/1.37  tff(c_71, plain, (![A_40, B_41, C_42]: (k2_relset_1(A_40, B_41, C_42)=k2_relat_1(C_42) | ~m1_subset_1(C_42, k1_zfmisc_1(k2_zfmisc_1(A_40, B_41))))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.66/1.37  tff(c_74, plain, (k2_relset_1('#skF_1', '#skF_1', '#skF_2')=k2_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_36, c_71])).
% 2.66/1.37  tff(c_79, plain, (k2_relat_1('#skF_2')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_26, c_74])).
% 2.66/1.37  tff(c_32, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_112])).
% 2.66/1.37  tff(c_89, plain, (![A_43, B_44, C_45]: (k1_relset_1(A_43, B_44, C_45)=k1_relat_1(C_45) | ~m1_subset_1(C_45, k1_zfmisc_1(k2_zfmisc_1(A_43, B_44))))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.66/1.37  tff(c_97, plain, (k1_relset_1('#skF_1', '#skF_1', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_30, c_89])).
% 2.66/1.37  tff(c_106, plain, (![A_46, B_47]: (k1_relset_1(A_46, A_46, B_47)=A_46 | ~m1_subset_1(B_47, k1_zfmisc_1(k2_zfmisc_1(A_46, A_46))) | ~v1_funct_2(B_47, A_46, A_46) | ~v1_funct_1(B_47))), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.66/1.37  tff(c_112, plain, (k1_relset_1('#skF_1', '#skF_1', '#skF_3')='#skF_1' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_30, c_106])).
% 2.66/1.37  tff(c_118, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_97, c_112])).
% 2.66/1.37  tff(c_181, plain, (![B_66, F_64, D_67, E_65, C_63, A_68]: (k1_partfun1(A_68, B_66, C_63, D_67, E_65, F_64)=k5_relat_1(E_65, F_64) | ~m1_subset_1(F_64, k1_zfmisc_1(k2_zfmisc_1(C_63, D_67))) | ~v1_funct_1(F_64) | ~m1_subset_1(E_65, k1_zfmisc_1(k2_zfmisc_1(A_68, B_66))) | ~v1_funct_1(E_65))), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.66/1.37  tff(c_185, plain, (![A_68, B_66, E_65]: (k1_partfun1(A_68, B_66, '#skF_1', '#skF_1', E_65, '#skF_3')=k5_relat_1(E_65, '#skF_3') | ~v1_funct_1('#skF_3') | ~m1_subset_1(E_65, k1_zfmisc_1(k2_zfmisc_1(A_68, B_66))) | ~v1_funct_1(E_65))), inference(resolution, [status(thm)], [c_30, c_181])).
% 2.66/1.37  tff(c_205, plain, (![A_72, B_73, E_74]: (k1_partfun1(A_72, B_73, '#skF_1', '#skF_1', E_74, '#skF_3')=k5_relat_1(E_74, '#skF_3') | ~m1_subset_1(E_74, k1_zfmisc_1(k2_zfmisc_1(A_72, B_73))) | ~v1_funct_1(E_74))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_185])).
% 2.66/1.37  tff(c_208, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', '#skF_3')=k5_relat_1('#skF_2', '#skF_3') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_36, c_205])).
% 2.66/1.37  tff(c_214, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', '#skF_3')=k5_relat_1('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_208])).
% 2.66/1.37  tff(c_28, plain, (r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', '#skF_3'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_112])).
% 2.66/1.37  tff(c_129, plain, (![D_48, C_49, A_50, B_51]: (D_48=C_49 | ~r2_relset_1(A_50, B_51, C_49, D_48) | ~m1_subset_1(D_48, k1_zfmisc_1(k2_zfmisc_1(A_50, B_51))) | ~m1_subset_1(C_49, k1_zfmisc_1(k2_zfmisc_1(A_50, B_51))))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.66/1.37  tff(c_135, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', '#skF_3')='#skF_2' | ~m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_28, c_129])).
% 2.66/1.37  tff(c_146, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', '#skF_3')='#skF_2' | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_135])).
% 2.66/1.37  tff(c_156, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_146])).
% 2.66/1.37  tff(c_219, plain, (~m1_subset_1(k5_relat_1('#skF_2', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_214, c_156])).
% 2.66/1.37  tff(c_235, plain, (![B_77, A_76, C_75, E_80, F_78, D_79]: (m1_subset_1(k1_partfun1(A_76, B_77, C_75, D_79, E_80, F_78), k1_zfmisc_1(k2_zfmisc_1(A_76, D_79))) | ~m1_subset_1(F_78, k1_zfmisc_1(k2_zfmisc_1(C_75, D_79))) | ~v1_funct_1(F_78) | ~m1_subset_1(E_80, k1_zfmisc_1(k2_zfmisc_1(A_76, B_77))) | ~v1_funct_1(E_80))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.66/1.37  tff(c_269, plain, (m1_subset_1(k5_relat_1('#skF_2', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v1_funct_1('#skF_3') | ~m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v1_funct_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_214, c_235])).
% 2.66/1.37  tff(c_283, plain, (m1_subset_1(k5_relat_1('#skF_2', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_36, c_34, c_30, c_269])).
% 2.66/1.37  tff(c_285, plain, $false, inference(negUnitSimplification, [status(thm)], [c_219, c_283])).
% 2.66/1.37  tff(c_286, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', '#skF_3')='#skF_2'), inference(splitRight, [status(thm)], [c_146])).
% 2.66/1.37  tff(c_332, plain, (![A_98, E_95, B_96, F_94, D_97, C_93]: (k1_partfun1(A_98, B_96, C_93, D_97, E_95, F_94)=k5_relat_1(E_95, F_94) | ~m1_subset_1(F_94, k1_zfmisc_1(k2_zfmisc_1(C_93, D_97))) | ~v1_funct_1(F_94) | ~m1_subset_1(E_95, k1_zfmisc_1(k2_zfmisc_1(A_98, B_96))) | ~v1_funct_1(E_95))), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.66/1.37  tff(c_336, plain, (![A_98, B_96, E_95]: (k1_partfun1(A_98, B_96, '#skF_1', '#skF_1', E_95, '#skF_3')=k5_relat_1(E_95, '#skF_3') | ~v1_funct_1('#skF_3') | ~m1_subset_1(E_95, k1_zfmisc_1(k2_zfmisc_1(A_98, B_96))) | ~v1_funct_1(E_95))), inference(resolution, [status(thm)], [c_30, c_332])).
% 2.66/1.37  tff(c_518, plain, (![A_108, B_109, E_110]: (k1_partfun1(A_108, B_109, '#skF_1', '#skF_1', E_110, '#skF_3')=k5_relat_1(E_110, '#skF_3') | ~m1_subset_1(E_110, k1_zfmisc_1(k2_zfmisc_1(A_108, B_109))) | ~v1_funct_1(E_110))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_336])).
% 2.66/1.37  tff(c_530, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', '#skF_3')=k5_relat_1('#skF_2', '#skF_3') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_36, c_518])).
% 2.66/1.37  tff(c_543, plain, (k5_relat_1('#skF_2', '#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_40, c_286, c_530])).
% 2.66/1.37  tff(c_20, plain, (![A_29]: (k6_relat_1(A_29)=k6_partfun1(A_29))), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.66/1.37  tff(c_2, plain, (![B_3, A_1]: (k6_relat_1(k1_relat_1(B_3))=B_3 | k5_relat_1(A_1, B_3)!=A_1 | k2_relat_1(A_1)!=k1_relat_1(B_3) | ~v1_funct_1(B_3) | ~v1_relat_1(B_3) | ~v1_funct_1(A_1) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.66/1.37  tff(c_41, plain, (![B_3, A_1]: (k6_partfun1(k1_relat_1(B_3))=B_3 | k5_relat_1(A_1, B_3)!=A_1 | k2_relat_1(A_1)!=k1_relat_1(B_3) | ~v1_funct_1(B_3) | ~v1_relat_1(B_3) | ~v1_funct_1(A_1) | ~v1_relat_1(A_1))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_2])).
% 2.66/1.37  tff(c_549, plain, (k6_partfun1(k1_relat_1('#skF_3'))='#skF_3' | k2_relat_1('#skF_2')!=k1_relat_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3') | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_543, c_41])).
% 2.66/1.37  tff(c_554, plain, (k6_partfun1('#skF_1')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_62, c_40, c_63, c_34, c_79, c_118, c_118, c_549])).
% 2.66/1.37  tff(c_24, plain, (~r2_relset_1('#skF_1', '#skF_1', '#skF_3', k6_partfun1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_112])).
% 2.66/1.37  tff(c_556, plain, (~r2_relset_1('#skF_1', '#skF_1', '#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_554, c_24])).
% 2.66/1.37  tff(c_559, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_70, c_556])).
% 2.66/1.37  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.66/1.37  
% 2.66/1.37  Inference rules
% 2.66/1.37  ----------------------
% 2.66/1.37  #Ref     : 0
% 2.66/1.37  #Sup     : 117
% 2.66/1.37  #Fact    : 0
% 2.66/1.37  #Define  : 0
% 2.66/1.37  #Split   : 1
% 2.66/1.37  #Chain   : 0
% 2.66/1.37  #Close   : 0
% 2.66/1.37  
% 2.66/1.37  Ordering : KBO
% 2.66/1.37  
% 2.66/1.37  Simplification rules
% 2.66/1.37  ----------------------
% 2.66/1.37  #Subsume      : 0
% 2.66/1.37  #Demod        : 93
% 2.66/1.37  #Tautology    : 38
% 2.66/1.37  #SimpNegUnit  : 1
% 2.66/1.37  #BackRed      : 10
% 2.66/1.37  
% 2.66/1.37  #Partial instantiations: 0
% 2.66/1.37  #Strategies tried      : 1
% 2.66/1.37  
% 2.66/1.37  Timing (in seconds)
% 2.66/1.37  ----------------------
% 2.66/1.38  Preprocessing        : 0.31
% 2.66/1.38  Parsing              : 0.17
% 2.66/1.38  CNF conversion       : 0.02
% 2.66/1.38  Main loop            : 0.29
% 2.66/1.38  Inferencing          : 0.11
% 2.66/1.38  Reduction            : 0.09
% 2.66/1.38  Demodulation         : 0.07
% 2.66/1.38  BG Simplification    : 0.02
% 2.66/1.38  Subsumption          : 0.05
% 2.66/1.38  Abstraction          : 0.02
% 2.66/1.38  MUC search           : 0.00
% 2.66/1.38  Cooper               : 0.00
% 2.66/1.38  Total                : 0.64
% 2.66/1.38  Index Insertion      : 0.00
% 2.66/1.38  Index Deletion       : 0.00
% 2.66/1.38  Index Matching       : 0.00
% 2.66/1.38  BG Taut test         : 0.00
%------------------------------------------------------------------------------
