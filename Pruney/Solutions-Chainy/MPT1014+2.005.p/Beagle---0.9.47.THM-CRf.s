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

% Result     : Theorem 2.76s
% Output     : CNFRefutation 3.18s
% Verified   : 
% Statistics : Number of formulae       :   88 ( 247 expanded)
%              Number of leaves         :   32 ( 102 expanded)
%              Depth                    :    9
%              Number of atoms          :  169 ( 874 expanded)
%              Number of equality atoms :   58 ( 224 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > m1_subset_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

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

tff(f_122,negated_conjecture,(
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

tff(f_78,axiom,(
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

tff(f_100,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_90,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( v1_funct_1(k1_partfun1(A,B,C,D,E,F))
        & m1_subset_1(k1_partfun1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).

tff(f_102,axiom,(
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

tff(c_40,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_74,plain,(
    ! [A_38,B_39,D_40] :
      ( r2_relset_1(A_38,B_39,D_40,D_40)
      | ~ m1_subset_1(D_40,k1_zfmisc_1(k2_zfmisc_1(A_38,B_39))) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_80,plain,(
    r2_relset_1('#skF_1','#skF_1','#skF_3','#skF_3') ),
    inference(resolution,[status(thm)],[c_40,c_74])).

tff(c_46,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_65,plain,(
    ! [C_35,A_36,B_37] :
      ( v1_relat_1(C_35)
      | ~ m1_subset_1(C_35,k1_zfmisc_1(k2_zfmisc_1(A_36,B_37))) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_72,plain,(
    v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_46,c_65])).

tff(c_50,plain,(
    v1_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_73,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_40,c_65])).

tff(c_44,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_36,plain,(
    k2_relset_1('#skF_1','#skF_1','#skF_2') = '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_82,plain,(
    ! [A_42,B_43,C_44] :
      ( k2_relset_1(A_42,B_43,C_44) = k2_relat_1(C_44)
      | ~ m1_subset_1(C_44,k1_zfmisc_1(k2_zfmisc_1(A_42,B_43))) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_85,plain,(
    k2_relset_1('#skF_1','#skF_1','#skF_2') = k2_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_46,c_82])).

tff(c_90,plain,(
    k2_relat_1('#skF_2') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_85])).

tff(c_42,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_100,plain,(
    ! [A_45,B_46,C_47] :
      ( k1_relset_1(A_45,B_46,C_47) = k1_relat_1(C_47)
      | ~ m1_subset_1(C_47,k1_zfmisc_1(k2_zfmisc_1(A_45,B_46))) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_108,plain,(
    k1_relset_1('#skF_1','#skF_1','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_40,c_100])).

tff(c_120,plain,(
    ! [B_54,A_55,C_56] :
      ( k1_xboole_0 = B_54
      | k1_relset_1(A_55,B_54,C_56) = A_55
      | ~ v1_funct_2(C_56,A_55,B_54)
      | ~ m1_subset_1(C_56,k1_zfmisc_1(k2_zfmisc_1(A_55,B_54))) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_126,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_relset_1('#skF_1','#skF_1','#skF_3') = '#skF_1'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_1') ),
    inference(resolution,[status(thm)],[c_40,c_120])).

tff(c_132,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_108,c_126])).

tff(c_139,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_132])).

tff(c_223,plain,(
    ! [E_83,D_78,B_79,F_81,A_80,C_82] :
      ( k1_partfun1(A_80,B_79,C_82,D_78,E_83,F_81) = k5_relat_1(E_83,F_81)
      | ~ m1_subset_1(F_81,k1_zfmisc_1(k2_zfmisc_1(C_82,D_78)))
      | ~ v1_funct_1(F_81)
      | ~ m1_subset_1(E_83,k1_zfmisc_1(k2_zfmisc_1(A_80,B_79)))
      | ~ v1_funct_1(E_83) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_227,plain,(
    ! [A_80,B_79,E_83] :
      ( k1_partfun1(A_80,B_79,'#skF_1','#skF_1',E_83,'#skF_3') = k5_relat_1(E_83,'#skF_3')
      | ~ v1_funct_1('#skF_3')
      | ~ m1_subset_1(E_83,k1_zfmisc_1(k2_zfmisc_1(A_80,B_79)))
      | ~ v1_funct_1(E_83) ) ),
    inference(resolution,[status(thm)],[c_40,c_223])).

tff(c_257,plain,(
    ! [A_87,B_88,E_89] :
      ( k1_partfun1(A_87,B_88,'#skF_1','#skF_1',E_89,'#skF_3') = k5_relat_1(E_89,'#skF_3')
      | ~ m1_subset_1(E_89,k1_zfmisc_1(k2_zfmisc_1(A_87,B_88)))
      | ~ v1_funct_1(E_89) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_227])).

tff(c_260,plain,
    ( k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2','#skF_3') = k5_relat_1('#skF_2','#skF_3')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_46,c_257])).

tff(c_266,plain,(
    k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2','#skF_3') = k5_relat_1('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_260])).

tff(c_38,plain,(
    r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2','#skF_3'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_166,plain,(
    ! [D_60,C_61,A_62,B_63] :
      ( D_60 = C_61
      | ~ r2_relset_1(A_62,B_63,C_61,D_60)
      | ~ m1_subset_1(D_60,k1_zfmisc_1(k2_zfmisc_1(A_62,B_63)))
      | ~ m1_subset_1(C_61,k1_zfmisc_1(k2_zfmisc_1(A_62,B_63))) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_172,plain,
    ( k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2','#skF_3') = '#skF_2'
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_38,c_166])).

tff(c_183,plain,
    ( k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2','#skF_3') = '#skF_2'
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_172])).

tff(c_185,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_183])).

tff(c_271,plain,(
    ~ m1_subset_1(k5_relat_1('#skF_2','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_266,c_185])).

tff(c_282,plain,(
    ! [D_92,F_95,C_90,B_91,A_94,E_93] :
      ( m1_subset_1(k1_partfun1(A_94,B_91,C_90,D_92,E_93,F_95),k1_zfmisc_1(k2_zfmisc_1(A_94,D_92)))
      | ~ m1_subset_1(F_95,k1_zfmisc_1(k2_zfmisc_1(C_90,D_92)))
      | ~ v1_funct_1(F_95)
      | ~ m1_subset_1(E_93,k1_zfmisc_1(k2_zfmisc_1(A_94,B_91)))
      | ~ v1_funct_1(E_93) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_330,plain,
    ( m1_subset_1(k5_relat_1('#skF_2','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ v1_funct_1('#skF_3')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ v1_funct_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_266,c_282])).

tff(c_353,plain,(
    m1_subset_1(k5_relat_1('#skF_2','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_46,c_44,c_40,c_330])).

tff(c_358,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_271,c_353])).

tff(c_359,plain,(
    k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2','#skF_3') = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_183])).

tff(c_405,plain,(
    ! [A_110,D_108,B_109,C_112,E_113,F_111] :
      ( k1_partfun1(A_110,B_109,C_112,D_108,E_113,F_111) = k5_relat_1(E_113,F_111)
      | ~ m1_subset_1(F_111,k1_zfmisc_1(k2_zfmisc_1(C_112,D_108)))
      | ~ v1_funct_1(F_111)
      | ~ m1_subset_1(E_113,k1_zfmisc_1(k2_zfmisc_1(A_110,B_109)))
      | ~ v1_funct_1(E_113) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_409,plain,(
    ! [A_110,B_109,E_113] :
      ( k1_partfun1(A_110,B_109,'#skF_1','#skF_1',E_113,'#skF_3') = k5_relat_1(E_113,'#skF_3')
      | ~ v1_funct_1('#skF_3')
      | ~ m1_subset_1(E_113,k1_zfmisc_1(k2_zfmisc_1(A_110,B_109)))
      | ~ v1_funct_1(E_113) ) ),
    inference(resolution,[status(thm)],[c_40,c_405])).

tff(c_416,plain,(
    ! [A_114,B_115,E_116] :
      ( k1_partfun1(A_114,B_115,'#skF_1','#skF_1',E_116,'#skF_3') = k5_relat_1(E_116,'#skF_3')
      | ~ m1_subset_1(E_116,k1_zfmisc_1(k2_zfmisc_1(A_114,B_115)))
      | ~ v1_funct_1(E_116) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_409])).

tff(c_419,plain,
    ( k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2','#skF_3') = k5_relat_1('#skF_2','#skF_3')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_46,c_416])).

tff(c_425,plain,(
    k5_relat_1('#skF_2','#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_359,c_419])).

tff(c_32,plain,(
    ! [A_32] : k6_relat_1(A_32) = k6_partfun1(A_32) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

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

tff(c_51,plain,(
    ! [B_3,A_1] :
      ( k6_partfun1(k1_relat_1(B_3)) = B_3
      | k5_relat_1(A_1,B_3) != A_1
      | k2_relat_1(A_1) != k1_relat_1(B_3)
      | ~ v1_funct_1(B_3)
      | ~ v1_relat_1(B_3)
      | ~ v1_funct_1(A_1)
      | ~ v1_relat_1(A_1) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_2])).

tff(c_431,plain,
    ( k6_partfun1(k1_relat_1('#skF_3')) = '#skF_3'
    | k2_relat_1('#skF_2') != k1_relat_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3')
    | ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_425,c_51])).

tff(c_436,plain,(
    k6_partfun1('#skF_1') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_50,c_73,c_44,c_90,c_139,c_139,c_431])).

tff(c_34,plain,(
    ~ r2_relset_1('#skF_1','#skF_1','#skF_3',k6_partfun1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_443,plain,(
    ~ r2_relset_1('#skF_1','#skF_1','#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_436,c_34])).

tff(c_446,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_443])).

tff(c_448,plain,(
    k1_relat_1('#skF_3') != '#skF_1' ),
    inference(splitRight,[status(thm)],[c_132])).

tff(c_447,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_132])).

tff(c_22,plain,(
    ! [B_18,C_19] :
      ( k1_relset_1(k1_xboole_0,B_18,C_19) = k1_xboole_0
      | ~ v1_funct_2(C_19,k1_xboole_0,B_18)
      | ~ m1_subset_1(C_19,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_18))) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_492,plain,(
    ! [B_123,C_124] :
      ( k1_relset_1('#skF_1',B_123,C_124) = '#skF_1'
      | ~ v1_funct_2(C_124,'#skF_1',B_123)
      | ~ m1_subset_1(C_124,k1_zfmisc_1(k2_zfmisc_1('#skF_1',B_123))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_447,c_447,c_447,c_447,c_22])).

tff(c_498,plain,
    ( k1_relset_1('#skF_1','#skF_1','#skF_3') = '#skF_1'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_1') ),
    inference(resolution,[status(thm)],[c_40,c_492])).

tff(c_504,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_108,c_498])).

tff(c_506,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_448,c_504])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n020.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 16:40:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.76/1.43  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.76/1.44  
% 2.76/1.44  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.76/1.45  %$ r2_relset_1 > v1_funct_2 > m1_subset_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.76/1.45  
% 2.76/1.45  %Foreground sorts:
% 2.76/1.45  
% 2.76/1.45  
% 2.76/1.45  %Background operators:
% 2.76/1.45  
% 2.76/1.45  
% 2.76/1.45  %Foreground operators:
% 2.76/1.45  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 2.76/1.45  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.76/1.45  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.76/1.45  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 2.76/1.45  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.76/1.45  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.76/1.45  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.76/1.45  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.76/1.45  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.76/1.45  tff('#skF_2', type, '#skF_2': $i).
% 2.76/1.45  tff('#skF_3', type, '#skF_3': $i).
% 2.76/1.45  tff('#skF_1', type, '#skF_1': $i).
% 2.76/1.45  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.76/1.45  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.76/1.45  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 2.76/1.45  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.76/1.45  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.76/1.45  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.76/1.45  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 2.76/1.45  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.76/1.45  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.76/1.45  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.76/1.45  
% 3.18/1.47  tff(f_122, negated_conjecture, ~(![A, B]: (((v1_funct_1(B) & v1_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, A, A)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => ((r2_relset_1(A, A, k1_partfun1(A, A, A, A, B, C), B) & (k2_relset_1(A, A, B) = A)) => r2_relset_1(A, A, C, k6_partfun1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t75_funct_2)).
% 3.18/1.47  tff(f_60, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 3.18/1.47  tff(f_44, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.18/1.47  tff(f_52, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 3.18/1.47  tff(f_48, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.18/1.47  tff(f_78, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 3.18/1.47  tff(f_100, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 3.18/1.47  tff(f_90, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (v1_funct_1(k1_partfun1(A, B, C, D, E, F)) & m1_subset_1(k1_partfun1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 3.18/1.47  tff(f_102, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 3.18/1.47  tff(f_40, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (((k2_relat_1(A) = k1_relat_1(B)) & (k5_relat_1(A, B) = A)) => (B = k6_relat_1(k1_relat_1(B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_funct_1)).
% 3.18/1.47  tff(c_40, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_122])).
% 3.18/1.47  tff(c_74, plain, (![A_38, B_39, D_40]: (r2_relset_1(A_38, B_39, D_40, D_40) | ~m1_subset_1(D_40, k1_zfmisc_1(k2_zfmisc_1(A_38, B_39))))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.18/1.47  tff(c_80, plain, (r2_relset_1('#skF_1', '#skF_1', '#skF_3', '#skF_3')), inference(resolution, [status(thm)], [c_40, c_74])).
% 3.18/1.47  tff(c_46, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_122])).
% 3.18/1.47  tff(c_65, plain, (![C_35, A_36, B_37]: (v1_relat_1(C_35) | ~m1_subset_1(C_35, k1_zfmisc_1(k2_zfmisc_1(A_36, B_37))))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.18/1.47  tff(c_72, plain, (v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_46, c_65])).
% 3.18/1.47  tff(c_50, plain, (v1_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_122])).
% 3.18/1.47  tff(c_73, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_40, c_65])).
% 3.18/1.47  tff(c_44, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_122])).
% 3.18/1.47  tff(c_36, plain, (k2_relset_1('#skF_1', '#skF_1', '#skF_2')='#skF_1'), inference(cnfTransformation, [status(thm)], [f_122])).
% 3.18/1.47  tff(c_82, plain, (![A_42, B_43, C_44]: (k2_relset_1(A_42, B_43, C_44)=k2_relat_1(C_44) | ~m1_subset_1(C_44, k1_zfmisc_1(k2_zfmisc_1(A_42, B_43))))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.18/1.47  tff(c_85, plain, (k2_relset_1('#skF_1', '#skF_1', '#skF_2')=k2_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_46, c_82])).
% 3.18/1.47  tff(c_90, plain, (k2_relat_1('#skF_2')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_36, c_85])).
% 3.18/1.47  tff(c_42, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_122])).
% 3.18/1.47  tff(c_100, plain, (![A_45, B_46, C_47]: (k1_relset_1(A_45, B_46, C_47)=k1_relat_1(C_47) | ~m1_subset_1(C_47, k1_zfmisc_1(k2_zfmisc_1(A_45, B_46))))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.18/1.47  tff(c_108, plain, (k1_relset_1('#skF_1', '#skF_1', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_40, c_100])).
% 3.18/1.47  tff(c_120, plain, (![B_54, A_55, C_56]: (k1_xboole_0=B_54 | k1_relset_1(A_55, B_54, C_56)=A_55 | ~v1_funct_2(C_56, A_55, B_54) | ~m1_subset_1(C_56, k1_zfmisc_1(k2_zfmisc_1(A_55, B_54))))), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.18/1.47  tff(c_126, plain, (k1_xboole_0='#skF_1' | k1_relset_1('#skF_1', '#skF_1', '#skF_3')='#skF_1' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_1')), inference(resolution, [status(thm)], [c_40, c_120])).
% 3.18/1.47  tff(c_132, plain, (k1_xboole_0='#skF_1' | k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_42, c_108, c_126])).
% 3.18/1.47  tff(c_139, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(splitLeft, [status(thm)], [c_132])).
% 3.18/1.47  tff(c_223, plain, (![E_83, D_78, B_79, F_81, A_80, C_82]: (k1_partfun1(A_80, B_79, C_82, D_78, E_83, F_81)=k5_relat_1(E_83, F_81) | ~m1_subset_1(F_81, k1_zfmisc_1(k2_zfmisc_1(C_82, D_78))) | ~v1_funct_1(F_81) | ~m1_subset_1(E_83, k1_zfmisc_1(k2_zfmisc_1(A_80, B_79))) | ~v1_funct_1(E_83))), inference(cnfTransformation, [status(thm)], [f_100])).
% 3.18/1.47  tff(c_227, plain, (![A_80, B_79, E_83]: (k1_partfun1(A_80, B_79, '#skF_1', '#skF_1', E_83, '#skF_3')=k5_relat_1(E_83, '#skF_3') | ~v1_funct_1('#skF_3') | ~m1_subset_1(E_83, k1_zfmisc_1(k2_zfmisc_1(A_80, B_79))) | ~v1_funct_1(E_83))), inference(resolution, [status(thm)], [c_40, c_223])).
% 3.18/1.47  tff(c_257, plain, (![A_87, B_88, E_89]: (k1_partfun1(A_87, B_88, '#skF_1', '#skF_1', E_89, '#skF_3')=k5_relat_1(E_89, '#skF_3') | ~m1_subset_1(E_89, k1_zfmisc_1(k2_zfmisc_1(A_87, B_88))) | ~v1_funct_1(E_89))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_227])).
% 3.18/1.47  tff(c_260, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', '#skF_3')=k5_relat_1('#skF_2', '#skF_3') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_46, c_257])).
% 3.18/1.47  tff(c_266, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', '#skF_3')=k5_relat_1('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_260])).
% 3.18/1.47  tff(c_38, plain, (r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', '#skF_3'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_122])).
% 3.18/1.47  tff(c_166, plain, (![D_60, C_61, A_62, B_63]: (D_60=C_61 | ~r2_relset_1(A_62, B_63, C_61, D_60) | ~m1_subset_1(D_60, k1_zfmisc_1(k2_zfmisc_1(A_62, B_63))) | ~m1_subset_1(C_61, k1_zfmisc_1(k2_zfmisc_1(A_62, B_63))))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.18/1.47  tff(c_172, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', '#skF_3')='#skF_2' | ~m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_38, c_166])).
% 3.18/1.47  tff(c_183, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', '#skF_3')='#skF_2' | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_172])).
% 3.18/1.47  tff(c_185, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_183])).
% 3.18/1.47  tff(c_271, plain, (~m1_subset_1(k5_relat_1('#skF_2', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_266, c_185])).
% 3.18/1.47  tff(c_282, plain, (![D_92, F_95, C_90, B_91, A_94, E_93]: (m1_subset_1(k1_partfun1(A_94, B_91, C_90, D_92, E_93, F_95), k1_zfmisc_1(k2_zfmisc_1(A_94, D_92))) | ~m1_subset_1(F_95, k1_zfmisc_1(k2_zfmisc_1(C_90, D_92))) | ~v1_funct_1(F_95) | ~m1_subset_1(E_93, k1_zfmisc_1(k2_zfmisc_1(A_94, B_91))) | ~v1_funct_1(E_93))), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.18/1.47  tff(c_330, plain, (m1_subset_1(k5_relat_1('#skF_2', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v1_funct_1('#skF_3') | ~m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v1_funct_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_266, c_282])).
% 3.18/1.47  tff(c_353, plain, (m1_subset_1(k5_relat_1('#skF_2', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_46, c_44, c_40, c_330])).
% 3.18/1.47  tff(c_358, plain, $false, inference(negUnitSimplification, [status(thm)], [c_271, c_353])).
% 3.18/1.47  tff(c_359, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', '#skF_3')='#skF_2'), inference(splitRight, [status(thm)], [c_183])).
% 3.18/1.47  tff(c_405, plain, (![A_110, D_108, B_109, C_112, E_113, F_111]: (k1_partfun1(A_110, B_109, C_112, D_108, E_113, F_111)=k5_relat_1(E_113, F_111) | ~m1_subset_1(F_111, k1_zfmisc_1(k2_zfmisc_1(C_112, D_108))) | ~v1_funct_1(F_111) | ~m1_subset_1(E_113, k1_zfmisc_1(k2_zfmisc_1(A_110, B_109))) | ~v1_funct_1(E_113))), inference(cnfTransformation, [status(thm)], [f_100])).
% 3.18/1.47  tff(c_409, plain, (![A_110, B_109, E_113]: (k1_partfun1(A_110, B_109, '#skF_1', '#skF_1', E_113, '#skF_3')=k5_relat_1(E_113, '#skF_3') | ~v1_funct_1('#skF_3') | ~m1_subset_1(E_113, k1_zfmisc_1(k2_zfmisc_1(A_110, B_109))) | ~v1_funct_1(E_113))), inference(resolution, [status(thm)], [c_40, c_405])).
% 3.18/1.47  tff(c_416, plain, (![A_114, B_115, E_116]: (k1_partfun1(A_114, B_115, '#skF_1', '#skF_1', E_116, '#skF_3')=k5_relat_1(E_116, '#skF_3') | ~m1_subset_1(E_116, k1_zfmisc_1(k2_zfmisc_1(A_114, B_115))) | ~v1_funct_1(E_116))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_409])).
% 3.18/1.47  tff(c_419, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', '#skF_3')=k5_relat_1('#skF_2', '#skF_3') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_46, c_416])).
% 3.18/1.47  tff(c_425, plain, (k5_relat_1('#skF_2', '#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_50, c_359, c_419])).
% 3.18/1.47  tff(c_32, plain, (![A_32]: (k6_relat_1(A_32)=k6_partfun1(A_32))), inference(cnfTransformation, [status(thm)], [f_102])).
% 3.18/1.47  tff(c_2, plain, (![B_3, A_1]: (k6_relat_1(k1_relat_1(B_3))=B_3 | k5_relat_1(A_1, B_3)!=A_1 | k2_relat_1(A_1)!=k1_relat_1(B_3) | ~v1_funct_1(B_3) | ~v1_relat_1(B_3) | ~v1_funct_1(A_1) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.18/1.47  tff(c_51, plain, (![B_3, A_1]: (k6_partfun1(k1_relat_1(B_3))=B_3 | k5_relat_1(A_1, B_3)!=A_1 | k2_relat_1(A_1)!=k1_relat_1(B_3) | ~v1_funct_1(B_3) | ~v1_relat_1(B_3) | ~v1_funct_1(A_1) | ~v1_relat_1(A_1))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_2])).
% 3.18/1.47  tff(c_431, plain, (k6_partfun1(k1_relat_1('#skF_3'))='#skF_3' | k2_relat_1('#skF_2')!=k1_relat_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3') | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_425, c_51])).
% 3.18/1.47  tff(c_436, plain, (k6_partfun1('#skF_1')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_72, c_50, c_73, c_44, c_90, c_139, c_139, c_431])).
% 3.18/1.47  tff(c_34, plain, (~r2_relset_1('#skF_1', '#skF_1', '#skF_3', k6_partfun1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_122])).
% 3.18/1.47  tff(c_443, plain, (~r2_relset_1('#skF_1', '#skF_1', '#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_436, c_34])).
% 3.18/1.47  tff(c_446, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_80, c_443])).
% 3.18/1.47  tff(c_448, plain, (k1_relat_1('#skF_3')!='#skF_1'), inference(splitRight, [status(thm)], [c_132])).
% 3.18/1.47  tff(c_447, plain, (k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_132])).
% 3.18/1.47  tff(c_22, plain, (![B_18, C_19]: (k1_relset_1(k1_xboole_0, B_18, C_19)=k1_xboole_0 | ~v1_funct_2(C_19, k1_xboole_0, B_18) | ~m1_subset_1(C_19, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_18))))), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.18/1.47  tff(c_492, plain, (![B_123, C_124]: (k1_relset_1('#skF_1', B_123, C_124)='#skF_1' | ~v1_funct_2(C_124, '#skF_1', B_123) | ~m1_subset_1(C_124, k1_zfmisc_1(k2_zfmisc_1('#skF_1', B_123))))), inference(demodulation, [status(thm), theory('equality')], [c_447, c_447, c_447, c_447, c_22])).
% 3.18/1.47  tff(c_498, plain, (k1_relset_1('#skF_1', '#skF_1', '#skF_3')='#skF_1' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_1')), inference(resolution, [status(thm)], [c_40, c_492])).
% 3.18/1.47  tff(c_504, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_42, c_108, c_498])).
% 3.18/1.47  tff(c_506, plain, $false, inference(negUnitSimplification, [status(thm)], [c_448, c_504])).
% 3.18/1.47  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.18/1.47  
% 3.18/1.47  Inference rules
% 3.18/1.47  ----------------------
% 3.18/1.47  #Ref     : 0
% 3.18/1.47  #Sup     : 99
% 3.18/1.47  #Fact    : 0
% 3.18/1.47  #Define  : 0
% 3.18/1.47  #Split   : 3
% 3.18/1.47  #Chain   : 0
% 3.18/1.47  #Close   : 0
% 3.18/1.47  
% 3.18/1.47  Ordering : KBO
% 3.18/1.47  
% 3.18/1.47  Simplification rules
% 3.18/1.47  ----------------------
% 3.18/1.47  #Subsume      : 1
% 3.18/1.47  #Demod        : 101
% 3.18/1.47  #Tautology    : 47
% 3.18/1.47  #SimpNegUnit  : 2
% 3.18/1.47  #BackRed      : 15
% 3.18/1.47  
% 3.18/1.47  #Partial instantiations: 0
% 3.18/1.47  #Strategies tried      : 1
% 3.18/1.47  
% 3.18/1.47  Timing (in seconds)
% 3.18/1.47  ----------------------
% 3.18/1.47  Preprocessing        : 0.36
% 3.18/1.47  Parsing              : 0.19
% 3.18/1.47  CNF conversion       : 0.02
% 3.18/1.47  Main loop            : 0.34
% 3.18/1.47  Inferencing          : 0.13
% 3.18/1.47  Reduction            : 0.11
% 3.18/1.47  Demodulation         : 0.08
% 3.18/1.47  BG Simplification    : 0.02
% 3.18/1.47  Subsumption          : 0.06
% 3.18/1.47  Abstraction          : 0.02
% 3.18/1.47  MUC search           : 0.00
% 3.18/1.47  Cooper               : 0.00
% 3.18/1.47  Total                : 0.74
% 3.18/1.47  Index Insertion      : 0.00
% 3.18/1.47  Index Deletion       : 0.00
% 3.18/1.47  Index Matching       : 0.00
% 3.18/1.47  BG Taut test         : 0.00
%------------------------------------------------------------------------------
