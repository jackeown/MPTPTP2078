%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:13:19 EST 2020

% Result     : Theorem 3.00s
% Output     : CNFRefutation 3.00s
% Verified   : 
% Statistics : Number of formulae       :   99 ( 175 expanded)
%              Number of leaves         :   38 (  79 expanded)
%              Depth                    :   10
%              Number of atoms          :  194 ( 678 expanded)
%              Number of equality atoms :   73 ( 226 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > v1_partfun1 > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(k6_partfun1,type,(
    k6_partfun1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_139,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ! [D] :
            ( ( v1_funct_1(D)
              & v1_funct_2(D,B,A)
              & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,A))) )
           => ( ( k2_relset_1(A,B,C) = B
                & r2_relset_1(A,A,k1_partfun1(A,B,B,A,C,D),k6_partfun1(A))
                & v2_funct_1(C) )
             => ( A = k1_xboole_0
                | B = k1_xboole_0
                | D = k2_funct_1(C) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_funct_2)).

tff(f_55,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_85,axiom,(
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

tff(f_34,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_32,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_59,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_113,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_51,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( ( v1_relat_1(B)
            & v1_funct_1(B) )
         => ( ( v2_funct_1(A)
              & k2_relat_1(A) = k1_relat_1(B)
              & k5_relat_1(A,B) = k6_relat_1(k1_relat_1(A)) )
           => B = k2_funct_1(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_funct_1)).

tff(f_111,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_101,axiom,(
    ! [A] :
      ( v1_partfun1(k6_partfun1(A),A)
      & m1_subset_1(k6_partfun1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).

tff(f_67,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_97,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( v1_funct_1(k1_partfun1(A,B,C,D,E,F))
        & m1_subset_1(k1_partfun1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).

tff(c_40,plain,(
    k2_funct_1('#skF_3') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_56,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_44,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_54,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_52,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_143,plain,(
    ! [A_54,B_55,C_56] :
      ( k1_relset_1(A_54,B_55,C_56) = k1_relat_1(C_56)
      | ~ m1_subset_1(C_56,k1_zfmisc_1(k2_zfmisc_1(A_54,B_55))) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_154,plain,(
    k1_relset_1('#skF_2','#skF_1','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_52,c_143])).

tff(c_219,plain,(
    ! [B_68,A_69,C_70] :
      ( k1_xboole_0 = B_68
      | k1_relset_1(A_69,B_68,C_70) = A_69
      | ~ v1_funct_2(C_70,A_69,B_68)
      | ~ m1_subset_1(C_70,k1_zfmisc_1(k2_zfmisc_1(A_69,B_68))) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_225,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_relset_1('#skF_2','#skF_1','#skF_4') = '#skF_2'
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_52,c_219])).

tff(c_233,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_relat_1('#skF_4') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_154,c_225])).

tff(c_234,plain,(
    k1_relat_1('#skF_4') = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_233])).

tff(c_4,plain,(
    ! [A_4,B_5] : v1_relat_1(k2_zfmisc_1(A_4,B_5)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_80,plain,(
    ! [B_42,A_43] :
      ( v1_relat_1(B_42)
      | ~ m1_subset_1(B_42,k1_zfmisc_1(A_43))
      | ~ v1_relat_1(A_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_86,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_1')) ),
    inference(resolution,[status(thm)],[c_52,c_80])).

tff(c_95,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_86])).

tff(c_58,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_89,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_58,c_80])).

tff(c_98,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_89])).

tff(c_62,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_46,plain,(
    v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_50,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_111,plain,(
    ! [A_49,B_50,C_51] :
      ( k2_relset_1(A_49,B_50,C_51) = k2_relat_1(C_51)
      | ~ m1_subset_1(C_51,k1_zfmisc_1(k2_zfmisc_1(A_49,B_50))) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_120,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_58,c_111])).

tff(c_124,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_120])).

tff(c_42,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_60,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_155,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_58,c_143])).

tff(c_228,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_1'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_58,c_219])).

tff(c_237,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_155,c_228])).

tff(c_238,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_237])).

tff(c_38,plain,(
    ! [A_35] : k6_relat_1(A_35) = k6_partfun1(A_35) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_6,plain,(
    ! [A_6,B_8] :
      ( k2_funct_1(A_6) = B_8
      | k6_relat_1(k1_relat_1(A_6)) != k5_relat_1(A_6,B_8)
      | k2_relat_1(A_6) != k1_relat_1(B_8)
      | ~ v2_funct_1(A_6)
      | ~ v1_funct_1(B_8)
      | ~ v1_relat_1(B_8)
      | ~ v1_funct_1(A_6)
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_498,plain,(
    ! [A_110,B_111] :
      ( k2_funct_1(A_110) = B_111
      | k6_partfun1(k1_relat_1(A_110)) != k5_relat_1(A_110,B_111)
      | k2_relat_1(A_110) != k1_relat_1(B_111)
      | ~ v2_funct_1(A_110)
      | ~ v1_funct_1(B_111)
      | ~ v1_relat_1(B_111)
      | ~ v1_funct_1(A_110)
      | ~ v1_relat_1(A_110) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_6])).

tff(c_500,plain,(
    ! [B_111] :
      ( k2_funct_1('#skF_3') = B_111
      | k5_relat_1('#skF_3',B_111) != k6_partfun1('#skF_1')
      | k2_relat_1('#skF_3') != k1_relat_1(B_111)
      | ~ v2_funct_1('#skF_3')
      | ~ v1_funct_1(B_111)
      | ~ v1_relat_1(B_111)
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_238,c_498])).

tff(c_507,plain,(
    ! [B_112] :
      ( k2_funct_1('#skF_3') = B_112
      | k5_relat_1('#skF_3',B_112) != k6_partfun1('#skF_1')
      | k1_relat_1(B_112) != '#skF_2'
      | ~ v1_funct_1(B_112)
      | ~ v1_relat_1(B_112) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_62,c_46,c_124,c_500])).

tff(c_516,plain,
    ( k2_funct_1('#skF_3') = '#skF_4'
    | k5_relat_1('#skF_3','#skF_4') != k6_partfun1('#skF_1')
    | k1_relat_1('#skF_4') != '#skF_2'
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_95,c_507])).

tff(c_526,plain,
    ( k2_funct_1('#skF_3') = '#skF_4'
    | k5_relat_1('#skF_3','#skF_4') != k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_234,c_516])).

tff(c_527,plain,(
    k5_relat_1('#skF_3','#skF_4') != k6_partfun1('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_526])).

tff(c_370,plain,(
    ! [C_99,A_96,F_97,B_95,E_98,D_94] :
      ( k1_partfun1(A_96,B_95,C_99,D_94,E_98,F_97) = k5_relat_1(E_98,F_97)
      | ~ m1_subset_1(F_97,k1_zfmisc_1(k2_zfmisc_1(C_99,D_94)))
      | ~ v1_funct_1(F_97)
      | ~ m1_subset_1(E_98,k1_zfmisc_1(k2_zfmisc_1(A_96,B_95)))
      | ~ v1_funct_1(E_98) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_374,plain,(
    ! [A_96,B_95,E_98] :
      ( k1_partfun1(A_96,B_95,'#skF_2','#skF_1',E_98,'#skF_4') = k5_relat_1(E_98,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_98,k1_zfmisc_1(k2_zfmisc_1(A_96,B_95)))
      | ~ v1_funct_1(E_98) ) ),
    inference(resolution,[status(thm)],[c_52,c_370])).

tff(c_384,plain,(
    ! [A_100,B_101,E_102] :
      ( k1_partfun1(A_100,B_101,'#skF_2','#skF_1',E_102,'#skF_4') = k5_relat_1(E_102,'#skF_4')
      | ~ m1_subset_1(E_102,k1_zfmisc_1(k2_zfmisc_1(A_100,B_101)))
      | ~ v1_funct_1(E_102) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_374])).

tff(c_393,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_58,c_384])).

tff(c_400,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_393])).

tff(c_34,plain,(
    ! [A_28] : m1_subset_1(k6_partfun1(A_28),k1_zfmisc_1(k2_zfmisc_1(A_28,A_28))) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_48,plain,(
    r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k6_partfun1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_253,plain,(
    ! [D_71,C_72,A_73,B_74] :
      ( D_71 = C_72
      | ~ r2_relset_1(A_73,B_74,C_72,D_71)
      | ~ m1_subset_1(D_71,k1_zfmisc_1(k2_zfmisc_1(A_73,B_74)))
      | ~ m1_subset_1(C_72,k1_zfmisc_1(k2_zfmisc_1(A_73,B_74))) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_261,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_48,c_253])).

tff(c_276,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_261])).

tff(c_286,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_276])).

tff(c_407,plain,(
    ~ m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_400,c_286])).

tff(c_420,plain,(
    ! [D_108,C_105,F_107,E_106,B_109,A_104] :
      ( m1_subset_1(k1_partfun1(A_104,B_109,C_105,D_108,E_106,F_107),k1_zfmisc_1(k2_zfmisc_1(A_104,D_108)))
      | ~ m1_subset_1(F_107,k1_zfmisc_1(k2_zfmisc_1(C_105,D_108)))
      | ~ v1_funct_1(F_107)
      | ~ m1_subset_1(E_106,k1_zfmisc_1(k2_zfmisc_1(A_104,B_109)))
      | ~ v1_funct_1(E_106) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_465,plain,
    ( m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_400,c_420])).

tff(c_486,plain,(
    m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_58,c_56,c_52,c_465])).

tff(c_488,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_407,c_486])).

tff(c_489,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_276])).

tff(c_586,plain,(
    ! [E_132,B_129,A_130,C_133,F_131,D_128] :
      ( k1_partfun1(A_130,B_129,C_133,D_128,E_132,F_131) = k5_relat_1(E_132,F_131)
      | ~ m1_subset_1(F_131,k1_zfmisc_1(k2_zfmisc_1(C_133,D_128)))
      | ~ v1_funct_1(F_131)
      | ~ m1_subset_1(E_132,k1_zfmisc_1(k2_zfmisc_1(A_130,B_129)))
      | ~ v1_funct_1(E_132) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_590,plain,(
    ! [A_130,B_129,E_132] :
      ( k1_partfun1(A_130,B_129,'#skF_2','#skF_1',E_132,'#skF_4') = k5_relat_1(E_132,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_132,k1_zfmisc_1(k2_zfmisc_1(A_130,B_129)))
      | ~ v1_funct_1(E_132) ) ),
    inference(resolution,[status(thm)],[c_52,c_586])).

tff(c_601,plain,(
    ! [A_134,B_135,E_136] :
      ( k1_partfun1(A_134,B_135,'#skF_2','#skF_1',E_136,'#skF_4') = k5_relat_1(E_136,'#skF_4')
      | ~ m1_subset_1(E_136,k1_zfmisc_1(k2_zfmisc_1(A_134,B_135)))
      | ~ v1_funct_1(E_136) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_590])).

tff(c_610,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_58,c_601])).

tff(c_617,plain,(
    k5_relat_1('#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_489,c_610])).

tff(c_619,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_527,c_617])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:53:38 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.00/1.43  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.00/1.44  
% 3.00/1.44  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.00/1.44  %$ r2_relset_1 > v1_funct_2 > v1_partfun1 > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 3.00/1.44  
% 3.00/1.44  %Foreground sorts:
% 3.00/1.44  
% 3.00/1.44  
% 3.00/1.44  %Background operators:
% 3.00/1.44  
% 3.00/1.44  
% 3.00/1.44  %Foreground operators:
% 3.00/1.44  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 3.00/1.44  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.00/1.44  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 3.00/1.44  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 3.00/1.44  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.00/1.44  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 3.00/1.44  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.00/1.44  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 3.00/1.44  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.00/1.44  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.00/1.44  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.00/1.44  tff('#skF_2', type, '#skF_2': $i).
% 3.00/1.44  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 3.00/1.44  tff('#skF_3', type, '#skF_3': $i).
% 3.00/1.44  tff('#skF_1', type, '#skF_1': $i).
% 3.00/1.44  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.00/1.44  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.00/1.44  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 3.00/1.44  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.00/1.44  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.00/1.44  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.00/1.44  tff('#skF_4', type, '#skF_4': $i).
% 3.00/1.44  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 3.00/1.44  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.00/1.44  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.00/1.44  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.00/1.44  
% 3.00/1.46  tff(f_139, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => ((((k2_relset_1(A, B, C) = B) & r2_relset_1(A, A, k1_partfun1(A, B, B, A, C, D), k6_partfun1(A))) & v2_funct_1(C)) => (((A = k1_xboole_0) | (B = k1_xboole_0)) | (D = k2_funct_1(C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_funct_2)).
% 3.00/1.46  tff(f_55, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.00/1.46  tff(f_85, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 3.00/1.46  tff(f_34, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 3.00/1.46  tff(f_32, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 3.00/1.46  tff(f_59, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 3.00/1.46  tff(f_113, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 3.00/1.46  tff(f_51, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (((v2_funct_1(A) & (k2_relat_1(A) = k1_relat_1(B))) & (k5_relat_1(A, B) = k6_relat_1(k1_relat_1(A)))) => (B = k2_funct_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_funct_1)).
% 3.00/1.46  tff(f_111, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 3.00/1.46  tff(f_101, axiom, (![A]: (v1_partfun1(k6_partfun1(A), A) & m1_subset_1(k6_partfun1(A), k1_zfmisc_1(k2_zfmisc_1(A, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_partfun1)).
% 3.00/1.46  tff(f_67, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 3.00/1.46  tff(f_97, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (v1_funct_1(k1_partfun1(A, B, C, D, E, F)) & m1_subset_1(k1_partfun1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 3.00/1.46  tff(c_40, plain, (k2_funct_1('#skF_3')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_139])).
% 3.00/1.46  tff(c_56, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_139])).
% 3.00/1.46  tff(c_44, plain, (k1_xboole_0!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_139])).
% 3.00/1.46  tff(c_54, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_139])).
% 3.00/1.46  tff(c_52, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_139])).
% 3.00/1.46  tff(c_143, plain, (![A_54, B_55, C_56]: (k1_relset_1(A_54, B_55, C_56)=k1_relat_1(C_56) | ~m1_subset_1(C_56, k1_zfmisc_1(k2_zfmisc_1(A_54, B_55))))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.00/1.46  tff(c_154, plain, (k1_relset_1('#skF_2', '#skF_1', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_52, c_143])).
% 3.00/1.46  tff(c_219, plain, (![B_68, A_69, C_70]: (k1_xboole_0=B_68 | k1_relset_1(A_69, B_68, C_70)=A_69 | ~v1_funct_2(C_70, A_69, B_68) | ~m1_subset_1(C_70, k1_zfmisc_1(k2_zfmisc_1(A_69, B_68))))), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.00/1.46  tff(c_225, plain, (k1_xboole_0='#skF_1' | k1_relset_1('#skF_2', '#skF_1', '#skF_4')='#skF_2' | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_52, c_219])).
% 3.00/1.46  tff(c_233, plain, (k1_xboole_0='#skF_1' | k1_relat_1('#skF_4')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_54, c_154, c_225])).
% 3.00/1.46  tff(c_234, plain, (k1_relat_1('#skF_4')='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_44, c_233])).
% 3.00/1.46  tff(c_4, plain, (![A_4, B_5]: (v1_relat_1(k2_zfmisc_1(A_4, B_5)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.00/1.46  tff(c_80, plain, (![B_42, A_43]: (v1_relat_1(B_42) | ~m1_subset_1(B_42, k1_zfmisc_1(A_43)) | ~v1_relat_1(A_43))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.00/1.46  tff(c_86, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_1'))), inference(resolution, [status(thm)], [c_52, c_80])).
% 3.00/1.46  tff(c_95, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_86])).
% 3.00/1.46  tff(c_58, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_139])).
% 3.00/1.46  tff(c_89, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_58, c_80])).
% 3.00/1.46  tff(c_98, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_89])).
% 3.00/1.46  tff(c_62, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_139])).
% 3.00/1.46  tff(c_46, plain, (v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_139])).
% 3.00/1.46  tff(c_50, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_2'), inference(cnfTransformation, [status(thm)], [f_139])).
% 3.00/1.46  tff(c_111, plain, (![A_49, B_50, C_51]: (k2_relset_1(A_49, B_50, C_51)=k2_relat_1(C_51) | ~m1_subset_1(C_51, k1_zfmisc_1(k2_zfmisc_1(A_49, B_50))))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.00/1.46  tff(c_120, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_58, c_111])).
% 3.00/1.46  tff(c_124, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_50, c_120])).
% 3.00/1.46  tff(c_42, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_139])).
% 3.00/1.46  tff(c_60, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_139])).
% 3.00/1.46  tff(c_155, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_58, c_143])).
% 3.00/1.46  tff(c_228, plain, (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_1' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_58, c_219])).
% 3.00/1.46  tff(c_237, plain, (k1_xboole_0='#skF_2' | k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_60, c_155, c_228])).
% 3.00/1.46  tff(c_238, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_42, c_237])).
% 3.00/1.46  tff(c_38, plain, (![A_35]: (k6_relat_1(A_35)=k6_partfun1(A_35))), inference(cnfTransformation, [status(thm)], [f_113])).
% 3.00/1.46  tff(c_6, plain, (![A_6, B_8]: (k2_funct_1(A_6)=B_8 | k6_relat_1(k1_relat_1(A_6))!=k5_relat_1(A_6, B_8) | k2_relat_1(A_6)!=k1_relat_1(B_8) | ~v2_funct_1(A_6) | ~v1_funct_1(B_8) | ~v1_relat_1(B_8) | ~v1_funct_1(A_6) | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.00/1.46  tff(c_498, plain, (![A_110, B_111]: (k2_funct_1(A_110)=B_111 | k6_partfun1(k1_relat_1(A_110))!=k5_relat_1(A_110, B_111) | k2_relat_1(A_110)!=k1_relat_1(B_111) | ~v2_funct_1(A_110) | ~v1_funct_1(B_111) | ~v1_relat_1(B_111) | ~v1_funct_1(A_110) | ~v1_relat_1(A_110))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_6])).
% 3.00/1.46  tff(c_500, plain, (![B_111]: (k2_funct_1('#skF_3')=B_111 | k5_relat_1('#skF_3', B_111)!=k6_partfun1('#skF_1') | k2_relat_1('#skF_3')!=k1_relat_1(B_111) | ~v2_funct_1('#skF_3') | ~v1_funct_1(B_111) | ~v1_relat_1(B_111) | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_238, c_498])).
% 3.00/1.46  tff(c_507, plain, (![B_112]: (k2_funct_1('#skF_3')=B_112 | k5_relat_1('#skF_3', B_112)!=k6_partfun1('#skF_1') | k1_relat_1(B_112)!='#skF_2' | ~v1_funct_1(B_112) | ~v1_relat_1(B_112))), inference(demodulation, [status(thm), theory('equality')], [c_98, c_62, c_46, c_124, c_500])).
% 3.00/1.46  tff(c_516, plain, (k2_funct_1('#skF_3')='#skF_4' | k5_relat_1('#skF_3', '#skF_4')!=k6_partfun1('#skF_1') | k1_relat_1('#skF_4')!='#skF_2' | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_95, c_507])).
% 3.00/1.46  tff(c_526, plain, (k2_funct_1('#skF_3')='#skF_4' | k5_relat_1('#skF_3', '#skF_4')!=k6_partfun1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_234, c_516])).
% 3.00/1.46  tff(c_527, plain, (k5_relat_1('#skF_3', '#skF_4')!=k6_partfun1('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_40, c_526])).
% 3.00/1.46  tff(c_370, plain, (![C_99, A_96, F_97, B_95, E_98, D_94]: (k1_partfun1(A_96, B_95, C_99, D_94, E_98, F_97)=k5_relat_1(E_98, F_97) | ~m1_subset_1(F_97, k1_zfmisc_1(k2_zfmisc_1(C_99, D_94))) | ~v1_funct_1(F_97) | ~m1_subset_1(E_98, k1_zfmisc_1(k2_zfmisc_1(A_96, B_95))) | ~v1_funct_1(E_98))), inference(cnfTransformation, [status(thm)], [f_111])).
% 3.00/1.46  tff(c_374, plain, (![A_96, B_95, E_98]: (k1_partfun1(A_96, B_95, '#skF_2', '#skF_1', E_98, '#skF_4')=k5_relat_1(E_98, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_98, k1_zfmisc_1(k2_zfmisc_1(A_96, B_95))) | ~v1_funct_1(E_98))), inference(resolution, [status(thm)], [c_52, c_370])).
% 3.00/1.46  tff(c_384, plain, (![A_100, B_101, E_102]: (k1_partfun1(A_100, B_101, '#skF_2', '#skF_1', E_102, '#skF_4')=k5_relat_1(E_102, '#skF_4') | ~m1_subset_1(E_102, k1_zfmisc_1(k2_zfmisc_1(A_100, B_101))) | ~v1_funct_1(E_102))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_374])).
% 3.00/1.46  tff(c_393, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_58, c_384])).
% 3.00/1.46  tff(c_400, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_393])).
% 3.00/1.46  tff(c_34, plain, (![A_28]: (m1_subset_1(k6_partfun1(A_28), k1_zfmisc_1(k2_zfmisc_1(A_28, A_28))))), inference(cnfTransformation, [status(thm)], [f_101])).
% 3.00/1.46  tff(c_48, plain, (r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k6_partfun1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_139])).
% 3.00/1.46  tff(c_253, plain, (![D_71, C_72, A_73, B_74]: (D_71=C_72 | ~r2_relset_1(A_73, B_74, C_72, D_71) | ~m1_subset_1(D_71, k1_zfmisc_1(k2_zfmisc_1(A_73, B_74))) | ~m1_subset_1(C_72, k1_zfmisc_1(k2_zfmisc_1(A_73, B_74))))), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.00/1.46  tff(c_261, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_48, c_253])).
% 3.00/1.46  tff(c_276, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_261])).
% 3.00/1.46  tff(c_286, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_276])).
% 3.00/1.46  tff(c_407, plain, (~m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_400, c_286])).
% 3.00/1.46  tff(c_420, plain, (![D_108, C_105, F_107, E_106, B_109, A_104]: (m1_subset_1(k1_partfun1(A_104, B_109, C_105, D_108, E_106, F_107), k1_zfmisc_1(k2_zfmisc_1(A_104, D_108))) | ~m1_subset_1(F_107, k1_zfmisc_1(k2_zfmisc_1(C_105, D_108))) | ~v1_funct_1(F_107) | ~m1_subset_1(E_106, k1_zfmisc_1(k2_zfmisc_1(A_104, B_109))) | ~v1_funct_1(E_106))), inference(cnfTransformation, [status(thm)], [f_97])).
% 3.00/1.46  tff(c_465, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_400, c_420])).
% 3.00/1.46  tff(c_486, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_58, c_56, c_52, c_465])).
% 3.00/1.46  tff(c_488, plain, $false, inference(negUnitSimplification, [status(thm)], [c_407, c_486])).
% 3.00/1.46  tff(c_489, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_276])).
% 3.00/1.46  tff(c_586, plain, (![E_132, B_129, A_130, C_133, F_131, D_128]: (k1_partfun1(A_130, B_129, C_133, D_128, E_132, F_131)=k5_relat_1(E_132, F_131) | ~m1_subset_1(F_131, k1_zfmisc_1(k2_zfmisc_1(C_133, D_128))) | ~v1_funct_1(F_131) | ~m1_subset_1(E_132, k1_zfmisc_1(k2_zfmisc_1(A_130, B_129))) | ~v1_funct_1(E_132))), inference(cnfTransformation, [status(thm)], [f_111])).
% 3.00/1.46  tff(c_590, plain, (![A_130, B_129, E_132]: (k1_partfun1(A_130, B_129, '#skF_2', '#skF_1', E_132, '#skF_4')=k5_relat_1(E_132, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_132, k1_zfmisc_1(k2_zfmisc_1(A_130, B_129))) | ~v1_funct_1(E_132))), inference(resolution, [status(thm)], [c_52, c_586])).
% 3.00/1.46  tff(c_601, plain, (![A_134, B_135, E_136]: (k1_partfun1(A_134, B_135, '#skF_2', '#skF_1', E_136, '#skF_4')=k5_relat_1(E_136, '#skF_4') | ~m1_subset_1(E_136, k1_zfmisc_1(k2_zfmisc_1(A_134, B_135))) | ~v1_funct_1(E_136))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_590])).
% 3.00/1.46  tff(c_610, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_58, c_601])).
% 3.00/1.46  tff(c_617, plain, (k5_relat_1('#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_489, c_610])).
% 3.00/1.46  tff(c_619, plain, $false, inference(negUnitSimplification, [status(thm)], [c_527, c_617])).
% 3.00/1.46  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.00/1.46  
% 3.00/1.46  Inference rules
% 3.00/1.46  ----------------------
% 3.00/1.46  #Ref     : 0
% 3.00/1.46  #Sup     : 117
% 3.00/1.46  #Fact    : 0
% 3.00/1.46  #Define  : 0
% 3.00/1.46  #Split   : 6
% 3.00/1.46  #Chain   : 0
% 3.00/1.46  #Close   : 0
% 3.00/1.46  
% 3.00/1.46  Ordering : KBO
% 3.00/1.46  
% 3.00/1.46  Simplification rules
% 3.00/1.46  ----------------------
% 3.00/1.46  #Subsume      : 2
% 3.00/1.46  #Demod        : 79
% 3.00/1.46  #Tautology    : 39
% 3.00/1.46  #SimpNegUnit  : 10
% 3.00/1.46  #BackRed      : 7
% 3.00/1.46  
% 3.00/1.46  #Partial instantiations: 0
% 3.00/1.46  #Strategies tried      : 1
% 3.00/1.46  
% 3.00/1.46  Timing (in seconds)
% 3.00/1.46  ----------------------
% 3.00/1.46  Preprocessing        : 0.34
% 3.00/1.46  Parsing              : 0.18
% 3.00/1.46  CNF conversion       : 0.02
% 3.00/1.46  Main loop            : 0.35
% 3.00/1.46  Inferencing          : 0.13
% 3.00/1.46  Reduction            : 0.12
% 3.00/1.46  Demodulation         : 0.08
% 3.00/1.46  BG Simplification    : 0.02
% 3.00/1.46  Subsumption          : 0.05
% 3.00/1.46  Abstraction          : 0.02
% 3.00/1.46  MUC search           : 0.00
% 3.00/1.46  Cooper               : 0.00
% 3.00/1.46  Total                : 0.73
% 3.00/1.46  Index Insertion      : 0.00
% 3.00/1.46  Index Deletion       : 0.00
% 3.00/1.46  Index Matching       : 0.00
% 3.00/1.46  BG Taut test         : 0.00
%------------------------------------------------------------------------------
