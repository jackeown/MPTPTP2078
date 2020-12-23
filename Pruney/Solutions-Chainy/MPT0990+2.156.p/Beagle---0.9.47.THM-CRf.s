%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:13:19 EST 2020

% Result     : Theorem 3.68s
% Output     : CNFRefutation 4.10s
% Verified   : 
% Statistics : Number of formulae       :  137 ( 704 expanded)
%              Number of leaves         :   42 ( 267 expanded)
%              Depth                    :   18
%              Number of atoms          :  321 (2948 expanded)
%              Number of equality atoms :  113 (1036 expanded)
%              Maximal formula depth    :   13 (   4 average)
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

tff(f_183,negated_conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_funct_2)).

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

tff(f_82,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_112,axiom,(
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

tff(f_86,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_140,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_70,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( ( v1_relat_1(B)
            & v1_funct_1(B) )
         => ( ( v2_funct_1(A)
              & k2_relat_1(B) = k1_relat_1(A)
              & k5_relat_1(B,A) = k6_relat_1(k2_relat_1(A)) )
           => B = k2_funct_1(A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_funct_1)).

tff(f_128,axiom,(
    ! [A] :
      ( v1_partfun1(k6_partfun1(A),A)
      & m1_subset_1(k6_partfun1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_partfun1)).

tff(f_94,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_138,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_124,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( v1_funct_1(k1_partfun1(A,B,C,D,E,F))
        & m1_subset_1(k1_partfun1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).

tff(f_157,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ! [D] :
          ( ( v1_funct_1(D)
            & v1_funct_2(D,B,A)
            & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,A))) )
         => ( r2_relset_1(B,B,k1_partfun1(B,A,A,B,D,C),k6_partfun1(B))
           => k2_relset_1(A,B,C) = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_funct_2)).

tff(f_53,axiom,(
    ! [A] : v2_funct_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_funct_1)).

tff(f_51,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( ( v1_relat_1(B)
            & v1_funct_1(B) )
         => ( ( v2_funct_1(k5_relat_1(B,A))
              & k2_relat_1(B) = k1_relat_1(A) )
           => ( v2_funct_1(B)
              & v2_funct_1(A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_funct_1)).

tff(f_78,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => k2_funct_1(k2_funct_1(A)) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_funct_1)).

tff(c_50,plain,(
    k2_funct_1('#skF_3') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_183])).

tff(c_4,plain,(
    ! [A_4,B_5] : v1_relat_1(k2_zfmisc_1(A_4,B_5)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_62,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_183])).

tff(c_92,plain,(
    ! [B_53,A_54] :
      ( v1_relat_1(B_53)
      | ~ m1_subset_1(B_53,k1_zfmisc_1(A_54))
      | ~ v1_relat_1(A_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_101,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_1')) ),
    inference(resolution,[status(thm)],[c_62,c_92])).

tff(c_110,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_101])).

tff(c_66,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_183])).

tff(c_54,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_183])).

tff(c_64,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_183])).

tff(c_172,plain,(
    ! [A_66,B_67,C_68] :
      ( k1_relset_1(A_66,B_67,C_68) = k1_relat_1(C_68)
      | ~ m1_subset_1(C_68,k1_zfmisc_1(k2_zfmisc_1(A_66,B_67))) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_184,plain,(
    k1_relset_1('#skF_2','#skF_1','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_62,c_172])).

tff(c_248,plain,(
    ! [B_80,A_81,C_82] :
      ( k1_xboole_0 = B_80
      | k1_relset_1(A_81,B_80,C_82) = A_81
      | ~ v1_funct_2(C_82,A_81,B_80)
      | ~ m1_subset_1(C_82,k1_zfmisc_1(k2_zfmisc_1(A_81,B_80))) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_257,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_relset_1('#skF_2','#skF_1','#skF_4') = '#skF_2'
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_62,c_248])).

tff(c_266,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_relat_1('#skF_4') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_184,c_257])).

tff(c_267,plain,(
    k1_relat_1('#skF_4') = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_266])).

tff(c_68,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_183])).

tff(c_98,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_68,c_92])).

tff(c_107,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_98])).

tff(c_72,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_183])).

tff(c_56,plain,(
    v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_183])).

tff(c_52,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_183])).

tff(c_70,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_183])).

tff(c_183,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_68,c_172])).

tff(c_254,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_1'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_68,c_248])).

tff(c_262,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_183,c_254])).

tff(c_263,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_262])).

tff(c_60,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_183])).

tff(c_139,plain,(
    ! [A_60,B_61,C_62] :
      ( k2_relset_1(A_60,B_61,C_62) = k2_relat_1(C_62)
      | ~ m1_subset_1(C_62,k1_zfmisc_1(k2_zfmisc_1(A_60,B_61))) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_145,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_68,c_139])).

tff(c_151,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_145])).

tff(c_46,plain,(
    ! [A_40] : k6_relat_1(A_40) = k6_partfun1(A_40) ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_12,plain,(
    ! [A_10,B_12] :
      ( k2_funct_1(A_10) = B_12
      | k6_relat_1(k2_relat_1(A_10)) != k5_relat_1(B_12,A_10)
      | k2_relat_1(B_12) != k1_relat_1(A_10)
      | ~ v2_funct_1(A_10)
      | ~ v1_funct_1(B_12)
      | ~ v1_relat_1(B_12)
      | ~ v1_funct_1(A_10)
      | ~ v1_relat_1(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_524,plain,(
    ! [A_123,B_124] :
      ( k2_funct_1(A_123) = B_124
      | k6_partfun1(k2_relat_1(A_123)) != k5_relat_1(B_124,A_123)
      | k2_relat_1(B_124) != k1_relat_1(A_123)
      | ~ v2_funct_1(A_123)
      | ~ v1_funct_1(B_124)
      | ~ v1_relat_1(B_124)
      | ~ v1_funct_1(A_123)
      | ~ v1_relat_1(A_123) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_12])).

tff(c_526,plain,(
    ! [B_124] :
      ( k2_funct_1('#skF_3') = B_124
      | k5_relat_1(B_124,'#skF_3') != k6_partfun1('#skF_2')
      | k2_relat_1(B_124) != k1_relat_1('#skF_3')
      | ~ v2_funct_1('#skF_3')
      | ~ v1_funct_1(B_124)
      | ~ v1_relat_1(B_124)
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_151,c_524])).

tff(c_529,plain,(
    ! [B_125] :
      ( k2_funct_1('#skF_3') = B_125
      | k5_relat_1(B_125,'#skF_3') != k6_partfun1('#skF_2')
      | k2_relat_1(B_125) != '#skF_1'
      | ~ v1_funct_1(B_125)
      | ~ v1_relat_1(B_125) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_107,c_72,c_56,c_263,c_526])).

tff(c_535,plain,
    ( k2_funct_1('#skF_3') = '#skF_4'
    | k5_relat_1('#skF_4','#skF_3') != k6_partfun1('#skF_2')
    | k2_relat_1('#skF_4') != '#skF_1'
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_110,c_529])).

tff(c_545,plain,
    ( k2_funct_1('#skF_3') = '#skF_4'
    | k5_relat_1('#skF_4','#skF_3') != k6_partfun1('#skF_2')
    | k2_relat_1('#skF_4') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_535])).

tff(c_546,plain,
    ( k5_relat_1('#skF_4','#skF_3') != k6_partfun1('#skF_2')
    | k2_relat_1('#skF_4') != '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_545])).

tff(c_551,plain,(
    k2_relat_1('#skF_4') != '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_546])).

tff(c_42,plain,(
    ! [A_33] : m1_subset_1(k6_partfun1(A_33),k1_zfmisc_1(k2_zfmisc_1(A_33,A_33))) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_129,plain,(
    ! [A_57,B_58,D_59] :
      ( r2_relset_1(A_57,B_58,D_59,D_59)
      | ~ m1_subset_1(D_59,k1_zfmisc_1(k2_zfmisc_1(A_57,B_58))) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_136,plain,(
    ! [A_33] : r2_relset_1(A_33,A_33,k6_partfun1(A_33),k6_partfun1(A_33)) ),
    inference(resolution,[status(thm)],[c_42,c_129])).

tff(c_152,plain,(
    k2_relset_1('#skF_2','#skF_1','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_62,c_139])).

tff(c_379,plain,(
    ! [E_108,C_110,A_105,F_107,B_109,D_106] :
      ( k1_partfun1(A_105,B_109,C_110,D_106,E_108,F_107) = k5_relat_1(E_108,F_107)
      | ~ m1_subset_1(F_107,k1_zfmisc_1(k2_zfmisc_1(C_110,D_106)))
      | ~ v1_funct_1(F_107)
      | ~ m1_subset_1(E_108,k1_zfmisc_1(k2_zfmisc_1(A_105,B_109)))
      | ~ v1_funct_1(E_108) ) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_385,plain,(
    ! [A_105,B_109,E_108] :
      ( k1_partfun1(A_105,B_109,'#skF_2','#skF_1',E_108,'#skF_4') = k5_relat_1(E_108,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_108,k1_zfmisc_1(k2_zfmisc_1(A_105,B_109)))
      | ~ v1_funct_1(E_108) ) ),
    inference(resolution,[status(thm)],[c_62,c_379])).

tff(c_410,plain,(
    ! [A_114,B_115,E_116] :
      ( k1_partfun1(A_114,B_115,'#skF_2','#skF_1',E_116,'#skF_4') = k5_relat_1(E_116,'#skF_4')
      | ~ m1_subset_1(E_116,k1_zfmisc_1(k2_zfmisc_1(A_114,B_115)))
      | ~ v1_funct_1(E_116) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_385])).

tff(c_416,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_68,c_410])).

tff(c_423,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_416])).

tff(c_58,plain,(
    r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k6_partfun1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_183])).

tff(c_293,plain,(
    ! [D_88,C_89,A_90,B_91] :
      ( D_88 = C_89
      | ~ r2_relset_1(A_90,B_91,C_89,D_88)
      | ~ m1_subset_1(D_88,k1_zfmisc_1(k2_zfmisc_1(A_90,B_91)))
      | ~ m1_subset_1(C_89,k1_zfmisc_1(k2_zfmisc_1(A_90,B_91))) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_301,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_58,c_293])).

tff(c_316,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_301])).

tff(c_317,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_316])).

tff(c_428,plain,(
    ~ m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_423,c_317])).

tff(c_444,plain,(
    ! [A_122,B_121,F_117,D_119,E_120,C_118] :
      ( m1_subset_1(k1_partfun1(A_122,B_121,C_118,D_119,E_120,F_117),k1_zfmisc_1(k2_zfmisc_1(A_122,D_119)))
      | ~ m1_subset_1(F_117,k1_zfmisc_1(k2_zfmisc_1(C_118,D_119)))
      | ~ v1_funct_1(F_117)
      | ~ m1_subset_1(E_120,k1_zfmisc_1(k2_zfmisc_1(A_122,B_121)))
      | ~ v1_funct_1(E_120) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_492,plain,
    ( m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_423,c_444])).

tff(c_512,plain,(
    m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_68,c_66,c_62,c_492])).

tff(c_514,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_428,c_512])).

tff(c_515,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_316])).

tff(c_883,plain,(
    ! [A_157,B_158,C_159,D_160] :
      ( k2_relset_1(A_157,B_158,C_159) = B_158
      | ~ r2_relset_1(B_158,B_158,k1_partfun1(B_158,A_157,A_157,B_158,D_160,C_159),k6_partfun1(B_158))
      | ~ m1_subset_1(D_160,k1_zfmisc_1(k2_zfmisc_1(B_158,A_157)))
      | ~ v1_funct_2(D_160,B_158,A_157)
      | ~ v1_funct_1(D_160)
      | ~ m1_subset_1(C_159,k1_zfmisc_1(k2_zfmisc_1(A_157,B_158)))
      | ~ v1_funct_2(C_159,A_157,B_158)
      | ~ v1_funct_1(C_159) ) ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_886,plain,
    ( k2_relset_1('#skF_2','#skF_1','#skF_4') = '#skF_1'
    | ~ r2_relset_1('#skF_1','#skF_1',k6_partfun1('#skF_1'),k6_partfun1('#skF_1'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_515,c_883])).

tff(c_888,plain,(
    k2_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_62,c_72,c_70,c_68,c_136,c_152,c_886])).

tff(c_890,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_551,c_888])).

tff(c_892,plain,(
    k2_relat_1('#skF_4') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_546])).

tff(c_73,plain,(
    ! [A_10,B_12] :
      ( k2_funct_1(A_10) = B_12
      | k6_partfun1(k2_relat_1(A_10)) != k5_relat_1(B_12,A_10)
      | k2_relat_1(B_12) != k1_relat_1(A_10)
      | ~ v2_funct_1(A_10)
      | ~ v1_funct_1(B_12)
      | ~ v1_relat_1(B_12)
      | ~ v1_funct_1(A_10)
      | ~ v1_relat_1(A_10) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_12])).

tff(c_896,plain,(
    ! [B_12] :
      ( k2_funct_1('#skF_4') = B_12
      | k5_relat_1(B_12,'#skF_4') != k6_partfun1('#skF_1')
      | k2_relat_1(B_12) != k1_relat_1('#skF_4')
      | ~ v2_funct_1('#skF_4')
      | ~ v1_funct_1(B_12)
      | ~ v1_relat_1(B_12)
      | ~ v1_funct_1('#skF_4')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_892,c_73])).

tff(c_900,plain,(
    ! [B_12] :
      ( k2_funct_1('#skF_4') = B_12
      | k5_relat_1(B_12,'#skF_4') != k6_partfun1('#skF_1')
      | k2_relat_1(B_12) != '#skF_2'
      | ~ v2_funct_1('#skF_4')
      | ~ v1_funct_1(B_12)
      | ~ v1_relat_1(B_12) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_110,c_66,c_267,c_896])).

tff(c_908,plain,(
    ~ v2_funct_1('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_900])).

tff(c_10,plain,(
    ! [A_9] : v2_funct_1(k6_relat_1(A_9)) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_74,plain,(
    ! [A_9] : v2_funct_1(k6_partfun1(A_9)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_10])).

tff(c_965,plain,(
    ! [A_178,D_179,E_181,F_180,C_183,B_182] :
      ( k1_partfun1(A_178,B_182,C_183,D_179,E_181,F_180) = k5_relat_1(E_181,F_180)
      | ~ m1_subset_1(F_180,k1_zfmisc_1(k2_zfmisc_1(C_183,D_179)))
      | ~ v1_funct_1(F_180)
      | ~ m1_subset_1(E_181,k1_zfmisc_1(k2_zfmisc_1(A_178,B_182)))
      | ~ v1_funct_1(E_181) ) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_971,plain,(
    ! [A_178,B_182,E_181] :
      ( k1_partfun1(A_178,B_182,'#skF_2','#skF_1',E_181,'#skF_4') = k5_relat_1(E_181,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_181,k1_zfmisc_1(k2_zfmisc_1(A_178,B_182)))
      | ~ v1_funct_1(E_181) ) ),
    inference(resolution,[status(thm)],[c_62,c_965])).

tff(c_979,plain,(
    ! [A_184,B_185,E_186] :
      ( k1_partfun1(A_184,B_185,'#skF_2','#skF_1',E_186,'#skF_4') = k5_relat_1(E_186,'#skF_4')
      | ~ m1_subset_1(E_186,k1_zfmisc_1(k2_zfmisc_1(A_184,B_185)))
      | ~ v1_funct_1(E_186) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_971])).

tff(c_985,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_68,c_979])).

tff(c_992,plain,(
    k5_relat_1('#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_515,c_985])).

tff(c_6,plain,(
    ! [A_6,B_8] :
      ( v2_funct_1(A_6)
      | k2_relat_1(B_8) != k1_relat_1(A_6)
      | ~ v2_funct_1(k5_relat_1(B_8,A_6))
      | ~ v1_funct_1(B_8)
      | ~ v1_relat_1(B_8)
      | ~ v1_funct_1(A_6)
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_999,plain,
    ( v2_funct_1('#skF_4')
    | k2_relat_1('#skF_3') != k1_relat_1('#skF_4')
    | ~ v2_funct_1(k6_partfun1('#skF_1'))
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_992,c_6])).

tff(c_1006,plain,(
    v2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_110,c_66,c_107,c_72,c_74,c_151,c_267,c_999])).

tff(c_1008,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_908,c_1006])).

tff(c_1010,plain,(
    v2_funct_1('#skF_4') ),
    inference(splitRight,[status(thm)],[c_900])).

tff(c_1011,plain,(
    ! [B_187] :
      ( k2_funct_1('#skF_4') = B_187
      | k5_relat_1(B_187,'#skF_4') != k6_partfun1('#skF_1')
      | k2_relat_1(B_187) != '#skF_2'
      | ~ v1_funct_1(B_187)
      | ~ v1_relat_1(B_187) ) ),
    inference(splitRight,[status(thm)],[c_900])).

tff(c_1020,plain,
    ( k2_funct_1('#skF_4') = '#skF_3'
    | k5_relat_1('#skF_3','#skF_4') != k6_partfun1('#skF_1')
    | k2_relat_1('#skF_3') != '#skF_2'
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_107,c_1011])).

tff(c_1030,plain,
    ( k2_funct_1('#skF_4') = '#skF_3'
    | k5_relat_1('#skF_3','#skF_4') != k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_151,c_1020])).

tff(c_1032,plain,(
    k5_relat_1('#skF_3','#skF_4') != k6_partfun1('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_1030])).

tff(c_1094,plain,(
    ! [B_209,C_210,A_205,F_207,E_208,D_206] :
      ( k1_partfun1(A_205,B_209,C_210,D_206,E_208,F_207) = k5_relat_1(E_208,F_207)
      | ~ m1_subset_1(F_207,k1_zfmisc_1(k2_zfmisc_1(C_210,D_206)))
      | ~ v1_funct_1(F_207)
      | ~ m1_subset_1(E_208,k1_zfmisc_1(k2_zfmisc_1(A_205,B_209)))
      | ~ v1_funct_1(E_208) ) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_1100,plain,(
    ! [A_205,B_209,E_208] :
      ( k1_partfun1(A_205,B_209,'#skF_2','#skF_1',E_208,'#skF_4') = k5_relat_1(E_208,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_208,k1_zfmisc_1(k2_zfmisc_1(A_205,B_209)))
      | ~ v1_funct_1(E_208) ) ),
    inference(resolution,[status(thm)],[c_62,c_1094])).

tff(c_1394,plain,(
    ! [A_225,B_226,E_227] :
      ( k1_partfun1(A_225,B_226,'#skF_2','#skF_1',E_227,'#skF_4') = k5_relat_1(E_227,'#skF_4')
      | ~ m1_subset_1(E_227,k1_zfmisc_1(k2_zfmisc_1(A_225,B_226)))
      | ~ v1_funct_1(E_227) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_1100])).

tff(c_1409,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_68,c_1394])).

tff(c_1423,plain,(
    k5_relat_1('#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_515,c_1409])).

tff(c_1425,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1032,c_1423])).

tff(c_1426,plain,(
    k2_funct_1('#skF_4') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_1030])).

tff(c_14,plain,(
    ! [A_13] :
      ( k2_funct_1(k2_funct_1(A_13)) = A_13
      | ~ v2_funct_1(A_13)
      | ~ v1_funct_1(A_13)
      | ~ v1_relat_1(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_1432,plain,
    ( k2_funct_1('#skF_3') = '#skF_4'
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1426,c_14])).

tff(c_1436,plain,(
    k2_funct_1('#skF_3') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_110,c_66,c_1010,c_1432])).

tff(c_1438,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_1436])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n017.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 17:47:31 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.68/1.65  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.01/1.68  
% 4.01/1.68  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.01/1.68  %$ r2_relset_1 > v1_funct_2 > v1_partfun1 > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 4.01/1.68  
% 4.01/1.68  %Foreground sorts:
% 4.01/1.68  
% 4.01/1.68  
% 4.01/1.68  %Background operators:
% 4.01/1.68  
% 4.01/1.68  
% 4.01/1.68  %Foreground operators:
% 4.01/1.68  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 4.01/1.68  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.01/1.68  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 4.01/1.68  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 4.01/1.68  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.01/1.68  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 4.01/1.68  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.01/1.68  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 4.01/1.68  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 4.01/1.68  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 4.01/1.68  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.01/1.68  tff('#skF_2', type, '#skF_2': $i).
% 4.01/1.68  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 4.10/1.68  tff('#skF_3', type, '#skF_3': $i).
% 4.10/1.68  tff('#skF_1', type, '#skF_1': $i).
% 4.10/1.68  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 4.10/1.68  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.10/1.68  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 4.10/1.68  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.10/1.68  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.10/1.68  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.10/1.68  tff('#skF_4', type, '#skF_4': $i).
% 4.10/1.68  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 4.10/1.68  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.10/1.68  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.10/1.68  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.10/1.68  
% 4.10/1.70  tff(f_183, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => ((((k2_relset_1(A, B, C) = B) & r2_relset_1(A, A, k1_partfun1(A, B, B, A, C, D), k6_partfun1(A))) & v2_funct_1(C)) => (((A = k1_xboole_0) | (B = k1_xboole_0)) | (D = k2_funct_1(C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_funct_2)).
% 4.10/1.70  tff(f_34, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 4.10/1.70  tff(f_32, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 4.10/1.70  tff(f_82, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 4.10/1.70  tff(f_112, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 4.10/1.70  tff(f_86, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 4.10/1.70  tff(f_140, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 4.10/1.70  tff(f_70, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (((v2_funct_1(A) & (k2_relat_1(B) = k1_relat_1(A))) & (k5_relat_1(B, A) = k6_relat_1(k2_relat_1(A)))) => (B = k2_funct_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_funct_1)).
% 4.10/1.70  tff(f_128, axiom, (![A]: (v1_partfun1(k6_partfun1(A), A) & m1_subset_1(k6_partfun1(A), k1_zfmisc_1(k2_zfmisc_1(A, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_partfun1)).
% 4.10/1.70  tff(f_94, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 4.10/1.70  tff(f_138, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 4.10/1.70  tff(f_124, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (v1_funct_1(k1_partfun1(A, B, C, D, E, F)) & m1_subset_1(k1_partfun1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 4.10/1.70  tff(f_157, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (r2_relset_1(B, B, k1_partfun1(B, A, A, B, D, C), k6_partfun1(B)) => (k2_relset_1(A, B, C) = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t24_funct_2)).
% 4.10/1.70  tff(f_53, axiom, (![A]: v2_funct_1(k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_funct_1)).
% 4.10/1.70  tff(f_51, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((v2_funct_1(k5_relat_1(B, A)) & (k2_relat_1(B) = k1_relat_1(A))) => (v2_funct_1(B) & v2_funct_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_funct_1)).
% 4.10/1.70  tff(f_78, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => (k2_funct_1(k2_funct_1(A)) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_funct_1)).
% 4.10/1.70  tff(c_50, plain, (k2_funct_1('#skF_3')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_183])).
% 4.10/1.70  tff(c_4, plain, (![A_4, B_5]: (v1_relat_1(k2_zfmisc_1(A_4, B_5)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 4.10/1.70  tff(c_62, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_183])).
% 4.10/1.70  tff(c_92, plain, (![B_53, A_54]: (v1_relat_1(B_53) | ~m1_subset_1(B_53, k1_zfmisc_1(A_54)) | ~v1_relat_1(A_54))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.10/1.70  tff(c_101, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_1'))), inference(resolution, [status(thm)], [c_62, c_92])).
% 4.10/1.70  tff(c_110, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_101])).
% 4.10/1.70  tff(c_66, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_183])).
% 4.10/1.70  tff(c_54, plain, (k1_xboole_0!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_183])).
% 4.10/1.70  tff(c_64, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_183])).
% 4.10/1.70  tff(c_172, plain, (![A_66, B_67, C_68]: (k1_relset_1(A_66, B_67, C_68)=k1_relat_1(C_68) | ~m1_subset_1(C_68, k1_zfmisc_1(k2_zfmisc_1(A_66, B_67))))), inference(cnfTransformation, [status(thm)], [f_82])).
% 4.10/1.70  tff(c_184, plain, (k1_relset_1('#skF_2', '#skF_1', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_62, c_172])).
% 4.10/1.70  tff(c_248, plain, (![B_80, A_81, C_82]: (k1_xboole_0=B_80 | k1_relset_1(A_81, B_80, C_82)=A_81 | ~v1_funct_2(C_82, A_81, B_80) | ~m1_subset_1(C_82, k1_zfmisc_1(k2_zfmisc_1(A_81, B_80))))), inference(cnfTransformation, [status(thm)], [f_112])).
% 4.10/1.70  tff(c_257, plain, (k1_xboole_0='#skF_1' | k1_relset_1('#skF_2', '#skF_1', '#skF_4')='#skF_2' | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_62, c_248])).
% 4.10/1.70  tff(c_266, plain, (k1_xboole_0='#skF_1' | k1_relat_1('#skF_4')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_64, c_184, c_257])).
% 4.10/1.70  tff(c_267, plain, (k1_relat_1('#skF_4')='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_54, c_266])).
% 4.10/1.70  tff(c_68, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_183])).
% 4.10/1.70  tff(c_98, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_68, c_92])).
% 4.10/1.70  tff(c_107, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_98])).
% 4.10/1.70  tff(c_72, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_183])).
% 4.10/1.70  tff(c_56, plain, (v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_183])).
% 4.10/1.70  tff(c_52, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_183])).
% 4.10/1.70  tff(c_70, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_183])).
% 4.10/1.70  tff(c_183, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_68, c_172])).
% 4.10/1.70  tff(c_254, plain, (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_1' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_68, c_248])).
% 4.10/1.70  tff(c_262, plain, (k1_xboole_0='#skF_2' | k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_70, c_183, c_254])).
% 4.10/1.70  tff(c_263, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_52, c_262])).
% 4.10/1.70  tff(c_60, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_2'), inference(cnfTransformation, [status(thm)], [f_183])).
% 4.10/1.70  tff(c_139, plain, (![A_60, B_61, C_62]: (k2_relset_1(A_60, B_61, C_62)=k2_relat_1(C_62) | ~m1_subset_1(C_62, k1_zfmisc_1(k2_zfmisc_1(A_60, B_61))))), inference(cnfTransformation, [status(thm)], [f_86])).
% 4.10/1.70  tff(c_145, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_68, c_139])).
% 4.10/1.70  tff(c_151, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_60, c_145])).
% 4.10/1.70  tff(c_46, plain, (![A_40]: (k6_relat_1(A_40)=k6_partfun1(A_40))), inference(cnfTransformation, [status(thm)], [f_140])).
% 4.10/1.70  tff(c_12, plain, (![A_10, B_12]: (k2_funct_1(A_10)=B_12 | k6_relat_1(k2_relat_1(A_10))!=k5_relat_1(B_12, A_10) | k2_relat_1(B_12)!=k1_relat_1(A_10) | ~v2_funct_1(A_10) | ~v1_funct_1(B_12) | ~v1_relat_1(B_12) | ~v1_funct_1(A_10) | ~v1_relat_1(A_10))), inference(cnfTransformation, [status(thm)], [f_70])).
% 4.10/1.70  tff(c_524, plain, (![A_123, B_124]: (k2_funct_1(A_123)=B_124 | k6_partfun1(k2_relat_1(A_123))!=k5_relat_1(B_124, A_123) | k2_relat_1(B_124)!=k1_relat_1(A_123) | ~v2_funct_1(A_123) | ~v1_funct_1(B_124) | ~v1_relat_1(B_124) | ~v1_funct_1(A_123) | ~v1_relat_1(A_123))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_12])).
% 4.10/1.70  tff(c_526, plain, (![B_124]: (k2_funct_1('#skF_3')=B_124 | k5_relat_1(B_124, '#skF_3')!=k6_partfun1('#skF_2') | k2_relat_1(B_124)!=k1_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_1(B_124) | ~v1_relat_1(B_124) | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_151, c_524])).
% 4.10/1.70  tff(c_529, plain, (![B_125]: (k2_funct_1('#skF_3')=B_125 | k5_relat_1(B_125, '#skF_3')!=k6_partfun1('#skF_2') | k2_relat_1(B_125)!='#skF_1' | ~v1_funct_1(B_125) | ~v1_relat_1(B_125))), inference(demodulation, [status(thm), theory('equality')], [c_107, c_72, c_56, c_263, c_526])).
% 4.10/1.70  tff(c_535, plain, (k2_funct_1('#skF_3')='#skF_4' | k5_relat_1('#skF_4', '#skF_3')!=k6_partfun1('#skF_2') | k2_relat_1('#skF_4')!='#skF_1' | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_110, c_529])).
% 4.10/1.70  tff(c_545, plain, (k2_funct_1('#skF_3')='#skF_4' | k5_relat_1('#skF_4', '#skF_3')!=k6_partfun1('#skF_2') | k2_relat_1('#skF_4')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_66, c_535])).
% 4.10/1.70  tff(c_546, plain, (k5_relat_1('#skF_4', '#skF_3')!=k6_partfun1('#skF_2') | k2_relat_1('#skF_4')!='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_50, c_545])).
% 4.10/1.70  tff(c_551, plain, (k2_relat_1('#skF_4')!='#skF_1'), inference(splitLeft, [status(thm)], [c_546])).
% 4.10/1.70  tff(c_42, plain, (![A_33]: (m1_subset_1(k6_partfun1(A_33), k1_zfmisc_1(k2_zfmisc_1(A_33, A_33))))), inference(cnfTransformation, [status(thm)], [f_128])).
% 4.10/1.70  tff(c_129, plain, (![A_57, B_58, D_59]: (r2_relset_1(A_57, B_58, D_59, D_59) | ~m1_subset_1(D_59, k1_zfmisc_1(k2_zfmisc_1(A_57, B_58))))), inference(cnfTransformation, [status(thm)], [f_94])).
% 4.10/1.70  tff(c_136, plain, (![A_33]: (r2_relset_1(A_33, A_33, k6_partfun1(A_33), k6_partfun1(A_33)))), inference(resolution, [status(thm)], [c_42, c_129])).
% 4.10/1.70  tff(c_152, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_62, c_139])).
% 4.10/1.70  tff(c_379, plain, (![E_108, C_110, A_105, F_107, B_109, D_106]: (k1_partfun1(A_105, B_109, C_110, D_106, E_108, F_107)=k5_relat_1(E_108, F_107) | ~m1_subset_1(F_107, k1_zfmisc_1(k2_zfmisc_1(C_110, D_106))) | ~v1_funct_1(F_107) | ~m1_subset_1(E_108, k1_zfmisc_1(k2_zfmisc_1(A_105, B_109))) | ~v1_funct_1(E_108))), inference(cnfTransformation, [status(thm)], [f_138])).
% 4.10/1.70  tff(c_385, plain, (![A_105, B_109, E_108]: (k1_partfun1(A_105, B_109, '#skF_2', '#skF_1', E_108, '#skF_4')=k5_relat_1(E_108, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_108, k1_zfmisc_1(k2_zfmisc_1(A_105, B_109))) | ~v1_funct_1(E_108))), inference(resolution, [status(thm)], [c_62, c_379])).
% 4.10/1.70  tff(c_410, plain, (![A_114, B_115, E_116]: (k1_partfun1(A_114, B_115, '#skF_2', '#skF_1', E_116, '#skF_4')=k5_relat_1(E_116, '#skF_4') | ~m1_subset_1(E_116, k1_zfmisc_1(k2_zfmisc_1(A_114, B_115))) | ~v1_funct_1(E_116))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_385])).
% 4.10/1.70  tff(c_416, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_68, c_410])).
% 4.10/1.70  tff(c_423, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_416])).
% 4.10/1.70  tff(c_58, plain, (r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k6_partfun1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_183])).
% 4.10/1.70  tff(c_293, plain, (![D_88, C_89, A_90, B_91]: (D_88=C_89 | ~r2_relset_1(A_90, B_91, C_89, D_88) | ~m1_subset_1(D_88, k1_zfmisc_1(k2_zfmisc_1(A_90, B_91))) | ~m1_subset_1(C_89, k1_zfmisc_1(k2_zfmisc_1(A_90, B_91))))), inference(cnfTransformation, [status(thm)], [f_94])).
% 4.10/1.70  tff(c_301, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_58, c_293])).
% 4.10/1.70  tff(c_316, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_301])).
% 4.10/1.70  tff(c_317, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_316])).
% 4.10/1.70  tff(c_428, plain, (~m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_423, c_317])).
% 4.10/1.70  tff(c_444, plain, (![A_122, B_121, F_117, D_119, E_120, C_118]: (m1_subset_1(k1_partfun1(A_122, B_121, C_118, D_119, E_120, F_117), k1_zfmisc_1(k2_zfmisc_1(A_122, D_119))) | ~m1_subset_1(F_117, k1_zfmisc_1(k2_zfmisc_1(C_118, D_119))) | ~v1_funct_1(F_117) | ~m1_subset_1(E_120, k1_zfmisc_1(k2_zfmisc_1(A_122, B_121))) | ~v1_funct_1(E_120))), inference(cnfTransformation, [status(thm)], [f_124])).
% 4.10/1.70  tff(c_492, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_423, c_444])).
% 4.10/1.70  tff(c_512, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_68, c_66, c_62, c_492])).
% 4.10/1.70  tff(c_514, plain, $false, inference(negUnitSimplification, [status(thm)], [c_428, c_512])).
% 4.10/1.70  tff(c_515, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_316])).
% 4.10/1.70  tff(c_883, plain, (![A_157, B_158, C_159, D_160]: (k2_relset_1(A_157, B_158, C_159)=B_158 | ~r2_relset_1(B_158, B_158, k1_partfun1(B_158, A_157, A_157, B_158, D_160, C_159), k6_partfun1(B_158)) | ~m1_subset_1(D_160, k1_zfmisc_1(k2_zfmisc_1(B_158, A_157))) | ~v1_funct_2(D_160, B_158, A_157) | ~v1_funct_1(D_160) | ~m1_subset_1(C_159, k1_zfmisc_1(k2_zfmisc_1(A_157, B_158))) | ~v1_funct_2(C_159, A_157, B_158) | ~v1_funct_1(C_159))), inference(cnfTransformation, [status(thm)], [f_157])).
% 4.10/1.70  tff(c_886, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')='#skF_1' | ~r2_relset_1('#skF_1', '#skF_1', k6_partfun1('#skF_1'), k6_partfun1('#skF_1')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_515, c_883])).
% 4.10/1.70  tff(c_888, plain, (k2_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_62, c_72, c_70, c_68, c_136, c_152, c_886])).
% 4.10/1.70  tff(c_890, plain, $false, inference(negUnitSimplification, [status(thm)], [c_551, c_888])).
% 4.10/1.70  tff(c_892, plain, (k2_relat_1('#skF_4')='#skF_1'), inference(splitRight, [status(thm)], [c_546])).
% 4.10/1.70  tff(c_73, plain, (![A_10, B_12]: (k2_funct_1(A_10)=B_12 | k6_partfun1(k2_relat_1(A_10))!=k5_relat_1(B_12, A_10) | k2_relat_1(B_12)!=k1_relat_1(A_10) | ~v2_funct_1(A_10) | ~v1_funct_1(B_12) | ~v1_relat_1(B_12) | ~v1_funct_1(A_10) | ~v1_relat_1(A_10))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_12])).
% 4.10/1.70  tff(c_896, plain, (![B_12]: (k2_funct_1('#skF_4')=B_12 | k5_relat_1(B_12, '#skF_4')!=k6_partfun1('#skF_1') | k2_relat_1(B_12)!=k1_relat_1('#skF_4') | ~v2_funct_1('#skF_4') | ~v1_funct_1(B_12) | ~v1_relat_1(B_12) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_892, c_73])).
% 4.10/1.70  tff(c_900, plain, (![B_12]: (k2_funct_1('#skF_4')=B_12 | k5_relat_1(B_12, '#skF_4')!=k6_partfun1('#skF_1') | k2_relat_1(B_12)!='#skF_2' | ~v2_funct_1('#skF_4') | ~v1_funct_1(B_12) | ~v1_relat_1(B_12))), inference(demodulation, [status(thm), theory('equality')], [c_110, c_66, c_267, c_896])).
% 4.10/1.70  tff(c_908, plain, (~v2_funct_1('#skF_4')), inference(splitLeft, [status(thm)], [c_900])).
% 4.10/1.70  tff(c_10, plain, (![A_9]: (v2_funct_1(k6_relat_1(A_9)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 4.10/1.70  tff(c_74, plain, (![A_9]: (v2_funct_1(k6_partfun1(A_9)))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_10])).
% 4.10/1.70  tff(c_965, plain, (![A_178, D_179, E_181, F_180, C_183, B_182]: (k1_partfun1(A_178, B_182, C_183, D_179, E_181, F_180)=k5_relat_1(E_181, F_180) | ~m1_subset_1(F_180, k1_zfmisc_1(k2_zfmisc_1(C_183, D_179))) | ~v1_funct_1(F_180) | ~m1_subset_1(E_181, k1_zfmisc_1(k2_zfmisc_1(A_178, B_182))) | ~v1_funct_1(E_181))), inference(cnfTransformation, [status(thm)], [f_138])).
% 4.10/1.70  tff(c_971, plain, (![A_178, B_182, E_181]: (k1_partfun1(A_178, B_182, '#skF_2', '#skF_1', E_181, '#skF_4')=k5_relat_1(E_181, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_181, k1_zfmisc_1(k2_zfmisc_1(A_178, B_182))) | ~v1_funct_1(E_181))), inference(resolution, [status(thm)], [c_62, c_965])).
% 4.10/1.70  tff(c_979, plain, (![A_184, B_185, E_186]: (k1_partfun1(A_184, B_185, '#skF_2', '#skF_1', E_186, '#skF_4')=k5_relat_1(E_186, '#skF_4') | ~m1_subset_1(E_186, k1_zfmisc_1(k2_zfmisc_1(A_184, B_185))) | ~v1_funct_1(E_186))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_971])).
% 4.10/1.70  tff(c_985, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_68, c_979])).
% 4.10/1.70  tff(c_992, plain, (k5_relat_1('#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_515, c_985])).
% 4.10/1.70  tff(c_6, plain, (![A_6, B_8]: (v2_funct_1(A_6) | k2_relat_1(B_8)!=k1_relat_1(A_6) | ~v2_funct_1(k5_relat_1(B_8, A_6)) | ~v1_funct_1(B_8) | ~v1_relat_1(B_8) | ~v1_funct_1(A_6) | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_51])).
% 4.10/1.70  tff(c_999, plain, (v2_funct_1('#skF_4') | k2_relat_1('#skF_3')!=k1_relat_1('#skF_4') | ~v2_funct_1(k6_partfun1('#skF_1')) | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_992, c_6])).
% 4.10/1.70  tff(c_1006, plain, (v2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_110, c_66, c_107, c_72, c_74, c_151, c_267, c_999])).
% 4.10/1.70  tff(c_1008, plain, $false, inference(negUnitSimplification, [status(thm)], [c_908, c_1006])).
% 4.10/1.70  tff(c_1010, plain, (v2_funct_1('#skF_4')), inference(splitRight, [status(thm)], [c_900])).
% 4.10/1.70  tff(c_1011, plain, (![B_187]: (k2_funct_1('#skF_4')=B_187 | k5_relat_1(B_187, '#skF_4')!=k6_partfun1('#skF_1') | k2_relat_1(B_187)!='#skF_2' | ~v1_funct_1(B_187) | ~v1_relat_1(B_187))), inference(splitRight, [status(thm)], [c_900])).
% 4.10/1.70  tff(c_1020, plain, (k2_funct_1('#skF_4')='#skF_3' | k5_relat_1('#skF_3', '#skF_4')!=k6_partfun1('#skF_1') | k2_relat_1('#skF_3')!='#skF_2' | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_107, c_1011])).
% 4.10/1.70  tff(c_1030, plain, (k2_funct_1('#skF_4')='#skF_3' | k5_relat_1('#skF_3', '#skF_4')!=k6_partfun1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_151, c_1020])).
% 4.10/1.70  tff(c_1032, plain, (k5_relat_1('#skF_3', '#skF_4')!=k6_partfun1('#skF_1')), inference(splitLeft, [status(thm)], [c_1030])).
% 4.10/1.70  tff(c_1094, plain, (![B_209, C_210, A_205, F_207, E_208, D_206]: (k1_partfun1(A_205, B_209, C_210, D_206, E_208, F_207)=k5_relat_1(E_208, F_207) | ~m1_subset_1(F_207, k1_zfmisc_1(k2_zfmisc_1(C_210, D_206))) | ~v1_funct_1(F_207) | ~m1_subset_1(E_208, k1_zfmisc_1(k2_zfmisc_1(A_205, B_209))) | ~v1_funct_1(E_208))), inference(cnfTransformation, [status(thm)], [f_138])).
% 4.10/1.70  tff(c_1100, plain, (![A_205, B_209, E_208]: (k1_partfun1(A_205, B_209, '#skF_2', '#skF_1', E_208, '#skF_4')=k5_relat_1(E_208, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_208, k1_zfmisc_1(k2_zfmisc_1(A_205, B_209))) | ~v1_funct_1(E_208))), inference(resolution, [status(thm)], [c_62, c_1094])).
% 4.10/1.70  tff(c_1394, plain, (![A_225, B_226, E_227]: (k1_partfun1(A_225, B_226, '#skF_2', '#skF_1', E_227, '#skF_4')=k5_relat_1(E_227, '#skF_4') | ~m1_subset_1(E_227, k1_zfmisc_1(k2_zfmisc_1(A_225, B_226))) | ~v1_funct_1(E_227))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_1100])).
% 4.10/1.70  tff(c_1409, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_68, c_1394])).
% 4.10/1.70  tff(c_1423, plain, (k5_relat_1('#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_515, c_1409])).
% 4.10/1.70  tff(c_1425, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1032, c_1423])).
% 4.10/1.70  tff(c_1426, plain, (k2_funct_1('#skF_4')='#skF_3'), inference(splitRight, [status(thm)], [c_1030])).
% 4.10/1.70  tff(c_14, plain, (![A_13]: (k2_funct_1(k2_funct_1(A_13))=A_13 | ~v2_funct_1(A_13) | ~v1_funct_1(A_13) | ~v1_relat_1(A_13))), inference(cnfTransformation, [status(thm)], [f_78])).
% 4.10/1.70  tff(c_1432, plain, (k2_funct_1('#skF_3')='#skF_4' | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1426, c_14])).
% 4.10/1.70  tff(c_1436, plain, (k2_funct_1('#skF_3')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_110, c_66, c_1010, c_1432])).
% 4.10/1.70  tff(c_1438, plain, $false, inference(negUnitSimplification, [status(thm)], [c_50, c_1436])).
% 4.10/1.70  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.10/1.70  
% 4.10/1.70  Inference rules
% 4.10/1.70  ----------------------
% 4.10/1.70  #Ref     : 0
% 4.10/1.70  #Sup     : 289
% 4.10/1.70  #Fact    : 0
% 4.10/1.70  #Define  : 0
% 4.10/1.70  #Split   : 16
% 4.10/1.70  #Chain   : 0
% 4.10/1.70  #Close   : 0
% 4.10/1.70  
% 4.10/1.70  Ordering : KBO
% 4.10/1.70  
% 4.10/1.70  Simplification rules
% 4.10/1.70  ----------------------
% 4.10/1.70  #Subsume      : 2
% 4.10/1.70  #Demod        : 228
% 4.10/1.70  #Tautology    : 77
% 4.10/1.70  #SimpNegUnit  : 20
% 4.10/1.70  #BackRed      : 12
% 4.10/1.70  
% 4.10/1.70  #Partial instantiations: 0
% 4.10/1.70  #Strategies tried      : 1
% 4.10/1.70  
% 4.10/1.70  Timing (in seconds)
% 4.10/1.70  ----------------------
% 4.10/1.71  Preprocessing        : 0.36
% 4.10/1.71  Parsing              : 0.19
% 4.10/1.71  CNF conversion       : 0.02
% 4.10/1.71  Main loop            : 0.55
% 4.10/1.71  Inferencing          : 0.19
% 4.10/1.71  Reduction            : 0.19
% 4.10/1.71  Demodulation         : 0.13
% 4.10/1.71  BG Simplification    : 0.03
% 4.10/1.71  Subsumption          : 0.09
% 4.10/1.71  Abstraction          : 0.03
% 4.10/1.71  MUC search           : 0.00
% 4.10/1.71  Cooper               : 0.00
% 4.10/1.71  Total                : 0.97
% 4.10/1.71  Index Insertion      : 0.00
% 4.10/1.71  Index Deletion       : 0.00
% 4.10/1.71  Index Matching       : 0.00
% 4.10/1.71  BG Taut test         : 0.00
%------------------------------------------------------------------------------
