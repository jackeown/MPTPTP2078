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
% DateTime   : Thu Dec  3 10:15:54 EST 2020

% Result     : Theorem 8.22s
% Output     : CNFRefutation 8.22s
% Verified   : 
% Statistics : Number of formulae       :  218 (5066 expanded)
%              Number of leaves         :   47 (1657 expanded)
%              Depth                    :   18
%              Number of atoms          :  449 (12445 expanded)
%              Number of equality atoms :  147 (4737 expanded)
%              Maximal formula depth    :   17 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v3_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k8_relat_1 > k5_relat_1 > k2_zfmisc_1 > k2_funct_2 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(k8_relat_1,type,(
    k8_relat_1: ( $i * $i ) > $i )).

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

tff(k2_funct_2,type,(
    k2_funct_2: ( $i * $i ) > $i )).

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

tff(v2_funct_2,type,(
    v2_funct_2: ( $i * $i ) > $o )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

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

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(v3_funct_2,type,(
    v3_funct_2: ( $i * $i * $i ) > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_214,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_funct_1(B)
          & v1_funct_2(B,A,A)
          & v3_funct_2(B,A,A)
          & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
       => ! [C] :
            ( ( v1_funct_1(C)
              & v1_funct_2(C,A,A)
              & v3_funct_2(C,A,A)
              & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
           => ( r2_relset_1(A,A,k1_partfun1(A,A,A,A,B,C),k6_partfun1(A))
             => r2_relset_1(A,A,C,k2_funct_2(A,B)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_funct_2)).

tff(f_102,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_148,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_45,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_50,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v2_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_funct_1)).

tff(f_41,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ( k1_relat_1(A) = k1_xboole_0
          | k2_relat_1(A) = k1_xboole_0 )
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).

tff(f_84,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_90,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_124,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A) )
     => ( v2_funct_2(B,A)
      <=> k2_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_funct_2)).

tff(f_116,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( ( v1_funct_1(C)
          & v3_funct_2(C,A,B) )
       => ( v1_funct_1(C)
          & v2_funct_1(C)
          & v2_funct_2(C,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_funct_2)).

tff(f_94,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_104,axiom,(
    ! [A] : m1_subset_1(k6_relat_1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_relset_1)).

tff(f_136,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( v1_funct_1(k1_partfun1(A,B,C,D,E,F))
        & m1_subset_1(k1_partfun1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).

tff(f_192,axiom,(
    ! [A,B,C] :
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

tff(f_146,axiom,(
    ! [A,B] :
      ( ( v1_funct_1(B)
        & v1_funct_2(B,A,A)
        & v3_funct_2(B,A,A)
        & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
     => k2_funct_2(A,B) = k2_funct_1(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_funct_2)).

tff(f_33,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k8_relat_1(k2_relat_1(A),A) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t126_relat_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k8_relat_1(A,B) = k5_relat_1(B,k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t123_relat_1)).

tff(f_80,axiom,(
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

tff(c_66,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_214])).

tff(c_399,plain,(
    ! [A_82,B_83,D_84] :
      ( r2_relset_1(A_82,B_83,D_84,D_84)
      | ~ m1_subset_1(D_84,k1_zfmisc_1(k2_zfmisc_1(A_82,B_83))) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_410,plain,(
    r2_relset_1('#skF_1','#skF_1','#skF_3','#skF_3') ),
    inference(resolution,[status(thm)],[c_66,c_399])).

tff(c_54,plain,(
    ! [A_40] : k6_relat_1(A_40) = k6_partfun1(A_40) ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_10,plain,(
    ! [A_5] : k1_relat_1(k6_relat_1(A_5)) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_87,plain,(
    ! [A_5] : k1_relat_1(k6_partfun1(A_5)) = A_5 ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_10])).

tff(c_16,plain,(
    ! [A_6] : v1_relat_1(k6_relat_1(A_6)) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_85,plain,(
    ! [A_6] : v1_relat_1(k6_partfun1(A_6)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_16])).

tff(c_151,plain,(
    ! [A_57] :
      ( k1_relat_1(A_57) != k1_xboole_0
      | k1_xboole_0 = A_57
      | ~ v1_relat_1(A_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_157,plain,(
    ! [A_6] :
      ( k1_relat_1(k6_partfun1(A_6)) != k1_xboole_0
      | k6_partfun1(A_6) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_85,c_151])).

tff(c_163,plain,(
    ! [A_6] :
      ( k1_xboole_0 != A_6
      | k6_partfun1(A_6) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_87,c_157])).

tff(c_64,plain,(
    r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2','#skF_3'),k6_partfun1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_214])).

tff(c_275,plain,
    ( r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2','#skF_3'),k1_xboole_0)
    | k1_xboole_0 != '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_163,c_64])).

tff(c_321,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_275])).

tff(c_80,plain,(
    v1_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_214])).

tff(c_78,plain,(
    v1_funct_2('#skF_2','#skF_1','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_214])).

tff(c_74,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_214])).

tff(c_72,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_214])).

tff(c_70,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_214])).

tff(c_276,plain,(
    ! [C_64,A_65,B_66] :
      ( v1_relat_1(C_64)
      | ~ m1_subset_1(C_64,k1_zfmisc_1(k2_zfmisc_1(A_65,B_66))) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_289,plain,(
    v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_74,c_276])).

tff(c_351,plain,(
    ! [C_74,B_75,A_76] :
      ( v5_relat_1(C_74,B_75)
      | ~ m1_subset_1(C_74,k1_zfmisc_1(k2_zfmisc_1(A_76,B_75))) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_367,plain,(
    v5_relat_1('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_74,c_351])).

tff(c_415,plain,(
    ! [B_86,A_87] :
      ( k2_relat_1(B_86) = A_87
      | ~ v2_funct_2(B_86,A_87)
      | ~ v5_relat_1(B_86,A_87)
      | ~ v1_relat_1(B_86) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_424,plain,
    ( k2_relat_1('#skF_2') = '#skF_1'
    | ~ v2_funct_2('#skF_2','#skF_1')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_367,c_415])).

tff(c_436,plain,
    ( k2_relat_1('#skF_2') = '#skF_1'
    | ~ v2_funct_2('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_289,c_424])).

tff(c_440,plain,(
    ~ v2_funct_2('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_436])).

tff(c_76,plain,(
    v3_funct_2('#skF_2','#skF_1','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_214])).

tff(c_789,plain,(
    ! [C_120,B_121,A_122] :
      ( v2_funct_2(C_120,B_121)
      | ~ v3_funct_2(C_120,A_122,B_121)
      | ~ v1_funct_1(C_120)
      | ~ m1_subset_1(C_120,k1_zfmisc_1(k2_zfmisc_1(A_122,B_121))) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_801,plain,
    ( v2_funct_2('#skF_2','#skF_1')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_74,c_789])).

tff(c_810,plain,(
    v2_funct_2('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_76,c_801])).

tff(c_812,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_440,c_810])).

tff(c_813,plain,(
    k2_relat_1('#skF_2') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_436])).

tff(c_1008,plain,(
    ! [A_143,B_144,C_145] :
      ( k2_relset_1(A_143,B_144,C_145) = k2_relat_1(C_145)
      | ~ m1_subset_1(C_145,k1_zfmisc_1(k2_zfmisc_1(A_143,B_144))) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_1020,plain,(
    k2_relset_1('#skF_1','#skF_1','#skF_2') = k2_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_74,c_1008])).

tff(c_1028,plain,(
    k2_relset_1('#skF_1','#skF_1','#skF_2') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_813,c_1020])).

tff(c_36,plain,(
    ! [A_26] : m1_subset_1(k6_relat_1(A_26),k1_zfmisc_1(k2_zfmisc_1(A_26,A_26))) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_81,plain,(
    ! [A_26] : m1_subset_1(k6_partfun1(A_26),k1_zfmisc_1(k2_zfmisc_1(A_26,A_26))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_36])).

tff(c_409,plain,(
    ! [A_26] : r2_relset_1(A_26,A_26,k6_partfun1(A_26),k6_partfun1(A_26)) ),
    inference(resolution,[status(thm)],[c_81,c_399])).

tff(c_1049,plain,(
    ! [C_147,A_148,B_149] :
      ( v2_funct_1(C_147)
      | ~ v3_funct_2(C_147,A_148,B_149)
      | ~ v1_funct_1(C_147)
      | ~ m1_subset_1(C_147,k1_zfmisc_1(k2_zfmisc_1(A_148,B_149))) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_1061,plain,
    ( v2_funct_1('#skF_2')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_74,c_1049])).

tff(c_1071,plain,(
    v2_funct_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_76,c_1061])).

tff(c_1958,plain,(
    ! [B_208,C_210,D_212,E_207,F_209,A_211] :
      ( m1_subset_1(k1_partfun1(A_211,B_208,C_210,D_212,E_207,F_209),k1_zfmisc_1(k2_zfmisc_1(A_211,D_212)))
      | ~ m1_subset_1(F_209,k1_zfmisc_1(k2_zfmisc_1(C_210,D_212)))
      | ~ v1_funct_1(F_209)
      | ~ m1_subset_1(E_207,k1_zfmisc_1(k2_zfmisc_1(A_211,B_208)))
      | ~ v1_funct_1(E_207) ) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_1328,plain,(
    ! [D_166,C_167,A_168,B_169] :
      ( D_166 = C_167
      | ~ r2_relset_1(A_168,B_169,C_167,D_166)
      | ~ m1_subset_1(D_166,k1_zfmisc_1(k2_zfmisc_1(A_168,B_169)))
      | ~ m1_subset_1(C_167,k1_zfmisc_1(k2_zfmisc_1(A_168,B_169))) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_1342,plain,
    ( k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2','#skF_3') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_64,c_1328])).

tff(c_1365,plain,
    ( k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2','#skF_3') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_81,c_1342])).

tff(c_1470,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_1365])).

tff(c_1966,plain,
    ( ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ v1_funct_1('#skF_3')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_1958,c_1470])).

tff(c_1996,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_74,c_72,c_66,c_1966])).

tff(c_1997,plain,(
    k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2','#skF_3') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_1365])).

tff(c_3026,plain,(
    ! [C_275,D_276,B_277,A_278] :
      ( k2_funct_1(C_275) = D_276
      | k1_xboole_0 = B_277
      | k1_xboole_0 = A_278
      | ~ v2_funct_1(C_275)
      | ~ r2_relset_1(A_278,A_278,k1_partfun1(A_278,B_277,B_277,A_278,C_275,D_276),k6_partfun1(A_278))
      | k2_relset_1(A_278,B_277,C_275) != B_277
      | ~ m1_subset_1(D_276,k1_zfmisc_1(k2_zfmisc_1(B_277,A_278)))
      | ~ v1_funct_2(D_276,B_277,A_278)
      | ~ v1_funct_1(D_276)
      | ~ m1_subset_1(C_275,k1_zfmisc_1(k2_zfmisc_1(A_278,B_277)))
      | ~ v1_funct_2(C_275,A_278,B_277)
      | ~ v1_funct_1(C_275) ) ),
    inference(cnfTransformation,[status(thm)],[f_192])).

tff(c_3041,plain,
    ( k2_funct_1('#skF_2') = '#skF_3'
    | k1_xboole_0 = '#skF_1'
    | k1_xboole_0 = '#skF_1'
    | ~ v2_funct_1('#skF_2')
    | ~ r2_relset_1('#skF_1','#skF_1',k6_partfun1('#skF_1'),k6_partfun1('#skF_1'))
    | k2_relset_1('#skF_1','#skF_1','#skF_2') != '#skF_1'
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_3')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_1997,c_3026])).

tff(c_3046,plain,
    ( k2_funct_1('#skF_2') = '#skF_3'
    | k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_78,c_74,c_72,c_70,c_66,c_1028,c_409,c_1071,c_3041])).

tff(c_3047,plain,(
    k2_funct_1('#skF_2') = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_321,c_3046])).

tff(c_1440,plain,(
    ! [A_173,B_174] :
      ( k2_funct_2(A_173,B_174) = k2_funct_1(B_174)
      | ~ m1_subset_1(B_174,k1_zfmisc_1(k2_zfmisc_1(A_173,A_173)))
      | ~ v3_funct_2(B_174,A_173,A_173)
      | ~ v1_funct_2(B_174,A_173,A_173)
      | ~ v1_funct_1(B_174) ) ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_1452,plain,
    ( k2_funct_2('#skF_1','#skF_2') = k2_funct_1('#skF_2')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_74,c_1440])).

tff(c_1460,plain,(
    k2_funct_2('#skF_1','#skF_2') = k2_funct_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_78,c_76,c_1452])).

tff(c_62,plain,(
    ~ r2_relset_1('#skF_1','#skF_1','#skF_3',k2_funct_2('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_214])).

tff(c_1465,plain,(
    ~ r2_relset_1('#skF_1','#skF_1','#skF_3',k2_funct_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1460,c_62])).

tff(c_3048,plain,(
    ~ r2_relset_1('#skF_1','#skF_1','#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3047,c_1465])).

tff(c_3052,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_410,c_3048])).

tff(c_3054,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_275])).

tff(c_288,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_66,c_276])).

tff(c_6,plain,(
    ! [A_4] :
      ( k2_relat_1(A_4) != k1_xboole_0
      | k1_xboole_0 = A_4
      | ~ v1_relat_1(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_296,plain,
    ( k2_relat_1('#skF_3') != k1_xboole_0
    | k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_288,c_6])).

tff(c_306,plain,(
    k2_relat_1('#skF_3') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_296])).

tff(c_3056,plain,(
    k2_relat_1('#skF_3') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3054,c_306])).

tff(c_3146,plain,(
    ! [C_283,B_284,A_285] :
      ( v5_relat_1(C_283,B_284)
      | ~ m1_subset_1(C_283,k1_zfmisc_1(k2_zfmisc_1(A_285,B_284))) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_3157,plain,(
    v5_relat_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_66,c_3146])).

tff(c_3230,plain,(
    ! [B_292,A_293] :
      ( k2_relat_1(B_292) = A_293
      | ~ v2_funct_2(B_292,A_293)
      | ~ v5_relat_1(B_292,A_293)
      | ~ v1_relat_1(B_292) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_3242,plain,
    ( k2_relat_1('#skF_3') = '#skF_1'
    | ~ v2_funct_2('#skF_3','#skF_1')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_3157,c_3230])).

tff(c_3255,plain,
    ( k2_relat_1('#skF_3') = '#skF_1'
    | ~ v2_funct_2('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_288,c_3242])).

tff(c_3256,plain,(
    ~ v2_funct_2('#skF_3','#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_3056,c_3255])).

tff(c_68,plain,(
    v3_funct_2('#skF_3','#skF_1','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_214])).

tff(c_3362,plain,(
    ! [C_303,B_304,A_305] :
      ( v2_funct_2(C_303,B_304)
      | ~ v3_funct_2(C_303,A_305,B_304)
      | ~ v1_funct_1(C_303)
      | ~ m1_subset_1(C_303,k1_zfmisc_1(k2_zfmisc_1(A_305,B_304))) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_3371,plain,
    ( v2_funct_2('#skF_3','#skF_1')
    | ~ v3_funct_2('#skF_3','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_66,c_3362])).

tff(c_3380,plain,(
    v2_funct_2('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_68,c_3371])).

tff(c_3382,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3256,c_3380])).

tff(c_3383,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_296])).

tff(c_3410,plain,
    ( r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2','#skF_3'),'#skF_3')
    | '#skF_3' != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3383,c_3383,c_275])).

tff(c_3411,plain,(
    '#skF_3' != '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_3410])).

tff(c_3384,plain,(
    k2_relat_1('#skF_3') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_296])).

tff(c_3400,plain,(
    k2_relat_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3383,c_3384])).

tff(c_3596,plain,(
    ! [C_316,B_317,A_318] :
      ( v5_relat_1(C_316,B_317)
      | ~ m1_subset_1(C_316,k1_zfmisc_1(k2_zfmisc_1(A_318,B_317))) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_3611,plain,(
    v5_relat_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_66,c_3596])).

tff(c_3655,plain,(
    ! [B_323,A_324] :
      ( k2_relat_1(B_323) = A_324
      | ~ v2_funct_2(B_323,A_324)
      | ~ v5_relat_1(B_323,A_324)
      | ~ v1_relat_1(B_323) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_3667,plain,
    ( k2_relat_1('#skF_3') = '#skF_1'
    | ~ v2_funct_2('#skF_3','#skF_1')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_3611,c_3655])).

tff(c_3679,plain,
    ( '#skF_3' = '#skF_1'
    | ~ v2_funct_2('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_288,c_3400,c_3667])).

tff(c_3680,plain,(
    ~ v2_funct_2('#skF_3','#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_3411,c_3679])).

tff(c_3857,plain,(
    ! [C_343,B_344,A_345] :
      ( v2_funct_2(C_343,B_344)
      | ~ v3_funct_2(C_343,A_345,B_344)
      | ~ v1_funct_1(C_343)
      | ~ m1_subset_1(C_343,k1_zfmisc_1(k2_zfmisc_1(A_345,B_344))) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_3866,plain,
    ( v2_funct_2('#skF_3','#skF_1')
    | ~ v3_funct_2('#skF_3','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_66,c_3857])).

tff(c_3877,plain,(
    v2_funct_2('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_68,c_3866])).

tff(c_3879,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3680,c_3877])).

tff(c_3881,plain,(
    '#skF_3' = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_3410])).

tff(c_3884,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3881,c_3383])).

tff(c_189,plain,(
    ! [A_59] : m1_subset_1(k6_partfun1(A_59),k1_zfmisc_1(k2_zfmisc_1(A_59,A_59))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_36])).

tff(c_192,plain,(
    ! [A_6] :
      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(A_6,A_6)))
      | k1_xboole_0 != A_6 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_163,c_189])).

tff(c_4547,plain,(
    ! [A_6] :
      ( m1_subset_1('#skF_1',k1_zfmisc_1(k2_zfmisc_1(A_6,A_6)))
      | A_6 != '#skF_1' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3884,c_3884,c_192])).

tff(c_4574,plain,(
    ! [A_405,B_406,D_407] :
      ( r2_relset_1(A_405,B_406,D_407,D_407)
      | ~ m1_subset_1(D_407,k1_zfmisc_1(k2_zfmisc_1(A_405,B_406))) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_4592,plain,(
    r2_relset_1('#skF_1','#skF_1','#skF_1','#skF_1') ),
    inference(resolution,[status(thm)],[c_4547,c_4574])).

tff(c_3891,plain,(
    v1_funct_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3881,c_72])).

tff(c_4548,plain,(
    m1_subset_1('#skF_1',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3884,c_3884,c_192])).

tff(c_5716,plain,(
    ! [E_476,F_478,C_479,D_481,B_477,A_480] :
      ( m1_subset_1(k1_partfun1(A_480,B_477,C_479,D_481,E_476,F_478),k1_zfmisc_1(k2_zfmisc_1(A_480,D_481)))
      | ~ m1_subset_1(F_478,k1_zfmisc_1(k2_zfmisc_1(C_479,D_481)))
      | ~ v1_funct_1(F_478)
      | ~ m1_subset_1(E_476,k1_zfmisc_1(k2_zfmisc_1(A_480,B_477)))
      | ~ v1_funct_1(E_476) ) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_3388,plain,(
    ! [A_6] :
      ( A_6 != '#skF_3'
      | k6_partfun1(A_6) = '#skF_3' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3383,c_3383,c_163])).

tff(c_4399,plain,(
    k6_partfun1('#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3881,c_3881,c_3388])).

tff(c_304,plain,
    ( k2_relat_1('#skF_2') != k1_xboole_0
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_289,c_6])).

tff(c_3984,plain,
    ( k2_relat_1('#skF_2') != '#skF_1'
    | '#skF_2' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3884,c_3884,c_304])).

tff(c_3985,plain,(
    k2_relat_1('#skF_2') != '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_3984])).

tff(c_3988,plain,(
    ! [C_352,B_353,A_354] :
      ( v5_relat_1(C_352,B_353)
      | ~ m1_subset_1(C_352,k1_zfmisc_1(k2_zfmisc_1(A_354,B_353))) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_4000,plain,(
    v5_relat_1('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_74,c_3988])).

tff(c_4215,plain,(
    ! [B_372,A_373] :
      ( k2_relat_1(B_372) = A_373
      | ~ v2_funct_2(B_372,A_373)
      | ~ v5_relat_1(B_372,A_373)
      | ~ v1_relat_1(B_372) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_4224,plain,
    ( k2_relat_1('#skF_2') = '#skF_1'
    | ~ v2_funct_2('#skF_2','#skF_1')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_4000,c_4215])).

tff(c_4233,plain,
    ( k2_relat_1('#skF_2') = '#skF_1'
    | ~ v2_funct_2('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_289,c_4224])).

tff(c_4234,plain,(
    ~ v2_funct_2('#skF_2','#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_3985,c_4233])).

tff(c_4357,plain,(
    ! [C_387,B_388,A_389] :
      ( v2_funct_2(C_387,B_388)
      | ~ v3_funct_2(C_387,A_389,B_388)
      | ~ v1_funct_1(C_387)
      | ~ m1_subset_1(C_387,k1_zfmisc_1(k2_zfmisc_1(A_389,B_388))) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_4366,plain,
    ( v2_funct_2('#skF_2','#skF_1')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_74,c_4357])).

tff(c_4374,plain,(
    v2_funct_2('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_76,c_4366])).

tff(c_4376,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4234,c_4374])).

tff(c_4377,plain,(
    '#skF_2' = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_3984])).

tff(c_3886,plain,(
    r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2','#skF_1'),k6_partfun1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3881,c_64])).

tff(c_4543,plain,(
    r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_1','#skF_1'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4399,c_4377,c_3886])).

tff(c_5096,plain,(
    ! [D_444,C_445,A_446,B_447] :
      ( D_444 = C_445
      | ~ r2_relset_1(A_446,B_447,C_445,D_444)
      | ~ m1_subset_1(D_444,k1_zfmisc_1(k2_zfmisc_1(A_446,B_447)))
      | ~ m1_subset_1(C_445,k1_zfmisc_1(k2_zfmisc_1(A_446,B_447))) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_5106,plain,
    ( k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_1','#skF_1') = '#skF_1'
    | ~ m1_subset_1('#skF_1',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_1','#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_4543,c_5096])).

tff(c_5121,plain,
    ( k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_1','#skF_1') = '#skF_1'
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_1','#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4548,c_5106])).

tff(c_5273,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_1','#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_5121])).

tff(c_5721,plain,
    ( ~ m1_subset_1('#skF_1',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ v1_funct_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_5716,c_5273])).

tff(c_5750,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3891,c_4548,c_5721])).

tff(c_5751,plain,(
    k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_1','#skF_1') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_5121])).

tff(c_3889,plain,(
    v1_funct_2('#skF_1','#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3881,c_70])).

tff(c_3890,plain,(
    v3_funct_2('#skF_1','#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3881,c_68])).

tff(c_4398,plain,(
    ! [A_6] :
      ( A_6 != '#skF_1'
      | k6_partfun1(A_6) = '#skF_1' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3881,c_3881,c_3388])).

tff(c_12,plain,(
    ! [A_5] : k2_relat_1(k6_relat_1(A_5)) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_86,plain,(
    ! [A_5] : k2_relat_1(k6_partfun1(A_5)) = A_5 ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_12])).

tff(c_193,plain,(
    ! [A_60] :
      ( k8_relat_1(k2_relat_1(A_60),A_60) = A_60
      | ~ v1_relat_1(A_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_205,plain,(
    ! [A_5] :
      ( k8_relat_1(A_5,k6_partfun1(A_5)) = k6_partfun1(A_5)
      | ~ v1_relat_1(k6_partfun1(A_5)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_86,c_193])).

tff(c_211,plain,(
    ! [A_5] : k8_relat_1(A_5,k6_partfun1(A_5)) = k6_partfun1(A_5) ),
    inference(demodulation,[status(thm),theory(equality)],[c_85,c_205])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( k5_relat_1(B_2,k6_relat_1(A_1)) = k8_relat_1(A_1,B_2)
      | ~ v1_relat_1(B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_88,plain,(
    ! [B_2,A_1] :
      ( k5_relat_1(B_2,k6_partfun1(A_1)) = k8_relat_1(A_1,B_2)
      | ~ v1_relat_1(B_2) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_2])).

tff(c_18,plain,(
    ! [A_6] : v2_funct_1(k6_relat_1(A_6)) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_84,plain,(
    ! [A_6] : v2_funct_1(k6_partfun1(A_6)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_18])).

tff(c_22,plain,(
    ! [A_10,B_12] :
      ( k2_funct_1(A_10) = B_12
      | k6_relat_1(k1_relat_1(A_10)) != k5_relat_1(A_10,B_12)
      | k2_relat_1(A_10) != k1_relat_1(B_12)
      | ~ v2_funct_1(A_10)
      | ~ v1_funct_1(B_12)
      | ~ v1_relat_1(B_12)
      | ~ v1_funct_1(A_10)
      | ~ v1_relat_1(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_5951,plain,(
    ! [A_486,B_487] :
      ( k2_funct_1(A_486) = B_487
      | k6_partfun1(k1_relat_1(A_486)) != k5_relat_1(A_486,B_487)
      | k2_relat_1(A_486) != k1_relat_1(B_487)
      | ~ v2_funct_1(A_486)
      | ~ v1_funct_1(B_487)
      | ~ v1_relat_1(B_487)
      | ~ v1_funct_1(A_486)
      | ~ v1_relat_1(A_486) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_22])).

tff(c_5968,plain,(
    ! [A_5,B_487] :
      ( k2_funct_1(k6_partfun1(A_5)) = B_487
      | k5_relat_1(k6_partfun1(A_5),B_487) != k6_partfun1(A_5)
      | k2_relat_1(k6_partfun1(A_5)) != k1_relat_1(B_487)
      | ~ v2_funct_1(k6_partfun1(A_5))
      | ~ v1_funct_1(B_487)
      | ~ v1_relat_1(B_487)
      | ~ v1_funct_1(k6_partfun1(A_5))
      | ~ v1_relat_1(k6_partfun1(A_5)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_87,c_5951])).

tff(c_7072,plain,(
    ! [A_557,B_558] :
      ( k2_funct_1(k6_partfun1(A_557)) = B_558
      | k5_relat_1(k6_partfun1(A_557),B_558) != k6_partfun1(A_557)
      | k1_relat_1(B_558) != A_557
      | ~ v1_funct_1(B_558)
      | ~ v1_relat_1(B_558)
      | ~ v1_funct_1(k6_partfun1(A_557)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_85,c_84,c_86,c_5968])).

tff(c_7093,plain,(
    ! [A_1,A_557] :
      ( k6_partfun1(A_1) = k2_funct_1(k6_partfun1(A_557))
      | k8_relat_1(A_1,k6_partfun1(A_557)) != k6_partfun1(A_557)
      | k1_relat_1(k6_partfun1(A_1)) != A_557
      | ~ v1_funct_1(k6_partfun1(A_1))
      | ~ v1_relat_1(k6_partfun1(A_1))
      | ~ v1_funct_1(k6_partfun1(A_557))
      | ~ v1_relat_1(k6_partfun1(A_557)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_88,c_7072])).

tff(c_7107,plain,(
    ! [A_559] :
      ( k2_funct_1(k6_partfun1(A_559)) = k6_partfun1(A_559)
      | ~ v1_funct_1(k6_partfun1(A_559)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_211,c_85,c_85,c_87,c_7093])).

tff(c_7122,plain,(
    ! [A_6] :
      ( k2_funct_1(k6_partfun1(A_6)) = k6_partfun1(A_6)
      | ~ v1_funct_1('#skF_1')
      | A_6 != '#skF_1' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4398,c_7107])).

tff(c_7126,plain,(
    ! [A_560] :
      ( k2_funct_1(k6_partfun1(A_560)) = k6_partfun1(A_560)
      | A_560 != '#skF_1' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3891,c_7122])).

tff(c_7151,plain,(
    ! [A_561] :
      ( k6_partfun1(A_561) = k2_funct_1('#skF_1')
      | A_561 != '#skF_1'
      | A_561 != '#skF_1' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4398,c_7126])).

tff(c_7292,plain,(
    ! [A_561] :
      ( v1_relat_1(k2_funct_1('#skF_1'))
      | A_561 != '#skF_1'
      | A_561 != '#skF_1' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_7151,c_85])).

tff(c_7329,plain,(
    ! [A_561] :
      ( A_561 != '#skF_1'
      | A_561 != '#skF_1' ) ),
    inference(splitLeft,[status(thm)],[c_7292])).

tff(c_7400,plain,(
    $false ),
    inference(reflexivity,[status(thm),theory(equality)],[c_7329])).

tff(c_7401,plain,(
    v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_7292])).

tff(c_8,plain,(
    ! [A_4] :
      ( k1_relat_1(A_4) != k1_xboole_0
      | k1_xboole_0 = A_4
      | ~ v1_relat_1(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_3389,plain,(
    ! [A_4] :
      ( k1_relat_1(A_4) != '#skF_3'
      | A_4 = '#skF_3'
      | ~ v1_relat_1(A_4) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3383,c_3383,c_8])).

tff(c_4506,plain,(
    ! [A_4] :
      ( k1_relat_1(A_4) != '#skF_1'
      | A_4 = '#skF_1'
      | ~ v1_relat_1(A_4) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3881,c_3881,c_3389])).

tff(c_7415,plain,
    ( k1_relat_1(k2_funct_1('#skF_1')) != '#skF_1'
    | k2_funct_1('#skF_1') = '#skF_1' ),
    inference(resolution,[status(thm)],[c_7401,c_4506])).

tff(c_7417,plain,(
    k1_relat_1(k2_funct_1('#skF_1')) != '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_7415])).

tff(c_7285,plain,(
    ! [A_561] :
      ( k1_relat_1(k2_funct_1('#skF_1')) = A_561
      | A_561 != '#skF_1'
      | A_561 != '#skF_1' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_7151,c_87])).

tff(c_7513,plain,(
    k1_relat_1(k2_funct_1('#skF_1')) = '#skF_1' ),
    inference(reflexivity,[status(thm),theory(equality)],[c_7285])).

tff(c_7517,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_7417,c_7513])).

tff(c_7518,plain,(
    k2_funct_1('#skF_1') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_7415])).

tff(c_6284,plain,(
    ! [F_505,A_507,E_503,C_506,B_504,D_508] :
      ( m1_subset_1(k1_partfun1(A_507,B_504,C_506,D_508,E_503,F_505),k1_zfmisc_1(k2_zfmisc_1(A_507,D_508)))
      | ~ m1_subset_1(F_505,k1_zfmisc_1(k2_zfmisc_1(C_506,D_508)))
      | ~ v1_funct_1(F_505)
      | ~ m1_subset_1(E_503,k1_zfmisc_1(k2_zfmisc_1(A_507,B_504)))
      | ~ v1_funct_1(E_503) ) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_52,plain,(
    ! [A_38,B_39] :
      ( k2_funct_2(A_38,B_39) = k2_funct_1(B_39)
      | ~ m1_subset_1(B_39,k1_zfmisc_1(k2_zfmisc_1(A_38,A_38)))
      | ~ v3_funct_2(B_39,A_38,A_38)
      | ~ v1_funct_2(B_39,A_38,A_38)
      | ~ v1_funct_1(B_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_9070,plain,(
    ! [B_648,C_651,D_649,F_650,E_652] :
      ( k2_funct_2(D_649,k1_partfun1(D_649,B_648,C_651,D_649,E_652,F_650)) = k2_funct_1(k1_partfun1(D_649,B_648,C_651,D_649,E_652,F_650))
      | ~ v3_funct_2(k1_partfun1(D_649,B_648,C_651,D_649,E_652,F_650),D_649,D_649)
      | ~ v1_funct_2(k1_partfun1(D_649,B_648,C_651,D_649,E_652,F_650),D_649,D_649)
      | ~ v1_funct_1(k1_partfun1(D_649,B_648,C_651,D_649,E_652,F_650))
      | ~ m1_subset_1(F_650,k1_zfmisc_1(k2_zfmisc_1(C_651,D_649)))
      | ~ v1_funct_1(F_650)
      | ~ m1_subset_1(E_652,k1_zfmisc_1(k2_zfmisc_1(D_649,B_648)))
      | ~ v1_funct_1(E_652) ) ),
    inference(resolution,[status(thm)],[c_6284,c_52])).

tff(c_9072,plain,
    ( k2_funct_2('#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_1','#skF_1')) = k2_funct_1(k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_1','#skF_1'))
    | ~ v3_funct_2('#skF_1','#skF_1','#skF_1')
    | ~ v1_funct_2(k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_1','#skF_1'),'#skF_1','#skF_1')
    | ~ v1_funct_1(k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_1','#skF_1'))
    | ~ m1_subset_1('#skF_1',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ v1_funct_1('#skF_1')
    | ~ m1_subset_1('#skF_1',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ v1_funct_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_5751,c_9070])).

tff(c_9074,plain,(
    k2_funct_2('#skF_1','#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3891,c_4548,c_3891,c_4548,c_3891,c_5751,c_3889,c_5751,c_3890,c_7518,c_5751,c_5751,c_9072])).

tff(c_3887,plain,(
    ~ r2_relset_1('#skF_1','#skF_1','#skF_1',k2_funct_2('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3881,c_62])).

tff(c_4454,plain,(
    ~ r2_relset_1('#skF_1','#skF_1','#skF_1',k2_funct_2('#skF_1','#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4377,c_3887])).

tff(c_9075,plain,(
    ~ r2_relset_1('#skF_1','#skF_1','#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_9074,c_4454])).

tff(c_9078,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4592,c_9075])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:14:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.22/2.76  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.22/2.78  
% 8.22/2.78  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.22/2.78  %$ r2_relset_1 > v3_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k8_relat_1 > k5_relat_1 > k2_zfmisc_1 > k2_funct_2 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 8.22/2.78  
% 8.22/2.78  %Foreground sorts:
% 8.22/2.78  
% 8.22/2.78  
% 8.22/2.78  %Background operators:
% 8.22/2.78  
% 8.22/2.78  
% 8.22/2.78  %Foreground operators:
% 8.22/2.78  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 8.22/2.78  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 8.22/2.78  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 8.22/2.78  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 8.22/2.78  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 8.22/2.78  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.22/2.78  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 8.22/2.78  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 8.22/2.78  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 8.22/2.78  tff(k2_funct_2, type, k2_funct_2: ($i * $i) > $i).
% 8.22/2.78  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 8.22/2.78  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 8.22/2.78  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 8.22/2.78  tff('#skF_2', type, '#skF_2': $i).
% 8.22/2.78  tff('#skF_3', type, '#skF_3': $i).
% 8.22/2.78  tff('#skF_1', type, '#skF_1': $i).
% 8.22/2.78  tff(v2_funct_2, type, v2_funct_2: ($i * $i) > $o).
% 8.22/2.78  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 8.22/2.78  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 8.22/2.78  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 8.22/2.78  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.22/2.78  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 8.22/2.78  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 8.22/2.78  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 8.22/2.78  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.22/2.78  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 8.22/2.78  tff(v3_funct_2, type, v3_funct_2: ($i * $i * $i) > $o).
% 8.22/2.78  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 8.22/2.78  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 8.22/2.78  
% 8.22/2.81  tff(f_214, negated_conjecture, ~(![A, B]: ((((v1_funct_1(B) & v1_funct_2(B, A, A)) & v3_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (![C]: ((((v1_funct_1(C) & v1_funct_2(C, A, A)) & v3_funct_2(C, A, A)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (r2_relset_1(A, A, k1_partfun1(A, A, A, A, B, C), k6_partfun1(A)) => r2_relset_1(A, A, C, k2_funct_2(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t87_funct_2)).
% 8.22/2.81  tff(f_102, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 8.22/2.81  tff(f_148, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 8.22/2.81  tff(f_45, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 8.22/2.81  tff(f_50, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v2_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc4_funct_1)).
% 8.22/2.81  tff(f_41, axiom, (![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_relat_1)).
% 8.22/2.81  tff(f_84, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 8.22/2.81  tff(f_90, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 8.22/2.81  tff(f_124, axiom, (![A, B]: ((v1_relat_1(B) & v5_relat_1(B, A)) => (v2_funct_2(B, A) <=> (k2_relat_1(B) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_funct_2)).
% 8.22/2.81  tff(f_116, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v3_funct_2(C, A, B)) => ((v1_funct_1(C) & v2_funct_1(C)) & v2_funct_2(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_funct_2)).
% 8.22/2.81  tff(f_94, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 8.22/2.81  tff(f_104, axiom, (![A]: m1_subset_1(k6_relat_1(A), k1_zfmisc_1(k2_zfmisc_1(A, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_relset_1)).
% 8.22/2.81  tff(f_136, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (v1_funct_1(k1_partfun1(A, B, C, D, E, F)) & m1_subset_1(k1_partfun1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 8.22/2.81  tff(f_192, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => ((((k2_relset_1(A, B, C) = B) & r2_relset_1(A, A, k1_partfun1(A, B, B, A, C, D), k6_partfun1(A))) & v2_funct_1(C)) => (((A = k1_xboole_0) | (B = k1_xboole_0)) | (D = k2_funct_1(C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_funct_2)).
% 8.22/2.81  tff(f_146, axiom, (![A, B]: ((((v1_funct_1(B) & v1_funct_2(B, A, A)) & v3_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (k2_funct_2(A, B) = k2_funct_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_funct_2)).
% 8.22/2.81  tff(f_33, axiom, (![A]: (v1_relat_1(A) => (k8_relat_1(k2_relat_1(A), A) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t126_relat_1)).
% 8.22/2.81  tff(f_29, axiom, (![A, B]: (v1_relat_1(B) => (k8_relat_1(A, B) = k5_relat_1(B, k6_relat_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t123_relat_1)).
% 8.22/2.81  tff(f_80, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (((v2_funct_1(A) & (k2_relat_1(A) = k1_relat_1(B))) & (k5_relat_1(A, B) = k6_relat_1(k1_relat_1(A)))) => (B = k2_funct_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_funct_1)).
% 8.22/2.81  tff(c_66, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_214])).
% 8.22/2.81  tff(c_399, plain, (![A_82, B_83, D_84]: (r2_relset_1(A_82, B_83, D_84, D_84) | ~m1_subset_1(D_84, k1_zfmisc_1(k2_zfmisc_1(A_82, B_83))))), inference(cnfTransformation, [status(thm)], [f_102])).
% 8.22/2.81  tff(c_410, plain, (r2_relset_1('#skF_1', '#skF_1', '#skF_3', '#skF_3')), inference(resolution, [status(thm)], [c_66, c_399])).
% 8.22/2.81  tff(c_54, plain, (![A_40]: (k6_relat_1(A_40)=k6_partfun1(A_40))), inference(cnfTransformation, [status(thm)], [f_148])).
% 8.22/2.81  tff(c_10, plain, (![A_5]: (k1_relat_1(k6_relat_1(A_5))=A_5)), inference(cnfTransformation, [status(thm)], [f_45])).
% 8.22/2.81  tff(c_87, plain, (![A_5]: (k1_relat_1(k6_partfun1(A_5))=A_5)), inference(demodulation, [status(thm), theory('equality')], [c_54, c_10])).
% 8.22/2.81  tff(c_16, plain, (![A_6]: (v1_relat_1(k6_relat_1(A_6)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 8.22/2.81  tff(c_85, plain, (![A_6]: (v1_relat_1(k6_partfun1(A_6)))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_16])).
% 8.22/2.81  tff(c_151, plain, (![A_57]: (k1_relat_1(A_57)!=k1_xboole_0 | k1_xboole_0=A_57 | ~v1_relat_1(A_57))), inference(cnfTransformation, [status(thm)], [f_41])).
% 8.22/2.81  tff(c_157, plain, (![A_6]: (k1_relat_1(k6_partfun1(A_6))!=k1_xboole_0 | k6_partfun1(A_6)=k1_xboole_0)), inference(resolution, [status(thm)], [c_85, c_151])).
% 8.22/2.81  tff(c_163, plain, (![A_6]: (k1_xboole_0!=A_6 | k6_partfun1(A_6)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_87, c_157])).
% 8.22/2.81  tff(c_64, plain, (r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', '#skF_3'), k6_partfun1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_214])).
% 8.22/2.81  tff(c_275, plain, (r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', '#skF_3'), k1_xboole_0) | k1_xboole_0!='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_163, c_64])).
% 8.22/2.81  tff(c_321, plain, (k1_xboole_0!='#skF_1'), inference(splitLeft, [status(thm)], [c_275])).
% 8.22/2.81  tff(c_80, plain, (v1_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_214])).
% 8.22/2.81  tff(c_78, plain, (v1_funct_2('#skF_2', '#skF_1', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_214])).
% 8.22/2.81  tff(c_74, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_214])).
% 8.22/2.81  tff(c_72, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_214])).
% 8.22/2.81  tff(c_70, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_214])).
% 8.22/2.81  tff(c_276, plain, (![C_64, A_65, B_66]: (v1_relat_1(C_64) | ~m1_subset_1(C_64, k1_zfmisc_1(k2_zfmisc_1(A_65, B_66))))), inference(cnfTransformation, [status(thm)], [f_84])).
% 8.22/2.81  tff(c_289, plain, (v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_74, c_276])).
% 8.22/2.81  tff(c_351, plain, (![C_74, B_75, A_76]: (v5_relat_1(C_74, B_75) | ~m1_subset_1(C_74, k1_zfmisc_1(k2_zfmisc_1(A_76, B_75))))), inference(cnfTransformation, [status(thm)], [f_90])).
% 8.22/2.81  tff(c_367, plain, (v5_relat_1('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_74, c_351])).
% 8.22/2.81  tff(c_415, plain, (![B_86, A_87]: (k2_relat_1(B_86)=A_87 | ~v2_funct_2(B_86, A_87) | ~v5_relat_1(B_86, A_87) | ~v1_relat_1(B_86))), inference(cnfTransformation, [status(thm)], [f_124])).
% 8.22/2.81  tff(c_424, plain, (k2_relat_1('#skF_2')='#skF_1' | ~v2_funct_2('#skF_2', '#skF_1') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_367, c_415])).
% 8.22/2.81  tff(c_436, plain, (k2_relat_1('#skF_2')='#skF_1' | ~v2_funct_2('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_289, c_424])).
% 8.22/2.81  tff(c_440, plain, (~v2_funct_2('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_436])).
% 8.22/2.81  tff(c_76, plain, (v3_funct_2('#skF_2', '#skF_1', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_214])).
% 8.22/2.81  tff(c_789, plain, (![C_120, B_121, A_122]: (v2_funct_2(C_120, B_121) | ~v3_funct_2(C_120, A_122, B_121) | ~v1_funct_1(C_120) | ~m1_subset_1(C_120, k1_zfmisc_1(k2_zfmisc_1(A_122, B_121))))), inference(cnfTransformation, [status(thm)], [f_116])).
% 8.22/2.81  tff(c_801, plain, (v2_funct_2('#skF_2', '#skF_1') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_74, c_789])).
% 8.22/2.81  tff(c_810, plain, (v2_funct_2('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_80, c_76, c_801])).
% 8.22/2.81  tff(c_812, plain, $false, inference(negUnitSimplification, [status(thm)], [c_440, c_810])).
% 8.22/2.81  tff(c_813, plain, (k2_relat_1('#skF_2')='#skF_1'), inference(splitRight, [status(thm)], [c_436])).
% 8.22/2.81  tff(c_1008, plain, (![A_143, B_144, C_145]: (k2_relset_1(A_143, B_144, C_145)=k2_relat_1(C_145) | ~m1_subset_1(C_145, k1_zfmisc_1(k2_zfmisc_1(A_143, B_144))))), inference(cnfTransformation, [status(thm)], [f_94])).
% 8.22/2.81  tff(c_1020, plain, (k2_relset_1('#skF_1', '#skF_1', '#skF_2')=k2_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_74, c_1008])).
% 8.22/2.81  tff(c_1028, plain, (k2_relset_1('#skF_1', '#skF_1', '#skF_2')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_813, c_1020])).
% 8.22/2.81  tff(c_36, plain, (![A_26]: (m1_subset_1(k6_relat_1(A_26), k1_zfmisc_1(k2_zfmisc_1(A_26, A_26))))), inference(cnfTransformation, [status(thm)], [f_104])).
% 8.22/2.81  tff(c_81, plain, (![A_26]: (m1_subset_1(k6_partfun1(A_26), k1_zfmisc_1(k2_zfmisc_1(A_26, A_26))))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_36])).
% 8.22/2.81  tff(c_409, plain, (![A_26]: (r2_relset_1(A_26, A_26, k6_partfun1(A_26), k6_partfun1(A_26)))), inference(resolution, [status(thm)], [c_81, c_399])).
% 8.22/2.81  tff(c_1049, plain, (![C_147, A_148, B_149]: (v2_funct_1(C_147) | ~v3_funct_2(C_147, A_148, B_149) | ~v1_funct_1(C_147) | ~m1_subset_1(C_147, k1_zfmisc_1(k2_zfmisc_1(A_148, B_149))))), inference(cnfTransformation, [status(thm)], [f_116])).
% 8.22/2.81  tff(c_1061, plain, (v2_funct_1('#skF_2') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_74, c_1049])).
% 8.22/2.81  tff(c_1071, plain, (v2_funct_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_80, c_76, c_1061])).
% 8.22/2.81  tff(c_1958, plain, (![B_208, C_210, D_212, E_207, F_209, A_211]: (m1_subset_1(k1_partfun1(A_211, B_208, C_210, D_212, E_207, F_209), k1_zfmisc_1(k2_zfmisc_1(A_211, D_212))) | ~m1_subset_1(F_209, k1_zfmisc_1(k2_zfmisc_1(C_210, D_212))) | ~v1_funct_1(F_209) | ~m1_subset_1(E_207, k1_zfmisc_1(k2_zfmisc_1(A_211, B_208))) | ~v1_funct_1(E_207))), inference(cnfTransformation, [status(thm)], [f_136])).
% 8.22/2.81  tff(c_1328, plain, (![D_166, C_167, A_168, B_169]: (D_166=C_167 | ~r2_relset_1(A_168, B_169, C_167, D_166) | ~m1_subset_1(D_166, k1_zfmisc_1(k2_zfmisc_1(A_168, B_169))) | ~m1_subset_1(C_167, k1_zfmisc_1(k2_zfmisc_1(A_168, B_169))))), inference(cnfTransformation, [status(thm)], [f_102])).
% 8.22/2.81  tff(c_1342, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', '#skF_3')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_64, c_1328])).
% 8.22/2.81  tff(c_1365, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', '#skF_3')=k6_partfun1('#skF_1') | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_81, c_1342])).
% 8.22/2.81  tff(c_1470, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_1365])).
% 8.22/2.81  tff(c_1966, plain, (~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v1_funct_1('#skF_3') | ~m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_1958, c_1470])).
% 8.22/2.81  tff(c_1996, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_80, c_74, c_72, c_66, c_1966])).
% 8.22/2.81  tff(c_1997, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', '#skF_3')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_1365])).
% 8.22/2.81  tff(c_3026, plain, (![C_275, D_276, B_277, A_278]: (k2_funct_1(C_275)=D_276 | k1_xboole_0=B_277 | k1_xboole_0=A_278 | ~v2_funct_1(C_275) | ~r2_relset_1(A_278, A_278, k1_partfun1(A_278, B_277, B_277, A_278, C_275, D_276), k6_partfun1(A_278)) | k2_relset_1(A_278, B_277, C_275)!=B_277 | ~m1_subset_1(D_276, k1_zfmisc_1(k2_zfmisc_1(B_277, A_278))) | ~v1_funct_2(D_276, B_277, A_278) | ~v1_funct_1(D_276) | ~m1_subset_1(C_275, k1_zfmisc_1(k2_zfmisc_1(A_278, B_277))) | ~v1_funct_2(C_275, A_278, B_277) | ~v1_funct_1(C_275))), inference(cnfTransformation, [status(thm)], [f_192])).
% 8.22/2.81  tff(c_3041, plain, (k2_funct_1('#skF_2')='#skF_3' | k1_xboole_0='#skF_1' | k1_xboole_0='#skF_1' | ~v2_funct_1('#skF_2') | ~r2_relset_1('#skF_1', '#skF_1', k6_partfun1('#skF_1'), k6_partfun1('#skF_1')) | k2_relset_1('#skF_1', '#skF_1', '#skF_2')!='#skF_1' | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_3') | ~m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_1997, c_3026])).
% 8.22/2.81  tff(c_3046, plain, (k2_funct_1('#skF_2')='#skF_3' | k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_80, c_78, c_74, c_72, c_70, c_66, c_1028, c_409, c_1071, c_3041])).
% 8.22/2.81  tff(c_3047, plain, (k2_funct_1('#skF_2')='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_321, c_3046])).
% 8.22/2.81  tff(c_1440, plain, (![A_173, B_174]: (k2_funct_2(A_173, B_174)=k2_funct_1(B_174) | ~m1_subset_1(B_174, k1_zfmisc_1(k2_zfmisc_1(A_173, A_173))) | ~v3_funct_2(B_174, A_173, A_173) | ~v1_funct_2(B_174, A_173, A_173) | ~v1_funct_1(B_174))), inference(cnfTransformation, [status(thm)], [f_146])).
% 8.22/2.81  tff(c_1452, plain, (k2_funct_2('#skF_1', '#skF_2')=k2_funct_1('#skF_2') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_74, c_1440])).
% 8.22/2.81  tff(c_1460, plain, (k2_funct_2('#skF_1', '#skF_2')=k2_funct_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_80, c_78, c_76, c_1452])).
% 8.22/2.81  tff(c_62, plain, (~r2_relset_1('#skF_1', '#skF_1', '#skF_3', k2_funct_2('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_214])).
% 8.22/2.81  tff(c_1465, plain, (~r2_relset_1('#skF_1', '#skF_1', '#skF_3', k2_funct_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_1460, c_62])).
% 8.22/2.81  tff(c_3048, plain, (~r2_relset_1('#skF_1', '#skF_1', '#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_3047, c_1465])).
% 8.22/2.81  tff(c_3052, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_410, c_3048])).
% 8.22/2.81  tff(c_3054, plain, (k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_275])).
% 8.22/2.81  tff(c_288, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_66, c_276])).
% 8.22/2.81  tff(c_6, plain, (![A_4]: (k2_relat_1(A_4)!=k1_xboole_0 | k1_xboole_0=A_4 | ~v1_relat_1(A_4))), inference(cnfTransformation, [status(thm)], [f_41])).
% 8.22/2.81  tff(c_296, plain, (k2_relat_1('#skF_3')!=k1_xboole_0 | k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_288, c_6])).
% 8.22/2.81  tff(c_306, plain, (k2_relat_1('#skF_3')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_296])).
% 8.22/2.81  tff(c_3056, plain, (k2_relat_1('#skF_3')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_3054, c_306])).
% 8.22/2.81  tff(c_3146, plain, (![C_283, B_284, A_285]: (v5_relat_1(C_283, B_284) | ~m1_subset_1(C_283, k1_zfmisc_1(k2_zfmisc_1(A_285, B_284))))), inference(cnfTransformation, [status(thm)], [f_90])).
% 8.22/2.81  tff(c_3157, plain, (v5_relat_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_66, c_3146])).
% 8.22/2.81  tff(c_3230, plain, (![B_292, A_293]: (k2_relat_1(B_292)=A_293 | ~v2_funct_2(B_292, A_293) | ~v5_relat_1(B_292, A_293) | ~v1_relat_1(B_292))), inference(cnfTransformation, [status(thm)], [f_124])).
% 8.22/2.81  tff(c_3242, plain, (k2_relat_1('#skF_3')='#skF_1' | ~v2_funct_2('#skF_3', '#skF_1') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_3157, c_3230])).
% 8.22/2.81  tff(c_3255, plain, (k2_relat_1('#skF_3')='#skF_1' | ~v2_funct_2('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_288, c_3242])).
% 8.22/2.81  tff(c_3256, plain, (~v2_funct_2('#skF_3', '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_3056, c_3255])).
% 8.22/2.81  tff(c_68, plain, (v3_funct_2('#skF_3', '#skF_1', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_214])).
% 8.22/2.81  tff(c_3362, plain, (![C_303, B_304, A_305]: (v2_funct_2(C_303, B_304) | ~v3_funct_2(C_303, A_305, B_304) | ~v1_funct_1(C_303) | ~m1_subset_1(C_303, k1_zfmisc_1(k2_zfmisc_1(A_305, B_304))))), inference(cnfTransformation, [status(thm)], [f_116])).
% 8.22/2.81  tff(c_3371, plain, (v2_funct_2('#skF_3', '#skF_1') | ~v3_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_66, c_3362])).
% 8.22/2.81  tff(c_3380, plain, (v2_funct_2('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_68, c_3371])).
% 8.22/2.81  tff(c_3382, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3256, c_3380])).
% 8.22/2.81  tff(c_3383, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_296])).
% 8.22/2.81  tff(c_3410, plain, (r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', '#skF_3'), '#skF_3') | '#skF_3'!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_3383, c_3383, c_275])).
% 8.22/2.81  tff(c_3411, plain, ('#skF_3'!='#skF_1'), inference(splitLeft, [status(thm)], [c_3410])).
% 8.22/2.81  tff(c_3384, plain, (k2_relat_1('#skF_3')=k1_xboole_0), inference(splitRight, [status(thm)], [c_296])).
% 8.22/2.81  tff(c_3400, plain, (k2_relat_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_3383, c_3384])).
% 8.22/2.81  tff(c_3596, plain, (![C_316, B_317, A_318]: (v5_relat_1(C_316, B_317) | ~m1_subset_1(C_316, k1_zfmisc_1(k2_zfmisc_1(A_318, B_317))))), inference(cnfTransformation, [status(thm)], [f_90])).
% 8.22/2.81  tff(c_3611, plain, (v5_relat_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_66, c_3596])).
% 8.22/2.81  tff(c_3655, plain, (![B_323, A_324]: (k2_relat_1(B_323)=A_324 | ~v2_funct_2(B_323, A_324) | ~v5_relat_1(B_323, A_324) | ~v1_relat_1(B_323))), inference(cnfTransformation, [status(thm)], [f_124])).
% 8.22/2.81  tff(c_3667, plain, (k2_relat_1('#skF_3')='#skF_1' | ~v2_funct_2('#skF_3', '#skF_1') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_3611, c_3655])).
% 8.22/2.81  tff(c_3679, plain, ('#skF_3'='#skF_1' | ~v2_funct_2('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_288, c_3400, c_3667])).
% 8.22/2.81  tff(c_3680, plain, (~v2_funct_2('#skF_3', '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_3411, c_3679])).
% 8.22/2.81  tff(c_3857, plain, (![C_343, B_344, A_345]: (v2_funct_2(C_343, B_344) | ~v3_funct_2(C_343, A_345, B_344) | ~v1_funct_1(C_343) | ~m1_subset_1(C_343, k1_zfmisc_1(k2_zfmisc_1(A_345, B_344))))), inference(cnfTransformation, [status(thm)], [f_116])).
% 8.22/2.81  tff(c_3866, plain, (v2_funct_2('#skF_3', '#skF_1') | ~v3_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_66, c_3857])).
% 8.22/2.81  tff(c_3877, plain, (v2_funct_2('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_68, c_3866])).
% 8.22/2.81  tff(c_3879, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3680, c_3877])).
% 8.22/2.81  tff(c_3881, plain, ('#skF_3'='#skF_1'), inference(splitRight, [status(thm)], [c_3410])).
% 8.22/2.81  tff(c_3884, plain, (k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_3881, c_3383])).
% 8.22/2.81  tff(c_189, plain, (![A_59]: (m1_subset_1(k6_partfun1(A_59), k1_zfmisc_1(k2_zfmisc_1(A_59, A_59))))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_36])).
% 8.22/2.81  tff(c_192, plain, (![A_6]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(k2_zfmisc_1(A_6, A_6))) | k1_xboole_0!=A_6)), inference(superposition, [status(thm), theory('equality')], [c_163, c_189])).
% 8.22/2.81  tff(c_4547, plain, (![A_6]: (m1_subset_1('#skF_1', k1_zfmisc_1(k2_zfmisc_1(A_6, A_6))) | A_6!='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_3884, c_3884, c_192])).
% 8.22/2.81  tff(c_4574, plain, (![A_405, B_406, D_407]: (r2_relset_1(A_405, B_406, D_407, D_407) | ~m1_subset_1(D_407, k1_zfmisc_1(k2_zfmisc_1(A_405, B_406))))), inference(cnfTransformation, [status(thm)], [f_102])).
% 8.22/2.81  tff(c_4592, plain, (r2_relset_1('#skF_1', '#skF_1', '#skF_1', '#skF_1')), inference(resolution, [status(thm)], [c_4547, c_4574])).
% 8.22/2.81  tff(c_3891, plain, (v1_funct_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_3881, c_72])).
% 8.22/2.81  tff(c_4548, plain, (m1_subset_1('#skF_1', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_3884, c_3884, c_192])).
% 8.22/2.81  tff(c_5716, plain, (![E_476, F_478, C_479, D_481, B_477, A_480]: (m1_subset_1(k1_partfun1(A_480, B_477, C_479, D_481, E_476, F_478), k1_zfmisc_1(k2_zfmisc_1(A_480, D_481))) | ~m1_subset_1(F_478, k1_zfmisc_1(k2_zfmisc_1(C_479, D_481))) | ~v1_funct_1(F_478) | ~m1_subset_1(E_476, k1_zfmisc_1(k2_zfmisc_1(A_480, B_477))) | ~v1_funct_1(E_476))), inference(cnfTransformation, [status(thm)], [f_136])).
% 8.22/2.81  tff(c_3388, plain, (![A_6]: (A_6!='#skF_3' | k6_partfun1(A_6)='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_3383, c_3383, c_163])).
% 8.22/2.81  tff(c_4399, plain, (k6_partfun1('#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_3881, c_3881, c_3388])).
% 8.22/2.81  tff(c_304, plain, (k2_relat_1('#skF_2')!=k1_xboole_0 | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_289, c_6])).
% 8.22/2.81  tff(c_3984, plain, (k2_relat_1('#skF_2')!='#skF_1' | '#skF_2'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_3884, c_3884, c_304])).
% 8.22/2.81  tff(c_3985, plain, (k2_relat_1('#skF_2')!='#skF_1'), inference(splitLeft, [status(thm)], [c_3984])).
% 8.22/2.81  tff(c_3988, plain, (![C_352, B_353, A_354]: (v5_relat_1(C_352, B_353) | ~m1_subset_1(C_352, k1_zfmisc_1(k2_zfmisc_1(A_354, B_353))))), inference(cnfTransformation, [status(thm)], [f_90])).
% 8.22/2.81  tff(c_4000, plain, (v5_relat_1('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_74, c_3988])).
% 8.22/2.81  tff(c_4215, plain, (![B_372, A_373]: (k2_relat_1(B_372)=A_373 | ~v2_funct_2(B_372, A_373) | ~v5_relat_1(B_372, A_373) | ~v1_relat_1(B_372))), inference(cnfTransformation, [status(thm)], [f_124])).
% 8.22/2.81  tff(c_4224, plain, (k2_relat_1('#skF_2')='#skF_1' | ~v2_funct_2('#skF_2', '#skF_1') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_4000, c_4215])).
% 8.22/2.81  tff(c_4233, plain, (k2_relat_1('#skF_2')='#skF_1' | ~v2_funct_2('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_289, c_4224])).
% 8.22/2.81  tff(c_4234, plain, (~v2_funct_2('#skF_2', '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_3985, c_4233])).
% 8.22/2.81  tff(c_4357, plain, (![C_387, B_388, A_389]: (v2_funct_2(C_387, B_388) | ~v3_funct_2(C_387, A_389, B_388) | ~v1_funct_1(C_387) | ~m1_subset_1(C_387, k1_zfmisc_1(k2_zfmisc_1(A_389, B_388))))), inference(cnfTransformation, [status(thm)], [f_116])).
% 8.22/2.81  tff(c_4366, plain, (v2_funct_2('#skF_2', '#skF_1') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_74, c_4357])).
% 8.22/2.81  tff(c_4374, plain, (v2_funct_2('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_80, c_76, c_4366])).
% 8.22/2.81  tff(c_4376, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4234, c_4374])).
% 8.22/2.81  tff(c_4377, plain, ('#skF_2'='#skF_1'), inference(splitRight, [status(thm)], [c_3984])).
% 8.22/2.81  tff(c_3886, plain, (r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', '#skF_1'), k6_partfun1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_3881, c_64])).
% 8.22/2.81  tff(c_4543, plain, (r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_1'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_4399, c_4377, c_3886])).
% 8.22/2.81  tff(c_5096, plain, (![D_444, C_445, A_446, B_447]: (D_444=C_445 | ~r2_relset_1(A_446, B_447, C_445, D_444) | ~m1_subset_1(D_444, k1_zfmisc_1(k2_zfmisc_1(A_446, B_447))) | ~m1_subset_1(C_445, k1_zfmisc_1(k2_zfmisc_1(A_446, B_447))))), inference(cnfTransformation, [status(thm)], [f_102])).
% 8.22/2.81  tff(c_5106, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_1')='#skF_1' | ~m1_subset_1('#skF_1', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_4543, c_5096])).
% 8.22/2.81  tff(c_5121, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_1')='#skF_1' | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_4548, c_5106])).
% 8.22/2.81  tff(c_5273, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_5121])).
% 8.22/2.81  tff(c_5721, plain, (~m1_subset_1('#skF_1', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v1_funct_1('#skF_1')), inference(resolution, [status(thm)], [c_5716, c_5273])).
% 8.22/2.81  tff(c_5750, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3891, c_4548, c_5721])).
% 8.22/2.81  tff(c_5751, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_1')='#skF_1'), inference(splitRight, [status(thm)], [c_5121])).
% 8.22/2.81  tff(c_3889, plain, (v1_funct_2('#skF_1', '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_3881, c_70])).
% 8.22/2.81  tff(c_3890, plain, (v3_funct_2('#skF_1', '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_3881, c_68])).
% 8.22/2.81  tff(c_4398, plain, (![A_6]: (A_6!='#skF_1' | k6_partfun1(A_6)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_3881, c_3881, c_3388])).
% 8.22/2.81  tff(c_12, plain, (![A_5]: (k2_relat_1(k6_relat_1(A_5))=A_5)), inference(cnfTransformation, [status(thm)], [f_45])).
% 8.22/2.81  tff(c_86, plain, (![A_5]: (k2_relat_1(k6_partfun1(A_5))=A_5)), inference(demodulation, [status(thm), theory('equality')], [c_54, c_12])).
% 8.22/2.81  tff(c_193, plain, (![A_60]: (k8_relat_1(k2_relat_1(A_60), A_60)=A_60 | ~v1_relat_1(A_60))), inference(cnfTransformation, [status(thm)], [f_33])).
% 8.22/2.81  tff(c_205, plain, (![A_5]: (k8_relat_1(A_5, k6_partfun1(A_5))=k6_partfun1(A_5) | ~v1_relat_1(k6_partfun1(A_5)))), inference(superposition, [status(thm), theory('equality')], [c_86, c_193])).
% 8.22/2.81  tff(c_211, plain, (![A_5]: (k8_relat_1(A_5, k6_partfun1(A_5))=k6_partfun1(A_5))), inference(demodulation, [status(thm), theory('equality')], [c_85, c_205])).
% 8.22/2.81  tff(c_2, plain, (![B_2, A_1]: (k5_relat_1(B_2, k6_relat_1(A_1))=k8_relat_1(A_1, B_2) | ~v1_relat_1(B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 8.22/2.81  tff(c_88, plain, (![B_2, A_1]: (k5_relat_1(B_2, k6_partfun1(A_1))=k8_relat_1(A_1, B_2) | ~v1_relat_1(B_2))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_2])).
% 8.22/2.81  tff(c_18, plain, (![A_6]: (v2_funct_1(k6_relat_1(A_6)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 8.22/2.81  tff(c_84, plain, (![A_6]: (v2_funct_1(k6_partfun1(A_6)))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_18])).
% 8.22/2.81  tff(c_22, plain, (![A_10, B_12]: (k2_funct_1(A_10)=B_12 | k6_relat_1(k1_relat_1(A_10))!=k5_relat_1(A_10, B_12) | k2_relat_1(A_10)!=k1_relat_1(B_12) | ~v2_funct_1(A_10) | ~v1_funct_1(B_12) | ~v1_relat_1(B_12) | ~v1_funct_1(A_10) | ~v1_relat_1(A_10))), inference(cnfTransformation, [status(thm)], [f_80])).
% 8.22/2.81  tff(c_5951, plain, (![A_486, B_487]: (k2_funct_1(A_486)=B_487 | k6_partfun1(k1_relat_1(A_486))!=k5_relat_1(A_486, B_487) | k2_relat_1(A_486)!=k1_relat_1(B_487) | ~v2_funct_1(A_486) | ~v1_funct_1(B_487) | ~v1_relat_1(B_487) | ~v1_funct_1(A_486) | ~v1_relat_1(A_486))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_22])).
% 8.22/2.81  tff(c_5968, plain, (![A_5, B_487]: (k2_funct_1(k6_partfun1(A_5))=B_487 | k5_relat_1(k6_partfun1(A_5), B_487)!=k6_partfun1(A_5) | k2_relat_1(k6_partfun1(A_5))!=k1_relat_1(B_487) | ~v2_funct_1(k6_partfun1(A_5)) | ~v1_funct_1(B_487) | ~v1_relat_1(B_487) | ~v1_funct_1(k6_partfun1(A_5)) | ~v1_relat_1(k6_partfun1(A_5)))), inference(superposition, [status(thm), theory('equality')], [c_87, c_5951])).
% 8.22/2.81  tff(c_7072, plain, (![A_557, B_558]: (k2_funct_1(k6_partfun1(A_557))=B_558 | k5_relat_1(k6_partfun1(A_557), B_558)!=k6_partfun1(A_557) | k1_relat_1(B_558)!=A_557 | ~v1_funct_1(B_558) | ~v1_relat_1(B_558) | ~v1_funct_1(k6_partfun1(A_557)))), inference(demodulation, [status(thm), theory('equality')], [c_85, c_84, c_86, c_5968])).
% 8.22/2.81  tff(c_7093, plain, (![A_1, A_557]: (k6_partfun1(A_1)=k2_funct_1(k6_partfun1(A_557)) | k8_relat_1(A_1, k6_partfun1(A_557))!=k6_partfun1(A_557) | k1_relat_1(k6_partfun1(A_1))!=A_557 | ~v1_funct_1(k6_partfun1(A_1)) | ~v1_relat_1(k6_partfun1(A_1)) | ~v1_funct_1(k6_partfun1(A_557)) | ~v1_relat_1(k6_partfun1(A_557)))), inference(superposition, [status(thm), theory('equality')], [c_88, c_7072])).
% 8.22/2.81  tff(c_7107, plain, (![A_559]: (k2_funct_1(k6_partfun1(A_559))=k6_partfun1(A_559) | ~v1_funct_1(k6_partfun1(A_559)))), inference(demodulation, [status(thm), theory('equality')], [c_211, c_85, c_85, c_87, c_7093])).
% 8.22/2.81  tff(c_7122, plain, (![A_6]: (k2_funct_1(k6_partfun1(A_6))=k6_partfun1(A_6) | ~v1_funct_1('#skF_1') | A_6!='#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_4398, c_7107])).
% 8.22/2.81  tff(c_7126, plain, (![A_560]: (k2_funct_1(k6_partfun1(A_560))=k6_partfun1(A_560) | A_560!='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_3891, c_7122])).
% 8.22/2.81  tff(c_7151, plain, (![A_561]: (k6_partfun1(A_561)=k2_funct_1('#skF_1') | A_561!='#skF_1' | A_561!='#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_4398, c_7126])).
% 8.22/2.81  tff(c_7292, plain, (![A_561]: (v1_relat_1(k2_funct_1('#skF_1')) | A_561!='#skF_1' | A_561!='#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_7151, c_85])).
% 8.22/2.81  tff(c_7329, plain, (![A_561]: (A_561!='#skF_1' | A_561!='#skF_1')), inference(splitLeft, [status(thm)], [c_7292])).
% 8.22/2.81  tff(c_7400, plain, $false, inference(reflexivity, [status(thm), theory('equality')], [c_7329])).
% 8.22/2.81  tff(c_7401, plain, (v1_relat_1(k2_funct_1('#skF_1'))), inference(splitRight, [status(thm)], [c_7292])).
% 8.22/2.81  tff(c_8, plain, (![A_4]: (k1_relat_1(A_4)!=k1_xboole_0 | k1_xboole_0=A_4 | ~v1_relat_1(A_4))), inference(cnfTransformation, [status(thm)], [f_41])).
% 8.22/2.81  tff(c_3389, plain, (![A_4]: (k1_relat_1(A_4)!='#skF_3' | A_4='#skF_3' | ~v1_relat_1(A_4))), inference(demodulation, [status(thm), theory('equality')], [c_3383, c_3383, c_8])).
% 8.22/2.81  tff(c_4506, plain, (![A_4]: (k1_relat_1(A_4)!='#skF_1' | A_4='#skF_1' | ~v1_relat_1(A_4))), inference(demodulation, [status(thm), theory('equality')], [c_3881, c_3881, c_3389])).
% 8.22/2.81  tff(c_7415, plain, (k1_relat_1(k2_funct_1('#skF_1'))!='#skF_1' | k2_funct_1('#skF_1')='#skF_1'), inference(resolution, [status(thm)], [c_7401, c_4506])).
% 8.22/2.81  tff(c_7417, plain, (k1_relat_1(k2_funct_1('#skF_1'))!='#skF_1'), inference(splitLeft, [status(thm)], [c_7415])).
% 8.22/2.81  tff(c_7285, plain, (![A_561]: (k1_relat_1(k2_funct_1('#skF_1'))=A_561 | A_561!='#skF_1' | A_561!='#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_7151, c_87])).
% 8.22/2.81  tff(c_7513, plain, (k1_relat_1(k2_funct_1('#skF_1'))='#skF_1'), inference(reflexivity, [status(thm), theory('equality')], [c_7285])).
% 8.22/2.81  tff(c_7517, plain, $false, inference(negUnitSimplification, [status(thm)], [c_7417, c_7513])).
% 8.22/2.81  tff(c_7518, plain, (k2_funct_1('#skF_1')='#skF_1'), inference(splitRight, [status(thm)], [c_7415])).
% 8.22/2.81  tff(c_6284, plain, (![F_505, A_507, E_503, C_506, B_504, D_508]: (m1_subset_1(k1_partfun1(A_507, B_504, C_506, D_508, E_503, F_505), k1_zfmisc_1(k2_zfmisc_1(A_507, D_508))) | ~m1_subset_1(F_505, k1_zfmisc_1(k2_zfmisc_1(C_506, D_508))) | ~v1_funct_1(F_505) | ~m1_subset_1(E_503, k1_zfmisc_1(k2_zfmisc_1(A_507, B_504))) | ~v1_funct_1(E_503))), inference(cnfTransformation, [status(thm)], [f_136])).
% 8.22/2.81  tff(c_52, plain, (![A_38, B_39]: (k2_funct_2(A_38, B_39)=k2_funct_1(B_39) | ~m1_subset_1(B_39, k1_zfmisc_1(k2_zfmisc_1(A_38, A_38))) | ~v3_funct_2(B_39, A_38, A_38) | ~v1_funct_2(B_39, A_38, A_38) | ~v1_funct_1(B_39))), inference(cnfTransformation, [status(thm)], [f_146])).
% 8.22/2.81  tff(c_9070, plain, (![B_648, C_651, D_649, F_650, E_652]: (k2_funct_2(D_649, k1_partfun1(D_649, B_648, C_651, D_649, E_652, F_650))=k2_funct_1(k1_partfun1(D_649, B_648, C_651, D_649, E_652, F_650)) | ~v3_funct_2(k1_partfun1(D_649, B_648, C_651, D_649, E_652, F_650), D_649, D_649) | ~v1_funct_2(k1_partfun1(D_649, B_648, C_651, D_649, E_652, F_650), D_649, D_649) | ~v1_funct_1(k1_partfun1(D_649, B_648, C_651, D_649, E_652, F_650)) | ~m1_subset_1(F_650, k1_zfmisc_1(k2_zfmisc_1(C_651, D_649))) | ~v1_funct_1(F_650) | ~m1_subset_1(E_652, k1_zfmisc_1(k2_zfmisc_1(D_649, B_648))) | ~v1_funct_1(E_652))), inference(resolution, [status(thm)], [c_6284, c_52])).
% 8.22/2.81  tff(c_9072, plain, (k2_funct_2('#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_1'))=k2_funct_1(k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_1')) | ~v3_funct_2('#skF_1', '#skF_1', '#skF_1') | ~v1_funct_2(k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_1'), '#skF_1', '#skF_1') | ~v1_funct_1(k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_1')) | ~m1_subset_1('#skF_1', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v1_funct_1('#skF_1') | ~m1_subset_1('#skF_1', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v1_funct_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_5751, c_9070])).
% 8.22/2.81  tff(c_9074, plain, (k2_funct_2('#skF_1', '#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_3891, c_4548, c_3891, c_4548, c_3891, c_5751, c_3889, c_5751, c_3890, c_7518, c_5751, c_5751, c_9072])).
% 8.22/2.81  tff(c_3887, plain, (~r2_relset_1('#skF_1', '#skF_1', '#skF_1', k2_funct_2('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_3881, c_62])).
% 8.22/2.81  tff(c_4454, plain, (~r2_relset_1('#skF_1', '#skF_1', '#skF_1', k2_funct_2('#skF_1', '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_4377, c_3887])).
% 8.22/2.81  tff(c_9075, plain, (~r2_relset_1('#skF_1', '#skF_1', '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_9074, c_4454])).
% 8.22/2.81  tff(c_9078, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4592, c_9075])).
% 8.22/2.81  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.22/2.81  
% 8.22/2.81  Inference rules
% 8.22/2.81  ----------------------
% 8.22/2.81  #Ref     : 44
% 8.22/2.81  #Sup     : 2240
% 8.22/2.81  #Fact    : 0
% 8.22/2.81  #Define  : 0
% 8.22/2.81  #Split   : 53
% 8.22/2.81  #Chain   : 0
% 8.22/2.81  #Close   : 0
% 8.22/2.81  
% 8.22/2.81  Ordering : KBO
% 8.22/2.81  
% 8.22/2.81  Simplification rules
% 8.22/2.81  ----------------------
% 8.22/2.81  #Subsume      : 851
% 8.22/2.81  #Demod        : 1462
% 8.22/2.81  #Tautology    : 720
% 8.22/2.81  #SimpNegUnit  : 14
% 8.22/2.81  #BackRed      : 56
% 8.22/2.81  
% 8.22/2.81  #Partial instantiations: 0
% 8.22/2.81  #Strategies tried      : 1
% 8.22/2.81  
% 8.22/2.81  Timing (in seconds)
% 8.22/2.81  ----------------------
% 8.22/2.81  Preprocessing        : 0.37
% 8.22/2.81  Parsing              : 0.20
% 8.22/2.81  CNF conversion       : 0.03
% 8.22/2.81  Main loop            : 1.59
% 8.22/2.81  Inferencing          : 0.48
% 8.22/2.81  Reduction            : 0.63
% 8.22/2.81  Demodulation         : 0.46
% 8.22/2.81  BG Simplification    : 0.06
% 8.22/2.81  Subsumption          : 0.33
% 8.22/2.81  Abstraction          : 0.06
% 8.22/2.82  MUC search           : 0.00
% 8.22/2.82  Cooper               : 0.00
% 8.22/2.82  Total                : 2.02
% 8.22/2.82  Index Insertion      : 0.00
% 8.22/2.82  Index Deletion       : 0.00
% 8.22/2.82  Index Matching       : 0.00
% 8.22/2.82  BG Taut test         : 0.00
%------------------------------------------------------------------------------
