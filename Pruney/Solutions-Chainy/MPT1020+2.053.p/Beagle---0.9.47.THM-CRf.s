%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:15:58 EST 2020

% Result     : Theorem 3.44s
% Output     : CNFRefutation 3.44s
% Verified   : 
% Statistics : Number of formulae       :  112 ( 300 expanded)
%              Number of leaves         :   43 ( 126 expanded)
%              Depth                    :   11
%              Number of atoms          :  222 (1041 expanded)
%              Number of equality atoms :   54 ( 108 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v3_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > v1_partfun1 > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > k2_funct_2 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
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

tff(v1_partfun1,type,(
    v1_partfun1: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(v2_funct_2,type,(
    v2_funct_2: ( $i * $i ) > $o )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

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

tff(f_157,negated_conjecture,(
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

tff(f_69,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_61,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_135,axiom,(
    ! [A,B] :
      ( ( v1_funct_1(B)
        & v1_funct_2(B,A,A)
        & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
     => k1_relset_1(A,A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_funct_2)).

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

tff(f_81,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( ( v1_funct_1(C)
          & v3_funct_2(C,A,B) )
       => ( v1_funct_1(C)
          & v2_funct_1(C)
          & v2_funct_2(C,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_funct_2)).

tff(f_57,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_89,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A) )
     => ( v2_funct_2(B,A)
      <=> k2_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_funct_2)).

tff(f_127,axiom,(
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

tff(f_101,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( v1_funct_1(k1_partfun1(A,B,C,D,E,F))
        & m1_subset_1(k1_partfun1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).

tff(f_105,axiom,(
    ! [A] :
      ( v1_partfun1(k6_partfun1(A),A)
      & m1_subset_1(k6_partfun1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).

tff(f_115,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_125,axiom,(
    ! [A,B] :
      ( ( v1_funct_1(B)
        & v1_funct_2(B,A,A)
        & v3_funct_2(B,A,A)
        & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
     => k2_funct_2(A,B) = k2_funct_1(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_funct_2)).

tff(c_48,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_324,plain,(
    ! [A_94,B_95,D_96] :
      ( r2_relset_1(A_94,B_95,D_96,D_96)
      | ~ m1_subset_1(D_96,k1_zfmisc_1(k2_zfmisc_1(A_94,B_95))) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_333,plain,(
    r2_relset_1('#skF_1','#skF_1','#skF_3','#skF_3') ),
    inference(resolution,[status(thm)],[c_48,c_324])).

tff(c_54,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_52,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_413,plain,(
    ! [A_110,B_111,C_112] :
      ( k1_relset_1(A_110,B_111,C_112) = k1_relat_1(C_112)
      | ~ m1_subset_1(C_112,k1_zfmisc_1(k2_zfmisc_1(A_110,B_111))) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_425,plain,(
    k1_relset_1('#skF_1','#skF_1','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_48,c_413])).

tff(c_482,plain,(
    ! [A_124,B_125] :
      ( k1_relset_1(A_124,A_124,B_125) = A_124
      | ~ m1_subset_1(B_125,k1_zfmisc_1(k2_zfmisc_1(A_124,A_124)))
      | ~ v1_funct_2(B_125,A_124,A_124)
      | ~ v1_funct_1(B_125) ) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_491,plain,
    ( k1_relset_1('#skF_1','#skF_1','#skF_3') = '#skF_1'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_48,c_482])).

tff(c_499,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_425,c_491])).

tff(c_4,plain,(
    ! [A_4,B_5] : v1_relat_1(k2_zfmisc_1(A_4,B_5)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_76,plain,(
    ! [B_48,A_49] :
      ( v1_relat_1(B_48)
      | ~ m1_subset_1(B_48,k1_zfmisc_1(A_49))
      | ~ v1_relat_1(A_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_85,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_1')) ),
    inference(resolution,[status(thm)],[c_48,c_76])).

tff(c_94,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_85])).

tff(c_56,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_82,plain,
    ( v1_relat_1('#skF_2')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_1')) ),
    inference(resolution,[status(thm)],[c_56,c_76])).

tff(c_91,plain,(
    v1_relat_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_82])).

tff(c_62,plain,(
    v1_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_58,plain,(
    v3_funct_2('#skF_2','#skF_1','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_435,plain,(
    ! [C_113,A_114,B_115] :
      ( v2_funct_1(C_113)
      | ~ v3_funct_2(C_113,A_114,B_115)
      | ~ v1_funct_1(C_113)
      | ~ m1_subset_1(C_113,k1_zfmisc_1(k2_zfmisc_1(A_114,B_115))) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_441,plain,
    ( v2_funct_1('#skF_2')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_56,c_435])).

tff(c_448,plain,(
    v2_funct_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_58,c_441])).

tff(c_110,plain,(
    ! [C_55,B_56,A_57] :
      ( v5_relat_1(C_55,B_56)
      | ~ m1_subset_1(C_55,k1_zfmisc_1(k2_zfmisc_1(A_57,B_56))) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_121,plain,(
    v5_relat_1('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_56,c_110])).

tff(c_125,plain,(
    ! [B_60,A_61] :
      ( k2_relat_1(B_60) = A_61
      | ~ v2_funct_2(B_60,A_61)
      | ~ v5_relat_1(B_60,A_61)
      | ~ v1_relat_1(B_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_134,plain,
    ( k2_relat_1('#skF_2') = '#skF_1'
    | ~ v2_funct_2('#skF_2','#skF_1')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_121,c_125])).

tff(c_143,plain,
    ( k2_relat_1('#skF_2') = '#skF_1'
    | ~ v2_funct_2('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_91,c_134])).

tff(c_335,plain,(
    ~ v2_funct_2('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_143])).

tff(c_386,plain,(
    ! [C_107,B_108,A_109] :
      ( v2_funct_2(C_107,B_108)
      | ~ v3_funct_2(C_107,A_109,B_108)
      | ~ v1_funct_1(C_107)
      | ~ m1_subset_1(C_107,k1_zfmisc_1(k2_zfmisc_1(A_109,B_108))) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_392,plain,
    ( v2_funct_2('#skF_2','#skF_1')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_56,c_386])).

tff(c_399,plain,(
    v2_funct_2('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_58,c_392])).

tff(c_401,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_335,c_399])).

tff(c_402,plain,(
    k2_relat_1('#skF_2') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_143])).

tff(c_60,plain,(
    v1_funct_2('#skF_2','#skF_1','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_424,plain,(
    k1_relset_1('#skF_1','#skF_1','#skF_2') = k1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_56,c_413])).

tff(c_488,plain,
    ( k1_relset_1('#skF_1','#skF_1','#skF_2') = '#skF_1'
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_56,c_482])).

tff(c_496,plain,(
    k1_relat_1('#skF_2') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_424,c_488])).

tff(c_40,plain,(
    ! [A_39] : k6_relat_1(A_39) = k6_partfun1(A_39) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

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

tff(c_801,plain,(
    ! [A_180,B_181] :
      ( k2_funct_1(A_180) = B_181
      | k6_partfun1(k1_relat_1(A_180)) != k5_relat_1(A_180,B_181)
      | k2_relat_1(A_180) != k1_relat_1(B_181)
      | ~ v2_funct_1(A_180)
      | ~ v1_funct_1(B_181)
      | ~ v1_relat_1(B_181)
      | ~ v1_funct_1(A_180)
      | ~ v1_relat_1(A_180) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_6])).

tff(c_805,plain,(
    ! [B_181] :
      ( k2_funct_1('#skF_2') = B_181
      | k5_relat_1('#skF_2',B_181) != k6_partfun1('#skF_1')
      | k2_relat_1('#skF_2') != k1_relat_1(B_181)
      | ~ v2_funct_1('#skF_2')
      | ~ v1_funct_1(B_181)
      | ~ v1_relat_1(B_181)
      | ~ v1_funct_1('#skF_2')
      | ~ v1_relat_1('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_496,c_801])).

tff(c_811,plain,(
    ! [B_183] :
      ( k2_funct_1('#skF_2') = B_183
      | k5_relat_1('#skF_2',B_183) != k6_partfun1('#skF_1')
      | k1_relat_1(B_183) != '#skF_1'
      | ~ v1_funct_1(B_183)
      | ~ v1_relat_1(B_183) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_91,c_62,c_448,c_402,c_805])).

tff(c_817,plain,
    ( k2_funct_1('#skF_2') = '#skF_3'
    | k5_relat_1('#skF_2','#skF_3') != k6_partfun1('#skF_1')
    | k1_relat_1('#skF_3') != '#skF_1'
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_94,c_811])).

tff(c_827,plain,
    ( k2_funct_1('#skF_2') = '#skF_3'
    | k5_relat_1('#skF_2','#skF_3') != k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_499,c_817])).

tff(c_832,plain,(
    k5_relat_1('#skF_2','#skF_3') != k6_partfun1('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_827])).

tff(c_692,plain,(
    ! [F_163,B_161,C_160,E_162,D_165,A_164] :
      ( m1_subset_1(k1_partfun1(A_164,B_161,C_160,D_165,E_162,F_163),k1_zfmisc_1(k2_zfmisc_1(A_164,D_165)))
      | ~ m1_subset_1(F_163,k1_zfmisc_1(k2_zfmisc_1(C_160,D_165)))
      | ~ v1_funct_1(F_163)
      | ~ m1_subset_1(E_162,k1_zfmisc_1(k2_zfmisc_1(A_164,B_161)))
      | ~ v1_funct_1(E_162) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_34,plain,(
    ! [A_30] : m1_subset_1(k6_partfun1(A_30),k1_zfmisc_1(k2_zfmisc_1(A_30,A_30))) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_46,plain,(
    r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2','#skF_3'),k6_partfun1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_519,plain,(
    ! [D_127,C_128,A_129,B_130] :
      ( D_127 = C_128
      | ~ r2_relset_1(A_129,B_130,C_128,D_127)
      | ~ m1_subset_1(D_127,k1_zfmisc_1(k2_zfmisc_1(A_129,B_130)))
      | ~ m1_subset_1(C_128,k1_zfmisc_1(k2_zfmisc_1(A_129,B_130))) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_527,plain,
    ( k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2','#skF_3') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_46,c_519])).

tff(c_542,plain,
    ( k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2','#skF_3') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_527])).

tff(c_569,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_542])).

tff(c_705,plain,
    ( ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ v1_funct_1('#skF_3')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_692,c_569])).

tff(c_741,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_56,c_54,c_48,c_705])).

tff(c_742,plain,(
    k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2','#skF_3') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_542])).

tff(c_855,plain,(
    ! [C_190,F_189,A_188,B_186,D_185,E_187] :
      ( k1_partfun1(A_188,B_186,C_190,D_185,E_187,F_189) = k5_relat_1(E_187,F_189)
      | ~ m1_subset_1(F_189,k1_zfmisc_1(k2_zfmisc_1(C_190,D_185)))
      | ~ v1_funct_1(F_189)
      | ~ m1_subset_1(E_187,k1_zfmisc_1(k2_zfmisc_1(A_188,B_186)))
      | ~ v1_funct_1(E_187) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_861,plain,(
    ! [A_188,B_186,E_187] :
      ( k1_partfun1(A_188,B_186,'#skF_1','#skF_1',E_187,'#skF_3') = k5_relat_1(E_187,'#skF_3')
      | ~ v1_funct_1('#skF_3')
      | ~ m1_subset_1(E_187,k1_zfmisc_1(k2_zfmisc_1(A_188,B_186)))
      | ~ v1_funct_1(E_187) ) ),
    inference(resolution,[status(thm)],[c_48,c_855])).

tff(c_871,plain,(
    ! [A_191,B_192,E_193] :
      ( k1_partfun1(A_191,B_192,'#skF_1','#skF_1',E_193,'#skF_3') = k5_relat_1(E_193,'#skF_3')
      | ~ m1_subset_1(E_193,k1_zfmisc_1(k2_zfmisc_1(A_191,B_192)))
      | ~ v1_funct_1(E_193) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_861])).

tff(c_877,plain,
    ( k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2','#skF_3') = k5_relat_1('#skF_2','#skF_3')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_56,c_871])).

tff(c_884,plain,(
    k5_relat_1('#skF_2','#skF_3') = k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_742,c_877])).

tff(c_886,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_832,c_884])).

tff(c_887,plain,(
    k2_funct_1('#skF_2') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_827])).

tff(c_543,plain,(
    ! [A_131,B_132] :
      ( k2_funct_2(A_131,B_132) = k2_funct_1(B_132)
      | ~ m1_subset_1(B_132,k1_zfmisc_1(k2_zfmisc_1(A_131,A_131)))
      | ~ v3_funct_2(B_132,A_131,A_131)
      | ~ v1_funct_2(B_132,A_131,A_131)
      | ~ v1_funct_1(B_132) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_549,plain,
    ( k2_funct_2('#skF_1','#skF_2') = k2_funct_1('#skF_2')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_56,c_543])).

tff(c_556,plain,(
    k2_funct_2('#skF_1','#skF_2') = k2_funct_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_58,c_549])).

tff(c_44,plain,(
    ~ r2_relset_1('#skF_1','#skF_1','#skF_3',k2_funct_2('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_560,plain,(
    ~ r2_relset_1('#skF_1','#skF_1','#skF_3',k2_funct_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_556,c_44])).

tff(c_890,plain,(
    ~ r2_relset_1('#skF_1','#skF_1','#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_887,c_560])).

tff(c_894,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_333,c_890])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n005.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 19:38:32 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.44/1.58  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.44/1.59  
% 3.44/1.59  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.44/1.59  %$ r2_relset_1 > v3_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > v1_partfun1 > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > k2_funct_2 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 3.44/1.59  
% 3.44/1.59  %Foreground sorts:
% 3.44/1.59  
% 3.44/1.59  
% 3.44/1.59  %Background operators:
% 3.44/1.59  
% 3.44/1.59  
% 3.44/1.59  %Foreground operators:
% 3.44/1.59  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.44/1.59  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 3.44/1.59  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 3.44/1.59  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.44/1.59  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 3.44/1.59  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 3.44/1.59  tff(k2_funct_2, type, k2_funct_2: ($i * $i) > $i).
% 3.44/1.59  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.44/1.59  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.44/1.59  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.44/1.59  tff('#skF_2', type, '#skF_2': $i).
% 3.44/1.59  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 3.44/1.59  tff('#skF_3', type, '#skF_3': $i).
% 3.44/1.59  tff('#skF_1', type, '#skF_1': $i).
% 3.44/1.59  tff(v2_funct_2, type, v2_funct_2: ($i * $i) > $o).
% 3.44/1.59  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.44/1.59  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.44/1.59  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.44/1.59  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 3.44/1.59  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.44/1.59  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.44/1.59  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.44/1.59  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 3.44/1.59  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.44/1.59  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.44/1.59  tff(v3_funct_2, type, v3_funct_2: ($i * $i * $i) > $o).
% 3.44/1.59  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.44/1.59  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.44/1.59  
% 3.44/1.61  tff(f_157, negated_conjecture, ~(![A, B]: ((((v1_funct_1(B) & v1_funct_2(B, A, A)) & v3_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (![C]: ((((v1_funct_1(C) & v1_funct_2(C, A, A)) & v3_funct_2(C, A, A)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (r2_relset_1(A, A, k1_partfun1(A, A, A, A, B, C), k6_partfun1(A)) => r2_relset_1(A, A, C, k2_funct_2(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t87_funct_2)).
% 3.44/1.61  tff(f_69, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 3.44/1.61  tff(f_61, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.44/1.61  tff(f_135, axiom, (![A, B]: (((v1_funct_1(B) & v1_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (k1_relset_1(A, A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t67_funct_2)).
% 3.44/1.61  tff(f_34, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 3.44/1.61  tff(f_32, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 3.44/1.61  tff(f_81, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v3_funct_2(C, A, B)) => ((v1_funct_1(C) & v2_funct_1(C)) & v2_funct_2(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_funct_2)).
% 3.44/1.61  tff(f_57, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.44/1.61  tff(f_89, axiom, (![A, B]: ((v1_relat_1(B) & v5_relat_1(B, A)) => (v2_funct_2(B, A) <=> (k2_relat_1(B) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_funct_2)).
% 3.44/1.61  tff(f_127, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 3.44/1.61  tff(f_51, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (((v2_funct_1(A) & (k2_relat_1(A) = k1_relat_1(B))) & (k5_relat_1(A, B) = k6_relat_1(k1_relat_1(A)))) => (B = k2_funct_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_funct_1)).
% 3.44/1.61  tff(f_101, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (v1_funct_1(k1_partfun1(A, B, C, D, E, F)) & m1_subset_1(k1_partfun1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 3.44/1.61  tff(f_105, axiom, (![A]: (v1_partfun1(k6_partfun1(A), A) & m1_subset_1(k6_partfun1(A), k1_zfmisc_1(k2_zfmisc_1(A, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_partfun1)).
% 3.44/1.61  tff(f_115, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 3.44/1.61  tff(f_125, axiom, (![A, B]: ((((v1_funct_1(B) & v1_funct_2(B, A, A)) & v3_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (k2_funct_2(A, B) = k2_funct_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_funct_2)).
% 3.44/1.61  tff(c_48, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_157])).
% 3.44/1.61  tff(c_324, plain, (![A_94, B_95, D_96]: (r2_relset_1(A_94, B_95, D_96, D_96) | ~m1_subset_1(D_96, k1_zfmisc_1(k2_zfmisc_1(A_94, B_95))))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.44/1.61  tff(c_333, plain, (r2_relset_1('#skF_1', '#skF_1', '#skF_3', '#skF_3')), inference(resolution, [status(thm)], [c_48, c_324])).
% 3.44/1.61  tff(c_54, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_157])).
% 3.44/1.61  tff(c_52, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_157])).
% 3.44/1.61  tff(c_413, plain, (![A_110, B_111, C_112]: (k1_relset_1(A_110, B_111, C_112)=k1_relat_1(C_112) | ~m1_subset_1(C_112, k1_zfmisc_1(k2_zfmisc_1(A_110, B_111))))), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.44/1.61  tff(c_425, plain, (k1_relset_1('#skF_1', '#skF_1', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_48, c_413])).
% 3.44/1.61  tff(c_482, plain, (![A_124, B_125]: (k1_relset_1(A_124, A_124, B_125)=A_124 | ~m1_subset_1(B_125, k1_zfmisc_1(k2_zfmisc_1(A_124, A_124))) | ~v1_funct_2(B_125, A_124, A_124) | ~v1_funct_1(B_125))), inference(cnfTransformation, [status(thm)], [f_135])).
% 3.44/1.61  tff(c_491, plain, (k1_relset_1('#skF_1', '#skF_1', '#skF_3')='#skF_1' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_48, c_482])).
% 3.44/1.61  tff(c_499, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_425, c_491])).
% 3.44/1.61  tff(c_4, plain, (![A_4, B_5]: (v1_relat_1(k2_zfmisc_1(A_4, B_5)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.44/1.61  tff(c_76, plain, (![B_48, A_49]: (v1_relat_1(B_48) | ~m1_subset_1(B_48, k1_zfmisc_1(A_49)) | ~v1_relat_1(A_49))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.44/1.61  tff(c_85, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_1'))), inference(resolution, [status(thm)], [c_48, c_76])).
% 3.44/1.61  tff(c_94, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_85])).
% 3.44/1.61  tff(c_56, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_157])).
% 3.44/1.61  tff(c_82, plain, (v1_relat_1('#skF_2') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_1'))), inference(resolution, [status(thm)], [c_56, c_76])).
% 3.44/1.61  tff(c_91, plain, (v1_relat_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_82])).
% 3.44/1.61  tff(c_62, plain, (v1_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_157])).
% 3.44/1.61  tff(c_58, plain, (v3_funct_2('#skF_2', '#skF_1', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_157])).
% 3.44/1.61  tff(c_435, plain, (![C_113, A_114, B_115]: (v2_funct_1(C_113) | ~v3_funct_2(C_113, A_114, B_115) | ~v1_funct_1(C_113) | ~m1_subset_1(C_113, k1_zfmisc_1(k2_zfmisc_1(A_114, B_115))))), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.44/1.61  tff(c_441, plain, (v2_funct_1('#skF_2') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_56, c_435])).
% 3.44/1.61  tff(c_448, plain, (v2_funct_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_58, c_441])).
% 3.44/1.61  tff(c_110, plain, (![C_55, B_56, A_57]: (v5_relat_1(C_55, B_56) | ~m1_subset_1(C_55, k1_zfmisc_1(k2_zfmisc_1(A_57, B_56))))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.44/1.61  tff(c_121, plain, (v5_relat_1('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_56, c_110])).
% 3.44/1.61  tff(c_125, plain, (![B_60, A_61]: (k2_relat_1(B_60)=A_61 | ~v2_funct_2(B_60, A_61) | ~v5_relat_1(B_60, A_61) | ~v1_relat_1(B_60))), inference(cnfTransformation, [status(thm)], [f_89])).
% 3.44/1.61  tff(c_134, plain, (k2_relat_1('#skF_2')='#skF_1' | ~v2_funct_2('#skF_2', '#skF_1') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_121, c_125])).
% 3.44/1.61  tff(c_143, plain, (k2_relat_1('#skF_2')='#skF_1' | ~v2_funct_2('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_91, c_134])).
% 3.44/1.61  tff(c_335, plain, (~v2_funct_2('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_143])).
% 3.44/1.61  tff(c_386, plain, (![C_107, B_108, A_109]: (v2_funct_2(C_107, B_108) | ~v3_funct_2(C_107, A_109, B_108) | ~v1_funct_1(C_107) | ~m1_subset_1(C_107, k1_zfmisc_1(k2_zfmisc_1(A_109, B_108))))), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.44/1.61  tff(c_392, plain, (v2_funct_2('#skF_2', '#skF_1') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_56, c_386])).
% 3.44/1.61  tff(c_399, plain, (v2_funct_2('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_58, c_392])).
% 3.44/1.61  tff(c_401, plain, $false, inference(negUnitSimplification, [status(thm)], [c_335, c_399])).
% 3.44/1.61  tff(c_402, plain, (k2_relat_1('#skF_2')='#skF_1'), inference(splitRight, [status(thm)], [c_143])).
% 3.44/1.61  tff(c_60, plain, (v1_funct_2('#skF_2', '#skF_1', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_157])).
% 3.44/1.61  tff(c_424, plain, (k1_relset_1('#skF_1', '#skF_1', '#skF_2')=k1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_56, c_413])).
% 3.44/1.61  tff(c_488, plain, (k1_relset_1('#skF_1', '#skF_1', '#skF_2')='#skF_1' | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_56, c_482])).
% 3.44/1.61  tff(c_496, plain, (k1_relat_1('#skF_2')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_424, c_488])).
% 3.44/1.61  tff(c_40, plain, (![A_39]: (k6_relat_1(A_39)=k6_partfun1(A_39))), inference(cnfTransformation, [status(thm)], [f_127])).
% 3.44/1.61  tff(c_6, plain, (![A_6, B_8]: (k2_funct_1(A_6)=B_8 | k6_relat_1(k1_relat_1(A_6))!=k5_relat_1(A_6, B_8) | k2_relat_1(A_6)!=k1_relat_1(B_8) | ~v2_funct_1(A_6) | ~v1_funct_1(B_8) | ~v1_relat_1(B_8) | ~v1_funct_1(A_6) | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.44/1.61  tff(c_801, plain, (![A_180, B_181]: (k2_funct_1(A_180)=B_181 | k6_partfun1(k1_relat_1(A_180))!=k5_relat_1(A_180, B_181) | k2_relat_1(A_180)!=k1_relat_1(B_181) | ~v2_funct_1(A_180) | ~v1_funct_1(B_181) | ~v1_relat_1(B_181) | ~v1_funct_1(A_180) | ~v1_relat_1(A_180))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_6])).
% 3.44/1.61  tff(c_805, plain, (![B_181]: (k2_funct_1('#skF_2')=B_181 | k5_relat_1('#skF_2', B_181)!=k6_partfun1('#skF_1') | k2_relat_1('#skF_2')!=k1_relat_1(B_181) | ~v2_funct_1('#skF_2') | ~v1_funct_1(B_181) | ~v1_relat_1(B_181) | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_496, c_801])).
% 3.44/1.61  tff(c_811, plain, (![B_183]: (k2_funct_1('#skF_2')=B_183 | k5_relat_1('#skF_2', B_183)!=k6_partfun1('#skF_1') | k1_relat_1(B_183)!='#skF_1' | ~v1_funct_1(B_183) | ~v1_relat_1(B_183))), inference(demodulation, [status(thm), theory('equality')], [c_91, c_62, c_448, c_402, c_805])).
% 3.44/1.61  tff(c_817, plain, (k2_funct_1('#skF_2')='#skF_3' | k5_relat_1('#skF_2', '#skF_3')!=k6_partfun1('#skF_1') | k1_relat_1('#skF_3')!='#skF_1' | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_94, c_811])).
% 3.44/1.61  tff(c_827, plain, (k2_funct_1('#skF_2')='#skF_3' | k5_relat_1('#skF_2', '#skF_3')!=k6_partfun1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_499, c_817])).
% 3.44/1.61  tff(c_832, plain, (k5_relat_1('#skF_2', '#skF_3')!=k6_partfun1('#skF_1')), inference(splitLeft, [status(thm)], [c_827])).
% 3.44/1.61  tff(c_692, plain, (![F_163, B_161, C_160, E_162, D_165, A_164]: (m1_subset_1(k1_partfun1(A_164, B_161, C_160, D_165, E_162, F_163), k1_zfmisc_1(k2_zfmisc_1(A_164, D_165))) | ~m1_subset_1(F_163, k1_zfmisc_1(k2_zfmisc_1(C_160, D_165))) | ~v1_funct_1(F_163) | ~m1_subset_1(E_162, k1_zfmisc_1(k2_zfmisc_1(A_164, B_161))) | ~v1_funct_1(E_162))), inference(cnfTransformation, [status(thm)], [f_101])).
% 3.44/1.61  tff(c_34, plain, (![A_30]: (m1_subset_1(k6_partfun1(A_30), k1_zfmisc_1(k2_zfmisc_1(A_30, A_30))))), inference(cnfTransformation, [status(thm)], [f_105])).
% 3.44/1.61  tff(c_46, plain, (r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', '#skF_3'), k6_partfun1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_157])).
% 3.44/1.61  tff(c_519, plain, (![D_127, C_128, A_129, B_130]: (D_127=C_128 | ~r2_relset_1(A_129, B_130, C_128, D_127) | ~m1_subset_1(D_127, k1_zfmisc_1(k2_zfmisc_1(A_129, B_130))) | ~m1_subset_1(C_128, k1_zfmisc_1(k2_zfmisc_1(A_129, B_130))))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.44/1.61  tff(c_527, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', '#skF_3')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_46, c_519])).
% 3.44/1.61  tff(c_542, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', '#skF_3')=k6_partfun1('#skF_1') | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_527])).
% 3.44/1.61  tff(c_569, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_542])).
% 3.44/1.61  tff(c_705, plain, (~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v1_funct_1('#skF_3') | ~m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_692, c_569])).
% 3.44/1.61  tff(c_741, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_62, c_56, c_54, c_48, c_705])).
% 3.44/1.61  tff(c_742, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', '#skF_3')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_542])).
% 3.44/1.61  tff(c_855, plain, (![C_190, F_189, A_188, B_186, D_185, E_187]: (k1_partfun1(A_188, B_186, C_190, D_185, E_187, F_189)=k5_relat_1(E_187, F_189) | ~m1_subset_1(F_189, k1_zfmisc_1(k2_zfmisc_1(C_190, D_185))) | ~v1_funct_1(F_189) | ~m1_subset_1(E_187, k1_zfmisc_1(k2_zfmisc_1(A_188, B_186))) | ~v1_funct_1(E_187))), inference(cnfTransformation, [status(thm)], [f_115])).
% 3.44/1.61  tff(c_861, plain, (![A_188, B_186, E_187]: (k1_partfun1(A_188, B_186, '#skF_1', '#skF_1', E_187, '#skF_3')=k5_relat_1(E_187, '#skF_3') | ~v1_funct_1('#skF_3') | ~m1_subset_1(E_187, k1_zfmisc_1(k2_zfmisc_1(A_188, B_186))) | ~v1_funct_1(E_187))), inference(resolution, [status(thm)], [c_48, c_855])).
% 3.44/1.61  tff(c_871, plain, (![A_191, B_192, E_193]: (k1_partfun1(A_191, B_192, '#skF_1', '#skF_1', E_193, '#skF_3')=k5_relat_1(E_193, '#skF_3') | ~m1_subset_1(E_193, k1_zfmisc_1(k2_zfmisc_1(A_191, B_192))) | ~v1_funct_1(E_193))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_861])).
% 3.44/1.61  tff(c_877, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', '#skF_3')=k5_relat_1('#skF_2', '#skF_3') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_56, c_871])).
% 3.44/1.61  tff(c_884, plain, (k5_relat_1('#skF_2', '#skF_3')=k6_partfun1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_742, c_877])).
% 3.44/1.61  tff(c_886, plain, $false, inference(negUnitSimplification, [status(thm)], [c_832, c_884])).
% 3.44/1.61  tff(c_887, plain, (k2_funct_1('#skF_2')='#skF_3'), inference(splitRight, [status(thm)], [c_827])).
% 3.44/1.61  tff(c_543, plain, (![A_131, B_132]: (k2_funct_2(A_131, B_132)=k2_funct_1(B_132) | ~m1_subset_1(B_132, k1_zfmisc_1(k2_zfmisc_1(A_131, A_131))) | ~v3_funct_2(B_132, A_131, A_131) | ~v1_funct_2(B_132, A_131, A_131) | ~v1_funct_1(B_132))), inference(cnfTransformation, [status(thm)], [f_125])).
% 3.44/1.61  tff(c_549, plain, (k2_funct_2('#skF_1', '#skF_2')=k2_funct_1('#skF_2') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_56, c_543])).
% 3.44/1.61  tff(c_556, plain, (k2_funct_2('#skF_1', '#skF_2')=k2_funct_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_58, c_549])).
% 3.44/1.61  tff(c_44, plain, (~r2_relset_1('#skF_1', '#skF_1', '#skF_3', k2_funct_2('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_157])).
% 3.44/1.61  tff(c_560, plain, (~r2_relset_1('#skF_1', '#skF_1', '#skF_3', k2_funct_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_556, c_44])).
% 3.44/1.61  tff(c_890, plain, (~r2_relset_1('#skF_1', '#skF_1', '#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_887, c_560])).
% 3.44/1.61  tff(c_894, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_333, c_890])).
% 3.44/1.61  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.44/1.61  
% 3.44/1.61  Inference rules
% 3.44/1.61  ----------------------
% 3.44/1.61  #Ref     : 0
% 3.44/1.61  #Sup     : 177
% 3.44/1.61  #Fact    : 0
% 3.44/1.61  #Define  : 0
% 3.44/1.61  #Split   : 12
% 3.44/1.61  #Chain   : 0
% 3.44/1.61  #Close   : 0
% 3.44/1.61  
% 3.44/1.61  Ordering : KBO
% 3.44/1.61  
% 3.44/1.61  Simplification rules
% 3.44/1.61  ----------------------
% 3.44/1.61  #Subsume      : 0
% 3.44/1.61  #Demod        : 133
% 3.44/1.61  #Tautology    : 58
% 3.44/1.61  #SimpNegUnit  : 4
% 3.44/1.61  #BackRed      : 7
% 3.44/1.61  
% 3.44/1.61  #Partial instantiations: 0
% 3.44/1.61  #Strategies tried      : 1
% 3.44/1.61  
% 3.44/1.61  Timing (in seconds)
% 3.44/1.61  ----------------------
% 3.44/1.61  Preprocessing        : 0.37
% 3.44/1.61  Parsing              : 0.20
% 3.44/1.61  CNF conversion       : 0.02
% 3.44/1.61  Main loop            : 0.45
% 3.44/1.61  Inferencing          : 0.17
% 3.44/1.61  Reduction            : 0.15
% 3.44/1.61  Demodulation         : 0.11
% 3.44/1.61  BG Simplification    : 0.02
% 3.44/1.61  Subsumption          : 0.06
% 3.44/1.61  Abstraction          : 0.02
% 3.44/1.61  MUC search           : 0.00
% 3.44/1.61  Cooper               : 0.00
% 3.44/1.61  Total                : 0.85
% 3.44/1.61  Index Insertion      : 0.00
% 3.44/1.61  Index Deletion       : 0.00
% 3.44/1.61  Index Matching       : 0.00
% 3.44/1.61  BG Taut test         : 0.00
%------------------------------------------------------------------------------
