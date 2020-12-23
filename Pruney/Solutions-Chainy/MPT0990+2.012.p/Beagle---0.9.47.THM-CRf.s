%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:12:57 EST 2020

% Result     : Theorem 8.24s
% Output     : CNFRefutation 8.24s
% Verified   : 
% Statistics : Number of formulae       :  145 ( 556 expanded)
%              Number of leaves         :   48 ( 225 expanded)
%              Depth                    :   13
%              Number of atoms          :  370 (2606 expanded)
%              Number of equality atoms :  106 ( 794 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff('#skF_4',type,(
    '#skF_4': $i )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_274,negated_conjecture,(
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

tff(f_105,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_119,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_232,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( ( v2_funct_1(C)
          & k2_relset_1(A,B,C) = B )
       => ( v1_funct_1(k2_funct_1(C))
          & v1_funct_2(k2_funct_1(C),B,A)
          & m1_subset_1(k2_funct_1(C),k1_zfmisc_1(k2_zfmisc_1(B,A))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_funct_2)).

tff(f_61,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A)
        & v2_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A))
        & v2_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_funct_1)).

tff(f_49,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).

tff(f_248,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( ( k2_relset_1(A,B,C) = B
          & v2_funct_1(C) )
       => ( B = k1_xboole_0
          | ( k5_relat_1(C,k2_funct_1(C)) = k6_partfun1(A)
            & k5_relat_1(k2_funct_1(C),C) = k6_partfun1(B) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_funct_2)).

tff(f_76,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( ( v1_relat_1(B)
            & v1_funct_1(B) )
         => ( ( v2_funct_1(A)
              & v2_funct_1(B) )
           => v2_funct_1(k5_relat_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_funct_1)).

tff(f_171,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_161,axiom,(
    ! [A] :
      ( v1_partfun1(k6_partfun1(A),A)
      & m1_subset_1(k6_partfun1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_partfun1)).

tff(f_127,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_157,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( v1_funct_1(k1_partfun1(A,B,C,D,E,F))
        & m1_subset_1(k1_partfun1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).

tff(f_216,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ! [E] :
          ( ( v1_funct_1(E)
            & v1_funct_2(E,B,C)
            & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(B,C))) )
         => ( ( v2_funct_1(k1_partfun1(A,B,B,C,D,E))
              & k2_relset_1(A,B,D) = B )
           => ( ( C = k1_xboole_0
                & B != k1_xboole_0 )
              | ( v2_funct_1(D)
                & v2_funct_1(E) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_funct_2)).

tff(f_115,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).

tff(f_190,axiom,(
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

tff(f_173,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_93,axiom,(
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

tff(f_101,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => k2_funct_1(k2_funct_1(A)) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_funct_1)).

tff(c_90,plain,(
    k2_funct_1('#skF_3') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_274])).

tff(c_102,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_274])).

tff(c_168,plain,(
    ! [C_80,A_81,B_82] :
      ( v1_relat_1(C_80)
      | ~ m1_subset_1(C_80,k1_zfmisc_1(k2_zfmisc_1(A_81,B_82))) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_184,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_102,c_168])).

tff(c_106,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_274])).

tff(c_104,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_274])).

tff(c_465,plain,(
    ! [A_138,B_139,C_140] :
      ( k2_relset_1(A_138,B_139,C_140) = k2_relat_1(C_140)
      | ~ m1_subset_1(C_140,k1_zfmisc_1(k2_zfmisc_1(A_138,B_139))) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_481,plain,(
    k2_relset_1('#skF_2','#skF_1','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_102,c_465])).

tff(c_2013,plain,(
    ! [C_349,A_350,B_351] :
      ( v1_funct_1(k2_funct_1(C_349))
      | k2_relset_1(A_350,B_351,C_349) != B_351
      | ~ v2_funct_1(C_349)
      | ~ m1_subset_1(C_349,k1_zfmisc_1(k2_zfmisc_1(A_350,B_351)))
      | ~ v1_funct_2(C_349,A_350,B_351)
      | ~ v1_funct_1(C_349) ) ),
    inference(cnfTransformation,[status(thm)],[f_232])).

tff(c_2023,plain,
    ( v1_funct_1(k2_funct_1('#skF_4'))
    | k2_relset_1('#skF_2','#skF_1','#skF_4') != '#skF_1'
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_102,c_2013])).

tff(c_2032,plain,
    ( v1_funct_1(k2_funct_1('#skF_4'))
    | k2_relat_1('#skF_4') != '#skF_1'
    | ~ v2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_106,c_104,c_481,c_2023])).

tff(c_2036,plain,(
    ~ v2_funct_1('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_2032])).

tff(c_94,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_274])).

tff(c_112,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_274])).

tff(c_110,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_274])).

tff(c_108,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_274])).

tff(c_185,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_108,c_168])).

tff(c_96,plain,(
    v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_274])).

tff(c_20,plain,(
    ! [A_8] :
      ( v2_funct_1(k2_funct_1(A_8))
      | ~ v2_funct_1(A_8)
      | ~ v1_funct_1(A_8)
      | ~ v1_relat_1(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_18,plain,(
    ! [A_7] :
      ( v1_relat_1(k2_funct_1(A_7))
      | ~ v1_funct_1(A_7)
      | ~ v1_relat_1(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_100,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_274])).

tff(c_2026,plain,
    ( v1_funct_1(k2_funct_1('#skF_3'))
    | k2_relset_1('#skF_1','#skF_2','#skF_3') != '#skF_2'
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_108,c_2013])).

tff(c_2035,plain,(
    v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_112,c_110,c_96,c_100,c_2026])).

tff(c_92,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_274])).

tff(c_4359,plain,(
    ! [A_541,C_542,B_543] :
      ( k6_partfun1(A_541) = k5_relat_1(C_542,k2_funct_1(C_542))
      | k1_xboole_0 = B_543
      | ~ v2_funct_1(C_542)
      | k2_relset_1(A_541,B_543,C_542) != B_543
      | ~ m1_subset_1(C_542,k1_zfmisc_1(k2_zfmisc_1(A_541,B_543)))
      | ~ v1_funct_2(C_542,A_541,B_543)
      | ~ v1_funct_1(C_542) ) ),
    inference(cnfTransformation,[status(thm)],[f_248])).

tff(c_4370,plain,
    ( k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_partfun1('#skF_1')
    | k1_xboole_0 = '#skF_2'
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1('#skF_1','#skF_2','#skF_3') != '#skF_2'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_108,c_4359])).

tff(c_4381,plain,
    ( k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_partfun1('#skF_1')
    | k1_xboole_0 = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_112,c_110,c_100,c_96,c_4370])).

tff(c_4382,plain,(
    k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_partfun1('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_92,c_4381])).

tff(c_26,plain,(
    ! [A_9,B_11] :
      ( v2_funct_1(k5_relat_1(A_9,B_11))
      | ~ v2_funct_1(B_11)
      | ~ v2_funct_1(A_9)
      | ~ v1_funct_1(B_11)
      | ~ v1_relat_1(B_11)
      | ~ v1_funct_1(A_9)
      | ~ v1_relat_1(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_4386,plain,
    ( v2_funct_1(k6_partfun1('#skF_1'))
    | ~ v2_funct_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_4382,c_26])).

tff(c_4390,plain,
    ( v2_funct_1(k6_partfun1('#skF_1'))
    | ~ v2_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_185,c_112,c_2035,c_96,c_4386])).

tff(c_4392,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_4390])).

tff(c_4395,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_18,c_4392])).

tff(c_4399,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_185,c_112,c_4395])).

tff(c_4400,plain,
    ( ~ v2_funct_1(k2_funct_1('#skF_3'))
    | v2_funct_1(k6_partfun1('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_4390])).

tff(c_4413,plain,(
    ~ v2_funct_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_4400])).

tff(c_4416,plain,
    ( ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_20,c_4413])).

tff(c_4420,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_185,c_112,c_96,c_4416])).

tff(c_4421,plain,(
    v2_funct_1(k6_partfun1('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_4400])).

tff(c_1469,plain,(
    ! [C_312,F_311,D_308,E_307,B_309,A_310] :
      ( k1_partfun1(A_310,B_309,C_312,D_308,E_307,F_311) = k5_relat_1(E_307,F_311)
      | ~ m1_subset_1(F_311,k1_zfmisc_1(k2_zfmisc_1(C_312,D_308)))
      | ~ v1_funct_1(F_311)
      | ~ m1_subset_1(E_307,k1_zfmisc_1(k2_zfmisc_1(A_310,B_309)))
      | ~ v1_funct_1(E_307) ) ),
    inference(cnfTransformation,[status(thm)],[f_171])).

tff(c_1476,plain,(
    ! [A_310,B_309,E_307] :
      ( k1_partfun1(A_310,B_309,'#skF_2','#skF_1',E_307,'#skF_4') = k5_relat_1(E_307,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_307,k1_zfmisc_1(k2_zfmisc_1(A_310,B_309)))
      | ~ v1_funct_1(E_307) ) ),
    inference(resolution,[status(thm)],[c_102,c_1469])).

tff(c_1515,plain,(
    ! [A_317,B_318,E_319] :
      ( k1_partfun1(A_317,B_318,'#skF_2','#skF_1',E_319,'#skF_4') = k5_relat_1(E_319,'#skF_4')
      | ~ m1_subset_1(E_319,k1_zfmisc_1(k2_zfmisc_1(A_317,B_318)))
      | ~ v1_funct_1(E_319) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_106,c_1476])).

tff(c_1528,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_108,c_1515])).

tff(c_1536,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_112,c_1528])).

tff(c_64,plain,(
    ! [A_41] : m1_subset_1(k6_partfun1(A_41),k1_zfmisc_1(k2_zfmisc_1(A_41,A_41))) ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_98,plain,(
    r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k6_partfun1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_274])).

tff(c_960,plain,(
    ! [D_235,C_236,A_237,B_238] :
      ( D_235 = C_236
      | ~ r2_relset_1(A_237,B_238,C_236,D_235)
      | ~ m1_subset_1(D_235,k1_zfmisc_1(k2_zfmisc_1(A_237,B_238)))
      | ~ m1_subset_1(C_236,k1_zfmisc_1(k2_zfmisc_1(A_237,B_238))) ) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_970,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_98,c_960])).

tff(c_987,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_970])).

tff(c_1013,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_987])).

tff(c_1544,plain,(
    ~ m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1536,c_1013])).

tff(c_1897,plain,(
    ! [C_345,F_344,A_343,E_346,D_347,B_348] :
      ( m1_subset_1(k1_partfun1(A_343,B_348,C_345,D_347,E_346,F_344),k1_zfmisc_1(k2_zfmisc_1(A_343,D_347)))
      | ~ m1_subset_1(F_344,k1_zfmisc_1(k2_zfmisc_1(C_345,D_347)))
      | ~ v1_funct_1(F_344)
      | ~ m1_subset_1(E_346,k1_zfmisc_1(k2_zfmisc_1(A_343,B_348)))
      | ~ v1_funct_1(E_346) ) ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_1970,plain,
    ( m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1536,c_1897])).

tff(c_2001,plain,(
    m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_112,c_108,c_106,c_102,c_1970])).

tff(c_2003,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1544,c_2001])).

tff(c_2004,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_987])).

tff(c_5255,plain,(
    ! [B_568,C_566,A_567,D_569,E_570] :
      ( k1_xboole_0 = C_566
      | v2_funct_1(E_570)
      | k2_relset_1(A_567,B_568,D_569) != B_568
      | ~ v2_funct_1(k1_partfun1(A_567,B_568,B_568,C_566,D_569,E_570))
      | ~ m1_subset_1(E_570,k1_zfmisc_1(k2_zfmisc_1(B_568,C_566)))
      | ~ v1_funct_2(E_570,B_568,C_566)
      | ~ v1_funct_1(E_570)
      | ~ m1_subset_1(D_569,k1_zfmisc_1(k2_zfmisc_1(A_567,B_568)))
      | ~ v1_funct_2(D_569,A_567,B_568)
      | ~ v1_funct_1(D_569) ) ),
    inference(cnfTransformation,[status(thm)],[f_216])).

tff(c_5259,plain,
    ( k1_xboole_0 = '#skF_1'
    | v2_funct_1('#skF_4')
    | k2_relset_1('#skF_1','#skF_2','#skF_3') != '#skF_2'
    | ~ v2_funct_1(k6_partfun1('#skF_1'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_2004,c_5255])).

tff(c_5264,plain,
    ( k1_xboole_0 = '#skF_1'
    | v2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_112,c_110,c_108,c_106,c_104,c_102,c_4421,c_100,c_5259])).

tff(c_5266,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2036,c_94,c_5264])).

tff(c_5268,plain,(
    v2_funct_1('#skF_4') ),
    inference(splitRight,[status(thm)],[c_2032])).

tff(c_478,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_108,c_465])).

tff(c_483,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_478])).

tff(c_381,plain,(
    ! [A_125,B_126,C_127] :
      ( k1_relset_1(A_125,B_126,C_127) = k1_relat_1(C_127)
      | ~ m1_subset_1(C_127,k1_zfmisc_1(k2_zfmisc_1(A_125,B_126))) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_397,plain,(
    k1_relset_1('#skF_2','#skF_1','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_102,c_381])).

tff(c_846,plain,(
    ! [B_222,A_223,C_224] :
      ( k1_xboole_0 = B_222
      | k1_relset_1(A_223,B_222,C_224) = A_223
      | ~ v1_funct_2(C_224,A_223,B_222)
      | ~ m1_subset_1(C_224,k1_zfmisc_1(k2_zfmisc_1(A_223,B_222))) ) ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_856,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_relset_1('#skF_2','#skF_1','#skF_4') = '#skF_2'
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_102,c_846])).

tff(c_865,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_relat_1('#skF_4') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_397,c_856])).

tff(c_866,plain,(
    k1_relat_1('#skF_4') = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_94,c_865])).

tff(c_5267,plain,
    ( k2_relat_1('#skF_4') != '#skF_1'
    | v1_funct_1(k2_funct_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_2032])).

tff(c_5269,plain,(
    k2_relat_1('#skF_4') != '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_5267])).

tff(c_367,plain,(
    ! [A_122,B_123,D_124] :
      ( r2_relset_1(A_122,B_123,D_124,D_124)
      | ~ m1_subset_1(D_124,k1_zfmisc_1(k2_zfmisc_1(A_122,B_123))) ) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_378,plain,(
    ! [A_41] : r2_relset_1(A_41,A_41,k6_partfun1(A_41),k6_partfun1(A_41)) ),
    inference(resolution,[status(thm)],[c_64,c_367])).

tff(c_7134,plain,(
    ! [A_690,B_691,C_692,D_693] :
      ( k2_relset_1(A_690,B_691,C_692) = B_691
      | ~ r2_relset_1(B_691,B_691,k1_partfun1(B_691,A_690,A_690,B_691,D_693,C_692),k6_partfun1(B_691))
      | ~ m1_subset_1(D_693,k1_zfmisc_1(k2_zfmisc_1(B_691,A_690)))
      | ~ v1_funct_2(D_693,B_691,A_690)
      | ~ v1_funct_1(D_693)
      | ~ m1_subset_1(C_692,k1_zfmisc_1(k2_zfmisc_1(A_690,B_691)))
      | ~ v1_funct_2(C_692,A_690,B_691)
      | ~ v1_funct_1(C_692) ) ),
    inference(cnfTransformation,[status(thm)],[f_190])).

tff(c_7140,plain,
    ( k2_relset_1('#skF_2','#skF_1','#skF_4') = '#skF_1'
    | ~ r2_relset_1('#skF_1','#skF_1',k6_partfun1('#skF_1'),k6_partfun1('#skF_1'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_2004,c_7134])).

tff(c_7144,plain,(
    k2_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_106,c_104,c_102,c_112,c_110,c_108,c_378,c_481,c_7140])).

tff(c_7146,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_5269,c_7144])).

tff(c_7148,plain,(
    k2_relat_1('#skF_4') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_5267])).

tff(c_68,plain,(
    ! [A_48] : k6_relat_1(A_48) = k6_partfun1(A_48) ),
    inference(cnfTransformation,[status(thm)],[f_173])).

tff(c_28,plain,(
    ! [A_12,B_14] :
      ( k2_funct_1(A_12) = B_14
      | k6_relat_1(k2_relat_1(A_12)) != k5_relat_1(B_14,A_12)
      | k2_relat_1(B_14) != k1_relat_1(A_12)
      | ~ v2_funct_1(A_12)
      | ~ v1_funct_1(B_14)
      | ~ v1_relat_1(B_14)
      | ~ v1_funct_1(A_12)
      | ~ v1_relat_1(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_7251,plain,(
    ! [A_704,B_705] :
      ( k2_funct_1(A_704) = B_705
      | k6_partfun1(k2_relat_1(A_704)) != k5_relat_1(B_705,A_704)
      | k2_relat_1(B_705) != k1_relat_1(A_704)
      | ~ v2_funct_1(A_704)
      | ~ v1_funct_1(B_705)
      | ~ v1_relat_1(B_705)
      | ~ v1_funct_1(A_704)
      | ~ v1_relat_1(A_704) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_28])).

tff(c_7253,plain,(
    ! [B_705] :
      ( k2_funct_1('#skF_4') = B_705
      | k5_relat_1(B_705,'#skF_4') != k6_partfun1('#skF_1')
      | k2_relat_1(B_705) != k1_relat_1('#skF_4')
      | ~ v2_funct_1('#skF_4')
      | ~ v1_funct_1(B_705)
      | ~ v1_relat_1(B_705)
      | ~ v1_funct_1('#skF_4')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_7148,c_7251])).

tff(c_7412,plain,(
    ! [B_717] :
      ( k2_funct_1('#skF_4') = B_717
      | k5_relat_1(B_717,'#skF_4') != k6_partfun1('#skF_1')
      | k2_relat_1(B_717) != '#skF_2'
      | ~ v1_funct_1(B_717)
      | ~ v1_relat_1(B_717) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_184,c_106,c_5268,c_866,c_7253])).

tff(c_7439,plain,
    ( k2_funct_1('#skF_4') = '#skF_3'
    | k5_relat_1('#skF_3','#skF_4') != k6_partfun1('#skF_1')
    | k2_relat_1('#skF_3') != '#skF_2'
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_185,c_7412])).

tff(c_7456,plain,
    ( k2_funct_1('#skF_4') = '#skF_3'
    | k5_relat_1('#skF_3','#skF_4') != k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_112,c_483,c_7439])).

tff(c_7461,plain,(
    k5_relat_1('#skF_3','#skF_4') != k6_partfun1('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_7456])).

tff(c_7973,plain,(
    ! [D_775,C_779,F_778,B_776,E_774,A_777] :
      ( k1_partfun1(A_777,B_776,C_779,D_775,E_774,F_778) = k5_relat_1(E_774,F_778)
      | ~ m1_subset_1(F_778,k1_zfmisc_1(k2_zfmisc_1(C_779,D_775)))
      | ~ v1_funct_1(F_778)
      | ~ m1_subset_1(E_774,k1_zfmisc_1(k2_zfmisc_1(A_777,B_776)))
      | ~ v1_funct_1(E_774) ) ),
    inference(cnfTransformation,[status(thm)],[f_171])).

tff(c_7982,plain,(
    ! [A_777,B_776,E_774] :
      ( k1_partfun1(A_777,B_776,'#skF_2','#skF_1',E_774,'#skF_4') = k5_relat_1(E_774,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_774,k1_zfmisc_1(k2_zfmisc_1(A_777,B_776)))
      | ~ v1_funct_1(E_774) ) ),
    inference(resolution,[status(thm)],[c_102,c_7973])).

tff(c_8101,plain,(
    ! [A_787,B_788,E_789] :
      ( k1_partfun1(A_787,B_788,'#skF_2','#skF_1',E_789,'#skF_4') = k5_relat_1(E_789,'#skF_4')
      | ~ m1_subset_1(E_789,k1_zfmisc_1(k2_zfmisc_1(A_787,B_788)))
      | ~ v1_funct_1(E_789) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_106,c_7982])).

tff(c_8117,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_108,c_8101])).

tff(c_8126,plain,(
    k5_relat_1('#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_112,c_2004,c_8117])).

tff(c_8128,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_7461,c_8126])).

tff(c_8129,plain,(
    k2_funct_1('#skF_4') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_7456])).

tff(c_30,plain,(
    ! [A_15] :
      ( k2_funct_1(k2_funct_1(A_15)) = A_15
      | ~ v2_funct_1(A_15)
      | ~ v1_funct_1(A_15)
      | ~ v1_relat_1(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_8137,plain,
    ( k2_funct_1('#skF_3') = '#skF_4'
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_8129,c_30])).

tff(c_8150,plain,(
    k2_funct_1('#skF_3') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_184,c_106,c_5268,c_8137])).

tff(c_8152,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_90,c_8150])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n016.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 16:11:49 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.24/3.01  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.24/3.03  
% 8.24/3.03  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.24/3.03  %$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 8.24/3.03  
% 8.24/3.03  %Foreground sorts:
% 8.24/3.03  
% 8.24/3.03  
% 8.24/3.03  %Background operators:
% 8.24/3.03  
% 8.24/3.03  
% 8.24/3.03  %Foreground operators:
% 8.24/3.03  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 8.24/3.03  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 8.24/3.03  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 8.24/3.03  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 8.24/3.03  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.24/3.03  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 8.24/3.03  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 8.24/3.03  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 8.24/3.03  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 8.24/3.03  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 8.24/3.03  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 8.24/3.03  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 8.24/3.03  tff('#skF_2', type, '#skF_2': $i).
% 8.24/3.03  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 8.24/3.03  tff('#skF_3', type, '#skF_3': $i).
% 8.24/3.03  tff('#skF_1', type, '#skF_1': $i).
% 8.24/3.03  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 8.24/3.03  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 8.24/3.03  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 8.24/3.03  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 8.24/3.03  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.24/3.03  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 8.24/3.03  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 8.24/3.03  tff('#skF_4', type, '#skF_4': $i).
% 8.24/3.03  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 8.24/3.03  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.24/3.03  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 8.24/3.03  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 8.24/3.03  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 8.24/3.03  
% 8.24/3.05  tff(f_274, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => ((((k2_relset_1(A, B, C) = B) & r2_relset_1(A, A, k1_partfun1(A, B, B, A, C, D), k6_partfun1(A))) & v2_funct_1(C)) => (((A = k1_xboole_0) | (B = k1_xboole_0)) | (D = k2_funct_1(C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_funct_2)).
% 8.24/3.05  tff(f_105, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 8.24/3.05  tff(f_119, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 8.24/3.05  tff(f_232, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((v2_funct_1(C) & (k2_relset_1(A, B, C) = B)) => ((v1_funct_1(k2_funct_1(C)) & v1_funct_2(k2_funct_1(C), B, A)) & m1_subset_1(k2_funct_1(C), k1_zfmisc_1(k2_zfmisc_1(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_funct_2)).
% 8.24/3.05  tff(f_61, axiom, (![A]: (((v1_relat_1(A) & v1_funct_1(A)) & v2_funct_1(A)) => ((v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))) & v2_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_funct_1)).
% 8.24/3.05  tff(f_49, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 8.24/3.05  tff(f_248, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((k2_relset_1(A, B, C) = B) & v2_funct_1(C)) => ((B = k1_xboole_0) | ((k5_relat_1(C, k2_funct_1(C)) = k6_partfun1(A)) & (k5_relat_1(k2_funct_1(C), C) = k6_partfun1(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t35_funct_2)).
% 8.24/3.05  tff(f_76, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((v2_funct_1(A) & v2_funct_1(B)) => v2_funct_1(k5_relat_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_funct_1)).
% 8.24/3.05  tff(f_171, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 8.24/3.05  tff(f_161, axiom, (![A]: (v1_partfun1(k6_partfun1(A), A) & m1_subset_1(k6_partfun1(A), k1_zfmisc_1(k2_zfmisc_1(A, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_partfun1)).
% 8.24/3.05  tff(f_127, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 8.24/3.05  tff(f_157, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (v1_funct_1(k1_partfun1(A, B, C, D, E, F)) & m1_subset_1(k1_partfun1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 8.24/3.05  tff(f_216, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, B, C)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => ((v2_funct_1(k1_partfun1(A, B, B, C, D, E)) & (k2_relset_1(A, B, D) = B)) => (((C = k1_xboole_0) & ~(B = k1_xboole_0)) | (v2_funct_1(D) & v2_funct_1(E)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t30_funct_2)).
% 8.24/3.05  tff(f_115, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 8.24/3.05  tff(f_145, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 8.24/3.05  tff(f_190, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (r2_relset_1(B, B, k1_partfun1(B, A, A, B, D, C), k6_partfun1(B)) => (k2_relset_1(A, B, C) = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t24_funct_2)).
% 8.24/3.05  tff(f_173, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 8.24/3.05  tff(f_93, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (((v2_funct_1(A) & (k2_relat_1(B) = k1_relat_1(A))) & (k5_relat_1(B, A) = k6_relat_1(k2_relat_1(A)))) => (B = k2_funct_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_funct_1)).
% 8.24/3.05  tff(f_101, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => (k2_funct_1(k2_funct_1(A)) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_funct_1)).
% 8.24/3.05  tff(c_90, plain, (k2_funct_1('#skF_3')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_274])).
% 8.24/3.05  tff(c_102, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_274])).
% 8.24/3.05  tff(c_168, plain, (![C_80, A_81, B_82]: (v1_relat_1(C_80) | ~m1_subset_1(C_80, k1_zfmisc_1(k2_zfmisc_1(A_81, B_82))))), inference(cnfTransformation, [status(thm)], [f_105])).
% 8.24/3.05  tff(c_184, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_102, c_168])).
% 8.24/3.05  tff(c_106, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_274])).
% 8.24/3.05  tff(c_104, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_274])).
% 8.24/3.05  tff(c_465, plain, (![A_138, B_139, C_140]: (k2_relset_1(A_138, B_139, C_140)=k2_relat_1(C_140) | ~m1_subset_1(C_140, k1_zfmisc_1(k2_zfmisc_1(A_138, B_139))))), inference(cnfTransformation, [status(thm)], [f_119])).
% 8.24/3.05  tff(c_481, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_102, c_465])).
% 8.24/3.05  tff(c_2013, plain, (![C_349, A_350, B_351]: (v1_funct_1(k2_funct_1(C_349)) | k2_relset_1(A_350, B_351, C_349)!=B_351 | ~v2_funct_1(C_349) | ~m1_subset_1(C_349, k1_zfmisc_1(k2_zfmisc_1(A_350, B_351))) | ~v1_funct_2(C_349, A_350, B_351) | ~v1_funct_1(C_349))), inference(cnfTransformation, [status(thm)], [f_232])).
% 8.24/3.05  tff(c_2023, plain, (v1_funct_1(k2_funct_1('#skF_4')) | k2_relset_1('#skF_2', '#skF_1', '#skF_4')!='#skF_1' | ~v2_funct_1('#skF_4') | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_102, c_2013])).
% 8.24/3.05  tff(c_2032, plain, (v1_funct_1(k2_funct_1('#skF_4')) | k2_relat_1('#skF_4')!='#skF_1' | ~v2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_106, c_104, c_481, c_2023])).
% 8.24/3.05  tff(c_2036, plain, (~v2_funct_1('#skF_4')), inference(splitLeft, [status(thm)], [c_2032])).
% 8.24/3.05  tff(c_94, plain, (k1_xboole_0!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_274])).
% 8.24/3.05  tff(c_112, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_274])).
% 8.24/3.05  tff(c_110, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_274])).
% 8.24/3.05  tff(c_108, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_274])).
% 8.24/3.05  tff(c_185, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_108, c_168])).
% 8.24/3.05  tff(c_96, plain, (v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_274])).
% 8.24/3.05  tff(c_20, plain, (![A_8]: (v2_funct_1(k2_funct_1(A_8)) | ~v2_funct_1(A_8) | ~v1_funct_1(A_8) | ~v1_relat_1(A_8))), inference(cnfTransformation, [status(thm)], [f_61])).
% 8.24/3.05  tff(c_18, plain, (![A_7]: (v1_relat_1(k2_funct_1(A_7)) | ~v1_funct_1(A_7) | ~v1_relat_1(A_7))), inference(cnfTransformation, [status(thm)], [f_49])).
% 8.24/3.05  tff(c_100, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_2'), inference(cnfTransformation, [status(thm)], [f_274])).
% 8.24/3.05  tff(c_2026, plain, (v1_funct_1(k2_funct_1('#skF_3')) | k2_relset_1('#skF_1', '#skF_2', '#skF_3')!='#skF_2' | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_108, c_2013])).
% 8.24/3.05  tff(c_2035, plain, (v1_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_112, c_110, c_96, c_100, c_2026])).
% 8.24/3.05  tff(c_92, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_274])).
% 8.24/3.05  tff(c_4359, plain, (![A_541, C_542, B_543]: (k6_partfun1(A_541)=k5_relat_1(C_542, k2_funct_1(C_542)) | k1_xboole_0=B_543 | ~v2_funct_1(C_542) | k2_relset_1(A_541, B_543, C_542)!=B_543 | ~m1_subset_1(C_542, k1_zfmisc_1(k2_zfmisc_1(A_541, B_543))) | ~v1_funct_2(C_542, A_541, B_543) | ~v1_funct_1(C_542))), inference(cnfTransformation, [status(thm)], [f_248])).
% 8.24/3.05  tff(c_4370, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_partfun1('#skF_1') | k1_xboole_0='#skF_2' | ~v2_funct_1('#skF_3') | k2_relset_1('#skF_1', '#skF_2', '#skF_3')!='#skF_2' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_108, c_4359])).
% 8.24/3.05  tff(c_4381, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_partfun1('#skF_1') | k1_xboole_0='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_112, c_110, c_100, c_96, c_4370])).
% 8.24/3.05  tff(c_4382, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_partfun1('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_92, c_4381])).
% 8.24/3.05  tff(c_26, plain, (![A_9, B_11]: (v2_funct_1(k5_relat_1(A_9, B_11)) | ~v2_funct_1(B_11) | ~v2_funct_1(A_9) | ~v1_funct_1(B_11) | ~v1_relat_1(B_11) | ~v1_funct_1(A_9) | ~v1_relat_1(A_9))), inference(cnfTransformation, [status(thm)], [f_76])).
% 8.24/3.05  tff(c_4386, plain, (v2_funct_1(k6_partfun1('#skF_1')) | ~v2_funct_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_4382, c_26])).
% 8.24/3.05  tff(c_4390, plain, (v2_funct_1(k6_partfun1('#skF_1')) | ~v2_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_185, c_112, c_2035, c_96, c_4386])).
% 8.24/3.05  tff(c_4392, plain, (~v1_relat_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_4390])).
% 8.24/3.05  tff(c_4395, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_18, c_4392])).
% 8.24/3.05  tff(c_4399, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_185, c_112, c_4395])).
% 8.24/3.05  tff(c_4400, plain, (~v2_funct_1(k2_funct_1('#skF_3')) | v2_funct_1(k6_partfun1('#skF_1'))), inference(splitRight, [status(thm)], [c_4390])).
% 8.24/3.05  tff(c_4413, plain, (~v2_funct_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_4400])).
% 8.24/3.05  tff(c_4416, plain, (~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_20, c_4413])).
% 8.24/3.05  tff(c_4420, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_185, c_112, c_96, c_4416])).
% 8.24/3.05  tff(c_4421, plain, (v2_funct_1(k6_partfun1('#skF_1'))), inference(splitRight, [status(thm)], [c_4400])).
% 8.24/3.05  tff(c_1469, plain, (![C_312, F_311, D_308, E_307, B_309, A_310]: (k1_partfun1(A_310, B_309, C_312, D_308, E_307, F_311)=k5_relat_1(E_307, F_311) | ~m1_subset_1(F_311, k1_zfmisc_1(k2_zfmisc_1(C_312, D_308))) | ~v1_funct_1(F_311) | ~m1_subset_1(E_307, k1_zfmisc_1(k2_zfmisc_1(A_310, B_309))) | ~v1_funct_1(E_307))), inference(cnfTransformation, [status(thm)], [f_171])).
% 8.24/3.05  tff(c_1476, plain, (![A_310, B_309, E_307]: (k1_partfun1(A_310, B_309, '#skF_2', '#skF_1', E_307, '#skF_4')=k5_relat_1(E_307, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_307, k1_zfmisc_1(k2_zfmisc_1(A_310, B_309))) | ~v1_funct_1(E_307))), inference(resolution, [status(thm)], [c_102, c_1469])).
% 8.24/3.05  tff(c_1515, plain, (![A_317, B_318, E_319]: (k1_partfun1(A_317, B_318, '#skF_2', '#skF_1', E_319, '#skF_4')=k5_relat_1(E_319, '#skF_4') | ~m1_subset_1(E_319, k1_zfmisc_1(k2_zfmisc_1(A_317, B_318))) | ~v1_funct_1(E_319))), inference(demodulation, [status(thm), theory('equality')], [c_106, c_1476])).
% 8.24/3.05  tff(c_1528, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_108, c_1515])).
% 8.24/3.05  tff(c_1536, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_112, c_1528])).
% 8.24/3.05  tff(c_64, plain, (![A_41]: (m1_subset_1(k6_partfun1(A_41), k1_zfmisc_1(k2_zfmisc_1(A_41, A_41))))), inference(cnfTransformation, [status(thm)], [f_161])).
% 8.24/3.05  tff(c_98, plain, (r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k6_partfun1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_274])).
% 8.24/3.05  tff(c_960, plain, (![D_235, C_236, A_237, B_238]: (D_235=C_236 | ~r2_relset_1(A_237, B_238, C_236, D_235) | ~m1_subset_1(D_235, k1_zfmisc_1(k2_zfmisc_1(A_237, B_238))) | ~m1_subset_1(C_236, k1_zfmisc_1(k2_zfmisc_1(A_237, B_238))))), inference(cnfTransformation, [status(thm)], [f_127])).
% 8.24/3.05  tff(c_970, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_98, c_960])).
% 8.24/3.05  tff(c_987, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_970])).
% 8.24/3.05  tff(c_1013, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_987])).
% 8.24/3.05  tff(c_1544, plain, (~m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_1536, c_1013])).
% 8.24/3.05  tff(c_1897, plain, (![C_345, F_344, A_343, E_346, D_347, B_348]: (m1_subset_1(k1_partfun1(A_343, B_348, C_345, D_347, E_346, F_344), k1_zfmisc_1(k2_zfmisc_1(A_343, D_347))) | ~m1_subset_1(F_344, k1_zfmisc_1(k2_zfmisc_1(C_345, D_347))) | ~v1_funct_1(F_344) | ~m1_subset_1(E_346, k1_zfmisc_1(k2_zfmisc_1(A_343, B_348))) | ~v1_funct_1(E_346))), inference(cnfTransformation, [status(thm)], [f_157])).
% 8.24/3.05  tff(c_1970, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1536, c_1897])).
% 8.24/3.05  tff(c_2001, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_112, c_108, c_106, c_102, c_1970])).
% 8.24/3.05  tff(c_2003, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1544, c_2001])).
% 8.24/3.05  tff(c_2004, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_987])).
% 8.24/3.05  tff(c_5255, plain, (![B_568, C_566, A_567, D_569, E_570]: (k1_xboole_0=C_566 | v2_funct_1(E_570) | k2_relset_1(A_567, B_568, D_569)!=B_568 | ~v2_funct_1(k1_partfun1(A_567, B_568, B_568, C_566, D_569, E_570)) | ~m1_subset_1(E_570, k1_zfmisc_1(k2_zfmisc_1(B_568, C_566))) | ~v1_funct_2(E_570, B_568, C_566) | ~v1_funct_1(E_570) | ~m1_subset_1(D_569, k1_zfmisc_1(k2_zfmisc_1(A_567, B_568))) | ~v1_funct_2(D_569, A_567, B_568) | ~v1_funct_1(D_569))), inference(cnfTransformation, [status(thm)], [f_216])).
% 8.24/3.05  tff(c_5259, plain, (k1_xboole_0='#skF_1' | v2_funct_1('#skF_4') | k2_relset_1('#skF_1', '#skF_2', '#skF_3')!='#skF_2' | ~v2_funct_1(k6_partfun1('#skF_1')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_2004, c_5255])).
% 8.24/3.05  tff(c_5264, plain, (k1_xboole_0='#skF_1' | v2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_112, c_110, c_108, c_106, c_104, c_102, c_4421, c_100, c_5259])).
% 8.24/3.05  tff(c_5266, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2036, c_94, c_5264])).
% 8.24/3.05  tff(c_5268, plain, (v2_funct_1('#skF_4')), inference(splitRight, [status(thm)], [c_2032])).
% 8.24/3.05  tff(c_478, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_108, c_465])).
% 8.24/3.05  tff(c_483, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_100, c_478])).
% 8.24/3.05  tff(c_381, plain, (![A_125, B_126, C_127]: (k1_relset_1(A_125, B_126, C_127)=k1_relat_1(C_127) | ~m1_subset_1(C_127, k1_zfmisc_1(k2_zfmisc_1(A_125, B_126))))), inference(cnfTransformation, [status(thm)], [f_115])).
% 8.24/3.05  tff(c_397, plain, (k1_relset_1('#skF_2', '#skF_1', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_102, c_381])).
% 8.24/3.05  tff(c_846, plain, (![B_222, A_223, C_224]: (k1_xboole_0=B_222 | k1_relset_1(A_223, B_222, C_224)=A_223 | ~v1_funct_2(C_224, A_223, B_222) | ~m1_subset_1(C_224, k1_zfmisc_1(k2_zfmisc_1(A_223, B_222))))), inference(cnfTransformation, [status(thm)], [f_145])).
% 8.24/3.05  tff(c_856, plain, (k1_xboole_0='#skF_1' | k1_relset_1('#skF_2', '#skF_1', '#skF_4')='#skF_2' | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_102, c_846])).
% 8.24/3.05  tff(c_865, plain, (k1_xboole_0='#skF_1' | k1_relat_1('#skF_4')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_104, c_397, c_856])).
% 8.24/3.05  tff(c_866, plain, (k1_relat_1('#skF_4')='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_94, c_865])).
% 8.24/3.05  tff(c_5267, plain, (k2_relat_1('#skF_4')!='#skF_1' | v1_funct_1(k2_funct_1('#skF_4'))), inference(splitRight, [status(thm)], [c_2032])).
% 8.24/3.05  tff(c_5269, plain, (k2_relat_1('#skF_4')!='#skF_1'), inference(splitLeft, [status(thm)], [c_5267])).
% 8.24/3.05  tff(c_367, plain, (![A_122, B_123, D_124]: (r2_relset_1(A_122, B_123, D_124, D_124) | ~m1_subset_1(D_124, k1_zfmisc_1(k2_zfmisc_1(A_122, B_123))))), inference(cnfTransformation, [status(thm)], [f_127])).
% 8.24/3.05  tff(c_378, plain, (![A_41]: (r2_relset_1(A_41, A_41, k6_partfun1(A_41), k6_partfun1(A_41)))), inference(resolution, [status(thm)], [c_64, c_367])).
% 8.24/3.05  tff(c_7134, plain, (![A_690, B_691, C_692, D_693]: (k2_relset_1(A_690, B_691, C_692)=B_691 | ~r2_relset_1(B_691, B_691, k1_partfun1(B_691, A_690, A_690, B_691, D_693, C_692), k6_partfun1(B_691)) | ~m1_subset_1(D_693, k1_zfmisc_1(k2_zfmisc_1(B_691, A_690))) | ~v1_funct_2(D_693, B_691, A_690) | ~v1_funct_1(D_693) | ~m1_subset_1(C_692, k1_zfmisc_1(k2_zfmisc_1(A_690, B_691))) | ~v1_funct_2(C_692, A_690, B_691) | ~v1_funct_1(C_692))), inference(cnfTransformation, [status(thm)], [f_190])).
% 8.24/3.05  tff(c_7140, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')='#skF_1' | ~r2_relset_1('#skF_1', '#skF_1', k6_partfun1('#skF_1'), k6_partfun1('#skF_1')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_2004, c_7134])).
% 8.24/3.05  tff(c_7144, plain, (k2_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_106, c_104, c_102, c_112, c_110, c_108, c_378, c_481, c_7140])).
% 8.24/3.05  tff(c_7146, plain, $false, inference(negUnitSimplification, [status(thm)], [c_5269, c_7144])).
% 8.24/3.05  tff(c_7148, plain, (k2_relat_1('#skF_4')='#skF_1'), inference(splitRight, [status(thm)], [c_5267])).
% 8.24/3.05  tff(c_68, plain, (![A_48]: (k6_relat_1(A_48)=k6_partfun1(A_48))), inference(cnfTransformation, [status(thm)], [f_173])).
% 8.24/3.05  tff(c_28, plain, (![A_12, B_14]: (k2_funct_1(A_12)=B_14 | k6_relat_1(k2_relat_1(A_12))!=k5_relat_1(B_14, A_12) | k2_relat_1(B_14)!=k1_relat_1(A_12) | ~v2_funct_1(A_12) | ~v1_funct_1(B_14) | ~v1_relat_1(B_14) | ~v1_funct_1(A_12) | ~v1_relat_1(A_12))), inference(cnfTransformation, [status(thm)], [f_93])).
% 8.24/3.05  tff(c_7251, plain, (![A_704, B_705]: (k2_funct_1(A_704)=B_705 | k6_partfun1(k2_relat_1(A_704))!=k5_relat_1(B_705, A_704) | k2_relat_1(B_705)!=k1_relat_1(A_704) | ~v2_funct_1(A_704) | ~v1_funct_1(B_705) | ~v1_relat_1(B_705) | ~v1_funct_1(A_704) | ~v1_relat_1(A_704))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_28])).
% 8.24/3.05  tff(c_7253, plain, (![B_705]: (k2_funct_1('#skF_4')=B_705 | k5_relat_1(B_705, '#skF_4')!=k6_partfun1('#skF_1') | k2_relat_1(B_705)!=k1_relat_1('#skF_4') | ~v2_funct_1('#skF_4') | ~v1_funct_1(B_705) | ~v1_relat_1(B_705) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_7148, c_7251])).
% 8.24/3.05  tff(c_7412, plain, (![B_717]: (k2_funct_1('#skF_4')=B_717 | k5_relat_1(B_717, '#skF_4')!=k6_partfun1('#skF_1') | k2_relat_1(B_717)!='#skF_2' | ~v1_funct_1(B_717) | ~v1_relat_1(B_717))), inference(demodulation, [status(thm), theory('equality')], [c_184, c_106, c_5268, c_866, c_7253])).
% 8.24/3.05  tff(c_7439, plain, (k2_funct_1('#skF_4')='#skF_3' | k5_relat_1('#skF_3', '#skF_4')!=k6_partfun1('#skF_1') | k2_relat_1('#skF_3')!='#skF_2' | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_185, c_7412])).
% 8.24/3.05  tff(c_7456, plain, (k2_funct_1('#skF_4')='#skF_3' | k5_relat_1('#skF_3', '#skF_4')!=k6_partfun1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_112, c_483, c_7439])).
% 8.24/3.05  tff(c_7461, plain, (k5_relat_1('#skF_3', '#skF_4')!=k6_partfun1('#skF_1')), inference(splitLeft, [status(thm)], [c_7456])).
% 8.24/3.05  tff(c_7973, plain, (![D_775, C_779, F_778, B_776, E_774, A_777]: (k1_partfun1(A_777, B_776, C_779, D_775, E_774, F_778)=k5_relat_1(E_774, F_778) | ~m1_subset_1(F_778, k1_zfmisc_1(k2_zfmisc_1(C_779, D_775))) | ~v1_funct_1(F_778) | ~m1_subset_1(E_774, k1_zfmisc_1(k2_zfmisc_1(A_777, B_776))) | ~v1_funct_1(E_774))), inference(cnfTransformation, [status(thm)], [f_171])).
% 8.24/3.05  tff(c_7982, plain, (![A_777, B_776, E_774]: (k1_partfun1(A_777, B_776, '#skF_2', '#skF_1', E_774, '#skF_4')=k5_relat_1(E_774, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_774, k1_zfmisc_1(k2_zfmisc_1(A_777, B_776))) | ~v1_funct_1(E_774))), inference(resolution, [status(thm)], [c_102, c_7973])).
% 8.24/3.05  tff(c_8101, plain, (![A_787, B_788, E_789]: (k1_partfun1(A_787, B_788, '#skF_2', '#skF_1', E_789, '#skF_4')=k5_relat_1(E_789, '#skF_4') | ~m1_subset_1(E_789, k1_zfmisc_1(k2_zfmisc_1(A_787, B_788))) | ~v1_funct_1(E_789))), inference(demodulation, [status(thm), theory('equality')], [c_106, c_7982])).
% 8.24/3.05  tff(c_8117, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_108, c_8101])).
% 8.24/3.05  tff(c_8126, plain, (k5_relat_1('#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_112, c_2004, c_8117])).
% 8.24/3.05  tff(c_8128, plain, $false, inference(negUnitSimplification, [status(thm)], [c_7461, c_8126])).
% 8.24/3.05  tff(c_8129, plain, (k2_funct_1('#skF_4')='#skF_3'), inference(splitRight, [status(thm)], [c_7456])).
% 8.24/3.05  tff(c_30, plain, (![A_15]: (k2_funct_1(k2_funct_1(A_15))=A_15 | ~v2_funct_1(A_15) | ~v1_funct_1(A_15) | ~v1_relat_1(A_15))), inference(cnfTransformation, [status(thm)], [f_101])).
% 8.24/3.05  tff(c_8137, plain, (k2_funct_1('#skF_3')='#skF_4' | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_8129, c_30])).
% 8.24/3.05  tff(c_8150, plain, (k2_funct_1('#skF_3')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_184, c_106, c_5268, c_8137])).
% 8.24/3.05  tff(c_8152, plain, $false, inference(negUnitSimplification, [status(thm)], [c_90, c_8150])).
% 8.24/3.05  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.24/3.05  
% 8.24/3.05  Inference rules
% 8.24/3.05  ----------------------
% 8.24/3.05  #Ref     : 0
% 8.24/3.05  #Sup     : 1577
% 8.24/3.05  #Fact    : 0
% 8.24/3.05  #Define  : 0
% 8.24/3.05  #Split   : 41
% 8.24/3.05  #Chain   : 0
% 8.24/3.05  #Close   : 0
% 8.24/3.05  
% 8.24/3.05  Ordering : KBO
% 8.24/3.05  
% 8.24/3.05  Simplification rules
% 8.24/3.05  ----------------------
% 8.24/3.05  #Subsume      : 115
% 8.24/3.05  #Demod        : 1368
% 8.24/3.05  #Tautology    : 342
% 8.24/3.05  #SimpNegUnit  : 146
% 8.24/3.05  #BackRed      : 25
% 8.24/3.05  
% 8.24/3.05  #Partial instantiations: 0
% 8.24/3.05  #Strategies tried      : 1
% 8.24/3.05  
% 8.24/3.05  Timing (in seconds)
% 8.24/3.05  ----------------------
% 8.24/3.05  Preprocessing        : 0.40
% 8.24/3.05  Parsing              : 0.21
% 8.24/3.05  CNF conversion       : 0.03
% 8.24/3.05  Main loop            : 1.87
% 8.24/3.05  Inferencing          : 0.58
% 8.24/3.06  Reduction            : 0.74
% 8.24/3.06  Demodulation         : 0.53
% 8.24/3.06  BG Simplification    : 0.07
% 8.24/3.06  Subsumption          : 0.36
% 8.24/3.06  Abstraction          : 0.09
% 8.24/3.06  MUC search           : 0.00
% 8.24/3.06  Cooper               : 0.00
% 8.24/3.06  Total                : 2.31
% 8.24/3.06  Index Insertion      : 0.00
% 8.24/3.06  Index Deletion       : 0.00
% 8.24/3.06  Index Matching       : 0.00
% 8.24/3.06  BG Taut test         : 0.00
%------------------------------------------------------------------------------
