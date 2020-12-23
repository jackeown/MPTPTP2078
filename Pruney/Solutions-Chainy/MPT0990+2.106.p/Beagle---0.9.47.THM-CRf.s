%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:13:11 EST 2020

% Result     : Theorem 13.96s
% Output     : CNFRefutation 14.18s
% Verified   : 
% Statistics : Number of formulae       :  244 (14084 expanded)
%              Number of leaves         :   55 (4858 expanded)
%              Depth                    :   30
%              Number of atoms          :  612 (54917 expanded)
%              Number of equality atoms :  179 (17465 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > o_0_0_xboole_0 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(o_0_0_xboole_0,type,(
    o_0_0_xboole_0: $i )).

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

tff('#skF_5',type,(
    '#skF_5': $i )).

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_275,negated_conjecture,(
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

tff(f_154,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_174,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( v1_funct_1(k1_partfun1(A,B,C,D,E,F))
        & m1_subset_1(k1_partfun1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).

tff(f_178,axiom,(
    ! [A] :
      ( v1_partfun1(k6_partfun1(A),A)
      & m1_subset_1(k6_partfun1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_partfun1)).

tff(f_162,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_188,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_53,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_45,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_80,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_32,axiom,(
    ? [A] : v1_xboole_0(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc1_xboole_0)).

tff(f_30,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_249,axiom,(
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

tff(f_207,axiom,(
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

tff(f_190,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_64,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_60,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => r1_tarski(k2_relat_1(k5_relat_1(A,B)),k2_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_relat_1)).

tff(f_127,axiom,(
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

tff(f_150,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_110,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k2_relat_1(A) = k1_relat_1(k2_funct_1(A))
          & k1_relat_1(A) = k2_relat_1(k2_funct_1(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_88,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v2_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_funct_1)).

tff(f_233,axiom,(
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

tff(f_100,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A)
        & v2_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A))
        & v2_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_funct_1)).

tff(c_96,plain,(
    k2_funct_1('#skF_4') != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_275])).

tff(c_118,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_275])).

tff(c_106,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_4') = '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_275])).

tff(c_114,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_275])).

tff(c_469,plain,(
    ! [A_119,B_120,C_121] :
      ( k2_relset_1(A_119,B_120,C_121) = k2_relat_1(C_121)
      | ~ m1_subset_1(C_121,k1_zfmisc_1(k2_zfmisc_1(A_119,B_120))) ) ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_475,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_114,c_469])).

tff(c_482,plain,(
    k2_relat_1('#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_106,c_475])).

tff(c_112,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_275])).

tff(c_108,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_275])).

tff(c_1700,plain,(
    ! [C_199,A_197,F_201,D_200,E_202,B_198] :
      ( m1_subset_1(k1_partfun1(A_197,B_198,C_199,D_200,E_202,F_201),k1_zfmisc_1(k2_zfmisc_1(A_197,D_200)))
      | ~ m1_subset_1(F_201,k1_zfmisc_1(k2_zfmisc_1(C_199,D_200)))
      | ~ v1_funct_1(F_201)
      | ~ m1_subset_1(E_202,k1_zfmisc_1(k2_zfmisc_1(A_197,B_198)))
      | ~ v1_funct_1(E_202) ) ),
    inference(cnfTransformation,[status(thm)],[f_174])).

tff(c_76,plain,(
    ! [A_45] : m1_subset_1(k6_partfun1(A_45),k1_zfmisc_1(k2_zfmisc_1(A_45,A_45))) ),
    inference(cnfTransformation,[status(thm)],[f_178])).

tff(c_104,plain,(
    r2_relset_1('#skF_2','#skF_2',k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5'),k6_partfun1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_275])).

tff(c_616,plain,(
    ! [D_129,C_130,A_131,B_132] :
      ( D_129 = C_130
      | ~ r2_relset_1(A_131,B_132,C_130,D_129)
      | ~ m1_subset_1(D_129,k1_zfmisc_1(k2_zfmisc_1(A_131,B_132)))
      | ~ m1_subset_1(C_130,k1_zfmisc_1(k2_zfmisc_1(A_131,B_132))) ) ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_624,plain,
    ( k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5') = k6_partfun1('#skF_2')
    | ~ m1_subset_1(k6_partfun1('#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2')))
    | ~ m1_subset_1(k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(resolution,[status(thm)],[c_104,c_616])).

tff(c_639,plain,
    ( k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5') = k6_partfun1('#skF_2')
    | ~ m1_subset_1(k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_624])).

tff(c_672,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_639])).

tff(c_1723,plain,
    ( ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2')))
    | ~ v1_funct_1('#skF_5')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_1700,c_672])).

tff(c_1755,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_118,c_114,c_112,c_108,c_1723])).

tff(c_1756,plain,(
    k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5') = k6_partfun1('#skF_2') ),
    inference(splitRight,[status(thm)],[c_639])).

tff(c_4830,plain,(
    ! [E_385,C_386,F_383,D_384,B_382,A_387] :
      ( k1_partfun1(A_387,B_382,C_386,D_384,E_385,F_383) = k5_relat_1(E_385,F_383)
      | ~ m1_subset_1(F_383,k1_zfmisc_1(k2_zfmisc_1(C_386,D_384)))
      | ~ v1_funct_1(F_383)
      | ~ m1_subset_1(E_385,k1_zfmisc_1(k2_zfmisc_1(A_387,B_382)))
      | ~ v1_funct_1(E_385) ) ),
    inference(cnfTransformation,[status(thm)],[f_188])).

tff(c_4836,plain,(
    ! [A_387,B_382,E_385] :
      ( k1_partfun1(A_387,B_382,'#skF_3','#skF_2',E_385,'#skF_5') = k5_relat_1(E_385,'#skF_5')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1(E_385,k1_zfmisc_1(k2_zfmisc_1(A_387,B_382)))
      | ~ v1_funct_1(E_385) ) ),
    inference(resolution,[status(thm)],[c_108,c_4830])).

tff(c_5868,plain,(
    ! [A_431,B_432,E_433] :
      ( k1_partfun1(A_431,B_432,'#skF_3','#skF_2',E_433,'#skF_5') = k5_relat_1(E_433,'#skF_5')
      | ~ m1_subset_1(E_433,k1_zfmisc_1(k2_zfmisc_1(A_431,B_432)))
      | ~ v1_funct_1(E_433) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_112,c_4836])).

tff(c_5883,plain,
    ( k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5') = k5_relat_1('#skF_4','#skF_5')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_114,c_5868])).

tff(c_5899,plain,(
    k5_relat_1('#skF_4','#skF_5') = k6_partfun1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_118,c_1756,c_5883])).

tff(c_20,plain,(
    ! [A_9,B_10] : v1_relat_1(k2_zfmisc_1(A_9,B_10)) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_267,plain,(
    ! [B_89,A_90] :
      ( v1_relat_1(B_89)
      | ~ m1_subset_1(B_89,k1_zfmisc_1(A_90))
      | ~ v1_relat_1(A_90) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_273,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_114,c_267])).

tff(c_282,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_273])).

tff(c_276,plain,
    ( v1_relat_1('#skF_5')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_3','#skF_2')) ),
    inference(resolution,[status(thm)],[c_108,c_267])).

tff(c_285,plain,(
    v1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_276])).

tff(c_34,plain,(
    ! [A_17] :
      ( v1_relat_1(k2_funct_1(A_17))
      | ~ v1_funct_1(A_17)
      | ~ v1_relat_1(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_12,plain,(
    ! [B_3] : r1_tarski(B_3,B_3) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_6,plain,(
    v1_xboole_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_134,plain,(
    ! [A_72] :
      ( k1_xboole_0 = A_72
      | ~ v1_xboole_0(A_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_142,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_6,c_134])).

tff(c_100,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_275])).

tff(c_152,plain,(
    '#skF_2' != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_142,c_100])).

tff(c_110,plain,(
    v1_funct_2('#skF_5','#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_275])).

tff(c_483,plain,(
    k2_relset_1('#skF_3','#skF_2','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_108,c_469])).

tff(c_92,plain,(
    ! [B_65,C_66,A_64] :
      ( k6_partfun1(B_65) = k5_relat_1(k2_funct_1(C_66),C_66)
      | k1_xboole_0 = B_65
      | ~ v2_funct_1(C_66)
      | k2_relset_1(A_64,B_65,C_66) != B_65
      | ~ m1_subset_1(C_66,k1_zfmisc_1(k2_zfmisc_1(A_64,B_65)))
      | ~ v1_funct_2(C_66,A_64,B_65)
      | ~ v1_funct_1(C_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_249])).

tff(c_2608,plain,(
    ! [B_256,C_257,A_258] :
      ( k6_partfun1(B_256) = k5_relat_1(k2_funct_1(C_257),C_257)
      | B_256 = '#skF_1'
      | ~ v2_funct_1(C_257)
      | k2_relset_1(A_258,B_256,C_257) != B_256
      | ~ m1_subset_1(C_257,k1_zfmisc_1(k2_zfmisc_1(A_258,B_256)))
      | ~ v1_funct_2(C_257,A_258,B_256)
      | ~ v1_funct_1(C_257) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_142,c_92])).

tff(c_2614,plain,
    ( k5_relat_1(k2_funct_1('#skF_5'),'#skF_5') = k6_partfun1('#skF_2')
    | '#skF_2' = '#skF_1'
    | ~ v2_funct_1('#skF_5')
    | k2_relset_1('#skF_3','#skF_2','#skF_5') != '#skF_2'
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_2')
    | ~ v1_funct_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_108,c_2608])).

tff(c_2624,plain,
    ( k5_relat_1(k2_funct_1('#skF_5'),'#skF_5') = k6_partfun1('#skF_2')
    | '#skF_2' = '#skF_1'
    | ~ v2_funct_1('#skF_5')
    | k2_relat_1('#skF_5') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_112,c_110,c_483,c_2614])).

tff(c_2625,plain,
    ( k5_relat_1(k2_funct_1('#skF_5'),'#skF_5') = k6_partfun1('#skF_2')
    | ~ v2_funct_1('#skF_5')
    | k2_relat_1('#skF_5') != '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_152,c_2624])).

tff(c_2802,plain,(
    k2_relat_1('#skF_5') != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_2625])).

tff(c_116,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_275])).

tff(c_438,plain,(
    ! [A_114,B_115,D_116] :
      ( r2_relset_1(A_114,B_115,D_116,D_116)
      | ~ m1_subset_1(D_116,k1_zfmisc_1(k2_zfmisc_1(A_114,B_115))) ) ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_445,plain,(
    ! [A_45] : r2_relset_1(A_45,A_45,k6_partfun1(A_45),k6_partfun1(A_45)) ),
    inference(resolution,[status(thm)],[c_76,c_438])).

tff(c_3455,plain,(
    ! [A_299,B_300,C_301,D_302] :
      ( k2_relset_1(A_299,B_300,C_301) = B_300
      | ~ r2_relset_1(B_300,B_300,k1_partfun1(B_300,A_299,A_299,B_300,D_302,C_301),k6_partfun1(B_300))
      | ~ m1_subset_1(D_302,k1_zfmisc_1(k2_zfmisc_1(B_300,A_299)))
      | ~ v1_funct_2(D_302,B_300,A_299)
      | ~ v1_funct_1(D_302)
      | ~ m1_subset_1(C_301,k1_zfmisc_1(k2_zfmisc_1(A_299,B_300)))
      | ~ v1_funct_2(C_301,A_299,B_300)
      | ~ v1_funct_1(C_301) ) ),
    inference(cnfTransformation,[status(thm)],[f_207])).

tff(c_3461,plain,
    ( k2_relset_1('#skF_3','#skF_2','#skF_5') = '#skF_2'
    | ~ r2_relset_1('#skF_2','#skF_2',k6_partfun1('#skF_2'),k6_partfun1('#skF_2'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_3')
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2')))
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_2')
    | ~ v1_funct_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_1756,c_3455])).

tff(c_3465,plain,(
    k2_relat_1('#skF_5') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_112,c_110,c_108,c_118,c_116,c_114,c_445,c_483,c_3461])).

tff(c_3467,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2802,c_3465])).

tff(c_3469,plain,(
    k2_relat_1('#skF_5') = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_2625])).

tff(c_80,plain,(
    ! [A_52] : k6_relat_1(A_52) = k6_partfun1(A_52) ),
    inference(cnfTransformation,[status(thm)],[f_190])).

tff(c_26,plain,(
    ! [A_14] : k2_relat_1(k6_relat_1(A_14)) = A_14 ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_127,plain,(
    ! [A_14] : k2_relat_1(k6_partfun1(A_14)) = A_14 ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_26])).

tff(c_2409,plain,(
    ! [C_248,B_244,E_247,F_245,A_249,D_246] :
      ( k1_partfun1(A_249,B_244,C_248,D_246,E_247,F_245) = k5_relat_1(E_247,F_245)
      | ~ m1_subset_1(F_245,k1_zfmisc_1(k2_zfmisc_1(C_248,D_246)))
      | ~ v1_funct_1(F_245)
      | ~ m1_subset_1(E_247,k1_zfmisc_1(k2_zfmisc_1(A_249,B_244)))
      | ~ v1_funct_1(E_247) ) ),
    inference(cnfTransformation,[status(thm)],[f_188])).

tff(c_2415,plain,(
    ! [A_249,B_244,E_247] :
      ( k1_partfun1(A_249,B_244,'#skF_3','#skF_2',E_247,'#skF_5') = k5_relat_1(E_247,'#skF_5')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1(E_247,k1_zfmisc_1(k2_zfmisc_1(A_249,B_244)))
      | ~ v1_funct_1(E_247) ) ),
    inference(resolution,[status(thm)],[c_108,c_2409])).

tff(c_2510,plain,(
    ! [A_253,B_254,E_255] :
      ( k1_partfun1(A_253,B_254,'#skF_3','#skF_2',E_255,'#skF_5') = k5_relat_1(E_255,'#skF_5')
      | ~ m1_subset_1(E_255,k1_zfmisc_1(k2_zfmisc_1(A_253,B_254)))
      | ~ v1_funct_1(E_255) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_112,c_2415])).

tff(c_2516,plain,
    ( k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5') = k5_relat_1('#skF_4','#skF_5')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_114,c_2510])).

tff(c_2525,plain,(
    k5_relat_1('#skF_4','#skF_5') = k6_partfun1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_118,c_1756,c_2516])).

tff(c_22,plain,(
    ! [A_11,B_13] :
      ( r1_tarski(k2_relat_1(k5_relat_1(A_11,B_13)),k2_relat_1(B_13))
      | ~ v1_relat_1(B_13)
      | ~ v1_relat_1(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_2597,plain,
    ( r1_tarski(k2_relat_1(k6_partfun1('#skF_2')),k2_relat_1('#skF_5'))
    | ~ v1_relat_1('#skF_5')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_2525,c_22])).

tff(c_2601,plain,(
    r1_tarski('#skF_2',k2_relat_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_282,c_285,c_127,c_2597])).

tff(c_8,plain,(
    ! [B_3,A_2] :
      ( B_3 = A_2
      | ~ r1_tarski(B_3,A_2)
      | ~ r1_tarski(A_2,B_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_2605,plain,
    ( k2_relat_1('#skF_5') = '#skF_2'
    | ~ r1_tarski(k2_relat_1('#skF_5'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_2601,c_8])).

tff(c_2606,plain,(
    ~ r1_tarski(k2_relat_1('#skF_5'),'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_2605])).

tff(c_3470,plain,(
    ~ r1_tarski('#skF_2','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3469,c_2606])).

tff(c_3476,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_3470])).

tff(c_3477,plain,(
    k2_relat_1('#skF_5') = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_2605])).

tff(c_102,plain,(
    v2_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_275])).

tff(c_54,plain,(
    ! [A_22,B_24] :
      ( k2_funct_1(A_22) = B_24
      | k6_relat_1(k2_relat_1(A_22)) != k5_relat_1(B_24,A_22)
      | k2_relat_1(B_24) != k1_relat_1(A_22)
      | ~ v2_funct_1(A_22)
      | ~ v1_funct_1(B_24)
      | ~ v1_relat_1(B_24)
      | ~ v1_funct_1(A_22)
      | ~ v1_relat_1(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_2171,plain,(
    ! [A_222,B_223] :
      ( k2_funct_1(A_222) = B_223
      | k6_partfun1(k2_relat_1(A_222)) != k5_relat_1(B_223,A_222)
      | k2_relat_1(B_223) != k1_relat_1(A_222)
      | ~ v2_funct_1(A_222)
      | ~ v1_funct_1(B_223)
      | ~ v1_relat_1(B_223)
      | ~ v1_funct_1(A_222)
      | ~ v1_relat_1(A_222) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_54])).

tff(c_2187,plain,(
    ! [B_223] :
      ( k2_funct_1('#skF_4') = B_223
      | k5_relat_1(B_223,'#skF_4') != k6_partfun1('#skF_3')
      | k2_relat_1(B_223) != k1_relat_1('#skF_4')
      | ~ v2_funct_1('#skF_4')
      | ~ v1_funct_1(B_223)
      | ~ v1_relat_1(B_223)
      | ~ v1_funct_1('#skF_4')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_482,c_2171])).

tff(c_2243,plain,(
    ! [B_225] :
      ( k2_funct_1('#skF_4') = B_225
      | k5_relat_1(B_225,'#skF_4') != k6_partfun1('#skF_3')
      | k2_relat_1(B_225) != k1_relat_1('#skF_4')
      | ~ v1_funct_1(B_225)
      | ~ v1_relat_1(B_225) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_282,c_118,c_102,c_2187])).

tff(c_2252,plain,
    ( k2_funct_1('#skF_4') = '#skF_5'
    | k5_relat_1('#skF_5','#skF_4') != k6_partfun1('#skF_3')
    | k2_relat_1('#skF_5') != k1_relat_1('#skF_4')
    | ~ v1_funct_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_285,c_2243])).

tff(c_2271,plain,
    ( k2_funct_1('#skF_4') = '#skF_5'
    | k5_relat_1('#skF_5','#skF_4') != k6_partfun1('#skF_3')
    | k2_relat_1('#skF_5') != k1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_112,c_2252])).

tff(c_2272,plain,
    ( k5_relat_1('#skF_5','#skF_4') != k6_partfun1('#skF_3')
    | k2_relat_1('#skF_5') != k1_relat_1('#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_96,c_2271])).

tff(c_2281,plain,(
    k2_relat_1('#skF_5') != k1_relat_1('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_2272])).

tff(c_3480,plain,(
    k1_relat_1('#skF_4') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3477,c_2281])).

tff(c_355,plain,(
    ! [C_106,A_107,B_108] :
      ( v4_relat_1(C_106,A_107)
      | ~ m1_subset_1(C_106,k1_zfmisc_1(k2_zfmisc_1(A_107,B_108))) ) ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_367,plain,(
    v4_relat_1('#skF_4','#skF_2') ),
    inference(resolution,[status(thm)],[c_114,c_355])).

tff(c_50,plain,(
    ! [A_21] :
      ( k2_relat_1(k2_funct_1(A_21)) = k1_relat_1(A_21)
      | ~ v2_funct_1(A_21)
      | ~ v1_funct_1(A_21)
      | ~ v1_relat_1(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_412,plain,(
    ! [A_113] :
      ( k1_relat_1(k2_funct_1(A_113)) = k2_relat_1(A_113)
      | ~ v2_funct_1(A_113)
      | ~ v1_funct_1(A_113)
      | ~ v1_relat_1(A_113) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_316,plain,(
    ! [B_100,A_101] :
      ( v4_relat_1(B_100,A_101)
      | ~ r1_tarski(k1_relat_1(B_100),A_101)
      | ~ v1_relat_1(B_100) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_330,plain,(
    ! [B_100] :
      ( v4_relat_1(B_100,k1_relat_1(B_100))
      | ~ v1_relat_1(B_100) ) ),
    inference(resolution,[status(thm)],[c_12,c_316])).

tff(c_640,plain,(
    ! [A_133] :
      ( v4_relat_1(k2_funct_1(A_133),k2_relat_1(A_133))
      | ~ v1_relat_1(k2_funct_1(A_133))
      | ~ v2_funct_1(A_133)
      | ~ v1_funct_1(A_133)
      | ~ v1_relat_1(A_133) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_412,c_330])).

tff(c_646,plain,
    ( v4_relat_1(k2_funct_1('#skF_4'),'#skF_3')
    | ~ v1_relat_1(k2_funct_1('#skF_4'))
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_482,c_640])).

tff(c_657,plain,
    ( v4_relat_1(k2_funct_1('#skF_4'),'#skF_3')
    | ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_282,c_118,c_102,c_646])).

tff(c_662,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_657])).

tff(c_665,plain,
    ( ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_34,c_662])).

tff(c_669,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_282,c_118,c_665])).

tff(c_671,plain,(
    v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_657])).

tff(c_98,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_275])).

tff(c_151,plain,(
    '#skF_3' != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_142,c_98])).

tff(c_94,plain,(
    ! [A_64,C_66,B_65] :
      ( k6_partfun1(A_64) = k5_relat_1(C_66,k2_funct_1(C_66))
      | k1_xboole_0 = B_65
      | ~ v2_funct_1(C_66)
      | k2_relset_1(A_64,B_65,C_66) != B_65
      | ~ m1_subset_1(C_66,k1_zfmisc_1(k2_zfmisc_1(A_64,B_65)))
      | ~ v1_funct_2(C_66,A_64,B_65)
      | ~ v1_funct_1(C_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_249])).

tff(c_3678,plain,(
    ! [A_309,C_310,B_311] :
      ( k6_partfun1(A_309) = k5_relat_1(C_310,k2_funct_1(C_310))
      | B_311 = '#skF_1'
      | ~ v2_funct_1(C_310)
      | k2_relset_1(A_309,B_311,C_310) != B_311
      | ~ m1_subset_1(C_310,k1_zfmisc_1(k2_zfmisc_1(A_309,B_311)))
      | ~ v1_funct_2(C_310,A_309,B_311)
      | ~ v1_funct_1(C_310) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_142,c_94])).

tff(c_3682,plain,
    ( k5_relat_1('#skF_4',k2_funct_1('#skF_4')) = k6_partfun1('#skF_2')
    | '#skF_3' = '#skF_1'
    | ~ v2_funct_1('#skF_4')
    | k2_relset_1('#skF_2','#skF_3','#skF_4') != '#skF_3'
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_3')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_114,c_3678])).

tff(c_3690,plain,
    ( k5_relat_1('#skF_4',k2_funct_1('#skF_4')) = k6_partfun1('#skF_2')
    | '#skF_3' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_118,c_116,c_106,c_102,c_3682])).

tff(c_3691,plain,(
    k5_relat_1('#skF_4',k2_funct_1('#skF_4')) = k6_partfun1('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_151,c_3690])).

tff(c_3699,plain,
    ( r1_tarski(k2_relat_1(k6_partfun1('#skF_2')),k2_relat_1(k2_funct_1('#skF_4')))
    | ~ v1_relat_1(k2_funct_1('#skF_4'))
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_3691,c_22])).

tff(c_3703,plain,(
    r1_tarski('#skF_2',k2_relat_1(k2_funct_1('#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_282,c_671,c_127,c_3699])).

tff(c_3709,plain,
    ( r1_tarski('#skF_2',k1_relat_1('#skF_4'))
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_3703])).

tff(c_3712,plain,(
    r1_tarski('#skF_2',k1_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_282,c_118,c_102,c_3709])).

tff(c_299,plain,(
    ! [B_94,A_95] :
      ( r1_tarski(k1_relat_1(B_94),A_95)
      | ~ v4_relat_1(B_94,A_95)
      | ~ v1_relat_1(B_94) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_305,plain,(
    ! [B_94,A_95] :
      ( k1_relat_1(B_94) = A_95
      | ~ r1_tarski(A_95,k1_relat_1(B_94))
      | ~ v4_relat_1(B_94,A_95)
      | ~ v1_relat_1(B_94) ) ),
    inference(resolution,[status(thm)],[c_299,c_8])).

tff(c_3715,plain,
    ( k1_relat_1('#skF_4') = '#skF_2'
    | ~ v4_relat_1('#skF_4','#skF_2')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_3712,c_305])).

tff(c_3720,plain,(
    k1_relat_1('#skF_4') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_282,c_367,c_3715])).

tff(c_3722,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3480,c_3720])).

tff(c_3724,plain,(
    k2_relat_1('#skF_5') = k1_relat_1('#skF_4') ),
    inference(splitRight,[status(thm)],[c_2272])).

tff(c_418,plain,(
    ! [A_113] :
      ( v4_relat_1(k2_funct_1(A_113),k2_relat_1(A_113))
      | ~ v1_relat_1(k2_funct_1(A_113))
      | ~ v2_funct_1(A_113)
      | ~ v1_funct_1(A_113)
      | ~ v1_relat_1(A_113) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_412,c_330])).

tff(c_3737,plain,
    ( v4_relat_1(k2_funct_1('#skF_5'),k1_relat_1('#skF_4'))
    | ~ v1_relat_1(k2_funct_1('#skF_5'))
    | ~ v2_funct_1('#skF_5')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_3724,c_418])).

tff(c_3753,plain,
    ( v4_relat_1(k2_funct_1('#skF_5'),k1_relat_1('#skF_4'))
    | ~ v1_relat_1(k2_funct_1('#skF_5'))
    | ~ v2_funct_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_285,c_112,c_3737])).

tff(c_3815,plain,(
    ~ v2_funct_1('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_3753])).

tff(c_42,plain,(
    ! [A_19] : v2_funct_1(k6_relat_1(A_19)) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_121,plain,(
    ! [A_19] : v2_funct_1(k6_partfun1(A_19)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_42])).

tff(c_86,plain,(
    ! [B_59,A_58,D_61,E_63,C_60] :
      ( k1_xboole_0 = C_60
      | v2_funct_1(E_63)
      | k2_relset_1(A_58,B_59,D_61) != B_59
      | ~ v2_funct_1(k1_partfun1(A_58,B_59,B_59,C_60,D_61,E_63))
      | ~ m1_subset_1(E_63,k1_zfmisc_1(k2_zfmisc_1(B_59,C_60)))
      | ~ v1_funct_2(E_63,B_59,C_60)
      | ~ v1_funct_1(E_63)
      | ~ m1_subset_1(D_61,k1_zfmisc_1(k2_zfmisc_1(A_58,B_59)))
      | ~ v1_funct_2(D_61,A_58,B_59)
      | ~ v1_funct_1(D_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_233])).

tff(c_4777,plain,(
    ! [A_375,E_376,D_374,C_377,B_373] :
      ( C_377 = '#skF_1'
      | v2_funct_1(E_376)
      | k2_relset_1(A_375,B_373,D_374) != B_373
      | ~ v2_funct_1(k1_partfun1(A_375,B_373,B_373,C_377,D_374,E_376))
      | ~ m1_subset_1(E_376,k1_zfmisc_1(k2_zfmisc_1(B_373,C_377)))
      | ~ v1_funct_2(E_376,B_373,C_377)
      | ~ v1_funct_1(E_376)
      | ~ m1_subset_1(D_374,k1_zfmisc_1(k2_zfmisc_1(A_375,B_373)))
      | ~ v1_funct_2(D_374,A_375,B_373)
      | ~ v1_funct_1(D_374) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_142,c_86])).

tff(c_4781,plain,
    ( '#skF_2' = '#skF_1'
    | v2_funct_1('#skF_5')
    | k2_relset_1('#skF_2','#skF_3','#skF_4') != '#skF_3'
    | ~ v2_funct_1(k6_partfun1('#skF_2'))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2')))
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_2')
    | ~ v1_funct_1('#skF_5')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_3')
    | ~ v1_funct_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1756,c_4777])).

tff(c_4786,plain,
    ( '#skF_2' = '#skF_1'
    | v2_funct_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_118,c_116,c_114,c_112,c_110,c_108,c_121,c_106,c_4781])).

tff(c_4788,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3815,c_152,c_4786])).

tff(c_4789,plain,
    ( ~ v1_relat_1(k2_funct_1('#skF_5'))
    | v4_relat_1(k2_funct_1('#skF_5'),k1_relat_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_3753])).

tff(c_4791,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_4789])).

tff(c_4794,plain,
    ( ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_34,c_4791])).

tff(c_4798,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_285,c_112,c_4794])).

tff(c_4800,plain,(
    v1_relat_1(k2_funct_1('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_4789])).

tff(c_32,plain,(
    ! [A_17] :
      ( v1_funct_1(k2_funct_1(A_17))
      | ~ v1_funct_1(A_17)
      | ~ v1_relat_1(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_4790,plain,(
    v2_funct_1('#skF_5') ),
    inference(splitRight,[status(thm)],[c_3753])).

tff(c_3725,plain,(
    k2_relset_1('#skF_3','#skF_2','#skF_5') = k1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3724,c_483])).

tff(c_4972,plain,(
    ! [A_393,C_394,B_395] :
      ( k6_partfun1(A_393) = k5_relat_1(C_394,k2_funct_1(C_394))
      | B_395 = '#skF_1'
      | ~ v2_funct_1(C_394)
      | k2_relset_1(A_393,B_395,C_394) != B_395
      | ~ m1_subset_1(C_394,k1_zfmisc_1(k2_zfmisc_1(A_393,B_395)))
      | ~ v1_funct_2(C_394,A_393,B_395)
      | ~ v1_funct_1(C_394) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_142,c_94])).

tff(c_4978,plain,
    ( k5_relat_1('#skF_5',k2_funct_1('#skF_5')) = k6_partfun1('#skF_3')
    | '#skF_2' = '#skF_1'
    | ~ v2_funct_1('#skF_5')
    | k2_relset_1('#skF_3','#skF_2','#skF_5') != '#skF_2'
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_2')
    | ~ v1_funct_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_108,c_4972])).

tff(c_4988,plain,
    ( k5_relat_1('#skF_5',k2_funct_1('#skF_5')) = k6_partfun1('#skF_3')
    | '#skF_2' = '#skF_1'
    | k1_relat_1('#skF_4') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_112,c_110,c_3725,c_4790,c_4978])).

tff(c_4989,plain,
    ( k5_relat_1('#skF_5',k2_funct_1('#skF_5')) = k6_partfun1('#skF_3')
    | k1_relat_1('#skF_4') != '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_152,c_4988])).

tff(c_5016,plain,(
    k1_relat_1('#skF_4') != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_4989])).

tff(c_4976,plain,
    ( k5_relat_1('#skF_4',k2_funct_1('#skF_4')) = k6_partfun1('#skF_2')
    | '#skF_3' = '#skF_1'
    | ~ v2_funct_1('#skF_4')
    | k2_relset_1('#skF_2','#skF_3','#skF_4') != '#skF_3'
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_3')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_114,c_4972])).

tff(c_4984,plain,
    ( k5_relat_1('#skF_4',k2_funct_1('#skF_4')) = k6_partfun1('#skF_2')
    | '#skF_3' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_118,c_116,c_106,c_102,c_4976])).

tff(c_4985,plain,(
    k5_relat_1('#skF_4',k2_funct_1('#skF_4')) = k6_partfun1('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_151,c_4984])).

tff(c_4993,plain,
    ( r1_tarski(k2_relat_1(k6_partfun1('#skF_2')),k2_relat_1(k2_funct_1('#skF_4')))
    | ~ v1_relat_1(k2_funct_1('#skF_4'))
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_4985,c_22])).

tff(c_4997,plain,(
    r1_tarski('#skF_2',k2_relat_1(k2_funct_1('#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_282,c_671,c_127,c_4993])).

tff(c_5003,plain,
    ( r1_tarski('#skF_2',k1_relat_1('#skF_4'))
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_4997])).

tff(c_5006,plain,(
    r1_tarski('#skF_2',k1_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_282,c_118,c_102,c_5003])).

tff(c_5009,plain,
    ( k1_relat_1('#skF_4') = '#skF_2'
    | ~ v4_relat_1('#skF_4','#skF_2')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_5006,c_305])).

tff(c_5014,plain,(
    k1_relat_1('#skF_4') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_282,c_367,c_5009])).

tff(c_5017,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_5016,c_5014])).

tff(c_5019,plain,(
    k1_relat_1('#skF_4') = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_4989])).

tff(c_52,plain,(
    ! [A_21] :
      ( k1_relat_1(k2_funct_1(A_21)) = k2_relat_1(A_21)
      | ~ v2_funct_1(A_21)
      | ~ v1_funct_1(A_21)
      | ~ v1_relat_1(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_4799,plain,(
    v4_relat_1(k2_funct_1('#skF_5'),k1_relat_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_4789])).

tff(c_18,plain,(
    ! [B_8,A_7] :
      ( r1_tarski(k1_relat_1(B_8),A_7)
      | ~ v4_relat_1(B_8,A_7)
      | ~ v1_relat_1(B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_535,plain,(
    ! [B_124,A_125] :
      ( k1_relat_1(B_124) = A_125
      | ~ r1_tarski(A_125,k1_relat_1(B_124))
      | ~ v4_relat_1(B_124,A_125)
      | ~ v1_relat_1(B_124) ) ),
    inference(resolution,[status(thm)],[c_299,c_8])).

tff(c_555,plain,(
    ! [B_8,B_124] :
      ( k1_relat_1(B_8) = k1_relat_1(B_124)
      | ~ v4_relat_1(B_124,k1_relat_1(B_8))
      | ~ v1_relat_1(B_124)
      | ~ v4_relat_1(B_8,k1_relat_1(B_124))
      | ~ v1_relat_1(B_8) ) ),
    inference(resolution,[status(thm)],[c_18,c_535])).

tff(c_4825,plain,
    ( k1_relat_1(k2_funct_1('#skF_5')) = k1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_funct_1('#skF_5'))
    | ~ v4_relat_1('#skF_4',k1_relat_1(k2_funct_1('#skF_5')))
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_4799,c_555])).

tff(c_4828,plain,
    ( k1_relat_1(k2_funct_1('#skF_5')) = k1_relat_1('#skF_4')
    | ~ v4_relat_1('#skF_4',k1_relat_1(k2_funct_1('#skF_5'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_282,c_4800,c_4825])).

tff(c_4846,plain,(
    ~ v4_relat_1('#skF_4',k1_relat_1(k2_funct_1('#skF_5'))) ),
    inference(splitLeft,[status(thm)],[c_4828])).

tff(c_4849,plain,
    ( ~ v4_relat_1('#skF_4',k2_relat_1('#skF_5'))
    | ~ v2_funct_1('#skF_5')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_52,c_4846])).

tff(c_4851,plain,(
    ~ v4_relat_1('#skF_4',k1_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_285,c_112,c_4790,c_3724,c_4849])).

tff(c_4854,plain,(
    ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_330,c_4851])).

tff(c_4858,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_282,c_4854])).

tff(c_4859,plain,(
    k1_relat_1(k2_funct_1('#skF_5')) = k1_relat_1('#skF_4') ),
    inference(splitRight,[status(thm)],[c_4828])).

tff(c_5024,plain,(
    k1_relat_1(k2_funct_1('#skF_5')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5019,c_4859])).

tff(c_5029,plain,(
    k2_relat_1('#skF_5') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5019,c_3724])).

tff(c_368,plain,(
    v4_relat_1('#skF_5','#skF_3') ),
    inference(resolution,[status(thm)],[c_108,c_355])).

tff(c_5018,plain,(
    k5_relat_1('#skF_5',k2_funct_1('#skF_5')) = k6_partfun1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_4989])).

tff(c_5311,plain,
    ( r1_tarski(k2_relat_1(k6_partfun1('#skF_3')),k2_relat_1(k2_funct_1('#skF_5')))
    | ~ v1_relat_1(k2_funct_1('#skF_5'))
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_5018,c_22])).

tff(c_5315,plain,(
    r1_tarski('#skF_3',k2_relat_1(k2_funct_1('#skF_5'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_285,c_4800,c_127,c_5311])).

tff(c_5321,plain,
    ( r1_tarski('#skF_3',k1_relat_1('#skF_5'))
    | ~ v2_funct_1('#skF_5')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_5315])).

tff(c_5324,plain,(
    r1_tarski('#skF_3',k1_relat_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_285,c_112,c_4790,c_5321])).

tff(c_5343,plain,
    ( k1_relat_1('#skF_5') = '#skF_3'
    | ~ v4_relat_1('#skF_5','#skF_3')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_5324,c_305])).

tff(c_5348,plain,(
    k1_relat_1('#skF_5') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_285,c_368,c_5343])).

tff(c_8832,plain,(
    ! [A_585,B_586] :
      ( k2_funct_1(k2_funct_1(A_585)) = B_586
      | k5_relat_1(B_586,k2_funct_1(A_585)) != k6_partfun1(k1_relat_1(A_585))
      | k2_relat_1(B_586) != k1_relat_1(k2_funct_1(A_585))
      | ~ v2_funct_1(k2_funct_1(A_585))
      | ~ v1_funct_1(B_586)
      | ~ v1_relat_1(B_586)
      | ~ v1_funct_1(k2_funct_1(A_585))
      | ~ v1_relat_1(k2_funct_1(A_585))
      | ~ v2_funct_1(A_585)
      | ~ v1_funct_1(A_585)
      | ~ v1_relat_1(A_585) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_2171])).

tff(c_8840,plain,
    ( k2_funct_1(k2_funct_1('#skF_5')) = '#skF_5'
    | k6_partfun1(k1_relat_1('#skF_5')) != k6_partfun1('#skF_3')
    | k1_relat_1(k2_funct_1('#skF_5')) != k2_relat_1('#skF_5')
    | ~ v2_funct_1(k2_funct_1('#skF_5'))
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5')
    | ~ v1_funct_1(k2_funct_1('#skF_5'))
    | ~ v1_relat_1(k2_funct_1('#skF_5'))
    | ~ v2_funct_1('#skF_5')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_5018,c_8832])).

tff(c_8861,plain,
    ( k2_funct_1(k2_funct_1('#skF_5')) = '#skF_5'
    | ~ v2_funct_1(k2_funct_1('#skF_5'))
    | ~ v1_funct_1(k2_funct_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_285,c_112,c_4790,c_4800,c_285,c_112,c_5024,c_5029,c_5348,c_8840])).

tff(c_8871,plain,(
    ~ v1_funct_1(k2_funct_1('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_8861])).

tff(c_8874,plain,
    ( ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_32,c_8871])).

tff(c_8878,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_285,c_112,c_8874])).

tff(c_8880,plain,(
    v1_funct_1(k2_funct_1('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_8861])).

tff(c_44,plain,(
    ! [A_20] :
      ( v2_funct_1(k2_funct_1(A_20))
      | ~ v2_funct_1(A_20)
      | ~ v1_funct_1(A_20)
      | ~ v1_relat_1(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_8879,plain,
    ( ~ v2_funct_1(k2_funct_1('#skF_5'))
    | k2_funct_1(k2_funct_1('#skF_5')) = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_8861])).

tff(c_8935,plain,(
    ~ v2_funct_1(k2_funct_1('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_8879])).

tff(c_8938,plain,
    ( ~ v2_funct_1('#skF_5')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_44,c_8935])).

tff(c_8942,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_285,c_112,c_4790,c_8938])).

tff(c_8944,plain,(
    v2_funct_1(k2_funct_1('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_8879])).

tff(c_8943,plain,(
    k2_funct_1(k2_funct_1('#skF_5')) = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_8879])).

tff(c_2189,plain,(
    ! [A_21,B_223] :
      ( k2_funct_1(k2_funct_1(A_21)) = B_223
      | k5_relat_1(B_223,k2_funct_1(A_21)) != k6_partfun1(k1_relat_1(A_21))
      | k2_relat_1(B_223) != k1_relat_1(k2_funct_1(A_21))
      | ~ v2_funct_1(k2_funct_1(A_21))
      | ~ v1_funct_1(B_223)
      | ~ v1_relat_1(B_223)
      | ~ v1_funct_1(k2_funct_1(A_21))
      | ~ v1_relat_1(k2_funct_1(A_21))
      | ~ v2_funct_1(A_21)
      | ~ v1_funct_1(A_21)
      | ~ v1_relat_1(A_21) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_2171])).

tff(c_8947,plain,(
    ! [B_223] :
      ( k2_funct_1(k2_funct_1(k2_funct_1('#skF_5'))) = B_223
      | k6_partfun1(k1_relat_1(k2_funct_1('#skF_5'))) != k5_relat_1(B_223,'#skF_5')
      | k2_relat_1(B_223) != k1_relat_1(k2_funct_1(k2_funct_1('#skF_5')))
      | ~ v2_funct_1(k2_funct_1(k2_funct_1('#skF_5')))
      | ~ v1_funct_1(B_223)
      | ~ v1_relat_1(B_223)
      | ~ v1_funct_1(k2_funct_1(k2_funct_1('#skF_5')))
      | ~ v1_relat_1(k2_funct_1(k2_funct_1('#skF_5')))
      | ~ v2_funct_1(k2_funct_1('#skF_5'))
      | ~ v1_funct_1(k2_funct_1('#skF_5'))
      | ~ v1_relat_1(k2_funct_1('#skF_5')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8943,c_2189])).

tff(c_17976,plain,(
    ! [B_826] :
      ( k2_funct_1('#skF_5') = B_826
      | k5_relat_1(B_826,'#skF_5') != k6_partfun1('#skF_2')
      | k2_relat_1(B_826) != '#skF_3'
      | ~ v1_funct_1(B_826)
      | ~ v1_relat_1(B_826) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4800,c_8880,c_8944,c_285,c_8943,c_112,c_8943,c_4790,c_8943,c_5348,c_8943,c_5024,c_8943,c_8947])).

tff(c_18138,plain,
    ( k2_funct_1('#skF_5') = '#skF_4'
    | k5_relat_1('#skF_4','#skF_5') != k6_partfun1('#skF_2')
    | k2_relat_1('#skF_4') != '#skF_3'
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_282,c_17976])).

tff(c_18310,plain,(
    k2_funct_1('#skF_5') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_118,c_482,c_5899,c_18138])).

tff(c_18325,plain,(
    k2_funct_1('#skF_4') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_18310,c_8943])).

tff(c_18342,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_96,c_18325])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:45:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 13.96/6.44  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 13.96/6.47  
% 13.96/6.47  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 13.96/6.47  %$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > o_0_0_xboole_0 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 13.96/6.47  
% 13.96/6.47  %Foreground sorts:
% 13.96/6.47  
% 13.96/6.47  
% 13.96/6.47  %Background operators:
% 13.96/6.47  
% 13.96/6.47  
% 13.96/6.47  %Foreground operators:
% 13.96/6.47  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 13.96/6.47  tff(o_0_0_xboole_0, type, o_0_0_xboole_0: $i).
% 13.96/6.47  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 13.96/6.47  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 13.96/6.47  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 13.96/6.47  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 13.96/6.47  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 13.96/6.47  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 13.96/6.47  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 13.96/6.47  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 13.96/6.47  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 13.96/6.47  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 13.96/6.47  tff('#skF_5', type, '#skF_5': $i).
% 13.96/6.47  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 13.96/6.47  tff('#skF_2', type, '#skF_2': $i).
% 13.96/6.47  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 13.96/6.47  tff('#skF_3', type, '#skF_3': $i).
% 13.96/6.47  tff('#skF_1', type, '#skF_1': $i).
% 13.96/6.47  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 13.96/6.47  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 13.96/6.47  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 13.96/6.47  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 13.96/6.47  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 13.96/6.47  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 13.96/6.47  tff('#skF_4', type, '#skF_4': $i).
% 13.96/6.47  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 13.96/6.47  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 13.96/6.47  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 13.96/6.47  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 13.96/6.47  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 13.96/6.47  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 13.96/6.47  
% 14.18/6.51  tff(f_275, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => ((((k2_relset_1(A, B, C) = B) & r2_relset_1(A, A, k1_partfun1(A, B, B, A, C, D), k6_partfun1(A))) & v2_funct_1(C)) => (((A = k1_xboole_0) | (B = k1_xboole_0)) | (D = k2_funct_1(C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_funct_2)).
% 14.18/6.51  tff(f_154, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 14.18/6.51  tff(f_174, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (v1_funct_1(k1_partfun1(A, B, C, D, E, F)) & m1_subset_1(k1_partfun1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 14.18/6.51  tff(f_178, axiom, (![A]: (v1_partfun1(k6_partfun1(A), A) & m1_subset_1(k6_partfun1(A), k1_zfmisc_1(k2_zfmisc_1(A, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_partfun1)).
% 14.18/6.51  tff(f_162, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 14.18/6.51  tff(f_188, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 14.18/6.51  tff(f_53, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 14.18/6.51  tff(f_45, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 14.18/6.51  tff(f_80, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 14.18/6.51  tff(f_38, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 14.18/6.51  tff(f_32, axiom, (?[A]: v1_xboole_0(A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', rc1_xboole_0)).
% 14.18/6.51  tff(f_30, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 14.18/6.51  tff(f_249, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((k2_relset_1(A, B, C) = B) & v2_funct_1(C)) => ((B = k1_xboole_0) | ((k5_relat_1(C, k2_funct_1(C)) = k6_partfun1(A)) & (k5_relat_1(k2_funct_1(C), C) = k6_partfun1(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t35_funct_2)).
% 14.18/6.51  tff(f_207, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (r2_relset_1(B, B, k1_partfun1(B, A, A, B, D, C), k6_partfun1(B)) => (k2_relset_1(A, B, C) = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t24_funct_2)).
% 14.18/6.51  tff(f_190, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 14.18/6.51  tff(f_64, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 14.18/6.51  tff(f_60, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => r1_tarski(k2_relat_1(k5_relat_1(A, B)), k2_relat_1(B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t45_relat_1)).
% 14.18/6.51  tff(f_127, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (((v2_funct_1(A) & (k2_relat_1(B) = k1_relat_1(A))) & (k5_relat_1(B, A) = k6_relat_1(k2_relat_1(A)))) => (B = k2_funct_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_funct_1)).
% 14.18/6.51  tff(f_150, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 14.18/6.51  tff(f_110, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k2_relat_1(A) = k1_relat_1(k2_funct_1(A))) & (k1_relat_1(A) = k2_relat_1(k2_funct_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_funct_1)).
% 14.18/6.51  tff(f_51, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d18_relat_1)).
% 14.18/6.51  tff(f_88, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v2_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc4_funct_1)).
% 14.18/6.51  tff(f_233, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, B, C)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => ((v2_funct_1(k1_partfun1(A, B, B, C, D, E)) & (k2_relset_1(A, B, D) = B)) => (((C = k1_xboole_0) & ~(B = k1_xboole_0)) | (v2_funct_1(D) & v2_funct_1(E)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t30_funct_2)).
% 14.18/6.51  tff(f_100, axiom, (![A]: (((v1_relat_1(A) & v1_funct_1(A)) & v2_funct_1(A)) => ((v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))) & v2_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_funct_1)).
% 14.18/6.51  tff(c_96, plain, (k2_funct_1('#skF_4')!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_275])).
% 14.18/6.51  tff(c_118, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_275])).
% 14.18/6.51  tff(c_106, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_4')='#skF_3'), inference(cnfTransformation, [status(thm)], [f_275])).
% 14.18/6.51  tff(c_114, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_275])).
% 14.18/6.51  tff(c_469, plain, (![A_119, B_120, C_121]: (k2_relset_1(A_119, B_120, C_121)=k2_relat_1(C_121) | ~m1_subset_1(C_121, k1_zfmisc_1(k2_zfmisc_1(A_119, B_120))))), inference(cnfTransformation, [status(thm)], [f_154])).
% 14.18/6.51  tff(c_475, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_114, c_469])).
% 14.18/6.51  tff(c_482, plain, (k2_relat_1('#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_106, c_475])).
% 14.18/6.51  tff(c_112, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_275])).
% 14.18/6.51  tff(c_108, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_275])).
% 14.18/6.51  tff(c_1700, plain, (![C_199, A_197, F_201, D_200, E_202, B_198]: (m1_subset_1(k1_partfun1(A_197, B_198, C_199, D_200, E_202, F_201), k1_zfmisc_1(k2_zfmisc_1(A_197, D_200))) | ~m1_subset_1(F_201, k1_zfmisc_1(k2_zfmisc_1(C_199, D_200))) | ~v1_funct_1(F_201) | ~m1_subset_1(E_202, k1_zfmisc_1(k2_zfmisc_1(A_197, B_198))) | ~v1_funct_1(E_202))), inference(cnfTransformation, [status(thm)], [f_174])).
% 14.18/6.51  tff(c_76, plain, (![A_45]: (m1_subset_1(k6_partfun1(A_45), k1_zfmisc_1(k2_zfmisc_1(A_45, A_45))))), inference(cnfTransformation, [status(thm)], [f_178])).
% 14.18/6.51  tff(c_104, plain, (r2_relset_1('#skF_2', '#skF_2', k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5'), k6_partfun1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_275])).
% 14.18/6.51  tff(c_616, plain, (![D_129, C_130, A_131, B_132]: (D_129=C_130 | ~r2_relset_1(A_131, B_132, C_130, D_129) | ~m1_subset_1(D_129, k1_zfmisc_1(k2_zfmisc_1(A_131, B_132))) | ~m1_subset_1(C_130, k1_zfmisc_1(k2_zfmisc_1(A_131, B_132))))), inference(cnfTransformation, [status(thm)], [f_162])).
% 14.18/6.51  tff(c_624, plain, (k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5')=k6_partfun1('#skF_2') | ~m1_subset_1(k6_partfun1('#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'))) | ~m1_subset_1(k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(resolution, [status(thm)], [c_104, c_616])).
% 14.18/6.51  tff(c_639, plain, (k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5')=k6_partfun1('#skF_2') | ~m1_subset_1(k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_624])).
% 14.18/6.51  tff(c_672, plain, (~m1_subset_1(k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(splitLeft, [status(thm)], [c_639])).
% 14.18/6.51  tff(c_1723, plain, (~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2'))) | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_1700, c_672])).
% 14.18/6.51  tff(c_1755, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_118, c_114, c_112, c_108, c_1723])).
% 14.18/6.51  tff(c_1756, plain, (k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5')=k6_partfun1('#skF_2')), inference(splitRight, [status(thm)], [c_639])).
% 14.18/6.51  tff(c_4830, plain, (![E_385, C_386, F_383, D_384, B_382, A_387]: (k1_partfun1(A_387, B_382, C_386, D_384, E_385, F_383)=k5_relat_1(E_385, F_383) | ~m1_subset_1(F_383, k1_zfmisc_1(k2_zfmisc_1(C_386, D_384))) | ~v1_funct_1(F_383) | ~m1_subset_1(E_385, k1_zfmisc_1(k2_zfmisc_1(A_387, B_382))) | ~v1_funct_1(E_385))), inference(cnfTransformation, [status(thm)], [f_188])).
% 14.18/6.51  tff(c_4836, plain, (![A_387, B_382, E_385]: (k1_partfun1(A_387, B_382, '#skF_3', '#skF_2', E_385, '#skF_5')=k5_relat_1(E_385, '#skF_5') | ~v1_funct_1('#skF_5') | ~m1_subset_1(E_385, k1_zfmisc_1(k2_zfmisc_1(A_387, B_382))) | ~v1_funct_1(E_385))), inference(resolution, [status(thm)], [c_108, c_4830])).
% 14.18/6.51  tff(c_5868, plain, (![A_431, B_432, E_433]: (k1_partfun1(A_431, B_432, '#skF_3', '#skF_2', E_433, '#skF_5')=k5_relat_1(E_433, '#skF_5') | ~m1_subset_1(E_433, k1_zfmisc_1(k2_zfmisc_1(A_431, B_432))) | ~v1_funct_1(E_433))), inference(demodulation, [status(thm), theory('equality')], [c_112, c_4836])).
% 14.18/6.51  tff(c_5883, plain, (k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5')=k5_relat_1('#skF_4', '#skF_5') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_114, c_5868])).
% 14.18/6.51  tff(c_5899, plain, (k5_relat_1('#skF_4', '#skF_5')=k6_partfun1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_118, c_1756, c_5883])).
% 14.18/6.51  tff(c_20, plain, (![A_9, B_10]: (v1_relat_1(k2_zfmisc_1(A_9, B_10)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 14.18/6.51  tff(c_267, plain, (![B_89, A_90]: (v1_relat_1(B_89) | ~m1_subset_1(B_89, k1_zfmisc_1(A_90)) | ~v1_relat_1(A_90))), inference(cnfTransformation, [status(thm)], [f_45])).
% 14.18/6.51  tff(c_273, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_114, c_267])).
% 14.18/6.51  tff(c_282, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_20, c_273])).
% 14.18/6.51  tff(c_276, plain, (v1_relat_1('#skF_5') | ~v1_relat_1(k2_zfmisc_1('#skF_3', '#skF_2'))), inference(resolution, [status(thm)], [c_108, c_267])).
% 14.18/6.51  tff(c_285, plain, (v1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_20, c_276])).
% 14.18/6.51  tff(c_34, plain, (![A_17]: (v1_relat_1(k2_funct_1(A_17)) | ~v1_funct_1(A_17) | ~v1_relat_1(A_17))), inference(cnfTransformation, [status(thm)], [f_80])).
% 14.18/6.51  tff(c_12, plain, (![B_3]: (r1_tarski(B_3, B_3))), inference(cnfTransformation, [status(thm)], [f_38])).
% 14.18/6.51  tff(c_6, plain, (v1_xboole_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_32])).
% 14.18/6.51  tff(c_134, plain, (![A_72]: (k1_xboole_0=A_72 | ~v1_xboole_0(A_72))), inference(cnfTransformation, [status(thm)], [f_30])).
% 14.18/6.51  tff(c_142, plain, (k1_xboole_0='#skF_1'), inference(resolution, [status(thm)], [c_6, c_134])).
% 14.18/6.51  tff(c_100, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_275])).
% 14.18/6.51  tff(c_152, plain, ('#skF_2'!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_142, c_100])).
% 14.18/6.51  tff(c_110, plain, (v1_funct_2('#skF_5', '#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_275])).
% 14.18/6.51  tff(c_483, plain, (k2_relset_1('#skF_3', '#skF_2', '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_108, c_469])).
% 14.18/6.51  tff(c_92, plain, (![B_65, C_66, A_64]: (k6_partfun1(B_65)=k5_relat_1(k2_funct_1(C_66), C_66) | k1_xboole_0=B_65 | ~v2_funct_1(C_66) | k2_relset_1(A_64, B_65, C_66)!=B_65 | ~m1_subset_1(C_66, k1_zfmisc_1(k2_zfmisc_1(A_64, B_65))) | ~v1_funct_2(C_66, A_64, B_65) | ~v1_funct_1(C_66))), inference(cnfTransformation, [status(thm)], [f_249])).
% 14.18/6.51  tff(c_2608, plain, (![B_256, C_257, A_258]: (k6_partfun1(B_256)=k5_relat_1(k2_funct_1(C_257), C_257) | B_256='#skF_1' | ~v2_funct_1(C_257) | k2_relset_1(A_258, B_256, C_257)!=B_256 | ~m1_subset_1(C_257, k1_zfmisc_1(k2_zfmisc_1(A_258, B_256))) | ~v1_funct_2(C_257, A_258, B_256) | ~v1_funct_1(C_257))), inference(demodulation, [status(thm), theory('equality')], [c_142, c_92])).
% 14.18/6.51  tff(c_2614, plain, (k5_relat_1(k2_funct_1('#skF_5'), '#skF_5')=k6_partfun1('#skF_2') | '#skF_2'='#skF_1' | ~v2_funct_1('#skF_5') | k2_relset_1('#skF_3', '#skF_2', '#skF_5')!='#skF_2' | ~v1_funct_2('#skF_5', '#skF_3', '#skF_2') | ~v1_funct_1('#skF_5')), inference(resolution, [status(thm)], [c_108, c_2608])).
% 14.18/6.51  tff(c_2624, plain, (k5_relat_1(k2_funct_1('#skF_5'), '#skF_5')=k6_partfun1('#skF_2') | '#skF_2'='#skF_1' | ~v2_funct_1('#skF_5') | k2_relat_1('#skF_5')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_112, c_110, c_483, c_2614])).
% 14.18/6.51  tff(c_2625, plain, (k5_relat_1(k2_funct_1('#skF_5'), '#skF_5')=k6_partfun1('#skF_2') | ~v2_funct_1('#skF_5') | k2_relat_1('#skF_5')!='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_152, c_2624])).
% 14.18/6.51  tff(c_2802, plain, (k2_relat_1('#skF_5')!='#skF_2'), inference(splitLeft, [status(thm)], [c_2625])).
% 14.18/6.51  tff(c_116, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_275])).
% 14.18/6.51  tff(c_438, plain, (![A_114, B_115, D_116]: (r2_relset_1(A_114, B_115, D_116, D_116) | ~m1_subset_1(D_116, k1_zfmisc_1(k2_zfmisc_1(A_114, B_115))))), inference(cnfTransformation, [status(thm)], [f_162])).
% 14.18/6.51  tff(c_445, plain, (![A_45]: (r2_relset_1(A_45, A_45, k6_partfun1(A_45), k6_partfun1(A_45)))), inference(resolution, [status(thm)], [c_76, c_438])).
% 14.18/6.51  tff(c_3455, plain, (![A_299, B_300, C_301, D_302]: (k2_relset_1(A_299, B_300, C_301)=B_300 | ~r2_relset_1(B_300, B_300, k1_partfun1(B_300, A_299, A_299, B_300, D_302, C_301), k6_partfun1(B_300)) | ~m1_subset_1(D_302, k1_zfmisc_1(k2_zfmisc_1(B_300, A_299))) | ~v1_funct_2(D_302, B_300, A_299) | ~v1_funct_1(D_302) | ~m1_subset_1(C_301, k1_zfmisc_1(k2_zfmisc_1(A_299, B_300))) | ~v1_funct_2(C_301, A_299, B_300) | ~v1_funct_1(C_301))), inference(cnfTransformation, [status(thm)], [f_207])).
% 14.18/6.51  tff(c_3461, plain, (k2_relset_1('#skF_3', '#skF_2', '#skF_5')='#skF_2' | ~r2_relset_1('#skF_2', '#skF_2', k6_partfun1('#skF_2'), k6_partfun1('#skF_2')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3') | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2'))) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_2') | ~v1_funct_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_1756, c_3455])).
% 14.18/6.51  tff(c_3465, plain, (k2_relat_1('#skF_5')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_112, c_110, c_108, c_118, c_116, c_114, c_445, c_483, c_3461])).
% 14.18/6.51  tff(c_3467, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2802, c_3465])).
% 14.18/6.51  tff(c_3469, plain, (k2_relat_1('#skF_5')='#skF_2'), inference(splitRight, [status(thm)], [c_2625])).
% 14.18/6.51  tff(c_80, plain, (![A_52]: (k6_relat_1(A_52)=k6_partfun1(A_52))), inference(cnfTransformation, [status(thm)], [f_190])).
% 14.18/6.51  tff(c_26, plain, (![A_14]: (k2_relat_1(k6_relat_1(A_14))=A_14)), inference(cnfTransformation, [status(thm)], [f_64])).
% 14.18/6.51  tff(c_127, plain, (![A_14]: (k2_relat_1(k6_partfun1(A_14))=A_14)), inference(demodulation, [status(thm), theory('equality')], [c_80, c_26])).
% 14.18/6.51  tff(c_2409, plain, (![C_248, B_244, E_247, F_245, A_249, D_246]: (k1_partfun1(A_249, B_244, C_248, D_246, E_247, F_245)=k5_relat_1(E_247, F_245) | ~m1_subset_1(F_245, k1_zfmisc_1(k2_zfmisc_1(C_248, D_246))) | ~v1_funct_1(F_245) | ~m1_subset_1(E_247, k1_zfmisc_1(k2_zfmisc_1(A_249, B_244))) | ~v1_funct_1(E_247))), inference(cnfTransformation, [status(thm)], [f_188])).
% 14.18/6.51  tff(c_2415, plain, (![A_249, B_244, E_247]: (k1_partfun1(A_249, B_244, '#skF_3', '#skF_2', E_247, '#skF_5')=k5_relat_1(E_247, '#skF_5') | ~v1_funct_1('#skF_5') | ~m1_subset_1(E_247, k1_zfmisc_1(k2_zfmisc_1(A_249, B_244))) | ~v1_funct_1(E_247))), inference(resolution, [status(thm)], [c_108, c_2409])).
% 14.18/6.51  tff(c_2510, plain, (![A_253, B_254, E_255]: (k1_partfun1(A_253, B_254, '#skF_3', '#skF_2', E_255, '#skF_5')=k5_relat_1(E_255, '#skF_5') | ~m1_subset_1(E_255, k1_zfmisc_1(k2_zfmisc_1(A_253, B_254))) | ~v1_funct_1(E_255))), inference(demodulation, [status(thm), theory('equality')], [c_112, c_2415])).
% 14.18/6.51  tff(c_2516, plain, (k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5')=k5_relat_1('#skF_4', '#skF_5') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_114, c_2510])).
% 14.18/6.51  tff(c_2525, plain, (k5_relat_1('#skF_4', '#skF_5')=k6_partfun1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_118, c_1756, c_2516])).
% 14.18/6.51  tff(c_22, plain, (![A_11, B_13]: (r1_tarski(k2_relat_1(k5_relat_1(A_11, B_13)), k2_relat_1(B_13)) | ~v1_relat_1(B_13) | ~v1_relat_1(A_11))), inference(cnfTransformation, [status(thm)], [f_60])).
% 14.18/6.51  tff(c_2597, plain, (r1_tarski(k2_relat_1(k6_partfun1('#skF_2')), k2_relat_1('#skF_5')) | ~v1_relat_1('#skF_5') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_2525, c_22])).
% 14.18/6.51  tff(c_2601, plain, (r1_tarski('#skF_2', k2_relat_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_282, c_285, c_127, c_2597])).
% 14.18/6.51  tff(c_8, plain, (![B_3, A_2]: (B_3=A_2 | ~r1_tarski(B_3, A_2) | ~r1_tarski(A_2, B_3))), inference(cnfTransformation, [status(thm)], [f_38])).
% 14.18/6.51  tff(c_2605, plain, (k2_relat_1('#skF_5')='#skF_2' | ~r1_tarski(k2_relat_1('#skF_5'), '#skF_2')), inference(resolution, [status(thm)], [c_2601, c_8])).
% 14.18/6.51  tff(c_2606, plain, (~r1_tarski(k2_relat_1('#skF_5'), '#skF_2')), inference(splitLeft, [status(thm)], [c_2605])).
% 14.18/6.51  tff(c_3470, plain, (~r1_tarski('#skF_2', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_3469, c_2606])).
% 14.18/6.51  tff(c_3476, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12, c_3470])).
% 14.18/6.51  tff(c_3477, plain, (k2_relat_1('#skF_5')='#skF_2'), inference(splitRight, [status(thm)], [c_2605])).
% 14.18/6.51  tff(c_102, plain, (v2_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_275])).
% 14.18/6.51  tff(c_54, plain, (![A_22, B_24]: (k2_funct_1(A_22)=B_24 | k6_relat_1(k2_relat_1(A_22))!=k5_relat_1(B_24, A_22) | k2_relat_1(B_24)!=k1_relat_1(A_22) | ~v2_funct_1(A_22) | ~v1_funct_1(B_24) | ~v1_relat_1(B_24) | ~v1_funct_1(A_22) | ~v1_relat_1(A_22))), inference(cnfTransformation, [status(thm)], [f_127])).
% 14.18/6.51  tff(c_2171, plain, (![A_222, B_223]: (k2_funct_1(A_222)=B_223 | k6_partfun1(k2_relat_1(A_222))!=k5_relat_1(B_223, A_222) | k2_relat_1(B_223)!=k1_relat_1(A_222) | ~v2_funct_1(A_222) | ~v1_funct_1(B_223) | ~v1_relat_1(B_223) | ~v1_funct_1(A_222) | ~v1_relat_1(A_222))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_54])).
% 14.18/6.51  tff(c_2187, plain, (![B_223]: (k2_funct_1('#skF_4')=B_223 | k5_relat_1(B_223, '#skF_4')!=k6_partfun1('#skF_3') | k2_relat_1(B_223)!=k1_relat_1('#skF_4') | ~v2_funct_1('#skF_4') | ~v1_funct_1(B_223) | ~v1_relat_1(B_223) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_482, c_2171])).
% 14.18/6.51  tff(c_2243, plain, (![B_225]: (k2_funct_1('#skF_4')=B_225 | k5_relat_1(B_225, '#skF_4')!=k6_partfun1('#skF_3') | k2_relat_1(B_225)!=k1_relat_1('#skF_4') | ~v1_funct_1(B_225) | ~v1_relat_1(B_225))), inference(demodulation, [status(thm), theory('equality')], [c_282, c_118, c_102, c_2187])).
% 14.18/6.51  tff(c_2252, plain, (k2_funct_1('#skF_4')='#skF_5' | k5_relat_1('#skF_5', '#skF_4')!=k6_partfun1('#skF_3') | k2_relat_1('#skF_5')!=k1_relat_1('#skF_4') | ~v1_funct_1('#skF_5')), inference(resolution, [status(thm)], [c_285, c_2243])).
% 14.18/6.51  tff(c_2271, plain, (k2_funct_1('#skF_4')='#skF_5' | k5_relat_1('#skF_5', '#skF_4')!=k6_partfun1('#skF_3') | k2_relat_1('#skF_5')!=k1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_112, c_2252])).
% 14.18/6.51  tff(c_2272, plain, (k5_relat_1('#skF_5', '#skF_4')!=k6_partfun1('#skF_3') | k2_relat_1('#skF_5')!=k1_relat_1('#skF_4')), inference(negUnitSimplification, [status(thm)], [c_96, c_2271])).
% 14.18/6.51  tff(c_2281, plain, (k2_relat_1('#skF_5')!=k1_relat_1('#skF_4')), inference(splitLeft, [status(thm)], [c_2272])).
% 14.18/6.51  tff(c_3480, plain, (k1_relat_1('#skF_4')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_3477, c_2281])).
% 14.18/6.51  tff(c_355, plain, (![C_106, A_107, B_108]: (v4_relat_1(C_106, A_107) | ~m1_subset_1(C_106, k1_zfmisc_1(k2_zfmisc_1(A_107, B_108))))), inference(cnfTransformation, [status(thm)], [f_150])).
% 14.18/6.51  tff(c_367, plain, (v4_relat_1('#skF_4', '#skF_2')), inference(resolution, [status(thm)], [c_114, c_355])).
% 14.18/6.51  tff(c_50, plain, (![A_21]: (k2_relat_1(k2_funct_1(A_21))=k1_relat_1(A_21) | ~v2_funct_1(A_21) | ~v1_funct_1(A_21) | ~v1_relat_1(A_21))), inference(cnfTransformation, [status(thm)], [f_110])).
% 14.18/6.51  tff(c_412, plain, (![A_113]: (k1_relat_1(k2_funct_1(A_113))=k2_relat_1(A_113) | ~v2_funct_1(A_113) | ~v1_funct_1(A_113) | ~v1_relat_1(A_113))), inference(cnfTransformation, [status(thm)], [f_110])).
% 14.18/6.51  tff(c_316, plain, (![B_100, A_101]: (v4_relat_1(B_100, A_101) | ~r1_tarski(k1_relat_1(B_100), A_101) | ~v1_relat_1(B_100))), inference(cnfTransformation, [status(thm)], [f_51])).
% 14.18/6.51  tff(c_330, plain, (![B_100]: (v4_relat_1(B_100, k1_relat_1(B_100)) | ~v1_relat_1(B_100))), inference(resolution, [status(thm)], [c_12, c_316])).
% 14.18/6.51  tff(c_640, plain, (![A_133]: (v4_relat_1(k2_funct_1(A_133), k2_relat_1(A_133)) | ~v1_relat_1(k2_funct_1(A_133)) | ~v2_funct_1(A_133) | ~v1_funct_1(A_133) | ~v1_relat_1(A_133))), inference(superposition, [status(thm), theory('equality')], [c_412, c_330])).
% 14.18/6.51  tff(c_646, plain, (v4_relat_1(k2_funct_1('#skF_4'), '#skF_3') | ~v1_relat_1(k2_funct_1('#skF_4')) | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_482, c_640])).
% 14.18/6.51  tff(c_657, plain, (v4_relat_1(k2_funct_1('#skF_4'), '#skF_3') | ~v1_relat_1(k2_funct_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_282, c_118, c_102, c_646])).
% 14.18/6.51  tff(c_662, plain, (~v1_relat_1(k2_funct_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_657])).
% 14.18/6.51  tff(c_665, plain, (~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_34, c_662])).
% 14.18/6.51  tff(c_669, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_282, c_118, c_665])).
% 14.18/6.51  tff(c_671, plain, (v1_relat_1(k2_funct_1('#skF_4'))), inference(splitRight, [status(thm)], [c_657])).
% 14.18/6.51  tff(c_98, plain, (k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_275])).
% 14.18/6.51  tff(c_151, plain, ('#skF_3'!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_142, c_98])).
% 14.18/6.51  tff(c_94, plain, (![A_64, C_66, B_65]: (k6_partfun1(A_64)=k5_relat_1(C_66, k2_funct_1(C_66)) | k1_xboole_0=B_65 | ~v2_funct_1(C_66) | k2_relset_1(A_64, B_65, C_66)!=B_65 | ~m1_subset_1(C_66, k1_zfmisc_1(k2_zfmisc_1(A_64, B_65))) | ~v1_funct_2(C_66, A_64, B_65) | ~v1_funct_1(C_66))), inference(cnfTransformation, [status(thm)], [f_249])).
% 14.18/6.51  tff(c_3678, plain, (![A_309, C_310, B_311]: (k6_partfun1(A_309)=k5_relat_1(C_310, k2_funct_1(C_310)) | B_311='#skF_1' | ~v2_funct_1(C_310) | k2_relset_1(A_309, B_311, C_310)!=B_311 | ~m1_subset_1(C_310, k1_zfmisc_1(k2_zfmisc_1(A_309, B_311))) | ~v1_funct_2(C_310, A_309, B_311) | ~v1_funct_1(C_310))), inference(demodulation, [status(thm), theory('equality')], [c_142, c_94])).
% 14.18/6.51  tff(c_3682, plain, (k5_relat_1('#skF_4', k2_funct_1('#skF_4'))=k6_partfun1('#skF_2') | '#skF_3'='#skF_1' | ~v2_funct_1('#skF_4') | k2_relset_1('#skF_2', '#skF_3', '#skF_4')!='#skF_3' | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_114, c_3678])).
% 14.18/6.51  tff(c_3690, plain, (k5_relat_1('#skF_4', k2_funct_1('#skF_4'))=k6_partfun1('#skF_2') | '#skF_3'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_118, c_116, c_106, c_102, c_3682])).
% 14.18/6.51  tff(c_3691, plain, (k5_relat_1('#skF_4', k2_funct_1('#skF_4'))=k6_partfun1('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_151, c_3690])).
% 14.18/6.51  tff(c_3699, plain, (r1_tarski(k2_relat_1(k6_partfun1('#skF_2')), k2_relat_1(k2_funct_1('#skF_4'))) | ~v1_relat_1(k2_funct_1('#skF_4')) | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_3691, c_22])).
% 14.18/6.51  tff(c_3703, plain, (r1_tarski('#skF_2', k2_relat_1(k2_funct_1('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_282, c_671, c_127, c_3699])).
% 14.18/6.51  tff(c_3709, plain, (r1_tarski('#skF_2', k1_relat_1('#skF_4')) | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_50, c_3703])).
% 14.18/6.51  tff(c_3712, plain, (r1_tarski('#skF_2', k1_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_282, c_118, c_102, c_3709])).
% 14.18/6.51  tff(c_299, plain, (![B_94, A_95]: (r1_tarski(k1_relat_1(B_94), A_95) | ~v4_relat_1(B_94, A_95) | ~v1_relat_1(B_94))), inference(cnfTransformation, [status(thm)], [f_51])).
% 14.18/6.51  tff(c_305, plain, (![B_94, A_95]: (k1_relat_1(B_94)=A_95 | ~r1_tarski(A_95, k1_relat_1(B_94)) | ~v4_relat_1(B_94, A_95) | ~v1_relat_1(B_94))), inference(resolution, [status(thm)], [c_299, c_8])).
% 14.18/6.51  tff(c_3715, plain, (k1_relat_1('#skF_4')='#skF_2' | ~v4_relat_1('#skF_4', '#skF_2') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_3712, c_305])).
% 14.18/6.51  tff(c_3720, plain, (k1_relat_1('#skF_4')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_282, c_367, c_3715])).
% 14.18/6.51  tff(c_3722, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3480, c_3720])).
% 14.18/6.51  tff(c_3724, plain, (k2_relat_1('#skF_5')=k1_relat_1('#skF_4')), inference(splitRight, [status(thm)], [c_2272])).
% 14.18/6.51  tff(c_418, plain, (![A_113]: (v4_relat_1(k2_funct_1(A_113), k2_relat_1(A_113)) | ~v1_relat_1(k2_funct_1(A_113)) | ~v2_funct_1(A_113) | ~v1_funct_1(A_113) | ~v1_relat_1(A_113))), inference(superposition, [status(thm), theory('equality')], [c_412, c_330])).
% 14.18/6.51  tff(c_3737, plain, (v4_relat_1(k2_funct_1('#skF_5'), k1_relat_1('#skF_4')) | ~v1_relat_1(k2_funct_1('#skF_5')) | ~v2_funct_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_3724, c_418])).
% 14.18/6.51  tff(c_3753, plain, (v4_relat_1(k2_funct_1('#skF_5'), k1_relat_1('#skF_4')) | ~v1_relat_1(k2_funct_1('#skF_5')) | ~v2_funct_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_285, c_112, c_3737])).
% 14.18/6.51  tff(c_3815, plain, (~v2_funct_1('#skF_5')), inference(splitLeft, [status(thm)], [c_3753])).
% 14.18/6.51  tff(c_42, plain, (![A_19]: (v2_funct_1(k6_relat_1(A_19)))), inference(cnfTransformation, [status(thm)], [f_88])).
% 14.18/6.51  tff(c_121, plain, (![A_19]: (v2_funct_1(k6_partfun1(A_19)))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_42])).
% 14.18/6.51  tff(c_86, plain, (![B_59, A_58, D_61, E_63, C_60]: (k1_xboole_0=C_60 | v2_funct_1(E_63) | k2_relset_1(A_58, B_59, D_61)!=B_59 | ~v2_funct_1(k1_partfun1(A_58, B_59, B_59, C_60, D_61, E_63)) | ~m1_subset_1(E_63, k1_zfmisc_1(k2_zfmisc_1(B_59, C_60))) | ~v1_funct_2(E_63, B_59, C_60) | ~v1_funct_1(E_63) | ~m1_subset_1(D_61, k1_zfmisc_1(k2_zfmisc_1(A_58, B_59))) | ~v1_funct_2(D_61, A_58, B_59) | ~v1_funct_1(D_61))), inference(cnfTransformation, [status(thm)], [f_233])).
% 14.18/6.51  tff(c_4777, plain, (![A_375, E_376, D_374, C_377, B_373]: (C_377='#skF_1' | v2_funct_1(E_376) | k2_relset_1(A_375, B_373, D_374)!=B_373 | ~v2_funct_1(k1_partfun1(A_375, B_373, B_373, C_377, D_374, E_376)) | ~m1_subset_1(E_376, k1_zfmisc_1(k2_zfmisc_1(B_373, C_377))) | ~v1_funct_2(E_376, B_373, C_377) | ~v1_funct_1(E_376) | ~m1_subset_1(D_374, k1_zfmisc_1(k2_zfmisc_1(A_375, B_373))) | ~v1_funct_2(D_374, A_375, B_373) | ~v1_funct_1(D_374))), inference(demodulation, [status(thm), theory('equality')], [c_142, c_86])).
% 14.18/6.51  tff(c_4781, plain, ('#skF_2'='#skF_1' | v2_funct_1('#skF_5') | k2_relset_1('#skF_2', '#skF_3', '#skF_4')!='#skF_3' | ~v2_funct_1(k6_partfun1('#skF_2')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2'))) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_2') | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3') | ~v1_funct_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1756, c_4777])).
% 14.18/6.51  tff(c_4786, plain, ('#skF_2'='#skF_1' | v2_funct_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_118, c_116, c_114, c_112, c_110, c_108, c_121, c_106, c_4781])).
% 14.18/6.51  tff(c_4788, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3815, c_152, c_4786])).
% 14.18/6.51  tff(c_4789, plain, (~v1_relat_1(k2_funct_1('#skF_5')) | v4_relat_1(k2_funct_1('#skF_5'), k1_relat_1('#skF_4'))), inference(splitRight, [status(thm)], [c_3753])).
% 14.18/6.51  tff(c_4791, plain, (~v1_relat_1(k2_funct_1('#skF_5'))), inference(splitLeft, [status(thm)], [c_4789])).
% 14.18/6.51  tff(c_4794, plain, (~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_34, c_4791])).
% 14.18/6.51  tff(c_4798, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_285, c_112, c_4794])).
% 14.18/6.51  tff(c_4800, plain, (v1_relat_1(k2_funct_1('#skF_5'))), inference(splitRight, [status(thm)], [c_4789])).
% 14.18/6.51  tff(c_32, plain, (![A_17]: (v1_funct_1(k2_funct_1(A_17)) | ~v1_funct_1(A_17) | ~v1_relat_1(A_17))), inference(cnfTransformation, [status(thm)], [f_80])).
% 14.18/6.51  tff(c_4790, plain, (v2_funct_1('#skF_5')), inference(splitRight, [status(thm)], [c_3753])).
% 14.18/6.51  tff(c_3725, plain, (k2_relset_1('#skF_3', '#skF_2', '#skF_5')=k1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_3724, c_483])).
% 14.18/6.51  tff(c_4972, plain, (![A_393, C_394, B_395]: (k6_partfun1(A_393)=k5_relat_1(C_394, k2_funct_1(C_394)) | B_395='#skF_1' | ~v2_funct_1(C_394) | k2_relset_1(A_393, B_395, C_394)!=B_395 | ~m1_subset_1(C_394, k1_zfmisc_1(k2_zfmisc_1(A_393, B_395))) | ~v1_funct_2(C_394, A_393, B_395) | ~v1_funct_1(C_394))), inference(demodulation, [status(thm), theory('equality')], [c_142, c_94])).
% 14.18/6.51  tff(c_4978, plain, (k5_relat_1('#skF_5', k2_funct_1('#skF_5'))=k6_partfun1('#skF_3') | '#skF_2'='#skF_1' | ~v2_funct_1('#skF_5') | k2_relset_1('#skF_3', '#skF_2', '#skF_5')!='#skF_2' | ~v1_funct_2('#skF_5', '#skF_3', '#skF_2') | ~v1_funct_1('#skF_5')), inference(resolution, [status(thm)], [c_108, c_4972])).
% 14.18/6.51  tff(c_4988, plain, (k5_relat_1('#skF_5', k2_funct_1('#skF_5'))=k6_partfun1('#skF_3') | '#skF_2'='#skF_1' | k1_relat_1('#skF_4')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_112, c_110, c_3725, c_4790, c_4978])).
% 14.18/6.51  tff(c_4989, plain, (k5_relat_1('#skF_5', k2_funct_1('#skF_5'))=k6_partfun1('#skF_3') | k1_relat_1('#skF_4')!='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_152, c_4988])).
% 14.18/6.51  tff(c_5016, plain, (k1_relat_1('#skF_4')!='#skF_2'), inference(splitLeft, [status(thm)], [c_4989])).
% 14.18/6.51  tff(c_4976, plain, (k5_relat_1('#skF_4', k2_funct_1('#skF_4'))=k6_partfun1('#skF_2') | '#skF_3'='#skF_1' | ~v2_funct_1('#skF_4') | k2_relset_1('#skF_2', '#skF_3', '#skF_4')!='#skF_3' | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_114, c_4972])).
% 14.18/6.51  tff(c_4984, plain, (k5_relat_1('#skF_4', k2_funct_1('#skF_4'))=k6_partfun1('#skF_2') | '#skF_3'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_118, c_116, c_106, c_102, c_4976])).
% 14.18/6.51  tff(c_4985, plain, (k5_relat_1('#skF_4', k2_funct_1('#skF_4'))=k6_partfun1('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_151, c_4984])).
% 14.18/6.51  tff(c_4993, plain, (r1_tarski(k2_relat_1(k6_partfun1('#skF_2')), k2_relat_1(k2_funct_1('#skF_4'))) | ~v1_relat_1(k2_funct_1('#skF_4')) | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_4985, c_22])).
% 14.18/6.51  tff(c_4997, plain, (r1_tarski('#skF_2', k2_relat_1(k2_funct_1('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_282, c_671, c_127, c_4993])).
% 14.18/6.51  tff(c_5003, plain, (r1_tarski('#skF_2', k1_relat_1('#skF_4')) | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_50, c_4997])).
% 14.18/6.51  tff(c_5006, plain, (r1_tarski('#skF_2', k1_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_282, c_118, c_102, c_5003])).
% 14.18/6.51  tff(c_5009, plain, (k1_relat_1('#skF_4')='#skF_2' | ~v4_relat_1('#skF_4', '#skF_2') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_5006, c_305])).
% 14.18/6.51  tff(c_5014, plain, (k1_relat_1('#skF_4')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_282, c_367, c_5009])).
% 14.18/6.51  tff(c_5017, plain, $false, inference(negUnitSimplification, [status(thm)], [c_5016, c_5014])).
% 14.18/6.51  tff(c_5019, plain, (k1_relat_1('#skF_4')='#skF_2'), inference(splitRight, [status(thm)], [c_4989])).
% 14.18/6.51  tff(c_52, plain, (![A_21]: (k1_relat_1(k2_funct_1(A_21))=k2_relat_1(A_21) | ~v2_funct_1(A_21) | ~v1_funct_1(A_21) | ~v1_relat_1(A_21))), inference(cnfTransformation, [status(thm)], [f_110])).
% 14.18/6.51  tff(c_4799, plain, (v4_relat_1(k2_funct_1('#skF_5'), k1_relat_1('#skF_4'))), inference(splitRight, [status(thm)], [c_4789])).
% 14.18/6.51  tff(c_18, plain, (![B_8, A_7]: (r1_tarski(k1_relat_1(B_8), A_7) | ~v4_relat_1(B_8, A_7) | ~v1_relat_1(B_8))), inference(cnfTransformation, [status(thm)], [f_51])).
% 14.18/6.51  tff(c_535, plain, (![B_124, A_125]: (k1_relat_1(B_124)=A_125 | ~r1_tarski(A_125, k1_relat_1(B_124)) | ~v4_relat_1(B_124, A_125) | ~v1_relat_1(B_124))), inference(resolution, [status(thm)], [c_299, c_8])).
% 14.18/6.51  tff(c_555, plain, (![B_8, B_124]: (k1_relat_1(B_8)=k1_relat_1(B_124) | ~v4_relat_1(B_124, k1_relat_1(B_8)) | ~v1_relat_1(B_124) | ~v4_relat_1(B_8, k1_relat_1(B_124)) | ~v1_relat_1(B_8))), inference(resolution, [status(thm)], [c_18, c_535])).
% 14.18/6.51  tff(c_4825, plain, (k1_relat_1(k2_funct_1('#skF_5'))=k1_relat_1('#skF_4') | ~v1_relat_1(k2_funct_1('#skF_5')) | ~v4_relat_1('#skF_4', k1_relat_1(k2_funct_1('#skF_5'))) | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_4799, c_555])).
% 14.18/6.51  tff(c_4828, plain, (k1_relat_1(k2_funct_1('#skF_5'))=k1_relat_1('#skF_4') | ~v4_relat_1('#skF_4', k1_relat_1(k2_funct_1('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_282, c_4800, c_4825])).
% 14.18/6.51  tff(c_4846, plain, (~v4_relat_1('#skF_4', k1_relat_1(k2_funct_1('#skF_5')))), inference(splitLeft, [status(thm)], [c_4828])).
% 14.18/6.51  tff(c_4849, plain, (~v4_relat_1('#skF_4', k2_relat_1('#skF_5')) | ~v2_funct_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_52, c_4846])).
% 14.18/6.51  tff(c_4851, plain, (~v4_relat_1('#skF_4', k1_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_285, c_112, c_4790, c_3724, c_4849])).
% 14.18/6.51  tff(c_4854, plain, (~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_330, c_4851])).
% 14.18/6.51  tff(c_4858, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_282, c_4854])).
% 14.18/6.51  tff(c_4859, plain, (k1_relat_1(k2_funct_1('#skF_5'))=k1_relat_1('#skF_4')), inference(splitRight, [status(thm)], [c_4828])).
% 14.18/6.51  tff(c_5024, plain, (k1_relat_1(k2_funct_1('#skF_5'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_5019, c_4859])).
% 14.18/6.51  tff(c_5029, plain, (k2_relat_1('#skF_5')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_5019, c_3724])).
% 14.18/6.51  tff(c_368, plain, (v4_relat_1('#skF_5', '#skF_3')), inference(resolution, [status(thm)], [c_108, c_355])).
% 14.18/6.51  tff(c_5018, plain, (k5_relat_1('#skF_5', k2_funct_1('#skF_5'))=k6_partfun1('#skF_3')), inference(splitRight, [status(thm)], [c_4989])).
% 14.18/6.51  tff(c_5311, plain, (r1_tarski(k2_relat_1(k6_partfun1('#skF_3')), k2_relat_1(k2_funct_1('#skF_5'))) | ~v1_relat_1(k2_funct_1('#skF_5')) | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_5018, c_22])).
% 14.18/6.51  tff(c_5315, plain, (r1_tarski('#skF_3', k2_relat_1(k2_funct_1('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_285, c_4800, c_127, c_5311])).
% 14.18/6.51  tff(c_5321, plain, (r1_tarski('#skF_3', k1_relat_1('#skF_5')) | ~v2_funct_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_50, c_5315])).
% 14.18/6.51  tff(c_5324, plain, (r1_tarski('#skF_3', k1_relat_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_285, c_112, c_4790, c_5321])).
% 14.18/6.51  tff(c_5343, plain, (k1_relat_1('#skF_5')='#skF_3' | ~v4_relat_1('#skF_5', '#skF_3') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_5324, c_305])).
% 14.18/6.51  tff(c_5348, plain, (k1_relat_1('#skF_5')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_285, c_368, c_5343])).
% 14.18/6.51  tff(c_8832, plain, (![A_585, B_586]: (k2_funct_1(k2_funct_1(A_585))=B_586 | k5_relat_1(B_586, k2_funct_1(A_585))!=k6_partfun1(k1_relat_1(A_585)) | k2_relat_1(B_586)!=k1_relat_1(k2_funct_1(A_585)) | ~v2_funct_1(k2_funct_1(A_585)) | ~v1_funct_1(B_586) | ~v1_relat_1(B_586) | ~v1_funct_1(k2_funct_1(A_585)) | ~v1_relat_1(k2_funct_1(A_585)) | ~v2_funct_1(A_585) | ~v1_funct_1(A_585) | ~v1_relat_1(A_585))), inference(superposition, [status(thm), theory('equality')], [c_50, c_2171])).
% 14.18/6.51  tff(c_8840, plain, (k2_funct_1(k2_funct_1('#skF_5'))='#skF_5' | k6_partfun1(k1_relat_1('#skF_5'))!=k6_partfun1('#skF_3') | k1_relat_1(k2_funct_1('#skF_5'))!=k2_relat_1('#skF_5') | ~v2_funct_1(k2_funct_1('#skF_5')) | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5') | ~v1_funct_1(k2_funct_1('#skF_5')) | ~v1_relat_1(k2_funct_1('#skF_5')) | ~v2_funct_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_5018, c_8832])).
% 14.18/6.51  tff(c_8861, plain, (k2_funct_1(k2_funct_1('#skF_5'))='#skF_5' | ~v2_funct_1(k2_funct_1('#skF_5')) | ~v1_funct_1(k2_funct_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_285, c_112, c_4790, c_4800, c_285, c_112, c_5024, c_5029, c_5348, c_8840])).
% 14.18/6.51  tff(c_8871, plain, (~v1_funct_1(k2_funct_1('#skF_5'))), inference(splitLeft, [status(thm)], [c_8861])).
% 14.18/6.51  tff(c_8874, plain, (~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_32, c_8871])).
% 14.18/6.51  tff(c_8878, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_285, c_112, c_8874])).
% 14.18/6.51  tff(c_8880, plain, (v1_funct_1(k2_funct_1('#skF_5'))), inference(splitRight, [status(thm)], [c_8861])).
% 14.18/6.51  tff(c_44, plain, (![A_20]: (v2_funct_1(k2_funct_1(A_20)) | ~v2_funct_1(A_20) | ~v1_funct_1(A_20) | ~v1_relat_1(A_20))), inference(cnfTransformation, [status(thm)], [f_100])).
% 14.18/6.51  tff(c_8879, plain, (~v2_funct_1(k2_funct_1('#skF_5')) | k2_funct_1(k2_funct_1('#skF_5'))='#skF_5'), inference(splitRight, [status(thm)], [c_8861])).
% 14.18/6.51  tff(c_8935, plain, (~v2_funct_1(k2_funct_1('#skF_5'))), inference(splitLeft, [status(thm)], [c_8879])).
% 14.18/6.51  tff(c_8938, plain, (~v2_funct_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_44, c_8935])).
% 14.18/6.51  tff(c_8942, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_285, c_112, c_4790, c_8938])).
% 14.18/6.51  tff(c_8944, plain, (v2_funct_1(k2_funct_1('#skF_5'))), inference(splitRight, [status(thm)], [c_8879])).
% 14.18/6.51  tff(c_8943, plain, (k2_funct_1(k2_funct_1('#skF_5'))='#skF_5'), inference(splitRight, [status(thm)], [c_8879])).
% 14.18/6.51  tff(c_2189, plain, (![A_21, B_223]: (k2_funct_1(k2_funct_1(A_21))=B_223 | k5_relat_1(B_223, k2_funct_1(A_21))!=k6_partfun1(k1_relat_1(A_21)) | k2_relat_1(B_223)!=k1_relat_1(k2_funct_1(A_21)) | ~v2_funct_1(k2_funct_1(A_21)) | ~v1_funct_1(B_223) | ~v1_relat_1(B_223) | ~v1_funct_1(k2_funct_1(A_21)) | ~v1_relat_1(k2_funct_1(A_21)) | ~v2_funct_1(A_21) | ~v1_funct_1(A_21) | ~v1_relat_1(A_21))), inference(superposition, [status(thm), theory('equality')], [c_50, c_2171])).
% 14.18/6.51  tff(c_8947, plain, (![B_223]: (k2_funct_1(k2_funct_1(k2_funct_1('#skF_5')))=B_223 | k6_partfun1(k1_relat_1(k2_funct_1('#skF_5')))!=k5_relat_1(B_223, '#skF_5') | k2_relat_1(B_223)!=k1_relat_1(k2_funct_1(k2_funct_1('#skF_5'))) | ~v2_funct_1(k2_funct_1(k2_funct_1('#skF_5'))) | ~v1_funct_1(B_223) | ~v1_relat_1(B_223) | ~v1_funct_1(k2_funct_1(k2_funct_1('#skF_5'))) | ~v1_relat_1(k2_funct_1(k2_funct_1('#skF_5'))) | ~v2_funct_1(k2_funct_1('#skF_5')) | ~v1_funct_1(k2_funct_1('#skF_5')) | ~v1_relat_1(k2_funct_1('#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_8943, c_2189])).
% 14.18/6.51  tff(c_17976, plain, (![B_826]: (k2_funct_1('#skF_5')=B_826 | k5_relat_1(B_826, '#skF_5')!=k6_partfun1('#skF_2') | k2_relat_1(B_826)!='#skF_3' | ~v1_funct_1(B_826) | ~v1_relat_1(B_826))), inference(demodulation, [status(thm), theory('equality')], [c_4800, c_8880, c_8944, c_285, c_8943, c_112, c_8943, c_4790, c_8943, c_5348, c_8943, c_5024, c_8943, c_8947])).
% 14.18/6.51  tff(c_18138, plain, (k2_funct_1('#skF_5')='#skF_4' | k5_relat_1('#skF_4', '#skF_5')!=k6_partfun1('#skF_2') | k2_relat_1('#skF_4')!='#skF_3' | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_282, c_17976])).
% 14.18/6.51  tff(c_18310, plain, (k2_funct_1('#skF_5')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_118, c_482, c_5899, c_18138])).
% 14.18/6.51  tff(c_18325, plain, (k2_funct_1('#skF_4')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_18310, c_8943])).
% 14.18/6.51  tff(c_18342, plain, $false, inference(negUnitSimplification, [status(thm)], [c_96, c_18325])).
% 14.18/6.51  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 14.18/6.51  
% 14.18/6.51  Inference rules
% 14.18/6.51  ----------------------
% 14.18/6.51  #Ref     : 0
% 14.18/6.51  #Sup     : 3762
% 14.18/6.51  #Fact    : 0
% 14.18/6.51  #Define  : 0
% 14.18/6.51  #Split   : 40
% 14.18/6.51  #Chain   : 0
% 14.18/6.51  #Close   : 0
% 14.18/6.51  
% 14.18/6.51  Ordering : KBO
% 14.18/6.51  
% 14.18/6.51  Simplification rules
% 14.18/6.51  ----------------------
% 14.18/6.51  #Subsume      : 226
% 14.18/6.51  #Demod        : 9755
% 14.18/6.51  #Tautology    : 1538
% 14.18/6.51  #SimpNegUnit  : 100
% 14.18/6.51  #BackRed      : 143
% 14.18/6.51  
% 14.18/6.51  #Partial instantiations: 0
% 14.18/6.51  #Strategies tried      : 1
% 14.18/6.51  
% 14.18/6.51  Timing (in seconds)
% 14.18/6.51  ----------------------
% 14.18/6.51  Preprocessing        : 0.42
% 14.18/6.51  Parsing              : 0.23
% 14.18/6.51  CNF conversion       : 0.03
% 14.18/6.51  Main loop            : 5.24
% 14.18/6.51  Inferencing          : 1.10
% 14.18/6.51  Reduction            : 2.99
% 14.18/6.51  Demodulation         : 2.60
% 14.18/6.51  BG Simplification    : 0.10
% 14.18/6.51  Subsumption          : 0.85
% 14.18/6.51  Abstraction          : 0.13
% 14.18/6.51  MUC search           : 0.00
% 14.18/6.51  Cooper               : 0.00
% 14.18/6.51  Total                : 5.74
% 14.18/6.51  Index Insertion      : 0.00
% 14.18/6.51  Index Deletion       : 0.00
% 14.18/6.51  Index Matching       : 0.00
% 14.18/6.51  BG Taut test         : 0.00
%------------------------------------------------------------------------------
