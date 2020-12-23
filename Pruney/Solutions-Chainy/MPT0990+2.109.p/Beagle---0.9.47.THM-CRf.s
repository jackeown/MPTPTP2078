%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:13:12 EST 2020

% Result     : Theorem 7.21s
% Output     : CNFRefutation 7.55s
% Verified   : 
% Statistics : Number of formulae       :  210 (2587 expanded)
%              Number of leaves         :   57 ( 922 expanded)
%              Depth                    :   24
%              Number of atoms          :  439 (7979 expanded)
%              Number of equality atoms :  132 (2486 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k9_relat_1 > k7_relat_1 > k5_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

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

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

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

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

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

tff(f_241,negated_conjecture,(
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

tff(f_46,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_38,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_158,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_198,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_99,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v2_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_funct_1)).

tff(f_162,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_182,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( v1_funct_1(k1_partfun1(A,B,C,D,E,F))
        & m1_subset_1(k1_partfun1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).

tff(f_186,axiom,(
    ! [A] :
      ( v1_partfun1(k6_partfun1(A),A)
      & m1_subset_1(k6_partfun1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).

tff(f_170,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_196,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_124,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_funct_1)).

tff(f_63,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_77,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_57,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k1_relat_1(k5_relat_1(A,B)) = k10_relat_1(A,k1_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t182_relat_1)).

tff(f_107,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r1_tarski(A,k2_relat_1(B))
       => k9_relat_1(B,k10_relat_1(B,A)) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t147_funct_1)).

tff(f_215,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_funct_2)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_87,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k2_relat_1(B),A)
       => k5_relat_1(B,k6_relat_1(A)) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_relat_1)).

tff(f_81,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k5_relat_1(k6_relat_1(k1_relat_1(A)),A) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t78_relat_1)).

tff(f_73,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ! [C] :
              ( v1_relat_1(C)
             => k5_relat_1(k5_relat_1(A,B),C) = k5_relat_1(A,k5_relat_1(B,C)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_relat_1)).

tff(f_134,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k2_relat_1(A) = k1_relat_1(k2_funct_1(A))
          & k1_relat_1(A) = k2_relat_1(k2_funct_1(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).

tff(f_95,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).

tff(f_144,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k5_relat_1(A,k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))
          & k5_relat_1(k2_funct_1(A),A) = k6_relat_1(k2_relat_1(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_1)).

tff(c_80,plain,(
    k2_funct_1('#skF_3') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_241])).

tff(c_14,plain,(
    ! [A_8,B_9] : v1_relat_1(k2_zfmisc_1(A_8,B_9)) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_92,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_241])).

tff(c_174,plain,(
    ! [B_82,A_83] :
      ( v1_relat_1(B_82)
      | ~ m1_subset_1(B_82,k1_zfmisc_1(A_83))
      | ~ v1_relat_1(A_83) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_180,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_1')) ),
    inference(resolution,[status(thm)],[c_92,c_174])).

tff(c_189,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_180])).

tff(c_249,plain,(
    ! [C_96,A_97,B_98] :
      ( v4_relat_1(C_96,A_97)
      | ~ m1_subset_1(C_96,k1_zfmisc_1(k2_zfmisc_1(A_97,B_98))) ) ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_261,plain,(
    v4_relat_1('#skF_4','#skF_2') ),
    inference(resolution,[status(thm)],[c_92,c_249])).

tff(c_12,plain,(
    ! [B_7,A_6] :
      ( r1_tarski(k1_relat_1(B_7),A_6)
      | ~ v4_relat_1(B_7,A_6)
      | ~ v1_relat_1(B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_96,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_241])).

tff(c_98,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_241])).

tff(c_183,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_98,c_174])).

tff(c_192,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_183])).

tff(c_102,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_241])).

tff(c_76,plain,(
    ! [A_61] : k6_relat_1(A_61) = k6_partfun1(A_61) ),
    inference(cnfTransformation,[status(thm)],[f_198])).

tff(c_38,plain,(
    ! [A_29] : v2_funct_1(k6_relat_1(A_29)) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_105,plain,(
    ! [A_29] : v2_funct_1(k6_partfun1(A_29)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_38])).

tff(c_90,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_241])).

tff(c_648,plain,(
    ! [A_129,B_130,C_131] :
      ( k2_relset_1(A_129,B_130,C_131) = k2_relat_1(C_131)
      | ~ m1_subset_1(C_131,k1_zfmisc_1(k2_zfmisc_1(A_129,B_130))) ) ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_657,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_98,c_648])).

tff(c_662,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_657])).

tff(c_2700,plain,(
    ! [F_203,A_206,D_204,B_205,C_207,E_208] :
      ( m1_subset_1(k1_partfun1(A_206,B_205,C_207,D_204,E_208,F_203),k1_zfmisc_1(k2_zfmisc_1(A_206,D_204)))
      | ~ m1_subset_1(F_203,k1_zfmisc_1(k2_zfmisc_1(C_207,D_204)))
      | ~ v1_funct_1(F_203)
      | ~ m1_subset_1(E_208,k1_zfmisc_1(k2_zfmisc_1(A_206,B_205)))
      | ~ v1_funct_1(E_208) ) ),
    inference(cnfTransformation,[status(thm)],[f_182])).

tff(c_72,plain,(
    ! [A_54] : m1_subset_1(k6_partfun1(A_54),k1_zfmisc_1(k2_zfmisc_1(A_54,A_54))) ),
    inference(cnfTransformation,[status(thm)],[f_186])).

tff(c_88,plain,(
    r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k6_partfun1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_241])).

tff(c_2167,plain,(
    ! [D_176,C_177,A_178,B_179] :
      ( D_176 = C_177
      | ~ r2_relset_1(A_178,B_179,C_177,D_176)
      | ~ m1_subset_1(D_176,k1_zfmisc_1(k2_zfmisc_1(A_178,B_179)))
      | ~ m1_subset_1(C_177,k1_zfmisc_1(k2_zfmisc_1(A_178,B_179))) ) ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_2175,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_88,c_2167])).

tff(c_2190,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_2175])).

tff(c_2333,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_2190])).

tff(c_2703,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_2700,c_2333])).

tff(c_2731,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_98,c_96,c_92,c_2703])).

tff(c_2732,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_2190])).

tff(c_3014,plain,(
    ! [D_221,F_224,B_220,C_223,A_222,E_225] :
      ( k1_partfun1(A_222,B_220,C_223,D_221,E_225,F_224) = k5_relat_1(E_225,F_224)
      | ~ m1_subset_1(F_224,k1_zfmisc_1(k2_zfmisc_1(C_223,D_221)))
      | ~ v1_funct_1(F_224)
      | ~ m1_subset_1(E_225,k1_zfmisc_1(k2_zfmisc_1(A_222,B_220)))
      | ~ v1_funct_1(E_225) ) ),
    inference(cnfTransformation,[status(thm)],[f_196])).

tff(c_3018,plain,(
    ! [A_222,B_220,E_225] :
      ( k1_partfun1(A_222,B_220,'#skF_2','#skF_1',E_225,'#skF_4') = k5_relat_1(E_225,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_225,k1_zfmisc_1(k2_zfmisc_1(A_222,B_220)))
      | ~ v1_funct_1(E_225) ) ),
    inference(resolution,[status(thm)],[c_92,c_3014])).

tff(c_3890,plain,(
    ! [A_253,B_254,E_255] :
      ( k1_partfun1(A_253,B_254,'#skF_2','#skF_1',E_255,'#skF_4') = k5_relat_1(E_255,'#skF_4')
      | ~ m1_subset_1(E_255,k1_zfmisc_1(k2_zfmisc_1(A_253,B_254)))
      | ~ v1_funct_1(E_255) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_3018])).

tff(c_3905,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_98,c_3890])).

tff(c_3916,plain,(
    k5_relat_1('#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_2732,c_3905])).

tff(c_42,plain,(
    ! [A_32,B_34] :
      ( v2_funct_1(A_32)
      | k2_relat_1(B_34) != k1_relat_1(A_32)
      | ~ v2_funct_1(k5_relat_1(B_34,A_32))
      | ~ v1_funct_1(B_34)
      | ~ v1_relat_1(B_34)
      | ~ v1_funct_1(A_32)
      | ~ v1_relat_1(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_3929,plain,
    ( v2_funct_1('#skF_4')
    | k2_relat_1('#skF_3') != k1_relat_1('#skF_4')
    | ~ v2_funct_1(k6_partfun1('#skF_1'))
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_3916,c_42])).

tff(c_3945,plain,
    ( v2_funct_1('#skF_4')
    | k1_relat_1('#skF_4') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_189,c_96,c_192,c_102,c_105,c_662,c_3929])).

tff(c_3951,plain,(
    k1_relat_1('#skF_4') != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_3945])).

tff(c_262,plain,(
    v4_relat_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_98,c_249])).

tff(c_272,plain,(
    ! [B_101,A_102] :
      ( k7_relat_1(B_101,A_102) = B_101
      | ~ v4_relat_1(B_101,A_102)
      | ~ v1_relat_1(B_101) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_275,plain,
    ( k7_relat_1('#skF_3','#skF_1') = '#skF_3'
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_262,c_272])).

tff(c_290,plain,(
    k7_relat_1('#skF_3','#skF_1') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_192,c_275])).

tff(c_16,plain,(
    ! [B_11,A_10] :
      ( k2_relat_1(k7_relat_1(B_11,A_10)) = k9_relat_1(B_11,A_10)
      | ~ v1_relat_1(B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_304,plain,
    ( k9_relat_1('#skF_3','#skF_1') = k2_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_290,c_16])).

tff(c_308,plain,(
    k9_relat_1('#skF_3','#skF_1') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_192,c_304])).

tff(c_663,plain,(
    k9_relat_1('#skF_3','#skF_1') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_662,c_308])).

tff(c_24,plain,(
    ! [A_24] : k1_relat_1(k6_relat_1(A_24)) = A_24 ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_110,plain,(
    ! [A_24] : k1_relat_1(k6_partfun1(A_24)) = A_24 ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_24])).

tff(c_18,plain,(
    ! [A_12,B_14] :
      ( k10_relat_1(A_12,k1_relat_1(B_14)) = k1_relat_1(k5_relat_1(A_12,B_14))
      | ~ v1_relat_1(B_14)
      | ~ v1_relat_1(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_878,plain,(
    ! [B_141,A_142] :
      ( k9_relat_1(B_141,k10_relat_1(B_141,A_142)) = A_142
      | ~ r1_tarski(A_142,k2_relat_1(B_141))
      | ~ v1_funct_1(B_141)
      | ~ v1_relat_1(B_141) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_880,plain,(
    ! [A_142] :
      ( k9_relat_1('#skF_3',k10_relat_1('#skF_3',A_142)) = A_142
      | ~ r1_tarski(A_142,'#skF_2')
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_662,c_878])).

tff(c_899,plain,(
    ! [A_143] :
      ( k9_relat_1('#skF_3',k10_relat_1('#skF_3',A_143)) = A_143
      | ~ r1_tarski(A_143,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_192,c_102,c_880])).

tff(c_912,plain,(
    ! [B_14] :
      ( k9_relat_1('#skF_3',k1_relat_1(k5_relat_1('#skF_3',B_14))) = k1_relat_1(B_14)
      | ~ r1_tarski(k1_relat_1(B_14),'#skF_2')
      | ~ v1_relat_1(B_14)
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_899])).

tff(c_918,plain,(
    ! [B_14] :
      ( k9_relat_1('#skF_3',k1_relat_1(k5_relat_1('#skF_3',B_14))) = k1_relat_1(B_14)
      | ~ r1_tarski(k1_relat_1(B_14),'#skF_2')
      | ~ v1_relat_1(B_14) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_192,c_912])).

tff(c_3935,plain,
    ( k9_relat_1('#skF_3',k1_relat_1(k6_partfun1('#skF_1'))) = k1_relat_1('#skF_4')
    | ~ r1_tarski(k1_relat_1('#skF_4'),'#skF_2')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_3916,c_918])).

tff(c_3949,plain,
    ( k1_relat_1('#skF_4') = '#skF_2'
    | ~ r1_tarski(k1_relat_1('#skF_4'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_189,c_663,c_110,c_3935])).

tff(c_3952,plain,(
    ~ r1_tarski(k1_relat_1('#skF_4'),'#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_3951,c_3949])).

tff(c_3955,plain,
    ( ~ v4_relat_1('#skF_4','#skF_2')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_12,c_3952])).

tff(c_3959,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_189,c_261,c_3955])).

tff(c_3961,plain,(
    k1_relat_1('#skF_4') = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_3945])).

tff(c_36,plain,(
    ! [A_29] : v1_relat_1(k6_relat_1(A_29)) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_106,plain,(
    ! [A_29] : v1_relat_1(k6_partfun1(A_29)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_36])).

tff(c_94,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_241])).

tff(c_100,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_241])).

tff(c_572,plain,(
    ! [A_121,B_122,D_123] :
      ( r2_relset_1(A_121,B_122,D_123,D_123)
      | ~ m1_subset_1(D_123,k1_zfmisc_1(k2_zfmisc_1(A_121,B_122))) ) ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_579,plain,(
    ! [A_54] : r2_relset_1(A_54,A_54,k6_partfun1(A_54),k6_partfun1(A_54)) ),
    inference(resolution,[status(thm)],[c_72,c_572])).

tff(c_660,plain,(
    k2_relset_1('#skF_2','#skF_1','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_92,c_648])).

tff(c_3441,plain,(
    ! [A_246,B_247,C_248,D_249] :
      ( k2_relset_1(A_246,B_247,C_248) = B_247
      | ~ r2_relset_1(B_247,B_247,k1_partfun1(B_247,A_246,A_246,B_247,D_249,C_248),k6_partfun1(B_247))
      | ~ m1_subset_1(D_249,k1_zfmisc_1(k2_zfmisc_1(B_247,A_246)))
      | ~ v1_funct_2(D_249,B_247,A_246)
      | ~ v1_funct_1(D_249)
      | ~ m1_subset_1(C_248,k1_zfmisc_1(k2_zfmisc_1(A_246,B_247)))
      | ~ v1_funct_2(C_248,A_246,B_247)
      | ~ v1_funct_1(C_248) ) ),
    inference(cnfTransformation,[status(thm)],[f_215])).

tff(c_3447,plain,
    ( k2_relset_1('#skF_2','#skF_1','#skF_4') = '#skF_1'
    | ~ r2_relset_1('#skF_1','#skF_1',k6_partfun1('#skF_1'),k6_partfun1('#skF_1'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_2732,c_3441])).

tff(c_3451,plain,(
    k2_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_94,c_92,c_102,c_100,c_98,c_579,c_660,c_3447])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_30,plain,(
    ! [B_27,A_26] :
      ( k5_relat_1(B_27,k6_relat_1(A_26)) = B_27
      | ~ r1_tarski(k2_relat_1(B_27),A_26)
      | ~ v1_relat_1(B_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_493,plain,(
    ! [B_116,A_117] :
      ( k5_relat_1(B_116,k6_partfun1(A_117)) = B_116
      | ~ r1_tarski(k2_relat_1(B_116),A_117)
      | ~ v1_relat_1(B_116) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_30])).

tff(c_506,plain,(
    ! [B_116] :
      ( k5_relat_1(B_116,k6_partfun1(k2_relat_1(B_116))) = B_116
      | ~ v1_relat_1(B_116) ) ),
    inference(resolution,[status(thm)],[c_6,c_493])).

tff(c_3465,plain,
    ( k5_relat_1('#skF_4',k6_partfun1('#skF_1')) = '#skF_4'
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_3451,c_506])).

tff(c_3478,plain,(
    k5_relat_1('#skF_4',k6_partfun1('#skF_1')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_189,c_3465])).

tff(c_28,plain,(
    ! [A_25] :
      ( k5_relat_1(k6_relat_1(k1_relat_1(A_25)),A_25) = A_25
      | ~ v1_relat_1(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_108,plain,(
    ! [A_25] :
      ( k5_relat_1(k6_partfun1(k1_relat_1(A_25)),A_25) = A_25
      | ~ v1_relat_1(A_25) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_28])).

tff(c_1296,plain,(
    ! [A_155,B_156,C_157] :
      ( k5_relat_1(k5_relat_1(A_155,B_156),C_157) = k5_relat_1(A_155,k5_relat_1(B_156,C_157))
      | ~ v1_relat_1(C_157)
      | ~ v1_relat_1(B_156)
      | ~ v1_relat_1(A_155) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_1352,plain,(
    ! [A_25,C_157] :
      ( k5_relat_1(k6_partfun1(k1_relat_1(A_25)),k5_relat_1(A_25,C_157)) = k5_relat_1(A_25,C_157)
      | ~ v1_relat_1(C_157)
      | ~ v1_relat_1(A_25)
      | ~ v1_relat_1(k6_partfun1(k1_relat_1(A_25)))
      | ~ v1_relat_1(A_25) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_108,c_1296])).

tff(c_3549,plain,(
    ! [A_250,C_251] :
      ( k5_relat_1(k6_partfun1(k1_relat_1(A_250)),k5_relat_1(A_250,C_251)) = k5_relat_1(A_250,C_251)
      | ~ v1_relat_1(C_251)
      | ~ v1_relat_1(A_250) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_106,c_1352])).

tff(c_3582,plain,
    ( k5_relat_1(k6_partfun1(k1_relat_1('#skF_4')),'#skF_4') = k5_relat_1('#skF_4',k6_partfun1('#skF_1'))
    | ~ v1_relat_1(k6_partfun1('#skF_1'))
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_3478,c_3549])).

tff(c_3676,plain,(
    k5_relat_1(k6_partfun1(k1_relat_1('#skF_4')),'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_189,c_106,c_3478,c_3582])).

tff(c_4011,plain,(
    k5_relat_1(k6_partfun1('#skF_2'),'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3961,c_3676])).

tff(c_1372,plain,(
    ! [A_25,C_157] :
      ( k5_relat_1(k6_partfun1(k1_relat_1(A_25)),k5_relat_1(A_25,C_157)) = k5_relat_1(A_25,C_157)
      | ~ v1_relat_1(C_157)
      | ~ v1_relat_1(A_25) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_106,c_1352])).

tff(c_3920,plain,
    ( k5_relat_1(k6_partfun1(k1_relat_1('#skF_3')),k6_partfun1('#skF_1')) = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_relat_1('#skF_4')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_3916,c_1372])).

tff(c_3939,plain,(
    k5_relat_1(k6_partfun1(k1_relat_1('#skF_3')),k6_partfun1('#skF_1')) = k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_192,c_189,c_3916,c_3920])).

tff(c_26,plain,(
    ! [A_24] : k2_relat_1(k6_relat_1(A_24)) = A_24 ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_109,plain,(
    ! [A_24] : k2_relat_1(k6_partfun1(A_24)) = A_24 ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_26])).

tff(c_499,plain,(
    ! [A_24,A_117] :
      ( k5_relat_1(k6_partfun1(A_24),k6_partfun1(A_117)) = k6_partfun1(A_24)
      | ~ r1_tarski(A_24,A_117)
      | ~ v1_relat_1(k6_partfun1(A_24)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_109,c_493])).

tff(c_505,plain,(
    ! [A_24,A_117] :
      ( k5_relat_1(k6_partfun1(A_24),k6_partfun1(A_117)) = k6_partfun1(A_24)
      | ~ r1_tarski(A_24,A_117) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_106,c_499])).

tff(c_631,plain,(
    ! [A_127,B_128] :
      ( k10_relat_1(A_127,k1_relat_1(B_128)) = k1_relat_1(k5_relat_1(A_127,B_128))
      | ~ v1_relat_1(B_128)
      | ~ v1_relat_1(A_127) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_643,plain,(
    ! [A_127,A_24] :
      ( k1_relat_1(k5_relat_1(A_127,k6_partfun1(A_24))) = k10_relat_1(A_127,A_24)
      | ~ v1_relat_1(k6_partfun1(A_24))
      | ~ v1_relat_1(A_127) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_110,c_631])).

tff(c_734,plain,(
    ! [A_134,A_135] :
      ( k1_relat_1(k5_relat_1(A_134,k6_partfun1(A_135))) = k10_relat_1(A_134,A_135)
      | ~ v1_relat_1(A_134) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_106,c_643])).

tff(c_770,plain,(
    ! [A_24,A_117] :
      ( k10_relat_1(k6_partfun1(A_24),A_117) = k1_relat_1(k6_partfun1(A_24))
      | ~ v1_relat_1(k6_partfun1(A_24))
      | ~ r1_tarski(A_24,A_117) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_505,c_734])).

tff(c_837,plain,(
    ! [A_138,A_139] :
      ( k10_relat_1(k6_partfun1(A_138),A_139) = A_138
      | ~ r1_tarski(A_138,A_139) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_106,c_110,c_770])).

tff(c_858,plain,(
    ! [A_138,B_14] :
      ( k1_relat_1(k5_relat_1(k6_partfun1(A_138),B_14)) = A_138
      | ~ r1_tarski(A_138,k1_relat_1(B_14))
      | ~ v1_relat_1(B_14)
      | ~ v1_relat_1(k6_partfun1(A_138)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_837])).

tff(c_870,plain,(
    ! [A_138,B_14] :
      ( k1_relat_1(k5_relat_1(k6_partfun1(A_138),B_14)) = A_138
      | ~ r1_tarski(A_138,k1_relat_1(B_14))
      | ~ v1_relat_1(B_14) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_106,c_858])).

tff(c_4274,plain,
    ( k1_relat_1(k6_partfun1('#skF_1')) = k1_relat_1('#skF_3')
    | ~ r1_tarski(k1_relat_1('#skF_3'),k1_relat_1(k6_partfun1('#skF_1')))
    | ~ v1_relat_1(k6_partfun1('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_3939,c_870])).

tff(c_4300,plain,
    ( k1_relat_1('#skF_3') = '#skF_1'
    | ~ r1_tarski(k1_relat_1('#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_106,c_110,c_110,c_4274])).

tff(c_4343,plain,(
    ~ r1_tarski(k1_relat_1('#skF_3'),'#skF_1') ),
    inference(splitLeft,[status(thm)],[c_4300])).

tff(c_4346,plain,
    ( ~ v4_relat_1('#skF_3','#skF_1')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_12,c_4343])).

tff(c_4350,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_192,c_262,c_4346])).

tff(c_4351,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_4300])).

tff(c_86,plain,(
    v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_241])).

tff(c_46,plain,(
    ! [A_35] :
      ( k2_relat_1(k2_funct_1(A_35)) = k1_relat_1(A_35)
      | ~ v2_funct_1(A_35)
      | ~ v1_funct_1(A_35)
      | ~ v1_relat_1(A_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_34,plain,(
    ! [A_28] :
      ( v1_relat_1(k2_funct_1(A_28))
      | ~ v1_funct_1(A_28)
      | ~ v1_relat_1(A_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_667,plain,
    ( k5_relat_1('#skF_3',k6_partfun1('#skF_2')) = '#skF_3'
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_662,c_506])).

tff(c_674,plain,(
    k5_relat_1('#skF_3',k6_partfun1('#skF_2')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_192,c_667])).

tff(c_767,plain,
    ( k10_relat_1('#skF_3','#skF_2') = k1_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_674,c_734])).

tff(c_786,plain,(
    k10_relat_1('#skF_3','#skF_2') = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_192,c_767])).

tff(c_908,plain,
    ( k9_relat_1('#skF_3',k1_relat_1('#skF_3')) = '#skF_2'
    | ~ r1_tarski('#skF_2','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_786,c_899])).

tff(c_916,plain,(
    k9_relat_1('#skF_3',k1_relat_1('#skF_3')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_908])).

tff(c_52,plain,(
    ! [A_36] :
      ( k5_relat_1(A_36,k2_funct_1(A_36)) = k6_relat_1(k1_relat_1(A_36))
      | ~ v2_funct_1(A_36)
      | ~ v1_funct_1(A_36)
      | ~ v1_relat_1(A_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_103,plain,(
    ! [A_36] :
      ( k5_relat_1(A_36,k2_funct_1(A_36)) = k6_partfun1(k1_relat_1(A_36))
      | ~ v2_funct_1(A_36)
      | ~ v1_funct_1(A_36)
      | ~ v1_relat_1(A_36) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_52])).

tff(c_1160,plain,(
    ! [B_152] :
      ( k9_relat_1('#skF_3',k1_relat_1(k5_relat_1('#skF_3',B_152))) = k1_relat_1(B_152)
      | ~ r1_tarski(k1_relat_1(B_152),'#skF_2')
      | ~ v1_relat_1(B_152) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_192,c_912])).

tff(c_1170,plain,
    ( k9_relat_1('#skF_3',k1_relat_1(k6_partfun1(k1_relat_1('#skF_3')))) = k1_relat_1(k2_funct_1('#skF_3'))
    | ~ r1_tarski(k1_relat_1(k2_funct_1('#skF_3')),'#skF_2')
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_103,c_1160])).

tff(c_1188,plain,
    ( k1_relat_1(k2_funct_1('#skF_3')) = '#skF_2'
    | ~ r1_tarski(k1_relat_1(k2_funct_1('#skF_3')),'#skF_2')
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_192,c_102,c_86,c_916,c_110,c_1170])).

tff(c_1286,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_1188])).

tff(c_1289,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_34,c_1286])).

tff(c_1293,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_192,c_102,c_1289])).

tff(c_1295,plain,(
    v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_1188])).

tff(c_48,plain,(
    ! [A_35] :
      ( k1_relat_1(k2_funct_1(A_35)) = k2_relat_1(A_35)
      | ~ v2_funct_1(A_35)
      | ~ v1_funct_1(A_35)
      | ~ v1_relat_1(A_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_1294,plain,
    ( ~ r1_tarski(k1_relat_1(k2_funct_1('#skF_3')),'#skF_2')
    | k1_relat_1(k2_funct_1('#skF_3')) = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_1188])).

tff(c_1373,plain,(
    ~ r1_tarski(k1_relat_1(k2_funct_1('#skF_3')),'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_1294])).

tff(c_1376,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_3'),'#skF_2')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_1373])).

tff(c_1382,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_192,c_102,c_86,c_6,c_662,c_1376])).

tff(c_1383,plain,(
    k1_relat_1(k2_funct_1('#skF_3')) = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_1294])).

tff(c_1415,plain,
    ( k5_relat_1(k6_partfun1('#skF_2'),k2_funct_1('#skF_3')) = k2_funct_1('#skF_3')
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1383,c_108])).

tff(c_1440,plain,(
    k5_relat_1(k6_partfun1('#skF_2'),k2_funct_1('#skF_3')) = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1295,c_1415])).

tff(c_22,plain,(
    ! [A_17,B_21,C_23] :
      ( k5_relat_1(k5_relat_1(A_17,B_21),C_23) = k5_relat_1(A_17,k5_relat_1(B_21,C_23))
      | ~ v1_relat_1(C_23)
      | ~ v1_relat_1(B_21)
      | ~ v1_relat_1(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_1613,plain,(
    ! [C_23] :
      ( k5_relat_1(k6_partfun1('#skF_2'),k5_relat_1(k2_funct_1('#skF_3'),C_23)) = k5_relat_1(k2_funct_1('#skF_3'),C_23)
      | ~ v1_relat_1(C_23)
      | ~ v1_relat_1(k2_funct_1('#skF_3'))
      | ~ v1_relat_1(k6_partfun1('#skF_2')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1440,c_22])).

tff(c_2191,plain,(
    ! [C_180] :
      ( k5_relat_1(k6_partfun1('#skF_2'),k5_relat_1(k2_funct_1('#skF_3'),C_180)) = k5_relat_1(k2_funct_1('#skF_3'),C_180)
      | ~ v1_relat_1(C_180) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_106,c_1295,c_1613])).

tff(c_2233,plain,
    ( k5_relat_1(k2_funct_1('#skF_3'),k6_partfun1(k2_relat_1(k2_funct_1('#skF_3')))) = k5_relat_1(k6_partfun1('#skF_2'),k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k6_partfun1(k2_relat_1(k2_funct_1('#skF_3'))))
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_506,c_2191])).

tff(c_2252,plain,(
    k5_relat_1(k2_funct_1('#skF_3'),k6_partfun1(k2_relat_1(k2_funct_1('#skF_3')))) = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1295,c_106,c_1440,c_2233])).

tff(c_2309,plain,
    ( k5_relat_1(k2_funct_1('#skF_3'),k6_partfun1(k1_relat_1('#skF_3'))) = k2_funct_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_2252])).

tff(c_2329,plain,(
    k5_relat_1(k2_funct_1('#skF_3'),k6_partfun1(k1_relat_1('#skF_3'))) = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_192,c_102,c_86,c_2309])).

tff(c_4363,plain,(
    k5_relat_1(k2_funct_1('#skF_3'),k6_partfun1('#skF_1')) = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4351,c_2329])).

tff(c_151,plain,(
    ! [A_80] :
      ( k5_relat_1(k6_partfun1(k1_relat_1(A_80)),A_80) = A_80
      | ~ v1_relat_1(A_80) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_28])).

tff(c_160,plain,(
    ! [A_24] :
      ( k5_relat_1(k6_partfun1(A_24),k6_partfun1(A_24)) = k6_partfun1(A_24)
      | ~ v1_relat_1(k6_partfun1(A_24)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_110,c_151])).

tff(c_164,plain,(
    ! [A_24] : k5_relat_1(k6_partfun1(A_24),k6_partfun1(A_24)) = k6_partfun1(A_24) ),
    inference(demodulation,[status(thm),theory(equality)],[c_106,c_160])).

tff(c_50,plain,(
    ! [A_36] :
      ( k5_relat_1(k2_funct_1(A_36),A_36) = k6_relat_1(k2_relat_1(A_36))
      | ~ v2_funct_1(A_36)
      | ~ v1_funct_1(A_36)
      | ~ v1_relat_1(A_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_104,plain,(
    ! [A_36] :
      ( k5_relat_1(k2_funct_1(A_36),A_36) = k6_partfun1(k2_relat_1(A_36))
      | ~ v2_funct_1(A_36)
      | ~ v1_funct_1(A_36)
      | ~ v1_relat_1(A_36) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_50])).

tff(c_2229,plain,
    ( k5_relat_1(k6_partfun1('#skF_2'),k6_partfun1(k2_relat_1('#skF_3'))) = k5_relat_1(k2_funct_1('#skF_3'),'#skF_3')
    | ~ v1_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_104,c_2191])).

tff(c_2250,plain,(
    k5_relat_1(k2_funct_1('#skF_3'),'#skF_3') = k6_partfun1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_192,c_102,c_86,c_192,c_164,c_662,c_2229])).

tff(c_2265,plain,(
    ! [C_23] :
      ( k5_relat_1(k2_funct_1('#skF_3'),k5_relat_1('#skF_3',C_23)) = k5_relat_1(k6_partfun1('#skF_2'),C_23)
      | ~ v1_relat_1(C_23)
      | ~ v1_relat_1('#skF_3')
      | ~ v1_relat_1(k2_funct_1('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2250,c_22])).

tff(c_2281,plain,(
    ! [C_23] :
      ( k5_relat_1(k2_funct_1('#skF_3'),k5_relat_1('#skF_3',C_23)) = k5_relat_1(k6_partfun1('#skF_2'),C_23)
      | ~ v1_relat_1(C_23) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1295,c_192,c_2265])).

tff(c_3923,plain,
    ( k5_relat_1(k2_funct_1('#skF_3'),k6_partfun1('#skF_1')) = k5_relat_1(k6_partfun1('#skF_2'),'#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_3916,c_2281])).

tff(c_3941,plain,(
    k5_relat_1(k2_funct_1('#skF_3'),k6_partfun1('#skF_1')) = k5_relat_1(k6_partfun1('#skF_2'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_189,c_3923])).

tff(c_5934,plain,(
    k2_funct_1('#skF_3') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4011,c_4363,c_3941])).

tff(c_5935,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_5934])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n001.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:30:00 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.21/2.43  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.21/2.45  
% 7.21/2.45  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.21/2.46  %$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k9_relat_1 > k7_relat_1 > k5_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 7.21/2.46  
% 7.21/2.46  %Foreground sorts:
% 7.21/2.46  
% 7.21/2.46  
% 7.21/2.46  %Background operators:
% 7.21/2.46  
% 7.21/2.46  
% 7.21/2.46  %Foreground operators:
% 7.21/2.46  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 7.21/2.46  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 7.21/2.46  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 7.21/2.46  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 7.21/2.46  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.21/2.46  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 7.21/2.46  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 7.21/2.46  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 7.21/2.46  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 7.21/2.46  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.21/2.46  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 7.21/2.46  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 7.21/2.46  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 7.21/2.46  tff('#skF_2', type, '#skF_2': $i).
% 7.21/2.46  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 7.21/2.46  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 7.21/2.46  tff('#skF_3', type, '#skF_3': $i).
% 7.21/2.46  tff('#skF_1', type, '#skF_1': $i).
% 7.21/2.46  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 7.21/2.46  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 7.21/2.46  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 7.21/2.46  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.21/2.46  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 7.21/2.46  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 7.21/2.46  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 7.21/2.46  tff('#skF_4', type, '#skF_4': $i).
% 7.21/2.46  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 7.21/2.46  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.21/2.46  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 7.21/2.46  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 7.21/2.46  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 7.21/2.46  
% 7.55/2.48  tff(f_241, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => ((((k2_relset_1(A, B, C) = B) & r2_relset_1(A, A, k1_partfun1(A, B, B, A, C, D), k6_partfun1(A))) & v2_funct_1(C)) => (((A = k1_xboole_0) | (B = k1_xboole_0)) | (D = k2_funct_1(C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_funct_2)).
% 7.55/2.48  tff(f_46, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 7.55/2.48  tff(f_38, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 7.55/2.48  tff(f_158, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 7.55/2.48  tff(f_44, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d18_relat_1)).
% 7.55/2.48  tff(f_198, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 7.55/2.48  tff(f_99, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v2_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc4_funct_1)).
% 7.55/2.48  tff(f_162, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 7.55/2.48  tff(f_182, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (v1_funct_1(k1_partfun1(A, B, C, D, E, F)) & m1_subset_1(k1_partfun1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 7.55/2.48  tff(f_186, axiom, (![A]: (v1_partfun1(k6_partfun1(A), A) & m1_subset_1(k6_partfun1(A), k1_zfmisc_1(k2_zfmisc_1(A, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_partfun1)).
% 7.55/2.48  tff(f_170, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 7.55/2.48  tff(f_196, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 7.55/2.48  tff(f_124, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((v2_funct_1(k5_relat_1(B, A)) & (k2_relat_1(B) = k1_relat_1(A))) => (v2_funct_1(B) & v2_funct_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_funct_1)).
% 7.55/2.48  tff(f_63, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t209_relat_1)).
% 7.55/2.48  tff(f_50, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_relat_1)).
% 7.55/2.48  tff(f_77, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 7.55/2.48  tff(f_57, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k1_relat_1(k5_relat_1(A, B)) = k10_relat_1(A, k1_relat_1(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t182_relat_1)).
% 7.55/2.48  tff(f_107, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r1_tarski(A, k2_relat_1(B)) => (k9_relat_1(B, k10_relat_1(B, A)) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t147_funct_1)).
% 7.55/2.48  tff(f_215, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (r2_relset_1(B, B, k1_partfun1(B, A, A, B, D, C), k6_partfun1(B)) => (k2_relset_1(A, B, C) = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t24_funct_2)).
% 7.55/2.48  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 7.55/2.48  tff(f_87, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(B), A) => (k5_relat_1(B, k6_relat_1(A)) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_relat_1)).
% 7.55/2.48  tff(f_81, axiom, (![A]: (v1_relat_1(A) => (k5_relat_1(k6_relat_1(k1_relat_1(A)), A) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t78_relat_1)).
% 7.55/2.48  tff(f_73, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (k5_relat_1(k5_relat_1(A, B), C) = k5_relat_1(A, k5_relat_1(B, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_relat_1)).
% 7.55/2.48  tff(f_134, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k2_relat_1(A) = k1_relat_1(k2_funct_1(A))) & (k1_relat_1(A) = k2_relat_1(k2_funct_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_funct_1)).
% 7.55/2.48  tff(f_95, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 7.55/2.48  tff(f_144, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k5_relat_1(A, k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))) & (k5_relat_1(k2_funct_1(A), A) = k6_relat_1(k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t61_funct_1)).
% 7.55/2.48  tff(c_80, plain, (k2_funct_1('#skF_3')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_241])).
% 7.55/2.48  tff(c_14, plain, (![A_8, B_9]: (v1_relat_1(k2_zfmisc_1(A_8, B_9)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 7.55/2.48  tff(c_92, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_241])).
% 7.55/2.48  tff(c_174, plain, (![B_82, A_83]: (v1_relat_1(B_82) | ~m1_subset_1(B_82, k1_zfmisc_1(A_83)) | ~v1_relat_1(A_83))), inference(cnfTransformation, [status(thm)], [f_38])).
% 7.55/2.48  tff(c_180, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_1'))), inference(resolution, [status(thm)], [c_92, c_174])).
% 7.55/2.48  tff(c_189, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_14, c_180])).
% 7.55/2.48  tff(c_249, plain, (![C_96, A_97, B_98]: (v4_relat_1(C_96, A_97) | ~m1_subset_1(C_96, k1_zfmisc_1(k2_zfmisc_1(A_97, B_98))))), inference(cnfTransformation, [status(thm)], [f_158])).
% 7.55/2.48  tff(c_261, plain, (v4_relat_1('#skF_4', '#skF_2')), inference(resolution, [status(thm)], [c_92, c_249])).
% 7.55/2.48  tff(c_12, plain, (![B_7, A_6]: (r1_tarski(k1_relat_1(B_7), A_6) | ~v4_relat_1(B_7, A_6) | ~v1_relat_1(B_7))), inference(cnfTransformation, [status(thm)], [f_44])).
% 7.55/2.48  tff(c_96, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_241])).
% 7.55/2.48  tff(c_98, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_241])).
% 7.55/2.48  tff(c_183, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_98, c_174])).
% 7.55/2.48  tff(c_192, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_14, c_183])).
% 7.55/2.48  tff(c_102, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_241])).
% 7.55/2.48  tff(c_76, plain, (![A_61]: (k6_relat_1(A_61)=k6_partfun1(A_61))), inference(cnfTransformation, [status(thm)], [f_198])).
% 7.55/2.48  tff(c_38, plain, (![A_29]: (v2_funct_1(k6_relat_1(A_29)))), inference(cnfTransformation, [status(thm)], [f_99])).
% 7.55/2.48  tff(c_105, plain, (![A_29]: (v2_funct_1(k6_partfun1(A_29)))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_38])).
% 7.55/2.48  tff(c_90, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_2'), inference(cnfTransformation, [status(thm)], [f_241])).
% 7.55/2.48  tff(c_648, plain, (![A_129, B_130, C_131]: (k2_relset_1(A_129, B_130, C_131)=k2_relat_1(C_131) | ~m1_subset_1(C_131, k1_zfmisc_1(k2_zfmisc_1(A_129, B_130))))), inference(cnfTransformation, [status(thm)], [f_162])).
% 7.55/2.48  tff(c_657, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_98, c_648])).
% 7.55/2.48  tff(c_662, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_90, c_657])).
% 7.55/2.48  tff(c_2700, plain, (![F_203, A_206, D_204, B_205, C_207, E_208]: (m1_subset_1(k1_partfun1(A_206, B_205, C_207, D_204, E_208, F_203), k1_zfmisc_1(k2_zfmisc_1(A_206, D_204))) | ~m1_subset_1(F_203, k1_zfmisc_1(k2_zfmisc_1(C_207, D_204))) | ~v1_funct_1(F_203) | ~m1_subset_1(E_208, k1_zfmisc_1(k2_zfmisc_1(A_206, B_205))) | ~v1_funct_1(E_208))), inference(cnfTransformation, [status(thm)], [f_182])).
% 7.55/2.48  tff(c_72, plain, (![A_54]: (m1_subset_1(k6_partfun1(A_54), k1_zfmisc_1(k2_zfmisc_1(A_54, A_54))))), inference(cnfTransformation, [status(thm)], [f_186])).
% 7.55/2.48  tff(c_88, plain, (r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k6_partfun1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_241])).
% 7.55/2.48  tff(c_2167, plain, (![D_176, C_177, A_178, B_179]: (D_176=C_177 | ~r2_relset_1(A_178, B_179, C_177, D_176) | ~m1_subset_1(D_176, k1_zfmisc_1(k2_zfmisc_1(A_178, B_179))) | ~m1_subset_1(C_177, k1_zfmisc_1(k2_zfmisc_1(A_178, B_179))))), inference(cnfTransformation, [status(thm)], [f_170])).
% 7.55/2.48  tff(c_2175, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_88, c_2167])).
% 7.55/2.48  tff(c_2190, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_2175])).
% 7.55/2.48  tff(c_2333, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_2190])).
% 7.55/2.48  tff(c_2703, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_2700, c_2333])).
% 7.55/2.48  tff(c_2731, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_102, c_98, c_96, c_92, c_2703])).
% 7.55/2.48  tff(c_2732, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_2190])).
% 7.55/2.48  tff(c_3014, plain, (![D_221, F_224, B_220, C_223, A_222, E_225]: (k1_partfun1(A_222, B_220, C_223, D_221, E_225, F_224)=k5_relat_1(E_225, F_224) | ~m1_subset_1(F_224, k1_zfmisc_1(k2_zfmisc_1(C_223, D_221))) | ~v1_funct_1(F_224) | ~m1_subset_1(E_225, k1_zfmisc_1(k2_zfmisc_1(A_222, B_220))) | ~v1_funct_1(E_225))), inference(cnfTransformation, [status(thm)], [f_196])).
% 7.55/2.48  tff(c_3018, plain, (![A_222, B_220, E_225]: (k1_partfun1(A_222, B_220, '#skF_2', '#skF_1', E_225, '#skF_4')=k5_relat_1(E_225, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_225, k1_zfmisc_1(k2_zfmisc_1(A_222, B_220))) | ~v1_funct_1(E_225))), inference(resolution, [status(thm)], [c_92, c_3014])).
% 7.55/2.48  tff(c_3890, plain, (![A_253, B_254, E_255]: (k1_partfun1(A_253, B_254, '#skF_2', '#skF_1', E_255, '#skF_4')=k5_relat_1(E_255, '#skF_4') | ~m1_subset_1(E_255, k1_zfmisc_1(k2_zfmisc_1(A_253, B_254))) | ~v1_funct_1(E_255))), inference(demodulation, [status(thm), theory('equality')], [c_96, c_3018])).
% 7.55/2.48  tff(c_3905, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_98, c_3890])).
% 7.55/2.48  tff(c_3916, plain, (k5_relat_1('#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_102, c_2732, c_3905])).
% 7.55/2.48  tff(c_42, plain, (![A_32, B_34]: (v2_funct_1(A_32) | k2_relat_1(B_34)!=k1_relat_1(A_32) | ~v2_funct_1(k5_relat_1(B_34, A_32)) | ~v1_funct_1(B_34) | ~v1_relat_1(B_34) | ~v1_funct_1(A_32) | ~v1_relat_1(A_32))), inference(cnfTransformation, [status(thm)], [f_124])).
% 7.55/2.48  tff(c_3929, plain, (v2_funct_1('#skF_4') | k2_relat_1('#skF_3')!=k1_relat_1('#skF_4') | ~v2_funct_1(k6_partfun1('#skF_1')) | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_3916, c_42])).
% 7.55/2.48  tff(c_3945, plain, (v2_funct_1('#skF_4') | k1_relat_1('#skF_4')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_189, c_96, c_192, c_102, c_105, c_662, c_3929])).
% 7.55/2.48  tff(c_3951, plain, (k1_relat_1('#skF_4')!='#skF_2'), inference(splitLeft, [status(thm)], [c_3945])).
% 7.55/2.48  tff(c_262, plain, (v4_relat_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_98, c_249])).
% 7.55/2.48  tff(c_272, plain, (![B_101, A_102]: (k7_relat_1(B_101, A_102)=B_101 | ~v4_relat_1(B_101, A_102) | ~v1_relat_1(B_101))), inference(cnfTransformation, [status(thm)], [f_63])).
% 7.55/2.48  tff(c_275, plain, (k7_relat_1('#skF_3', '#skF_1')='#skF_3' | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_262, c_272])).
% 7.55/2.48  tff(c_290, plain, (k7_relat_1('#skF_3', '#skF_1')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_192, c_275])).
% 7.55/2.48  tff(c_16, plain, (![B_11, A_10]: (k2_relat_1(k7_relat_1(B_11, A_10))=k9_relat_1(B_11, A_10) | ~v1_relat_1(B_11))), inference(cnfTransformation, [status(thm)], [f_50])).
% 7.55/2.48  tff(c_304, plain, (k9_relat_1('#skF_3', '#skF_1')=k2_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_290, c_16])).
% 7.55/2.48  tff(c_308, plain, (k9_relat_1('#skF_3', '#skF_1')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_192, c_304])).
% 7.55/2.48  tff(c_663, plain, (k9_relat_1('#skF_3', '#skF_1')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_662, c_308])).
% 7.55/2.48  tff(c_24, plain, (![A_24]: (k1_relat_1(k6_relat_1(A_24))=A_24)), inference(cnfTransformation, [status(thm)], [f_77])).
% 7.55/2.48  tff(c_110, plain, (![A_24]: (k1_relat_1(k6_partfun1(A_24))=A_24)), inference(demodulation, [status(thm), theory('equality')], [c_76, c_24])).
% 7.55/2.48  tff(c_18, plain, (![A_12, B_14]: (k10_relat_1(A_12, k1_relat_1(B_14))=k1_relat_1(k5_relat_1(A_12, B_14)) | ~v1_relat_1(B_14) | ~v1_relat_1(A_12))), inference(cnfTransformation, [status(thm)], [f_57])).
% 7.55/2.48  tff(c_878, plain, (![B_141, A_142]: (k9_relat_1(B_141, k10_relat_1(B_141, A_142))=A_142 | ~r1_tarski(A_142, k2_relat_1(B_141)) | ~v1_funct_1(B_141) | ~v1_relat_1(B_141))), inference(cnfTransformation, [status(thm)], [f_107])).
% 7.55/2.48  tff(c_880, plain, (![A_142]: (k9_relat_1('#skF_3', k10_relat_1('#skF_3', A_142))=A_142 | ~r1_tarski(A_142, '#skF_2') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_662, c_878])).
% 7.55/2.48  tff(c_899, plain, (![A_143]: (k9_relat_1('#skF_3', k10_relat_1('#skF_3', A_143))=A_143 | ~r1_tarski(A_143, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_192, c_102, c_880])).
% 7.55/2.48  tff(c_912, plain, (![B_14]: (k9_relat_1('#skF_3', k1_relat_1(k5_relat_1('#skF_3', B_14)))=k1_relat_1(B_14) | ~r1_tarski(k1_relat_1(B_14), '#skF_2') | ~v1_relat_1(B_14) | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_18, c_899])).
% 7.55/2.48  tff(c_918, plain, (![B_14]: (k9_relat_1('#skF_3', k1_relat_1(k5_relat_1('#skF_3', B_14)))=k1_relat_1(B_14) | ~r1_tarski(k1_relat_1(B_14), '#skF_2') | ~v1_relat_1(B_14))), inference(demodulation, [status(thm), theory('equality')], [c_192, c_912])).
% 7.55/2.48  tff(c_3935, plain, (k9_relat_1('#skF_3', k1_relat_1(k6_partfun1('#skF_1')))=k1_relat_1('#skF_4') | ~r1_tarski(k1_relat_1('#skF_4'), '#skF_2') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_3916, c_918])).
% 7.55/2.48  tff(c_3949, plain, (k1_relat_1('#skF_4')='#skF_2' | ~r1_tarski(k1_relat_1('#skF_4'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_189, c_663, c_110, c_3935])).
% 7.55/2.48  tff(c_3952, plain, (~r1_tarski(k1_relat_1('#skF_4'), '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_3951, c_3949])).
% 7.55/2.48  tff(c_3955, plain, (~v4_relat_1('#skF_4', '#skF_2') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_12, c_3952])).
% 7.55/2.48  tff(c_3959, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_189, c_261, c_3955])).
% 7.55/2.48  tff(c_3961, plain, (k1_relat_1('#skF_4')='#skF_2'), inference(splitRight, [status(thm)], [c_3945])).
% 7.55/2.48  tff(c_36, plain, (![A_29]: (v1_relat_1(k6_relat_1(A_29)))), inference(cnfTransformation, [status(thm)], [f_99])).
% 7.55/2.48  tff(c_106, plain, (![A_29]: (v1_relat_1(k6_partfun1(A_29)))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_36])).
% 7.55/2.48  tff(c_94, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_241])).
% 7.55/2.48  tff(c_100, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_241])).
% 7.55/2.48  tff(c_572, plain, (![A_121, B_122, D_123]: (r2_relset_1(A_121, B_122, D_123, D_123) | ~m1_subset_1(D_123, k1_zfmisc_1(k2_zfmisc_1(A_121, B_122))))), inference(cnfTransformation, [status(thm)], [f_170])).
% 7.55/2.48  tff(c_579, plain, (![A_54]: (r2_relset_1(A_54, A_54, k6_partfun1(A_54), k6_partfun1(A_54)))), inference(resolution, [status(thm)], [c_72, c_572])).
% 7.55/2.48  tff(c_660, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_92, c_648])).
% 7.55/2.48  tff(c_3441, plain, (![A_246, B_247, C_248, D_249]: (k2_relset_1(A_246, B_247, C_248)=B_247 | ~r2_relset_1(B_247, B_247, k1_partfun1(B_247, A_246, A_246, B_247, D_249, C_248), k6_partfun1(B_247)) | ~m1_subset_1(D_249, k1_zfmisc_1(k2_zfmisc_1(B_247, A_246))) | ~v1_funct_2(D_249, B_247, A_246) | ~v1_funct_1(D_249) | ~m1_subset_1(C_248, k1_zfmisc_1(k2_zfmisc_1(A_246, B_247))) | ~v1_funct_2(C_248, A_246, B_247) | ~v1_funct_1(C_248))), inference(cnfTransformation, [status(thm)], [f_215])).
% 7.55/2.49  tff(c_3447, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')='#skF_1' | ~r2_relset_1('#skF_1', '#skF_1', k6_partfun1('#skF_1'), k6_partfun1('#skF_1')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_2732, c_3441])).
% 7.55/2.49  tff(c_3451, plain, (k2_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_96, c_94, c_92, c_102, c_100, c_98, c_579, c_660, c_3447])).
% 7.55/2.49  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 7.55/2.49  tff(c_30, plain, (![B_27, A_26]: (k5_relat_1(B_27, k6_relat_1(A_26))=B_27 | ~r1_tarski(k2_relat_1(B_27), A_26) | ~v1_relat_1(B_27))), inference(cnfTransformation, [status(thm)], [f_87])).
% 7.55/2.49  tff(c_493, plain, (![B_116, A_117]: (k5_relat_1(B_116, k6_partfun1(A_117))=B_116 | ~r1_tarski(k2_relat_1(B_116), A_117) | ~v1_relat_1(B_116))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_30])).
% 7.55/2.49  tff(c_506, plain, (![B_116]: (k5_relat_1(B_116, k6_partfun1(k2_relat_1(B_116)))=B_116 | ~v1_relat_1(B_116))), inference(resolution, [status(thm)], [c_6, c_493])).
% 7.55/2.49  tff(c_3465, plain, (k5_relat_1('#skF_4', k6_partfun1('#skF_1'))='#skF_4' | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_3451, c_506])).
% 7.55/2.49  tff(c_3478, plain, (k5_relat_1('#skF_4', k6_partfun1('#skF_1'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_189, c_3465])).
% 7.55/2.49  tff(c_28, plain, (![A_25]: (k5_relat_1(k6_relat_1(k1_relat_1(A_25)), A_25)=A_25 | ~v1_relat_1(A_25))), inference(cnfTransformation, [status(thm)], [f_81])).
% 7.55/2.49  tff(c_108, plain, (![A_25]: (k5_relat_1(k6_partfun1(k1_relat_1(A_25)), A_25)=A_25 | ~v1_relat_1(A_25))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_28])).
% 7.55/2.49  tff(c_1296, plain, (![A_155, B_156, C_157]: (k5_relat_1(k5_relat_1(A_155, B_156), C_157)=k5_relat_1(A_155, k5_relat_1(B_156, C_157)) | ~v1_relat_1(C_157) | ~v1_relat_1(B_156) | ~v1_relat_1(A_155))), inference(cnfTransformation, [status(thm)], [f_73])).
% 7.55/2.49  tff(c_1352, plain, (![A_25, C_157]: (k5_relat_1(k6_partfun1(k1_relat_1(A_25)), k5_relat_1(A_25, C_157))=k5_relat_1(A_25, C_157) | ~v1_relat_1(C_157) | ~v1_relat_1(A_25) | ~v1_relat_1(k6_partfun1(k1_relat_1(A_25))) | ~v1_relat_1(A_25))), inference(superposition, [status(thm), theory('equality')], [c_108, c_1296])).
% 7.55/2.49  tff(c_3549, plain, (![A_250, C_251]: (k5_relat_1(k6_partfun1(k1_relat_1(A_250)), k5_relat_1(A_250, C_251))=k5_relat_1(A_250, C_251) | ~v1_relat_1(C_251) | ~v1_relat_1(A_250))), inference(demodulation, [status(thm), theory('equality')], [c_106, c_1352])).
% 7.55/2.49  tff(c_3582, plain, (k5_relat_1(k6_partfun1(k1_relat_1('#skF_4')), '#skF_4')=k5_relat_1('#skF_4', k6_partfun1('#skF_1')) | ~v1_relat_1(k6_partfun1('#skF_1')) | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_3478, c_3549])).
% 7.55/2.49  tff(c_3676, plain, (k5_relat_1(k6_partfun1(k1_relat_1('#skF_4')), '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_189, c_106, c_3478, c_3582])).
% 7.55/2.49  tff(c_4011, plain, (k5_relat_1(k6_partfun1('#skF_2'), '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_3961, c_3676])).
% 7.55/2.49  tff(c_1372, plain, (![A_25, C_157]: (k5_relat_1(k6_partfun1(k1_relat_1(A_25)), k5_relat_1(A_25, C_157))=k5_relat_1(A_25, C_157) | ~v1_relat_1(C_157) | ~v1_relat_1(A_25))), inference(demodulation, [status(thm), theory('equality')], [c_106, c_1352])).
% 7.55/2.49  tff(c_3920, plain, (k5_relat_1(k6_partfun1(k1_relat_1('#skF_3')), k6_partfun1('#skF_1'))=k5_relat_1('#skF_3', '#skF_4') | ~v1_relat_1('#skF_4') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_3916, c_1372])).
% 7.55/2.49  tff(c_3939, plain, (k5_relat_1(k6_partfun1(k1_relat_1('#skF_3')), k6_partfun1('#skF_1'))=k6_partfun1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_192, c_189, c_3916, c_3920])).
% 7.55/2.49  tff(c_26, plain, (![A_24]: (k2_relat_1(k6_relat_1(A_24))=A_24)), inference(cnfTransformation, [status(thm)], [f_77])).
% 7.55/2.49  tff(c_109, plain, (![A_24]: (k2_relat_1(k6_partfun1(A_24))=A_24)), inference(demodulation, [status(thm), theory('equality')], [c_76, c_26])).
% 7.55/2.49  tff(c_499, plain, (![A_24, A_117]: (k5_relat_1(k6_partfun1(A_24), k6_partfun1(A_117))=k6_partfun1(A_24) | ~r1_tarski(A_24, A_117) | ~v1_relat_1(k6_partfun1(A_24)))), inference(superposition, [status(thm), theory('equality')], [c_109, c_493])).
% 7.55/2.49  tff(c_505, plain, (![A_24, A_117]: (k5_relat_1(k6_partfun1(A_24), k6_partfun1(A_117))=k6_partfun1(A_24) | ~r1_tarski(A_24, A_117))), inference(demodulation, [status(thm), theory('equality')], [c_106, c_499])).
% 7.55/2.49  tff(c_631, plain, (![A_127, B_128]: (k10_relat_1(A_127, k1_relat_1(B_128))=k1_relat_1(k5_relat_1(A_127, B_128)) | ~v1_relat_1(B_128) | ~v1_relat_1(A_127))), inference(cnfTransformation, [status(thm)], [f_57])).
% 7.55/2.49  tff(c_643, plain, (![A_127, A_24]: (k1_relat_1(k5_relat_1(A_127, k6_partfun1(A_24)))=k10_relat_1(A_127, A_24) | ~v1_relat_1(k6_partfun1(A_24)) | ~v1_relat_1(A_127))), inference(superposition, [status(thm), theory('equality')], [c_110, c_631])).
% 7.55/2.49  tff(c_734, plain, (![A_134, A_135]: (k1_relat_1(k5_relat_1(A_134, k6_partfun1(A_135)))=k10_relat_1(A_134, A_135) | ~v1_relat_1(A_134))), inference(demodulation, [status(thm), theory('equality')], [c_106, c_643])).
% 7.55/2.49  tff(c_770, plain, (![A_24, A_117]: (k10_relat_1(k6_partfun1(A_24), A_117)=k1_relat_1(k6_partfun1(A_24)) | ~v1_relat_1(k6_partfun1(A_24)) | ~r1_tarski(A_24, A_117))), inference(superposition, [status(thm), theory('equality')], [c_505, c_734])).
% 7.55/2.49  tff(c_837, plain, (![A_138, A_139]: (k10_relat_1(k6_partfun1(A_138), A_139)=A_138 | ~r1_tarski(A_138, A_139))), inference(demodulation, [status(thm), theory('equality')], [c_106, c_110, c_770])).
% 7.55/2.49  tff(c_858, plain, (![A_138, B_14]: (k1_relat_1(k5_relat_1(k6_partfun1(A_138), B_14))=A_138 | ~r1_tarski(A_138, k1_relat_1(B_14)) | ~v1_relat_1(B_14) | ~v1_relat_1(k6_partfun1(A_138)))), inference(superposition, [status(thm), theory('equality')], [c_18, c_837])).
% 7.55/2.49  tff(c_870, plain, (![A_138, B_14]: (k1_relat_1(k5_relat_1(k6_partfun1(A_138), B_14))=A_138 | ~r1_tarski(A_138, k1_relat_1(B_14)) | ~v1_relat_1(B_14))), inference(demodulation, [status(thm), theory('equality')], [c_106, c_858])).
% 7.55/2.49  tff(c_4274, plain, (k1_relat_1(k6_partfun1('#skF_1'))=k1_relat_1('#skF_3') | ~r1_tarski(k1_relat_1('#skF_3'), k1_relat_1(k6_partfun1('#skF_1'))) | ~v1_relat_1(k6_partfun1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_3939, c_870])).
% 7.55/2.49  tff(c_4300, plain, (k1_relat_1('#skF_3')='#skF_1' | ~r1_tarski(k1_relat_1('#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_106, c_110, c_110, c_4274])).
% 7.55/2.49  tff(c_4343, plain, (~r1_tarski(k1_relat_1('#skF_3'), '#skF_1')), inference(splitLeft, [status(thm)], [c_4300])).
% 7.55/2.49  tff(c_4346, plain, (~v4_relat_1('#skF_3', '#skF_1') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_12, c_4343])).
% 7.55/2.49  tff(c_4350, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_192, c_262, c_4346])).
% 7.55/2.49  tff(c_4351, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(splitRight, [status(thm)], [c_4300])).
% 7.55/2.49  tff(c_86, plain, (v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_241])).
% 7.55/2.49  tff(c_46, plain, (![A_35]: (k2_relat_1(k2_funct_1(A_35))=k1_relat_1(A_35) | ~v2_funct_1(A_35) | ~v1_funct_1(A_35) | ~v1_relat_1(A_35))), inference(cnfTransformation, [status(thm)], [f_134])).
% 7.55/2.49  tff(c_34, plain, (![A_28]: (v1_relat_1(k2_funct_1(A_28)) | ~v1_funct_1(A_28) | ~v1_relat_1(A_28))), inference(cnfTransformation, [status(thm)], [f_95])).
% 7.55/2.49  tff(c_667, plain, (k5_relat_1('#skF_3', k6_partfun1('#skF_2'))='#skF_3' | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_662, c_506])).
% 7.55/2.49  tff(c_674, plain, (k5_relat_1('#skF_3', k6_partfun1('#skF_2'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_192, c_667])).
% 7.55/2.49  tff(c_767, plain, (k10_relat_1('#skF_3', '#skF_2')=k1_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_674, c_734])).
% 7.55/2.49  tff(c_786, plain, (k10_relat_1('#skF_3', '#skF_2')=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_192, c_767])).
% 7.55/2.49  tff(c_908, plain, (k9_relat_1('#skF_3', k1_relat_1('#skF_3'))='#skF_2' | ~r1_tarski('#skF_2', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_786, c_899])).
% 7.55/2.49  tff(c_916, plain, (k9_relat_1('#skF_3', k1_relat_1('#skF_3'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_6, c_908])).
% 7.55/2.49  tff(c_52, plain, (![A_36]: (k5_relat_1(A_36, k2_funct_1(A_36))=k6_relat_1(k1_relat_1(A_36)) | ~v2_funct_1(A_36) | ~v1_funct_1(A_36) | ~v1_relat_1(A_36))), inference(cnfTransformation, [status(thm)], [f_144])).
% 7.55/2.49  tff(c_103, plain, (![A_36]: (k5_relat_1(A_36, k2_funct_1(A_36))=k6_partfun1(k1_relat_1(A_36)) | ~v2_funct_1(A_36) | ~v1_funct_1(A_36) | ~v1_relat_1(A_36))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_52])).
% 7.55/2.49  tff(c_1160, plain, (![B_152]: (k9_relat_1('#skF_3', k1_relat_1(k5_relat_1('#skF_3', B_152)))=k1_relat_1(B_152) | ~r1_tarski(k1_relat_1(B_152), '#skF_2') | ~v1_relat_1(B_152))), inference(demodulation, [status(thm), theory('equality')], [c_192, c_912])).
% 7.55/2.49  tff(c_1170, plain, (k9_relat_1('#skF_3', k1_relat_1(k6_partfun1(k1_relat_1('#skF_3'))))=k1_relat_1(k2_funct_1('#skF_3')) | ~r1_tarski(k1_relat_1(k2_funct_1('#skF_3')), '#skF_2') | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_103, c_1160])).
% 7.55/2.49  tff(c_1188, plain, (k1_relat_1(k2_funct_1('#skF_3'))='#skF_2' | ~r1_tarski(k1_relat_1(k2_funct_1('#skF_3')), '#skF_2') | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_192, c_102, c_86, c_916, c_110, c_1170])).
% 7.55/2.49  tff(c_1286, plain, (~v1_relat_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_1188])).
% 7.55/2.49  tff(c_1289, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_34, c_1286])).
% 7.55/2.49  tff(c_1293, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_192, c_102, c_1289])).
% 7.55/2.49  tff(c_1295, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_1188])).
% 7.55/2.49  tff(c_48, plain, (![A_35]: (k1_relat_1(k2_funct_1(A_35))=k2_relat_1(A_35) | ~v2_funct_1(A_35) | ~v1_funct_1(A_35) | ~v1_relat_1(A_35))), inference(cnfTransformation, [status(thm)], [f_134])).
% 7.55/2.49  tff(c_1294, plain, (~r1_tarski(k1_relat_1(k2_funct_1('#skF_3')), '#skF_2') | k1_relat_1(k2_funct_1('#skF_3'))='#skF_2'), inference(splitRight, [status(thm)], [c_1188])).
% 7.55/2.49  tff(c_1373, plain, (~r1_tarski(k1_relat_1(k2_funct_1('#skF_3')), '#skF_2')), inference(splitLeft, [status(thm)], [c_1294])).
% 7.55/2.49  tff(c_1376, plain, (~r1_tarski(k2_relat_1('#skF_3'), '#skF_2') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_48, c_1373])).
% 7.55/2.49  tff(c_1382, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_192, c_102, c_86, c_6, c_662, c_1376])).
% 7.55/2.49  tff(c_1383, plain, (k1_relat_1(k2_funct_1('#skF_3'))='#skF_2'), inference(splitRight, [status(thm)], [c_1294])).
% 7.55/2.49  tff(c_1415, plain, (k5_relat_1(k6_partfun1('#skF_2'), k2_funct_1('#skF_3'))=k2_funct_1('#skF_3') | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_1383, c_108])).
% 7.55/2.49  tff(c_1440, plain, (k5_relat_1(k6_partfun1('#skF_2'), k2_funct_1('#skF_3'))=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1295, c_1415])).
% 7.55/2.49  tff(c_22, plain, (![A_17, B_21, C_23]: (k5_relat_1(k5_relat_1(A_17, B_21), C_23)=k5_relat_1(A_17, k5_relat_1(B_21, C_23)) | ~v1_relat_1(C_23) | ~v1_relat_1(B_21) | ~v1_relat_1(A_17))), inference(cnfTransformation, [status(thm)], [f_73])).
% 7.55/2.49  tff(c_1613, plain, (![C_23]: (k5_relat_1(k6_partfun1('#skF_2'), k5_relat_1(k2_funct_1('#skF_3'), C_23))=k5_relat_1(k2_funct_1('#skF_3'), C_23) | ~v1_relat_1(C_23) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k6_partfun1('#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_1440, c_22])).
% 7.55/2.49  tff(c_2191, plain, (![C_180]: (k5_relat_1(k6_partfun1('#skF_2'), k5_relat_1(k2_funct_1('#skF_3'), C_180))=k5_relat_1(k2_funct_1('#skF_3'), C_180) | ~v1_relat_1(C_180))), inference(demodulation, [status(thm), theory('equality')], [c_106, c_1295, c_1613])).
% 7.55/2.49  tff(c_2233, plain, (k5_relat_1(k2_funct_1('#skF_3'), k6_partfun1(k2_relat_1(k2_funct_1('#skF_3'))))=k5_relat_1(k6_partfun1('#skF_2'), k2_funct_1('#skF_3')) | ~v1_relat_1(k6_partfun1(k2_relat_1(k2_funct_1('#skF_3')))) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_506, c_2191])).
% 7.55/2.49  tff(c_2252, plain, (k5_relat_1(k2_funct_1('#skF_3'), k6_partfun1(k2_relat_1(k2_funct_1('#skF_3'))))=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1295, c_106, c_1440, c_2233])).
% 7.55/2.49  tff(c_2309, plain, (k5_relat_1(k2_funct_1('#skF_3'), k6_partfun1(k1_relat_1('#skF_3')))=k2_funct_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_46, c_2252])).
% 7.55/2.49  tff(c_2329, plain, (k5_relat_1(k2_funct_1('#skF_3'), k6_partfun1(k1_relat_1('#skF_3')))=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_192, c_102, c_86, c_2309])).
% 7.55/2.49  tff(c_4363, plain, (k5_relat_1(k2_funct_1('#skF_3'), k6_partfun1('#skF_1'))=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_4351, c_2329])).
% 7.55/2.49  tff(c_151, plain, (![A_80]: (k5_relat_1(k6_partfun1(k1_relat_1(A_80)), A_80)=A_80 | ~v1_relat_1(A_80))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_28])).
% 7.55/2.49  tff(c_160, plain, (![A_24]: (k5_relat_1(k6_partfun1(A_24), k6_partfun1(A_24))=k6_partfun1(A_24) | ~v1_relat_1(k6_partfun1(A_24)))), inference(superposition, [status(thm), theory('equality')], [c_110, c_151])).
% 7.55/2.49  tff(c_164, plain, (![A_24]: (k5_relat_1(k6_partfun1(A_24), k6_partfun1(A_24))=k6_partfun1(A_24))), inference(demodulation, [status(thm), theory('equality')], [c_106, c_160])).
% 7.55/2.49  tff(c_50, plain, (![A_36]: (k5_relat_1(k2_funct_1(A_36), A_36)=k6_relat_1(k2_relat_1(A_36)) | ~v2_funct_1(A_36) | ~v1_funct_1(A_36) | ~v1_relat_1(A_36))), inference(cnfTransformation, [status(thm)], [f_144])).
% 7.55/2.49  tff(c_104, plain, (![A_36]: (k5_relat_1(k2_funct_1(A_36), A_36)=k6_partfun1(k2_relat_1(A_36)) | ~v2_funct_1(A_36) | ~v1_funct_1(A_36) | ~v1_relat_1(A_36))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_50])).
% 7.55/2.49  tff(c_2229, plain, (k5_relat_1(k6_partfun1('#skF_2'), k6_partfun1(k2_relat_1('#skF_3')))=k5_relat_1(k2_funct_1('#skF_3'), '#skF_3') | ~v1_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_104, c_2191])).
% 7.55/2.49  tff(c_2250, plain, (k5_relat_1(k2_funct_1('#skF_3'), '#skF_3')=k6_partfun1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_192, c_102, c_86, c_192, c_164, c_662, c_2229])).
% 7.55/2.49  tff(c_2265, plain, (![C_23]: (k5_relat_1(k2_funct_1('#skF_3'), k5_relat_1('#skF_3', C_23))=k5_relat_1(k6_partfun1('#skF_2'), C_23) | ~v1_relat_1(C_23) | ~v1_relat_1('#skF_3') | ~v1_relat_1(k2_funct_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_2250, c_22])).
% 7.55/2.49  tff(c_2281, plain, (![C_23]: (k5_relat_1(k2_funct_1('#skF_3'), k5_relat_1('#skF_3', C_23))=k5_relat_1(k6_partfun1('#skF_2'), C_23) | ~v1_relat_1(C_23))), inference(demodulation, [status(thm), theory('equality')], [c_1295, c_192, c_2265])).
% 7.55/2.49  tff(c_3923, plain, (k5_relat_1(k2_funct_1('#skF_3'), k6_partfun1('#skF_1'))=k5_relat_1(k6_partfun1('#skF_2'), '#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_3916, c_2281])).
% 7.55/2.49  tff(c_3941, plain, (k5_relat_1(k2_funct_1('#skF_3'), k6_partfun1('#skF_1'))=k5_relat_1(k6_partfun1('#skF_2'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_189, c_3923])).
% 7.55/2.49  tff(c_5934, plain, (k2_funct_1('#skF_3')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_4011, c_4363, c_3941])).
% 7.55/2.49  tff(c_5935, plain, $false, inference(negUnitSimplification, [status(thm)], [c_80, c_5934])).
% 7.55/2.49  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.55/2.49  
% 7.55/2.49  Inference rules
% 7.55/2.49  ----------------------
% 7.55/2.49  #Ref     : 0
% 7.55/2.49  #Sup     : 1237
% 7.55/2.49  #Fact    : 0
% 7.55/2.49  #Define  : 0
% 7.55/2.49  #Split   : 11
% 7.55/2.49  #Chain   : 0
% 7.55/2.49  #Close   : 0
% 7.55/2.49  
% 7.55/2.49  Ordering : KBO
% 7.55/2.49  
% 7.55/2.49  Simplification rules
% 7.55/2.49  ----------------------
% 7.55/2.49  #Subsume      : 53
% 7.55/2.49  #Demod        : 2066
% 7.55/2.49  #Tautology    : 681
% 7.55/2.49  #SimpNegUnit  : 2
% 7.55/2.49  #BackRed      : 35
% 7.55/2.49  
% 7.55/2.49  #Partial instantiations: 0
% 7.55/2.49  #Strategies tried      : 1
% 7.55/2.49  
% 7.55/2.49  Timing (in seconds)
% 7.55/2.49  ----------------------
% 7.55/2.49  Preprocessing        : 0.41
% 7.55/2.49  Parsing              : 0.22
% 7.55/2.49  CNF conversion       : 0.03
% 7.55/2.49  Main loop            : 1.29
% 7.55/2.49  Inferencing          : 0.40
% 7.55/2.49  Reduction            : 0.51
% 7.55/2.49  Demodulation         : 0.40
% 7.55/2.49  BG Simplification    : 0.05
% 7.55/2.49  Subsumption          : 0.23
% 7.55/2.49  Abstraction          : 0.05
% 7.55/2.49  MUC search           : 0.00
% 7.55/2.49  Cooper               : 0.00
% 7.55/2.49  Total                : 1.76
% 7.55/2.49  Index Insertion      : 0.00
% 7.55/2.49  Index Deletion       : 0.00
% 7.55/2.49  Index Matching       : 0.00
% 7.55/2.49  BG Taut test         : 0.00
%------------------------------------------------------------------------------
