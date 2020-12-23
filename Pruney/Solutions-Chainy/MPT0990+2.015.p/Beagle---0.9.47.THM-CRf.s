%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:12:57 EST 2020

% Result     : Theorem 7.61s
% Output     : CNFRefutation 7.61s
% Verified   : 
% Statistics : Number of formulae       :  169 (1120 expanded)
%              Number of leaves         :   60 ( 427 expanded)
%              Depth                    :   21
%              Number of atoms          :  352 (4338 expanded)
%              Number of equality atoms :   97 (1276 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k9_relat_1 > k7_relat_1 > k5_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_subset_1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_238,negated_conjecture,(
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

tff(f_149,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_155,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_195,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_92,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v2_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_funct_1)).

tff(f_159,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_179,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( v1_funct_1(k1_partfun1(A,B,C,D,E,F))
        & m1_subset_1(k1_partfun1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).

tff(f_183,axiom,(
    ! [A] :
      ( v1_partfun1(k6_partfun1(A),A)
      & m1_subset_1(k6_partfun1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_partfun1)).

tff(f_167,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_193,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_117,axiom,(
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

tff(f_56,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_70,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_50,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k1_relat_1(k5_relat_1(A,B)) = k10_relat_1(A,k1_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t182_relat_1)).

tff(f_100,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r1_tarski(A,k2_relat_1(B))
       => k9_relat_1(B,k10_relat_1(B,A)) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t147_funct_1)).

tff(f_27,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_29,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_80,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k2_relat_1(B),A)
       => k5_relat_1(B,k6_relat_1(A)) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_relat_1)).

tff(f_137,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k5_relat_1(A,k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))
          & k5_relat_1(k2_funct_1(A),A) = k6_relat_1(k2_relat_1(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_funct_1)).

tff(f_88,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).

tff(f_212,axiom,(
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

tff(f_66,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ! [C] :
              ( v1_relat_1(C)
             => k5_relat_1(k5_relat_1(A,B),C) = k5_relat_1(A,k5_relat_1(B,C)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_relat_1)).

tff(f_127,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k2_relat_1(A) = k1_relat_1(k2_funct_1(A))
          & k1_relat_1(A) = k2_relat_1(k2_funct_1(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).

tff(f_74,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k5_relat_1(k6_relat_1(k1_relat_1(A)),A) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t78_relat_1)).

tff(f_145,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => k2_funct_1(k2_funct_1(A)) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_funct_1)).

tff(c_80,plain,(
    k2_funct_1('#skF_3') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_238])).

tff(c_92,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_238])).

tff(c_183,plain,(
    ! [C_85,A_86,B_87] :
      ( v1_relat_1(C_85)
      | ~ m1_subset_1(C_85,k1_zfmisc_1(k2_zfmisc_1(A_86,B_87))) ) ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_204,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_92,c_183])).

tff(c_96,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_238])).

tff(c_362,plain,(
    ! [C_112,A_113,B_114] :
      ( v4_relat_1(C_112,A_113)
      | ~ m1_subset_1(C_112,k1_zfmisc_1(k2_zfmisc_1(A_113,B_114))) ) ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_383,plain,(
    v4_relat_1('#skF_4','#skF_2') ),
    inference(resolution,[status(thm)],[c_92,c_362])).

tff(c_12,plain,(
    ! [B_6,A_5] :
      ( r1_tarski(k1_relat_1(B_6),A_5)
      | ~ v4_relat_1(B_6,A_5)
      | ~ v1_relat_1(B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_98,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_238])).

tff(c_205,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_98,c_183])).

tff(c_102,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_238])).

tff(c_76,plain,(
    ! [A_61] : k6_relat_1(A_61) = k6_partfun1(A_61) ),
    inference(cnfTransformation,[status(thm)],[f_195])).

tff(c_36,plain,(
    ! [A_26] : v2_funct_1(k6_relat_1(A_26)) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_105,plain,(
    ! [A_26] : v2_funct_1(k6_partfun1(A_26)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_36])).

tff(c_90,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_238])).

tff(c_933,plain,(
    ! [A_166,B_167,C_168] :
      ( k2_relset_1(A_166,B_167,C_168) = k2_relat_1(C_168)
      | ~ m1_subset_1(C_168,k1_zfmisc_1(k2_zfmisc_1(A_166,B_167))) ) ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_946,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_98,c_933])).

tff(c_956,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_946])).

tff(c_2832,plain,(
    ! [A_268,B_267,F_265,E_270,D_266,C_269] :
      ( m1_subset_1(k1_partfun1(A_268,B_267,C_269,D_266,E_270,F_265),k1_zfmisc_1(k2_zfmisc_1(A_268,D_266)))
      | ~ m1_subset_1(F_265,k1_zfmisc_1(k2_zfmisc_1(C_269,D_266)))
      | ~ v1_funct_1(F_265)
      | ~ m1_subset_1(E_270,k1_zfmisc_1(k2_zfmisc_1(A_268,B_267)))
      | ~ v1_funct_1(E_270) ) ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_72,plain,(
    ! [A_54] : m1_subset_1(k6_partfun1(A_54),k1_zfmisc_1(k2_zfmisc_1(A_54,A_54))) ),
    inference(cnfTransformation,[status(thm)],[f_183])).

tff(c_88,plain,(
    r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k6_partfun1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_238])).

tff(c_2365,plain,(
    ! [D_233,C_234,A_235,B_236] :
      ( D_233 = C_234
      | ~ r2_relset_1(A_235,B_236,C_234,D_233)
      | ~ m1_subset_1(D_233,k1_zfmisc_1(k2_zfmisc_1(A_235,B_236)))
      | ~ m1_subset_1(C_234,k1_zfmisc_1(k2_zfmisc_1(A_235,B_236))) ) ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_2375,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_88,c_2365])).

tff(c_2394,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_2375])).

tff(c_2498,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_2394])).

tff(c_2845,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_2832,c_2498])).

tff(c_2870,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_98,c_96,c_92,c_2845])).

tff(c_2871,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_2394])).

tff(c_3211,plain,(
    ! [A_290,D_289,F_292,E_293,B_288,C_291] :
      ( k1_partfun1(A_290,B_288,C_291,D_289,E_293,F_292) = k5_relat_1(E_293,F_292)
      | ~ m1_subset_1(F_292,k1_zfmisc_1(k2_zfmisc_1(C_291,D_289)))
      | ~ v1_funct_1(F_292)
      | ~ m1_subset_1(E_293,k1_zfmisc_1(k2_zfmisc_1(A_290,B_288)))
      | ~ v1_funct_1(E_293) ) ),
    inference(cnfTransformation,[status(thm)],[f_193])).

tff(c_3218,plain,(
    ! [A_290,B_288,E_293] :
      ( k1_partfun1(A_290,B_288,'#skF_2','#skF_1',E_293,'#skF_4') = k5_relat_1(E_293,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_293,k1_zfmisc_1(k2_zfmisc_1(A_290,B_288)))
      | ~ v1_funct_1(E_293) ) ),
    inference(resolution,[status(thm)],[c_92,c_3211])).

tff(c_3483,plain,(
    ! [A_306,B_307,E_308] :
      ( k1_partfun1(A_306,B_307,'#skF_2','#skF_1',E_308,'#skF_4') = k5_relat_1(E_308,'#skF_4')
      | ~ m1_subset_1(E_308,k1_zfmisc_1(k2_zfmisc_1(A_306,B_307)))
      | ~ v1_funct_1(E_308) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_3218])).

tff(c_3499,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_98,c_3483])).

tff(c_3512,plain,(
    k5_relat_1('#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_2871,c_3499])).

tff(c_40,plain,(
    ! [A_29,B_31] :
      ( v2_funct_1(A_29)
      | k2_relat_1(B_31) != k1_relat_1(A_29)
      | ~ v2_funct_1(k5_relat_1(B_31,A_29))
      | ~ v1_funct_1(B_31)
      | ~ v1_relat_1(B_31)
      | ~ v1_funct_1(A_29)
      | ~ v1_relat_1(A_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_3520,plain,
    ( v2_funct_1('#skF_4')
    | k2_relat_1('#skF_3') != k1_relat_1('#skF_4')
    | ~ v2_funct_1(k6_partfun1('#skF_1'))
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_3512,c_40])).

tff(c_3532,plain,
    ( v2_funct_1('#skF_4')
    | k1_relat_1('#skF_4') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_204,c_96,c_205,c_102,c_105,c_956,c_3520])).

tff(c_3538,plain,(
    k1_relat_1('#skF_4') != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_3532])).

tff(c_384,plain,(
    v4_relat_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_98,c_362])).

tff(c_18,plain,(
    ! [B_13,A_12] :
      ( k7_relat_1(B_13,A_12) = B_13
      | ~ v4_relat_1(B_13,A_12)
      | ~ v1_relat_1(B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_394,plain,
    ( k7_relat_1('#skF_3','#skF_1') = '#skF_3'
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_384,c_18])).

tff(c_397,plain,(
    k7_relat_1('#skF_3','#skF_1') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_205,c_394])).

tff(c_14,plain,(
    ! [B_8,A_7] :
      ( k2_relat_1(k7_relat_1(B_8,A_7)) = k9_relat_1(B_8,A_7)
      | ~ v1_relat_1(B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_410,plain,
    ( k9_relat_1('#skF_3','#skF_1') = k2_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_397,c_14])).

tff(c_414,plain,(
    k9_relat_1('#skF_3','#skF_1') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_205,c_410])).

tff(c_958,plain,(
    k9_relat_1('#skF_3','#skF_1') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_956,c_414])).

tff(c_22,plain,(
    ! [A_21] : k1_relat_1(k6_relat_1(A_21)) = A_21 ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_110,plain,(
    ! [A_21] : k1_relat_1(k6_partfun1(A_21)) = A_21 ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_22])).

tff(c_16,plain,(
    ! [A_9,B_11] :
      ( k10_relat_1(A_9,k1_relat_1(B_11)) = k1_relat_1(k5_relat_1(A_9,B_11))
      | ~ v1_relat_1(B_11)
      | ~ v1_relat_1(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_1174,plain,(
    ! [B_178,A_179] :
      ( k9_relat_1(B_178,k10_relat_1(B_178,A_179)) = A_179
      | ~ r1_tarski(A_179,k2_relat_1(B_178))
      | ~ v1_funct_1(B_178)
      | ~ v1_relat_1(B_178) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_1176,plain,(
    ! [A_179] :
      ( k9_relat_1('#skF_3',k10_relat_1('#skF_3',A_179)) = A_179
      | ~ r1_tarski(A_179,'#skF_2')
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_956,c_1174])).

tff(c_1195,plain,(
    ! [A_180] :
      ( k9_relat_1('#skF_3',k10_relat_1('#skF_3',A_180)) = A_180
      | ~ r1_tarski(A_180,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_205,c_102,c_1176])).

tff(c_1208,plain,(
    ! [B_11] :
      ( k9_relat_1('#skF_3',k1_relat_1(k5_relat_1('#skF_3',B_11))) = k1_relat_1(B_11)
      | ~ r1_tarski(k1_relat_1(B_11),'#skF_2')
      | ~ v1_relat_1(B_11)
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_1195])).

tff(c_1214,plain,(
    ! [B_11] :
      ( k9_relat_1('#skF_3',k1_relat_1(k5_relat_1('#skF_3',B_11))) = k1_relat_1(B_11)
      | ~ r1_tarski(k1_relat_1(B_11),'#skF_2')
      | ~ v1_relat_1(B_11) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_205,c_1208])).

tff(c_3526,plain,
    ( k9_relat_1('#skF_3',k1_relat_1(k6_partfun1('#skF_1'))) = k1_relat_1('#skF_4')
    | ~ r1_tarski(k1_relat_1('#skF_4'),'#skF_2')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_3512,c_1214])).

tff(c_3536,plain,
    ( k1_relat_1('#skF_4') = '#skF_2'
    | ~ r1_tarski(k1_relat_1('#skF_4'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_204,c_958,c_110,c_3526])).

tff(c_3539,plain,(
    ~ r1_tarski(k1_relat_1('#skF_4'),'#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_3538,c_3536])).

tff(c_3542,plain,
    ( ~ v4_relat_1('#skF_4','#skF_2')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_12,c_3539])).

tff(c_3546,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_204,c_383,c_3542])).

tff(c_3547,plain,(
    v2_funct_1('#skF_4') ),
    inference(splitRight,[status(thm)],[c_3532])).

tff(c_2,plain,(
    ! [A_1] : k2_subset_1(A_1) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_4,plain,(
    ! [A_2] : m1_subset_1(k2_subset_1(A_2),k1_zfmisc_1(A_2)) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_111,plain,(
    ! [A_2] : m1_subset_1(A_2,k1_zfmisc_1(A_2)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_4])).

tff(c_158,plain,(
    ! [A_78,B_79] :
      ( r1_tarski(A_78,B_79)
      | ~ m1_subset_1(A_78,k1_zfmisc_1(B_79)) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_174,plain,(
    ! [A_2] : r1_tarski(A_2,A_2) ),
    inference(resolution,[status(thm)],[c_111,c_158])).

tff(c_28,plain,(
    ! [B_24,A_23] :
      ( k5_relat_1(B_24,k6_relat_1(A_23)) = B_24
      | ~ r1_tarski(k2_relat_1(B_24),A_23)
      | ~ v1_relat_1(B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_596,plain,(
    ! [B_134,A_135] :
      ( k5_relat_1(B_134,k6_partfun1(A_135)) = B_134
      | ~ r1_tarski(k2_relat_1(B_134),A_135)
      | ~ v1_relat_1(B_134) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_28])).

tff(c_607,plain,(
    ! [B_134] :
      ( k5_relat_1(B_134,k6_partfun1(k2_relat_1(B_134))) = B_134
      | ~ v1_relat_1(B_134) ) ),
    inference(resolution,[status(thm)],[c_174,c_596])).

tff(c_962,plain,
    ( k5_relat_1('#skF_3',k6_partfun1('#skF_2')) = '#skF_3'
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_956,c_607])).

tff(c_969,plain,(
    k5_relat_1('#skF_3',k6_partfun1('#skF_2')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_205,c_962])).

tff(c_3548,plain,(
    k1_relat_1('#skF_4') = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_3532])).

tff(c_50,plain,(
    ! [A_33] :
      ( k5_relat_1(A_33,k2_funct_1(A_33)) = k6_relat_1(k1_relat_1(A_33))
      | ~ v2_funct_1(A_33)
      | ~ v1_funct_1(A_33)
      | ~ v1_relat_1(A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_103,plain,(
    ! [A_33] :
      ( k5_relat_1(A_33,k2_funct_1(A_33)) = k6_partfun1(k1_relat_1(A_33))
      | ~ v2_funct_1(A_33)
      | ~ v1_funct_1(A_33)
      | ~ v1_relat_1(A_33) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_50])).

tff(c_32,plain,(
    ! [A_25] :
      ( v1_relat_1(k2_funct_1(A_25))
      | ~ v1_funct_1(A_25)
      | ~ v1_relat_1(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_94,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_238])).

tff(c_100,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_238])).

tff(c_803,plain,(
    ! [A_152,B_153,D_154] :
      ( r2_relset_1(A_152,B_153,D_154,D_154)
      | ~ m1_subset_1(D_154,k1_zfmisc_1(k2_zfmisc_1(A_152,B_153))) ) ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_817,plain,(
    ! [A_54] : r2_relset_1(A_54,A_54,k6_partfun1(A_54),k6_partfun1(A_54)) ),
    inference(resolution,[status(thm)],[c_72,c_803])).

tff(c_954,plain,(
    k2_relset_1('#skF_2','#skF_1','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_92,c_933])).

tff(c_3549,plain,(
    ! [A_309,B_310,C_311,D_312] :
      ( k2_relset_1(A_309,B_310,C_311) = B_310
      | ~ r2_relset_1(B_310,B_310,k1_partfun1(B_310,A_309,A_309,B_310,D_312,C_311),k6_partfun1(B_310))
      | ~ m1_subset_1(D_312,k1_zfmisc_1(k2_zfmisc_1(B_310,A_309)))
      | ~ v1_funct_2(D_312,B_310,A_309)
      | ~ v1_funct_1(D_312)
      | ~ m1_subset_1(C_311,k1_zfmisc_1(k2_zfmisc_1(A_309,B_310)))
      | ~ v1_funct_2(C_311,A_309,B_310)
      | ~ v1_funct_1(C_311) ) ),
    inference(cnfTransformation,[status(thm)],[f_212])).

tff(c_3552,plain,
    ( k2_relset_1('#skF_2','#skF_1','#skF_4') = '#skF_1'
    | ~ r2_relset_1('#skF_1','#skF_1',k6_partfun1('#skF_1'),k6_partfun1('#skF_1'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_2871,c_3549])).

tff(c_3554,plain,(
    k2_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_94,c_92,c_102,c_100,c_98,c_817,c_954,c_3552])).

tff(c_48,plain,(
    ! [A_33] :
      ( k5_relat_1(k2_funct_1(A_33),A_33) = k6_relat_1(k2_relat_1(A_33))
      | ~ v2_funct_1(A_33)
      | ~ v1_funct_1(A_33)
      | ~ v1_relat_1(A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_104,plain,(
    ! [A_33] :
      ( k5_relat_1(k2_funct_1(A_33),A_33) = k6_partfun1(k2_relat_1(A_33))
      | ~ v2_funct_1(A_33)
      | ~ v1_funct_1(A_33)
      | ~ v1_relat_1(A_33) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_48])).

tff(c_3594,plain,(
    ! [A_9] :
      ( k1_relat_1(k5_relat_1(A_9,'#skF_4')) = k10_relat_1(A_9,'#skF_2')
      | ~ v1_relat_1('#skF_4')
      | ~ v1_relat_1(A_9) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3548,c_16])).

tff(c_5470,plain,(
    ! [A_349] :
      ( k1_relat_1(k5_relat_1(A_349,'#skF_4')) = k10_relat_1(A_349,'#skF_2')
      | ~ v1_relat_1(A_349) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_204,c_3594])).

tff(c_5547,plain,
    ( k1_relat_1(k6_partfun1(k2_relat_1('#skF_4'))) = k10_relat_1(k2_funct_1('#skF_4'),'#skF_2')
    | ~ v1_relat_1(k2_funct_1('#skF_4'))
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_104,c_5470])).

tff(c_5577,plain,
    ( k10_relat_1(k2_funct_1('#skF_4'),'#skF_2') = '#skF_1'
    | ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_204,c_96,c_3547,c_110,c_3554,c_5547])).

tff(c_5582,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_5577])).

tff(c_5660,plain,
    ( ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_32,c_5582])).

tff(c_5664,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_204,c_96,c_5660])).

tff(c_5666,plain,(
    v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_5577])).

tff(c_20,plain,(
    ! [A_14,B_18,C_20] :
      ( k5_relat_1(k5_relat_1(A_14,B_18),C_20) = k5_relat_1(A_14,k5_relat_1(B_18,C_20))
      | ~ v1_relat_1(C_20)
      | ~ v1_relat_1(B_18)
      | ~ v1_relat_1(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_3523,plain,(
    ! [C_20] :
      ( k5_relat_1(k6_partfun1('#skF_1'),C_20) = k5_relat_1('#skF_3',k5_relat_1('#skF_4',C_20))
      | ~ v1_relat_1(C_20)
      | ~ v1_relat_1('#skF_4')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3512,c_20])).

tff(c_6771,plain,(
    ! [C_383] :
      ( k5_relat_1(k6_partfun1('#skF_1'),C_383) = k5_relat_1('#skF_3',k5_relat_1('#skF_4',C_383))
      | ~ v1_relat_1(C_383) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_205,c_204,c_3523])).

tff(c_773,plain,(
    ! [A_151] :
      ( k1_relat_1(k2_funct_1(A_151)) = k2_relat_1(A_151)
      | ~ v2_funct_1(A_151)
      | ~ v1_funct_1(A_151)
      | ~ v1_relat_1(A_151) ) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_26,plain,(
    ! [A_22] :
      ( k5_relat_1(k6_relat_1(k1_relat_1(A_22)),A_22) = A_22
      | ~ v1_relat_1(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_108,plain,(
    ! [A_22] :
      ( k5_relat_1(k6_partfun1(k1_relat_1(A_22)),A_22) = A_22
      | ~ v1_relat_1(A_22) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_26])).

tff(c_4607,plain,(
    ! [A_334] :
      ( k5_relat_1(k6_partfun1(k2_relat_1(A_334)),k2_funct_1(A_334)) = k2_funct_1(A_334)
      | ~ v1_relat_1(k2_funct_1(A_334))
      | ~ v2_funct_1(A_334)
      | ~ v1_funct_1(A_334)
      | ~ v1_relat_1(A_334) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_773,c_108])).

tff(c_4647,plain,
    ( k5_relat_1(k6_partfun1('#skF_1'),k2_funct_1('#skF_4')) = k2_funct_1('#skF_4')
    | ~ v1_relat_1(k2_funct_1('#skF_4'))
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_3554,c_4607])).

tff(c_4680,plain,
    ( k5_relat_1(k6_partfun1('#skF_1'),k2_funct_1('#skF_4')) = k2_funct_1('#skF_4')
    | ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_204,c_96,c_3547,c_4647])).

tff(c_5928,plain,(
    k5_relat_1(k6_partfun1('#skF_1'),k2_funct_1('#skF_4')) = k2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5666,c_4680])).

tff(c_6802,plain,
    ( k5_relat_1('#skF_3',k5_relat_1('#skF_4',k2_funct_1('#skF_4'))) = k2_funct_1('#skF_4')
    | ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_6771,c_5928])).

tff(c_6917,plain,(
    k5_relat_1('#skF_3',k5_relat_1('#skF_4',k2_funct_1('#skF_4'))) = k2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5666,c_6802])).

tff(c_7020,plain,
    ( k5_relat_1('#skF_3',k6_partfun1(k1_relat_1('#skF_4'))) = k2_funct_1('#skF_4')
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_103,c_6917])).

tff(c_7033,plain,(
    k2_funct_1('#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_204,c_96,c_3547,c_969,c_3548,c_7020])).

tff(c_52,plain,(
    ! [A_34] :
      ( k2_funct_1(k2_funct_1(A_34)) = A_34
      | ~ v2_funct_1(A_34)
      | ~ v1_funct_1(A_34)
      | ~ v1_relat_1(A_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_7093,plain,
    ( k2_funct_1('#skF_3') = '#skF_4'
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_7033,c_52])).

tff(c_7125,plain,(
    k2_funct_1('#skF_3') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_204,c_96,c_3547,c_7093])).

tff(c_7127,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_7125])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:51:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.61/2.77  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.61/2.78  
% 7.61/2.78  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.61/2.79  %$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k9_relat_1 > k7_relat_1 > k5_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_subset_1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 7.61/2.79  
% 7.61/2.79  %Foreground sorts:
% 7.61/2.79  
% 7.61/2.79  
% 7.61/2.79  %Background operators:
% 7.61/2.79  
% 7.61/2.79  
% 7.61/2.79  %Foreground operators:
% 7.61/2.79  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 7.61/2.79  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 7.61/2.79  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 7.61/2.79  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 7.61/2.79  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.61/2.79  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 7.61/2.79  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 7.61/2.79  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 7.61/2.79  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 7.61/2.79  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.61/2.79  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 7.61/2.79  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 7.61/2.79  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 7.61/2.79  tff('#skF_2', type, '#skF_2': $i).
% 7.61/2.79  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 7.61/2.79  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 7.61/2.79  tff('#skF_3', type, '#skF_3': $i).
% 7.61/2.79  tff('#skF_1', type, '#skF_1': $i).
% 7.61/2.79  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 7.61/2.79  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 7.61/2.79  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 7.61/2.79  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.61/2.79  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 7.61/2.79  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 7.61/2.79  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 7.61/2.79  tff('#skF_4', type, '#skF_4': $i).
% 7.61/2.79  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 7.61/2.79  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.61/2.79  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 7.61/2.79  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 7.61/2.79  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 7.61/2.79  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 7.61/2.79  
% 7.61/2.81  tff(f_238, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => ((((k2_relset_1(A, B, C) = B) & r2_relset_1(A, A, k1_partfun1(A, B, B, A, C, D), k6_partfun1(A))) & v2_funct_1(C)) => (((A = k1_xboole_0) | (B = k1_xboole_0)) | (D = k2_funct_1(C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_funct_2)).
% 7.61/2.81  tff(f_149, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 7.61/2.81  tff(f_155, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 7.61/2.81  tff(f_39, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d18_relat_1)).
% 7.61/2.81  tff(f_195, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 7.61/2.81  tff(f_92, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v2_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc4_funct_1)).
% 7.61/2.81  tff(f_159, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 7.61/2.81  tff(f_179, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (v1_funct_1(k1_partfun1(A, B, C, D, E, F)) & m1_subset_1(k1_partfun1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 7.61/2.81  tff(f_183, axiom, (![A]: (v1_partfun1(k6_partfun1(A), A) & m1_subset_1(k6_partfun1(A), k1_zfmisc_1(k2_zfmisc_1(A, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_partfun1)).
% 7.61/2.81  tff(f_167, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 7.61/2.81  tff(f_193, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 7.61/2.81  tff(f_117, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((v2_funct_1(k5_relat_1(B, A)) & (k2_relat_1(B) = k1_relat_1(A))) => (v2_funct_1(B) & v2_funct_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_funct_1)).
% 7.61/2.81  tff(f_56, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t209_relat_1)).
% 7.61/2.81  tff(f_43, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_relat_1)).
% 7.61/2.81  tff(f_70, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 7.61/2.81  tff(f_50, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k1_relat_1(k5_relat_1(A, B)) = k10_relat_1(A, k1_relat_1(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t182_relat_1)).
% 7.61/2.81  tff(f_100, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r1_tarski(A, k2_relat_1(B)) => (k9_relat_1(B, k10_relat_1(B, A)) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t147_funct_1)).
% 7.61/2.81  tff(f_27, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 7.61/2.81  tff(f_29, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 7.61/2.81  tff(f_33, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 7.61/2.81  tff(f_80, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(B), A) => (k5_relat_1(B, k6_relat_1(A)) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_relat_1)).
% 7.61/2.81  tff(f_137, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k5_relat_1(A, k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))) & (k5_relat_1(k2_funct_1(A), A) = k6_relat_1(k2_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t61_funct_1)).
% 7.61/2.81  tff(f_88, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 7.61/2.81  tff(f_212, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (r2_relset_1(B, B, k1_partfun1(B, A, A, B, D, C), k6_partfun1(B)) => (k2_relset_1(A, B, C) = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t24_funct_2)).
% 7.61/2.81  tff(f_66, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (k5_relat_1(k5_relat_1(A, B), C) = k5_relat_1(A, k5_relat_1(B, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_relat_1)).
% 7.61/2.81  tff(f_127, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k2_relat_1(A) = k1_relat_1(k2_funct_1(A))) & (k1_relat_1(A) = k2_relat_1(k2_funct_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_funct_1)).
% 7.61/2.81  tff(f_74, axiom, (![A]: (v1_relat_1(A) => (k5_relat_1(k6_relat_1(k1_relat_1(A)), A) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t78_relat_1)).
% 7.61/2.81  tff(f_145, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => (k2_funct_1(k2_funct_1(A)) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_funct_1)).
% 7.61/2.81  tff(c_80, plain, (k2_funct_1('#skF_3')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_238])).
% 7.61/2.81  tff(c_92, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_238])).
% 7.61/2.81  tff(c_183, plain, (![C_85, A_86, B_87]: (v1_relat_1(C_85) | ~m1_subset_1(C_85, k1_zfmisc_1(k2_zfmisc_1(A_86, B_87))))), inference(cnfTransformation, [status(thm)], [f_149])).
% 7.61/2.81  tff(c_204, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_92, c_183])).
% 7.61/2.81  tff(c_96, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_238])).
% 7.61/2.81  tff(c_362, plain, (![C_112, A_113, B_114]: (v4_relat_1(C_112, A_113) | ~m1_subset_1(C_112, k1_zfmisc_1(k2_zfmisc_1(A_113, B_114))))), inference(cnfTransformation, [status(thm)], [f_155])).
% 7.61/2.81  tff(c_383, plain, (v4_relat_1('#skF_4', '#skF_2')), inference(resolution, [status(thm)], [c_92, c_362])).
% 7.61/2.81  tff(c_12, plain, (![B_6, A_5]: (r1_tarski(k1_relat_1(B_6), A_5) | ~v4_relat_1(B_6, A_5) | ~v1_relat_1(B_6))), inference(cnfTransformation, [status(thm)], [f_39])).
% 7.61/2.81  tff(c_98, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_238])).
% 7.61/2.81  tff(c_205, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_98, c_183])).
% 7.61/2.81  tff(c_102, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_238])).
% 7.61/2.81  tff(c_76, plain, (![A_61]: (k6_relat_1(A_61)=k6_partfun1(A_61))), inference(cnfTransformation, [status(thm)], [f_195])).
% 7.61/2.81  tff(c_36, plain, (![A_26]: (v2_funct_1(k6_relat_1(A_26)))), inference(cnfTransformation, [status(thm)], [f_92])).
% 7.61/2.81  tff(c_105, plain, (![A_26]: (v2_funct_1(k6_partfun1(A_26)))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_36])).
% 7.61/2.81  tff(c_90, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_2'), inference(cnfTransformation, [status(thm)], [f_238])).
% 7.61/2.81  tff(c_933, plain, (![A_166, B_167, C_168]: (k2_relset_1(A_166, B_167, C_168)=k2_relat_1(C_168) | ~m1_subset_1(C_168, k1_zfmisc_1(k2_zfmisc_1(A_166, B_167))))), inference(cnfTransformation, [status(thm)], [f_159])).
% 7.61/2.81  tff(c_946, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_98, c_933])).
% 7.61/2.81  tff(c_956, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_90, c_946])).
% 7.61/2.81  tff(c_2832, plain, (![A_268, B_267, F_265, E_270, D_266, C_269]: (m1_subset_1(k1_partfun1(A_268, B_267, C_269, D_266, E_270, F_265), k1_zfmisc_1(k2_zfmisc_1(A_268, D_266))) | ~m1_subset_1(F_265, k1_zfmisc_1(k2_zfmisc_1(C_269, D_266))) | ~v1_funct_1(F_265) | ~m1_subset_1(E_270, k1_zfmisc_1(k2_zfmisc_1(A_268, B_267))) | ~v1_funct_1(E_270))), inference(cnfTransformation, [status(thm)], [f_179])).
% 7.61/2.81  tff(c_72, plain, (![A_54]: (m1_subset_1(k6_partfun1(A_54), k1_zfmisc_1(k2_zfmisc_1(A_54, A_54))))), inference(cnfTransformation, [status(thm)], [f_183])).
% 7.61/2.81  tff(c_88, plain, (r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k6_partfun1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_238])).
% 7.61/2.81  tff(c_2365, plain, (![D_233, C_234, A_235, B_236]: (D_233=C_234 | ~r2_relset_1(A_235, B_236, C_234, D_233) | ~m1_subset_1(D_233, k1_zfmisc_1(k2_zfmisc_1(A_235, B_236))) | ~m1_subset_1(C_234, k1_zfmisc_1(k2_zfmisc_1(A_235, B_236))))), inference(cnfTransformation, [status(thm)], [f_167])).
% 7.61/2.81  tff(c_2375, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_88, c_2365])).
% 7.61/2.81  tff(c_2394, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_2375])).
% 7.61/2.81  tff(c_2498, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_2394])).
% 7.61/2.81  tff(c_2845, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_2832, c_2498])).
% 7.61/2.81  tff(c_2870, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_102, c_98, c_96, c_92, c_2845])).
% 7.61/2.81  tff(c_2871, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_2394])).
% 7.61/2.81  tff(c_3211, plain, (![A_290, D_289, F_292, E_293, B_288, C_291]: (k1_partfun1(A_290, B_288, C_291, D_289, E_293, F_292)=k5_relat_1(E_293, F_292) | ~m1_subset_1(F_292, k1_zfmisc_1(k2_zfmisc_1(C_291, D_289))) | ~v1_funct_1(F_292) | ~m1_subset_1(E_293, k1_zfmisc_1(k2_zfmisc_1(A_290, B_288))) | ~v1_funct_1(E_293))), inference(cnfTransformation, [status(thm)], [f_193])).
% 7.61/2.81  tff(c_3218, plain, (![A_290, B_288, E_293]: (k1_partfun1(A_290, B_288, '#skF_2', '#skF_1', E_293, '#skF_4')=k5_relat_1(E_293, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_293, k1_zfmisc_1(k2_zfmisc_1(A_290, B_288))) | ~v1_funct_1(E_293))), inference(resolution, [status(thm)], [c_92, c_3211])).
% 7.61/2.81  tff(c_3483, plain, (![A_306, B_307, E_308]: (k1_partfun1(A_306, B_307, '#skF_2', '#skF_1', E_308, '#skF_4')=k5_relat_1(E_308, '#skF_4') | ~m1_subset_1(E_308, k1_zfmisc_1(k2_zfmisc_1(A_306, B_307))) | ~v1_funct_1(E_308))), inference(demodulation, [status(thm), theory('equality')], [c_96, c_3218])).
% 7.61/2.81  tff(c_3499, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_98, c_3483])).
% 7.61/2.81  tff(c_3512, plain, (k5_relat_1('#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_102, c_2871, c_3499])).
% 7.61/2.81  tff(c_40, plain, (![A_29, B_31]: (v2_funct_1(A_29) | k2_relat_1(B_31)!=k1_relat_1(A_29) | ~v2_funct_1(k5_relat_1(B_31, A_29)) | ~v1_funct_1(B_31) | ~v1_relat_1(B_31) | ~v1_funct_1(A_29) | ~v1_relat_1(A_29))), inference(cnfTransformation, [status(thm)], [f_117])).
% 7.61/2.81  tff(c_3520, plain, (v2_funct_1('#skF_4') | k2_relat_1('#skF_3')!=k1_relat_1('#skF_4') | ~v2_funct_1(k6_partfun1('#skF_1')) | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_3512, c_40])).
% 7.61/2.81  tff(c_3532, plain, (v2_funct_1('#skF_4') | k1_relat_1('#skF_4')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_204, c_96, c_205, c_102, c_105, c_956, c_3520])).
% 7.61/2.81  tff(c_3538, plain, (k1_relat_1('#skF_4')!='#skF_2'), inference(splitLeft, [status(thm)], [c_3532])).
% 7.61/2.81  tff(c_384, plain, (v4_relat_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_98, c_362])).
% 7.61/2.81  tff(c_18, plain, (![B_13, A_12]: (k7_relat_1(B_13, A_12)=B_13 | ~v4_relat_1(B_13, A_12) | ~v1_relat_1(B_13))), inference(cnfTransformation, [status(thm)], [f_56])).
% 7.61/2.81  tff(c_394, plain, (k7_relat_1('#skF_3', '#skF_1')='#skF_3' | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_384, c_18])).
% 7.61/2.81  tff(c_397, plain, (k7_relat_1('#skF_3', '#skF_1')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_205, c_394])).
% 7.61/2.81  tff(c_14, plain, (![B_8, A_7]: (k2_relat_1(k7_relat_1(B_8, A_7))=k9_relat_1(B_8, A_7) | ~v1_relat_1(B_8))), inference(cnfTransformation, [status(thm)], [f_43])).
% 7.61/2.81  tff(c_410, plain, (k9_relat_1('#skF_3', '#skF_1')=k2_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_397, c_14])).
% 7.61/2.81  tff(c_414, plain, (k9_relat_1('#skF_3', '#skF_1')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_205, c_410])).
% 7.61/2.81  tff(c_958, plain, (k9_relat_1('#skF_3', '#skF_1')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_956, c_414])).
% 7.61/2.81  tff(c_22, plain, (![A_21]: (k1_relat_1(k6_relat_1(A_21))=A_21)), inference(cnfTransformation, [status(thm)], [f_70])).
% 7.61/2.81  tff(c_110, plain, (![A_21]: (k1_relat_1(k6_partfun1(A_21))=A_21)), inference(demodulation, [status(thm), theory('equality')], [c_76, c_22])).
% 7.61/2.81  tff(c_16, plain, (![A_9, B_11]: (k10_relat_1(A_9, k1_relat_1(B_11))=k1_relat_1(k5_relat_1(A_9, B_11)) | ~v1_relat_1(B_11) | ~v1_relat_1(A_9))), inference(cnfTransformation, [status(thm)], [f_50])).
% 7.61/2.81  tff(c_1174, plain, (![B_178, A_179]: (k9_relat_1(B_178, k10_relat_1(B_178, A_179))=A_179 | ~r1_tarski(A_179, k2_relat_1(B_178)) | ~v1_funct_1(B_178) | ~v1_relat_1(B_178))), inference(cnfTransformation, [status(thm)], [f_100])).
% 7.61/2.81  tff(c_1176, plain, (![A_179]: (k9_relat_1('#skF_3', k10_relat_1('#skF_3', A_179))=A_179 | ~r1_tarski(A_179, '#skF_2') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_956, c_1174])).
% 7.61/2.81  tff(c_1195, plain, (![A_180]: (k9_relat_1('#skF_3', k10_relat_1('#skF_3', A_180))=A_180 | ~r1_tarski(A_180, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_205, c_102, c_1176])).
% 7.61/2.81  tff(c_1208, plain, (![B_11]: (k9_relat_1('#skF_3', k1_relat_1(k5_relat_1('#skF_3', B_11)))=k1_relat_1(B_11) | ~r1_tarski(k1_relat_1(B_11), '#skF_2') | ~v1_relat_1(B_11) | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_16, c_1195])).
% 7.61/2.81  tff(c_1214, plain, (![B_11]: (k9_relat_1('#skF_3', k1_relat_1(k5_relat_1('#skF_3', B_11)))=k1_relat_1(B_11) | ~r1_tarski(k1_relat_1(B_11), '#skF_2') | ~v1_relat_1(B_11))), inference(demodulation, [status(thm), theory('equality')], [c_205, c_1208])).
% 7.61/2.81  tff(c_3526, plain, (k9_relat_1('#skF_3', k1_relat_1(k6_partfun1('#skF_1')))=k1_relat_1('#skF_4') | ~r1_tarski(k1_relat_1('#skF_4'), '#skF_2') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_3512, c_1214])).
% 7.61/2.81  tff(c_3536, plain, (k1_relat_1('#skF_4')='#skF_2' | ~r1_tarski(k1_relat_1('#skF_4'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_204, c_958, c_110, c_3526])).
% 7.61/2.81  tff(c_3539, plain, (~r1_tarski(k1_relat_1('#skF_4'), '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_3538, c_3536])).
% 7.61/2.81  tff(c_3542, plain, (~v4_relat_1('#skF_4', '#skF_2') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_12, c_3539])).
% 7.61/2.81  tff(c_3546, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_204, c_383, c_3542])).
% 7.61/2.81  tff(c_3547, plain, (v2_funct_1('#skF_4')), inference(splitRight, [status(thm)], [c_3532])).
% 7.61/2.81  tff(c_2, plain, (![A_1]: (k2_subset_1(A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 7.61/2.81  tff(c_4, plain, (![A_2]: (m1_subset_1(k2_subset_1(A_2), k1_zfmisc_1(A_2)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 7.61/2.81  tff(c_111, plain, (![A_2]: (m1_subset_1(A_2, k1_zfmisc_1(A_2)))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_4])).
% 7.61/2.81  tff(c_158, plain, (![A_78, B_79]: (r1_tarski(A_78, B_79) | ~m1_subset_1(A_78, k1_zfmisc_1(B_79)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 7.61/2.81  tff(c_174, plain, (![A_2]: (r1_tarski(A_2, A_2))), inference(resolution, [status(thm)], [c_111, c_158])).
% 7.61/2.81  tff(c_28, plain, (![B_24, A_23]: (k5_relat_1(B_24, k6_relat_1(A_23))=B_24 | ~r1_tarski(k2_relat_1(B_24), A_23) | ~v1_relat_1(B_24))), inference(cnfTransformation, [status(thm)], [f_80])).
% 7.61/2.81  tff(c_596, plain, (![B_134, A_135]: (k5_relat_1(B_134, k6_partfun1(A_135))=B_134 | ~r1_tarski(k2_relat_1(B_134), A_135) | ~v1_relat_1(B_134))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_28])).
% 7.61/2.81  tff(c_607, plain, (![B_134]: (k5_relat_1(B_134, k6_partfun1(k2_relat_1(B_134)))=B_134 | ~v1_relat_1(B_134))), inference(resolution, [status(thm)], [c_174, c_596])).
% 7.61/2.81  tff(c_962, plain, (k5_relat_1('#skF_3', k6_partfun1('#skF_2'))='#skF_3' | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_956, c_607])).
% 7.61/2.81  tff(c_969, plain, (k5_relat_1('#skF_3', k6_partfun1('#skF_2'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_205, c_962])).
% 7.61/2.81  tff(c_3548, plain, (k1_relat_1('#skF_4')='#skF_2'), inference(splitRight, [status(thm)], [c_3532])).
% 7.61/2.81  tff(c_50, plain, (![A_33]: (k5_relat_1(A_33, k2_funct_1(A_33))=k6_relat_1(k1_relat_1(A_33)) | ~v2_funct_1(A_33) | ~v1_funct_1(A_33) | ~v1_relat_1(A_33))), inference(cnfTransformation, [status(thm)], [f_137])).
% 7.61/2.81  tff(c_103, plain, (![A_33]: (k5_relat_1(A_33, k2_funct_1(A_33))=k6_partfun1(k1_relat_1(A_33)) | ~v2_funct_1(A_33) | ~v1_funct_1(A_33) | ~v1_relat_1(A_33))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_50])).
% 7.61/2.81  tff(c_32, plain, (![A_25]: (v1_relat_1(k2_funct_1(A_25)) | ~v1_funct_1(A_25) | ~v1_relat_1(A_25))), inference(cnfTransformation, [status(thm)], [f_88])).
% 7.61/2.81  tff(c_94, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_238])).
% 7.61/2.81  tff(c_100, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_238])).
% 7.61/2.81  tff(c_803, plain, (![A_152, B_153, D_154]: (r2_relset_1(A_152, B_153, D_154, D_154) | ~m1_subset_1(D_154, k1_zfmisc_1(k2_zfmisc_1(A_152, B_153))))), inference(cnfTransformation, [status(thm)], [f_167])).
% 7.61/2.81  tff(c_817, plain, (![A_54]: (r2_relset_1(A_54, A_54, k6_partfun1(A_54), k6_partfun1(A_54)))), inference(resolution, [status(thm)], [c_72, c_803])).
% 7.61/2.81  tff(c_954, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_92, c_933])).
% 7.61/2.81  tff(c_3549, plain, (![A_309, B_310, C_311, D_312]: (k2_relset_1(A_309, B_310, C_311)=B_310 | ~r2_relset_1(B_310, B_310, k1_partfun1(B_310, A_309, A_309, B_310, D_312, C_311), k6_partfun1(B_310)) | ~m1_subset_1(D_312, k1_zfmisc_1(k2_zfmisc_1(B_310, A_309))) | ~v1_funct_2(D_312, B_310, A_309) | ~v1_funct_1(D_312) | ~m1_subset_1(C_311, k1_zfmisc_1(k2_zfmisc_1(A_309, B_310))) | ~v1_funct_2(C_311, A_309, B_310) | ~v1_funct_1(C_311))), inference(cnfTransformation, [status(thm)], [f_212])).
% 7.61/2.81  tff(c_3552, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')='#skF_1' | ~r2_relset_1('#skF_1', '#skF_1', k6_partfun1('#skF_1'), k6_partfun1('#skF_1')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_2871, c_3549])).
% 7.61/2.81  tff(c_3554, plain, (k2_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_96, c_94, c_92, c_102, c_100, c_98, c_817, c_954, c_3552])).
% 7.61/2.81  tff(c_48, plain, (![A_33]: (k5_relat_1(k2_funct_1(A_33), A_33)=k6_relat_1(k2_relat_1(A_33)) | ~v2_funct_1(A_33) | ~v1_funct_1(A_33) | ~v1_relat_1(A_33))), inference(cnfTransformation, [status(thm)], [f_137])).
% 7.61/2.81  tff(c_104, plain, (![A_33]: (k5_relat_1(k2_funct_1(A_33), A_33)=k6_partfun1(k2_relat_1(A_33)) | ~v2_funct_1(A_33) | ~v1_funct_1(A_33) | ~v1_relat_1(A_33))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_48])).
% 7.61/2.81  tff(c_3594, plain, (![A_9]: (k1_relat_1(k5_relat_1(A_9, '#skF_4'))=k10_relat_1(A_9, '#skF_2') | ~v1_relat_1('#skF_4') | ~v1_relat_1(A_9))), inference(superposition, [status(thm), theory('equality')], [c_3548, c_16])).
% 7.61/2.81  tff(c_5470, plain, (![A_349]: (k1_relat_1(k5_relat_1(A_349, '#skF_4'))=k10_relat_1(A_349, '#skF_2') | ~v1_relat_1(A_349))), inference(demodulation, [status(thm), theory('equality')], [c_204, c_3594])).
% 7.61/2.81  tff(c_5547, plain, (k1_relat_1(k6_partfun1(k2_relat_1('#skF_4')))=k10_relat_1(k2_funct_1('#skF_4'), '#skF_2') | ~v1_relat_1(k2_funct_1('#skF_4')) | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_104, c_5470])).
% 7.61/2.81  tff(c_5577, plain, (k10_relat_1(k2_funct_1('#skF_4'), '#skF_2')='#skF_1' | ~v1_relat_1(k2_funct_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_204, c_96, c_3547, c_110, c_3554, c_5547])).
% 7.61/2.81  tff(c_5582, plain, (~v1_relat_1(k2_funct_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_5577])).
% 7.61/2.81  tff(c_5660, plain, (~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_32, c_5582])).
% 7.61/2.81  tff(c_5664, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_204, c_96, c_5660])).
% 7.61/2.81  tff(c_5666, plain, (v1_relat_1(k2_funct_1('#skF_4'))), inference(splitRight, [status(thm)], [c_5577])).
% 7.61/2.81  tff(c_20, plain, (![A_14, B_18, C_20]: (k5_relat_1(k5_relat_1(A_14, B_18), C_20)=k5_relat_1(A_14, k5_relat_1(B_18, C_20)) | ~v1_relat_1(C_20) | ~v1_relat_1(B_18) | ~v1_relat_1(A_14))), inference(cnfTransformation, [status(thm)], [f_66])).
% 7.61/2.81  tff(c_3523, plain, (![C_20]: (k5_relat_1(k6_partfun1('#skF_1'), C_20)=k5_relat_1('#skF_3', k5_relat_1('#skF_4', C_20)) | ~v1_relat_1(C_20) | ~v1_relat_1('#skF_4') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_3512, c_20])).
% 7.61/2.81  tff(c_6771, plain, (![C_383]: (k5_relat_1(k6_partfun1('#skF_1'), C_383)=k5_relat_1('#skF_3', k5_relat_1('#skF_4', C_383)) | ~v1_relat_1(C_383))), inference(demodulation, [status(thm), theory('equality')], [c_205, c_204, c_3523])).
% 7.61/2.81  tff(c_773, plain, (![A_151]: (k1_relat_1(k2_funct_1(A_151))=k2_relat_1(A_151) | ~v2_funct_1(A_151) | ~v1_funct_1(A_151) | ~v1_relat_1(A_151))), inference(cnfTransformation, [status(thm)], [f_127])).
% 7.61/2.81  tff(c_26, plain, (![A_22]: (k5_relat_1(k6_relat_1(k1_relat_1(A_22)), A_22)=A_22 | ~v1_relat_1(A_22))), inference(cnfTransformation, [status(thm)], [f_74])).
% 7.61/2.81  tff(c_108, plain, (![A_22]: (k5_relat_1(k6_partfun1(k1_relat_1(A_22)), A_22)=A_22 | ~v1_relat_1(A_22))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_26])).
% 7.61/2.81  tff(c_4607, plain, (![A_334]: (k5_relat_1(k6_partfun1(k2_relat_1(A_334)), k2_funct_1(A_334))=k2_funct_1(A_334) | ~v1_relat_1(k2_funct_1(A_334)) | ~v2_funct_1(A_334) | ~v1_funct_1(A_334) | ~v1_relat_1(A_334))), inference(superposition, [status(thm), theory('equality')], [c_773, c_108])).
% 7.61/2.81  tff(c_4647, plain, (k5_relat_1(k6_partfun1('#skF_1'), k2_funct_1('#skF_4'))=k2_funct_1('#skF_4') | ~v1_relat_1(k2_funct_1('#skF_4')) | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_3554, c_4607])).
% 7.61/2.81  tff(c_4680, plain, (k5_relat_1(k6_partfun1('#skF_1'), k2_funct_1('#skF_4'))=k2_funct_1('#skF_4') | ~v1_relat_1(k2_funct_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_204, c_96, c_3547, c_4647])).
% 7.61/2.81  tff(c_5928, plain, (k5_relat_1(k6_partfun1('#skF_1'), k2_funct_1('#skF_4'))=k2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_5666, c_4680])).
% 7.61/2.81  tff(c_6802, plain, (k5_relat_1('#skF_3', k5_relat_1('#skF_4', k2_funct_1('#skF_4')))=k2_funct_1('#skF_4') | ~v1_relat_1(k2_funct_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_6771, c_5928])).
% 7.61/2.81  tff(c_6917, plain, (k5_relat_1('#skF_3', k5_relat_1('#skF_4', k2_funct_1('#skF_4')))=k2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_5666, c_6802])).
% 7.61/2.81  tff(c_7020, plain, (k5_relat_1('#skF_3', k6_partfun1(k1_relat_1('#skF_4')))=k2_funct_1('#skF_4') | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_103, c_6917])).
% 7.61/2.81  tff(c_7033, plain, (k2_funct_1('#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_204, c_96, c_3547, c_969, c_3548, c_7020])).
% 7.61/2.81  tff(c_52, plain, (![A_34]: (k2_funct_1(k2_funct_1(A_34))=A_34 | ~v2_funct_1(A_34) | ~v1_funct_1(A_34) | ~v1_relat_1(A_34))), inference(cnfTransformation, [status(thm)], [f_145])).
% 7.61/2.81  tff(c_7093, plain, (k2_funct_1('#skF_3')='#skF_4' | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_7033, c_52])).
% 7.61/2.81  tff(c_7125, plain, (k2_funct_1('#skF_3')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_204, c_96, c_3547, c_7093])).
% 7.61/2.81  tff(c_7127, plain, $false, inference(negUnitSimplification, [status(thm)], [c_80, c_7125])).
% 7.61/2.81  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.61/2.81  
% 7.61/2.81  Inference rules
% 7.61/2.81  ----------------------
% 7.61/2.81  #Ref     : 0
% 7.61/2.81  #Sup     : 1473
% 7.61/2.81  #Fact    : 0
% 7.61/2.81  #Define  : 0
% 7.61/2.81  #Split   : 14
% 7.61/2.81  #Chain   : 0
% 7.61/2.81  #Close   : 0
% 7.61/2.81  
% 7.61/2.81  Ordering : KBO
% 7.61/2.81  
% 7.61/2.81  Simplification rules
% 7.61/2.81  ----------------------
% 7.61/2.81  #Subsume      : 73
% 7.61/2.81  #Demod        : 2479
% 7.61/2.81  #Tautology    : 767
% 7.61/2.81  #SimpNegUnit  : 2
% 7.61/2.81  #BackRed      : 38
% 7.61/2.81  
% 7.61/2.81  #Partial instantiations: 0
% 7.61/2.81  #Strategies tried      : 1
% 7.61/2.81  
% 7.61/2.81  Timing (in seconds)
% 7.61/2.81  ----------------------
% 7.61/2.81  Preprocessing        : 0.39
% 7.61/2.81  Parsing              : 0.20
% 7.61/2.81  CNF conversion       : 0.03
% 7.61/2.81  Main loop            : 1.51
% 7.61/2.81  Inferencing          : 0.45
% 7.61/2.81  Reduction            : 0.64
% 7.61/2.81  Demodulation         : 0.49
% 7.61/2.81  BG Simplification    : 0.05
% 7.61/2.81  Subsumption          : 0.26
% 7.61/2.81  Abstraction          : 0.06
% 7.61/2.81  MUC search           : 0.00
% 7.61/2.81  Cooper               : 0.00
% 7.61/2.81  Total                : 1.95
% 7.61/2.81  Index Insertion      : 0.00
% 7.61/2.81  Index Deletion       : 0.00
% 7.61/2.81  Index Matching       : 0.00
% 7.61/2.81  BG Taut test         : 0.00
%------------------------------------------------------------------------------
