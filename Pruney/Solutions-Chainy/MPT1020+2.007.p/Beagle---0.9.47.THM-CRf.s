%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:15:51 EST 2020

% Result     : Theorem 14.58s
% Output     : CNFRefutation 14.87s
% Verified   : 
% Statistics : Number of formulae       :  371 (4033 expanded)
%              Number of leaves         :   73 (1341 expanded)
%              Depth                    :   17
%              Number of atoms          :  680 (10694 expanded)
%              Number of equality atoms :  196 (1740 expanded)
%              Maximal formula depth    :   12 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v3_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > v1_partfun1 > r2_xboole_0 > r2_hidden > r1_tarski > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k8_relset_1 > k7_relset_1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k7_relat_1 > k5_relat_1 > k2_zfmisc_1 > k2_funct_2 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1

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

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k8_relset_1,type,(
    k8_relset_1: ( $i * $i * $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(k2_funct_2,type,(
    k2_funct_2: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k7_relset_1,type,(
    k7_relset_1: ( $i * $i * $i * $i ) > $i )).

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

tff(v2_funct_2,type,(
    v2_funct_2: ( $i * $i ) > $o )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(r2_xboole_0,type,(
    r2_xboole_0: ( $i * $i ) > $o )).

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

tff(v3_funct_2,type,(
    v3_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_76,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_292,negated_conjecture,(
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

tff(f_70,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_148,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_174,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( ( v1_funct_1(C)
          & v3_funct_2(C,A,B) )
       => ( v1_funct_1(C)
          & v2_funct_1(C)
          & v2_funct_2(C,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_funct_2)).

tff(f_252,axiom,(
    ! [A,B] :
      ( ( v1_funct_1(B)
        & v1_funct_2(B,A,A)
        & v3_funct_2(B,A,A)
        & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
     => k2_funct_2(A,B) = k2_funct_1(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_funct_2)).

tff(f_228,axiom,(
    ! [A,B] :
      ( ( v1_funct_1(B)
        & v1_funct_2(B,A,A)
        & v3_funct_2(B,A,A)
        & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
     => ( v1_funct_1(k2_funct_2(A,B))
        & v1_funct_2(k2_funct_2(A,B),A,A)
        & v3_funct_2(k2_funct_2(A,B),A,A)
        & m1_subset_1(k2_funct_2(A,B),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_2)).

tff(f_126,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_132,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_200,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A) )
     => ( v2_funct_2(B,A)
      <=> k2_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_funct_2)).

tff(f_254,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_112,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k5_relat_1(A,k6_relat_1(k2_relat_1(A))) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t80_relat_1)).

tff(f_104,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ( k1_relat_1(A) = k1_xboole_0
          | k2_relat_1(A) = k1_xboole_0 )
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).

tff(f_86,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_80,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_140,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_156,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( k7_relset_1(A,B,C,A) = k2_relset_1(A,B,C)
        & k8_relset_1(A,B,C,B) = k1_relset_1(A,B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_relset_1)).

tff(f_270,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( ( k2_relset_1(A,B,C) = B
          & v2_funct_1(C) )
       => ( B = k1_xboole_0
          | ( k5_relat_1(C,k2_funct_1(C)) = k6_partfun1(A)
            & k5_relat_1(k2_funct_1(C),C) = k6_partfun1(B) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_funct_2)).

tff(f_212,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( v1_funct_1(k1_partfun1(A,B,C,D,E,F))
        & m1_subset_1(k1_partfun1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).

tff(f_232,axiom,(
    ! [A] :
      ( v1_partfun1(k6_partfun1(A),A)
      & m1_subset_1(k6_partfun1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).

tff(f_242,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_96,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ! [C] :
              ( v1_relat_1(C)
             => k5_relat_1(k5_relat_1(A,B),C) = k5_relat_1(A,k5_relat_1(B,C)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_relat_1)).

tff(f_192,axiom,(
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

tff(f_136,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_108,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k5_relat_1(k6_relat_1(k1_relat_1(A)),A) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t78_relat_1)).

tff(f_120,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => k2_funct_1(k2_funct_1(A)) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_funct_1)).

tff(f_33,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_52,axiom,(
    ! [A,B] :
      ( v1_xboole_0(B)
     => v1_xboole_0(k2_zfmisc_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_zfmisc_1)).

tff(f_56,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r2_xboole_0(A,B)
    <=> ( r1_tarski(A,B)
        & A != B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_xboole_0)).

tff(f_43,axiom,(
    ! [A,B] :
      ~ ( r2_xboole_0(A,B)
        & ! [C] :
            ~ ( r2_hidden(C,B)
              & ~ r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_xboole_0)).

tff(f_48,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_boole)).

tff(f_150,axiom,(
    ! [A] : r1_tarski(k6_relat_1(A),k2_zfmisc_1(A,A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_relset_1)).

tff(f_122,axiom,(
    ! [A] : k2_funct_1(k6_relat_1(A)) = k6_relat_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_funct_1)).

tff(c_28,plain,(
    ! [A_19,B_20] : v1_relat_1(k2_zfmisc_1(A_19,B_20)) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_124,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_292])).

tff(c_205,plain,(
    ! [B_116,A_117] :
      ( v1_relat_1(B_116)
      | ~ m1_subset_1(B_116,k1_zfmisc_1(A_117))
      | ~ v1_relat_1(A_117) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_214,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_2')) ),
    inference(resolution,[status(thm)],[c_124,c_205])).

tff(c_224,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_214])).

tff(c_602,plain,(
    ! [A_180,B_181,D_182] :
      ( r2_relset_1(A_180,B_181,D_182,D_182)
      | ~ m1_subset_1(D_182,k1_zfmisc_1(k2_zfmisc_1(A_180,B_181))) ) ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_614,plain,(
    r2_relset_1('#skF_2','#skF_2','#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_124,c_602])).

tff(c_130,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_292])).

tff(c_126,plain,(
    v3_funct_2('#skF_4','#skF_2','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_292])).

tff(c_2514,plain,(
    ! [C_337,A_338,B_339] :
      ( v2_funct_1(C_337)
      | ~ v3_funct_2(C_337,A_338,B_339)
      | ~ v1_funct_1(C_337)
      | ~ m1_subset_1(C_337,k1_zfmisc_1(k2_zfmisc_1(A_338,B_339))) ) ),
    inference(cnfTransformation,[status(thm)],[f_174])).

tff(c_2527,plain,
    ( v2_funct_1('#skF_4')
    | ~ v3_funct_2('#skF_4','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_124,c_2514])).

tff(c_2535,plain,(
    v2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_130,c_126,c_2527])).

tff(c_128,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_292])).

tff(c_6117,plain,(
    ! [A_526,B_527] :
      ( k2_funct_2(A_526,B_527) = k2_funct_1(B_527)
      | ~ m1_subset_1(B_527,k1_zfmisc_1(k2_zfmisc_1(A_526,A_526)))
      | ~ v3_funct_2(B_527,A_526,A_526)
      | ~ v1_funct_2(B_527,A_526,A_526)
      | ~ v1_funct_1(B_527) ) ),
    inference(cnfTransformation,[status(thm)],[f_252])).

tff(c_6139,plain,
    ( k2_funct_2('#skF_2','#skF_4') = k2_funct_1('#skF_4')
    | ~ v3_funct_2('#skF_4','#skF_2','#skF_2')
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_124,c_6117])).

tff(c_6148,plain,(
    k2_funct_2('#skF_2','#skF_4') = k2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_130,c_128,c_126,c_6139])).

tff(c_6896,plain,(
    ! [A_575,B_576] :
      ( m1_subset_1(k2_funct_2(A_575,B_576),k1_zfmisc_1(k2_zfmisc_1(A_575,A_575)))
      | ~ m1_subset_1(B_576,k1_zfmisc_1(k2_zfmisc_1(A_575,A_575)))
      | ~ v3_funct_2(B_576,A_575,A_575)
      | ~ v1_funct_2(B_576,A_575,A_575)
      | ~ v1_funct_1(B_576) ) ),
    inference(cnfTransformation,[status(thm)],[f_228])).

tff(c_6976,plain,
    ( m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2')))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2')))
    | ~ v3_funct_2('#skF_4','#skF_2','#skF_2')
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_6148,c_6896])).

tff(c_7024,plain,(
    m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_130,c_128,c_126,c_124,c_6976])).

tff(c_48,plain,(
    ! [C_39,A_37,B_38] :
      ( v1_relat_1(C_39)
      | ~ m1_subset_1(C_39,k1_zfmisc_1(k2_zfmisc_1(A_37,B_38))) ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_7483,plain,(
    v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_7024,c_48])).

tff(c_132,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_292])).

tff(c_217,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_2')) ),
    inference(resolution,[status(thm)],[c_132,c_205])).

tff(c_227,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_217])).

tff(c_387,plain,(
    ! [C_139,B_140,A_141] :
      ( v5_relat_1(C_139,B_140)
      | ~ m1_subset_1(C_139,k1_zfmisc_1(k2_zfmisc_1(A_141,B_140))) ) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_404,plain,(
    v5_relat_1('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_132,c_387])).

tff(c_617,plain,(
    ! [B_184,A_185] :
      ( k2_relat_1(B_184) = A_185
      | ~ v2_funct_2(B_184,A_185)
      | ~ v5_relat_1(B_184,A_185)
      | ~ v1_relat_1(B_184) ) ),
    inference(cnfTransformation,[status(thm)],[f_200])).

tff(c_623,plain,
    ( k2_relat_1('#skF_3') = '#skF_2'
    | ~ v2_funct_2('#skF_3','#skF_2')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_404,c_617])).

tff(c_632,plain,
    ( k2_relat_1('#skF_3') = '#skF_2'
    | ~ v2_funct_2('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_227,c_623])).

tff(c_636,plain,(
    ~ v2_funct_2('#skF_3','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_632])).

tff(c_138,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_292])).

tff(c_134,plain,(
    v3_funct_2('#skF_3','#skF_2','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_292])).

tff(c_1630,plain,(
    ! [C_267,B_268,A_269] :
      ( v2_funct_2(C_267,B_268)
      | ~ v3_funct_2(C_267,A_269,B_268)
      | ~ v1_funct_1(C_267)
      | ~ m1_subset_1(C_267,k1_zfmisc_1(k2_zfmisc_1(A_269,B_268))) ) ),
    inference(cnfTransformation,[status(thm)],[f_174])).

tff(c_1649,plain,
    ( v2_funct_2('#skF_3','#skF_2')
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_132,c_1630])).

tff(c_1657,plain,(
    v2_funct_2('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_138,c_134,c_1649])).

tff(c_1659,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_636,c_1657])).

tff(c_1660,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_632])).

tff(c_114,plain,(
    ! [A_86] : k6_relat_1(A_86) = k6_partfun1(A_86) ),
    inference(cnfTransformation,[status(thm)],[f_254])).

tff(c_42,plain,(
    ! [A_34] :
      ( k5_relat_1(A_34,k6_relat_1(k2_relat_1(A_34))) = A_34
      | ~ v1_relat_1(A_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_141,plain,(
    ! [A_34] :
      ( k5_relat_1(A_34,k6_partfun1(k2_relat_1(A_34))) = A_34
      | ~ v1_relat_1(A_34) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_114,c_42])).

tff(c_1670,plain,
    ( k5_relat_1('#skF_3',k6_partfun1('#skF_2')) = '#skF_3'
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1660,c_141])).

tff(c_1679,plain,(
    k5_relat_1('#skF_3',k6_partfun1('#skF_2')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_227,c_1670])).

tff(c_36,plain,(
    ! [A_32] :
      ( k2_relat_1(A_32) != k1_xboole_0
      | k1_xboole_0 = A_32
      | ~ v1_relat_1(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_242,plain,
    ( k2_relat_1('#skF_3') != k1_xboole_0
    | k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_227,c_36])).

tff(c_271,plain,(
    k2_relat_1('#skF_3') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_242])).

tff(c_1663,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1660,c_271])).

tff(c_403,plain,(
    v5_relat_1('#skF_4','#skF_2') ),
    inference(resolution,[status(thm)],[c_124,c_387])).

tff(c_626,plain,
    ( k2_relat_1('#skF_4') = '#skF_2'
    | ~ v2_funct_2('#skF_4','#skF_2')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_403,c_617])).

tff(c_635,plain,
    ( k2_relat_1('#skF_4') = '#skF_2'
    | ~ v2_funct_2('#skF_4','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_224,c_626])).

tff(c_1682,plain,(
    ~ v2_funct_2('#skF_4','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_635])).

tff(c_2175,plain,(
    ! [C_309,B_310,A_311] :
      ( v2_funct_2(C_309,B_310)
      | ~ v3_funct_2(C_309,A_311,B_310)
      | ~ v1_funct_1(C_309)
      | ~ m1_subset_1(C_309,k1_zfmisc_1(k2_zfmisc_1(A_311,B_310))) ) ),
    inference(cnfTransformation,[status(thm)],[f_174])).

tff(c_2191,plain,
    ( v2_funct_2('#skF_4','#skF_2')
    | ~ v3_funct_2('#skF_4','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_124,c_2175])).

tff(c_2199,plain,(
    v2_funct_2('#skF_4','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_130,c_126,c_2191])).

tff(c_2201,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1682,c_2199])).

tff(c_2202,plain,(
    k2_relat_1('#skF_4') = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_635])).

tff(c_441,plain,(
    ! [C_153,A_154,B_155] :
      ( v4_relat_1(C_153,A_154)
      | ~ m1_subset_1(C_153,k1_zfmisc_1(k2_zfmisc_1(A_154,B_155))) ) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_457,plain,(
    v4_relat_1('#skF_4','#skF_2') ),
    inference(resolution,[status(thm)],[c_124,c_441])).

tff(c_32,plain,(
    ! [B_24,A_23] :
      ( k7_relat_1(B_24,A_23) = B_24
      | ~ v4_relat_1(B_24,A_23)
      | ~ v1_relat_1(B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_461,plain,
    ( k7_relat_1('#skF_4','#skF_2') = '#skF_4'
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_457,c_32])).

tff(c_464,plain,(
    k7_relat_1('#skF_4','#skF_2') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_224,c_461])).

tff(c_30,plain,(
    ! [B_22,A_21] :
      ( k2_relat_1(k7_relat_1(B_22,A_21)) = k9_relat_1(B_22,A_21)
      | ~ v1_relat_1(B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_481,plain,
    ( k9_relat_1('#skF_4','#skF_2') = k2_relat_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_464,c_30])).

tff(c_485,plain,(
    k9_relat_1('#skF_4','#skF_2') = k2_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_224,c_481])).

tff(c_2204,plain,(
    k9_relat_1('#skF_4','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2202,c_485])).

tff(c_2449,plain,(
    ! [A_328,B_329,C_330,D_331] :
      ( k7_relset_1(A_328,B_329,C_330,D_331) = k9_relat_1(C_330,D_331)
      | ~ m1_subset_1(C_330,k1_zfmisc_1(k2_zfmisc_1(A_328,B_329))) ) ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_2463,plain,(
    ! [D_331] : k7_relset_1('#skF_2','#skF_2','#skF_4',D_331) = k9_relat_1('#skF_4',D_331) ),
    inference(resolution,[status(thm)],[c_124,c_2449])).

tff(c_2752,plain,(
    ! [A_355,B_356,C_357] :
      ( k7_relset_1(A_355,B_356,C_357,A_355) = k2_relset_1(A_355,B_356,C_357)
      | ~ m1_subset_1(C_357,k1_zfmisc_1(k2_zfmisc_1(A_355,B_356))) ) ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_2763,plain,(
    k7_relset_1('#skF_2','#skF_2','#skF_4','#skF_2') = k2_relset_1('#skF_2','#skF_2','#skF_4') ),
    inference(resolution,[status(thm)],[c_124,c_2752])).

tff(c_2769,plain,(
    k2_relset_1('#skF_2','#skF_2','#skF_4') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2204,c_2463,c_2763])).

tff(c_7488,plain,(
    ! [A_586,C_587,B_588] :
      ( k6_partfun1(A_586) = k5_relat_1(C_587,k2_funct_1(C_587))
      | k1_xboole_0 = B_588
      | ~ v2_funct_1(C_587)
      | k2_relset_1(A_586,B_588,C_587) != B_588
      | ~ m1_subset_1(C_587,k1_zfmisc_1(k2_zfmisc_1(A_586,B_588)))
      | ~ v1_funct_2(C_587,A_586,B_588)
      | ~ v1_funct_1(C_587) ) ),
    inference(cnfTransformation,[status(thm)],[f_270])).

tff(c_7511,plain,
    ( k5_relat_1('#skF_4',k2_funct_1('#skF_4')) = k6_partfun1('#skF_2')
    | k1_xboole_0 = '#skF_2'
    | ~ v2_funct_1('#skF_4')
    | k2_relset_1('#skF_2','#skF_2','#skF_4') != '#skF_2'
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_124,c_7488])).

tff(c_7529,plain,
    ( k5_relat_1('#skF_4',k2_funct_1('#skF_4')) = k6_partfun1('#skF_2')
    | k1_xboole_0 = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_130,c_128,c_2769,c_2535,c_7511])).

tff(c_7530,plain,(
    k5_relat_1('#skF_4',k2_funct_1('#skF_4')) = k6_partfun1('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_1663,c_7529])).

tff(c_5518,plain,(
    ! [C_503,E_502,F_499,A_500,D_501,B_498] :
      ( m1_subset_1(k1_partfun1(A_500,B_498,C_503,D_501,E_502,F_499),k1_zfmisc_1(k2_zfmisc_1(A_500,D_501)))
      | ~ m1_subset_1(F_499,k1_zfmisc_1(k2_zfmisc_1(C_503,D_501)))
      | ~ v1_funct_1(F_499)
      | ~ m1_subset_1(E_502,k1_zfmisc_1(k2_zfmisc_1(A_500,B_498)))
      | ~ v1_funct_1(E_502) ) ),
    inference(cnfTransformation,[status(thm)],[f_212])).

tff(c_108,plain,(
    ! [A_77] : m1_subset_1(k6_partfun1(A_77),k1_zfmisc_1(k2_zfmisc_1(A_77,A_77))) ),
    inference(cnfTransformation,[status(thm)],[f_232])).

tff(c_122,plain,(
    r2_relset_1('#skF_2','#skF_2',k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2','#skF_3','#skF_4'),k6_partfun1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_292])).

tff(c_3599,plain,(
    ! [D_413,C_414,A_415,B_416] :
      ( D_413 = C_414
      | ~ r2_relset_1(A_415,B_416,C_414,D_413)
      | ~ m1_subset_1(D_413,k1_zfmisc_1(k2_zfmisc_1(A_415,B_416)))
      | ~ m1_subset_1(C_414,k1_zfmisc_1(k2_zfmisc_1(A_415,B_416))) ) ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_3607,plain,
    ( k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2','#skF_3','#skF_4') = k6_partfun1('#skF_2')
    | ~ m1_subset_1(k6_partfun1('#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2')))
    | ~ m1_subset_1(k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(resolution,[status(thm)],[c_122,c_3599])).

tff(c_3622,plain,
    ( k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2','#skF_3','#skF_4') = k6_partfun1('#skF_2')
    | ~ m1_subset_1(k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_108,c_3607])).

tff(c_3707,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_3622])).

tff(c_5549,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_5518,c_3707])).

tff(c_5634,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_138,c_132,c_130,c_124,c_5549])).

tff(c_5635,plain,(
    k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2','#skF_3','#skF_4') = k6_partfun1('#skF_2') ),
    inference(splitRight,[status(thm)],[c_3622])).

tff(c_7269,plain,(
    ! [D_582,F_583,B_584,E_585,A_580,C_581] :
      ( k1_partfun1(A_580,B_584,C_581,D_582,E_585,F_583) = k5_relat_1(E_585,F_583)
      | ~ m1_subset_1(F_583,k1_zfmisc_1(k2_zfmisc_1(C_581,D_582)))
      | ~ v1_funct_1(F_583)
      | ~ m1_subset_1(E_585,k1_zfmisc_1(k2_zfmisc_1(A_580,B_584)))
      | ~ v1_funct_1(E_585) ) ),
    inference(cnfTransformation,[status(thm)],[f_242])).

tff(c_7290,plain,(
    ! [A_580,B_584,E_585] :
      ( k1_partfun1(A_580,B_584,'#skF_2','#skF_2',E_585,'#skF_4') = k5_relat_1(E_585,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_585,k1_zfmisc_1(k2_zfmisc_1(A_580,B_584)))
      | ~ v1_funct_1(E_585) ) ),
    inference(resolution,[status(thm)],[c_124,c_7269])).

tff(c_7698,plain,(
    ! [A_592,B_593,E_594] :
      ( k1_partfun1(A_592,B_593,'#skF_2','#skF_2',E_594,'#skF_4') = k5_relat_1(E_594,'#skF_4')
      | ~ m1_subset_1(E_594,k1_zfmisc_1(k2_zfmisc_1(A_592,B_593)))
      | ~ v1_funct_1(E_594) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_130,c_7290])).

tff(c_7735,plain,
    ( k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_132,c_7698])).

tff(c_7750,plain,(
    k5_relat_1('#skF_3','#skF_4') = k6_partfun1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_138,c_5635,c_7735])).

tff(c_34,plain,(
    ! [A_25,B_29,C_31] :
      ( k5_relat_1(k5_relat_1(A_25,B_29),C_31) = k5_relat_1(A_25,k5_relat_1(B_29,C_31))
      | ~ v1_relat_1(C_31)
      | ~ v1_relat_1(B_29)
      | ~ v1_relat_1(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_7764,plain,(
    ! [C_31] :
      ( k5_relat_1(k6_partfun1('#skF_2'),C_31) = k5_relat_1('#skF_3',k5_relat_1('#skF_4',C_31))
      | ~ v1_relat_1(C_31)
      | ~ v1_relat_1('#skF_4')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_7750,c_34])).

tff(c_12469,plain,(
    ! [C_713] :
      ( k5_relat_1(k6_partfun1('#skF_2'),C_713) = k5_relat_1('#skF_3',k5_relat_1('#skF_4',C_713))
      | ~ v1_relat_1(C_713) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_227,c_224,c_7764])).

tff(c_6229,plain,(
    ! [A_538,B_539] :
      ( v1_funct_2(k2_funct_2(A_538,B_539),A_538,A_538)
      | ~ m1_subset_1(B_539,k1_zfmisc_1(k2_zfmisc_1(A_538,A_538)))
      | ~ v3_funct_2(B_539,A_538,A_538)
      | ~ v1_funct_2(B_539,A_538,A_538)
      | ~ v1_funct_1(B_539) ) ),
    inference(cnfTransformation,[status(thm)],[f_228])).

tff(c_6244,plain,
    ( v1_funct_2(k2_funct_2('#skF_2','#skF_4'),'#skF_2','#skF_2')
    | ~ v3_funct_2('#skF_4','#skF_2','#skF_2')
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_124,c_6229])).

tff(c_6251,plain,(
    v1_funct_2(k2_funct_1('#skF_4'),'#skF_2','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_130,c_128,c_126,c_6148,c_6244])).

tff(c_88,plain,(
    ! [B_65,A_64,C_66] :
      ( k1_xboole_0 = B_65
      | k1_relset_1(A_64,B_65,C_66) = A_64
      | ~ v1_funct_2(C_66,A_64,B_65)
      | ~ m1_subset_1(C_66,k1_zfmisc_1(k2_zfmisc_1(A_64,B_65))) ) ),
    inference(cnfTransformation,[status(thm)],[f_192])).

tff(c_7401,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1('#skF_2','#skF_2',k2_funct_1('#skF_4')) = '#skF_2'
    | ~ v1_funct_2(k2_funct_1('#skF_4'),'#skF_2','#skF_2') ),
    inference(resolution,[status(thm)],[c_7024,c_88])).

tff(c_7467,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1('#skF_2','#skF_2',k2_funct_1('#skF_4')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6251,c_7401])).

tff(c_7468,plain,(
    k1_relset_1('#skF_2','#skF_2',k2_funct_1('#skF_4')) = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_1663,c_7467])).

tff(c_54,plain,(
    ! [A_43,B_44,C_45] :
      ( k1_relset_1(A_43,B_44,C_45) = k1_relat_1(C_45)
      | ~ m1_subset_1(C_45,k1_zfmisc_1(k2_zfmisc_1(A_43,B_44))) ) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_7478,plain,(
    k1_relset_1('#skF_2','#skF_2',k2_funct_1('#skF_4')) = k1_relat_1(k2_funct_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_7024,c_54])).

tff(c_9309,plain,(
    k1_relat_1(k2_funct_1('#skF_4')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_7468,c_7478])).

tff(c_40,plain,(
    ! [A_33] :
      ( k5_relat_1(k6_relat_1(k1_relat_1(A_33)),A_33) = A_33
      | ~ v1_relat_1(A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_142,plain,(
    ! [A_33] :
      ( k5_relat_1(k6_partfun1(k1_relat_1(A_33)),A_33) = A_33
      | ~ v1_relat_1(A_33) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_114,c_40])).

tff(c_9317,plain,
    ( k5_relat_1(k6_partfun1('#skF_2'),k2_funct_1('#skF_4')) = k2_funct_1('#skF_4')
    | ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_9309,c_142])).

tff(c_9323,plain,(
    k5_relat_1(k6_partfun1('#skF_2'),k2_funct_1('#skF_4')) = k2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_7483,c_9317])).

tff(c_12490,plain,
    ( k5_relat_1('#skF_3',k5_relat_1('#skF_4',k2_funct_1('#skF_4'))) = k2_funct_1('#skF_4')
    | ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_12469,c_9323])).

tff(c_12615,plain,(
    k2_funct_1('#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_7483,c_1679,c_7530,c_12490])).

tff(c_44,plain,(
    ! [A_35] :
      ( k2_funct_1(k2_funct_1(A_35)) = A_35
      | ~ v2_funct_1(A_35)
      | ~ v1_funct_1(A_35)
      | ~ v1_relat_1(A_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_12719,plain,
    ( k2_funct_1('#skF_3') = '#skF_4'
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_12615,c_44])).

tff(c_12723,plain,(
    k2_funct_1('#skF_3') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_224,c_130,c_2535,c_12719])).

tff(c_136,plain,(
    v1_funct_2('#skF_3','#skF_2','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_292])).

tff(c_6142,plain,
    ( k2_funct_2('#skF_2','#skF_3') = k2_funct_1('#skF_3')
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_132,c_6117])).

tff(c_6151,plain,(
    k2_funct_2('#skF_2','#skF_3') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_138,c_136,c_134,c_6142])).

tff(c_120,plain,(
    ~ r2_relset_1('#skF_2','#skF_2','#skF_4',k2_funct_2('#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_292])).

tff(c_6158,plain,(
    ~ r2_relset_1('#skF_2','#skF_2','#skF_4',k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6151,c_120])).

tff(c_12889,plain,(
    ~ r2_relset_1('#skF_2','#skF_2','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12723,c_6158])).

tff(c_12917,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_614,c_12889])).

tff(c_12918,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_242])).

tff(c_8,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_12925,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12918,c_8])).

tff(c_12919,plain,(
    k2_relat_1('#skF_3') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_242])).

tff(c_12930,plain,(
    k2_relat_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12918,c_12919])).

tff(c_13206,plain,(
    ! [C_747,B_748,A_749] :
      ( v5_relat_1(C_747,B_748)
      | ~ m1_subset_1(C_747,k1_zfmisc_1(k2_zfmisc_1(A_749,B_748))) ) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_13223,plain,(
    v5_relat_1('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_132,c_13206])).

tff(c_14456,plain,(
    ! [B_876,A_877] :
      ( k2_relat_1(B_876) = A_877
      | ~ v2_funct_2(B_876,A_877)
      | ~ v5_relat_1(B_876,A_877)
      | ~ v1_relat_1(B_876) ) ),
    inference(cnfTransformation,[status(thm)],[f_200])).

tff(c_14465,plain,
    ( k2_relat_1('#skF_3') = '#skF_2'
    | ~ v2_funct_2('#skF_3','#skF_2')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_13223,c_14456])).

tff(c_14477,plain,
    ( '#skF_2' = '#skF_3'
    | ~ v2_funct_2('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_227,c_12930,c_14465])).

tff(c_14481,plain,(
    ~ v2_funct_2('#skF_3','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_14477])).

tff(c_15461,plain,(
    ! [C_956,B_957,A_958] :
      ( v2_funct_2(C_956,B_957)
      | ~ v3_funct_2(C_956,A_958,B_957)
      | ~ v1_funct_1(C_956)
      | ~ m1_subset_1(C_956,k1_zfmisc_1(k2_zfmisc_1(A_958,B_957))) ) ),
    inference(cnfTransformation,[status(thm)],[f_174])).

tff(c_15480,plain,
    ( v2_funct_2('#skF_3','#skF_2')
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_132,c_15461])).

tff(c_15488,plain,(
    v2_funct_2('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_138,c_134,c_15480])).

tff(c_15490,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_14481,c_15488])).

tff(c_15491,plain,(
    '#skF_2' = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_14477])).

tff(c_16,plain,(
    ! [A_8,B_9] :
      ( v1_xboole_0(k2_zfmisc_1(A_8,B_9))
      | ~ v1_xboole_0(B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_169,plain,(
    ! [A_105,B_106] :
      ( r1_tarski(A_105,B_106)
      | ~ m1_subset_1(A_105,k1_zfmisc_1(B_106)) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_177,plain,(
    r1_tarski('#skF_3',k2_zfmisc_1('#skF_2','#skF_2')) ),
    inference(resolution,[status(thm)],[c_132,c_169])).

tff(c_254,plain,(
    ! [A_119,B_120] :
      ( r2_xboole_0(A_119,B_120)
      | B_120 = A_119
      | ~ r1_tarski(A_119,B_120) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_199,plain,(
    ! [A_112,B_113] :
      ( r2_hidden('#skF_1'(A_112,B_113),B_113)
      | ~ r2_xboole_0(A_112,B_113) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_14,plain,(
    ! [B_7,A_6] :
      ( ~ v1_xboole_0(B_7)
      | ~ r2_hidden(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_203,plain,(
    ! [B_113,A_112] :
      ( ~ v1_xboole_0(B_113)
      | ~ r2_xboole_0(A_112,B_113) ) ),
    inference(resolution,[status(thm)],[c_199,c_14])).

tff(c_12989,plain,(
    ! [B_722,A_723] :
      ( ~ v1_xboole_0(B_722)
      | B_722 = A_723
      | ~ r1_tarski(A_723,B_722) ) ),
    inference(resolution,[status(thm)],[c_254,c_203])).

tff(c_12999,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1('#skF_2','#skF_2'))
    | k2_zfmisc_1('#skF_2','#skF_2') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_177,c_12989])).

tff(c_13002,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_2','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_12999])).

tff(c_13006,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_16,c_13002])).

tff(c_15503,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_15491,c_13006])).

tff(c_15518,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12925,c_15503])).

tff(c_15519,plain,(
    k2_zfmisc_1('#skF_2','#skF_2') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_12999])).

tff(c_176,plain,(
    r1_tarski('#skF_4',k2_zfmisc_1('#skF_2','#skF_2')) ),
    inference(resolution,[status(thm)],[c_124,c_169])).

tff(c_15522,plain,(
    r1_tarski('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_15519,c_176])).

tff(c_265,plain,(
    ! [B_120,A_119] :
      ( ~ v1_xboole_0(B_120)
      | B_120 = A_119
      | ~ r1_tarski(A_119,B_120) ) ),
    inference(resolution,[status(thm)],[c_254,c_203])).

tff(c_15557,plain,
    ( ~ v1_xboole_0('#skF_3')
    | '#skF_3' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_15522,c_265])).

tff(c_15563,plain,(
    '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12925,c_15557])).

tff(c_15576,plain,(
    k2_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_15563,c_15563,c_12930])).

tff(c_234,plain,
    ( k2_relat_1('#skF_4') != k1_xboole_0
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_224,c_36])).

tff(c_253,plain,(
    k2_relat_1('#skF_4') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_234])).

tff(c_12922,plain,(
    k2_relat_1('#skF_4') != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12918,c_253])).

tff(c_15575,plain,(
    k2_relat_1('#skF_4') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_15563,c_12922])).

tff(c_15646,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_15576,c_15575])).

tff(c_15647,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_234])).

tff(c_15648,plain,(
    k2_relat_1('#skF_4') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_234])).

tff(c_15671,plain,(
    k2_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_15647,c_15648])).

tff(c_15666,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_15647,c_8])).

tff(c_22163,plain,(
    ! [C_1635,B_1636,A_1637] :
      ( v5_relat_1(C_1635,B_1636)
      | ~ m1_subset_1(C_1635,k1_zfmisc_1(k2_zfmisc_1(A_1637,B_1636))) ) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_22176,plain,(
    v5_relat_1('#skF_4','#skF_2') ),
    inference(resolution,[status(thm)],[c_124,c_22163])).

tff(c_22851,plain,(
    ! [B_1728,A_1729] :
      ( k2_relat_1(B_1728) = A_1729
      | ~ v2_funct_2(B_1728,A_1729)
      | ~ v5_relat_1(B_1728,A_1729)
      | ~ v1_relat_1(B_1728) ) ),
    inference(cnfTransformation,[status(thm)],[f_200])).

tff(c_22860,plain,
    ( k2_relat_1('#skF_4') = '#skF_2'
    | ~ v2_funct_2('#skF_4','#skF_2')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_22176,c_22851])).

tff(c_22869,plain,
    ( '#skF_2' = '#skF_4'
    | ~ v2_funct_2('#skF_4','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_224,c_15671,c_22860])).

tff(c_22870,plain,(
    ~ v2_funct_2('#skF_4','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_22869])).

tff(c_23337,plain,(
    ! [C_1770,B_1771,A_1772] :
      ( v2_funct_2(C_1770,B_1771)
      | ~ v3_funct_2(C_1770,A_1772,B_1771)
      | ~ v1_funct_1(C_1770)
      | ~ m1_subset_1(C_1770,k1_zfmisc_1(k2_zfmisc_1(A_1772,B_1771))) ) ),
    inference(cnfTransformation,[status(thm)],[f_174])).

tff(c_23353,plain,
    ( v2_funct_2('#skF_4','#skF_2')
    | ~ v3_funct_2('#skF_4','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_124,c_23337])).

tff(c_23358,plain,(
    v2_funct_2('#skF_4','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_130,c_126,c_23353])).

tff(c_23360,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_22870,c_23358])).

tff(c_23361,plain,(
    '#skF_2' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_22869])).

tff(c_15649,plain,(
    ! [A_960,B_961] :
      ( r2_xboole_0(A_960,B_961)
      | B_961 = A_960
      | ~ r1_tarski(A_960,B_961) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_22044,plain,(
    ! [B_1618,A_1619] :
      ( ~ v1_xboole_0(B_1618)
      | B_1618 = A_1619
      | ~ r1_tarski(A_1619,B_1618) ) ),
    inference(resolution,[status(thm)],[c_15649,c_203])).

tff(c_22051,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1('#skF_2','#skF_2'))
    | k2_zfmisc_1('#skF_2','#skF_2') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_176,c_22044])).

tff(c_22110,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_2','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_22051])).

tff(c_22114,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_16,c_22110])).

tff(c_23368,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_23361,c_22114])).

tff(c_23379,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_15666,c_23368])).

tff(c_23380,plain,(
    k2_zfmisc_1('#skF_2','#skF_2') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_22051])).

tff(c_23383,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_23380,c_124])).

tff(c_23610,plain,(
    ! [C_1791,B_1792,A_1793] :
      ( v5_relat_1(C_1791,B_1792)
      | ~ m1_subset_1(C_1791,k1_zfmisc_1(k2_zfmisc_1(A_1793,B_1792))) ) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_23639,plain,(
    ! [C_1797] :
      ( v5_relat_1(C_1797,'#skF_2')
      | ~ m1_subset_1(C_1797,k1_zfmisc_1('#skF_4')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_23380,c_23610])).

tff(c_23647,plain,(
    v5_relat_1('#skF_4','#skF_2') ),
    inference(resolution,[status(thm)],[c_23383,c_23639])).

tff(c_24931,plain,(
    ! [B_1924,A_1925] :
      ( k2_relat_1(B_1924) = A_1925
      | ~ v2_funct_2(B_1924,A_1925)
      | ~ v5_relat_1(B_1924,A_1925)
      | ~ v1_relat_1(B_1924) ) ),
    inference(cnfTransformation,[status(thm)],[f_200])).

tff(c_24940,plain,
    ( k2_relat_1('#skF_4') = '#skF_2'
    | ~ v2_funct_2('#skF_4','#skF_2')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_23647,c_24931])).

tff(c_24950,plain,
    ( '#skF_2' = '#skF_4'
    | ~ v2_funct_2('#skF_4','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_224,c_15671,c_24940])).

tff(c_24978,plain,(
    ~ v2_funct_2('#skF_4','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_24950])).

tff(c_62,plain,(
    ! [A_54] : r1_tarski(k6_relat_1(A_54),k2_zfmisc_1(A_54,A_54)) ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_139,plain,(
    ! [A_54] : r1_tarski(k6_partfun1(A_54),k2_zfmisc_1(A_54,A_54)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_114,c_62])).

tff(c_23394,plain,(
    r1_tarski(k6_partfun1('#skF_2'),'#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_23380,c_139])).

tff(c_15660,plain,(
    ! [B_961,A_960] :
      ( ~ v1_xboole_0(B_961)
      | B_961 = A_960
      | ~ r1_tarski(A_960,B_961) ) ),
    inference(resolution,[status(thm)],[c_15649,c_203])).

tff(c_23446,plain,
    ( ~ v1_xboole_0('#skF_4')
    | k6_partfun1('#skF_2') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_23394,c_15660])).

tff(c_23452,plain,(
    k6_partfun1('#skF_2') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_15666,c_23446])).

tff(c_26028,plain,(
    ! [C_2024,B_2025,A_2026] :
      ( v2_funct_2(C_2024,B_2025)
      | ~ v3_funct_2(C_2024,A_2026,B_2025)
      | ~ v1_funct_1(C_2024)
      | ~ m1_subset_1(C_2024,k1_zfmisc_1(k2_zfmisc_1(A_2026,B_2025))) ) ),
    inference(cnfTransformation,[status(thm)],[f_174])).

tff(c_26053,plain,(
    ! [A_2027] :
      ( v2_funct_2(k6_partfun1(A_2027),A_2027)
      | ~ v3_funct_2(k6_partfun1(A_2027),A_2027,A_2027)
      | ~ v1_funct_1(k6_partfun1(A_2027)) ) ),
    inference(resolution,[status(thm)],[c_108,c_26028])).

tff(c_26056,plain,
    ( v2_funct_2(k6_partfun1('#skF_2'),'#skF_2')
    | ~ v3_funct_2('#skF_4','#skF_2','#skF_2')
    | ~ v1_funct_1(k6_partfun1('#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_23452,c_26053])).

tff(c_26058,plain,(
    v2_funct_2('#skF_4','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_130,c_23452,c_126,c_23452,c_26056])).

tff(c_26060,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_24978,c_26058])).

tff(c_26061,plain,(
    '#skF_2' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_24950])).

tff(c_24825,plain,(
    ! [A_1916,B_1917,D_1918] :
      ( r2_relset_1(A_1916,B_1917,D_1918,D_1918)
      | ~ m1_subset_1(D_1918,k1_zfmisc_1(k2_zfmisc_1(A_1916,B_1917))) ) ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_24835,plain,(
    ! [A_1919] : r2_relset_1(A_1919,A_1919,k6_partfun1(A_1919),k6_partfun1(A_1919)) ),
    inference(resolution,[status(thm)],[c_108,c_24825])).

tff(c_24838,plain,(
    r2_relset_1('#skF_2','#skF_2','#skF_4',k6_partfun1('#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_23452,c_24835])).

tff(c_24842,plain,(
    r2_relset_1('#skF_2','#skF_2','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_23452,c_24838])).

tff(c_26065,plain,(
    r2_relset_1('#skF_4','#skF_4','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26061,c_26061,c_24842])).

tff(c_26077,plain,(
    k6_partfun1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_26061,c_23452])).

tff(c_26080,plain,(
    v1_funct_2('#skF_4','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26061,c_26061,c_128])).

tff(c_26081,plain,(
    v3_funct_2('#skF_4','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26061,c_26061,c_126])).

tff(c_46,plain,(
    ! [A_36] : k2_funct_1(k6_relat_1(A_36)) = k6_relat_1(A_36) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_140,plain,(
    ! [A_36] : k2_funct_1(k6_partfun1(A_36)) = k6_partfun1(A_36) ),
    inference(demodulation,[status(thm),theory(equality)],[c_114,c_114,c_46])).

tff(c_28600,plain,(
    ! [A_2207,B_2208] :
      ( k2_funct_2(A_2207,B_2208) = k2_funct_1(B_2208)
      | ~ m1_subset_1(B_2208,k1_zfmisc_1(k2_zfmisc_1(A_2207,A_2207)))
      | ~ v3_funct_2(B_2208,A_2207,A_2207)
      | ~ v1_funct_2(B_2208,A_2207,A_2207)
      | ~ v1_funct_1(B_2208) ) ),
    inference(cnfTransformation,[status(thm)],[f_252])).

tff(c_28618,plain,(
    ! [A_77] :
      ( k2_funct_2(A_77,k6_partfun1(A_77)) = k2_funct_1(k6_partfun1(A_77))
      | ~ v3_funct_2(k6_partfun1(A_77),A_77,A_77)
      | ~ v1_funct_2(k6_partfun1(A_77),A_77,A_77)
      | ~ v1_funct_1(k6_partfun1(A_77)) ) ),
    inference(resolution,[status(thm)],[c_108,c_28600])).

tff(c_33578,plain,(
    ! [A_2435] :
      ( k2_funct_2(A_2435,k6_partfun1(A_2435)) = k6_partfun1(A_2435)
      | ~ v3_funct_2(k6_partfun1(A_2435),A_2435,A_2435)
      | ~ v1_funct_2(k6_partfun1(A_2435),A_2435,A_2435)
      | ~ v1_funct_1(k6_partfun1(A_2435)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_140,c_28618])).

tff(c_33581,plain,
    ( k2_funct_2('#skF_4',k6_partfun1('#skF_4')) = k6_partfun1('#skF_4')
    | ~ v3_funct_2('#skF_4','#skF_4','#skF_4')
    | ~ v1_funct_2(k6_partfun1('#skF_4'),'#skF_4','#skF_4')
    | ~ v1_funct_1(k6_partfun1('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_26077,c_33578])).

tff(c_33583,plain,(
    k2_funct_2('#skF_4','#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_130,c_26077,c_26080,c_26077,c_26081,c_26077,c_26077,c_33581])).

tff(c_15869,plain,(
    ! [C_992,B_993,A_994] :
      ( v5_relat_1(C_992,B_993)
      | ~ m1_subset_1(C_992,k1_zfmisc_1(k2_zfmisc_1(A_994,B_993))) ) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_15885,plain,(
    v5_relat_1('#skF_4','#skF_2') ),
    inference(resolution,[status(thm)],[c_124,c_15869])).

tff(c_16629,plain,(
    ! [B_1073,A_1074] :
      ( k2_relat_1(B_1073) = A_1074
      | ~ v2_funct_2(B_1073,A_1074)
      | ~ v5_relat_1(B_1073,A_1074)
      | ~ v1_relat_1(B_1073) ) ),
    inference(cnfTransformation,[status(thm)],[f_200])).

tff(c_16641,plain,
    ( k2_relat_1('#skF_4') = '#skF_2'
    | ~ v2_funct_2('#skF_4','#skF_2')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_15885,c_16629])).

tff(c_16653,plain,
    ( '#skF_2' = '#skF_4'
    | ~ v2_funct_2('#skF_4','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_224,c_15671,c_16641])).

tff(c_16654,plain,(
    ~ v2_funct_2('#skF_4','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_16653])).

tff(c_17075,plain,(
    ! [C_1112,B_1113,A_1114] :
      ( v2_funct_2(C_1112,B_1113)
      | ~ v3_funct_2(C_1112,A_1114,B_1113)
      | ~ v1_funct_1(C_1112)
      | ~ m1_subset_1(C_1112,k1_zfmisc_1(k2_zfmisc_1(A_1114,B_1113))) ) ),
    inference(cnfTransformation,[status(thm)],[f_174])).

tff(c_17091,plain,
    ( v2_funct_2('#skF_4','#skF_2')
    | ~ v3_funct_2('#skF_4','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_124,c_17075])).

tff(c_17099,plain,(
    v2_funct_2('#skF_4','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_130,c_126,c_17091])).

tff(c_17101,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_16654,c_17099])).

tff(c_17102,plain,(
    '#skF_2' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_16653])).

tff(c_15802,plain,(
    ! [B_975,A_976] :
      ( ~ v1_xboole_0(B_975)
      | B_975 = A_976
      | ~ r1_tarski(A_976,B_975) ) ),
    inference(resolution,[status(thm)],[c_15649,c_203])).

tff(c_15813,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1('#skF_2','#skF_2'))
    | k2_zfmisc_1('#skF_2','#skF_2') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_176,c_15802])).

tff(c_15830,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_2','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_15813])).

tff(c_15834,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_16,c_15830])).

tff(c_17112,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_17102,c_15834])).

tff(c_17127,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_15666,c_17112])).

tff(c_17128,plain,(
    k2_zfmisc_1('#skF_2','#skF_2') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_15813])).

tff(c_17130,plain,(
    r1_tarski('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_17128,c_177])).

tff(c_17157,plain,
    ( ~ v1_xboole_0('#skF_4')
    | '#skF_3' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_17130,c_15660])).

tff(c_17163,plain,(
    '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_15666,c_17157])).

tff(c_15683,plain,
    ( k2_relat_1('#skF_3') != '#skF_4'
    | '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_15647,c_15647,c_242])).

tff(c_15684,plain,(
    k2_relat_1('#skF_3') != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_15683])).

tff(c_17168,plain,(
    k2_relat_1('#skF_4') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_17163,c_15684])).

tff(c_17178,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_15671,c_17168])).

tff(c_17179,plain,(
    '#skF_3' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_15683])).

tff(c_38,plain,(
    ! [A_32] :
      ( k1_relat_1(A_32) != k1_xboole_0
      | k1_xboole_0 = A_32
      | ~ v1_relat_1(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_243,plain,
    ( k1_relat_1('#skF_3') != k1_xboole_0
    | k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_227,c_38])).

tff(c_15681,plain,
    ( k1_relat_1('#skF_3') != '#skF_4'
    | '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_15647,c_15647,c_243])).

tff(c_15682,plain,(
    k1_relat_1('#skF_3') != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_15681])).

tff(c_17181,plain,(
    k1_relat_1('#skF_4') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_17179,c_15682])).

tff(c_17374,plain,(
    ! [C_1143,B_1144,A_1145] :
      ( v5_relat_1(C_1143,B_1144)
      | ~ m1_subset_1(C_1143,k1_zfmisc_1(k2_zfmisc_1(A_1145,B_1144))) ) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_17387,plain,(
    v5_relat_1('#skF_4','#skF_2') ),
    inference(resolution,[status(thm)],[c_124,c_17374])).

tff(c_18135,plain,(
    ! [B_1243,A_1244] :
      ( k2_relat_1(B_1243) = A_1244
      | ~ v2_funct_2(B_1243,A_1244)
      | ~ v5_relat_1(B_1243,A_1244)
      | ~ v1_relat_1(B_1243) ) ),
    inference(cnfTransformation,[status(thm)],[f_200])).

tff(c_18144,plain,
    ( k2_relat_1('#skF_4') = '#skF_2'
    | ~ v2_funct_2('#skF_4','#skF_2')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_17387,c_18135])).

tff(c_18153,plain,
    ( '#skF_2' = '#skF_4'
    | ~ v2_funct_2('#skF_4','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_224,c_15671,c_18144])).

tff(c_18154,plain,(
    ~ v2_funct_2('#skF_4','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_18153])).

tff(c_18672,plain,(
    ! [C_1294,B_1295,A_1296] :
      ( v2_funct_2(C_1294,B_1295)
      | ~ v3_funct_2(C_1294,A_1296,B_1295)
      | ~ v1_funct_1(C_1294)
      | ~ m1_subset_1(C_1294,k1_zfmisc_1(k2_zfmisc_1(A_1296,B_1295))) ) ),
    inference(cnfTransformation,[status(thm)],[f_174])).

tff(c_18688,plain,
    ( v2_funct_2('#skF_4','#skF_2')
    | ~ v3_funct_2('#skF_4','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_124,c_18672])).

tff(c_18693,plain,(
    v2_funct_2('#skF_4','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_130,c_126,c_18688])).

tff(c_18695,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_18154,c_18693])).

tff(c_18696,plain,(
    '#skF_2' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_18153])).

tff(c_17235,plain,(
    ! [B_1119,A_1120] :
      ( ~ v1_xboole_0(B_1119)
      | B_1119 = A_1120
      | ~ r1_tarski(A_1120,B_1119) ) ),
    inference(resolution,[status(thm)],[c_15649,c_203])).

tff(c_17242,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1('#skF_2','#skF_2'))
    | k2_zfmisc_1('#skF_2','#skF_2') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_176,c_17235])).

tff(c_17317,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_2','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_17242])).

tff(c_17321,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_16,c_17317])).

tff(c_18703,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_18696,c_17321])).

tff(c_18714,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_15666,c_18703])).

tff(c_18715,plain,(
    k2_zfmisc_1('#skF_2','#skF_2') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_17242])).

tff(c_18729,plain,(
    r1_tarski(k6_partfun1('#skF_2'),'#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_18715,c_139])).

tff(c_18768,plain,
    ( ~ v1_xboole_0('#skF_4')
    | k6_partfun1('#skF_2') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_18729,c_15660])).

tff(c_18774,plain,(
    k6_partfun1('#skF_2') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_15666,c_18768])).

tff(c_18947,plain,(
    ! [C_1314,B_1315,A_1316] :
      ( v5_relat_1(C_1314,B_1315)
      | ~ m1_subset_1(C_1314,k1_zfmisc_1(k2_zfmisc_1(A_1316,B_1315))) ) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_18960,plain,(
    ! [A_1317] : v5_relat_1(k6_partfun1(A_1317),A_1317) ),
    inference(resolution,[status(thm)],[c_108,c_18947])).

tff(c_18963,plain,(
    v5_relat_1('#skF_4','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_18774,c_18960])).

tff(c_20303,plain,(
    ! [B_1456,A_1457] :
      ( k2_relat_1(B_1456) = A_1457
      | ~ v2_funct_2(B_1456,A_1457)
      | ~ v5_relat_1(B_1456,A_1457)
      | ~ v1_relat_1(B_1456) ) ),
    inference(cnfTransformation,[status(thm)],[f_200])).

tff(c_20312,plain,
    ( k2_relat_1('#skF_4') = '#skF_2'
    | ~ v2_funct_2('#skF_4','#skF_2')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_18963,c_20303])).

tff(c_20322,plain,
    ( '#skF_2' = '#skF_4'
    | ~ v2_funct_2('#skF_4','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_224,c_15671,c_20312])).

tff(c_20326,plain,(
    ~ v2_funct_2('#skF_4','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_20322])).

tff(c_18718,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18715,c_124])).

tff(c_21109,plain,(
    ! [C_1525,B_1526,A_1527] :
      ( v2_funct_2(C_1525,B_1526)
      | ~ v3_funct_2(C_1525,A_1527,B_1526)
      | ~ v1_funct_1(C_1525)
      | ~ m1_subset_1(C_1525,k1_zfmisc_1(k2_zfmisc_1(A_1527,B_1526))) ) ),
    inference(cnfTransformation,[status(thm)],[f_174])).

tff(c_21161,plain,(
    ! [C_1533] :
      ( v2_funct_2(C_1533,'#skF_2')
      | ~ v3_funct_2(C_1533,'#skF_2','#skF_2')
      | ~ v1_funct_1(C_1533)
      | ~ m1_subset_1(C_1533,k1_zfmisc_1('#skF_4')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18715,c_21109])).

tff(c_21164,plain,
    ( v2_funct_2('#skF_4','#skF_2')
    | ~ v3_funct_2('#skF_4','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_18718,c_21161])).

tff(c_21171,plain,(
    v2_funct_2('#skF_4','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_130,c_126,c_21164])).

tff(c_21173,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_20326,c_21171])).

tff(c_21174,plain,(
    '#skF_2' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_20322])).

tff(c_21190,plain,(
    v1_funct_2('#skF_4','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_21174,c_21174,c_128])).

tff(c_21187,plain,(
    k6_partfun1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_21174,c_18774])).

tff(c_21344,plain,(
    ! [A_1537,B_1538,C_1539] :
      ( k1_relset_1(A_1537,B_1538,C_1539) = k1_relat_1(C_1539)
      | ~ m1_subset_1(C_1539,k1_zfmisc_1(k2_zfmisc_1(A_1537,B_1538))) ) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_21414,plain,(
    ! [A_1546] : k1_relset_1(A_1546,A_1546,k6_partfun1(A_1546)) = k1_relat_1(k6_partfun1(A_1546)) ),
    inference(resolution,[status(thm)],[c_108,c_21344])).

tff(c_21423,plain,(
    k1_relat_1(k6_partfun1('#skF_4')) = k1_relset_1('#skF_4','#skF_4','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_21187,c_21414])).

tff(c_21426,plain,(
    k1_relset_1('#skF_4','#skF_4','#skF_4') = k1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_21187,c_21423])).

tff(c_86,plain,(
    ! [B_65,C_66] :
      ( k1_relset_1(k1_xboole_0,B_65,C_66) = k1_xboole_0
      | ~ v1_funct_2(C_66,k1_xboole_0,B_65)
      | ~ m1_subset_1(C_66,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_65))) ) ),
    inference(cnfTransformation,[status(thm)],[f_192])).

tff(c_21922,plain,(
    ! [B_1604,C_1605] :
      ( k1_relset_1('#skF_4',B_1604,C_1605) = '#skF_4'
      | ~ v1_funct_2(C_1605,'#skF_4',B_1604)
      | ~ m1_subset_1(C_1605,k1_zfmisc_1(k2_zfmisc_1('#skF_4',B_1604))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_15647,c_15647,c_15647,c_15647,c_86])).

tff(c_21929,plain,
    ( k1_relset_1('#skF_4','#skF_4',k6_partfun1('#skF_4')) = '#skF_4'
    | ~ v1_funct_2(k6_partfun1('#skF_4'),'#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_108,c_21922])).

tff(c_21936,plain,(
    k1_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_21190,c_21187,c_21426,c_21187,c_21929])).

tff(c_21938,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_17181,c_21936])).

tff(c_21939,plain,(
    '#skF_3' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_15681])).

tff(c_21944,plain,(
    ~ r2_relset_1('#skF_2','#skF_2','#skF_4',k2_funct_2('#skF_2','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_21939,c_120])).

tff(c_26079,plain,(
    ~ r2_relset_1('#skF_4','#skF_4','#skF_4',k2_funct_2('#skF_4','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26061,c_26061,c_26061,c_21944])).

tff(c_33585,plain,(
    ~ r2_relset_1('#skF_4','#skF_4','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_33583,c_26079])).

tff(c_33589,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_26065,c_33585])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:00:35 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 14.58/6.56  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 14.58/6.61  
% 14.58/6.61  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 14.58/6.61  %$ r2_relset_1 > v3_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > v1_partfun1 > r2_xboole_0 > r2_hidden > r1_tarski > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k8_relset_1 > k7_relset_1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k7_relat_1 > k5_relat_1 > k2_zfmisc_1 > k2_funct_2 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 14.58/6.61  
% 14.58/6.61  %Foreground sorts:
% 14.58/6.61  
% 14.58/6.61  
% 14.58/6.61  %Background operators:
% 14.58/6.61  
% 14.58/6.61  
% 14.58/6.61  %Foreground operators:
% 14.58/6.61  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 14.58/6.61  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 14.58/6.61  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 14.58/6.61  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 14.58/6.61  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 14.58/6.61  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 14.58/6.61  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 14.58/6.61  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 14.58/6.61  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 14.58/6.61  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 14.58/6.61  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 14.58/6.61  tff(k2_funct_2, type, k2_funct_2: ($i * $i) > $i).
% 14.58/6.61  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 14.58/6.61  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 14.58/6.61  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 14.58/6.61  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 14.58/6.61  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 14.58/6.61  tff('#skF_2', type, '#skF_2': $i).
% 14.58/6.61  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 14.58/6.61  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 14.58/6.61  tff('#skF_3', type, '#skF_3': $i).
% 14.58/6.61  tff(v2_funct_2, type, v2_funct_2: ($i * $i) > $o).
% 14.58/6.61  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 14.58/6.61  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 14.58/6.61  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 14.58/6.61  tff(r2_xboole_0, type, r2_xboole_0: ($i * $i) > $o).
% 14.58/6.61  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 14.58/6.61  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 14.58/6.61  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 14.58/6.61  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 14.58/6.61  tff('#skF_4', type, '#skF_4': $i).
% 14.58/6.61  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 14.58/6.61  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 14.58/6.61  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 14.58/6.61  tff(v3_funct_2, type, v3_funct_2: ($i * $i * $i) > $o).
% 14.58/6.61  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 14.58/6.61  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 14.58/6.61  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 14.58/6.61  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 14.58/6.61  
% 14.87/6.65  tff(f_76, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 14.87/6.65  tff(f_292, negated_conjecture, ~(![A, B]: ((((v1_funct_1(B) & v1_funct_2(B, A, A)) & v3_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (![C]: ((((v1_funct_1(C) & v1_funct_2(C, A, A)) & v3_funct_2(C, A, A)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (r2_relset_1(A, A, k1_partfun1(A, A, A, A, B, C), k6_partfun1(A)) => r2_relset_1(A, A, C, k2_funct_2(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t87_funct_2)).
% 14.87/6.65  tff(f_70, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 14.87/6.65  tff(f_148, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 14.87/6.65  tff(f_174, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v3_funct_2(C, A, B)) => ((v1_funct_1(C) & v2_funct_1(C)) & v2_funct_2(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_funct_2)).
% 14.87/6.65  tff(f_252, axiom, (![A, B]: ((((v1_funct_1(B) & v1_funct_2(B, A, A)) & v3_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (k2_funct_2(A, B) = k2_funct_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_funct_2)).
% 14.87/6.65  tff(f_228, axiom, (![A, B]: ((((v1_funct_1(B) & v1_funct_2(B, A, A)) & v3_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (((v1_funct_1(k2_funct_2(A, B)) & v1_funct_2(k2_funct_2(A, B), A, A)) & v3_funct_2(k2_funct_2(A, B), A, A)) & m1_subset_1(k2_funct_2(A, B), k1_zfmisc_1(k2_zfmisc_1(A, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_funct_2)).
% 14.87/6.65  tff(f_126, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 14.87/6.65  tff(f_132, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 14.87/6.65  tff(f_200, axiom, (![A, B]: ((v1_relat_1(B) & v5_relat_1(B, A)) => (v2_funct_2(B, A) <=> (k2_relat_1(B) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_funct_2)).
% 14.87/6.65  tff(f_254, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 14.87/6.65  tff(f_112, axiom, (![A]: (v1_relat_1(A) => (k5_relat_1(A, k6_relat_1(k2_relat_1(A))) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t80_relat_1)).
% 14.87/6.65  tff(f_104, axiom, (![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_relat_1)).
% 14.87/6.65  tff(f_86, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t209_relat_1)).
% 14.87/6.65  tff(f_80, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_relat_1)).
% 14.87/6.65  tff(f_140, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 14.87/6.65  tff(f_156, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((k7_relset_1(A, B, C, A) = k2_relset_1(A, B, C)) & (k8_relset_1(A, B, C, B) = k1_relset_1(A, B, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_relset_1)).
% 14.87/6.65  tff(f_270, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((k2_relset_1(A, B, C) = B) & v2_funct_1(C)) => ((B = k1_xboole_0) | ((k5_relat_1(C, k2_funct_1(C)) = k6_partfun1(A)) & (k5_relat_1(k2_funct_1(C), C) = k6_partfun1(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t35_funct_2)).
% 14.87/6.65  tff(f_212, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (v1_funct_1(k1_partfun1(A, B, C, D, E, F)) & m1_subset_1(k1_partfun1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 14.87/6.65  tff(f_232, axiom, (![A]: (v1_partfun1(k6_partfun1(A), A) & m1_subset_1(k6_partfun1(A), k1_zfmisc_1(k2_zfmisc_1(A, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_partfun1)).
% 14.87/6.65  tff(f_242, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 14.87/6.65  tff(f_96, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (k5_relat_1(k5_relat_1(A, B), C) = k5_relat_1(A, k5_relat_1(B, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_relat_1)).
% 14.87/6.65  tff(f_192, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 14.87/6.65  tff(f_136, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 14.87/6.65  tff(f_108, axiom, (![A]: (v1_relat_1(A) => (k5_relat_1(k6_relat_1(k1_relat_1(A)), A) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t78_relat_1)).
% 14.87/6.65  tff(f_120, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => (k2_funct_1(k2_funct_1(A)) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_funct_1)).
% 14.87/6.65  tff(f_33, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 14.87/6.65  tff(f_52, axiom, (![A, B]: (v1_xboole_0(B) => v1_xboole_0(k2_zfmisc_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc3_zfmisc_1)).
% 14.87/6.65  tff(f_56, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 14.87/6.65  tff(f_32, axiom, (![A, B]: (r2_xboole_0(A, B) <=> (r1_tarski(A, B) & ~(A = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_xboole_0)).
% 14.87/6.65  tff(f_43, axiom, (![A, B]: ~(r2_xboole_0(A, B) & (![C]: ~(r2_hidden(C, B) & ~r2_hidden(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_xboole_0)).
% 14.87/6.65  tff(f_48, axiom, (![A, B]: ~(r2_hidden(A, B) & v1_xboole_0(B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_boole)).
% 14.87/6.65  tff(f_150, axiom, (![A]: r1_tarski(k6_relat_1(A), k2_zfmisc_1(A, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_relset_1)).
% 14.87/6.65  tff(f_122, axiom, (![A]: (k2_funct_1(k6_relat_1(A)) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t67_funct_1)).
% 14.87/6.65  tff(c_28, plain, (![A_19, B_20]: (v1_relat_1(k2_zfmisc_1(A_19, B_20)))), inference(cnfTransformation, [status(thm)], [f_76])).
% 14.87/6.65  tff(c_124, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_292])).
% 14.87/6.65  tff(c_205, plain, (![B_116, A_117]: (v1_relat_1(B_116) | ~m1_subset_1(B_116, k1_zfmisc_1(A_117)) | ~v1_relat_1(A_117))), inference(cnfTransformation, [status(thm)], [f_70])).
% 14.87/6.65  tff(c_214, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_2'))), inference(resolution, [status(thm)], [c_124, c_205])).
% 14.87/6.65  tff(c_224, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_214])).
% 14.87/6.65  tff(c_602, plain, (![A_180, B_181, D_182]: (r2_relset_1(A_180, B_181, D_182, D_182) | ~m1_subset_1(D_182, k1_zfmisc_1(k2_zfmisc_1(A_180, B_181))))), inference(cnfTransformation, [status(thm)], [f_148])).
% 14.87/6.65  tff(c_614, plain, (r2_relset_1('#skF_2', '#skF_2', '#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_124, c_602])).
% 14.87/6.65  tff(c_130, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_292])).
% 14.87/6.65  tff(c_126, plain, (v3_funct_2('#skF_4', '#skF_2', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_292])).
% 14.87/6.65  tff(c_2514, plain, (![C_337, A_338, B_339]: (v2_funct_1(C_337) | ~v3_funct_2(C_337, A_338, B_339) | ~v1_funct_1(C_337) | ~m1_subset_1(C_337, k1_zfmisc_1(k2_zfmisc_1(A_338, B_339))))), inference(cnfTransformation, [status(thm)], [f_174])).
% 14.87/6.65  tff(c_2527, plain, (v2_funct_1('#skF_4') | ~v3_funct_2('#skF_4', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_124, c_2514])).
% 14.87/6.65  tff(c_2535, plain, (v2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_130, c_126, c_2527])).
% 14.87/6.65  tff(c_128, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_292])).
% 14.87/6.65  tff(c_6117, plain, (![A_526, B_527]: (k2_funct_2(A_526, B_527)=k2_funct_1(B_527) | ~m1_subset_1(B_527, k1_zfmisc_1(k2_zfmisc_1(A_526, A_526))) | ~v3_funct_2(B_527, A_526, A_526) | ~v1_funct_2(B_527, A_526, A_526) | ~v1_funct_1(B_527))), inference(cnfTransformation, [status(thm)], [f_252])).
% 14.87/6.65  tff(c_6139, plain, (k2_funct_2('#skF_2', '#skF_4')=k2_funct_1('#skF_4') | ~v3_funct_2('#skF_4', '#skF_2', '#skF_2') | ~v1_funct_2('#skF_4', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_124, c_6117])).
% 14.87/6.65  tff(c_6148, plain, (k2_funct_2('#skF_2', '#skF_4')=k2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_130, c_128, c_126, c_6139])).
% 14.87/6.65  tff(c_6896, plain, (![A_575, B_576]: (m1_subset_1(k2_funct_2(A_575, B_576), k1_zfmisc_1(k2_zfmisc_1(A_575, A_575))) | ~m1_subset_1(B_576, k1_zfmisc_1(k2_zfmisc_1(A_575, A_575))) | ~v3_funct_2(B_576, A_575, A_575) | ~v1_funct_2(B_576, A_575, A_575) | ~v1_funct_1(B_576))), inference(cnfTransformation, [status(thm)], [f_228])).
% 14.87/6.65  tff(c_6976, plain, (m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'))) | ~v3_funct_2('#skF_4', '#skF_2', '#skF_2') | ~v1_funct_2('#skF_4', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_6148, c_6896])).
% 14.87/6.65  tff(c_7024, plain, (m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_130, c_128, c_126, c_124, c_6976])).
% 14.87/6.65  tff(c_48, plain, (![C_39, A_37, B_38]: (v1_relat_1(C_39) | ~m1_subset_1(C_39, k1_zfmisc_1(k2_zfmisc_1(A_37, B_38))))), inference(cnfTransformation, [status(thm)], [f_126])).
% 14.87/6.65  tff(c_7483, plain, (v1_relat_1(k2_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_7024, c_48])).
% 14.87/6.65  tff(c_132, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_292])).
% 14.87/6.65  tff(c_217, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_2'))), inference(resolution, [status(thm)], [c_132, c_205])).
% 14.87/6.65  tff(c_227, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_217])).
% 14.87/6.65  tff(c_387, plain, (![C_139, B_140, A_141]: (v5_relat_1(C_139, B_140) | ~m1_subset_1(C_139, k1_zfmisc_1(k2_zfmisc_1(A_141, B_140))))), inference(cnfTransformation, [status(thm)], [f_132])).
% 14.87/6.65  tff(c_404, plain, (v5_relat_1('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_132, c_387])).
% 14.87/6.65  tff(c_617, plain, (![B_184, A_185]: (k2_relat_1(B_184)=A_185 | ~v2_funct_2(B_184, A_185) | ~v5_relat_1(B_184, A_185) | ~v1_relat_1(B_184))), inference(cnfTransformation, [status(thm)], [f_200])).
% 14.87/6.65  tff(c_623, plain, (k2_relat_1('#skF_3')='#skF_2' | ~v2_funct_2('#skF_3', '#skF_2') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_404, c_617])).
% 14.87/6.65  tff(c_632, plain, (k2_relat_1('#skF_3')='#skF_2' | ~v2_funct_2('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_227, c_623])).
% 14.87/6.65  tff(c_636, plain, (~v2_funct_2('#skF_3', '#skF_2')), inference(splitLeft, [status(thm)], [c_632])).
% 14.87/6.65  tff(c_138, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_292])).
% 14.87/6.65  tff(c_134, plain, (v3_funct_2('#skF_3', '#skF_2', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_292])).
% 14.87/6.65  tff(c_1630, plain, (![C_267, B_268, A_269]: (v2_funct_2(C_267, B_268) | ~v3_funct_2(C_267, A_269, B_268) | ~v1_funct_1(C_267) | ~m1_subset_1(C_267, k1_zfmisc_1(k2_zfmisc_1(A_269, B_268))))), inference(cnfTransformation, [status(thm)], [f_174])).
% 14.87/6.65  tff(c_1649, plain, (v2_funct_2('#skF_3', '#skF_2') | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_132, c_1630])).
% 14.87/6.65  tff(c_1657, plain, (v2_funct_2('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_138, c_134, c_1649])).
% 14.87/6.65  tff(c_1659, plain, $false, inference(negUnitSimplification, [status(thm)], [c_636, c_1657])).
% 14.87/6.65  tff(c_1660, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(splitRight, [status(thm)], [c_632])).
% 14.87/6.65  tff(c_114, plain, (![A_86]: (k6_relat_1(A_86)=k6_partfun1(A_86))), inference(cnfTransformation, [status(thm)], [f_254])).
% 14.87/6.65  tff(c_42, plain, (![A_34]: (k5_relat_1(A_34, k6_relat_1(k2_relat_1(A_34)))=A_34 | ~v1_relat_1(A_34))), inference(cnfTransformation, [status(thm)], [f_112])).
% 14.87/6.65  tff(c_141, plain, (![A_34]: (k5_relat_1(A_34, k6_partfun1(k2_relat_1(A_34)))=A_34 | ~v1_relat_1(A_34))), inference(demodulation, [status(thm), theory('equality')], [c_114, c_42])).
% 14.87/6.65  tff(c_1670, plain, (k5_relat_1('#skF_3', k6_partfun1('#skF_2'))='#skF_3' | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1660, c_141])).
% 14.87/6.65  tff(c_1679, plain, (k5_relat_1('#skF_3', k6_partfun1('#skF_2'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_227, c_1670])).
% 14.87/6.65  tff(c_36, plain, (![A_32]: (k2_relat_1(A_32)!=k1_xboole_0 | k1_xboole_0=A_32 | ~v1_relat_1(A_32))), inference(cnfTransformation, [status(thm)], [f_104])).
% 14.87/6.65  tff(c_242, plain, (k2_relat_1('#skF_3')!=k1_xboole_0 | k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_227, c_36])).
% 14.87/6.65  tff(c_271, plain, (k2_relat_1('#skF_3')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_242])).
% 14.87/6.65  tff(c_1663, plain, (k1_xboole_0!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_1660, c_271])).
% 14.87/6.65  tff(c_403, plain, (v5_relat_1('#skF_4', '#skF_2')), inference(resolution, [status(thm)], [c_124, c_387])).
% 14.87/6.65  tff(c_626, plain, (k2_relat_1('#skF_4')='#skF_2' | ~v2_funct_2('#skF_4', '#skF_2') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_403, c_617])).
% 14.87/6.65  tff(c_635, plain, (k2_relat_1('#skF_4')='#skF_2' | ~v2_funct_2('#skF_4', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_224, c_626])).
% 14.87/6.65  tff(c_1682, plain, (~v2_funct_2('#skF_4', '#skF_2')), inference(splitLeft, [status(thm)], [c_635])).
% 14.87/6.65  tff(c_2175, plain, (![C_309, B_310, A_311]: (v2_funct_2(C_309, B_310) | ~v3_funct_2(C_309, A_311, B_310) | ~v1_funct_1(C_309) | ~m1_subset_1(C_309, k1_zfmisc_1(k2_zfmisc_1(A_311, B_310))))), inference(cnfTransformation, [status(thm)], [f_174])).
% 14.87/6.65  tff(c_2191, plain, (v2_funct_2('#skF_4', '#skF_2') | ~v3_funct_2('#skF_4', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_124, c_2175])).
% 14.87/6.65  tff(c_2199, plain, (v2_funct_2('#skF_4', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_130, c_126, c_2191])).
% 14.87/6.65  tff(c_2201, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1682, c_2199])).
% 14.87/6.65  tff(c_2202, plain, (k2_relat_1('#skF_4')='#skF_2'), inference(splitRight, [status(thm)], [c_635])).
% 14.87/6.65  tff(c_441, plain, (![C_153, A_154, B_155]: (v4_relat_1(C_153, A_154) | ~m1_subset_1(C_153, k1_zfmisc_1(k2_zfmisc_1(A_154, B_155))))), inference(cnfTransformation, [status(thm)], [f_132])).
% 14.87/6.65  tff(c_457, plain, (v4_relat_1('#skF_4', '#skF_2')), inference(resolution, [status(thm)], [c_124, c_441])).
% 14.87/6.65  tff(c_32, plain, (![B_24, A_23]: (k7_relat_1(B_24, A_23)=B_24 | ~v4_relat_1(B_24, A_23) | ~v1_relat_1(B_24))), inference(cnfTransformation, [status(thm)], [f_86])).
% 14.87/6.65  tff(c_461, plain, (k7_relat_1('#skF_4', '#skF_2')='#skF_4' | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_457, c_32])).
% 14.87/6.65  tff(c_464, plain, (k7_relat_1('#skF_4', '#skF_2')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_224, c_461])).
% 14.87/6.65  tff(c_30, plain, (![B_22, A_21]: (k2_relat_1(k7_relat_1(B_22, A_21))=k9_relat_1(B_22, A_21) | ~v1_relat_1(B_22))), inference(cnfTransformation, [status(thm)], [f_80])).
% 14.87/6.65  tff(c_481, plain, (k9_relat_1('#skF_4', '#skF_2')=k2_relat_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_464, c_30])).
% 14.87/6.65  tff(c_485, plain, (k9_relat_1('#skF_4', '#skF_2')=k2_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_224, c_481])).
% 14.87/6.65  tff(c_2204, plain, (k9_relat_1('#skF_4', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_2202, c_485])).
% 14.87/6.65  tff(c_2449, plain, (![A_328, B_329, C_330, D_331]: (k7_relset_1(A_328, B_329, C_330, D_331)=k9_relat_1(C_330, D_331) | ~m1_subset_1(C_330, k1_zfmisc_1(k2_zfmisc_1(A_328, B_329))))), inference(cnfTransformation, [status(thm)], [f_140])).
% 14.87/6.65  tff(c_2463, plain, (![D_331]: (k7_relset_1('#skF_2', '#skF_2', '#skF_4', D_331)=k9_relat_1('#skF_4', D_331))), inference(resolution, [status(thm)], [c_124, c_2449])).
% 14.87/6.65  tff(c_2752, plain, (![A_355, B_356, C_357]: (k7_relset_1(A_355, B_356, C_357, A_355)=k2_relset_1(A_355, B_356, C_357) | ~m1_subset_1(C_357, k1_zfmisc_1(k2_zfmisc_1(A_355, B_356))))), inference(cnfTransformation, [status(thm)], [f_156])).
% 14.87/6.65  tff(c_2763, plain, (k7_relset_1('#skF_2', '#skF_2', '#skF_4', '#skF_2')=k2_relset_1('#skF_2', '#skF_2', '#skF_4')), inference(resolution, [status(thm)], [c_124, c_2752])).
% 14.87/6.65  tff(c_2769, plain, (k2_relset_1('#skF_2', '#skF_2', '#skF_4')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_2204, c_2463, c_2763])).
% 14.87/6.65  tff(c_7488, plain, (![A_586, C_587, B_588]: (k6_partfun1(A_586)=k5_relat_1(C_587, k2_funct_1(C_587)) | k1_xboole_0=B_588 | ~v2_funct_1(C_587) | k2_relset_1(A_586, B_588, C_587)!=B_588 | ~m1_subset_1(C_587, k1_zfmisc_1(k2_zfmisc_1(A_586, B_588))) | ~v1_funct_2(C_587, A_586, B_588) | ~v1_funct_1(C_587))), inference(cnfTransformation, [status(thm)], [f_270])).
% 14.87/6.65  tff(c_7511, plain, (k5_relat_1('#skF_4', k2_funct_1('#skF_4'))=k6_partfun1('#skF_2') | k1_xboole_0='#skF_2' | ~v2_funct_1('#skF_4') | k2_relset_1('#skF_2', '#skF_2', '#skF_4')!='#skF_2' | ~v1_funct_2('#skF_4', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_124, c_7488])).
% 14.87/6.65  tff(c_7529, plain, (k5_relat_1('#skF_4', k2_funct_1('#skF_4'))=k6_partfun1('#skF_2') | k1_xboole_0='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_130, c_128, c_2769, c_2535, c_7511])).
% 14.87/6.65  tff(c_7530, plain, (k5_relat_1('#skF_4', k2_funct_1('#skF_4'))=k6_partfun1('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_1663, c_7529])).
% 14.87/6.65  tff(c_5518, plain, (![C_503, E_502, F_499, A_500, D_501, B_498]: (m1_subset_1(k1_partfun1(A_500, B_498, C_503, D_501, E_502, F_499), k1_zfmisc_1(k2_zfmisc_1(A_500, D_501))) | ~m1_subset_1(F_499, k1_zfmisc_1(k2_zfmisc_1(C_503, D_501))) | ~v1_funct_1(F_499) | ~m1_subset_1(E_502, k1_zfmisc_1(k2_zfmisc_1(A_500, B_498))) | ~v1_funct_1(E_502))), inference(cnfTransformation, [status(thm)], [f_212])).
% 14.87/6.65  tff(c_108, plain, (![A_77]: (m1_subset_1(k6_partfun1(A_77), k1_zfmisc_1(k2_zfmisc_1(A_77, A_77))))), inference(cnfTransformation, [status(thm)], [f_232])).
% 14.87/6.65  tff(c_122, plain, (r2_relset_1('#skF_2', '#skF_2', k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', '#skF_3', '#skF_4'), k6_partfun1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_292])).
% 14.87/6.65  tff(c_3599, plain, (![D_413, C_414, A_415, B_416]: (D_413=C_414 | ~r2_relset_1(A_415, B_416, C_414, D_413) | ~m1_subset_1(D_413, k1_zfmisc_1(k2_zfmisc_1(A_415, B_416))) | ~m1_subset_1(C_414, k1_zfmisc_1(k2_zfmisc_1(A_415, B_416))))), inference(cnfTransformation, [status(thm)], [f_148])).
% 14.87/6.65  tff(c_3607, plain, (k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', '#skF_3', '#skF_4')=k6_partfun1('#skF_2') | ~m1_subset_1(k6_partfun1('#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'))) | ~m1_subset_1(k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(resolution, [status(thm)], [c_122, c_3599])).
% 14.87/6.65  tff(c_3622, plain, (k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', '#skF_3', '#skF_4')=k6_partfun1('#skF_2') | ~m1_subset_1(k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_108, c_3607])).
% 14.87/6.65  tff(c_3707, plain, (~m1_subset_1(k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(splitLeft, [status(thm)], [c_3622])).
% 14.87/6.65  tff(c_5549, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_5518, c_3707])).
% 14.87/6.65  tff(c_5634, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_138, c_132, c_130, c_124, c_5549])).
% 14.87/6.65  tff(c_5635, plain, (k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', '#skF_3', '#skF_4')=k6_partfun1('#skF_2')), inference(splitRight, [status(thm)], [c_3622])).
% 14.87/6.65  tff(c_7269, plain, (![D_582, F_583, B_584, E_585, A_580, C_581]: (k1_partfun1(A_580, B_584, C_581, D_582, E_585, F_583)=k5_relat_1(E_585, F_583) | ~m1_subset_1(F_583, k1_zfmisc_1(k2_zfmisc_1(C_581, D_582))) | ~v1_funct_1(F_583) | ~m1_subset_1(E_585, k1_zfmisc_1(k2_zfmisc_1(A_580, B_584))) | ~v1_funct_1(E_585))), inference(cnfTransformation, [status(thm)], [f_242])).
% 14.87/6.65  tff(c_7290, plain, (![A_580, B_584, E_585]: (k1_partfun1(A_580, B_584, '#skF_2', '#skF_2', E_585, '#skF_4')=k5_relat_1(E_585, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_585, k1_zfmisc_1(k2_zfmisc_1(A_580, B_584))) | ~v1_funct_1(E_585))), inference(resolution, [status(thm)], [c_124, c_7269])).
% 14.87/6.65  tff(c_7698, plain, (![A_592, B_593, E_594]: (k1_partfun1(A_592, B_593, '#skF_2', '#skF_2', E_594, '#skF_4')=k5_relat_1(E_594, '#skF_4') | ~m1_subset_1(E_594, k1_zfmisc_1(k2_zfmisc_1(A_592, B_593))) | ~v1_funct_1(E_594))), inference(demodulation, [status(thm), theory('equality')], [c_130, c_7290])).
% 14.87/6.65  tff(c_7735, plain, (k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_132, c_7698])).
% 14.87/6.65  tff(c_7750, plain, (k5_relat_1('#skF_3', '#skF_4')=k6_partfun1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_138, c_5635, c_7735])).
% 14.87/6.65  tff(c_34, plain, (![A_25, B_29, C_31]: (k5_relat_1(k5_relat_1(A_25, B_29), C_31)=k5_relat_1(A_25, k5_relat_1(B_29, C_31)) | ~v1_relat_1(C_31) | ~v1_relat_1(B_29) | ~v1_relat_1(A_25))), inference(cnfTransformation, [status(thm)], [f_96])).
% 14.87/6.65  tff(c_7764, plain, (![C_31]: (k5_relat_1(k6_partfun1('#skF_2'), C_31)=k5_relat_1('#skF_3', k5_relat_1('#skF_4', C_31)) | ~v1_relat_1(C_31) | ~v1_relat_1('#skF_4') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_7750, c_34])).
% 14.87/6.65  tff(c_12469, plain, (![C_713]: (k5_relat_1(k6_partfun1('#skF_2'), C_713)=k5_relat_1('#skF_3', k5_relat_1('#skF_4', C_713)) | ~v1_relat_1(C_713))), inference(demodulation, [status(thm), theory('equality')], [c_227, c_224, c_7764])).
% 14.87/6.65  tff(c_6229, plain, (![A_538, B_539]: (v1_funct_2(k2_funct_2(A_538, B_539), A_538, A_538) | ~m1_subset_1(B_539, k1_zfmisc_1(k2_zfmisc_1(A_538, A_538))) | ~v3_funct_2(B_539, A_538, A_538) | ~v1_funct_2(B_539, A_538, A_538) | ~v1_funct_1(B_539))), inference(cnfTransformation, [status(thm)], [f_228])).
% 14.87/6.65  tff(c_6244, plain, (v1_funct_2(k2_funct_2('#skF_2', '#skF_4'), '#skF_2', '#skF_2') | ~v3_funct_2('#skF_4', '#skF_2', '#skF_2') | ~v1_funct_2('#skF_4', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_124, c_6229])).
% 14.87/6.65  tff(c_6251, plain, (v1_funct_2(k2_funct_1('#skF_4'), '#skF_2', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_130, c_128, c_126, c_6148, c_6244])).
% 14.87/6.65  tff(c_88, plain, (![B_65, A_64, C_66]: (k1_xboole_0=B_65 | k1_relset_1(A_64, B_65, C_66)=A_64 | ~v1_funct_2(C_66, A_64, B_65) | ~m1_subset_1(C_66, k1_zfmisc_1(k2_zfmisc_1(A_64, B_65))))), inference(cnfTransformation, [status(thm)], [f_192])).
% 14.87/6.65  tff(c_7401, plain, (k1_xboole_0='#skF_2' | k1_relset_1('#skF_2', '#skF_2', k2_funct_1('#skF_4'))='#skF_2' | ~v1_funct_2(k2_funct_1('#skF_4'), '#skF_2', '#skF_2')), inference(resolution, [status(thm)], [c_7024, c_88])).
% 14.87/6.65  tff(c_7467, plain, (k1_xboole_0='#skF_2' | k1_relset_1('#skF_2', '#skF_2', k2_funct_1('#skF_4'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_6251, c_7401])).
% 14.87/6.65  tff(c_7468, plain, (k1_relset_1('#skF_2', '#skF_2', k2_funct_1('#skF_4'))='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_1663, c_7467])).
% 14.87/6.65  tff(c_54, plain, (![A_43, B_44, C_45]: (k1_relset_1(A_43, B_44, C_45)=k1_relat_1(C_45) | ~m1_subset_1(C_45, k1_zfmisc_1(k2_zfmisc_1(A_43, B_44))))), inference(cnfTransformation, [status(thm)], [f_136])).
% 14.87/6.65  tff(c_7478, plain, (k1_relset_1('#skF_2', '#skF_2', k2_funct_1('#skF_4'))=k1_relat_1(k2_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_7024, c_54])).
% 14.87/6.65  tff(c_9309, plain, (k1_relat_1(k2_funct_1('#skF_4'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_7468, c_7478])).
% 14.87/6.65  tff(c_40, plain, (![A_33]: (k5_relat_1(k6_relat_1(k1_relat_1(A_33)), A_33)=A_33 | ~v1_relat_1(A_33))), inference(cnfTransformation, [status(thm)], [f_108])).
% 14.87/6.65  tff(c_142, plain, (![A_33]: (k5_relat_1(k6_partfun1(k1_relat_1(A_33)), A_33)=A_33 | ~v1_relat_1(A_33))), inference(demodulation, [status(thm), theory('equality')], [c_114, c_40])).
% 14.87/6.65  tff(c_9317, plain, (k5_relat_1(k6_partfun1('#skF_2'), k2_funct_1('#skF_4'))=k2_funct_1('#skF_4') | ~v1_relat_1(k2_funct_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_9309, c_142])).
% 14.87/6.65  tff(c_9323, plain, (k5_relat_1(k6_partfun1('#skF_2'), k2_funct_1('#skF_4'))=k2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_7483, c_9317])).
% 14.87/6.65  tff(c_12490, plain, (k5_relat_1('#skF_3', k5_relat_1('#skF_4', k2_funct_1('#skF_4')))=k2_funct_1('#skF_4') | ~v1_relat_1(k2_funct_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_12469, c_9323])).
% 14.87/6.65  tff(c_12615, plain, (k2_funct_1('#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_7483, c_1679, c_7530, c_12490])).
% 14.87/6.65  tff(c_44, plain, (![A_35]: (k2_funct_1(k2_funct_1(A_35))=A_35 | ~v2_funct_1(A_35) | ~v1_funct_1(A_35) | ~v1_relat_1(A_35))), inference(cnfTransformation, [status(thm)], [f_120])).
% 14.87/6.65  tff(c_12719, plain, (k2_funct_1('#skF_3')='#skF_4' | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_12615, c_44])).
% 14.87/6.65  tff(c_12723, plain, (k2_funct_1('#skF_3')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_224, c_130, c_2535, c_12719])).
% 14.87/6.65  tff(c_136, plain, (v1_funct_2('#skF_3', '#skF_2', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_292])).
% 14.87/6.65  tff(c_6142, plain, (k2_funct_2('#skF_2', '#skF_3')=k2_funct_1('#skF_3') | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_132, c_6117])).
% 14.87/6.65  tff(c_6151, plain, (k2_funct_2('#skF_2', '#skF_3')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_138, c_136, c_134, c_6142])).
% 14.87/6.65  tff(c_120, plain, (~r2_relset_1('#skF_2', '#skF_2', '#skF_4', k2_funct_2('#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_292])).
% 14.87/6.65  tff(c_6158, plain, (~r2_relset_1('#skF_2', '#skF_2', '#skF_4', k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_6151, c_120])).
% 14.87/6.65  tff(c_12889, plain, (~r2_relset_1('#skF_2', '#skF_2', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_12723, c_6158])).
% 14.87/6.65  tff(c_12917, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_614, c_12889])).
% 14.87/6.65  tff(c_12918, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_242])).
% 14.87/6.65  tff(c_8, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 14.87/6.65  tff(c_12925, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_12918, c_8])).
% 14.87/6.65  tff(c_12919, plain, (k2_relat_1('#skF_3')=k1_xboole_0), inference(splitRight, [status(thm)], [c_242])).
% 14.87/6.65  tff(c_12930, plain, (k2_relat_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_12918, c_12919])).
% 14.87/6.65  tff(c_13206, plain, (![C_747, B_748, A_749]: (v5_relat_1(C_747, B_748) | ~m1_subset_1(C_747, k1_zfmisc_1(k2_zfmisc_1(A_749, B_748))))), inference(cnfTransformation, [status(thm)], [f_132])).
% 14.87/6.65  tff(c_13223, plain, (v5_relat_1('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_132, c_13206])).
% 14.87/6.65  tff(c_14456, plain, (![B_876, A_877]: (k2_relat_1(B_876)=A_877 | ~v2_funct_2(B_876, A_877) | ~v5_relat_1(B_876, A_877) | ~v1_relat_1(B_876))), inference(cnfTransformation, [status(thm)], [f_200])).
% 14.87/6.65  tff(c_14465, plain, (k2_relat_1('#skF_3')='#skF_2' | ~v2_funct_2('#skF_3', '#skF_2') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_13223, c_14456])).
% 14.87/6.65  tff(c_14477, plain, ('#skF_2'='#skF_3' | ~v2_funct_2('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_227, c_12930, c_14465])).
% 14.87/6.65  tff(c_14481, plain, (~v2_funct_2('#skF_3', '#skF_2')), inference(splitLeft, [status(thm)], [c_14477])).
% 14.87/6.65  tff(c_15461, plain, (![C_956, B_957, A_958]: (v2_funct_2(C_956, B_957) | ~v3_funct_2(C_956, A_958, B_957) | ~v1_funct_1(C_956) | ~m1_subset_1(C_956, k1_zfmisc_1(k2_zfmisc_1(A_958, B_957))))), inference(cnfTransformation, [status(thm)], [f_174])).
% 14.87/6.65  tff(c_15480, plain, (v2_funct_2('#skF_3', '#skF_2') | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_132, c_15461])).
% 14.87/6.65  tff(c_15488, plain, (v2_funct_2('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_138, c_134, c_15480])).
% 14.87/6.65  tff(c_15490, plain, $false, inference(negUnitSimplification, [status(thm)], [c_14481, c_15488])).
% 14.87/6.65  tff(c_15491, plain, ('#skF_2'='#skF_3'), inference(splitRight, [status(thm)], [c_14477])).
% 14.87/6.65  tff(c_16, plain, (![A_8, B_9]: (v1_xboole_0(k2_zfmisc_1(A_8, B_9)) | ~v1_xboole_0(B_9))), inference(cnfTransformation, [status(thm)], [f_52])).
% 14.87/6.65  tff(c_169, plain, (![A_105, B_106]: (r1_tarski(A_105, B_106) | ~m1_subset_1(A_105, k1_zfmisc_1(B_106)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 14.87/6.65  tff(c_177, plain, (r1_tarski('#skF_3', k2_zfmisc_1('#skF_2', '#skF_2'))), inference(resolution, [status(thm)], [c_132, c_169])).
% 14.87/6.65  tff(c_254, plain, (![A_119, B_120]: (r2_xboole_0(A_119, B_120) | B_120=A_119 | ~r1_tarski(A_119, B_120))), inference(cnfTransformation, [status(thm)], [f_32])).
% 14.87/6.65  tff(c_199, plain, (![A_112, B_113]: (r2_hidden('#skF_1'(A_112, B_113), B_113) | ~r2_xboole_0(A_112, B_113))), inference(cnfTransformation, [status(thm)], [f_43])).
% 14.87/6.65  tff(c_14, plain, (![B_7, A_6]: (~v1_xboole_0(B_7) | ~r2_hidden(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_48])).
% 14.87/6.65  tff(c_203, plain, (![B_113, A_112]: (~v1_xboole_0(B_113) | ~r2_xboole_0(A_112, B_113))), inference(resolution, [status(thm)], [c_199, c_14])).
% 14.87/6.65  tff(c_12989, plain, (![B_722, A_723]: (~v1_xboole_0(B_722) | B_722=A_723 | ~r1_tarski(A_723, B_722))), inference(resolution, [status(thm)], [c_254, c_203])).
% 14.87/6.65  tff(c_12999, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_2', '#skF_2')) | k2_zfmisc_1('#skF_2', '#skF_2')='#skF_3'), inference(resolution, [status(thm)], [c_177, c_12989])).
% 14.87/6.65  tff(c_13002, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_2', '#skF_2'))), inference(splitLeft, [status(thm)], [c_12999])).
% 14.87/6.65  tff(c_13006, plain, (~v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_16, c_13002])).
% 14.87/6.65  tff(c_15503, plain, (~v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_15491, c_13006])).
% 14.87/6.65  tff(c_15518, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12925, c_15503])).
% 14.87/6.65  tff(c_15519, plain, (k2_zfmisc_1('#skF_2', '#skF_2')='#skF_3'), inference(splitRight, [status(thm)], [c_12999])).
% 14.87/6.65  tff(c_176, plain, (r1_tarski('#skF_4', k2_zfmisc_1('#skF_2', '#skF_2'))), inference(resolution, [status(thm)], [c_124, c_169])).
% 14.87/6.65  tff(c_15522, plain, (r1_tarski('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_15519, c_176])).
% 14.87/6.65  tff(c_265, plain, (![B_120, A_119]: (~v1_xboole_0(B_120) | B_120=A_119 | ~r1_tarski(A_119, B_120))), inference(resolution, [status(thm)], [c_254, c_203])).
% 14.87/6.65  tff(c_15557, plain, (~v1_xboole_0('#skF_3') | '#skF_3'='#skF_4'), inference(resolution, [status(thm)], [c_15522, c_265])).
% 14.87/6.65  tff(c_15563, plain, ('#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_12925, c_15557])).
% 14.87/6.65  tff(c_15576, plain, (k2_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_15563, c_15563, c_12930])).
% 14.87/6.65  tff(c_234, plain, (k2_relat_1('#skF_4')!=k1_xboole_0 | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_224, c_36])).
% 14.87/6.65  tff(c_253, plain, (k2_relat_1('#skF_4')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_234])).
% 14.87/6.65  tff(c_12922, plain, (k2_relat_1('#skF_4')!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_12918, c_253])).
% 14.87/6.65  tff(c_15575, plain, (k2_relat_1('#skF_4')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_15563, c_12922])).
% 14.87/6.65  tff(c_15646, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_15576, c_15575])).
% 14.87/6.65  tff(c_15647, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_234])).
% 14.87/6.65  tff(c_15648, plain, (k2_relat_1('#skF_4')=k1_xboole_0), inference(splitRight, [status(thm)], [c_234])).
% 14.87/6.65  tff(c_15671, plain, (k2_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_15647, c_15648])).
% 14.87/6.65  tff(c_15666, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_15647, c_8])).
% 14.87/6.65  tff(c_22163, plain, (![C_1635, B_1636, A_1637]: (v5_relat_1(C_1635, B_1636) | ~m1_subset_1(C_1635, k1_zfmisc_1(k2_zfmisc_1(A_1637, B_1636))))), inference(cnfTransformation, [status(thm)], [f_132])).
% 14.87/6.65  tff(c_22176, plain, (v5_relat_1('#skF_4', '#skF_2')), inference(resolution, [status(thm)], [c_124, c_22163])).
% 14.87/6.65  tff(c_22851, plain, (![B_1728, A_1729]: (k2_relat_1(B_1728)=A_1729 | ~v2_funct_2(B_1728, A_1729) | ~v5_relat_1(B_1728, A_1729) | ~v1_relat_1(B_1728))), inference(cnfTransformation, [status(thm)], [f_200])).
% 14.87/6.65  tff(c_22860, plain, (k2_relat_1('#skF_4')='#skF_2' | ~v2_funct_2('#skF_4', '#skF_2') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_22176, c_22851])).
% 14.87/6.65  tff(c_22869, plain, ('#skF_2'='#skF_4' | ~v2_funct_2('#skF_4', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_224, c_15671, c_22860])).
% 14.87/6.65  tff(c_22870, plain, (~v2_funct_2('#skF_4', '#skF_2')), inference(splitLeft, [status(thm)], [c_22869])).
% 14.87/6.65  tff(c_23337, plain, (![C_1770, B_1771, A_1772]: (v2_funct_2(C_1770, B_1771) | ~v3_funct_2(C_1770, A_1772, B_1771) | ~v1_funct_1(C_1770) | ~m1_subset_1(C_1770, k1_zfmisc_1(k2_zfmisc_1(A_1772, B_1771))))), inference(cnfTransformation, [status(thm)], [f_174])).
% 14.87/6.65  tff(c_23353, plain, (v2_funct_2('#skF_4', '#skF_2') | ~v3_funct_2('#skF_4', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_124, c_23337])).
% 14.87/6.65  tff(c_23358, plain, (v2_funct_2('#skF_4', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_130, c_126, c_23353])).
% 14.87/6.65  tff(c_23360, plain, $false, inference(negUnitSimplification, [status(thm)], [c_22870, c_23358])).
% 14.87/6.65  tff(c_23361, plain, ('#skF_2'='#skF_4'), inference(splitRight, [status(thm)], [c_22869])).
% 14.87/6.65  tff(c_15649, plain, (![A_960, B_961]: (r2_xboole_0(A_960, B_961) | B_961=A_960 | ~r1_tarski(A_960, B_961))), inference(cnfTransformation, [status(thm)], [f_32])).
% 14.87/6.65  tff(c_22044, plain, (![B_1618, A_1619]: (~v1_xboole_0(B_1618) | B_1618=A_1619 | ~r1_tarski(A_1619, B_1618))), inference(resolution, [status(thm)], [c_15649, c_203])).
% 14.87/6.65  tff(c_22051, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_2', '#skF_2')) | k2_zfmisc_1('#skF_2', '#skF_2')='#skF_4'), inference(resolution, [status(thm)], [c_176, c_22044])).
% 14.87/6.65  tff(c_22110, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_2', '#skF_2'))), inference(splitLeft, [status(thm)], [c_22051])).
% 14.87/6.65  tff(c_22114, plain, (~v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_16, c_22110])).
% 14.87/6.65  tff(c_23368, plain, (~v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_23361, c_22114])).
% 14.87/6.65  tff(c_23379, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_15666, c_23368])).
% 14.87/6.65  tff(c_23380, plain, (k2_zfmisc_1('#skF_2', '#skF_2')='#skF_4'), inference(splitRight, [status(thm)], [c_22051])).
% 14.87/6.65  tff(c_23383, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_23380, c_124])).
% 14.87/6.65  tff(c_23610, plain, (![C_1791, B_1792, A_1793]: (v5_relat_1(C_1791, B_1792) | ~m1_subset_1(C_1791, k1_zfmisc_1(k2_zfmisc_1(A_1793, B_1792))))), inference(cnfTransformation, [status(thm)], [f_132])).
% 14.87/6.65  tff(c_23639, plain, (![C_1797]: (v5_relat_1(C_1797, '#skF_2') | ~m1_subset_1(C_1797, k1_zfmisc_1('#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_23380, c_23610])).
% 14.87/6.65  tff(c_23647, plain, (v5_relat_1('#skF_4', '#skF_2')), inference(resolution, [status(thm)], [c_23383, c_23639])).
% 14.87/6.65  tff(c_24931, plain, (![B_1924, A_1925]: (k2_relat_1(B_1924)=A_1925 | ~v2_funct_2(B_1924, A_1925) | ~v5_relat_1(B_1924, A_1925) | ~v1_relat_1(B_1924))), inference(cnfTransformation, [status(thm)], [f_200])).
% 14.87/6.65  tff(c_24940, plain, (k2_relat_1('#skF_4')='#skF_2' | ~v2_funct_2('#skF_4', '#skF_2') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_23647, c_24931])).
% 14.87/6.65  tff(c_24950, plain, ('#skF_2'='#skF_4' | ~v2_funct_2('#skF_4', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_224, c_15671, c_24940])).
% 14.87/6.65  tff(c_24978, plain, (~v2_funct_2('#skF_4', '#skF_2')), inference(splitLeft, [status(thm)], [c_24950])).
% 14.87/6.65  tff(c_62, plain, (![A_54]: (r1_tarski(k6_relat_1(A_54), k2_zfmisc_1(A_54, A_54)))), inference(cnfTransformation, [status(thm)], [f_150])).
% 14.87/6.65  tff(c_139, plain, (![A_54]: (r1_tarski(k6_partfun1(A_54), k2_zfmisc_1(A_54, A_54)))), inference(demodulation, [status(thm), theory('equality')], [c_114, c_62])).
% 14.87/6.65  tff(c_23394, plain, (r1_tarski(k6_partfun1('#skF_2'), '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_23380, c_139])).
% 14.87/6.65  tff(c_15660, plain, (![B_961, A_960]: (~v1_xboole_0(B_961) | B_961=A_960 | ~r1_tarski(A_960, B_961))), inference(resolution, [status(thm)], [c_15649, c_203])).
% 14.87/6.65  tff(c_23446, plain, (~v1_xboole_0('#skF_4') | k6_partfun1('#skF_2')='#skF_4'), inference(resolution, [status(thm)], [c_23394, c_15660])).
% 14.87/6.65  tff(c_23452, plain, (k6_partfun1('#skF_2')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_15666, c_23446])).
% 14.87/6.65  tff(c_26028, plain, (![C_2024, B_2025, A_2026]: (v2_funct_2(C_2024, B_2025) | ~v3_funct_2(C_2024, A_2026, B_2025) | ~v1_funct_1(C_2024) | ~m1_subset_1(C_2024, k1_zfmisc_1(k2_zfmisc_1(A_2026, B_2025))))), inference(cnfTransformation, [status(thm)], [f_174])).
% 14.87/6.65  tff(c_26053, plain, (![A_2027]: (v2_funct_2(k6_partfun1(A_2027), A_2027) | ~v3_funct_2(k6_partfun1(A_2027), A_2027, A_2027) | ~v1_funct_1(k6_partfun1(A_2027)))), inference(resolution, [status(thm)], [c_108, c_26028])).
% 14.87/6.65  tff(c_26056, plain, (v2_funct_2(k6_partfun1('#skF_2'), '#skF_2') | ~v3_funct_2('#skF_4', '#skF_2', '#skF_2') | ~v1_funct_1(k6_partfun1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_23452, c_26053])).
% 14.87/6.65  tff(c_26058, plain, (v2_funct_2('#skF_4', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_130, c_23452, c_126, c_23452, c_26056])).
% 14.87/6.65  tff(c_26060, plain, $false, inference(negUnitSimplification, [status(thm)], [c_24978, c_26058])).
% 14.87/6.65  tff(c_26061, plain, ('#skF_2'='#skF_4'), inference(splitRight, [status(thm)], [c_24950])).
% 14.87/6.65  tff(c_24825, plain, (![A_1916, B_1917, D_1918]: (r2_relset_1(A_1916, B_1917, D_1918, D_1918) | ~m1_subset_1(D_1918, k1_zfmisc_1(k2_zfmisc_1(A_1916, B_1917))))), inference(cnfTransformation, [status(thm)], [f_148])).
% 14.87/6.65  tff(c_24835, plain, (![A_1919]: (r2_relset_1(A_1919, A_1919, k6_partfun1(A_1919), k6_partfun1(A_1919)))), inference(resolution, [status(thm)], [c_108, c_24825])).
% 14.87/6.65  tff(c_24838, plain, (r2_relset_1('#skF_2', '#skF_2', '#skF_4', k6_partfun1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_23452, c_24835])).
% 14.87/6.65  tff(c_24842, plain, (r2_relset_1('#skF_2', '#skF_2', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_23452, c_24838])).
% 14.87/6.65  tff(c_26065, plain, (r2_relset_1('#skF_4', '#skF_4', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_26061, c_26061, c_24842])).
% 14.87/6.65  tff(c_26077, plain, (k6_partfun1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_26061, c_23452])).
% 14.87/6.65  tff(c_26080, plain, (v1_funct_2('#skF_4', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_26061, c_26061, c_128])).
% 14.87/6.65  tff(c_26081, plain, (v3_funct_2('#skF_4', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_26061, c_26061, c_126])).
% 14.87/6.65  tff(c_46, plain, (![A_36]: (k2_funct_1(k6_relat_1(A_36))=k6_relat_1(A_36))), inference(cnfTransformation, [status(thm)], [f_122])).
% 14.87/6.65  tff(c_140, plain, (![A_36]: (k2_funct_1(k6_partfun1(A_36))=k6_partfun1(A_36))), inference(demodulation, [status(thm), theory('equality')], [c_114, c_114, c_46])).
% 14.87/6.65  tff(c_28600, plain, (![A_2207, B_2208]: (k2_funct_2(A_2207, B_2208)=k2_funct_1(B_2208) | ~m1_subset_1(B_2208, k1_zfmisc_1(k2_zfmisc_1(A_2207, A_2207))) | ~v3_funct_2(B_2208, A_2207, A_2207) | ~v1_funct_2(B_2208, A_2207, A_2207) | ~v1_funct_1(B_2208))), inference(cnfTransformation, [status(thm)], [f_252])).
% 14.87/6.65  tff(c_28618, plain, (![A_77]: (k2_funct_2(A_77, k6_partfun1(A_77))=k2_funct_1(k6_partfun1(A_77)) | ~v3_funct_2(k6_partfun1(A_77), A_77, A_77) | ~v1_funct_2(k6_partfun1(A_77), A_77, A_77) | ~v1_funct_1(k6_partfun1(A_77)))), inference(resolution, [status(thm)], [c_108, c_28600])).
% 14.87/6.65  tff(c_33578, plain, (![A_2435]: (k2_funct_2(A_2435, k6_partfun1(A_2435))=k6_partfun1(A_2435) | ~v3_funct_2(k6_partfun1(A_2435), A_2435, A_2435) | ~v1_funct_2(k6_partfun1(A_2435), A_2435, A_2435) | ~v1_funct_1(k6_partfun1(A_2435)))), inference(demodulation, [status(thm), theory('equality')], [c_140, c_28618])).
% 14.87/6.65  tff(c_33581, plain, (k2_funct_2('#skF_4', k6_partfun1('#skF_4'))=k6_partfun1('#skF_4') | ~v3_funct_2('#skF_4', '#skF_4', '#skF_4') | ~v1_funct_2(k6_partfun1('#skF_4'), '#skF_4', '#skF_4') | ~v1_funct_1(k6_partfun1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_26077, c_33578])).
% 14.87/6.65  tff(c_33583, plain, (k2_funct_2('#skF_4', '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_130, c_26077, c_26080, c_26077, c_26081, c_26077, c_26077, c_33581])).
% 14.87/6.65  tff(c_15869, plain, (![C_992, B_993, A_994]: (v5_relat_1(C_992, B_993) | ~m1_subset_1(C_992, k1_zfmisc_1(k2_zfmisc_1(A_994, B_993))))), inference(cnfTransformation, [status(thm)], [f_132])).
% 14.87/6.65  tff(c_15885, plain, (v5_relat_1('#skF_4', '#skF_2')), inference(resolution, [status(thm)], [c_124, c_15869])).
% 14.87/6.65  tff(c_16629, plain, (![B_1073, A_1074]: (k2_relat_1(B_1073)=A_1074 | ~v2_funct_2(B_1073, A_1074) | ~v5_relat_1(B_1073, A_1074) | ~v1_relat_1(B_1073))), inference(cnfTransformation, [status(thm)], [f_200])).
% 14.87/6.65  tff(c_16641, plain, (k2_relat_1('#skF_4')='#skF_2' | ~v2_funct_2('#skF_4', '#skF_2') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_15885, c_16629])).
% 14.87/6.65  tff(c_16653, plain, ('#skF_2'='#skF_4' | ~v2_funct_2('#skF_4', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_224, c_15671, c_16641])).
% 14.87/6.65  tff(c_16654, plain, (~v2_funct_2('#skF_4', '#skF_2')), inference(splitLeft, [status(thm)], [c_16653])).
% 14.87/6.65  tff(c_17075, plain, (![C_1112, B_1113, A_1114]: (v2_funct_2(C_1112, B_1113) | ~v3_funct_2(C_1112, A_1114, B_1113) | ~v1_funct_1(C_1112) | ~m1_subset_1(C_1112, k1_zfmisc_1(k2_zfmisc_1(A_1114, B_1113))))), inference(cnfTransformation, [status(thm)], [f_174])).
% 14.87/6.65  tff(c_17091, plain, (v2_funct_2('#skF_4', '#skF_2') | ~v3_funct_2('#skF_4', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_124, c_17075])).
% 14.87/6.65  tff(c_17099, plain, (v2_funct_2('#skF_4', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_130, c_126, c_17091])).
% 14.87/6.65  tff(c_17101, plain, $false, inference(negUnitSimplification, [status(thm)], [c_16654, c_17099])).
% 14.87/6.65  tff(c_17102, plain, ('#skF_2'='#skF_4'), inference(splitRight, [status(thm)], [c_16653])).
% 14.87/6.65  tff(c_15802, plain, (![B_975, A_976]: (~v1_xboole_0(B_975) | B_975=A_976 | ~r1_tarski(A_976, B_975))), inference(resolution, [status(thm)], [c_15649, c_203])).
% 14.87/6.65  tff(c_15813, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_2', '#skF_2')) | k2_zfmisc_1('#skF_2', '#skF_2')='#skF_4'), inference(resolution, [status(thm)], [c_176, c_15802])).
% 14.87/6.65  tff(c_15830, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_2', '#skF_2'))), inference(splitLeft, [status(thm)], [c_15813])).
% 14.87/6.65  tff(c_15834, plain, (~v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_16, c_15830])).
% 14.87/6.65  tff(c_17112, plain, (~v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_17102, c_15834])).
% 14.87/6.65  tff(c_17127, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_15666, c_17112])).
% 14.87/6.65  tff(c_17128, plain, (k2_zfmisc_1('#skF_2', '#skF_2')='#skF_4'), inference(splitRight, [status(thm)], [c_15813])).
% 14.87/6.65  tff(c_17130, plain, (r1_tarski('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_17128, c_177])).
% 14.87/6.65  tff(c_17157, plain, (~v1_xboole_0('#skF_4') | '#skF_3'='#skF_4'), inference(resolution, [status(thm)], [c_17130, c_15660])).
% 14.87/6.65  tff(c_17163, plain, ('#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_15666, c_17157])).
% 14.87/6.65  tff(c_15683, plain, (k2_relat_1('#skF_3')!='#skF_4' | '#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_15647, c_15647, c_242])).
% 14.87/6.65  tff(c_15684, plain, (k2_relat_1('#skF_3')!='#skF_4'), inference(splitLeft, [status(thm)], [c_15683])).
% 14.87/6.65  tff(c_17168, plain, (k2_relat_1('#skF_4')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_17163, c_15684])).
% 14.87/6.65  tff(c_17178, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_15671, c_17168])).
% 14.87/6.65  tff(c_17179, plain, ('#skF_3'='#skF_4'), inference(splitRight, [status(thm)], [c_15683])).
% 14.87/6.65  tff(c_38, plain, (![A_32]: (k1_relat_1(A_32)!=k1_xboole_0 | k1_xboole_0=A_32 | ~v1_relat_1(A_32))), inference(cnfTransformation, [status(thm)], [f_104])).
% 14.87/6.65  tff(c_243, plain, (k1_relat_1('#skF_3')!=k1_xboole_0 | k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_227, c_38])).
% 14.87/6.65  tff(c_15681, plain, (k1_relat_1('#skF_3')!='#skF_4' | '#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_15647, c_15647, c_243])).
% 14.87/6.65  tff(c_15682, plain, (k1_relat_1('#skF_3')!='#skF_4'), inference(splitLeft, [status(thm)], [c_15681])).
% 14.87/6.65  tff(c_17181, plain, (k1_relat_1('#skF_4')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_17179, c_15682])).
% 14.87/6.65  tff(c_17374, plain, (![C_1143, B_1144, A_1145]: (v5_relat_1(C_1143, B_1144) | ~m1_subset_1(C_1143, k1_zfmisc_1(k2_zfmisc_1(A_1145, B_1144))))), inference(cnfTransformation, [status(thm)], [f_132])).
% 14.87/6.65  tff(c_17387, plain, (v5_relat_1('#skF_4', '#skF_2')), inference(resolution, [status(thm)], [c_124, c_17374])).
% 14.87/6.65  tff(c_18135, plain, (![B_1243, A_1244]: (k2_relat_1(B_1243)=A_1244 | ~v2_funct_2(B_1243, A_1244) | ~v5_relat_1(B_1243, A_1244) | ~v1_relat_1(B_1243))), inference(cnfTransformation, [status(thm)], [f_200])).
% 14.87/6.65  tff(c_18144, plain, (k2_relat_1('#skF_4')='#skF_2' | ~v2_funct_2('#skF_4', '#skF_2') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_17387, c_18135])).
% 14.87/6.65  tff(c_18153, plain, ('#skF_2'='#skF_4' | ~v2_funct_2('#skF_4', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_224, c_15671, c_18144])).
% 14.87/6.65  tff(c_18154, plain, (~v2_funct_2('#skF_4', '#skF_2')), inference(splitLeft, [status(thm)], [c_18153])).
% 14.87/6.65  tff(c_18672, plain, (![C_1294, B_1295, A_1296]: (v2_funct_2(C_1294, B_1295) | ~v3_funct_2(C_1294, A_1296, B_1295) | ~v1_funct_1(C_1294) | ~m1_subset_1(C_1294, k1_zfmisc_1(k2_zfmisc_1(A_1296, B_1295))))), inference(cnfTransformation, [status(thm)], [f_174])).
% 14.87/6.65  tff(c_18688, plain, (v2_funct_2('#skF_4', '#skF_2') | ~v3_funct_2('#skF_4', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_124, c_18672])).
% 14.87/6.65  tff(c_18693, plain, (v2_funct_2('#skF_4', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_130, c_126, c_18688])).
% 14.87/6.65  tff(c_18695, plain, $false, inference(negUnitSimplification, [status(thm)], [c_18154, c_18693])).
% 14.87/6.65  tff(c_18696, plain, ('#skF_2'='#skF_4'), inference(splitRight, [status(thm)], [c_18153])).
% 14.87/6.65  tff(c_17235, plain, (![B_1119, A_1120]: (~v1_xboole_0(B_1119) | B_1119=A_1120 | ~r1_tarski(A_1120, B_1119))), inference(resolution, [status(thm)], [c_15649, c_203])).
% 14.87/6.65  tff(c_17242, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_2', '#skF_2')) | k2_zfmisc_1('#skF_2', '#skF_2')='#skF_4'), inference(resolution, [status(thm)], [c_176, c_17235])).
% 14.87/6.65  tff(c_17317, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_2', '#skF_2'))), inference(splitLeft, [status(thm)], [c_17242])).
% 14.87/6.65  tff(c_17321, plain, (~v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_16, c_17317])).
% 14.87/6.65  tff(c_18703, plain, (~v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_18696, c_17321])).
% 14.87/6.65  tff(c_18714, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_15666, c_18703])).
% 14.87/6.65  tff(c_18715, plain, (k2_zfmisc_1('#skF_2', '#skF_2')='#skF_4'), inference(splitRight, [status(thm)], [c_17242])).
% 14.87/6.65  tff(c_18729, plain, (r1_tarski(k6_partfun1('#skF_2'), '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_18715, c_139])).
% 14.87/6.65  tff(c_18768, plain, (~v1_xboole_0('#skF_4') | k6_partfun1('#skF_2')='#skF_4'), inference(resolution, [status(thm)], [c_18729, c_15660])).
% 14.87/6.65  tff(c_18774, plain, (k6_partfun1('#skF_2')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_15666, c_18768])).
% 14.87/6.65  tff(c_18947, plain, (![C_1314, B_1315, A_1316]: (v5_relat_1(C_1314, B_1315) | ~m1_subset_1(C_1314, k1_zfmisc_1(k2_zfmisc_1(A_1316, B_1315))))), inference(cnfTransformation, [status(thm)], [f_132])).
% 14.87/6.65  tff(c_18960, plain, (![A_1317]: (v5_relat_1(k6_partfun1(A_1317), A_1317))), inference(resolution, [status(thm)], [c_108, c_18947])).
% 14.87/6.65  tff(c_18963, plain, (v5_relat_1('#skF_4', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_18774, c_18960])).
% 14.87/6.65  tff(c_20303, plain, (![B_1456, A_1457]: (k2_relat_1(B_1456)=A_1457 | ~v2_funct_2(B_1456, A_1457) | ~v5_relat_1(B_1456, A_1457) | ~v1_relat_1(B_1456))), inference(cnfTransformation, [status(thm)], [f_200])).
% 14.87/6.65  tff(c_20312, plain, (k2_relat_1('#skF_4')='#skF_2' | ~v2_funct_2('#skF_4', '#skF_2') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_18963, c_20303])).
% 14.87/6.65  tff(c_20322, plain, ('#skF_2'='#skF_4' | ~v2_funct_2('#skF_4', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_224, c_15671, c_20312])).
% 14.87/6.65  tff(c_20326, plain, (~v2_funct_2('#skF_4', '#skF_2')), inference(splitLeft, [status(thm)], [c_20322])).
% 14.87/6.65  tff(c_18718, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_18715, c_124])).
% 14.87/6.65  tff(c_21109, plain, (![C_1525, B_1526, A_1527]: (v2_funct_2(C_1525, B_1526) | ~v3_funct_2(C_1525, A_1527, B_1526) | ~v1_funct_1(C_1525) | ~m1_subset_1(C_1525, k1_zfmisc_1(k2_zfmisc_1(A_1527, B_1526))))), inference(cnfTransformation, [status(thm)], [f_174])).
% 14.87/6.65  tff(c_21161, plain, (![C_1533]: (v2_funct_2(C_1533, '#skF_2') | ~v3_funct_2(C_1533, '#skF_2', '#skF_2') | ~v1_funct_1(C_1533) | ~m1_subset_1(C_1533, k1_zfmisc_1('#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_18715, c_21109])).
% 14.87/6.65  tff(c_21164, plain, (v2_funct_2('#skF_4', '#skF_2') | ~v3_funct_2('#skF_4', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_18718, c_21161])).
% 14.87/6.65  tff(c_21171, plain, (v2_funct_2('#skF_4', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_130, c_126, c_21164])).
% 14.87/6.65  tff(c_21173, plain, $false, inference(negUnitSimplification, [status(thm)], [c_20326, c_21171])).
% 14.87/6.65  tff(c_21174, plain, ('#skF_2'='#skF_4'), inference(splitRight, [status(thm)], [c_20322])).
% 14.87/6.65  tff(c_21190, plain, (v1_funct_2('#skF_4', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_21174, c_21174, c_128])).
% 14.87/6.65  tff(c_21187, plain, (k6_partfun1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_21174, c_18774])).
% 14.87/6.65  tff(c_21344, plain, (![A_1537, B_1538, C_1539]: (k1_relset_1(A_1537, B_1538, C_1539)=k1_relat_1(C_1539) | ~m1_subset_1(C_1539, k1_zfmisc_1(k2_zfmisc_1(A_1537, B_1538))))), inference(cnfTransformation, [status(thm)], [f_136])).
% 14.87/6.65  tff(c_21414, plain, (![A_1546]: (k1_relset_1(A_1546, A_1546, k6_partfun1(A_1546))=k1_relat_1(k6_partfun1(A_1546)))), inference(resolution, [status(thm)], [c_108, c_21344])).
% 14.87/6.65  tff(c_21423, plain, (k1_relat_1(k6_partfun1('#skF_4'))=k1_relset_1('#skF_4', '#skF_4', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_21187, c_21414])).
% 14.87/6.65  tff(c_21426, plain, (k1_relset_1('#skF_4', '#skF_4', '#skF_4')=k1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_21187, c_21423])).
% 14.87/6.65  tff(c_86, plain, (![B_65, C_66]: (k1_relset_1(k1_xboole_0, B_65, C_66)=k1_xboole_0 | ~v1_funct_2(C_66, k1_xboole_0, B_65) | ~m1_subset_1(C_66, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_65))))), inference(cnfTransformation, [status(thm)], [f_192])).
% 14.87/6.65  tff(c_21922, plain, (![B_1604, C_1605]: (k1_relset_1('#skF_4', B_1604, C_1605)='#skF_4' | ~v1_funct_2(C_1605, '#skF_4', B_1604) | ~m1_subset_1(C_1605, k1_zfmisc_1(k2_zfmisc_1('#skF_4', B_1604))))), inference(demodulation, [status(thm), theory('equality')], [c_15647, c_15647, c_15647, c_15647, c_86])).
% 14.87/6.65  tff(c_21929, plain, (k1_relset_1('#skF_4', '#skF_4', k6_partfun1('#skF_4'))='#skF_4' | ~v1_funct_2(k6_partfun1('#skF_4'), '#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_108, c_21922])).
% 14.87/6.65  tff(c_21936, plain, (k1_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_21190, c_21187, c_21426, c_21187, c_21929])).
% 14.87/6.65  tff(c_21938, plain, $false, inference(negUnitSimplification, [status(thm)], [c_17181, c_21936])).
% 14.87/6.65  tff(c_21939, plain, ('#skF_3'='#skF_4'), inference(splitRight, [status(thm)], [c_15681])).
% 14.87/6.65  tff(c_21944, plain, (~r2_relset_1('#skF_2', '#skF_2', '#skF_4', k2_funct_2('#skF_2', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_21939, c_120])).
% 14.87/6.65  tff(c_26079, plain, (~r2_relset_1('#skF_4', '#skF_4', '#skF_4', k2_funct_2('#skF_4', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_26061, c_26061, c_26061, c_21944])).
% 14.87/6.65  tff(c_33585, plain, (~r2_relset_1('#skF_4', '#skF_4', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_33583, c_26079])).
% 14.87/6.65  tff(c_33589, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_26065, c_33585])).
% 14.87/6.65  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 14.87/6.65  
% 14.87/6.65  Inference rules
% 14.87/6.65  ----------------------
% 14.87/6.65  #Ref     : 0
% 14.87/6.65  #Sup     : 7944
% 14.87/6.65  #Fact    : 0
% 14.87/6.65  #Define  : 0
% 14.87/6.65  #Split   : 64
% 14.87/6.65  #Chain   : 0
% 14.87/6.65  #Close   : 0
% 14.87/6.65  
% 14.87/6.65  Ordering : KBO
% 14.87/6.65  
% 14.87/6.65  Simplification rules
% 14.87/6.65  ----------------------
% 14.87/6.65  #Subsume      : 979
% 14.87/6.65  #Demod        : 8000
% 14.87/6.65  #Tautology    : 2840
% 14.87/6.65  #SimpNegUnit  : 107
% 14.87/6.65  #BackRed      : 419
% 14.87/6.65  
% 14.87/6.65  #Partial instantiations: 0
% 14.87/6.65  #Strategies tried      : 1
% 14.87/6.65  
% 14.87/6.65  Timing (in seconds)
% 14.87/6.65  ----------------------
% 14.87/6.66  Preprocessing        : 0.44
% 14.87/6.66  Parsing              : 0.23
% 14.87/6.66  CNF conversion       : 0.03
% 14.87/6.66  Main loop            : 5.38
% 14.87/6.66  Inferencing          : 1.50
% 14.87/6.66  Reduction            : 2.14
% 14.87/6.66  Demodulation         : 1.58
% 14.87/6.66  BG Simplification    : 0.14
% 14.87/6.66  Subsumption          : 1.22
% 14.87/6.66  Abstraction          : 0.17
% 14.87/6.66  MUC search           : 0.00
% 14.87/6.66  Cooper               : 0.00
% 14.87/6.66  Total                : 5.92
% 14.87/6.66  Index Insertion      : 0.00
% 14.87/6.66  Index Deletion       : 0.00
% 14.87/6.66  Index Matching       : 0.00
% 14.87/6.66  BG Taut test         : 0.00
%------------------------------------------------------------------------------
