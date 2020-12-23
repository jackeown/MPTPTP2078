%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:12:33 EST 2020

% Result     : Theorem 17.81s
% Output     : CNFRefutation 18.26s
% Verified   : 
% Statistics : Number of formulae       :  424 (3428 expanded)
%              Number of leaves         :   61 (1132 expanded)
%              Depth                    :   28
%              Number of atoms          :  860 (8849 expanded)
%              Number of equality atoms :  247 (2589 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r2_hidden > r1_tarski > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k9_relat_1 > k5_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1

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

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_250,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( ( v2_funct_1(C)
            & k2_relset_1(A,B,C) = B )
         => ( v1_funct_1(k2_funct_1(C))
            & v1_funct_2(k2_funct_1(C),B,A)
            & m1_subset_1(k2_funct_1(C),k1_zfmisc_1(k2_zfmisc_1(B,A))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_funct_2)).

tff(f_178,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_172,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_78,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ( k1_relat_1(A) = k1_xboole_0
          | k2_relat_1(A) = k1_xboole_0 )
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).

tff(f_101,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).

tff(f_182,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_151,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k2_relat_1(A) = k1_relat_1(k2_funct_1(A))
          & k1_relat_1(A) = k2_relat_1(k2_funct_1(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_39,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_70,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k10_relat_1(A,k2_relat_1(A)) = k1_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_relat_1)).

tff(f_117,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r1_tarski(A,k2_relat_1(B))
       => k9_relat_1(B,k10_relat_1(B,A)) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t147_funct_1)).

tff(f_128,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( ( v2_funct_1(A)
            & r1_tarski(B,k1_relat_1(A)) )
         => k9_relat_1(k2_funct_1(A),k9_relat_1(A,B)) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t177_funct_1)).

tff(f_66,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k9_relat_1(A,k1_relat_1(A)) = k2_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_relat_1)).

tff(f_214,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_funct_1(A)
        & v1_funct_2(A,k1_relat_1(A),k2_relat_1(A))
        & m1_subset_1(A,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A)))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_funct_2)).

tff(f_62,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_233,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r1_tarski(B,C)
       => ( ( B = k1_xboole_0
            & A != k1_xboole_0 )
          | ( v1_funct_1(D)
            & v1_funct_2(D,A,C)
            & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,C))) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_funct_2)).

tff(f_204,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_93,axiom,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_relat_1)).

tff(f_88,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_33,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_109,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v2_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_funct_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_202,axiom,(
    ! [A] :
      ( v1_partfun1(k6_partfun1(A),A)
      & m1_subset_1(k6_partfun1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).

tff(f_56,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

tff(f_49,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_105,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v1_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).

tff(f_92,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k5_relat_1(A,k6_relat_1(k2_relat_1(A))) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t80_relat_1)).

tff(f_168,axiom,(
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

tff(f_84,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( k1_relat_1(A) = k1_xboole_0
      <=> k2_relat_1(A) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_relat_1)).

tff(f_188,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(C,A)))
     => ( r1_tarski(k2_relat_1(D),B)
       => m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(C,B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_relset_1)).

tff(f_198,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( ( v1_funct_1(C)
          & v1_partfun1(C,A) )
       => ( v1_funct_1(C)
          & v1_funct_2(C,A,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_funct_2)).

tff(c_120,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_250])).

tff(c_20692,plain,(
    ! [C_1086,A_1087,B_1088] :
      ( v4_relat_1(C_1086,A_1087)
      | ~ m1_subset_1(C_1086,k1_zfmisc_1(k2_zfmisc_1(A_1087,B_1088))) ) ),
    inference(cnfTransformation,[status(thm)],[f_178])).

tff(c_20716,plain,(
    v4_relat_1('#skF_4','#skF_2') ),
    inference(resolution,[status(thm)],[c_120,c_20692])).

tff(c_20189,plain,(
    ! [C_1034,A_1035,B_1036] :
      ( v1_relat_1(C_1034)
      | ~ m1_subset_1(C_1034,k1_zfmisc_1(k2_zfmisc_1(A_1035,B_1036))) ) ),
    inference(cnfTransformation,[status(thm)],[f_172])).

tff(c_20211,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_120,c_20189])).

tff(c_38,plain,(
    ! [A_19] :
      ( k1_relat_1(A_19) != k1_xboole_0
      | k1_xboole_0 = A_19
      | ~ v1_relat_1(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_20227,plain,
    ( k1_relat_1('#skF_4') != k1_xboole_0
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_20211,c_38])).

tff(c_20245,plain,(
    k1_relat_1('#skF_4') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_20227])).

tff(c_124,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_250])).

tff(c_52,plain,(
    ! [A_23] :
      ( v1_funct_1(k2_funct_1(A_23))
      | ~ v1_funct_1(A_23)
      | ~ v1_relat_1(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_114,plain,
    ( ~ m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2')))
    | ~ v1_funct_2(k2_funct_1('#skF_4'),'#skF_3','#skF_2')
    | ~ v1_funct_1(k2_funct_1('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_250])).

tff(c_253,plain,(
    ~ v1_funct_1(k2_funct_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_114])).

tff(c_256,plain,
    ( ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_52,c_253])).

tff(c_259,plain,(
    ~ v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_124,c_256])).

tff(c_597,plain,(
    ! [C_102,A_103,B_104] :
      ( v1_relat_1(C_102)
      | ~ m1_subset_1(C_102,k1_zfmisc_1(k2_zfmisc_1(A_103,B_104))) ) ),
    inference(cnfTransformation,[status(thm)],[f_172])).

tff(c_607,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_120,c_597])).

tff(c_618,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_259,c_607])).

tff(c_620,plain,(
    v1_funct_1(k2_funct_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_114])).

tff(c_118,plain,(
    v2_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_250])).

tff(c_116,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_4') = '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_250])).

tff(c_21326,plain,(
    ! [A_1157,B_1158,C_1159] :
      ( k2_relset_1(A_1157,B_1158,C_1159) = k2_relat_1(C_1159)
      | ~ m1_subset_1(C_1159,k1_zfmisc_1(k2_zfmisc_1(A_1157,B_1158))) ) ),
    inference(cnfTransformation,[status(thm)],[f_182])).

tff(c_21345,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_120,c_21326])).

tff(c_21360,plain,(
    k2_relat_1('#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_116,c_21345])).

tff(c_72,plain,(
    ! [A_34] :
      ( k1_relat_1(k2_funct_1(A_34)) = k2_relat_1(A_34)
      | ~ v2_funct_1(A_34)
      | ~ v1_funct_1(A_34)
      | ~ v1_relat_1(A_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_1197,plain,(
    ! [C_165,A_166,B_167] :
      ( v4_relat_1(C_165,A_166)
      | ~ m1_subset_1(C_165,k1_zfmisc_1(k2_zfmisc_1(A_166,B_167))) ) ),
    inference(cnfTransformation,[status(thm)],[f_178])).

tff(c_1216,plain,(
    v4_relat_1('#skF_4','#skF_2') ),
    inference(resolution,[status(thm)],[c_120,c_1197])).

tff(c_887,plain,(
    ! [C_127,A_128,B_129] :
      ( v1_relat_1(C_127)
      | ~ m1_subset_1(C_127,k1_zfmisc_1(k2_zfmisc_1(A_128,B_129))) ) ),
    inference(cnfTransformation,[status(thm)],[f_172])).

tff(c_905,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_120,c_887])).

tff(c_917,plain,
    ( k1_relat_1('#skF_4') != k1_xboole_0
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_905,c_38])).

tff(c_919,plain,(
    k1_relat_1('#skF_4') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_917])).

tff(c_1621,plain,(
    ! [A_213,B_214,C_215] :
      ( k2_relset_1(A_213,B_214,C_215) = k2_relat_1(C_215)
      | ~ m1_subset_1(C_215,k1_zfmisc_1(k2_zfmisc_1(A_213,B_214))) ) ),
    inference(cnfTransformation,[status(thm)],[f_182])).

tff(c_1631,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_120,c_1621])).

tff(c_1642,plain,(
    k2_relat_1('#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_116,c_1631])).

tff(c_54,plain,(
    ! [A_23] :
      ( v1_relat_1(k2_funct_1(A_23))
      | ~ v1_funct_1(A_23)
      | ~ v1_relat_1(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_14,plain,(
    ! [B_7] : r1_tarski(B_7,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_34,plain,(
    ! [A_18] :
      ( k10_relat_1(A_18,k2_relat_1(A_18)) = k1_relat_1(A_18)
      | ~ v1_relat_1(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_1650,plain,
    ( k10_relat_1('#skF_4','#skF_3') = k1_relat_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1642,c_34])).

tff(c_1659,plain,(
    k10_relat_1('#skF_4','#skF_3') = k1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_905,c_1650])).

tff(c_1885,plain,(
    ! [B_234,A_235] :
      ( k9_relat_1(B_234,k10_relat_1(B_234,A_235)) = A_235
      | ~ r1_tarski(A_235,k2_relat_1(B_234))
      | ~ v1_funct_1(B_234)
      | ~ v1_relat_1(B_234) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_1887,plain,(
    ! [A_235] :
      ( k9_relat_1('#skF_4',k10_relat_1('#skF_4',A_235)) = A_235
      | ~ r1_tarski(A_235,'#skF_3')
      | ~ v1_funct_1('#skF_4')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1642,c_1885])).

tff(c_2084,plain,(
    ! [A_255] :
      ( k9_relat_1('#skF_4',k10_relat_1('#skF_4',A_255)) = A_255
      | ~ r1_tarski(A_255,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_905,c_124,c_1887])).

tff(c_2093,plain,
    ( k9_relat_1('#skF_4',k1_relat_1('#skF_4')) = '#skF_3'
    | ~ r1_tarski('#skF_3','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1659,c_2084])).

tff(c_2101,plain,(
    k9_relat_1('#skF_4',k1_relat_1('#skF_4')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_2093])).

tff(c_2467,plain,(
    ! [A_281,B_282] :
      ( k9_relat_1(k2_funct_1(A_281),k9_relat_1(A_281,B_282)) = B_282
      | ~ r1_tarski(B_282,k1_relat_1(A_281))
      | ~ v2_funct_1(A_281)
      | ~ v1_funct_1(A_281)
      | ~ v1_relat_1(A_281) ) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_2482,plain,
    ( k9_relat_1(k2_funct_1('#skF_4'),'#skF_3') = k1_relat_1('#skF_4')
    | ~ r1_tarski(k1_relat_1('#skF_4'),k1_relat_1('#skF_4'))
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_2101,c_2467])).

tff(c_2498,plain,(
    k9_relat_1(k2_funct_1('#skF_4'),'#skF_3') = k1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_905,c_124,c_118,c_14,c_2482])).

tff(c_1481,plain,(
    ! [A_195] :
      ( k1_relat_1(k2_funct_1(A_195)) = k2_relat_1(A_195)
      | ~ v2_funct_1(A_195)
      | ~ v1_funct_1(A_195)
      | ~ v1_relat_1(A_195) ) ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_32,plain,(
    ! [A_17] :
      ( k9_relat_1(A_17,k1_relat_1(A_17)) = k2_relat_1(A_17)
      | ~ v1_relat_1(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_12733,plain,(
    ! [A_647] :
      ( k9_relat_1(k2_funct_1(A_647),k2_relat_1(A_647)) = k2_relat_1(k2_funct_1(A_647))
      | ~ v1_relat_1(k2_funct_1(A_647))
      | ~ v2_funct_1(A_647)
      | ~ v1_funct_1(A_647)
      | ~ v1_relat_1(A_647) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1481,c_32])).

tff(c_12766,plain,
    ( k9_relat_1(k2_funct_1('#skF_4'),'#skF_3') = k2_relat_1(k2_funct_1('#skF_4'))
    | ~ v1_relat_1(k2_funct_1('#skF_4'))
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1642,c_12733])).

tff(c_12785,plain,
    ( k2_relat_1(k2_funct_1('#skF_4')) = k1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_905,c_124,c_118,c_2498,c_12766])).

tff(c_12790,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_12785])).

tff(c_12799,plain,
    ( ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_54,c_12790])).

tff(c_12805,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_905,c_124,c_12799])).

tff(c_12807,plain,(
    v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_12785])).

tff(c_12806,plain,(
    k2_relat_1(k2_funct_1('#skF_4')) = k1_relat_1('#skF_4') ),
    inference(splitRight,[status(thm)],[c_12785])).

tff(c_98,plain,(
    ! [A_56] :
      ( v1_funct_2(A_56,k1_relat_1(A_56),k2_relat_1(A_56))
      | ~ v1_funct_1(A_56)
      | ~ v1_relat_1(A_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_214])).

tff(c_12936,plain,
    ( v1_funct_2(k2_funct_1('#skF_4'),k1_relat_1(k2_funct_1('#skF_4')),k1_relat_1('#skF_4'))
    | ~ v1_funct_1(k2_funct_1('#skF_4'))
    | ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_12806,c_98])).

tff(c_12988,plain,(
    v1_funct_2(k2_funct_1('#skF_4'),k1_relat_1(k2_funct_1('#skF_4')),k1_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12807,c_620,c_12936])).

tff(c_14093,plain,
    ( v1_funct_2(k2_funct_1('#skF_4'),k2_relat_1('#skF_4'),k1_relat_1('#skF_4'))
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_72,c_12988])).

tff(c_14095,plain,(
    v1_funct_2(k2_funct_1('#skF_4'),'#skF_3',k1_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_905,c_124,c_118,c_1642,c_14093])).

tff(c_1732,plain,(
    ! [A_223] :
      ( m1_subset_1(A_223,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_223),k2_relat_1(A_223))))
      | ~ v1_funct_1(A_223)
      | ~ v1_relat_1(A_223) ) ),
    inference(cnfTransformation,[status(thm)],[f_214])).

tff(c_14886,plain,(
    ! [A_696] :
      ( m1_subset_1(k2_funct_1(A_696),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(A_696),k2_relat_1(k2_funct_1(A_696)))))
      | ~ v1_funct_1(k2_funct_1(A_696))
      | ~ v1_relat_1(k2_funct_1(A_696))
      | ~ v2_funct_1(A_696)
      | ~ v1_funct_1(A_696)
      | ~ v1_relat_1(A_696) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_72,c_1732])).

tff(c_14953,plain,
    ( m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_3',k2_relat_1(k2_funct_1('#skF_4')))))
    | ~ v1_funct_1(k2_funct_1('#skF_4'))
    | ~ v1_relat_1(k2_funct_1('#skF_4'))
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1642,c_14886])).

tff(c_14997,plain,(
    m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_3',k1_relat_1('#skF_4')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_905,c_124,c_118,c_12807,c_620,c_12806,c_14953])).

tff(c_30,plain,(
    ! [B_16,A_15] :
      ( r1_tarski(k1_relat_1(B_16),A_15)
      | ~ v4_relat_1(B_16,A_15)
      | ~ v1_relat_1(B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_3167,plain,(
    ! [B_318,D_319,A_320,C_321] :
      ( k1_xboole_0 = B_318
      | m1_subset_1(D_319,k1_zfmisc_1(k2_zfmisc_1(A_320,C_321)))
      | ~ r1_tarski(B_318,C_321)
      | ~ m1_subset_1(D_319,k1_zfmisc_1(k2_zfmisc_1(A_320,B_318)))
      | ~ v1_funct_2(D_319,A_320,B_318)
      | ~ v1_funct_1(D_319) ) ),
    inference(cnfTransformation,[status(thm)],[f_233])).

tff(c_16321,plain,(
    ! [B_726,D_727,A_728,A_729] :
      ( k1_relat_1(B_726) = k1_xboole_0
      | m1_subset_1(D_727,k1_zfmisc_1(k2_zfmisc_1(A_728,A_729)))
      | ~ m1_subset_1(D_727,k1_zfmisc_1(k2_zfmisc_1(A_728,k1_relat_1(B_726))))
      | ~ v1_funct_2(D_727,A_728,k1_relat_1(B_726))
      | ~ v1_funct_1(D_727)
      | ~ v4_relat_1(B_726,A_729)
      | ~ v1_relat_1(B_726) ) ),
    inference(resolution,[status(thm)],[c_30,c_3167])).

tff(c_16327,plain,(
    ! [A_729] :
      ( k1_relat_1('#skF_4') = k1_xboole_0
      | m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_3',A_729)))
      | ~ v1_funct_2(k2_funct_1('#skF_4'),'#skF_3',k1_relat_1('#skF_4'))
      | ~ v1_funct_1(k2_funct_1('#skF_4'))
      | ~ v4_relat_1('#skF_4',A_729)
      | ~ v1_relat_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_14997,c_16321])).

tff(c_16376,plain,(
    ! [A_729] :
      ( k1_relat_1('#skF_4') = k1_xboole_0
      | m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_3',A_729)))
      | ~ v4_relat_1('#skF_4',A_729) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_905,c_620,c_14095,c_16327])).

tff(c_16404,plain,(
    ! [A_730] :
      ( m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_3',A_730)))
      | ~ v4_relat_1('#skF_4',A_730) ) ),
    inference(negUnitSimplification,[status(thm)],[c_919,c_16376])).

tff(c_619,plain,
    ( ~ v1_funct_2(k2_funct_1('#skF_4'),'#skF_3','#skF_2')
    | ~ m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_114])).

tff(c_686,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_619])).

tff(c_16451,plain,(
    ~ v4_relat_1('#skF_4','#skF_2') ),
    inference(resolution,[status(thm)],[c_16404,c_686])).

tff(c_16505,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1216,c_16451])).

tff(c_16506,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_917])).

tff(c_145,plain,(
    ! [A_65] : k6_relat_1(A_65) = k6_partfun1(A_65) ),
    inference(cnfTransformation,[status(thm)],[f_204])).

tff(c_50,plain,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_151,plain,(
    k6_partfun1(k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_145,c_50])).

tff(c_94,plain,(
    ! [A_55] : k6_relat_1(A_55) = k6_partfun1(A_55) ),
    inference(cnfTransformation,[status(thm)],[f_204])).

tff(c_46,plain,(
    ! [A_21] : k2_relat_1(k6_relat_1(A_21)) = A_21 ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_217,plain,(
    ! [A_70] : k2_relat_1(k6_partfun1(A_70)) = A_70 ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_46])).

tff(c_226,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_151,c_217])).

tff(c_16519,plain,(
    k2_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_16506,c_16506,c_226])).

tff(c_36,plain,(
    ! [A_19] :
      ( k2_relat_1(A_19) != k1_xboole_0
      | k1_xboole_0 = A_19
      | ~ v1_relat_1(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_916,plain,
    ( k2_relat_1('#skF_4') != k1_xboole_0
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_905,c_36])).

tff(c_918,plain,(
    k2_relat_1('#skF_4') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_916])).

tff(c_16508,plain,(
    k2_relat_1('#skF_4') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_16506,c_918])).

tff(c_16583,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_16519,c_16508])).

tff(c_16584,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_916])).

tff(c_8,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_16604,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16584,c_8])).

tff(c_44,plain,(
    ! [A_21] : k1_relat_1(k6_relat_1(A_21)) = A_21 ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_133,plain,(
    ! [A_21] : k1_relat_1(k6_partfun1(A_21)) = A_21 ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_44])).

tff(c_60,plain,(
    ! [A_25] : v1_relat_1(k6_relat_1(A_25)) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_128,plain,(
    ! [A_25] : v1_relat_1(k6_partfun1(A_25)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_60])).

tff(c_236,plain,(
    ! [A_75] :
      ( k1_relat_1(A_75) != k1_xboole_0
      | k1_xboole_0 = A_75
      | ~ v1_relat_1(A_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_245,plain,(
    ! [A_25] :
      ( k1_relat_1(k6_partfun1(A_25)) != k1_xboole_0
      | k6_partfun1(A_25) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_128,c_236])).

tff(c_260,plain,(
    k6_partfun1(k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_133,c_245])).

tff(c_18,plain,(
    ! [A_8] : k2_zfmisc_1(A_8,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_663,plain,(
    ! [A_109] : m1_subset_1(k6_partfun1(A_109),k1_zfmisc_1(k2_zfmisc_1(A_109,A_109))) ),
    inference(cnfTransformation,[status(thm)],[f_202])).

tff(c_673,plain,(
    m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_663])).

tff(c_679,plain,(
    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_260,c_673])).

tff(c_16592,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16584,c_16584,c_679])).

tff(c_17639,plain,(
    ! [C_821,B_822,A_823] :
      ( ~ v1_xboole_0(C_821)
      | ~ m1_subset_1(B_822,k1_zfmisc_1(C_821))
      | ~ r2_hidden(A_823,B_822) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_17641,plain,(
    ! [A_823] :
      ( ~ v1_xboole_0('#skF_4')
      | ~ r2_hidden(A_823,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_16592,c_17639])).

tff(c_17651,plain,(
    ! [A_824] : ~ r2_hidden(A_824,'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16604,c_17641])).

tff(c_17656,plain,(
    ! [B_2] : r1_tarski('#skF_4',B_2) ),
    inference(resolution,[status(thm)],[c_6,c_17651])).

tff(c_178,plain,(
    ! [A_67] : k1_relat_1(k6_partfun1(A_67)) = A_67 ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_44])).

tff(c_187,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_151,c_178])).

tff(c_16598,plain,(
    k1_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_16584,c_16584,c_187])).

tff(c_17513,plain,(
    ! [B_805,A_806] :
      ( v4_relat_1(B_805,A_806)
      | ~ r1_tarski(k1_relat_1(B_805),A_806)
      | ~ v1_relat_1(B_805) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_17516,plain,(
    ! [A_806] :
      ( v4_relat_1('#skF_4',A_806)
      | ~ r1_tarski('#skF_4',A_806)
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16598,c_17513])).

tff(c_17525,plain,(
    ! [A_806] :
      ( v4_relat_1('#skF_4',A_806)
      | ~ r1_tarski('#skF_4',A_806) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_905,c_17516])).

tff(c_17658,plain,(
    ! [A_806] : v4_relat_1('#skF_4',A_806) ),
    inference(demodulation,[status(thm),theory(equality)],[c_17656,c_17525])).

tff(c_252,plain,(
    ! [A_25] :
      ( k1_xboole_0 != A_25
      | k6_partfun1(A_25) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_133,c_245])).

tff(c_16594,plain,(
    ! [A_25] :
      ( A_25 != '#skF_4'
      | k6_partfun1(A_25) = '#skF_4' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16584,c_16584,c_252])).

tff(c_17818,plain,(
    ! [B_846,A_847] :
      ( r1_tarski(k1_relat_1(B_846),A_847)
      | ~ v4_relat_1(B_846,A_847)
      | ~ v1_relat_1(B_846) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_17841,plain,(
    ! [A_21,A_847] :
      ( r1_tarski(A_21,A_847)
      | ~ v4_relat_1(k6_partfun1(A_21),A_847)
      | ~ v1_relat_1(k6_partfun1(A_21)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_133,c_17818])).

tff(c_17851,plain,(
    ! [A_848,A_849] :
      ( r1_tarski(A_848,A_849)
      | ~ v4_relat_1(k6_partfun1(A_848),A_849) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_128,c_17841])).

tff(c_17868,plain,(
    ! [A_25,A_849] :
      ( r1_tarski(A_25,A_849)
      | ~ v4_relat_1('#skF_4',A_849)
      | A_25 != '#skF_4' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16594,c_17851])).

tff(c_17880,plain,(
    ! [A_850,A_851] :
      ( r1_tarski(A_850,A_851)
      | A_850 != '#skF_4' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_17658,c_17868])).

tff(c_24,plain,(
    ! [A_10,B_11] :
      ( m1_subset_1(A_10,k1_zfmisc_1(B_11))
      | ~ r1_tarski(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_722,plain,(
    ~ r1_tarski(k2_funct_1('#skF_4'),k2_zfmisc_1('#skF_3','#skF_2')) ),
    inference(resolution,[status(thm)],[c_24,c_686])).

tff(c_17907,plain,(
    k2_funct_1('#skF_4') != '#skF_4' ),
    inference(resolution,[status(thm)],[c_17880,c_722])).

tff(c_58,plain,(
    ! [A_24] : v1_funct_1(k6_relat_1(A_24)) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_129,plain,(
    ! [A_24] : v1_funct_1(k6_partfun1(A_24)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_58])).

tff(c_62,plain,(
    ! [A_25] : v2_funct_1(k6_relat_1(A_25)) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_127,plain,(
    ! [A_25] : v2_funct_1(k6_partfun1(A_25)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_62])).

tff(c_132,plain,(
    ! [A_21] : k2_relat_1(k6_partfun1(A_21)) = A_21 ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_46])).

tff(c_48,plain,(
    ! [A_22] :
      ( k5_relat_1(A_22,k6_relat_1(k2_relat_1(A_22))) = A_22
      | ~ v1_relat_1(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_738,plain,(
    ! [A_115] :
      ( k5_relat_1(A_115,k6_partfun1(k2_relat_1(A_115))) = A_115
      | ~ v1_relat_1(A_115) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_48])).

tff(c_753,plain,(
    ! [A_21] :
      ( k5_relat_1(k6_partfun1(A_21),k6_partfun1(A_21)) = k6_partfun1(A_21)
      | ~ v1_relat_1(k6_partfun1(A_21)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_132,c_738])).

tff(c_759,plain,(
    ! [A_21] : k5_relat_1(k6_partfun1(A_21),k6_partfun1(A_21)) = k6_partfun1(A_21) ),
    inference(demodulation,[status(thm),theory(equality)],[c_128,c_753])).

tff(c_74,plain,(
    ! [A_35,B_37] :
      ( k2_funct_1(A_35) = B_37
      | k6_relat_1(k1_relat_1(A_35)) != k5_relat_1(A_35,B_37)
      | k2_relat_1(A_35) != k1_relat_1(B_37)
      | ~ v2_funct_1(A_35)
      | ~ v1_funct_1(B_37)
      | ~ v1_relat_1(B_37)
      | ~ v1_funct_1(A_35)
      | ~ v1_relat_1(A_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_168])).

tff(c_19707,plain,(
    ! [A_1009,B_1010] :
      ( k2_funct_1(A_1009) = B_1010
      | k6_partfun1(k1_relat_1(A_1009)) != k5_relat_1(A_1009,B_1010)
      | k2_relat_1(A_1009) != k1_relat_1(B_1010)
      | ~ v2_funct_1(A_1009)
      | ~ v1_funct_1(B_1010)
      | ~ v1_relat_1(B_1010)
      | ~ v1_funct_1(A_1009)
      | ~ v1_relat_1(A_1009) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_74])).

tff(c_19718,plain,(
    ! [A_21] :
      ( k2_funct_1(k6_partfun1(A_21)) = k6_partfun1(A_21)
      | k6_partfun1(k1_relat_1(k6_partfun1(A_21))) != k6_partfun1(A_21)
      | k2_relat_1(k6_partfun1(A_21)) != k1_relat_1(k6_partfun1(A_21))
      | ~ v2_funct_1(k6_partfun1(A_21))
      | ~ v1_funct_1(k6_partfun1(A_21))
      | ~ v1_relat_1(k6_partfun1(A_21))
      | ~ v1_funct_1(k6_partfun1(A_21))
      | ~ v1_relat_1(k6_partfun1(A_21)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_759,c_19707])).

tff(c_19734,plain,(
    ! [A_1011] : k2_funct_1(k6_partfun1(A_1011)) = k6_partfun1(A_1011) ),
    inference(demodulation,[status(thm),theory(equality)],[c_128,c_129,c_128,c_129,c_127,c_133,c_132,c_133,c_19718])).

tff(c_19772,plain,(
    ! [A_1012] :
      ( k6_partfun1(A_1012) = k2_funct_1('#skF_4')
      | A_1012 != '#skF_4' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16594,c_19734])).

tff(c_19855,plain,(
    ! [A_1012] :
      ( A_1012 != '#skF_4'
      | k2_funct_1('#skF_4') = '#skF_4'
      | A_1012 != '#skF_4' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_19772,c_16594])).

tff(c_19899,plain,(
    ! [A_1012] :
      ( A_1012 != '#skF_4'
      | A_1012 != '#skF_4' ) ),
    inference(negUnitSimplification,[status(thm)],[c_17907,c_19855])).

tff(c_19908,plain,(
    $false ),
    inference(reflexivity,[status(thm),theory(equality)],[c_19899])).

tff(c_19910,plain,(
    m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_619])).

tff(c_20207,plain,(
    v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_19910,c_20189])).

tff(c_21371,plain,
    ( k10_relat_1('#skF_4','#skF_3') = k1_relat_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_21360,c_34])).

tff(c_21382,plain,(
    k10_relat_1('#skF_4','#skF_3') = k1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20211,c_21371])).

tff(c_21439,plain,(
    ! [B_1161,A_1162] :
      ( k9_relat_1(B_1161,k10_relat_1(B_1161,A_1162)) = A_1162
      | ~ r1_tarski(A_1162,k2_relat_1(B_1161))
      | ~ v1_funct_1(B_1161)
      | ~ v1_relat_1(B_1161) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_21441,plain,(
    ! [A_1162] :
      ( k9_relat_1('#skF_4',k10_relat_1('#skF_4',A_1162)) = A_1162
      | ~ r1_tarski(A_1162,'#skF_3')
      | ~ v1_funct_1('#skF_4')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_21360,c_21439])).

tff(c_21503,plain,(
    ! [A_1163] :
      ( k9_relat_1('#skF_4',k10_relat_1('#skF_4',A_1163)) = A_1163
      | ~ r1_tarski(A_1163,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20211,c_124,c_21441])).

tff(c_21512,plain,
    ( k9_relat_1('#skF_4',k1_relat_1('#skF_4')) = '#skF_3'
    | ~ r1_tarski('#skF_3','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_21382,c_21503])).

tff(c_21520,plain,(
    k9_relat_1('#skF_4',k1_relat_1('#skF_4')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_21512])).

tff(c_22209,plain,(
    ! [A_1209,B_1210] :
      ( k9_relat_1(k2_funct_1(A_1209),k9_relat_1(A_1209,B_1210)) = B_1210
      | ~ r1_tarski(B_1210,k1_relat_1(A_1209))
      | ~ v2_funct_1(A_1209)
      | ~ v1_funct_1(A_1209)
      | ~ v1_relat_1(A_1209) ) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_22224,plain,
    ( k9_relat_1(k2_funct_1('#skF_4'),'#skF_3') = k1_relat_1('#skF_4')
    | ~ r1_tarski(k1_relat_1('#skF_4'),k1_relat_1('#skF_4'))
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_21520,c_22209])).

tff(c_22240,plain,(
    k9_relat_1(k2_funct_1('#skF_4'),'#skF_3') = k1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20211,c_124,c_118,c_14,c_22224])).

tff(c_20941,plain,(
    ! [A_1112] :
      ( k1_relat_1(k2_funct_1(A_1112)) = k2_relat_1(A_1112)
      | ~ v2_funct_1(A_1112)
      | ~ v1_funct_1(A_1112)
      | ~ v1_relat_1(A_1112) ) ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_30900,plain,(
    ! [A_1511] :
      ( k9_relat_1(k2_funct_1(A_1511),k2_relat_1(A_1511)) = k2_relat_1(k2_funct_1(A_1511))
      | ~ v1_relat_1(k2_funct_1(A_1511))
      | ~ v2_funct_1(A_1511)
      | ~ v1_funct_1(A_1511)
      | ~ v1_relat_1(A_1511) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20941,c_32])).

tff(c_30930,plain,
    ( k9_relat_1(k2_funct_1('#skF_4'),'#skF_3') = k2_relat_1(k2_funct_1('#skF_4'))
    | ~ v1_relat_1(k2_funct_1('#skF_4'))
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_21360,c_30900])).

tff(c_30947,plain,(
    k2_relat_1(k2_funct_1('#skF_4')) = k1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20211,c_124,c_118,c_20207,c_22240,c_30930])).

tff(c_31015,plain,
    ( v1_funct_2(k2_funct_1('#skF_4'),k1_relat_1(k2_funct_1('#skF_4')),k1_relat_1('#skF_4'))
    | ~ v1_funct_1(k2_funct_1('#skF_4'))
    | ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_30947,c_98])).

tff(c_31067,plain,(
    v1_funct_2(k2_funct_1('#skF_4'),k1_relat_1(k2_funct_1('#skF_4')),k1_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20207,c_620,c_31015])).

tff(c_32171,plain,
    ( v1_funct_2(k2_funct_1('#skF_4'),k2_relat_1('#skF_4'),k1_relat_1('#skF_4'))
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_72,c_31067])).

tff(c_32173,plain,(
    v1_funct_2(k2_funct_1('#skF_4'),'#skF_3',k1_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20211,c_124,c_118,c_21360,c_32171])).

tff(c_21250,plain,(
    ! [A_1146] :
      ( m1_subset_1(A_1146,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_1146),k2_relat_1(A_1146))))
      | ~ v1_funct_1(A_1146)
      | ~ v1_relat_1(A_1146) ) ),
    inference(cnfTransformation,[status(thm)],[f_214])).

tff(c_34330,plain,(
    ! [A_1583] :
      ( m1_subset_1(k2_funct_1(A_1583),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(A_1583),k2_relat_1(k2_funct_1(A_1583)))))
      | ~ v1_funct_1(k2_funct_1(A_1583))
      | ~ v1_relat_1(k2_funct_1(A_1583))
      | ~ v2_funct_1(A_1583)
      | ~ v1_funct_1(A_1583)
      | ~ v1_relat_1(A_1583) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_72,c_21250])).

tff(c_34394,plain,
    ( m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_3',k2_relat_1(k2_funct_1('#skF_4')))))
    | ~ v1_funct_1(k2_funct_1('#skF_4'))
    | ~ v1_relat_1(k2_funct_1('#skF_4'))
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_21360,c_34330])).

tff(c_34436,plain,(
    m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_3',k1_relat_1('#skF_4')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20211,c_124,c_118,c_20207,c_620,c_30947,c_34394])).

tff(c_22453,plain,(
    ! [B_1219,D_1220,A_1221,C_1222] :
      ( k1_xboole_0 = B_1219
      | v1_funct_2(D_1220,A_1221,C_1222)
      | ~ r1_tarski(B_1219,C_1222)
      | ~ m1_subset_1(D_1220,k1_zfmisc_1(k2_zfmisc_1(A_1221,B_1219)))
      | ~ v1_funct_2(D_1220,A_1221,B_1219)
      | ~ v1_funct_1(D_1220) ) ),
    inference(cnfTransformation,[status(thm)],[f_233])).

tff(c_35312,plain,(
    ! [B_1600,D_1601,A_1602,A_1603] :
      ( k1_relat_1(B_1600) = k1_xboole_0
      | v1_funct_2(D_1601,A_1602,A_1603)
      | ~ m1_subset_1(D_1601,k1_zfmisc_1(k2_zfmisc_1(A_1602,k1_relat_1(B_1600))))
      | ~ v1_funct_2(D_1601,A_1602,k1_relat_1(B_1600))
      | ~ v1_funct_1(D_1601)
      | ~ v4_relat_1(B_1600,A_1603)
      | ~ v1_relat_1(B_1600) ) ),
    inference(resolution,[status(thm)],[c_30,c_22453])).

tff(c_35316,plain,(
    ! [A_1603] :
      ( k1_relat_1('#skF_4') = k1_xboole_0
      | v1_funct_2(k2_funct_1('#skF_4'),'#skF_3',A_1603)
      | ~ v1_funct_2(k2_funct_1('#skF_4'),'#skF_3',k1_relat_1('#skF_4'))
      | ~ v1_funct_1(k2_funct_1('#skF_4'))
      | ~ v4_relat_1('#skF_4',A_1603)
      | ~ v1_relat_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_34436,c_35312])).

tff(c_35364,plain,(
    ! [A_1603] :
      ( k1_relat_1('#skF_4') = k1_xboole_0
      | v1_funct_2(k2_funct_1('#skF_4'),'#skF_3',A_1603)
      | ~ v4_relat_1('#skF_4',A_1603) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20211,c_620,c_32173,c_35316])).

tff(c_35395,plain,(
    ! [A_1604] :
      ( v1_funct_2(k2_funct_1('#skF_4'),'#skF_3',A_1604)
      | ~ v4_relat_1('#skF_4',A_1604) ) ),
    inference(negUnitSimplification,[status(thm)],[c_20245,c_35364])).

tff(c_19909,plain,(
    ~ v1_funct_2(k2_funct_1('#skF_4'),'#skF_3','#skF_2') ),
    inference(splitRight,[status(thm)],[c_619])).

tff(c_35398,plain,(
    ~ v4_relat_1('#skF_4','#skF_2') ),
    inference(resolution,[status(thm)],[c_35395,c_19909])).

tff(c_35402,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_20716,c_35398])).

tff(c_35403,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_20227])).

tff(c_35404,plain,(
    k1_relat_1('#skF_4') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_20227])).

tff(c_35435,plain,(
    k1_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_35403,c_35404])).

tff(c_42,plain,(
    ! [A_20] :
      ( k2_relat_1(A_20) = k1_xboole_0
      | k1_relat_1(A_20) != k1_xboole_0
      | ~ v1_relat_1(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_20225,plain,
    ( k2_relat_1('#skF_4') = k1_xboole_0
    | k1_relat_1('#skF_4') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_20211,c_42])).

tff(c_35433,plain,
    ( k2_relat_1('#skF_4') = '#skF_4'
    | k1_relat_1('#skF_4') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_35403,c_35403,c_20225])).

tff(c_35434,plain,(
    k1_relat_1('#skF_4') != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_35433])).

tff(c_35471,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_35435,c_35434])).

tff(c_35472,plain,(
    k2_relat_1('#skF_4') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_35433])).

tff(c_20226,plain,
    ( k2_relat_1('#skF_4') != k1_xboole_0
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_20211,c_36])).

tff(c_20244,plain,(
    k2_relat_1('#skF_4') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_20226])).

tff(c_35518,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_35472,c_35403,c_20244])).

tff(c_35519,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_20226])).

tff(c_35534,plain,(
    ! [A_8] : k2_zfmisc_1(A_8,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_35519,c_35519,c_18])).

tff(c_35520,plain,(
    k2_relat_1('#skF_4') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_20226])).

tff(c_35582,plain,(
    k2_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_35519,c_35520])).

tff(c_36410,plain,(
    ! [A_1673,B_1674,C_1675] :
      ( k2_relset_1(A_1673,B_1674,C_1675) = k2_relat_1(C_1675)
      | ~ m1_subset_1(C_1675,k1_zfmisc_1(k2_zfmisc_1(A_1673,B_1674))) ) ),
    inference(cnfTransformation,[status(thm)],[f_182])).

tff(c_36429,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_120,c_36410])).

tff(c_36436,plain,(
    '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_116,c_35582,c_36429])).

tff(c_35541,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_35519,c_8])).

tff(c_35529,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_35519,c_35519,c_679])).

tff(c_26,plain,(
    ! [C_14,B_13,A_12] :
      ( ~ v1_xboole_0(C_14)
      | ~ m1_subset_1(B_13,k1_zfmisc_1(C_14))
      | ~ r2_hidden(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_35667,plain,(
    ! [A_12] :
      ( ~ v1_xboole_0('#skF_4')
      | ~ r2_hidden(A_12,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_35529,c_26])).

tff(c_35678,plain,(
    ! [A_1615] : ~ r2_hidden(A_1615,'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_35541,c_35667])).

tff(c_35683,plain,(
    ! [B_2] : r1_tarski('#skF_4',B_2) ),
    inference(resolution,[status(thm)],[c_6,c_35678])).

tff(c_35535,plain,(
    k1_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_35519,c_35519,c_187])).

tff(c_35922,plain,(
    ! [B_1635,A_1636] :
      ( v4_relat_1(B_1635,A_1636)
      | ~ r1_tarski(k1_relat_1(B_1635),A_1636)
      | ~ v1_relat_1(B_1635) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_35928,plain,(
    ! [A_1636] :
      ( v4_relat_1('#skF_4',A_1636)
      | ~ r1_tarski('#skF_4',A_1636)
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_35535,c_35922])).

tff(c_35938,plain,(
    ! [A_1636] : v4_relat_1('#skF_4',A_1636) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20211,c_35683,c_35928])).

tff(c_35531,plain,(
    ! [A_25] :
      ( A_25 != '#skF_4'
      | k6_partfun1(A_25) = '#skF_4' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_35519,c_35519,c_252])).

tff(c_35761,plain,(
    ! [B_1622,A_1623] :
      ( r1_tarski(k1_relat_1(B_1622),A_1623)
      | ~ v4_relat_1(B_1622,A_1623)
      | ~ v1_relat_1(B_1622) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_35769,plain,(
    ! [A_21,A_1623] :
      ( r1_tarski(A_21,A_1623)
      | ~ v4_relat_1(k6_partfun1(A_21),A_1623)
      | ~ v1_relat_1(k6_partfun1(A_21)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_133,c_35761])).

tff(c_36250,plain,(
    ! [A_1656,A_1657] :
      ( r1_tarski(A_1656,A_1657)
      | ~ v4_relat_1(k6_partfun1(A_1656),A_1657) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_128,c_35769])).

tff(c_36260,plain,(
    ! [A_25,A_1657] :
      ( r1_tarski(A_25,A_1657)
      | ~ v4_relat_1('#skF_4',A_1657)
      | A_25 != '#skF_4' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_35531,c_36250])).

tff(c_36272,plain,(
    ! [A_1658,A_1659] :
      ( r1_tarski(A_1658,A_1659)
      | A_1658 != '#skF_4' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_35938,c_36260])).

tff(c_654,plain,(
    ! [A_107,B_108] :
      ( r1_tarski(A_107,B_108)
      | ~ m1_subset_1(A_107,k1_zfmisc_1(B_108)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_662,plain,(
    r1_tarski('#skF_4',k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_120,c_654])).

tff(c_20077,plain,(
    ! [B_1024,A_1025] :
      ( B_1024 = A_1025
      | ~ r1_tarski(B_1024,A_1025)
      | ~ r1_tarski(A_1025,B_1024) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_20091,plain,
    ( k2_zfmisc_1('#skF_2','#skF_3') = '#skF_4'
    | ~ r1_tarski(k2_zfmisc_1('#skF_2','#skF_3'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_662,c_20077])).

tff(c_20142,plain,(
    ~ r1_tarski(k2_zfmisc_1('#skF_2','#skF_3'),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_20091])).

tff(c_36298,plain,(
    k2_zfmisc_1('#skF_2','#skF_3') != '#skF_4' ),
    inference(resolution,[status(thm)],[c_36272,c_20142])).

tff(c_36437,plain,(
    k2_zfmisc_1('#skF_2','#skF_4') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_36436,c_36298])).

tff(c_36448,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_35534,c_36437])).

tff(c_36449,plain,(
    k2_zfmisc_1('#skF_2','#skF_3') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_20091])).

tff(c_36452,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36449,c_120])).

tff(c_36792,plain,(
    ! [C_1706,A_1707,B_1708] :
      ( v4_relat_1(C_1706,A_1707)
      | ~ m1_subset_1(C_1706,k1_zfmisc_1(k2_zfmisc_1(A_1707,B_1708))) ) ),
    inference(cnfTransformation,[status(thm)],[f_178])).

tff(c_36837,plain,(
    ! [C_1711] :
      ( v4_relat_1(C_1711,'#skF_2')
      | ~ m1_subset_1(C_1711,k1_zfmisc_1('#skF_4')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_36449,c_36792])).

tff(c_36845,plain,(
    v4_relat_1('#skF_4','#skF_2') ),
    inference(resolution,[status(thm)],[c_36452,c_36837])).

tff(c_16,plain,(
    ! [B_9,A_8] :
      ( k1_xboole_0 = B_9
      | k1_xboole_0 = A_8
      | k2_zfmisc_1(A_8,B_9) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_36457,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 != '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_36449,c_16])).

tff(c_36506,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_36457])).

tff(c_36514,plain,(
    ! [C_1680,A_1681,B_1682] :
      ( v1_relat_1(C_1680)
      | ~ m1_subset_1(C_1680,k1_zfmisc_1(k2_zfmisc_1(A_1681,B_1682))) ) ),
    inference(cnfTransformation,[status(thm)],[f_172])).

tff(c_36562,plain,(
    ! [C_1684] :
      ( v1_relat_1(C_1684)
      | ~ m1_subset_1(C_1684,k1_zfmisc_1('#skF_4')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_36449,c_36514])).

tff(c_36570,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_36452,c_36562])).

tff(c_36583,plain,
    ( k1_relat_1('#skF_4') != k1_xboole_0
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_36570,c_38])).

tff(c_36591,plain,(
    k1_relat_1('#skF_4') != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_36506,c_36583])).

tff(c_37608,plain,(
    ! [A_1773,B_1774,C_1775] :
      ( k2_relset_1(A_1773,B_1774,C_1775) = k2_relat_1(C_1775)
      | ~ m1_subset_1(C_1775,k1_zfmisc_1(k2_zfmisc_1(A_1773,B_1774))) ) ),
    inference(cnfTransformation,[status(thm)],[f_182])).

tff(c_37789,plain,(
    ! [C_1789] :
      ( k2_relset_1('#skF_2','#skF_3',C_1789) = k2_relat_1(C_1789)
      | ~ m1_subset_1(C_1789,k1_zfmisc_1('#skF_4')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_36449,c_37608])).

tff(c_37792,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_36452,c_37789])).

tff(c_37798,plain,(
    k2_relat_1('#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_116,c_37792])).

tff(c_36531,plain,(
    v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_19910,c_36514])).

tff(c_37810,plain,
    ( k10_relat_1('#skF_4','#skF_3') = k1_relat_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_37798,c_34])).

tff(c_37821,plain,(
    k10_relat_1('#skF_4','#skF_3') = k1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36570,c_37810])).

tff(c_37836,plain,(
    ! [B_1790,A_1791] :
      ( k9_relat_1(B_1790,k10_relat_1(B_1790,A_1791)) = A_1791
      | ~ r1_tarski(A_1791,k2_relat_1(B_1790))
      | ~ v1_funct_1(B_1790)
      | ~ v1_relat_1(B_1790) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_37838,plain,(
    ! [A_1791] :
      ( k9_relat_1('#skF_4',k10_relat_1('#skF_4',A_1791)) = A_1791
      | ~ r1_tarski(A_1791,'#skF_3')
      | ~ v1_funct_1('#skF_4')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_37798,c_37836])).

tff(c_40849,plain,(
    ! [A_1940] :
      ( k9_relat_1('#skF_4',k10_relat_1('#skF_4',A_1940)) = A_1940
      | ~ r1_tarski(A_1940,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36570,c_124,c_37838])).

tff(c_40861,plain,
    ( k9_relat_1('#skF_4',k1_relat_1('#skF_4')) = '#skF_3'
    | ~ r1_tarski('#skF_3','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_37821,c_40849])).

tff(c_40871,plain,(
    k9_relat_1('#skF_4',k1_relat_1('#skF_4')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_40861])).

tff(c_66,plain,(
    ! [A_28,B_30] :
      ( k9_relat_1(k2_funct_1(A_28),k9_relat_1(A_28,B_30)) = B_30
      | ~ r1_tarski(B_30,k1_relat_1(A_28))
      | ~ v2_funct_1(A_28)
      | ~ v1_funct_1(A_28)
      | ~ v1_relat_1(A_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_40877,plain,
    ( k9_relat_1(k2_funct_1('#skF_4'),'#skF_3') = k1_relat_1('#skF_4')
    | ~ r1_tarski(k1_relat_1('#skF_4'),k1_relat_1('#skF_4'))
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_40871,c_66])).

tff(c_40890,plain,(
    k9_relat_1(k2_funct_1('#skF_4'),'#skF_3') = k1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36570,c_124,c_118,c_14,c_40877])).

tff(c_37482,plain,(
    ! [A_1766] :
      ( k1_relat_1(k2_funct_1(A_1766)) = k2_relat_1(A_1766)
      | ~ v2_funct_1(A_1766)
      | ~ v1_funct_1(A_1766)
      | ~ v1_relat_1(A_1766) ) ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_46976,plain,(
    ! [A_2177] :
      ( k9_relat_1(k2_funct_1(A_2177),k2_relat_1(A_2177)) = k2_relat_1(k2_funct_1(A_2177))
      | ~ v1_relat_1(k2_funct_1(A_2177))
      | ~ v2_funct_1(A_2177)
      | ~ v1_funct_1(A_2177)
      | ~ v1_relat_1(A_2177) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_37482,c_32])).

tff(c_47006,plain,
    ( k9_relat_1(k2_funct_1('#skF_4'),'#skF_3') = k2_relat_1(k2_funct_1('#skF_4'))
    | ~ v1_relat_1(k2_funct_1('#skF_4'))
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_37798,c_46976])).

tff(c_47023,plain,(
    k2_relat_1(k2_funct_1('#skF_4')) = k1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36570,c_124,c_118,c_36531,c_40890,c_47006])).

tff(c_47129,plain,
    ( v1_funct_2(k2_funct_1('#skF_4'),k1_relat_1(k2_funct_1('#skF_4')),k1_relat_1('#skF_4'))
    | ~ v1_funct_1(k2_funct_1('#skF_4'))
    | ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_47023,c_98])).

tff(c_47186,plain,(
    v1_funct_2(k2_funct_1('#skF_4'),k1_relat_1(k2_funct_1('#skF_4')),k1_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36531,c_620,c_47129])).

tff(c_47348,plain,
    ( v1_funct_2(k2_funct_1('#skF_4'),k2_relat_1('#skF_4'),k1_relat_1('#skF_4'))
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_72,c_47186])).

tff(c_47350,plain,(
    v1_funct_2(k2_funct_1('#skF_4'),'#skF_3',k1_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36570,c_124,c_118,c_37798,c_47348])).

tff(c_36816,plain,(
    v4_relat_1(k2_funct_1('#skF_4'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_19910,c_36792])).

tff(c_37734,plain,(
    ! [A_1786] :
      ( m1_subset_1(A_1786,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_1786),k2_relat_1(A_1786))))
      | ~ v1_funct_1(A_1786)
      | ~ v1_relat_1(A_1786) ) ),
    inference(cnfTransformation,[status(thm)],[f_214])).

tff(c_22,plain,(
    ! [A_10,B_11] :
      ( r1_tarski(A_10,B_11)
      | ~ m1_subset_1(A_10,k1_zfmisc_1(B_11)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_37775,plain,(
    ! [A_1786] :
      ( r1_tarski(A_1786,k2_zfmisc_1(k1_relat_1(A_1786),k2_relat_1(A_1786)))
      | ~ v1_funct_1(A_1786)
      | ~ v1_relat_1(A_1786) ) ),
    inference(resolution,[status(thm)],[c_37734,c_22])).

tff(c_47115,plain,
    ( r1_tarski(k2_funct_1('#skF_4'),k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_4')),k1_relat_1('#skF_4')))
    | ~ v1_funct_1(k2_funct_1('#skF_4'))
    | ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_47023,c_37775])).

tff(c_47175,plain,(
    r1_tarski(k2_funct_1('#skF_4'),k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_4')),k1_relat_1('#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36531,c_620,c_47115])).

tff(c_36818,plain,(
    ! [A_10,A_1707,B_1708] :
      ( v4_relat_1(A_10,A_1707)
      | ~ r1_tarski(A_10,k2_zfmisc_1(A_1707,B_1708)) ) ),
    inference(resolution,[status(thm)],[c_24,c_36792])).

tff(c_47562,plain,(
    v4_relat_1(k2_funct_1('#skF_4'),k1_relat_1(k2_funct_1('#skF_4'))) ),
    inference(resolution,[status(thm)],[c_47175,c_36818])).

tff(c_47581,plain,(
    ! [A_2181,A_2182] :
      ( r1_tarski(k2_relat_1(A_2181),A_2182)
      | ~ v4_relat_1(k2_funct_1(A_2181),A_2182)
      | ~ v1_relat_1(k2_funct_1(A_2181))
      | ~ v2_funct_1(A_2181)
      | ~ v1_funct_1(A_2181)
      | ~ v1_relat_1(A_2181) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_37482,c_30])).

tff(c_47584,plain,
    ( r1_tarski(k2_relat_1('#skF_4'),k1_relat_1(k2_funct_1('#skF_4')))
    | ~ v1_relat_1(k2_funct_1('#skF_4'))
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_47562,c_47581])).

tff(c_47627,plain,(
    r1_tarski('#skF_3',k1_relat_1(k2_funct_1('#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36570,c_124,c_118,c_36531,c_37798,c_47584])).

tff(c_36667,plain,(
    ! [B_1695,A_1696] :
      ( r1_tarski(k1_relat_1(B_1695),A_1696)
      | ~ v4_relat_1(B_1695,A_1696)
      | ~ v1_relat_1(B_1695) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_10,plain,(
    ! [B_7,A_6] :
      ( B_7 = A_6
      | ~ r1_tarski(B_7,A_6)
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_36691,plain,(
    ! [B_1695,A_1696] :
      ( k1_relat_1(B_1695) = A_1696
      | ~ r1_tarski(A_1696,k1_relat_1(B_1695))
      | ~ v4_relat_1(B_1695,A_1696)
      | ~ v1_relat_1(B_1695) ) ),
    inference(resolution,[status(thm)],[c_36667,c_10])).

tff(c_47651,plain,
    ( k1_relat_1(k2_funct_1('#skF_4')) = '#skF_3'
    | ~ v4_relat_1(k2_funct_1('#skF_4'),'#skF_3')
    | ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_47627,c_36691])).

tff(c_47685,plain,(
    k1_relat_1(k2_funct_1('#skF_4')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_36531,c_36816,c_47651])).

tff(c_96,plain,(
    ! [A_56] :
      ( m1_subset_1(A_56,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_56),k2_relat_1(A_56))))
      | ~ v1_funct_1(A_56)
      | ~ v1_relat_1(A_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_214])).

tff(c_47767,plain,
    ( m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_3',k2_relat_1(k2_funct_1('#skF_4')))))
    | ~ v1_funct_1(k2_funct_1('#skF_4'))
    | ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_47685,c_96])).

tff(c_47840,plain,(
    m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_3',k1_relat_1('#skF_4')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36531,c_620,c_47023,c_47767])).

tff(c_38733,plain,(
    ! [B_1861,D_1862,A_1863,C_1864] :
      ( k1_xboole_0 = B_1861
      | v1_funct_2(D_1862,A_1863,C_1864)
      | ~ r1_tarski(B_1861,C_1864)
      | ~ m1_subset_1(D_1862,k1_zfmisc_1(k2_zfmisc_1(A_1863,B_1861)))
      | ~ v1_funct_2(D_1862,A_1863,B_1861)
      | ~ v1_funct_1(D_1862) ) ),
    inference(cnfTransformation,[status(thm)],[f_233])).

tff(c_50862,plain,(
    ! [B_2264,D_2265,A_2266,A_2267] :
      ( k1_relat_1(B_2264) = k1_xboole_0
      | v1_funct_2(D_2265,A_2266,A_2267)
      | ~ m1_subset_1(D_2265,k1_zfmisc_1(k2_zfmisc_1(A_2266,k1_relat_1(B_2264))))
      | ~ v1_funct_2(D_2265,A_2266,k1_relat_1(B_2264))
      | ~ v1_funct_1(D_2265)
      | ~ v4_relat_1(B_2264,A_2267)
      | ~ v1_relat_1(B_2264) ) ),
    inference(resolution,[status(thm)],[c_30,c_38733])).

tff(c_50872,plain,(
    ! [A_2267] :
      ( k1_relat_1('#skF_4') = k1_xboole_0
      | v1_funct_2(k2_funct_1('#skF_4'),'#skF_3',A_2267)
      | ~ v1_funct_2(k2_funct_1('#skF_4'),'#skF_3',k1_relat_1('#skF_4'))
      | ~ v1_funct_1(k2_funct_1('#skF_4'))
      | ~ v4_relat_1('#skF_4',A_2267)
      | ~ v1_relat_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_47840,c_50862])).

tff(c_50919,plain,(
    ! [A_2267] :
      ( k1_relat_1('#skF_4') = k1_xboole_0
      | v1_funct_2(k2_funct_1('#skF_4'),'#skF_3',A_2267)
      | ~ v4_relat_1('#skF_4',A_2267) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36570,c_620,c_47350,c_50872])).

tff(c_50944,plain,(
    ! [A_2268] :
      ( v1_funct_2(k2_funct_1('#skF_4'),'#skF_3',A_2268)
      | ~ v4_relat_1('#skF_4',A_2268) ) ),
    inference(negUnitSimplification,[status(thm)],[c_36591,c_50919])).

tff(c_50947,plain,(
    ~ v4_relat_1('#skF_4','#skF_2') ),
    inference(resolution,[status(thm)],[c_50944,c_19909])).

tff(c_50951,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_36845,c_50947])).

tff(c_50953,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_36457])).

tff(c_622,plain,(
    ! [A_105] :
      ( k1_xboole_0 != A_105
      | k6_partfun1(A_105) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_133,c_245])).

tff(c_90,plain,(
    ! [A_54] : v1_partfun1(k6_partfun1(A_54),A_54) ),
    inference(cnfTransformation,[status(thm)],[f_202])).

tff(c_631,plain,(
    ! [A_105] :
      ( v1_partfun1(k1_xboole_0,A_105)
      | k1_xboole_0 != A_105 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_622,c_90])).

tff(c_51157,plain,(
    v1_partfun1('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50953,c_50953,c_631])).

tff(c_50964,plain,(
    ! [A_25] :
      ( A_25 != '#skF_4'
      | k6_partfun1(A_25) = '#skF_4' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50953,c_50953,c_252])).

tff(c_50967,plain,(
    ! [A_8] : k2_zfmisc_1(A_8,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_50953,c_50953,c_18])).

tff(c_51899,plain,(
    ! [C_2325,A_2326,B_2327] :
      ( v4_relat_1(C_2325,A_2326)
      | ~ m1_subset_1(C_2325,k1_zfmisc_1(k2_zfmisc_1(A_2326,B_2327))) ) ),
    inference(cnfTransformation,[status(thm)],[f_178])).

tff(c_52261,plain,(
    ! [C_2368,A_2369] :
      ( v4_relat_1(C_2368,A_2369)
      | ~ m1_subset_1(C_2368,k1_zfmisc_1('#skF_4')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_50967,c_51899])).

tff(c_52323,plain,(
    ! [A_2374,A_2375] :
      ( v4_relat_1(A_2374,A_2375)
      | ~ r1_tarski(A_2374,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_24,c_52261])).

tff(c_51970,plain,(
    ! [B_2332,A_2333] :
      ( r1_tarski(k1_relat_1(B_2332),A_2333)
      | ~ v4_relat_1(B_2332,A_2333)
      | ~ v1_relat_1(B_2332) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_51978,plain,(
    ! [A_21,A_2333] :
      ( r1_tarski(A_21,A_2333)
      | ~ v4_relat_1(k6_partfun1(A_21),A_2333)
      | ~ v1_relat_1(k6_partfun1(A_21)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_133,c_51970])).

tff(c_51983,plain,(
    ! [A_21,A_2333] :
      ( r1_tarski(A_21,A_2333)
      | ~ v4_relat_1(k6_partfun1(A_21),A_2333) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_128,c_51978])).

tff(c_52394,plain,(
    ! [A_2383,A_2384] :
      ( r1_tarski(A_2383,A_2384)
      | ~ r1_tarski(k6_partfun1(A_2383),'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_52323,c_51983])).

tff(c_52396,plain,(
    ! [A_25,A_2384] :
      ( r1_tarski(A_25,A_2384)
      | ~ r1_tarski('#skF_4','#skF_4')
      | A_25 != '#skF_4' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_50964,c_52394])).

tff(c_52399,plain,(
    ! [A_2384] : r1_tarski('#skF_4',A_2384) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_52396])).

tff(c_50966,plain,(
    k2_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_50953,c_50953,c_226])).

tff(c_669,plain,(
    ! [A_25] :
      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(A_25,A_25)))
      | k1_xboole_0 != A_25 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_252,c_663])).

tff(c_53185,plain,(
    ! [A_2473] :
      ( m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(A_2473,A_2473)))
      | A_2473 != '#skF_4' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50953,c_50953,c_669])).

tff(c_84,plain,(
    ! [D_50,C_49,B_48,A_47] :
      ( m1_subset_1(D_50,k1_zfmisc_1(k2_zfmisc_1(C_49,B_48)))
      | ~ r1_tarski(k2_relat_1(D_50),B_48)
      | ~ m1_subset_1(D_50,k1_zfmisc_1(k2_zfmisc_1(C_49,A_47))) ) ),
    inference(cnfTransformation,[status(thm)],[f_188])).

tff(c_53187,plain,(
    ! [A_2473,B_48] :
      ( m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(A_2473,B_48)))
      | ~ r1_tarski(k2_relat_1('#skF_4'),B_48)
      | A_2473 != '#skF_4' ) ),
    inference(resolution,[status(thm)],[c_53185,c_84])).

tff(c_53757,plain,(
    ! [A_2508,B_2509] :
      ( m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(A_2508,B_2509)))
      | A_2508 != '#skF_4' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52399,c_50966,c_53187])).

tff(c_86,plain,(
    ! [C_53,A_51,B_52] :
      ( v1_funct_2(C_53,A_51,B_52)
      | ~ v1_partfun1(C_53,A_51)
      | ~ v1_funct_1(C_53)
      | ~ m1_subset_1(C_53,k1_zfmisc_1(k2_zfmisc_1(A_51,B_52))) ) ),
    inference(cnfTransformation,[status(thm)],[f_198])).

tff(c_53762,plain,(
    ! [A_2508,B_2509] :
      ( v1_funct_2('#skF_4',A_2508,B_2509)
      | ~ v1_partfun1('#skF_4',A_2508)
      | ~ v1_funct_1('#skF_4')
      | A_2508 != '#skF_4' ) ),
    inference(resolution,[status(thm)],[c_53757,c_86])).

tff(c_54034,plain,(
    ! [A_2529,B_2530] :
      ( v1_funct_2('#skF_4',A_2529,B_2530)
      | ~ v1_partfun1('#skF_4',A_2529)
      | A_2529 != '#skF_4' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_124,c_53762])).

tff(c_20,plain,(
    ! [B_9] : k2_zfmisc_1(k1_xboole_0,B_9) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_50969,plain,(
    ! [B_9] : k2_zfmisc_1('#skF_4',B_9) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_50953,c_50953,c_20])).

tff(c_50952,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_36457])).

tff(c_51653,plain,
    ( '#skF_2' = '#skF_4'
    | '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_50953,c_50953,c_50952])).

tff(c_51654,plain,(
    '#skF_3' = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_51653])).

tff(c_50974,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50953,c_8])).

tff(c_51624,plain,(
    ! [C_2312,B_2313,A_2314] :
      ( ~ v1_xboole_0(C_2312)
      | ~ m1_subset_1(B_2313,k1_zfmisc_1(C_2312))
      | ~ r2_hidden(A_2314,B_2313) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_51628,plain,(
    ! [A_2314] :
      ( ~ v1_xboole_0('#skF_4')
      | ~ r2_hidden(A_2314,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_36452,c_51624])).

tff(c_51641,plain,(
    ! [A_2315] : ~ r2_hidden(A_2315,'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50974,c_51628])).

tff(c_51646,plain,(
    ! [B_2] : r1_tarski('#skF_4',B_2) ),
    inference(resolution,[status(thm)],[c_6,c_51641])).

tff(c_51344,plain,(
    ! [C_2290,B_2291,A_2292] :
      ( ~ v1_xboole_0(C_2290)
      | ~ m1_subset_1(B_2291,k1_zfmisc_1(C_2290))
      | ~ r2_hidden(A_2292,B_2291) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_51348,plain,(
    ! [A_2292] :
      ( ~ v1_xboole_0('#skF_4')
      | ~ r2_hidden(A_2292,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_36452,c_51344])).

tff(c_51361,plain,(
    ! [A_2293] : ~ r2_hidden(A_2293,'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50974,c_51348])).

tff(c_51366,plain,(
    ! [B_2] : r1_tarski('#skF_4',B_2) ),
    inference(resolution,[status(thm)],[c_6,c_51361])).

tff(c_51085,plain,
    ( '#skF_2' = '#skF_4'
    | '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_50953,c_50953,c_50952])).

tff(c_51086,plain,(
    '#skF_3' = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_51085])).

tff(c_19929,plain,(
    r1_tarski(k2_funct_1('#skF_4'),k2_zfmisc_1('#skF_3','#skF_2')) ),
    inference(resolution,[status(thm)],[c_19910,c_22])).

tff(c_20089,plain,
    ( k2_zfmisc_1('#skF_3','#skF_2') = k2_funct_1('#skF_4')
    | ~ r1_tarski(k2_zfmisc_1('#skF_3','#skF_2'),k2_funct_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_19929,c_20077])).

tff(c_50982,plain,(
    ~ r1_tarski(k2_zfmisc_1('#skF_3','#skF_2'),k2_funct_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_20089])).

tff(c_51245,plain,(
    ~ r1_tarski('#skF_4',k2_funct_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50969,c_51086,c_50982])).

tff(c_51370,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_51366,c_51245])).

tff(c_51371,plain,(
    '#skF_2' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_51085])).

tff(c_51522,plain,(
    ~ r1_tarski('#skF_4',k2_funct_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50967,c_51371,c_50982])).

tff(c_51650,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_51646,c_51522])).

tff(c_51651,plain,(
    k2_zfmisc_1('#skF_3','#skF_2') = k2_funct_1('#skF_4') ),
    inference(splitRight,[status(thm)],[c_20089])).

tff(c_51827,plain,(
    k2_funct_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_50969,c_51654,c_51651])).

tff(c_51658,plain,(
    ~ v1_funct_2(k2_funct_1('#skF_4'),'#skF_4','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_51654,c_19909])).

tff(c_51897,plain,(
    ~ v1_funct_2('#skF_4','#skF_4','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_51827,c_51658])).

tff(c_54037,plain,(
    ~ v1_partfun1('#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_54034,c_51897])).

tff(c_54041,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_51157,c_54037])).

tff(c_54043,plain,(
    '#skF_3' != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_51653])).

tff(c_54322,plain,(
    ! [C_2544,B_2545,A_2546] :
      ( ~ v1_xboole_0(C_2544)
      | ~ m1_subset_1(B_2545,k1_zfmisc_1(C_2544))
      | ~ r2_hidden(A_2546,B_2545) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_54324,plain,(
    ! [A_2546] :
      ( ~ v1_xboole_0('#skF_4')
      | ~ r2_hidden(A_2546,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_36452,c_54322])).

tff(c_54334,plain,(
    ! [A_2547] : ~ r2_hidden(A_2547,'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50974,c_54324])).

tff(c_54339,plain,(
    ! [B_2] : r1_tarski('#skF_4',B_2) ),
    inference(resolution,[status(thm)],[c_6,c_54334])).

tff(c_162,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_151,c_128])).

tff(c_50972,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50953,c_162])).

tff(c_50968,plain,(
    k1_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_50953,c_50953,c_187])).

tff(c_54235,plain,(
    ! [B_2539,A_2540] :
      ( v4_relat_1(B_2539,A_2540)
      | ~ r1_tarski(k1_relat_1(B_2539),A_2540)
      | ~ v1_relat_1(B_2539) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_54238,plain,(
    ! [A_2540] :
      ( v4_relat_1('#skF_4',A_2540)
      | ~ r1_tarski('#skF_4',A_2540)
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_50968,c_54235])).

tff(c_54247,plain,(
    ! [A_2540] :
      ( v4_relat_1('#skF_4',A_2540)
      | ~ r1_tarski('#skF_4',A_2540) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50972,c_54238])).

tff(c_54430,plain,(
    ! [A_2540] : v4_relat_1('#skF_4',A_2540) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54339,c_54247])).

tff(c_54406,plain,(
    ! [B_2553,A_2554] :
      ( r1_tarski(k1_relat_1(B_2553),A_2554)
      | ~ v4_relat_1(B_2553,A_2554)
      | ~ v1_relat_1(B_2553) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_54421,plain,(
    ! [A_21,A_2554] :
      ( r1_tarski(A_21,A_2554)
      | ~ v4_relat_1(k6_partfun1(A_21),A_2554)
      | ~ v1_relat_1(k6_partfun1(A_21)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_133,c_54406])).

tff(c_54490,plain,(
    ! [A_2561,A_2562] :
      ( r1_tarski(A_2561,A_2562)
      | ~ v4_relat_1(k6_partfun1(A_2561),A_2562) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_128,c_54421])).

tff(c_54503,plain,(
    ! [A_25,A_2562] :
      ( r1_tarski(A_25,A_2562)
      | ~ v4_relat_1('#skF_4',A_2562)
      | A_25 != '#skF_4' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_50964,c_54490])).

tff(c_54532,plain,(
    ! [A_2562] : r1_tarski('#skF_4',A_2562) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54430,c_54503])).

tff(c_55319,plain,(
    ! [A_25] :
      ( m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(A_25,A_25)))
      | A_25 != '#skF_4' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50953,c_50953,c_669])).

tff(c_55611,plain,(
    ! [D_2688,C_2689,B_2690,A_2691] :
      ( m1_subset_1(D_2688,k1_zfmisc_1(k2_zfmisc_1(C_2689,B_2690)))
      | ~ r1_tarski(k2_relat_1(D_2688),B_2690)
      | ~ m1_subset_1(D_2688,k1_zfmisc_1(k2_zfmisc_1(C_2689,A_2691))) ) ),
    inference(cnfTransformation,[status(thm)],[f_188])).

tff(c_55613,plain,(
    ! [A_25,B_2690] :
      ( m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(A_25,B_2690)))
      | ~ r1_tarski(k2_relat_1('#skF_4'),B_2690)
      | A_25 != '#skF_4' ) ),
    inference(resolution,[status(thm)],[c_55319,c_55611])).

tff(c_55694,plain,(
    ! [A_2699,B_2700] :
      ( m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(A_2699,B_2700)))
      | A_2699 != '#skF_4' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54532,c_50966,c_55613])).

tff(c_82,plain,(
    ! [A_44,B_45,C_46] :
      ( k2_relset_1(A_44,B_45,C_46) = k2_relat_1(C_46)
      | ~ m1_subset_1(C_46,k1_zfmisc_1(k2_zfmisc_1(A_44,B_45))) ) ),
    inference(cnfTransformation,[status(thm)],[f_182])).

tff(c_55702,plain,(
    ! [A_2699,B_2700] :
      ( k2_relset_1(A_2699,B_2700,'#skF_4') = k2_relat_1('#skF_4')
      | A_2699 != '#skF_4' ) ),
    inference(resolution,[status(thm)],[c_55694,c_82])).

tff(c_55743,plain,(
    ! [B_2700] : k2_relset_1('#skF_4',B_2700,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_50966,c_55702])).

tff(c_54042,plain,(
    '#skF_2' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_51653])).

tff(c_54048,plain,(
    k2_relset_1('#skF_4','#skF_3','#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_54042,c_116])).

tff(c_55744,plain,(
    '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_55743,c_54048])).

tff(c_55746,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_54043,c_55744])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:19:05 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 17.81/9.23  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 17.95/9.29  
% 17.95/9.29  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 17.95/9.30  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r2_hidden > r1_tarski > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k9_relat_1 > k5_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 17.95/9.30  
% 17.95/9.30  %Foreground sorts:
% 17.95/9.30  
% 17.95/9.30  
% 17.95/9.30  %Background operators:
% 17.95/9.30  
% 17.95/9.30  
% 17.95/9.30  %Foreground operators:
% 17.95/9.30  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 17.95/9.30  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 17.95/9.30  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 17.95/9.30  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 17.95/9.30  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 17.95/9.30  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 17.95/9.30  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 17.95/9.30  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 17.95/9.30  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 17.95/9.30  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 17.95/9.30  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 17.95/9.30  tff('#skF_2', type, '#skF_2': $i).
% 17.95/9.30  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 17.95/9.30  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 17.95/9.30  tff('#skF_3', type, '#skF_3': $i).
% 17.95/9.30  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 17.95/9.30  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 17.95/9.30  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 17.95/9.30  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 17.95/9.30  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 17.95/9.30  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 17.95/9.30  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 17.95/9.30  tff('#skF_4', type, '#skF_4': $i).
% 17.95/9.30  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 17.95/9.30  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 17.95/9.30  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 17.95/9.30  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 17.95/9.30  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 17.95/9.30  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 17.95/9.30  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 17.95/9.30  
% 18.26/9.34  tff(f_250, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((v2_funct_1(C) & (k2_relset_1(A, B, C) = B)) => ((v1_funct_1(k2_funct_1(C)) & v1_funct_2(k2_funct_1(C), B, A)) & m1_subset_1(k2_funct_1(C), k1_zfmisc_1(k2_zfmisc_1(B, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_funct_2)).
% 18.26/9.34  tff(f_178, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 18.26/9.34  tff(f_172, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 18.26/9.34  tff(f_78, axiom, (![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_relat_1)).
% 18.26/9.34  tff(f_101, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 18.26/9.34  tff(f_182, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 18.26/9.34  tff(f_151, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k2_relat_1(A) = k1_relat_1(k2_funct_1(A))) & (k1_relat_1(A) = k2_relat_1(k2_funct_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_funct_1)).
% 18.26/9.34  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 18.26/9.34  tff(f_39, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 18.26/9.34  tff(f_70, axiom, (![A]: (v1_relat_1(A) => (k10_relat_1(A, k2_relat_1(A)) = k1_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t169_relat_1)).
% 18.26/9.34  tff(f_117, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r1_tarski(A, k2_relat_1(B)) => (k9_relat_1(B, k10_relat_1(B, A)) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t147_funct_1)).
% 18.26/9.34  tff(f_128, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v2_funct_1(A) & r1_tarski(B, k1_relat_1(A))) => (k9_relat_1(k2_funct_1(A), k9_relat_1(A, B)) = B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t177_funct_1)).
% 18.26/9.34  tff(f_66, axiom, (![A]: (v1_relat_1(A) => (k9_relat_1(A, k1_relat_1(A)) = k2_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t146_relat_1)).
% 18.26/9.34  tff(f_214, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => ((v1_funct_1(A) & v1_funct_2(A, k1_relat_1(A), k2_relat_1(A))) & m1_subset_1(A, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_funct_2)).
% 18.26/9.34  tff(f_62, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d18_relat_1)).
% 18.26/9.34  tff(f_233, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r1_tarski(B, C) => (((B = k1_xboole_0) & ~(A = k1_xboole_0)) | ((v1_funct_1(D) & v1_funct_2(D, A, C)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t9_funct_2)).
% 18.26/9.34  tff(f_204, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 18.26/9.34  tff(f_93, axiom, (k6_relat_1(k1_xboole_0) = k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t81_relat_1)).
% 18.26/9.34  tff(f_88, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 18.26/9.34  tff(f_33, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 18.26/9.34  tff(f_109, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v2_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc4_funct_1)).
% 18.26/9.34  tff(f_45, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 18.26/9.34  tff(f_202, axiom, (![A]: (v1_partfun1(k6_partfun1(A), A) & m1_subset_1(k6_partfun1(A), k1_zfmisc_1(k2_zfmisc_1(A, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_partfun1)).
% 18.26/9.34  tff(f_56, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_subset)).
% 18.26/9.34  tff(f_49, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 18.26/9.34  tff(f_105, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v1_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc3_funct_1)).
% 18.26/9.34  tff(f_92, axiom, (![A]: (v1_relat_1(A) => (k5_relat_1(A, k6_relat_1(k2_relat_1(A))) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t80_relat_1)).
% 18.26/9.34  tff(f_168, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (((v2_funct_1(A) & (k2_relat_1(A) = k1_relat_1(B))) & (k5_relat_1(A, B) = k6_relat_1(k1_relat_1(A)))) => (B = k2_funct_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_funct_1)).
% 18.26/9.34  tff(f_84, axiom, (![A]: (v1_relat_1(A) => ((k1_relat_1(A) = k1_xboole_0) <=> (k2_relat_1(A) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_relat_1)).
% 18.26/9.34  tff(f_188, axiom, (![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(C, A))) => (r1_tarski(k2_relat_1(D), B) => m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(C, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t14_relset_1)).
% 18.26/9.34  tff(f_198, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v1_partfun1(C, A)) => (v1_funct_1(C) & v1_funct_2(C, A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_funct_2)).
% 18.26/9.34  tff(c_120, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_250])).
% 18.26/9.34  tff(c_20692, plain, (![C_1086, A_1087, B_1088]: (v4_relat_1(C_1086, A_1087) | ~m1_subset_1(C_1086, k1_zfmisc_1(k2_zfmisc_1(A_1087, B_1088))))), inference(cnfTransformation, [status(thm)], [f_178])).
% 18.26/9.34  tff(c_20716, plain, (v4_relat_1('#skF_4', '#skF_2')), inference(resolution, [status(thm)], [c_120, c_20692])).
% 18.26/9.34  tff(c_20189, plain, (![C_1034, A_1035, B_1036]: (v1_relat_1(C_1034) | ~m1_subset_1(C_1034, k1_zfmisc_1(k2_zfmisc_1(A_1035, B_1036))))), inference(cnfTransformation, [status(thm)], [f_172])).
% 18.26/9.34  tff(c_20211, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_120, c_20189])).
% 18.26/9.34  tff(c_38, plain, (![A_19]: (k1_relat_1(A_19)!=k1_xboole_0 | k1_xboole_0=A_19 | ~v1_relat_1(A_19))), inference(cnfTransformation, [status(thm)], [f_78])).
% 18.26/9.34  tff(c_20227, plain, (k1_relat_1('#skF_4')!=k1_xboole_0 | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_20211, c_38])).
% 18.26/9.34  tff(c_20245, plain, (k1_relat_1('#skF_4')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_20227])).
% 18.26/9.34  tff(c_124, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_250])).
% 18.26/9.34  tff(c_52, plain, (![A_23]: (v1_funct_1(k2_funct_1(A_23)) | ~v1_funct_1(A_23) | ~v1_relat_1(A_23))), inference(cnfTransformation, [status(thm)], [f_101])).
% 18.26/9.34  tff(c_114, plain, (~m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2'))) | ~v1_funct_2(k2_funct_1('#skF_4'), '#skF_3', '#skF_2') | ~v1_funct_1(k2_funct_1('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_250])).
% 18.26/9.34  tff(c_253, plain, (~v1_funct_1(k2_funct_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_114])).
% 18.26/9.34  tff(c_256, plain, (~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_52, c_253])).
% 18.26/9.34  tff(c_259, plain, (~v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_124, c_256])).
% 18.26/9.34  tff(c_597, plain, (![C_102, A_103, B_104]: (v1_relat_1(C_102) | ~m1_subset_1(C_102, k1_zfmisc_1(k2_zfmisc_1(A_103, B_104))))), inference(cnfTransformation, [status(thm)], [f_172])).
% 18.26/9.34  tff(c_607, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_120, c_597])).
% 18.26/9.34  tff(c_618, plain, $false, inference(negUnitSimplification, [status(thm)], [c_259, c_607])).
% 18.26/9.34  tff(c_620, plain, (v1_funct_1(k2_funct_1('#skF_4'))), inference(splitRight, [status(thm)], [c_114])).
% 18.26/9.34  tff(c_118, plain, (v2_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_250])).
% 18.26/9.34  tff(c_116, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_4')='#skF_3'), inference(cnfTransformation, [status(thm)], [f_250])).
% 18.26/9.34  tff(c_21326, plain, (![A_1157, B_1158, C_1159]: (k2_relset_1(A_1157, B_1158, C_1159)=k2_relat_1(C_1159) | ~m1_subset_1(C_1159, k1_zfmisc_1(k2_zfmisc_1(A_1157, B_1158))))), inference(cnfTransformation, [status(thm)], [f_182])).
% 18.26/9.34  tff(c_21345, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_120, c_21326])).
% 18.26/9.34  tff(c_21360, plain, (k2_relat_1('#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_116, c_21345])).
% 18.26/9.34  tff(c_72, plain, (![A_34]: (k1_relat_1(k2_funct_1(A_34))=k2_relat_1(A_34) | ~v2_funct_1(A_34) | ~v1_funct_1(A_34) | ~v1_relat_1(A_34))), inference(cnfTransformation, [status(thm)], [f_151])).
% 18.26/9.34  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 18.26/9.34  tff(c_1197, plain, (![C_165, A_166, B_167]: (v4_relat_1(C_165, A_166) | ~m1_subset_1(C_165, k1_zfmisc_1(k2_zfmisc_1(A_166, B_167))))), inference(cnfTransformation, [status(thm)], [f_178])).
% 18.26/9.34  tff(c_1216, plain, (v4_relat_1('#skF_4', '#skF_2')), inference(resolution, [status(thm)], [c_120, c_1197])).
% 18.26/9.34  tff(c_887, plain, (![C_127, A_128, B_129]: (v1_relat_1(C_127) | ~m1_subset_1(C_127, k1_zfmisc_1(k2_zfmisc_1(A_128, B_129))))), inference(cnfTransformation, [status(thm)], [f_172])).
% 18.26/9.34  tff(c_905, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_120, c_887])).
% 18.26/9.34  tff(c_917, plain, (k1_relat_1('#skF_4')!=k1_xboole_0 | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_905, c_38])).
% 18.26/9.34  tff(c_919, plain, (k1_relat_1('#skF_4')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_917])).
% 18.26/9.34  tff(c_1621, plain, (![A_213, B_214, C_215]: (k2_relset_1(A_213, B_214, C_215)=k2_relat_1(C_215) | ~m1_subset_1(C_215, k1_zfmisc_1(k2_zfmisc_1(A_213, B_214))))), inference(cnfTransformation, [status(thm)], [f_182])).
% 18.26/9.34  tff(c_1631, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_120, c_1621])).
% 18.26/9.34  tff(c_1642, plain, (k2_relat_1('#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_116, c_1631])).
% 18.26/9.34  tff(c_54, plain, (![A_23]: (v1_relat_1(k2_funct_1(A_23)) | ~v1_funct_1(A_23) | ~v1_relat_1(A_23))), inference(cnfTransformation, [status(thm)], [f_101])).
% 18.26/9.34  tff(c_14, plain, (![B_7]: (r1_tarski(B_7, B_7))), inference(cnfTransformation, [status(thm)], [f_39])).
% 18.26/9.34  tff(c_34, plain, (![A_18]: (k10_relat_1(A_18, k2_relat_1(A_18))=k1_relat_1(A_18) | ~v1_relat_1(A_18))), inference(cnfTransformation, [status(thm)], [f_70])).
% 18.26/9.34  tff(c_1650, plain, (k10_relat_1('#skF_4', '#skF_3')=k1_relat_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1642, c_34])).
% 18.26/9.34  tff(c_1659, plain, (k10_relat_1('#skF_4', '#skF_3')=k1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_905, c_1650])).
% 18.26/9.34  tff(c_1885, plain, (![B_234, A_235]: (k9_relat_1(B_234, k10_relat_1(B_234, A_235))=A_235 | ~r1_tarski(A_235, k2_relat_1(B_234)) | ~v1_funct_1(B_234) | ~v1_relat_1(B_234))), inference(cnfTransformation, [status(thm)], [f_117])).
% 18.26/9.34  tff(c_1887, plain, (![A_235]: (k9_relat_1('#skF_4', k10_relat_1('#skF_4', A_235))=A_235 | ~r1_tarski(A_235, '#skF_3') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_1642, c_1885])).
% 18.26/9.34  tff(c_2084, plain, (![A_255]: (k9_relat_1('#skF_4', k10_relat_1('#skF_4', A_255))=A_255 | ~r1_tarski(A_255, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_905, c_124, c_1887])).
% 18.26/9.34  tff(c_2093, plain, (k9_relat_1('#skF_4', k1_relat_1('#skF_4'))='#skF_3' | ~r1_tarski('#skF_3', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1659, c_2084])).
% 18.26/9.34  tff(c_2101, plain, (k9_relat_1('#skF_4', k1_relat_1('#skF_4'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_14, c_2093])).
% 18.26/9.34  tff(c_2467, plain, (![A_281, B_282]: (k9_relat_1(k2_funct_1(A_281), k9_relat_1(A_281, B_282))=B_282 | ~r1_tarski(B_282, k1_relat_1(A_281)) | ~v2_funct_1(A_281) | ~v1_funct_1(A_281) | ~v1_relat_1(A_281))), inference(cnfTransformation, [status(thm)], [f_128])).
% 18.26/9.34  tff(c_2482, plain, (k9_relat_1(k2_funct_1('#skF_4'), '#skF_3')=k1_relat_1('#skF_4') | ~r1_tarski(k1_relat_1('#skF_4'), k1_relat_1('#skF_4')) | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_2101, c_2467])).
% 18.26/9.34  tff(c_2498, plain, (k9_relat_1(k2_funct_1('#skF_4'), '#skF_3')=k1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_905, c_124, c_118, c_14, c_2482])).
% 18.26/9.34  tff(c_1481, plain, (![A_195]: (k1_relat_1(k2_funct_1(A_195))=k2_relat_1(A_195) | ~v2_funct_1(A_195) | ~v1_funct_1(A_195) | ~v1_relat_1(A_195))), inference(cnfTransformation, [status(thm)], [f_151])).
% 18.26/9.34  tff(c_32, plain, (![A_17]: (k9_relat_1(A_17, k1_relat_1(A_17))=k2_relat_1(A_17) | ~v1_relat_1(A_17))), inference(cnfTransformation, [status(thm)], [f_66])).
% 18.26/9.34  tff(c_12733, plain, (![A_647]: (k9_relat_1(k2_funct_1(A_647), k2_relat_1(A_647))=k2_relat_1(k2_funct_1(A_647)) | ~v1_relat_1(k2_funct_1(A_647)) | ~v2_funct_1(A_647) | ~v1_funct_1(A_647) | ~v1_relat_1(A_647))), inference(superposition, [status(thm), theory('equality')], [c_1481, c_32])).
% 18.26/9.34  tff(c_12766, plain, (k9_relat_1(k2_funct_1('#skF_4'), '#skF_3')=k2_relat_1(k2_funct_1('#skF_4')) | ~v1_relat_1(k2_funct_1('#skF_4')) | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1642, c_12733])).
% 18.26/9.34  tff(c_12785, plain, (k2_relat_1(k2_funct_1('#skF_4'))=k1_relat_1('#skF_4') | ~v1_relat_1(k2_funct_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_905, c_124, c_118, c_2498, c_12766])).
% 18.26/9.34  tff(c_12790, plain, (~v1_relat_1(k2_funct_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_12785])).
% 18.26/9.34  tff(c_12799, plain, (~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_54, c_12790])).
% 18.26/9.34  tff(c_12805, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_905, c_124, c_12799])).
% 18.26/9.34  tff(c_12807, plain, (v1_relat_1(k2_funct_1('#skF_4'))), inference(splitRight, [status(thm)], [c_12785])).
% 18.26/9.34  tff(c_12806, plain, (k2_relat_1(k2_funct_1('#skF_4'))=k1_relat_1('#skF_4')), inference(splitRight, [status(thm)], [c_12785])).
% 18.26/9.34  tff(c_98, plain, (![A_56]: (v1_funct_2(A_56, k1_relat_1(A_56), k2_relat_1(A_56)) | ~v1_funct_1(A_56) | ~v1_relat_1(A_56))), inference(cnfTransformation, [status(thm)], [f_214])).
% 18.26/9.34  tff(c_12936, plain, (v1_funct_2(k2_funct_1('#skF_4'), k1_relat_1(k2_funct_1('#skF_4')), k1_relat_1('#skF_4')) | ~v1_funct_1(k2_funct_1('#skF_4')) | ~v1_relat_1(k2_funct_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_12806, c_98])).
% 18.26/9.34  tff(c_12988, plain, (v1_funct_2(k2_funct_1('#skF_4'), k1_relat_1(k2_funct_1('#skF_4')), k1_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_12807, c_620, c_12936])).
% 18.26/9.34  tff(c_14093, plain, (v1_funct_2(k2_funct_1('#skF_4'), k2_relat_1('#skF_4'), k1_relat_1('#skF_4')) | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_72, c_12988])).
% 18.26/9.34  tff(c_14095, plain, (v1_funct_2(k2_funct_1('#skF_4'), '#skF_3', k1_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_905, c_124, c_118, c_1642, c_14093])).
% 18.26/9.34  tff(c_1732, plain, (![A_223]: (m1_subset_1(A_223, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_223), k2_relat_1(A_223)))) | ~v1_funct_1(A_223) | ~v1_relat_1(A_223))), inference(cnfTransformation, [status(thm)], [f_214])).
% 18.26/9.34  tff(c_14886, plain, (![A_696]: (m1_subset_1(k2_funct_1(A_696), k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(A_696), k2_relat_1(k2_funct_1(A_696))))) | ~v1_funct_1(k2_funct_1(A_696)) | ~v1_relat_1(k2_funct_1(A_696)) | ~v2_funct_1(A_696) | ~v1_funct_1(A_696) | ~v1_relat_1(A_696))), inference(superposition, [status(thm), theory('equality')], [c_72, c_1732])).
% 18.26/9.34  tff(c_14953, plain, (m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', k2_relat_1(k2_funct_1('#skF_4'))))) | ~v1_funct_1(k2_funct_1('#skF_4')) | ~v1_relat_1(k2_funct_1('#skF_4')) | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1642, c_14886])).
% 18.26/9.34  tff(c_14997, plain, (m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', k1_relat_1('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_905, c_124, c_118, c_12807, c_620, c_12806, c_14953])).
% 18.26/9.34  tff(c_30, plain, (![B_16, A_15]: (r1_tarski(k1_relat_1(B_16), A_15) | ~v4_relat_1(B_16, A_15) | ~v1_relat_1(B_16))), inference(cnfTransformation, [status(thm)], [f_62])).
% 18.26/9.34  tff(c_3167, plain, (![B_318, D_319, A_320, C_321]: (k1_xboole_0=B_318 | m1_subset_1(D_319, k1_zfmisc_1(k2_zfmisc_1(A_320, C_321))) | ~r1_tarski(B_318, C_321) | ~m1_subset_1(D_319, k1_zfmisc_1(k2_zfmisc_1(A_320, B_318))) | ~v1_funct_2(D_319, A_320, B_318) | ~v1_funct_1(D_319))), inference(cnfTransformation, [status(thm)], [f_233])).
% 18.26/9.34  tff(c_16321, plain, (![B_726, D_727, A_728, A_729]: (k1_relat_1(B_726)=k1_xboole_0 | m1_subset_1(D_727, k1_zfmisc_1(k2_zfmisc_1(A_728, A_729))) | ~m1_subset_1(D_727, k1_zfmisc_1(k2_zfmisc_1(A_728, k1_relat_1(B_726)))) | ~v1_funct_2(D_727, A_728, k1_relat_1(B_726)) | ~v1_funct_1(D_727) | ~v4_relat_1(B_726, A_729) | ~v1_relat_1(B_726))), inference(resolution, [status(thm)], [c_30, c_3167])).
% 18.26/9.34  tff(c_16327, plain, (![A_729]: (k1_relat_1('#skF_4')=k1_xboole_0 | m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', A_729))) | ~v1_funct_2(k2_funct_1('#skF_4'), '#skF_3', k1_relat_1('#skF_4')) | ~v1_funct_1(k2_funct_1('#skF_4')) | ~v4_relat_1('#skF_4', A_729) | ~v1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_14997, c_16321])).
% 18.26/9.34  tff(c_16376, plain, (![A_729]: (k1_relat_1('#skF_4')=k1_xboole_0 | m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', A_729))) | ~v4_relat_1('#skF_4', A_729))), inference(demodulation, [status(thm), theory('equality')], [c_905, c_620, c_14095, c_16327])).
% 18.26/9.34  tff(c_16404, plain, (![A_730]: (m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', A_730))) | ~v4_relat_1('#skF_4', A_730))), inference(negUnitSimplification, [status(thm)], [c_919, c_16376])).
% 18.26/9.34  tff(c_619, plain, (~v1_funct_2(k2_funct_1('#skF_4'), '#skF_3', '#skF_2') | ~m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(splitRight, [status(thm)], [c_114])).
% 18.26/9.34  tff(c_686, plain, (~m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(splitLeft, [status(thm)], [c_619])).
% 18.26/9.34  tff(c_16451, plain, (~v4_relat_1('#skF_4', '#skF_2')), inference(resolution, [status(thm)], [c_16404, c_686])).
% 18.26/9.34  tff(c_16505, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1216, c_16451])).
% 18.26/9.34  tff(c_16506, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_917])).
% 18.26/9.34  tff(c_145, plain, (![A_65]: (k6_relat_1(A_65)=k6_partfun1(A_65))), inference(cnfTransformation, [status(thm)], [f_204])).
% 18.26/9.34  tff(c_50, plain, (k6_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_93])).
% 18.26/9.34  tff(c_151, plain, (k6_partfun1(k1_xboole_0)=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_145, c_50])).
% 18.26/9.34  tff(c_94, plain, (![A_55]: (k6_relat_1(A_55)=k6_partfun1(A_55))), inference(cnfTransformation, [status(thm)], [f_204])).
% 18.26/9.34  tff(c_46, plain, (![A_21]: (k2_relat_1(k6_relat_1(A_21))=A_21)), inference(cnfTransformation, [status(thm)], [f_88])).
% 18.26/9.34  tff(c_217, plain, (![A_70]: (k2_relat_1(k6_partfun1(A_70))=A_70)), inference(demodulation, [status(thm), theory('equality')], [c_94, c_46])).
% 18.26/9.34  tff(c_226, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_151, c_217])).
% 18.26/9.34  tff(c_16519, plain, (k2_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_16506, c_16506, c_226])).
% 18.26/9.34  tff(c_36, plain, (![A_19]: (k2_relat_1(A_19)!=k1_xboole_0 | k1_xboole_0=A_19 | ~v1_relat_1(A_19))), inference(cnfTransformation, [status(thm)], [f_78])).
% 18.26/9.34  tff(c_916, plain, (k2_relat_1('#skF_4')!=k1_xboole_0 | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_905, c_36])).
% 18.26/9.34  tff(c_918, plain, (k2_relat_1('#skF_4')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_916])).
% 18.26/9.34  tff(c_16508, plain, (k2_relat_1('#skF_4')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_16506, c_918])).
% 18.26/9.34  tff(c_16583, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_16519, c_16508])).
% 18.26/9.34  tff(c_16584, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_916])).
% 18.26/9.34  tff(c_8, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 18.26/9.34  tff(c_16604, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_16584, c_8])).
% 18.26/9.34  tff(c_44, plain, (![A_21]: (k1_relat_1(k6_relat_1(A_21))=A_21)), inference(cnfTransformation, [status(thm)], [f_88])).
% 18.26/9.34  tff(c_133, plain, (![A_21]: (k1_relat_1(k6_partfun1(A_21))=A_21)), inference(demodulation, [status(thm), theory('equality')], [c_94, c_44])).
% 18.26/9.34  tff(c_60, plain, (![A_25]: (v1_relat_1(k6_relat_1(A_25)))), inference(cnfTransformation, [status(thm)], [f_109])).
% 18.26/9.34  tff(c_128, plain, (![A_25]: (v1_relat_1(k6_partfun1(A_25)))), inference(demodulation, [status(thm), theory('equality')], [c_94, c_60])).
% 18.26/9.34  tff(c_236, plain, (![A_75]: (k1_relat_1(A_75)!=k1_xboole_0 | k1_xboole_0=A_75 | ~v1_relat_1(A_75))), inference(cnfTransformation, [status(thm)], [f_78])).
% 18.26/9.34  tff(c_245, plain, (![A_25]: (k1_relat_1(k6_partfun1(A_25))!=k1_xboole_0 | k6_partfun1(A_25)=k1_xboole_0)), inference(resolution, [status(thm)], [c_128, c_236])).
% 18.26/9.34  tff(c_260, plain, (k6_partfun1(k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_133, c_245])).
% 18.26/9.34  tff(c_18, plain, (![A_8]: (k2_zfmisc_1(A_8, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_45])).
% 18.26/9.34  tff(c_663, plain, (![A_109]: (m1_subset_1(k6_partfun1(A_109), k1_zfmisc_1(k2_zfmisc_1(A_109, A_109))))), inference(cnfTransformation, [status(thm)], [f_202])).
% 18.26/9.34  tff(c_673, plain, (m1_subset_1(k6_partfun1(k1_xboole_0), k1_zfmisc_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_18, c_663])).
% 18.26/9.34  tff(c_679, plain, (m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_260, c_673])).
% 18.26/9.34  tff(c_16592, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_16584, c_16584, c_679])).
% 18.26/9.34  tff(c_17639, plain, (![C_821, B_822, A_823]: (~v1_xboole_0(C_821) | ~m1_subset_1(B_822, k1_zfmisc_1(C_821)) | ~r2_hidden(A_823, B_822))), inference(cnfTransformation, [status(thm)], [f_56])).
% 18.26/9.34  tff(c_17641, plain, (![A_823]: (~v1_xboole_0('#skF_4') | ~r2_hidden(A_823, '#skF_4'))), inference(resolution, [status(thm)], [c_16592, c_17639])).
% 18.26/9.34  tff(c_17651, plain, (![A_824]: (~r2_hidden(A_824, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_16604, c_17641])).
% 18.26/9.34  tff(c_17656, plain, (![B_2]: (r1_tarski('#skF_4', B_2))), inference(resolution, [status(thm)], [c_6, c_17651])).
% 18.26/9.34  tff(c_178, plain, (![A_67]: (k1_relat_1(k6_partfun1(A_67))=A_67)), inference(demodulation, [status(thm), theory('equality')], [c_94, c_44])).
% 18.26/9.34  tff(c_187, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_151, c_178])).
% 18.26/9.34  tff(c_16598, plain, (k1_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_16584, c_16584, c_187])).
% 18.26/9.34  tff(c_17513, plain, (![B_805, A_806]: (v4_relat_1(B_805, A_806) | ~r1_tarski(k1_relat_1(B_805), A_806) | ~v1_relat_1(B_805))), inference(cnfTransformation, [status(thm)], [f_62])).
% 18.26/9.34  tff(c_17516, plain, (![A_806]: (v4_relat_1('#skF_4', A_806) | ~r1_tarski('#skF_4', A_806) | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_16598, c_17513])).
% 18.26/9.34  tff(c_17525, plain, (![A_806]: (v4_relat_1('#skF_4', A_806) | ~r1_tarski('#skF_4', A_806))), inference(demodulation, [status(thm), theory('equality')], [c_905, c_17516])).
% 18.26/9.34  tff(c_17658, plain, (![A_806]: (v4_relat_1('#skF_4', A_806))), inference(demodulation, [status(thm), theory('equality')], [c_17656, c_17525])).
% 18.26/9.34  tff(c_252, plain, (![A_25]: (k1_xboole_0!=A_25 | k6_partfun1(A_25)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_133, c_245])).
% 18.26/9.34  tff(c_16594, plain, (![A_25]: (A_25!='#skF_4' | k6_partfun1(A_25)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_16584, c_16584, c_252])).
% 18.26/9.34  tff(c_17818, plain, (![B_846, A_847]: (r1_tarski(k1_relat_1(B_846), A_847) | ~v4_relat_1(B_846, A_847) | ~v1_relat_1(B_846))), inference(cnfTransformation, [status(thm)], [f_62])).
% 18.26/9.34  tff(c_17841, plain, (![A_21, A_847]: (r1_tarski(A_21, A_847) | ~v4_relat_1(k6_partfun1(A_21), A_847) | ~v1_relat_1(k6_partfun1(A_21)))), inference(superposition, [status(thm), theory('equality')], [c_133, c_17818])).
% 18.26/9.34  tff(c_17851, plain, (![A_848, A_849]: (r1_tarski(A_848, A_849) | ~v4_relat_1(k6_partfun1(A_848), A_849))), inference(demodulation, [status(thm), theory('equality')], [c_128, c_17841])).
% 18.26/9.34  tff(c_17868, plain, (![A_25, A_849]: (r1_tarski(A_25, A_849) | ~v4_relat_1('#skF_4', A_849) | A_25!='#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_16594, c_17851])).
% 18.26/9.34  tff(c_17880, plain, (![A_850, A_851]: (r1_tarski(A_850, A_851) | A_850!='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_17658, c_17868])).
% 18.26/9.34  tff(c_24, plain, (![A_10, B_11]: (m1_subset_1(A_10, k1_zfmisc_1(B_11)) | ~r1_tarski(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_49])).
% 18.26/9.34  tff(c_722, plain, (~r1_tarski(k2_funct_1('#skF_4'), k2_zfmisc_1('#skF_3', '#skF_2'))), inference(resolution, [status(thm)], [c_24, c_686])).
% 18.26/9.34  tff(c_17907, plain, (k2_funct_1('#skF_4')!='#skF_4'), inference(resolution, [status(thm)], [c_17880, c_722])).
% 18.26/9.34  tff(c_58, plain, (![A_24]: (v1_funct_1(k6_relat_1(A_24)))), inference(cnfTransformation, [status(thm)], [f_105])).
% 18.26/9.34  tff(c_129, plain, (![A_24]: (v1_funct_1(k6_partfun1(A_24)))), inference(demodulation, [status(thm), theory('equality')], [c_94, c_58])).
% 18.26/9.34  tff(c_62, plain, (![A_25]: (v2_funct_1(k6_relat_1(A_25)))), inference(cnfTransformation, [status(thm)], [f_109])).
% 18.26/9.34  tff(c_127, plain, (![A_25]: (v2_funct_1(k6_partfun1(A_25)))), inference(demodulation, [status(thm), theory('equality')], [c_94, c_62])).
% 18.26/9.34  tff(c_132, plain, (![A_21]: (k2_relat_1(k6_partfun1(A_21))=A_21)), inference(demodulation, [status(thm), theory('equality')], [c_94, c_46])).
% 18.26/9.34  tff(c_48, plain, (![A_22]: (k5_relat_1(A_22, k6_relat_1(k2_relat_1(A_22)))=A_22 | ~v1_relat_1(A_22))), inference(cnfTransformation, [status(thm)], [f_92])).
% 18.26/9.34  tff(c_738, plain, (![A_115]: (k5_relat_1(A_115, k6_partfun1(k2_relat_1(A_115)))=A_115 | ~v1_relat_1(A_115))), inference(demodulation, [status(thm), theory('equality')], [c_94, c_48])).
% 18.26/9.34  tff(c_753, plain, (![A_21]: (k5_relat_1(k6_partfun1(A_21), k6_partfun1(A_21))=k6_partfun1(A_21) | ~v1_relat_1(k6_partfun1(A_21)))), inference(superposition, [status(thm), theory('equality')], [c_132, c_738])).
% 18.26/9.34  tff(c_759, plain, (![A_21]: (k5_relat_1(k6_partfun1(A_21), k6_partfun1(A_21))=k6_partfun1(A_21))), inference(demodulation, [status(thm), theory('equality')], [c_128, c_753])).
% 18.26/9.34  tff(c_74, plain, (![A_35, B_37]: (k2_funct_1(A_35)=B_37 | k6_relat_1(k1_relat_1(A_35))!=k5_relat_1(A_35, B_37) | k2_relat_1(A_35)!=k1_relat_1(B_37) | ~v2_funct_1(A_35) | ~v1_funct_1(B_37) | ~v1_relat_1(B_37) | ~v1_funct_1(A_35) | ~v1_relat_1(A_35))), inference(cnfTransformation, [status(thm)], [f_168])).
% 18.26/9.34  tff(c_19707, plain, (![A_1009, B_1010]: (k2_funct_1(A_1009)=B_1010 | k6_partfun1(k1_relat_1(A_1009))!=k5_relat_1(A_1009, B_1010) | k2_relat_1(A_1009)!=k1_relat_1(B_1010) | ~v2_funct_1(A_1009) | ~v1_funct_1(B_1010) | ~v1_relat_1(B_1010) | ~v1_funct_1(A_1009) | ~v1_relat_1(A_1009))), inference(demodulation, [status(thm), theory('equality')], [c_94, c_74])).
% 18.26/9.34  tff(c_19718, plain, (![A_21]: (k2_funct_1(k6_partfun1(A_21))=k6_partfun1(A_21) | k6_partfun1(k1_relat_1(k6_partfun1(A_21)))!=k6_partfun1(A_21) | k2_relat_1(k6_partfun1(A_21))!=k1_relat_1(k6_partfun1(A_21)) | ~v2_funct_1(k6_partfun1(A_21)) | ~v1_funct_1(k6_partfun1(A_21)) | ~v1_relat_1(k6_partfun1(A_21)) | ~v1_funct_1(k6_partfun1(A_21)) | ~v1_relat_1(k6_partfun1(A_21)))), inference(superposition, [status(thm), theory('equality')], [c_759, c_19707])).
% 18.26/9.34  tff(c_19734, plain, (![A_1011]: (k2_funct_1(k6_partfun1(A_1011))=k6_partfun1(A_1011))), inference(demodulation, [status(thm), theory('equality')], [c_128, c_129, c_128, c_129, c_127, c_133, c_132, c_133, c_19718])).
% 18.26/9.34  tff(c_19772, plain, (![A_1012]: (k6_partfun1(A_1012)=k2_funct_1('#skF_4') | A_1012!='#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_16594, c_19734])).
% 18.26/9.34  tff(c_19855, plain, (![A_1012]: (A_1012!='#skF_4' | k2_funct_1('#skF_4')='#skF_4' | A_1012!='#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_19772, c_16594])).
% 18.26/9.34  tff(c_19899, plain, (![A_1012]: (A_1012!='#skF_4' | A_1012!='#skF_4')), inference(negUnitSimplification, [status(thm)], [c_17907, c_19855])).
% 18.26/9.34  tff(c_19908, plain, $false, inference(reflexivity, [status(thm), theory('equality')], [c_19899])).
% 18.26/9.34  tff(c_19910, plain, (m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(splitRight, [status(thm)], [c_619])).
% 18.26/9.34  tff(c_20207, plain, (v1_relat_1(k2_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_19910, c_20189])).
% 18.26/9.34  tff(c_21371, plain, (k10_relat_1('#skF_4', '#skF_3')=k1_relat_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_21360, c_34])).
% 18.26/9.34  tff(c_21382, plain, (k10_relat_1('#skF_4', '#skF_3')=k1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_20211, c_21371])).
% 18.26/9.34  tff(c_21439, plain, (![B_1161, A_1162]: (k9_relat_1(B_1161, k10_relat_1(B_1161, A_1162))=A_1162 | ~r1_tarski(A_1162, k2_relat_1(B_1161)) | ~v1_funct_1(B_1161) | ~v1_relat_1(B_1161))), inference(cnfTransformation, [status(thm)], [f_117])).
% 18.26/9.34  tff(c_21441, plain, (![A_1162]: (k9_relat_1('#skF_4', k10_relat_1('#skF_4', A_1162))=A_1162 | ~r1_tarski(A_1162, '#skF_3') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_21360, c_21439])).
% 18.26/9.34  tff(c_21503, plain, (![A_1163]: (k9_relat_1('#skF_4', k10_relat_1('#skF_4', A_1163))=A_1163 | ~r1_tarski(A_1163, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_20211, c_124, c_21441])).
% 18.26/9.34  tff(c_21512, plain, (k9_relat_1('#skF_4', k1_relat_1('#skF_4'))='#skF_3' | ~r1_tarski('#skF_3', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_21382, c_21503])).
% 18.26/9.34  tff(c_21520, plain, (k9_relat_1('#skF_4', k1_relat_1('#skF_4'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_14, c_21512])).
% 18.26/9.34  tff(c_22209, plain, (![A_1209, B_1210]: (k9_relat_1(k2_funct_1(A_1209), k9_relat_1(A_1209, B_1210))=B_1210 | ~r1_tarski(B_1210, k1_relat_1(A_1209)) | ~v2_funct_1(A_1209) | ~v1_funct_1(A_1209) | ~v1_relat_1(A_1209))), inference(cnfTransformation, [status(thm)], [f_128])).
% 18.26/9.34  tff(c_22224, plain, (k9_relat_1(k2_funct_1('#skF_4'), '#skF_3')=k1_relat_1('#skF_4') | ~r1_tarski(k1_relat_1('#skF_4'), k1_relat_1('#skF_4')) | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_21520, c_22209])).
% 18.26/9.34  tff(c_22240, plain, (k9_relat_1(k2_funct_1('#skF_4'), '#skF_3')=k1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_20211, c_124, c_118, c_14, c_22224])).
% 18.26/9.34  tff(c_20941, plain, (![A_1112]: (k1_relat_1(k2_funct_1(A_1112))=k2_relat_1(A_1112) | ~v2_funct_1(A_1112) | ~v1_funct_1(A_1112) | ~v1_relat_1(A_1112))), inference(cnfTransformation, [status(thm)], [f_151])).
% 18.26/9.34  tff(c_30900, plain, (![A_1511]: (k9_relat_1(k2_funct_1(A_1511), k2_relat_1(A_1511))=k2_relat_1(k2_funct_1(A_1511)) | ~v1_relat_1(k2_funct_1(A_1511)) | ~v2_funct_1(A_1511) | ~v1_funct_1(A_1511) | ~v1_relat_1(A_1511))), inference(superposition, [status(thm), theory('equality')], [c_20941, c_32])).
% 18.26/9.34  tff(c_30930, plain, (k9_relat_1(k2_funct_1('#skF_4'), '#skF_3')=k2_relat_1(k2_funct_1('#skF_4')) | ~v1_relat_1(k2_funct_1('#skF_4')) | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_21360, c_30900])).
% 18.26/9.34  tff(c_30947, plain, (k2_relat_1(k2_funct_1('#skF_4'))=k1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_20211, c_124, c_118, c_20207, c_22240, c_30930])).
% 18.26/9.34  tff(c_31015, plain, (v1_funct_2(k2_funct_1('#skF_4'), k1_relat_1(k2_funct_1('#skF_4')), k1_relat_1('#skF_4')) | ~v1_funct_1(k2_funct_1('#skF_4')) | ~v1_relat_1(k2_funct_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_30947, c_98])).
% 18.26/9.34  tff(c_31067, plain, (v1_funct_2(k2_funct_1('#skF_4'), k1_relat_1(k2_funct_1('#skF_4')), k1_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_20207, c_620, c_31015])).
% 18.26/9.34  tff(c_32171, plain, (v1_funct_2(k2_funct_1('#skF_4'), k2_relat_1('#skF_4'), k1_relat_1('#skF_4')) | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_72, c_31067])).
% 18.26/9.34  tff(c_32173, plain, (v1_funct_2(k2_funct_1('#skF_4'), '#skF_3', k1_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_20211, c_124, c_118, c_21360, c_32171])).
% 18.26/9.34  tff(c_21250, plain, (![A_1146]: (m1_subset_1(A_1146, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_1146), k2_relat_1(A_1146)))) | ~v1_funct_1(A_1146) | ~v1_relat_1(A_1146))), inference(cnfTransformation, [status(thm)], [f_214])).
% 18.26/9.34  tff(c_34330, plain, (![A_1583]: (m1_subset_1(k2_funct_1(A_1583), k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(A_1583), k2_relat_1(k2_funct_1(A_1583))))) | ~v1_funct_1(k2_funct_1(A_1583)) | ~v1_relat_1(k2_funct_1(A_1583)) | ~v2_funct_1(A_1583) | ~v1_funct_1(A_1583) | ~v1_relat_1(A_1583))), inference(superposition, [status(thm), theory('equality')], [c_72, c_21250])).
% 18.26/9.34  tff(c_34394, plain, (m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', k2_relat_1(k2_funct_1('#skF_4'))))) | ~v1_funct_1(k2_funct_1('#skF_4')) | ~v1_relat_1(k2_funct_1('#skF_4')) | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_21360, c_34330])).
% 18.26/9.34  tff(c_34436, plain, (m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', k1_relat_1('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_20211, c_124, c_118, c_20207, c_620, c_30947, c_34394])).
% 18.26/9.34  tff(c_22453, plain, (![B_1219, D_1220, A_1221, C_1222]: (k1_xboole_0=B_1219 | v1_funct_2(D_1220, A_1221, C_1222) | ~r1_tarski(B_1219, C_1222) | ~m1_subset_1(D_1220, k1_zfmisc_1(k2_zfmisc_1(A_1221, B_1219))) | ~v1_funct_2(D_1220, A_1221, B_1219) | ~v1_funct_1(D_1220))), inference(cnfTransformation, [status(thm)], [f_233])).
% 18.26/9.34  tff(c_35312, plain, (![B_1600, D_1601, A_1602, A_1603]: (k1_relat_1(B_1600)=k1_xboole_0 | v1_funct_2(D_1601, A_1602, A_1603) | ~m1_subset_1(D_1601, k1_zfmisc_1(k2_zfmisc_1(A_1602, k1_relat_1(B_1600)))) | ~v1_funct_2(D_1601, A_1602, k1_relat_1(B_1600)) | ~v1_funct_1(D_1601) | ~v4_relat_1(B_1600, A_1603) | ~v1_relat_1(B_1600))), inference(resolution, [status(thm)], [c_30, c_22453])).
% 18.26/9.34  tff(c_35316, plain, (![A_1603]: (k1_relat_1('#skF_4')=k1_xboole_0 | v1_funct_2(k2_funct_1('#skF_4'), '#skF_3', A_1603) | ~v1_funct_2(k2_funct_1('#skF_4'), '#skF_3', k1_relat_1('#skF_4')) | ~v1_funct_1(k2_funct_1('#skF_4')) | ~v4_relat_1('#skF_4', A_1603) | ~v1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_34436, c_35312])).
% 18.26/9.34  tff(c_35364, plain, (![A_1603]: (k1_relat_1('#skF_4')=k1_xboole_0 | v1_funct_2(k2_funct_1('#skF_4'), '#skF_3', A_1603) | ~v4_relat_1('#skF_4', A_1603))), inference(demodulation, [status(thm), theory('equality')], [c_20211, c_620, c_32173, c_35316])).
% 18.26/9.34  tff(c_35395, plain, (![A_1604]: (v1_funct_2(k2_funct_1('#skF_4'), '#skF_3', A_1604) | ~v4_relat_1('#skF_4', A_1604))), inference(negUnitSimplification, [status(thm)], [c_20245, c_35364])).
% 18.26/9.34  tff(c_19909, plain, (~v1_funct_2(k2_funct_1('#skF_4'), '#skF_3', '#skF_2')), inference(splitRight, [status(thm)], [c_619])).
% 18.26/9.34  tff(c_35398, plain, (~v4_relat_1('#skF_4', '#skF_2')), inference(resolution, [status(thm)], [c_35395, c_19909])).
% 18.26/9.34  tff(c_35402, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_20716, c_35398])).
% 18.26/9.34  tff(c_35403, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_20227])).
% 18.26/9.34  tff(c_35404, plain, (k1_relat_1('#skF_4')=k1_xboole_0), inference(splitRight, [status(thm)], [c_20227])).
% 18.26/9.34  tff(c_35435, plain, (k1_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_35403, c_35404])).
% 18.26/9.34  tff(c_42, plain, (![A_20]: (k2_relat_1(A_20)=k1_xboole_0 | k1_relat_1(A_20)!=k1_xboole_0 | ~v1_relat_1(A_20))), inference(cnfTransformation, [status(thm)], [f_84])).
% 18.26/9.34  tff(c_20225, plain, (k2_relat_1('#skF_4')=k1_xboole_0 | k1_relat_1('#skF_4')!=k1_xboole_0), inference(resolution, [status(thm)], [c_20211, c_42])).
% 18.26/9.34  tff(c_35433, plain, (k2_relat_1('#skF_4')='#skF_4' | k1_relat_1('#skF_4')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_35403, c_35403, c_20225])).
% 18.26/9.34  tff(c_35434, plain, (k1_relat_1('#skF_4')!='#skF_4'), inference(splitLeft, [status(thm)], [c_35433])).
% 18.26/9.34  tff(c_35471, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_35435, c_35434])).
% 18.26/9.34  tff(c_35472, plain, (k2_relat_1('#skF_4')='#skF_4'), inference(splitRight, [status(thm)], [c_35433])).
% 18.26/9.34  tff(c_20226, plain, (k2_relat_1('#skF_4')!=k1_xboole_0 | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_20211, c_36])).
% 18.26/9.34  tff(c_20244, plain, (k2_relat_1('#skF_4')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_20226])).
% 18.26/9.34  tff(c_35518, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_35472, c_35403, c_20244])).
% 18.26/9.34  tff(c_35519, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_20226])).
% 18.26/9.34  tff(c_35534, plain, (![A_8]: (k2_zfmisc_1(A_8, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_35519, c_35519, c_18])).
% 18.26/9.34  tff(c_35520, plain, (k2_relat_1('#skF_4')=k1_xboole_0), inference(splitRight, [status(thm)], [c_20226])).
% 18.26/9.34  tff(c_35582, plain, (k2_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_35519, c_35520])).
% 18.26/9.34  tff(c_36410, plain, (![A_1673, B_1674, C_1675]: (k2_relset_1(A_1673, B_1674, C_1675)=k2_relat_1(C_1675) | ~m1_subset_1(C_1675, k1_zfmisc_1(k2_zfmisc_1(A_1673, B_1674))))), inference(cnfTransformation, [status(thm)], [f_182])).
% 18.26/9.34  tff(c_36429, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_120, c_36410])).
% 18.26/9.34  tff(c_36436, plain, ('#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_116, c_35582, c_36429])).
% 18.26/9.34  tff(c_35541, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_35519, c_8])).
% 18.26/9.34  tff(c_35529, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_35519, c_35519, c_679])).
% 18.26/9.34  tff(c_26, plain, (![C_14, B_13, A_12]: (~v1_xboole_0(C_14) | ~m1_subset_1(B_13, k1_zfmisc_1(C_14)) | ~r2_hidden(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_56])).
% 18.26/9.34  tff(c_35667, plain, (![A_12]: (~v1_xboole_0('#skF_4') | ~r2_hidden(A_12, '#skF_4'))), inference(resolution, [status(thm)], [c_35529, c_26])).
% 18.26/9.34  tff(c_35678, plain, (![A_1615]: (~r2_hidden(A_1615, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_35541, c_35667])).
% 18.26/9.34  tff(c_35683, plain, (![B_2]: (r1_tarski('#skF_4', B_2))), inference(resolution, [status(thm)], [c_6, c_35678])).
% 18.26/9.34  tff(c_35535, plain, (k1_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_35519, c_35519, c_187])).
% 18.26/9.34  tff(c_35922, plain, (![B_1635, A_1636]: (v4_relat_1(B_1635, A_1636) | ~r1_tarski(k1_relat_1(B_1635), A_1636) | ~v1_relat_1(B_1635))), inference(cnfTransformation, [status(thm)], [f_62])).
% 18.26/9.34  tff(c_35928, plain, (![A_1636]: (v4_relat_1('#skF_4', A_1636) | ~r1_tarski('#skF_4', A_1636) | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_35535, c_35922])).
% 18.26/9.34  tff(c_35938, plain, (![A_1636]: (v4_relat_1('#skF_4', A_1636))), inference(demodulation, [status(thm), theory('equality')], [c_20211, c_35683, c_35928])).
% 18.26/9.34  tff(c_35531, plain, (![A_25]: (A_25!='#skF_4' | k6_partfun1(A_25)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_35519, c_35519, c_252])).
% 18.26/9.34  tff(c_35761, plain, (![B_1622, A_1623]: (r1_tarski(k1_relat_1(B_1622), A_1623) | ~v4_relat_1(B_1622, A_1623) | ~v1_relat_1(B_1622))), inference(cnfTransformation, [status(thm)], [f_62])).
% 18.26/9.34  tff(c_35769, plain, (![A_21, A_1623]: (r1_tarski(A_21, A_1623) | ~v4_relat_1(k6_partfun1(A_21), A_1623) | ~v1_relat_1(k6_partfun1(A_21)))), inference(superposition, [status(thm), theory('equality')], [c_133, c_35761])).
% 18.26/9.34  tff(c_36250, plain, (![A_1656, A_1657]: (r1_tarski(A_1656, A_1657) | ~v4_relat_1(k6_partfun1(A_1656), A_1657))), inference(demodulation, [status(thm), theory('equality')], [c_128, c_35769])).
% 18.26/9.34  tff(c_36260, plain, (![A_25, A_1657]: (r1_tarski(A_25, A_1657) | ~v4_relat_1('#skF_4', A_1657) | A_25!='#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_35531, c_36250])).
% 18.26/9.34  tff(c_36272, plain, (![A_1658, A_1659]: (r1_tarski(A_1658, A_1659) | A_1658!='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_35938, c_36260])).
% 18.26/9.34  tff(c_654, plain, (![A_107, B_108]: (r1_tarski(A_107, B_108) | ~m1_subset_1(A_107, k1_zfmisc_1(B_108)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 18.26/9.34  tff(c_662, plain, (r1_tarski('#skF_4', k2_zfmisc_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_120, c_654])).
% 18.26/9.34  tff(c_20077, plain, (![B_1024, A_1025]: (B_1024=A_1025 | ~r1_tarski(B_1024, A_1025) | ~r1_tarski(A_1025, B_1024))), inference(cnfTransformation, [status(thm)], [f_39])).
% 18.26/9.34  tff(c_20091, plain, (k2_zfmisc_1('#skF_2', '#skF_3')='#skF_4' | ~r1_tarski(k2_zfmisc_1('#skF_2', '#skF_3'), '#skF_4')), inference(resolution, [status(thm)], [c_662, c_20077])).
% 18.26/9.34  tff(c_20142, plain, (~r1_tarski(k2_zfmisc_1('#skF_2', '#skF_3'), '#skF_4')), inference(splitLeft, [status(thm)], [c_20091])).
% 18.26/9.34  tff(c_36298, plain, (k2_zfmisc_1('#skF_2', '#skF_3')!='#skF_4'), inference(resolution, [status(thm)], [c_36272, c_20142])).
% 18.26/9.34  tff(c_36437, plain, (k2_zfmisc_1('#skF_2', '#skF_4')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_36436, c_36298])).
% 18.26/9.34  tff(c_36448, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_35534, c_36437])).
% 18.26/9.34  tff(c_36449, plain, (k2_zfmisc_1('#skF_2', '#skF_3')='#skF_4'), inference(splitRight, [status(thm)], [c_20091])).
% 18.26/9.34  tff(c_36452, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_36449, c_120])).
% 18.26/9.34  tff(c_36792, plain, (![C_1706, A_1707, B_1708]: (v4_relat_1(C_1706, A_1707) | ~m1_subset_1(C_1706, k1_zfmisc_1(k2_zfmisc_1(A_1707, B_1708))))), inference(cnfTransformation, [status(thm)], [f_178])).
% 18.26/9.34  tff(c_36837, plain, (![C_1711]: (v4_relat_1(C_1711, '#skF_2') | ~m1_subset_1(C_1711, k1_zfmisc_1('#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_36449, c_36792])).
% 18.26/9.34  tff(c_36845, plain, (v4_relat_1('#skF_4', '#skF_2')), inference(resolution, [status(thm)], [c_36452, c_36837])).
% 18.26/9.34  tff(c_16, plain, (![B_9, A_8]: (k1_xboole_0=B_9 | k1_xboole_0=A_8 | k2_zfmisc_1(A_8, B_9)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_45])).
% 18.26/9.34  tff(c_36457, plain, (k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2' | k1_xboole_0!='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_36449, c_16])).
% 18.26/9.34  tff(c_36506, plain, (k1_xboole_0!='#skF_4'), inference(splitLeft, [status(thm)], [c_36457])).
% 18.26/9.34  tff(c_36514, plain, (![C_1680, A_1681, B_1682]: (v1_relat_1(C_1680) | ~m1_subset_1(C_1680, k1_zfmisc_1(k2_zfmisc_1(A_1681, B_1682))))), inference(cnfTransformation, [status(thm)], [f_172])).
% 18.26/9.34  tff(c_36562, plain, (![C_1684]: (v1_relat_1(C_1684) | ~m1_subset_1(C_1684, k1_zfmisc_1('#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_36449, c_36514])).
% 18.26/9.34  tff(c_36570, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_36452, c_36562])).
% 18.26/9.34  tff(c_36583, plain, (k1_relat_1('#skF_4')!=k1_xboole_0 | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_36570, c_38])).
% 18.26/9.34  tff(c_36591, plain, (k1_relat_1('#skF_4')!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_36506, c_36583])).
% 18.26/9.34  tff(c_37608, plain, (![A_1773, B_1774, C_1775]: (k2_relset_1(A_1773, B_1774, C_1775)=k2_relat_1(C_1775) | ~m1_subset_1(C_1775, k1_zfmisc_1(k2_zfmisc_1(A_1773, B_1774))))), inference(cnfTransformation, [status(thm)], [f_182])).
% 18.26/9.34  tff(c_37789, plain, (![C_1789]: (k2_relset_1('#skF_2', '#skF_3', C_1789)=k2_relat_1(C_1789) | ~m1_subset_1(C_1789, k1_zfmisc_1('#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_36449, c_37608])).
% 18.26/9.34  tff(c_37792, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_36452, c_37789])).
% 18.26/9.34  tff(c_37798, plain, (k2_relat_1('#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_116, c_37792])).
% 18.26/9.34  tff(c_36531, plain, (v1_relat_1(k2_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_19910, c_36514])).
% 18.26/9.34  tff(c_37810, plain, (k10_relat_1('#skF_4', '#skF_3')=k1_relat_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_37798, c_34])).
% 18.26/9.34  tff(c_37821, plain, (k10_relat_1('#skF_4', '#skF_3')=k1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_36570, c_37810])).
% 18.26/9.34  tff(c_37836, plain, (![B_1790, A_1791]: (k9_relat_1(B_1790, k10_relat_1(B_1790, A_1791))=A_1791 | ~r1_tarski(A_1791, k2_relat_1(B_1790)) | ~v1_funct_1(B_1790) | ~v1_relat_1(B_1790))), inference(cnfTransformation, [status(thm)], [f_117])).
% 18.26/9.34  tff(c_37838, plain, (![A_1791]: (k9_relat_1('#skF_4', k10_relat_1('#skF_4', A_1791))=A_1791 | ~r1_tarski(A_1791, '#skF_3') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_37798, c_37836])).
% 18.26/9.34  tff(c_40849, plain, (![A_1940]: (k9_relat_1('#skF_4', k10_relat_1('#skF_4', A_1940))=A_1940 | ~r1_tarski(A_1940, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_36570, c_124, c_37838])).
% 18.26/9.34  tff(c_40861, plain, (k9_relat_1('#skF_4', k1_relat_1('#skF_4'))='#skF_3' | ~r1_tarski('#skF_3', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_37821, c_40849])).
% 18.26/9.34  tff(c_40871, plain, (k9_relat_1('#skF_4', k1_relat_1('#skF_4'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_14, c_40861])).
% 18.26/9.34  tff(c_66, plain, (![A_28, B_30]: (k9_relat_1(k2_funct_1(A_28), k9_relat_1(A_28, B_30))=B_30 | ~r1_tarski(B_30, k1_relat_1(A_28)) | ~v2_funct_1(A_28) | ~v1_funct_1(A_28) | ~v1_relat_1(A_28))), inference(cnfTransformation, [status(thm)], [f_128])).
% 18.26/9.34  tff(c_40877, plain, (k9_relat_1(k2_funct_1('#skF_4'), '#skF_3')=k1_relat_1('#skF_4') | ~r1_tarski(k1_relat_1('#skF_4'), k1_relat_1('#skF_4')) | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_40871, c_66])).
% 18.26/9.34  tff(c_40890, plain, (k9_relat_1(k2_funct_1('#skF_4'), '#skF_3')=k1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_36570, c_124, c_118, c_14, c_40877])).
% 18.26/9.34  tff(c_37482, plain, (![A_1766]: (k1_relat_1(k2_funct_1(A_1766))=k2_relat_1(A_1766) | ~v2_funct_1(A_1766) | ~v1_funct_1(A_1766) | ~v1_relat_1(A_1766))), inference(cnfTransformation, [status(thm)], [f_151])).
% 18.26/9.34  tff(c_46976, plain, (![A_2177]: (k9_relat_1(k2_funct_1(A_2177), k2_relat_1(A_2177))=k2_relat_1(k2_funct_1(A_2177)) | ~v1_relat_1(k2_funct_1(A_2177)) | ~v2_funct_1(A_2177) | ~v1_funct_1(A_2177) | ~v1_relat_1(A_2177))), inference(superposition, [status(thm), theory('equality')], [c_37482, c_32])).
% 18.26/9.34  tff(c_47006, plain, (k9_relat_1(k2_funct_1('#skF_4'), '#skF_3')=k2_relat_1(k2_funct_1('#skF_4')) | ~v1_relat_1(k2_funct_1('#skF_4')) | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_37798, c_46976])).
% 18.26/9.34  tff(c_47023, plain, (k2_relat_1(k2_funct_1('#skF_4'))=k1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_36570, c_124, c_118, c_36531, c_40890, c_47006])).
% 18.26/9.34  tff(c_47129, plain, (v1_funct_2(k2_funct_1('#skF_4'), k1_relat_1(k2_funct_1('#skF_4')), k1_relat_1('#skF_4')) | ~v1_funct_1(k2_funct_1('#skF_4')) | ~v1_relat_1(k2_funct_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_47023, c_98])).
% 18.26/9.34  tff(c_47186, plain, (v1_funct_2(k2_funct_1('#skF_4'), k1_relat_1(k2_funct_1('#skF_4')), k1_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_36531, c_620, c_47129])).
% 18.26/9.34  tff(c_47348, plain, (v1_funct_2(k2_funct_1('#skF_4'), k2_relat_1('#skF_4'), k1_relat_1('#skF_4')) | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_72, c_47186])).
% 18.26/9.34  tff(c_47350, plain, (v1_funct_2(k2_funct_1('#skF_4'), '#skF_3', k1_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_36570, c_124, c_118, c_37798, c_47348])).
% 18.26/9.34  tff(c_36816, plain, (v4_relat_1(k2_funct_1('#skF_4'), '#skF_3')), inference(resolution, [status(thm)], [c_19910, c_36792])).
% 18.26/9.34  tff(c_37734, plain, (![A_1786]: (m1_subset_1(A_1786, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_1786), k2_relat_1(A_1786)))) | ~v1_funct_1(A_1786) | ~v1_relat_1(A_1786))), inference(cnfTransformation, [status(thm)], [f_214])).
% 18.26/9.34  tff(c_22, plain, (![A_10, B_11]: (r1_tarski(A_10, B_11) | ~m1_subset_1(A_10, k1_zfmisc_1(B_11)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 18.26/9.34  tff(c_37775, plain, (![A_1786]: (r1_tarski(A_1786, k2_zfmisc_1(k1_relat_1(A_1786), k2_relat_1(A_1786))) | ~v1_funct_1(A_1786) | ~v1_relat_1(A_1786))), inference(resolution, [status(thm)], [c_37734, c_22])).
% 18.26/9.34  tff(c_47115, plain, (r1_tarski(k2_funct_1('#skF_4'), k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_4')), k1_relat_1('#skF_4'))) | ~v1_funct_1(k2_funct_1('#skF_4')) | ~v1_relat_1(k2_funct_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_47023, c_37775])).
% 18.26/9.34  tff(c_47175, plain, (r1_tarski(k2_funct_1('#skF_4'), k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_4')), k1_relat_1('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_36531, c_620, c_47115])).
% 18.26/9.34  tff(c_36818, plain, (![A_10, A_1707, B_1708]: (v4_relat_1(A_10, A_1707) | ~r1_tarski(A_10, k2_zfmisc_1(A_1707, B_1708)))), inference(resolution, [status(thm)], [c_24, c_36792])).
% 18.26/9.34  tff(c_47562, plain, (v4_relat_1(k2_funct_1('#skF_4'), k1_relat_1(k2_funct_1('#skF_4')))), inference(resolution, [status(thm)], [c_47175, c_36818])).
% 18.26/9.34  tff(c_47581, plain, (![A_2181, A_2182]: (r1_tarski(k2_relat_1(A_2181), A_2182) | ~v4_relat_1(k2_funct_1(A_2181), A_2182) | ~v1_relat_1(k2_funct_1(A_2181)) | ~v2_funct_1(A_2181) | ~v1_funct_1(A_2181) | ~v1_relat_1(A_2181))), inference(superposition, [status(thm), theory('equality')], [c_37482, c_30])).
% 18.26/9.34  tff(c_47584, plain, (r1_tarski(k2_relat_1('#skF_4'), k1_relat_1(k2_funct_1('#skF_4'))) | ~v1_relat_1(k2_funct_1('#skF_4')) | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_47562, c_47581])).
% 18.26/9.34  tff(c_47627, plain, (r1_tarski('#skF_3', k1_relat_1(k2_funct_1('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_36570, c_124, c_118, c_36531, c_37798, c_47584])).
% 18.26/9.34  tff(c_36667, plain, (![B_1695, A_1696]: (r1_tarski(k1_relat_1(B_1695), A_1696) | ~v4_relat_1(B_1695, A_1696) | ~v1_relat_1(B_1695))), inference(cnfTransformation, [status(thm)], [f_62])).
% 18.26/9.34  tff(c_10, plain, (![B_7, A_6]: (B_7=A_6 | ~r1_tarski(B_7, A_6) | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_39])).
% 18.26/9.34  tff(c_36691, plain, (![B_1695, A_1696]: (k1_relat_1(B_1695)=A_1696 | ~r1_tarski(A_1696, k1_relat_1(B_1695)) | ~v4_relat_1(B_1695, A_1696) | ~v1_relat_1(B_1695))), inference(resolution, [status(thm)], [c_36667, c_10])).
% 18.26/9.34  tff(c_47651, plain, (k1_relat_1(k2_funct_1('#skF_4'))='#skF_3' | ~v4_relat_1(k2_funct_1('#skF_4'), '#skF_3') | ~v1_relat_1(k2_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_47627, c_36691])).
% 18.26/9.34  tff(c_47685, plain, (k1_relat_1(k2_funct_1('#skF_4'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_36531, c_36816, c_47651])).
% 18.26/9.34  tff(c_96, plain, (![A_56]: (m1_subset_1(A_56, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_56), k2_relat_1(A_56)))) | ~v1_funct_1(A_56) | ~v1_relat_1(A_56))), inference(cnfTransformation, [status(thm)], [f_214])).
% 18.26/9.34  tff(c_47767, plain, (m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', k2_relat_1(k2_funct_1('#skF_4'))))) | ~v1_funct_1(k2_funct_1('#skF_4')) | ~v1_relat_1(k2_funct_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_47685, c_96])).
% 18.26/9.35  tff(c_47840, plain, (m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', k1_relat_1('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_36531, c_620, c_47023, c_47767])).
% 18.26/9.35  tff(c_38733, plain, (![B_1861, D_1862, A_1863, C_1864]: (k1_xboole_0=B_1861 | v1_funct_2(D_1862, A_1863, C_1864) | ~r1_tarski(B_1861, C_1864) | ~m1_subset_1(D_1862, k1_zfmisc_1(k2_zfmisc_1(A_1863, B_1861))) | ~v1_funct_2(D_1862, A_1863, B_1861) | ~v1_funct_1(D_1862))), inference(cnfTransformation, [status(thm)], [f_233])).
% 18.26/9.35  tff(c_50862, plain, (![B_2264, D_2265, A_2266, A_2267]: (k1_relat_1(B_2264)=k1_xboole_0 | v1_funct_2(D_2265, A_2266, A_2267) | ~m1_subset_1(D_2265, k1_zfmisc_1(k2_zfmisc_1(A_2266, k1_relat_1(B_2264)))) | ~v1_funct_2(D_2265, A_2266, k1_relat_1(B_2264)) | ~v1_funct_1(D_2265) | ~v4_relat_1(B_2264, A_2267) | ~v1_relat_1(B_2264))), inference(resolution, [status(thm)], [c_30, c_38733])).
% 18.26/9.35  tff(c_50872, plain, (![A_2267]: (k1_relat_1('#skF_4')=k1_xboole_0 | v1_funct_2(k2_funct_1('#skF_4'), '#skF_3', A_2267) | ~v1_funct_2(k2_funct_1('#skF_4'), '#skF_3', k1_relat_1('#skF_4')) | ~v1_funct_1(k2_funct_1('#skF_4')) | ~v4_relat_1('#skF_4', A_2267) | ~v1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_47840, c_50862])).
% 18.26/9.35  tff(c_50919, plain, (![A_2267]: (k1_relat_1('#skF_4')=k1_xboole_0 | v1_funct_2(k2_funct_1('#skF_4'), '#skF_3', A_2267) | ~v4_relat_1('#skF_4', A_2267))), inference(demodulation, [status(thm), theory('equality')], [c_36570, c_620, c_47350, c_50872])).
% 18.26/9.35  tff(c_50944, plain, (![A_2268]: (v1_funct_2(k2_funct_1('#skF_4'), '#skF_3', A_2268) | ~v4_relat_1('#skF_4', A_2268))), inference(negUnitSimplification, [status(thm)], [c_36591, c_50919])).
% 18.26/9.35  tff(c_50947, plain, (~v4_relat_1('#skF_4', '#skF_2')), inference(resolution, [status(thm)], [c_50944, c_19909])).
% 18.26/9.35  tff(c_50951, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_36845, c_50947])).
% 18.26/9.35  tff(c_50953, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_36457])).
% 18.26/9.35  tff(c_622, plain, (![A_105]: (k1_xboole_0!=A_105 | k6_partfun1(A_105)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_133, c_245])).
% 18.26/9.35  tff(c_90, plain, (![A_54]: (v1_partfun1(k6_partfun1(A_54), A_54))), inference(cnfTransformation, [status(thm)], [f_202])).
% 18.26/9.35  tff(c_631, plain, (![A_105]: (v1_partfun1(k1_xboole_0, A_105) | k1_xboole_0!=A_105)), inference(superposition, [status(thm), theory('equality')], [c_622, c_90])).
% 18.26/9.35  tff(c_51157, plain, (v1_partfun1('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_50953, c_50953, c_631])).
% 18.26/9.35  tff(c_50964, plain, (![A_25]: (A_25!='#skF_4' | k6_partfun1(A_25)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_50953, c_50953, c_252])).
% 18.26/9.35  tff(c_50967, plain, (![A_8]: (k2_zfmisc_1(A_8, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_50953, c_50953, c_18])).
% 18.26/9.35  tff(c_51899, plain, (![C_2325, A_2326, B_2327]: (v4_relat_1(C_2325, A_2326) | ~m1_subset_1(C_2325, k1_zfmisc_1(k2_zfmisc_1(A_2326, B_2327))))), inference(cnfTransformation, [status(thm)], [f_178])).
% 18.26/9.35  tff(c_52261, plain, (![C_2368, A_2369]: (v4_relat_1(C_2368, A_2369) | ~m1_subset_1(C_2368, k1_zfmisc_1('#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_50967, c_51899])).
% 18.26/9.35  tff(c_52323, plain, (![A_2374, A_2375]: (v4_relat_1(A_2374, A_2375) | ~r1_tarski(A_2374, '#skF_4'))), inference(resolution, [status(thm)], [c_24, c_52261])).
% 18.26/9.35  tff(c_51970, plain, (![B_2332, A_2333]: (r1_tarski(k1_relat_1(B_2332), A_2333) | ~v4_relat_1(B_2332, A_2333) | ~v1_relat_1(B_2332))), inference(cnfTransformation, [status(thm)], [f_62])).
% 18.26/9.35  tff(c_51978, plain, (![A_21, A_2333]: (r1_tarski(A_21, A_2333) | ~v4_relat_1(k6_partfun1(A_21), A_2333) | ~v1_relat_1(k6_partfun1(A_21)))), inference(superposition, [status(thm), theory('equality')], [c_133, c_51970])).
% 18.26/9.35  tff(c_51983, plain, (![A_21, A_2333]: (r1_tarski(A_21, A_2333) | ~v4_relat_1(k6_partfun1(A_21), A_2333))), inference(demodulation, [status(thm), theory('equality')], [c_128, c_51978])).
% 18.26/9.35  tff(c_52394, plain, (![A_2383, A_2384]: (r1_tarski(A_2383, A_2384) | ~r1_tarski(k6_partfun1(A_2383), '#skF_4'))), inference(resolution, [status(thm)], [c_52323, c_51983])).
% 18.26/9.35  tff(c_52396, plain, (![A_25, A_2384]: (r1_tarski(A_25, A_2384) | ~r1_tarski('#skF_4', '#skF_4') | A_25!='#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_50964, c_52394])).
% 18.26/9.35  tff(c_52399, plain, (![A_2384]: (r1_tarski('#skF_4', A_2384))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_52396])).
% 18.26/9.35  tff(c_50966, plain, (k2_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_50953, c_50953, c_226])).
% 18.26/9.35  tff(c_669, plain, (![A_25]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(k2_zfmisc_1(A_25, A_25))) | k1_xboole_0!=A_25)), inference(superposition, [status(thm), theory('equality')], [c_252, c_663])).
% 18.26/9.35  tff(c_53185, plain, (![A_2473]: (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(A_2473, A_2473))) | A_2473!='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_50953, c_50953, c_669])).
% 18.26/9.35  tff(c_84, plain, (![D_50, C_49, B_48, A_47]: (m1_subset_1(D_50, k1_zfmisc_1(k2_zfmisc_1(C_49, B_48))) | ~r1_tarski(k2_relat_1(D_50), B_48) | ~m1_subset_1(D_50, k1_zfmisc_1(k2_zfmisc_1(C_49, A_47))))), inference(cnfTransformation, [status(thm)], [f_188])).
% 18.26/9.35  tff(c_53187, plain, (![A_2473, B_48]: (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(A_2473, B_48))) | ~r1_tarski(k2_relat_1('#skF_4'), B_48) | A_2473!='#skF_4')), inference(resolution, [status(thm)], [c_53185, c_84])).
% 18.26/9.35  tff(c_53757, plain, (![A_2508, B_2509]: (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(A_2508, B_2509))) | A_2508!='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_52399, c_50966, c_53187])).
% 18.26/9.35  tff(c_86, plain, (![C_53, A_51, B_52]: (v1_funct_2(C_53, A_51, B_52) | ~v1_partfun1(C_53, A_51) | ~v1_funct_1(C_53) | ~m1_subset_1(C_53, k1_zfmisc_1(k2_zfmisc_1(A_51, B_52))))), inference(cnfTransformation, [status(thm)], [f_198])).
% 18.26/9.35  tff(c_53762, plain, (![A_2508, B_2509]: (v1_funct_2('#skF_4', A_2508, B_2509) | ~v1_partfun1('#skF_4', A_2508) | ~v1_funct_1('#skF_4') | A_2508!='#skF_4')), inference(resolution, [status(thm)], [c_53757, c_86])).
% 18.26/9.35  tff(c_54034, plain, (![A_2529, B_2530]: (v1_funct_2('#skF_4', A_2529, B_2530) | ~v1_partfun1('#skF_4', A_2529) | A_2529!='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_124, c_53762])).
% 18.26/9.35  tff(c_20, plain, (![B_9]: (k2_zfmisc_1(k1_xboole_0, B_9)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_45])).
% 18.26/9.35  tff(c_50969, plain, (![B_9]: (k2_zfmisc_1('#skF_4', B_9)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_50953, c_50953, c_20])).
% 18.26/9.35  tff(c_50952, plain, (k1_xboole_0='#skF_2' | k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_36457])).
% 18.26/9.35  tff(c_51653, plain, ('#skF_2'='#skF_4' | '#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_50953, c_50953, c_50952])).
% 18.26/9.35  tff(c_51654, plain, ('#skF_3'='#skF_4'), inference(splitLeft, [status(thm)], [c_51653])).
% 18.26/9.35  tff(c_50974, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_50953, c_8])).
% 18.26/9.35  tff(c_51624, plain, (![C_2312, B_2313, A_2314]: (~v1_xboole_0(C_2312) | ~m1_subset_1(B_2313, k1_zfmisc_1(C_2312)) | ~r2_hidden(A_2314, B_2313))), inference(cnfTransformation, [status(thm)], [f_56])).
% 18.26/9.35  tff(c_51628, plain, (![A_2314]: (~v1_xboole_0('#skF_4') | ~r2_hidden(A_2314, '#skF_4'))), inference(resolution, [status(thm)], [c_36452, c_51624])).
% 18.26/9.35  tff(c_51641, plain, (![A_2315]: (~r2_hidden(A_2315, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_50974, c_51628])).
% 18.26/9.35  tff(c_51646, plain, (![B_2]: (r1_tarski('#skF_4', B_2))), inference(resolution, [status(thm)], [c_6, c_51641])).
% 18.26/9.35  tff(c_51344, plain, (![C_2290, B_2291, A_2292]: (~v1_xboole_0(C_2290) | ~m1_subset_1(B_2291, k1_zfmisc_1(C_2290)) | ~r2_hidden(A_2292, B_2291))), inference(cnfTransformation, [status(thm)], [f_56])).
% 18.26/9.35  tff(c_51348, plain, (![A_2292]: (~v1_xboole_0('#skF_4') | ~r2_hidden(A_2292, '#skF_4'))), inference(resolution, [status(thm)], [c_36452, c_51344])).
% 18.26/9.35  tff(c_51361, plain, (![A_2293]: (~r2_hidden(A_2293, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_50974, c_51348])).
% 18.26/9.35  tff(c_51366, plain, (![B_2]: (r1_tarski('#skF_4', B_2))), inference(resolution, [status(thm)], [c_6, c_51361])).
% 18.26/9.35  tff(c_51085, plain, ('#skF_2'='#skF_4' | '#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_50953, c_50953, c_50952])).
% 18.26/9.35  tff(c_51086, plain, ('#skF_3'='#skF_4'), inference(splitLeft, [status(thm)], [c_51085])).
% 18.26/9.35  tff(c_19929, plain, (r1_tarski(k2_funct_1('#skF_4'), k2_zfmisc_1('#skF_3', '#skF_2'))), inference(resolution, [status(thm)], [c_19910, c_22])).
% 18.26/9.35  tff(c_20089, plain, (k2_zfmisc_1('#skF_3', '#skF_2')=k2_funct_1('#skF_4') | ~r1_tarski(k2_zfmisc_1('#skF_3', '#skF_2'), k2_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_19929, c_20077])).
% 18.26/9.35  tff(c_50982, plain, (~r1_tarski(k2_zfmisc_1('#skF_3', '#skF_2'), k2_funct_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_20089])).
% 18.26/9.35  tff(c_51245, plain, (~r1_tarski('#skF_4', k2_funct_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_50969, c_51086, c_50982])).
% 18.26/9.35  tff(c_51370, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_51366, c_51245])).
% 18.26/9.35  tff(c_51371, plain, ('#skF_2'='#skF_4'), inference(splitRight, [status(thm)], [c_51085])).
% 18.26/9.35  tff(c_51522, plain, (~r1_tarski('#skF_4', k2_funct_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_50967, c_51371, c_50982])).
% 18.26/9.35  tff(c_51650, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_51646, c_51522])).
% 18.26/9.35  tff(c_51651, plain, (k2_zfmisc_1('#skF_3', '#skF_2')=k2_funct_1('#skF_4')), inference(splitRight, [status(thm)], [c_20089])).
% 18.26/9.35  tff(c_51827, plain, (k2_funct_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_50969, c_51654, c_51651])).
% 18.26/9.35  tff(c_51658, plain, (~v1_funct_2(k2_funct_1('#skF_4'), '#skF_4', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_51654, c_19909])).
% 18.26/9.35  tff(c_51897, plain, (~v1_funct_2('#skF_4', '#skF_4', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_51827, c_51658])).
% 18.26/9.35  tff(c_54037, plain, (~v1_partfun1('#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_54034, c_51897])).
% 18.26/9.35  tff(c_54041, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_51157, c_54037])).
% 18.26/9.35  tff(c_54043, plain, ('#skF_3'!='#skF_4'), inference(splitRight, [status(thm)], [c_51653])).
% 18.26/9.35  tff(c_54322, plain, (![C_2544, B_2545, A_2546]: (~v1_xboole_0(C_2544) | ~m1_subset_1(B_2545, k1_zfmisc_1(C_2544)) | ~r2_hidden(A_2546, B_2545))), inference(cnfTransformation, [status(thm)], [f_56])).
% 18.26/9.35  tff(c_54324, plain, (![A_2546]: (~v1_xboole_0('#skF_4') | ~r2_hidden(A_2546, '#skF_4'))), inference(resolution, [status(thm)], [c_36452, c_54322])).
% 18.26/9.35  tff(c_54334, plain, (![A_2547]: (~r2_hidden(A_2547, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_50974, c_54324])).
% 18.26/9.35  tff(c_54339, plain, (![B_2]: (r1_tarski('#skF_4', B_2))), inference(resolution, [status(thm)], [c_6, c_54334])).
% 18.26/9.35  tff(c_162, plain, (v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_151, c_128])).
% 18.26/9.35  tff(c_50972, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_50953, c_162])).
% 18.26/9.35  tff(c_50968, plain, (k1_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_50953, c_50953, c_187])).
% 18.26/9.35  tff(c_54235, plain, (![B_2539, A_2540]: (v4_relat_1(B_2539, A_2540) | ~r1_tarski(k1_relat_1(B_2539), A_2540) | ~v1_relat_1(B_2539))), inference(cnfTransformation, [status(thm)], [f_62])).
% 18.26/9.35  tff(c_54238, plain, (![A_2540]: (v4_relat_1('#skF_4', A_2540) | ~r1_tarski('#skF_4', A_2540) | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_50968, c_54235])).
% 18.26/9.35  tff(c_54247, plain, (![A_2540]: (v4_relat_1('#skF_4', A_2540) | ~r1_tarski('#skF_4', A_2540))), inference(demodulation, [status(thm), theory('equality')], [c_50972, c_54238])).
% 18.26/9.35  tff(c_54430, plain, (![A_2540]: (v4_relat_1('#skF_4', A_2540))), inference(demodulation, [status(thm), theory('equality')], [c_54339, c_54247])).
% 18.26/9.35  tff(c_54406, plain, (![B_2553, A_2554]: (r1_tarski(k1_relat_1(B_2553), A_2554) | ~v4_relat_1(B_2553, A_2554) | ~v1_relat_1(B_2553))), inference(cnfTransformation, [status(thm)], [f_62])).
% 18.26/9.35  tff(c_54421, plain, (![A_21, A_2554]: (r1_tarski(A_21, A_2554) | ~v4_relat_1(k6_partfun1(A_21), A_2554) | ~v1_relat_1(k6_partfun1(A_21)))), inference(superposition, [status(thm), theory('equality')], [c_133, c_54406])).
% 18.26/9.35  tff(c_54490, plain, (![A_2561, A_2562]: (r1_tarski(A_2561, A_2562) | ~v4_relat_1(k6_partfun1(A_2561), A_2562))), inference(demodulation, [status(thm), theory('equality')], [c_128, c_54421])).
% 18.26/9.35  tff(c_54503, plain, (![A_25, A_2562]: (r1_tarski(A_25, A_2562) | ~v4_relat_1('#skF_4', A_2562) | A_25!='#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_50964, c_54490])).
% 18.26/9.35  tff(c_54532, plain, (![A_2562]: (r1_tarski('#skF_4', A_2562))), inference(demodulation, [status(thm), theory('equality')], [c_54430, c_54503])).
% 18.26/9.35  tff(c_55319, plain, (![A_25]: (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(A_25, A_25))) | A_25!='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_50953, c_50953, c_669])).
% 18.26/9.35  tff(c_55611, plain, (![D_2688, C_2689, B_2690, A_2691]: (m1_subset_1(D_2688, k1_zfmisc_1(k2_zfmisc_1(C_2689, B_2690))) | ~r1_tarski(k2_relat_1(D_2688), B_2690) | ~m1_subset_1(D_2688, k1_zfmisc_1(k2_zfmisc_1(C_2689, A_2691))))), inference(cnfTransformation, [status(thm)], [f_188])).
% 18.26/9.35  tff(c_55613, plain, (![A_25, B_2690]: (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(A_25, B_2690))) | ~r1_tarski(k2_relat_1('#skF_4'), B_2690) | A_25!='#skF_4')), inference(resolution, [status(thm)], [c_55319, c_55611])).
% 18.26/9.35  tff(c_55694, plain, (![A_2699, B_2700]: (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(A_2699, B_2700))) | A_2699!='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_54532, c_50966, c_55613])).
% 18.26/9.35  tff(c_82, plain, (![A_44, B_45, C_46]: (k2_relset_1(A_44, B_45, C_46)=k2_relat_1(C_46) | ~m1_subset_1(C_46, k1_zfmisc_1(k2_zfmisc_1(A_44, B_45))))), inference(cnfTransformation, [status(thm)], [f_182])).
% 18.26/9.35  tff(c_55702, plain, (![A_2699, B_2700]: (k2_relset_1(A_2699, B_2700, '#skF_4')=k2_relat_1('#skF_4') | A_2699!='#skF_4')), inference(resolution, [status(thm)], [c_55694, c_82])).
% 18.26/9.35  tff(c_55743, plain, (![B_2700]: (k2_relset_1('#skF_4', B_2700, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_50966, c_55702])).
% 18.26/9.35  tff(c_54042, plain, ('#skF_2'='#skF_4'), inference(splitRight, [status(thm)], [c_51653])).
% 18.26/9.35  tff(c_54048, plain, (k2_relset_1('#skF_4', '#skF_3', '#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_54042, c_116])).
% 18.26/9.35  tff(c_55744, plain, ('#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_55743, c_54048])).
% 18.26/9.35  tff(c_55746, plain, $false, inference(negUnitSimplification, [status(thm)], [c_54043, c_55744])).
% 18.26/9.35  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 18.26/9.35  
% 18.26/9.35  Inference rules
% 18.26/9.35  ----------------------
% 18.26/9.35  #Ref     : 38
% 18.26/9.35  #Sup     : 12931
% 18.26/9.35  #Fact    : 0
% 18.26/9.35  #Define  : 0
% 18.26/9.35  #Split   : 93
% 18.26/9.35  #Chain   : 0
% 18.26/9.35  #Close   : 0
% 18.26/9.35  
% 18.26/9.35  Ordering : KBO
% 18.26/9.35  
% 18.26/9.35  Simplification rules
% 18.26/9.35  ----------------------
% 18.26/9.35  #Subsume      : 4975
% 18.26/9.35  #Demod        : 10628
% 18.26/9.35  #Tautology    : 3897
% 18.26/9.35  #SimpNegUnit  : 369
% 18.26/9.35  #BackRed      : 372
% 18.26/9.35  
% 18.26/9.35  #Partial instantiations: 0
% 18.26/9.35  #Strategies tried      : 1
% 18.26/9.35  
% 18.26/9.35  Timing (in seconds)
% 18.26/9.35  ----------------------
% 18.26/9.35  Preprocessing        : 0.42
% 18.26/9.35  Parsing              : 0.23
% 18.26/9.35  CNF conversion       : 0.03
% 18.26/9.35  Main loop            : 8.03
% 18.26/9.35  Inferencing          : 1.88
% 18.26/9.35  Reduction            : 3.24
% 18.26/9.35  Demodulation         : 2.41
% 18.26/9.35  BG Simplification    : 0.14
% 18.26/9.35  Subsumption          : 2.27
% 18.26/9.35  Abstraction          : 0.20
% 18.26/9.35  MUC search           : 0.00
% 18.26/9.35  Cooper               : 0.00
% 18.26/9.35  Total                : 8.58
% 18.26/9.35  Index Insertion      : 0.00
% 18.26/9.35  Index Deletion       : 0.00
% 18.26/9.35  Index Matching       : 0.00
% 18.26/9.35  BG Taut test         : 0.00
%------------------------------------------------------------------------------
