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
% DateTime   : Thu Dec  3 10:13:16 EST 2020

% Result     : Theorem 20.27s
% Output     : CNFRefutation 20.49s
% Verified   : 
% Statistics : Number of formulae       :  257 (2060 expanded)
%              Number of leaves         :   58 ( 752 expanded)
%              Depth                    :   19
%              Number of atoms          :  595 (7848 expanded)
%              Number of equality atoms :  186 (2218 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > v1_partfun1 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k8_relset_1 > k2_relset_1 > k9_relat_1 > k5_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k6_relat_1 > k6_partfun1 > k4_relat_1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(k8_relset_1,type,(
    k8_relset_1: ( $i * $i * $i * $i ) > $i )).

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k4_relat_1,type,(
    k4_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_298,negated_conjecture,(
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

tff(f_48,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_42,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_102,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => k2_funct_1(A) = k4_relat_1(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_funct_1)).

tff(f_46,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => v1_relat_1(k4_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_relat_1)).

tff(f_256,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( ( v2_funct_1(C)
          & k2_relset_1(A,B,C) = B )
       => ( v1_funct_1(k2_funct_1(C))
          & v1_funct_2(k2_funct_1(C),B,A)
          & m1_subset_1(k2_funct_1(C),k1_zfmisc_1(k2_zfmisc_1(B,A))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_funct_2)).

tff(f_52,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k4_relat_1(k4_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k4_relat_1)).

tff(f_157,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_197,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_114,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v2_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_funct_1)).

tff(f_195,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_185,axiom,(
    ! [A] :
      ( v1_partfun1(k6_partfun1(A),A)
      & m1_subset_1(k6_partfun1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).

tff(f_169,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_181,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( v1_funct_1(k1_partfun1(A,B,C,D,E,F))
        & m1_subset_1(k1_partfun1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).

tff(f_240,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_funct_2)).

tff(f_214,axiom,(
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

tff(f_60,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k10_relat_1(A,k2_relat_1(A)) = k1_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_relat_1)).

tff(f_161,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k8_relset_1(A,B,C,D) = k10_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

tff(f_153,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k8_relset_1(A,B,C,D),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k8_relset_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_66,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( k2_relat_1(A) = k1_relat_1(k4_relat_1(A))
        & k1_relat_1(A) = k2_relat_1(k4_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_relat_1)).

tff(f_84,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_272,axiom,(
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

tff(f_73,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => r1_tarski(k2_relat_1(k5_relat_1(A,B)),k2_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_relat_1)).

tff(f_86,axiom,(
    ! [A] : k4_relat_1(k6_relat_1(A)) = k6_relat_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_relat_1)).

tff(f_80,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k4_relat_1(k5_relat_1(A,B)) = k5_relat_1(k4_relat_1(B),k4_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t54_relat_1)).

tff(f_149,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_funct_1)).

tff(c_102,plain,(
    k2_funct_1('#skF_3') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_298])).

tff(c_16,plain,(
    ! [A_9,B_10] : v1_relat_1(k2_zfmisc_1(A_9,B_10)) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_120,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_298])).

tff(c_299,plain,(
    ! [B_106,A_107] :
      ( v1_relat_1(B_106)
      | ~ m1_subset_1(B_106,k1_zfmisc_1(A_107))
      | ~ v1_relat_1(A_107) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_308,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_120,c_299])).

tff(c_318,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_308])).

tff(c_124,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_298])).

tff(c_108,plain,(
    v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_298])).

tff(c_426,plain,(
    ! [A_116] :
      ( k4_relat_1(A_116) = k2_funct_1(A_116)
      | ~ v2_funct_1(A_116)
      | ~ v1_funct_1(A_116)
      | ~ v1_relat_1(A_116) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_432,plain,
    ( k4_relat_1('#skF_3') = k2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_108,c_426])).

tff(c_438,plain,(
    k4_relat_1('#skF_3') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_318,c_124,c_432])).

tff(c_14,plain,(
    ! [A_8] :
      ( v1_relat_1(k4_relat_1(A_8))
      | ~ v1_relat_1(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_451,plain,
    ( v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_438,c_14])).

tff(c_461,plain,(
    v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_318,c_451])).

tff(c_122,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_298])).

tff(c_112,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_298])).

tff(c_5166,plain,(
    ! [C_369,A_370,B_371] :
      ( v1_funct_1(k2_funct_1(C_369))
      | k2_relset_1(A_370,B_371,C_369) != B_371
      | ~ v2_funct_1(C_369)
      | ~ m1_subset_1(C_369,k1_zfmisc_1(k2_zfmisc_1(A_370,B_371)))
      | ~ v1_funct_2(C_369,A_370,B_371)
      | ~ v1_funct_1(C_369) ) ),
    inference(cnfTransformation,[status(thm)],[f_256])).

tff(c_5180,plain,
    ( v1_funct_1(k2_funct_1('#skF_3'))
    | k2_relset_1('#skF_1','#skF_2','#skF_3') != '#skF_2'
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_120,c_5166])).

tff(c_5191,plain,(
    v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_124,c_122,c_108,c_112,c_5180])).

tff(c_18,plain,(
    ! [A_11] :
      ( k4_relat_1(k4_relat_1(A_11)) = A_11
      | ~ v1_relat_1(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_448,plain,
    ( k4_relat_1(k2_funct_1('#skF_3')) = '#skF_3'
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_438,c_18])).

tff(c_459,plain,(
    k4_relat_1(k2_funct_1('#skF_3')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_318,c_448])).

tff(c_92,plain,(
    ! [C_76,B_75,A_74] :
      ( m1_subset_1(k2_funct_1(C_76),k1_zfmisc_1(k2_zfmisc_1(B_75,A_74)))
      | k2_relset_1(A_74,B_75,C_76) != B_75
      | ~ v2_funct_1(C_76)
      | ~ m1_subset_1(C_76,k1_zfmisc_1(k2_zfmisc_1(A_74,B_75)))
      | ~ v1_funct_2(C_76,A_74,B_75)
      | ~ v1_funct_1(C_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_256])).

tff(c_114,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_298])).

tff(c_311,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_1')) ),
    inference(resolution,[status(thm)],[c_114,c_299])).

tff(c_321,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_311])).

tff(c_118,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_298])).

tff(c_116,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_298])).

tff(c_741,plain,(
    ! [A_134,B_135,C_136] :
      ( k2_relset_1(A_134,B_135,C_136) = k2_relat_1(C_136)
      | ~ m1_subset_1(C_136,k1_zfmisc_1(k2_zfmisc_1(A_134,B_135))) ) ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_760,plain,(
    k2_relset_1('#skF_2','#skF_1','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_114,c_741])).

tff(c_5183,plain,
    ( v1_funct_1(k2_funct_1('#skF_4'))
    | k2_relset_1('#skF_2','#skF_1','#skF_4') != '#skF_1'
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_114,c_5166])).

tff(c_5194,plain,
    ( v1_funct_1(k2_funct_1('#skF_4'))
    | k2_relat_1('#skF_4') != '#skF_1'
    | ~ v2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_118,c_116,c_760,c_5183])).

tff(c_5200,plain,(
    ~ v2_funct_1('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_5194])).

tff(c_106,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_298])).

tff(c_80,plain,(
    ! [A_62] : k6_relat_1(A_62) = k6_partfun1(A_62) ),
    inference(cnfTransformation,[status(thm)],[f_197])).

tff(c_50,plain,(
    ! [A_27] : v2_funct_1(k6_relat_1(A_27)) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_126,plain,(
    ! [A_27] : v2_funct_1(k6_partfun1(A_27)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_50])).

tff(c_3164,plain,(
    ! [F_269,C_270,E_271,A_273,D_272,B_268] :
      ( k1_partfun1(A_273,B_268,C_270,D_272,E_271,F_269) = k5_relat_1(E_271,F_269)
      | ~ m1_subset_1(F_269,k1_zfmisc_1(k2_zfmisc_1(C_270,D_272)))
      | ~ v1_funct_1(F_269)
      | ~ m1_subset_1(E_271,k1_zfmisc_1(k2_zfmisc_1(A_273,B_268)))
      | ~ v1_funct_1(E_271) ) ),
    inference(cnfTransformation,[status(thm)],[f_195])).

tff(c_3184,plain,(
    ! [A_273,B_268,E_271] :
      ( k1_partfun1(A_273,B_268,'#skF_2','#skF_1',E_271,'#skF_4') = k5_relat_1(E_271,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_271,k1_zfmisc_1(k2_zfmisc_1(A_273,B_268)))
      | ~ v1_funct_1(E_271) ) ),
    inference(resolution,[status(thm)],[c_114,c_3164])).

tff(c_3462,plain,(
    ! [A_285,B_286,E_287] :
      ( k1_partfun1(A_285,B_286,'#skF_2','#skF_1',E_287,'#skF_4') = k5_relat_1(E_287,'#skF_4')
      | ~ m1_subset_1(E_287,k1_zfmisc_1(k2_zfmisc_1(A_285,B_286)))
      | ~ v1_funct_1(E_287) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_118,c_3184])).

tff(c_3487,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_120,c_3462])).

tff(c_3499,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_124,c_3487])).

tff(c_76,plain,(
    ! [A_55] : m1_subset_1(k6_partfun1(A_55),k1_zfmisc_1(k2_zfmisc_1(A_55,A_55))) ),
    inference(cnfTransformation,[status(thm)],[f_185])).

tff(c_110,plain,(
    r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k6_partfun1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_298])).

tff(c_1433,plain,(
    ! [D_164,C_165,A_166,B_167] :
      ( D_164 = C_165
      | ~ r2_relset_1(A_166,B_167,C_165,D_164)
      | ~ m1_subset_1(D_164,k1_zfmisc_1(k2_zfmisc_1(A_166,B_167)))
      | ~ m1_subset_1(C_165,k1_zfmisc_1(k2_zfmisc_1(A_166,B_167))) ) ),
    inference(cnfTransformation,[status(thm)],[f_169])).

tff(c_1443,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_110,c_1433])).

tff(c_1460,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_1443])).

tff(c_1497,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_1460])).

tff(c_3505,plain,(
    ~ m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3499,c_1497])).

tff(c_3771,plain,(
    ! [C_297,E_298,D_302,A_301,B_299,F_300] :
      ( m1_subset_1(k1_partfun1(A_301,B_299,C_297,D_302,E_298,F_300),k1_zfmisc_1(k2_zfmisc_1(A_301,D_302)))
      | ~ m1_subset_1(F_300,k1_zfmisc_1(k2_zfmisc_1(C_297,D_302)))
      | ~ v1_funct_1(F_300)
      | ~ m1_subset_1(E_298,k1_zfmisc_1(k2_zfmisc_1(A_301,B_299)))
      | ~ v1_funct_1(E_298) ) ),
    inference(cnfTransformation,[status(thm)],[f_181])).

tff(c_3816,plain,
    ( m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_3499,c_3771])).

tff(c_3843,plain,(
    m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_124,c_120,c_118,c_114,c_3816])).

tff(c_3845,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3505,c_3843])).

tff(c_3846,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_1460])).

tff(c_10909,plain,(
    ! [C_633,B_634,E_635,A_636,D_632] :
      ( k1_xboole_0 = C_633
      | v2_funct_1(E_635)
      | k2_relset_1(A_636,B_634,D_632) != B_634
      | ~ v2_funct_1(k1_partfun1(A_636,B_634,B_634,C_633,D_632,E_635))
      | ~ m1_subset_1(E_635,k1_zfmisc_1(k2_zfmisc_1(B_634,C_633)))
      | ~ v1_funct_2(E_635,B_634,C_633)
      | ~ v1_funct_1(E_635)
      | ~ m1_subset_1(D_632,k1_zfmisc_1(k2_zfmisc_1(A_636,B_634)))
      | ~ v1_funct_2(D_632,A_636,B_634)
      | ~ v1_funct_1(D_632) ) ),
    inference(cnfTransformation,[status(thm)],[f_240])).

tff(c_10913,plain,
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
    inference(superposition,[status(thm),theory(equality)],[c_3846,c_10909])).

tff(c_10918,plain,
    ( k1_xboole_0 = '#skF_1'
    | v2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_124,c_122,c_120,c_118,c_116,c_114,c_126,c_112,c_10913])).

tff(c_10920,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_5200,c_106,c_10918])).

tff(c_10922,plain,(
    v2_funct_1('#skF_4') ),
    inference(splitRight,[status(thm)],[c_5194])).

tff(c_42,plain,(
    ! [A_25] :
      ( k4_relat_1(A_25) = k2_funct_1(A_25)
      | ~ v2_funct_1(A_25)
      | ~ v1_funct_1(A_25)
      | ~ v1_relat_1(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_10925,plain,
    ( k4_relat_1('#skF_4') = k2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_10922,c_42])).

tff(c_10928,plain,(
    k4_relat_1('#skF_4') = k2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_321,c_118,c_10925])).

tff(c_10953,plain,
    ( v1_relat_1(k2_funct_1('#skF_4'))
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_10928,c_14])).

tff(c_10971,plain,(
    v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_321,c_10953])).

tff(c_10921,plain,
    ( k2_relat_1('#skF_4') != '#skF_1'
    | v1_funct_1(k2_funct_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_5194])).

tff(c_10973,plain,(
    k2_relat_1('#skF_4') != '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_10921])).

tff(c_705,plain,(
    ! [A_127,B_128,D_129] :
      ( r2_relset_1(A_127,B_128,D_129,D_129)
      | ~ m1_subset_1(D_129,k1_zfmisc_1(k2_zfmisc_1(A_127,B_128))) ) ),
    inference(cnfTransformation,[status(thm)],[f_169])).

tff(c_715,plain,(
    ! [A_55] : r2_relset_1(A_55,A_55,k6_partfun1(A_55),k6_partfun1(A_55)) ),
    inference(resolution,[status(thm)],[c_76,c_705])).

tff(c_12716,plain,(
    ! [A_722,B_723,C_724,D_725] :
      ( k2_relset_1(A_722,B_723,C_724) = B_723
      | ~ r2_relset_1(B_723,B_723,k1_partfun1(B_723,A_722,A_722,B_723,D_725,C_724),k6_partfun1(B_723))
      | ~ m1_subset_1(D_725,k1_zfmisc_1(k2_zfmisc_1(B_723,A_722)))
      | ~ v1_funct_2(D_725,B_723,A_722)
      | ~ v1_funct_1(D_725)
      | ~ m1_subset_1(C_724,k1_zfmisc_1(k2_zfmisc_1(A_722,B_723)))
      | ~ v1_funct_2(C_724,A_722,B_723)
      | ~ v1_funct_1(C_724) ) ),
    inference(cnfTransformation,[status(thm)],[f_214])).

tff(c_12722,plain,
    ( k2_relset_1('#skF_2','#skF_1','#skF_4') = '#skF_1'
    | ~ r2_relset_1('#skF_1','#skF_1',k6_partfun1('#skF_1'),k6_partfun1('#skF_1'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_3846,c_12716])).

tff(c_12726,plain,(
    k2_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_118,c_116,c_114,c_124,c_122,c_120,c_715,c_760,c_12722])).

tff(c_12728,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_10973,c_12726])).

tff(c_12729,plain,(
    v1_funct_1(k2_funct_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_10921])).

tff(c_22,plain,(
    ! [A_13] :
      ( k10_relat_1(A_13,k2_relat_1(A_13)) = k1_relat_1(A_13)
      | ~ v1_relat_1(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_1333,plain,(
    ! [A_156,B_157,C_158,D_159] :
      ( k8_relset_1(A_156,B_157,C_158,D_159) = k10_relat_1(C_158,D_159)
      | ~ m1_subset_1(C_158,k1_zfmisc_1(k2_zfmisc_1(A_156,B_157))) ) ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_1398,plain,(
    ! [D_163] : k8_relset_1('#skF_2','#skF_1','#skF_4',D_163) = k10_relat_1('#skF_4',D_163) ),
    inference(resolution,[status(thm)],[c_114,c_1333])).

tff(c_60,plain,(
    ! [A_34,B_35,C_36,D_37] :
      ( m1_subset_1(k8_relset_1(A_34,B_35,C_36,D_37),k1_zfmisc_1(A_34))
      | ~ m1_subset_1(C_36,k1_zfmisc_1(k2_zfmisc_1(A_34,B_35))) ) ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_1404,plain,(
    ! [D_163] :
      ( m1_subset_1(k10_relat_1('#skF_4',D_163),k1_zfmisc_1('#skF_2'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1398,c_60])).

tff(c_1461,plain,(
    ! [D_168] : m1_subset_1(k10_relat_1('#skF_4',D_168),k1_zfmisc_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_114,c_1404])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( r1_tarski(A_3,B_4)
      | ~ m1_subset_1(A_3,k1_zfmisc_1(B_4)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_1476,plain,(
    ! [D_169] : r1_tarski(k10_relat_1('#skF_4',D_169),'#skF_2') ),
    inference(resolution,[status(thm)],[c_1461,c_8])).

tff(c_1485,plain,
    ( r1_tarski(k1_relat_1('#skF_4'),'#skF_2')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_1476])).

tff(c_1489,plain,(
    r1_tarski(k1_relat_1('#skF_4'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_321,c_1485])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_1496,plain,
    ( k1_relat_1('#skF_4') = '#skF_2'
    | ~ r1_tarski('#skF_2',k1_relat_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_1489,c_2])).

tff(c_13105,plain,(
    ~ r1_tarski('#skF_2',k1_relat_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_1496])).

tff(c_24,plain,(
    ! [A_14] :
      ( k2_relat_1(k4_relat_1(A_14)) = k1_relat_1(A_14)
      | ~ v1_relat_1(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_10944,plain,
    ( k2_relat_1(k2_funct_1('#skF_4')) = k1_relat_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_10928,c_24])).

tff(c_10965,plain,(
    k2_relat_1(k2_funct_1('#skF_4')) = k1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_321,c_10944])).

tff(c_34,plain,(
    ! [A_21] : k2_relat_1(k6_relat_1(A_21)) = A_21 ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_131,plain,(
    ! [A_21] : k2_relat_1(k6_partfun1(A_21)) = A_21 ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_34])).

tff(c_12730,plain,(
    k2_relat_1('#skF_4') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_10921])).

tff(c_12731,plain,(
    k2_relset_1('#skF_2','#skF_1','#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12730,c_760])).

tff(c_13864,plain,(
    ! [A_774,C_775,B_776] :
      ( k6_partfun1(A_774) = k5_relat_1(C_775,k2_funct_1(C_775))
      | k1_xboole_0 = B_776
      | ~ v2_funct_1(C_775)
      | k2_relset_1(A_774,B_776,C_775) != B_776
      | ~ m1_subset_1(C_775,k1_zfmisc_1(k2_zfmisc_1(A_774,B_776)))
      | ~ v1_funct_2(C_775,A_774,B_776)
      | ~ v1_funct_1(C_775) ) ),
    inference(cnfTransformation,[status(thm)],[f_272])).

tff(c_13884,plain,
    ( k5_relat_1('#skF_4',k2_funct_1('#skF_4')) = k6_partfun1('#skF_2')
    | k1_xboole_0 = '#skF_1'
    | ~ v2_funct_1('#skF_4')
    | k2_relset_1('#skF_2','#skF_1','#skF_4') != '#skF_1'
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_114,c_13864])).

tff(c_13899,plain,
    ( k5_relat_1('#skF_4',k2_funct_1('#skF_4')) = k6_partfun1('#skF_2')
    | k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_118,c_116,c_12731,c_10922,c_13884])).

tff(c_13900,plain,(
    k5_relat_1('#skF_4',k2_funct_1('#skF_4')) = k6_partfun1('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_106,c_13899])).

tff(c_28,plain,(
    ! [A_15,B_17] :
      ( r1_tarski(k2_relat_1(k5_relat_1(A_15,B_17)),k2_relat_1(B_17))
      | ~ v1_relat_1(B_17)
      | ~ v1_relat_1(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_13920,plain,
    ( r1_tarski(k2_relat_1(k6_partfun1('#skF_2')),k2_relat_1(k2_funct_1('#skF_4')))
    | ~ v1_relat_1(k2_funct_1('#skF_4'))
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_13900,c_28])).

tff(c_13924,plain,(
    r1_tarski('#skF_2',k1_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_321,c_10971,c_10965,c_131,c_13920])).

tff(c_13926,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_13105,c_13924])).

tff(c_13927,plain,(
    k1_relat_1('#skF_4') = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_1496])).

tff(c_13931,plain,(
    k2_relat_1(k2_funct_1('#skF_4')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_13927,c_10965])).

tff(c_751,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_120,c_741])).

tff(c_759,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_112,c_751])).

tff(c_26,plain,(
    ! [A_14] :
      ( k1_relat_1(k4_relat_1(A_14)) = k2_relat_1(A_14)
      | ~ v1_relat_1(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_445,plain,
    ( k1_relat_1(k2_funct_1('#skF_3')) = k2_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_438,c_26])).

tff(c_457,plain,(
    k1_relat_1(k2_funct_1('#skF_3')) = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_318,c_445])).

tff(c_764,plain,(
    k1_relat_1(k2_funct_1('#skF_3')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_759,c_457])).

tff(c_774,plain,
    ( k10_relat_1('#skF_3','#skF_2') = k1_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_759,c_22])).

tff(c_782,plain,(
    k10_relat_1('#skF_3','#skF_2') = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_318,c_774])).

tff(c_1351,plain,(
    ! [D_160] : k8_relset_1('#skF_1','#skF_2','#skF_3',D_160) = k10_relat_1('#skF_3',D_160) ),
    inference(resolution,[status(thm)],[c_120,c_1333])).

tff(c_1357,plain,(
    ! [D_160] :
      ( m1_subset_1(k10_relat_1('#skF_3',D_160),k1_zfmisc_1('#skF_1'))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1351,c_60])).

tff(c_1365,plain,(
    ! [D_161] : m1_subset_1(k10_relat_1('#skF_3',D_161),k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_120,c_1357])).

tff(c_1382,plain,(
    ! [D_162] : r1_tarski(k10_relat_1('#skF_3',D_162),'#skF_1') ),
    inference(resolution,[status(thm)],[c_1365,c_8])).

tff(c_1389,plain,(
    r1_tarski(k1_relat_1('#skF_3'),'#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_782,c_1382])).

tff(c_1420,plain,
    ( k1_relat_1('#skF_3') = '#skF_1'
    | ~ r1_tarski('#skF_1',k1_relat_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_1389,c_2])).

tff(c_3863,plain,(
    ~ r1_tarski('#skF_1',k1_relat_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_1420])).

tff(c_104,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_298])).

tff(c_5010,plain,(
    ! [A_366,C_367,B_368] :
      ( k6_partfun1(A_366) = k5_relat_1(C_367,k2_funct_1(C_367))
      | k1_xboole_0 = B_368
      | ~ v2_funct_1(C_367)
      | k2_relset_1(A_366,B_368,C_367) != B_368
      | ~ m1_subset_1(C_367,k1_zfmisc_1(k2_zfmisc_1(A_366,B_368)))
      | ~ v1_funct_2(C_367,A_366,B_368)
      | ~ v1_funct_1(C_367) ) ),
    inference(cnfTransformation,[status(thm)],[f_272])).

tff(c_5028,plain,
    ( k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_partfun1('#skF_1')
    | k1_xboole_0 = '#skF_2'
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1('#skF_1','#skF_2','#skF_3') != '#skF_2'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_120,c_5010])).

tff(c_5042,plain,
    ( k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_partfun1('#skF_1')
    | k1_xboole_0 = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_124,c_122,c_112,c_108,c_5028])).

tff(c_5043,plain,(
    k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_partfun1('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_104,c_5042])).

tff(c_442,plain,
    ( k2_relat_1(k2_funct_1('#skF_3')) = k1_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_438,c_24])).

tff(c_455,plain,(
    k2_relat_1(k2_funct_1('#skF_3')) = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_318,c_442])).

tff(c_589,plain,(
    ! [A_120,B_121] :
      ( r1_tarski(k2_relat_1(k5_relat_1(A_120,B_121)),k2_relat_1(B_121))
      | ~ v1_relat_1(B_121)
      | ~ v1_relat_1(A_120) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_606,plain,(
    ! [A_120] :
      ( r1_tarski(k2_relat_1(k5_relat_1(A_120,k2_funct_1('#skF_3'))),k1_relat_1('#skF_3'))
      | ~ v1_relat_1(k2_funct_1('#skF_3'))
      | ~ v1_relat_1(A_120) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_455,c_589])).

tff(c_629,plain,(
    ! [A_120] :
      ( r1_tarski(k2_relat_1(k5_relat_1(A_120,k2_funct_1('#skF_3'))),k1_relat_1('#skF_3'))
      | ~ v1_relat_1(A_120) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_461,c_606])).

tff(c_5056,plain,
    ( r1_tarski(k2_relat_1(k6_partfun1('#skF_1')),k1_relat_1('#skF_3'))
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_5043,c_629])).

tff(c_5065,plain,(
    r1_tarski('#skF_1',k1_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_318,c_131,c_5056])).

tff(c_5067,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3863,c_5065])).

tff(c_5068,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_1420])).

tff(c_5081,plain,(
    k2_relat_1(k2_funct_1('#skF_3')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5068,c_455])).

tff(c_36,plain,(
    ! [A_22] : k4_relat_1(k6_relat_1(A_22)) = k6_relat_1(A_22) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_130,plain,(
    ! [A_22] : k4_relat_1(k6_partfun1(A_22)) = k6_partfun1(A_22) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_80,c_36])).

tff(c_14124,plain,(
    ! [E_789,D_790,A_791,B_786,C_788,F_787] :
      ( k1_partfun1(A_791,B_786,C_788,D_790,E_789,F_787) = k5_relat_1(E_789,F_787)
      | ~ m1_subset_1(F_787,k1_zfmisc_1(k2_zfmisc_1(C_788,D_790)))
      | ~ v1_funct_1(F_787)
      | ~ m1_subset_1(E_789,k1_zfmisc_1(k2_zfmisc_1(A_791,B_786)))
      | ~ v1_funct_1(E_789) ) ),
    inference(cnfTransformation,[status(thm)],[f_195])).

tff(c_14136,plain,(
    ! [A_791,B_786,E_789] :
      ( k1_partfun1(A_791,B_786,'#skF_2','#skF_1',E_789,'#skF_4') = k5_relat_1(E_789,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_789,k1_zfmisc_1(k2_zfmisc_1(A_791,B_786)))
      | ~ v1_funct_1(E_789) ) ),
    inference(resolution,[status(thm)],[c_114,c_14124])).

tff(c_14539,plain,(
    ! [A_805,B_806,E_807] :
      ( k1_partfun1(A_805,B_806,'#skF_2','#skF_1',E_807,'#skF_4') = k5_relat_1(E_807,'#skF_4')
      | ~ m1_subset_1(E_807,k1_zfmisc_1(k2_zfmisc_1(A_805,B_806)))
      | ~ v1_funct_1(E_807) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_118,c_14136])).

tff(c_14556,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_120,c_14539])).

tff(c_14566,plain,(
    k5_relat_1('#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_124,c_3846,c_14556])).

tff(c_853,plain,(
    ! [B_138,A_139] :
      ( k5_relat_1(k4_relat_1(B_138),k4_relat_1(A_139)) = k4_relat_1(k5_relat_1(A_139,B_138))
      | ~ v1_relat_1(B_138)
      | ~ v1_relat_1(A_139) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_874,plain,(
    ! [B_138] :
      ( k5_relat_1(k4_relat_1(B_138),k2_funct_1('#skF_3')) = k4_relat_1(k5_relat_1('#skF_3',B_138))
      | ~ v1_relat_1(B_138)
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_438,c_853])).

tff(c_896,plain,(
    ! [B_138] :
      ( k5_relat_1(k4_relat_1(B_138),k2_funct_1('#skF_3')) = k4_relat_1(k5_relat_1('#skF_3',B_138))
      | ~ v1_relat_1(B_138) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_318,c_874])).

tff(c_10932,plain,
    ( k5_relat_1(k2_funct_1('#skF_4'),k2_funct_1('#skF_3')) = k4_relat_1(k5_relat_1('#skF_3','#skF_4'))
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_10928,c_896])).

tff(c_10957,plain,(
    k5_relat_1(k2_funct_1('#skF_4'),k2_funct_1('#skF_3')) = k4_relat_1(k5_relat_1('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_321,c_10932])).

tff(c_14571,plain,(
    k5_relat_1(k2_funct_1('#skF_4'),k2_funct_1('#skF_3')) = k4_relat_1(k6_partfun1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14566,c_10957])).

tff(c_14573,plain,(
    k5_relat_1(k2_funct_1('#skF_4'),k2_funct_1('#skF_3')) = k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_130,c_14571])).

tff(c_58,plain,(
    ! [A_31,B_33] :
      ( k2_funct_1(A_31) = B_33
      | k6_relat_1(k2_relat_1(A_31)) != k5_relat_1(B_33,A_31)
      | k2_relat_1(B_33) != k1_relat_1(A_31)
      | ~ v2_funct_1(A_31)
      | ~ v1_funct_1(B_33)
      | ~ v1_relat_1(B_33)
      | ~ v1_funct_1(A_31)
      | ~ v1_relat_1(A_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_125,plain,(
    ! [A_31,B_33] :
      ( k2_funct_1(A_31) = B_33
      | k6_partfun1(k2_relat_1(A_31)) != k5_relat_1(B_33,A_31)
      | k2_relat_1(B_33) != k1_relat_1(A_31)
      | ~ v2_funct_1(A_31)
      | ~ v1_funct_1(B_33)
      | ~ v1_relat_1(B_33)
      | ~ v1_funct_1(A_31)
      | ~ v1_relat_1(A_31) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_58])).

tff(c_14590,plain,
    ( k2_funct_1(k2_funct_1('#skF_3')) = k2_funct_1('#skF_4')
    | k6_partfun1(k2_relat_1(k2_funct_1('#skF_3'))) != k6_partfun1('#skF_1')
    | k2_relat_1(k2_funct_1('#skF_4')) != k1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_funct_1(k2_funct_1('#skF_4'))
    | ~ v1_relat_1(k2_funct_1('#skF_4'))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_14573,c_125])).

tff(c_14597,plain,
    ( k2_funct_1(k2_funct_1('#skF_3')) = k2_funct_1('#skF_4')
    | ~ v2_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_461,c_5191,c_10971,c_12729,c_13931,c_764,c_5081,c_14590])).

tff(c_14601,plain,(
    ~ v2_funct_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_14597])).

tff(c_13076,plain,(
    ! [C_729,B_730,A_731] :
      ( v1_funct_2(k2_funct_1(C_729),B_730,A_731)
      | k2_relset_1(A_731,B_730,C_729) != B_730
      | ~ v2_funct_1(C_729)
      | ~ m1_subset_1(C_729,k1_zfmisc_1(k2_zfmisc_1(A_731,B_730)))
      | ~ v1_funct_2(C_729,A_731,B_730)
      | ~ v1_funct_1(C_729) ) ),
    inference(cnfTransformation,[status(thm)],[f_256])).

tff(c_13090,plain,
    ( v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | k2_relset_1('#skF_1','#skF_2','#skF_3') != '#skF_2'
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_120,c_13076])).

tff(c_13101,plain,(
    v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_124,c_122,c_108,c_112,c_13090])).

tff(c_14236,plain,(
    ! [C_793,B_794,A_795] :
      ( m1_subset_1(k2_funct_1(C_793),k1_zfmisc_1(k2_zfmisc_1(B_794,A_795)))
      | k2_relset_1(A_795,B_794,C_793) != B_794
      | ~ v2_funct_1(C_793)
      | ~ m1_subset_1(C_793,k1_zfmisc_1(k2_zfmisc_1(A_795,B_794)))
      | ~ v1_funct_2(C_793,A_795,B_794)
      | ~ v1_funct_1(C_793) ) ),
    inference(cnfTransformation,[status(thm)],[f_256])).

tff(c_62,plain,(
    ! [A_38,B_39,C_40] :
      ( k2_relset_1(A_38,B_39,C_40) = k2_relat_1(C_40)
      | ~ m1_subset_1(C_40,k1_zfmisc_1(k2_zfmisc_1(A_38,B_39))) ) ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_47978,plain,(
    ! [B_1578,A_1579,C_1580] :
      ( k2_relset_1(B_1578,A_1579,k2_funct_1(C_1580)) = k2_relat_1(k2_funct_1(C_1580))
      | k2_relset_1(A_1579,B_1578,C_1580) != B_1578
      | ~ v2_funct_1(C_1580)
      | ~ m1_subset_1(C_1580,k1_zfmisc_1(k2_zfmisc_1(A_1579,B_1578)))
      | ~ v1_funct_2(C_1580,A_1579,B_1578)
      | ~ v1_funct_1(C_1580) ) ),
    inference(resolution,[status(thm)],[c_14236,c_62])).

tff(c_48039,plain,
    ( k2_relset_1('#skF_2','#skF_1',k2_funct_1('#skF_3')) = k2_relat_1(k2_funct_1('#skF_3'))
    | k2_relset_1('#skF_1','#skF_2','#skF_3') != '#skF_2'
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_120,c_47978])).

tff(c_48079,plain,(
    k2_relset_1('#skF_2','#skF_1',k2_funct_1('#skF_3')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_124,c_122,c_108,c_112,c_5081,c_48039])).

tff(c_14437,plain,(
    ! [B_802,C_803,A_804] :
      ( k6_partfun1(B_802) = k5_relat_1(k2_funct_1(C_803),C_803)
      | k1_xboole_0 = B_802
      | ~ v2_funct_1(C_803)
      | k2_relset_1(A_804,B_802,C_803) != B_802
      | ~ m1_subset_1(C_803,k1_zfmisc_1(k2_zfmisc_1(A_804,B_802)))
      | ~ v1_funct_2(C_803,A_804,B_802)
      | ~ v1_funct_1(C_803) ) ),
    inference(cnfTransformation,[status(thm)],[f_272])).

tff(c_14449,plain,
    ( k5_relat_1(k2_funct_1('#skF_3'),'#skF_3') = k6_partfun1('#skF_2')
    | k1_xboole_0 = '#skF_2'
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1('#skF_1','#skF_2','#skF_3') != '#skF_2'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_120,c_14437])).

tff(c_14460,plain,
    ( k5_relat_1(k2_funct_1('#skF_3'),'#skF_3') = k6_partfun1('#skF_2')
    | k1_xboole_0 = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_124,c_122,c_112,c_108,c_14449])).

tff(c_14461,plain,(
    k5_relat_1(k2_funct_1('#skF_3'),'#skF_3') = k6_partfun1('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_104,c_14460])).

tff(c_14274,plain,(
    ! [C_793,B_794,A_795] :
      ( r1_tarski(k2_funct_1(C_793),k2_zfmisc_1(B_794,A_795))
      | k2_relset_1(A_795,B_794,C_793) != B_794
      | ~ v2_funct_1(C_793)
      | ~ m1_subset_1(C_793,k1_zfmisc_1(k2_zfmisc_1(A_795,B_794)))
      | ~ v1_funct_2(C_793,A_795,B_794)
      | ~ v1_funct_1(C_793) ) ),
    inference(resolution,[status(thm)],[c_14236,c_8])).

tff(c_64,plain,(
    ! [A_41,B_42,C_43,D_44] :
      ( k8_relset_1(A_41,B_42,C_43,D_44) = k10_relat_1(C_43,D_44)
      | ~ m1_subset_1(C_43,k1_zfmisc_1(k2_zfmisc_1(A_41,B_42))) ) ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_48391,plain,(
    ! [B_1588,A_1589,C_1590,D_1591] :
      ( k8_relset_1(B_1588,A_1589,k2_funct_1(C_1590),D_1591) = k10_relat_1(k2_funct_1(C_1590),D_1591)
      | k2_relset_1(A_1589,B_1588,C_1590) != B_1588
      | ~ v2_funct_1(C_1590)
      | ~ m1_subset_1(C_1590,k1_zfmisc_1(k2_zfmisc_1(A_1589,B_1588)))
      | ~ v1_funct_2(C_1590,A_1589,B_1588)
      | ~ v1_funct_1(C_1590) ) ),
    inference(resolution,[status(thm)],[c_14236,c_64])).

tff(c_48436,plain,(
    ! [D_1591] :
      ( k8_relset_1('#skF_2','#skF_1',k2_funct_1('#skF_3'),D_1591) = k10_relat_1(k2_funct_1('#skF_3'),D_1591)
      | k2_relset_1('#skF_1','#skF_2','#skF_3') != '#skF_2'
      | ~ v2_funct_1('#skF_3')
      | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
      | ~ v1_funct_1('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_120,c_48391])).

tff(c_48482,plain,(
    ! [D_1592] : k8_relset_1('#skF_2','#skF_1',k2_funct_1('#skF_3'),D_1592) = k10_relat_1(k2_funct_1('#skF_3'),D_1592) ),
    inference(demodulation,[status(thm),theory(equality)],[c_124,c_122,c_108,c_112,c_48436])).

tff(c_10,plain,(
    ! [A_3,B_4] :
      ( m1_subset_1(A_3,k1_zfmisc_1(B_4))
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_1174,plain,(
    ! [A_149,B_150,C_151,D_152] :
      ( m1_subset_1(k8_relset_1(A_149,B_150,C_151,D_152),k1_zfmisc_1(A_149))
      | ~ m1_subset_1(C_151,k1_zfmisc_1(k2_zfmisc_1(A_149,B_150))) ) ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_30476,plain,(
    ! [A_1193,B_1194,C_1195,D_1196] :
      ( r1_tarski(k8_relset_1(A_1193,B_1194,C_1195,D_1196),A_1193)
      | ~ m1_subset_1(C_1195,k1_zfmisc_1(k2_zfmisc_1(A_1193,B_1194))) ) ),
    inference(resolution,[status(thm)],[c_1174,c_8])).

tff(c_30515,plain,(
    ! [A_1193,B_1194,A_3,D_1196] :
      ( r1_tarski(k8_relset_1(A_1193,B_1194,A_3,D_1196),A_1193)
      | ~ r1_tarski(A_3,k2_zfmisc_1(A_1193,B_1194)) ) ),
    inference(resolution,[status(thm)],[c_10,c_30476])).

tff(c_48488,plain,(
    ! [D_1592] :
      ( r1_tarski(k10_relat_1(k2_funct_1('#skF_3'),D_1592),'#skF_2')
      | ~ r1_tarski(k2_funct_1('#skF_3'),k2_zfmisc_1('#skF_2','#skF_1')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_48482,c_30515])).

tff(c_48512,plain,(
    ~ r1_tarski(k2_funct_1('#skF_3'),k2_zfmisc_1('#skF_2','#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_48488])).

tff(c_48515,plain,
    ( k2_relset_1('#skF_1','#skF_2','#skF_3') != '#skF_2'
    | ~ v2_funct_1('#skF_3')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_14274,c_48512])).

tff(c_48519,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_124,c_122,c_120,c_108,c_112,c_48515])).

tff(c_48521,plain,(
    r1_tarski(k2_funct_1('#skF_3'),k2_zfmisc_1('#skF_2','#skF_1')) ),
    inference(splitRight,[status(thm)],[c_48488])).

tff(c_14134,plain,(
    ! [A_791,B_786,E_789] :
      ( k1_partfun1(A_791,B_786,'#skF_1','#skF_2',E_789,'#skF_3') = k5_relat_1(E_789,'#skF_3')
      | ~ v1_funct_1('#skF_3')
      | ~ m1_subset_1(E_789,k1_zfmisc_1(k2_zfmisc_1(A_791,B_786)))
      | ~ v1_funct_1(E_789) ) ),
    inference(resolution,[status(thm)],[c_120,c_14124])).

tff(c_14978,plain,(
    ! [A_827,B_828,E_829] :
      ( k1_partfun1(A_827,B_828,'#skF_1','#skF_2',E_829,'#skF_3') = k5_relat_1(E_829,'#skF_3')
      | ~ m1_subset_1(E_829,k1_zfmisc_1(k2_zfmisc_1(A_827,B_828)))
      | ~ v1_funct_1(E_829) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_124,c_14134])).

tff(c_15016,plain,(
    ! [A_827,B_828,A_3] :
      ( k1_partfun1(A_827,B_828,'#skF_1','#skF_2',A_3,'#skF_3') = k5_relat_1(A_3,'#skF_3')
      | ~ v1_funct_1(A_3)
      | ~ r1_tarski(A_3,k2_zfmisc_1(A_827,B_828)) ) ),
    inference(resolution,[status(thm)],[c_10,c_14978])).

tff(c_48577,plain,
    ( k1_partfun1('#skF_2','#skF_1','#skF_1','#skF_2',k2_funct_1('#skF_3'),'#skF_3') = k5_relat_1(k2_funct_1('#skF_3'),'#skF_3')
    | ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_48521,c_15016])).

tff(c_48629,plain,(
    k1_partfun1('#skF_2','#skF_1','#skF_1','#skF_2',k2_funct_1('#skF_3'),'#skF_3') = k6_partfun1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5191,c_14461,c_48577])).

tff(c_90,plain,(
    ! [C_70,E_73,B_69,D_71,A_68] :
      ( k1_xboole_0 = C_70
      | v2_funct_1(D_71)
      | k2_relset_1(A_68,B_69,D_71) != B_69
      | ~ v2_funct_1(k1_partfun1(A_68,B_69,B_69,C_70,D_71,E_73))
      | ~ m1_subset_1(E_73,k1_zfmisc_1(k2_zfmisc_1(B_69,C_70)))
      | ~ v1_funct_2(E_73,B_69,C_70)
      | ~ v1_funct_1(E_73)
      | ~ m1_subset_1(D_71,k1_zfmisc_1(k2_zfmisc_1(A_68,B_69)))
      | ~ v1_funct_2(D_71,A_68,B_69)
      | ~ v1_funct_1(D_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_240])).

tff(c_48800,plain,
    ( k1_xboole_0 = '#skF_2'
    | v2_funct_1(k2_funct_1('#skF_3'))
    | k2_relset_1('#skF_2','#skF_1',k2_funct_1('#skF_3')) != '#skF_1'
    | ~ v2_funct_1(k6_partfun1('#skF_2'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3')
    | ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_48629,c_90])).

tff(c_48814,plain,
    ( k1_xboole_0 = '#skF_2'
    | v2_funct_1(k2_funct_1('#skF_3'))
    | ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5191,c_13101,c_124,c_122,c_120,c_126,c_48079,c_48800])).

tff(c_48815,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(negUnitSimplification,[status(thm)],[c_14601,c_104,c_48814])).

tff(c_48826,plain,
    ( k2_relset_1('#skF_1','#skF_2','#skF_3') != '#skF_2'
    | ~ v2_funct_1('#skF_3')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_92,c_48815])).

tff(c_48833,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_124,c_122,c_120,c_108,c_112,c_48826])).

tff(c_48835,plain,(
    v2_funct_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_14597])).

tff(c_48838,plain,
    ( k4_relat_1(k2_funct_1('#skF_3')) = k2_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_48835,c_42])).

tff(c_48841,plain,(
    k2_funct_1(k2_funct_1('#skF_3')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_461,c_5191,c_459,c_48838])).

tff(c_48834,plain,(
    k2_funct_1(k2_funct_1('#skF_3')) = k2_funct_1('#skF_4') ),
    inference(splitRight,[status(thm)],[c_14597])).

tff(c_48876,plain,(
    k2_funct_1('#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_48841,c_48834])).

tff(c_10950,plain,
    ( k4_relat_1(k2_funct_1('#skF_4')) = '#skF_4'
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_10928,c_18])).

tff(c_10969,plain,(
    k4_relat_1(k2_funct_1('#skF_4')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_321,c_10950])).

tff(c_48889,plain,(
    k4_relat_1('#skF_3') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_48876,c_10969])).

tff(c_48938,plain,(
    k2_funct_1('#skF_3') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_48889,c_438])).

tff(c_48940,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_102,c_48938])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n015.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 19:10:23 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 20.27/11.41  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 20.44/11.44  
% 20.44/11.44  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 20.44/11.44  %$ r2_relset_1 > v1_funct_2 > v1_partfun1 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k8_relset_1 > k2_relset_1 > k9_relat_1 > k5_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k6_relat_1 > k6_partfun1 > k4_relat_1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 20.44/11.44  
% 20.44/11.44  %Foreground sorts:
% 20.44/11.44  
% 20.44/11.44  
% 20.44/11.44  %Background operators:
% 20.44/11.44  
% 20.44/11.44  
% 20.44/11.44  %Foreground operators:
% 20.44/11.44  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 20.44/11.44  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 20.44/11.44  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 20.44/11.44  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 20.44/11.44  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 20.44/11.44  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 20.44/11.44  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 20.44/11.44  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 20.44/11.44  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 20.44/11.44  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 20.44/11.44  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 20.44/11.44  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 20.44/11.44  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 20.44/11.44  tff('#skF_2', type, '#skF_2': $i).
% 20.44/11.44  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 20.44/11.44  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 20.44/11.44  tff('#skF_3', type, '#skF_3': $i).
% 20.44/11.44  tff('#skF_1', type, '#skF_1': $i).
% 20.44/11.44  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 20.44/11.44  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 20.44/11.44  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 20.44/11.44  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 20.44/11.44  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 20.44/11.44  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 20.44/11.44  tff('#skF_4', type, '#skF_4': $i).
% 20.44/11.44  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 20.44/11.44  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 20.44/11.44  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 20.44/11.44  tff(k4_relat_1, type, k4_relat_1: $i > $i).
% 20.44/11.44  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 20.44/11.44  
% 20.49/11.47  tff(f_298, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => ((((k2_relset_1(A, B, C) = B) & r2_relset_1(A, A, k1_partfun1(A, B, B, A, C, D), k6_partfun1(A))) & v2_funct_1(C)) => (((A = k1_xboole_0) | (B = k1_xboole_0)) | (D = k2_funct_1(C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_funct_2)).
% 20.49/11.47  tff(f_48, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 20.49/11.47  tff(f_42, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 20.49/11.47  tff(f_102, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => (k2_funct_1(A) = k4_relat_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d9_funct_1)).
% 20.49/11.47  tff(f_46, axiom, (![A]: (v1_relat_1(A) => v1_relat_1(k4_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k4_relat_1)).
% 20.49/11.47  tff(f_256, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((v2_funct_1(C) & (k2_relset_1(A, B, C) = B)) => ((v1_funct_1(k2_funct_1(C)) & v1_funct_2(k2_funct_1(C), B, A)) & m1_subset_1(k2_funct_1(C), k1_zfmisc_1(k2_zfmisc_1(B, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_funct_2)).
% 20.49/11.47  tff(f_52, axiom, (![A]: (v1_relat_1(A) => (k4_relat_1(k4_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', involutiveness_k4_relat_1)).
% 20.49/11.47  tff(f_157, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 20.49/11.47  tff(f_197, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 20.49/11.47  tff(f_114, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v2_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc4_funct_1)).
% 20.49/11.47  tff(f_195, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 20.49/11.47  tff(f_185, axiom, (![A]: (v1_partfun1(k6_partfun1(A), A) & m1_subset_1(k6_partfun1(A), k1_zfmisc_1(k2_zfmisc_1(A, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_partfun1)).
% 20.49/11.47  tff(f_169, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 20.49/11.47  tff(f_181, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (v1_funct_1(k1_partfun1(A, B, C, D, E, F)) & m1_subset_1(k1_partfun1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 20.49/11.47  tff(f_240, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, B, C)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => ((v2_funct_1(k1_partfun1(A, B, B, C, D, E)) & (k2_relset_1(A, B, D) = B)) => (((C = k1_xboole_0) & ~(B = k1_xboole_0)) | (v2_funct_1(D) & v2_funct_1(E)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t30_funct_2)).
% 20.49/11.47  tff(f_214, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (r2_relset_1(B, B, k1_partfun1(B, A, A, B, D, C), k6_partfun1(B)) => (k2_relset_1(A, B, C) = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t24_funct_2)).
% 20.49/11.47  tff(f_60, axiom, (![A]: (v1_relat_1(A) => (k10_relat_1(A, k2_relat_1(A)) = k1_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t169_relat_1)).
% 20.49/11.47  tff(f_161, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k8_relset_1(A, B, C, D) = k10_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k8_relset_1)).
% 20.49/11.47  tff(f_153, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k8_relset_1(A, B, C, D), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k8_relset_1)).
% 20.49/11.47  tff(f_35, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 20.49/11.47  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 20.49/11.47  tff(f_66, axiom, (![A]: (v1_relat_1(A) => ((k2_relat_1(A) = k1_relat_1(k4_relat_1(A))) & (k1_relat_1(A) = k2_relat_1(k4_relat_1(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t37_relat_1)).
% 20.49/11.47  tff(f_84, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 20.49/11.47  tff(f_272, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((k2_relset_1(A, B, C) = B) & v2_funct_1(C)) => ((B = k1_xboole_0) | ((k5_relat_1(C, k2_funct_1(C)) = k6_partfun1(A)) & (k5_relat_1(k2_funct_1(C), C) = k6_partfun1(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t35_funct_2)).
% 20.49/11.47  tff(f_73, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => r1_tarski(k2_relat_1(k5_relat_1(A, B)), k2_relat_1(B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t45_relat_1)).
% 20.49/11.47  tff(f_86, axiom, (![A]: (k4_relat_1(k6_relat_1(A)) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_relat_1)).
% 20.49/11.47  tff(f_80, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k4_relat_1(k5_relat_1(A, B)) = k5_relat_1(k4_relat_1(B), k4_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t54_relat_1)).
% 20.49/11.47  tff(f_149, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (((v2_funct_1(A) & (k2_relat_1(B) = k1_relat_1(A))) & (k5_relat_1(B, A) = k6_relat_1(k2_relat_1(A)))) => (B = k2_funct_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_funct_1)).
% 20.49/11.47  tff(c_102, plain, (k2_funct_1('#skF_3')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_298])).
% 20.49/11.47  tff(c_16, plain, (![A_9, B_10]: (v1_relat_1(k2_zfmisc_1(A_9, B_10)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 20.49/11.47  tff(c_120, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_298])).
% 20.49/11.47  tff(c_299, plain, (![B_106, A_107]: (v1_relat_1(B_106) | ~m1_subset_1(B_106, k1_zfmisc_1(A_107)) | ~v1_relat_1(A_107))), inference(cnfTransformation, [status(thm)], [f_42])).
% 20.49/11.47  tff(c_308, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_120, c_299])).
% 20.49/11.47  tff(c_318, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_16, c_308])).
% 20.49/11.47  tff(c_124, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_298])).
% 20.49/11.47  tff(c_108, plain, (v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_298])).
% 20.49/11.47  tff(c_426, plain, (![A_116]: (k4_relat_1(A_116)=k2_funct_1(A_116) | ~v2_funct_1(A_116) | ~v1_funct_1(A_116) | ~v1_relat_1(A_116))), inference(cnfTransformation, [status(thm)], [f_102])).
% 20.49/11.47  tff(c_432, plain, (k4_relat_1('#skF_3')=k2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_108, c_426])).
% 20.49/11.47  tff(c_438, plain, (k4_relat_1('#skF_3')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_318, c_124, c_432])).
% 20.49/11.47  tff(c_14, plain, (![A_8]: (v1_relat_1(k4_relat_1(A_8)) | ~v1_relat_1(A_8))), inference(cnfTransformation, [status(thm)], [f_46])).
% 20.49/11.47  tff(c_451, plain, (v1_relat_1(k2_funct_1('#skF_3')) | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_438, c_14])).
% 20.49/11.47  tff(c_461, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_318, c_451])).
% 20.49/11.47  tff(c_122, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_298])).
% 20.49/11.47  tff(c_112, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_2'), inference(cnfTransformation, [status(thm)], [f_298])).
% 20.49/11.47  tff(c_5166, plain, (![C_369, A_370, B_371]: (v1_funct_1(k2_funct_1(C_369)) | k2_relset_1(A_370, B_371, C_369)!=B_371 | ~v2_funct_1(C_369) | ~m1_subset_1(C_369, k1_zfmisc_1(k2_zfmisc_1(A_370, B_371))) | ~v1_funct_2(C_369, A_370, B_371) | ~v1_funct_1(C_369))), inference(cnfTransformation, [status(thm)], [f_256])).
% 20.49/11.47  tff(c_5180, plain, (v1_funct_1(k2_funct_1('#skF_3')) | k2_relset_1('#skF_1', '#skF_2', '#skF_3')!='#skF_2' | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_120, c_5166])).
% 20.49/11.47  tff(c_5191, plain, (v1_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_124, c_122, c_108, c_112, c_5180])).
% 20.49/11.47  tff(c_18, plain, (![A_11]: (k4_relat_1(k4_relat_1(A_11))=A_11 | ~v1_relat_1(A_11))), inference(cnfTransformation, [status(thm)], [f_52])).
% 20.49/11.47  tff(c_448, plain, (k4_relat_1(k2_funct_1('#skF_3'))='#skF_3' | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_438, c_18])).
% 20.49/11.47  tff(c_459, plain, (k4_relat_1(k2_funct_1('#skF_3'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_318, c_448])).
% 20.49/11.47  tff(c_92, plain, (![C_76, B_75, A_74]: (m1_subset_1(k2_funct_1(C_76), k1_zfmisc_1(k2_zfmisc_1(B_75, A_74))) | k2_relset_1(A_74, B_75, C_76)!=B_75 | ~v2_funct_1(C_76) | ~m1_subset_1(C_76, k1_zfmisc_1(k2_zfmisc_1(A_74, B_75))) | ~v1_funct_2(C_76, A_74, B_75) | ~v1_funct_1(C_76))), inference(cnfTransformation, [status(thm)], [f_256])).
% 20.49/11.47  tff(c_114, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_298])).
% 20.49/11.47  tff(c_311, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_1'))), inference(resolution, [status(thm)], [c_114, c_299])).
% 20.49/11.47  tff(c_321, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_16, c_311])).
% 20.49/11.47  tff(c_118, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_298])).
% 20.49/11.47  tff(c_116, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_298])).
% 20.49/11.47  tff(c_741, plain, (![A_134, B_135, C_136]: (k2_relset_1(A_134, B_135, C_136)=k2_relat_1(C_136) | ~m1_subset_1(C_136, k1_zfmisc_1(k2_zfmisc_1(A_134, B_135))))), inference(cnfTransformation, [status(thm)], [f_157])).
% 20.49/11.47  tff(c_760, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_114, c_741])).
% 20.49/11.47  tff(c_5183, plain, (v1_funct_1(k2_funct_1('#skF_4')) | k2_relset_1('#skF_2', '#skF_1', '#skF_4')!='#skF_1' | ~v2_funct_1('#skF_4') | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_114, c_5166])).
% 20.49/11.47  tff(c_5194, plain, (v1_funct_1(k2_funct_1('#skF_4')) | k2_relat_1('#skF_4')!='#skF_1' | ~v2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_118, c_116, c_760, c_5183])).
% 20.49/11.47  tff(c_5200, plain, (~v2_funct_1('#skF_4')), inference(splitLeft, [status(thm)], [c_5194])).
% 20.49/11.47  tff(c_106, plain, (k1_xboole_0!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_298])).
% 20.49/11.47  tff(c_80, plain, (![A_62]: (k6_relat_1(A_62)=k6_partfun1(A_62))), inference(cnfTransformation, [status(thm)], [f_197])).
% 20.49/11.47  tff(c_50, plain, (![A_27]: (v2_funct_1(k6_relat_1(A_27)))), inference(cnfTransformation, [status(thm)], [f_114])).
% 20.49/11.47  tff(c_126, plain, (![A_27]: (v2_funct_1(k6_partfun1(A_27)))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_50])).
% 20.49/11.47  tff(c_3164, plain, (![F_269, C_270, E_271, A_273, D_272, B_268]: (k1_partfun1(A_273, B_268, C_270, D_272, E_271, F_269)=k5_relat_1(E_271, F_269) | ~m1_subset_1(F_269, k1_zfmisc_1(k2_zfmisc_1(C_270, D_272))) | ~v1_funct_1(F_269) | ~m1_subset_1(E_271, k1_zfmisc_1(k2_zfmisc_1(A_273, B_268))) | ~v1_funct_1(E_271))), inference(cnfTransformation, [status(thm)], [f_195])).
% 20.49/11.47  tff(c_3184, plain, (![A_273, B_268, E_271]: (k1_partfun1(A_273, B_268, '#skF_2', '#skF_1', E_271, '#skF_4')=k5_relat_1(E_271, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_271, k1_zfmisc_1(k2_zfmisc_1(A_273, B_268))) | ~v1_funct_1(E_271))), inference(resolution, [status(thm)], [c_114, c_3164])).
% 20.49/11.47  tff(c_3462, plain, (![A_285, B_286, E_287]: (k1_partfun1(A_285, B_286, '#skF_2', '#skF_1', E_287, '#skF_4')=k5_relat_1(E_287, '#skF_4') | ~m1_subset_1(E_287, k1_zfmisc_1(k2_zfmisc_1(A_285, B_286))) | ~v1_funct_1(E_287))), inference(demodulation, [status(thm), theory('equality')], [c_118, c_3184])).
% 20.49/11.47  tff(c_3487, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_120, c_3462])).
% 20.49/11.47  tff(c_3499, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_124, c_3487])).
% 20.49/11.47  tff(c_76, plain, (![A_55]: (m1_subset_1(k6_partfun1(A_55), k1_zfmisc_1(k2_zfmisc_1(A_55, A_55))))), inference(cnfTransformation, [status(thm)], [f_185])).
% 20.49/11.47  tff(c_110, plain, (r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k6_partfun1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_298])).
% 20.49/11.47  tff(c_1433, plain, (![D_164, C_165, A_166, B_167]: (D_164=C_165 | ~r2_relset_1(A_166, B_167, C_165, D_164) | ~m1_subset_1(D_164, k1_zfmisc_1(k2_zfmisc_1(A_166, B_167))) | ~m1_subset_1(C_165, k1_zfmisc_1(k2_zfmisc_1(A_166, B_167))))), inference(cnfTransformation, [status(thm)], [f_169])).
% 20.49/11.47  tff(c_1443, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_110, c_1433])).
% 20.49/11.47  tff(c_1460, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_1443])).
% 20.49/11.47  tff(c_1497, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_1460])).
% 20.49/11.47  tff(c_3505, plain, (~m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_3499, c_1497])).
% 20.49/11.47  tff(c_3771, plain, (![C_297, E_298, D_302, A_301, B_299, F_300]: (m1_subset_1(k1_partfun1(A_301, B_299, C_297, D_302, E_298, F_300), k1_zfmisc_1(k2_zfmisc_1(A_301, D_302))) | ~m1_subset_1(F_300, k1_zfmisc_1(k2_zfmisc_1(C_297, D_302))) | ~v1_funct_1(F_300) | ~m1_subset_1(E_298, k1_zfmisc_1(k2_zfmisc_1(A_301, B_299))) | ~v1_funct_1(E_298))), inference(cnfTransformation, [status(thm)], [f_181])).
% 20.49/11.47  tff(c_3816, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_3499, c_3771])).
% 20.49/11.47  tff(c_3843, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_124, c_120, c_118, c_114, c_3816])).
% 20.49/11.47  tff(c_3845, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3505, c_3843])).
% 20.49/11.47  tff(c_3846, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_1460])).
% 20.49/11.47  tff(c_10909, plain, (![C_633, B_634, E_635, A_636, D_632]: (k1_xboole_0=C_633 | v2_funct_1(E_635) | k2_relset_1(A_636, B_634, D_632)!=B_634 | ~v2_funct_1(k1_partfun1(A_636, B_634, B_634, C_633, D_632, E_635)) | ~m1_subset_1(E_635, k1_zfmisc_1(k2_zfmisc_1(B_634, C_633))) | ~v1_funct_2(E_635, B_634, C_633) | ~v1_funct_1(E_635) | ~m1_subset_1(D_632, k1_zfmisc_1(k2_zfmisc_1(A_636, B_634))) | ~v1_funct_2(D_632, A_636, B_634) | ~v1_funct_1(D_632))), inference(cnfTransformation, [status(thm)], [f_240])).
% 20.49/11.47  tff(c_10913, plain, (k1_xboole_0='#skF_1' | v2_funct_1('#skF_4') | k2_relset_1('#skF_1', '#skF_2', '#skF_3')!='#skF_2' | ~v2_funct_1(k6_partfun1('#skF_1')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_3846, c_10909])).
% 20.49/11.47  tff(c_10918, plain, (k1_xboole_0='#skF_1' | v2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_124, c_122, c_120, c_118, c_116, c_114, c_126, c_112, c_10913])).
% 20.49/11.47  tff(c_10920, plain, $false, inference(negUnitSimplification, [status(thm)], [c_5200, c_106, c_10918])).
% 20.49/11.47  tff(c_10922, plain, (v2_funct_1('#skF_4')), inference(splitRight, [status(thm)], [c_5194])).
% 20.49/11.47  tff(c_42, plain, (![A_25]: (k4_relat_1(A_25)=k2_funct_1(A_25) | ~v2_funct_1(A_25) | ~v1_funct_1(A_25) | ~v1_relat_1(A_25))), inference(cnfTransformation, [status(thm)], [f_102])).
% 20.49/11.47  tff(c_10925, plain, (k4_relat_1('#skF_4')=k2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_10922, c_42])).
% 20.49/11.47  tff(c_10928, plain, (k4_relat_1('#skF_4')=k2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_321, c_118, c_10925])).
% 20.49/11.47  tff(c_10953, plain, (v1_relat_1(k2_funct_1('#skF_4')) | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_10928, c_14])).
% 20.49/11.47  tff(c_10971, plain, (v1_relat_1(k2_funct_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_321, c_10953])).
% 20.49/11.47  tff(c_10921, plain, (k2_relat_1('#skF_4')!='#skF_1' | v1_funct_1(k2_funct_1('#skF_4'))), inference(splitRight, [status(thm)], [c_5194])).
% 20.49/11.47  tff(c_10973, plain, (k2_relat_1('#skF_4')!='#skF_1'), inference(splitLeft, [status(thm)], [c_10921])).
% 20.49/11.47  tff(c_705, plain, (![A_127, B_128, D_129]: (r2_relset_1(A_127, B_128, D_129, D_129) | ~m1_subset_1(D_129, k1_zfmisc_1(k2_zfmisc_1(A_127, B_128))))), inference(cnfTransformation, [status(thm)], [f_169])).
% 20.49/11.47  tff(c_715, plain, (![A_55]: (r2_relset_1(A_55, A_55, k6_partfun1(A_55), k6_partfun1(A_55)))), inference(resolution, [status(thm)], [c_76, c_705])).
% 20.49/11.47  tff(c_12716, plain, (![A_722, B_723, C_724, D_725]: (k2_relset_1(A_722, B_723, C_724)=B_723 | ~r2_relset_1(B_723, B_723, k1_partfun1(B_723, A_722, A_722, B_723, D_725, C_724), k6_partfun1(B_723)) | ~m1_subset_1(D_725, k1_zfmisc_1(k2_zfmisc_1(B_723, A_722))) | ~v1_funct_2(D_725, B_723, A_722) | ~v1_funct_1(D_725) | ~m1_subset_1(C_724, k1_zfmisc_1(k2_zfmisc_1(A_722, B_723))) | ~v1_funct_2(C_724, A_722, B_723) | ~v1_funct_1(C_724))), inference(cnfTransformation, [status(thm)], [f_214])).
% 20.49/11.47  tff(c_12722, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')='#skF_1' | ~r2_relset_1('#skF_1', '#skF_1', k6_partfun1('#skF_1'), k6_partfun1('#skF_1')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_3846, c_12716])).
% 20.49/11.47  tff(c_12726, plain, (k2_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_118, c_116, c_114, c_124, c_122, c_120, c_715, c_760, c_12722])).
% 20.49/11.47  tff(c_12728, plain, $false, inference(negUnitSimplification, [status(thm)], [c_10973, c_12726])).
% 20.49/11.47  tff(c_12729, plain, (v1_funct_1(k2_funct_1('#skF_4'))), inference(splitRight, [status(thm)], [c_10921])).
% 20.49/11.47  tff(c_22, plain, (![A_13]: (k10_relat_1(A_13, k2_relat_1(A_13))=k1_relat_1(A_13) | ~v1_relat_1(A_13))), inference(cnfTransformation, [status(thm)], [f_60])).
% 20.49/11.47  tff(c_1333, plain, (![A_156, B_157, C_158, D_159]: (k8_relset_1(A_156, B_157, C_158, D_159)=k10_relat_1(C_158, D_159) | ~m1_subset_1(C_158, k1_zfmisc_1(k2_zfmisc_1(A_156, B_157))))), inference(cnfTransformation, [status(thm)], [f_161])).
% 20.49/11.47  tff(c_1398, plain, (![D_163]: (k8_relset_1('#skF_2', '#skF_1', '#skF_4', D_163)=k10_relat_1('#skF_4', D_163))), inference(resolution, [status(thm)], [c_114, c_1333])).
% 20.49/11.47  tff(c_60, plain, (![A_34, B_35, C_36, D_37]: (m1_subset_1(k8_relset_1(A_34, B_35, C_36, D_37), k1_zfmisc_1(A_34)) | ~m1_subset_1(C_36, k1_zfmisc_1(k2_zfmisc_1(A_34, B_35))))), inference(cnfTransformation, [status(thm)], [f_153])).
% 20.49/11.47  tff(c_1404, plain, (![D_163]: (m1_subset_1(k10_relat_1('#skF_4', D_163), k1_zfmisc_1('#skF_2')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))))), inference(superposition, [status(thm), theory('equality')], [c_1398, c_60])).
% 20.49/11.47  tff(c_1461, plain, (![D_168]: (m1_subset_1(k10_relat_1('#skF_4', D_168), k1_zfmisc_1('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_114, c_1404])).
% 20.49/11.47  tff(c_8, plain, (![A_3, B_4]: (r1_tarski(A_3, B_4) | ~m1_subset_1(A_3, k1_zfmisc_1(B_4)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 20.49/11.47  tff(c_1476, plain, (![D_169]: (r1_tarski(k10_relat_1('#skF_4', D_169), '#skF_2'))), inference(resolution, [status(thm)], [c_1461, c_8])).
% 20.49/11.47  tff(c_1485, plain, (r1_tarski(k1_relat_1('#skF_4'), '#skF_2') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_22, c_1476])).
% 20.49/11.47  tff(c_1489, plain, (r1_tarski(k1_relat_1('#skF_4'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_321, c_1485])).
% 20.49/11.47  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 20.49/11.47  tff(c_1496, plain, (k1_relat_1('#skF_4')='#skF_2' | ~r1_tarski('#skF_2', k1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_1489, c_2])).
% 20.49/11.47  tff(c_13105, plain, (~r1_tarski('#skF_2', k1_relat_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_1496])).
% 20.49/11.47  tff(c_24, plain, (![A_14]: (k2_relat_1(k4_relat_1(A_14))=k1_relat_1(A_14) | ~v1_relat_1(A_14))), inference(cnfTransformation, [status(thm)], [f_66])).
% 20.49/11.47  tff(c_10944, plain, (k2_relat_1(k2_funct_1('#skF_4'))=k1_relat_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_10928, c_24])).
% 20.49/11.47  tff(c_10965, plain, (k2_relat_1(k2_funct_1('#skF_4'))=k1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_321, c_10944])).
% 20.49/11.47  tff(c_34, plain, (![A_21]: (k2_relat_1(k6_relat_1(A_21))=A_21)), inference(cnfTransformation, [status(thm)], [f_84])).
% 20.49/11.47  tff(c_131, plain, (![A_21]: (k2_relat_1(k6_partfun1(A_21))=A_21)), inference(demodulation, [status(thm), theory('equality')], [c_80, c_34])).
% 20.49/11.47  tff(c_12730, plain, (k2_relat_1('#skF_4')='#skF_1'), inference(splitRight, [status(thm)], [c_10921])).
% 20.49/11.47  tff(c_12731, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_12730, c_760])).
% 20.49/11.47  tff(c_13864, plain, (![A_774, C_775, B_776]: (k6_partfun1(A_774)=k5_relat_1(C_775, k2_funct_1(C_775)) | k1_xboole_0=B_776 | ~v2_funct_1(C_775) | k2_relset_1(A_774, B_776, C_775)!=B_776 | ~m1_subset_1(C_775, k1_zfmisc_1(k2_zfmisc_1(A_774, B_776))) | ~v1_funct_2(C_775, A_774, B_776) | ~v1_funct_1(C_775))), inference(cnfTransformation, [status(thm)], [f_272])).
% 20.49/11.47  tff(c_13884, plain, (k5_relat_1('#skF_4', k2_funct_1('#skF_4'))=k6_partfun1('#skF_2') | k1_xboole_0='#skF_1' | ~v2_funct_1('#skF_4') | k2_relset_1('#skF_2', '#skF_1', '#skF_4')!='#skF_1' | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_114, c_13864])).
% 20.49/11.47  tff(c_13899, plain, (k5_relat_1('#skF_4', k2_funct_1('#skF_4'))=k6_partfun1('#skF_2') | k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_118, c_116, c_12731, c_10922, c_13884])).
% 20.49/11.47  tff(c_13900, plain, (k5_relat_1('#skF_4', k2_funct_1('#skF_4'))=k6_partfun1('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_106, c_13899])).
% 20.49/11.47  tff(c_28, plain, (![A_15, B_17]: (r1_tarski(k2_relat_1(k5_relat_1(A_15, B_17)), k2_relat_1(B_17)) | ~v1_relat_1(B_17) | ~v1_relat_1(A_15))), inference(cnfTransformation, [status(thm)], [f_73])).
% 20.49/11.47  tff(c_13920, plain, (r1_tarski(k2_relat_1(k6_partfun1('#skF_2')), k2_relat_1(k2_funct_1('#skF_4'))) | ~v1_relat_1(k2_funct_1('#skF_4')) | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_13900, c_28])).
% 20.49/11.47  tff(c_13924, plain, (r1_tarski('#skF_2', k1_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_321, c_10971, c_10965, c_131, c_13920])).
% 20.49/11.47  tff(c_13926, plain, $false, inference(negUnitSimplification, [status(thm)], [c_13105, c_13924])).
% 20.49/11.47  tff(c_13927, plain, (k1_relat_1('#skF_4')='#skF_2'), inference(splitRight, [status(thm)], [c_1496])).
% 20.49/11.47  tff(c_13931, plain, (k2_relat_1(k2_funct_1('#skF_4'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_13927, c_10965])).
% 20.49/11.47  tff(c_751, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_120, c_741])).
% 20.49/11.47  tff(c_759, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_112, c_751])).
% 20.49/11.47  tff(c_26, plain, (![A_14]: (k1_relat_1(k4_relat_1(A_14))=k2_relat_1(A_14) | ~v1_relat_1(A_14))), inference(cnfTransformation, [status(thm)], [f_66])).
% 20.49/11.47  tff(c_445, plain, (k1_relat_1(k2_funct_1('#skF_3'))=k2_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_438, c_26])).
% 20.49/11.47  tff(c_457, plain, (k1_relat_1(k2_funct_1('#skF_3'))=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_318, c_445])).
% 20.49/11.47  tff(c_764, plain, (k1_relat_1(k2_funct_1('#skF_3'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_759, c_457])).
% 20.49/11.47  tff(c_774, plain, (k10_relat_1('#skF_3', '#skF_2')=k1_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_759, c_22])).
% 20.49/11.47  tff(c_782, plain, (k10_relat_1('#skF_3', '#skF_2')=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_318, c_774])).
% 20.49/11.47  tff(c_1351, plain, (![D_160]: (k8_relset_1('#skF_1', '#skF_2', '#skF_3', D_160)=k10_relat_1('#skF_3', D_160))), inference(resolution, [status(thm)], [c_120, c_1333])).
% 20.49/11.47  tff(c_1357, plain, (![D_160]: (m1_subset_1(k10_relat_1('#skF_3', D_160), k1_zfmisc_1('#skF_1')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))))), inference(superposition, [status(thm), theory('equality')], [c_1351, c_60])).
% 20.49/11.47  tff(c_1365, plain, (![D_161]: (m1_subset_1(k10_relat_1('#skF_3', D_161), k1_zfmisc_1('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_120, c_1357])).
% 20.49/11.47  tff(c_1382, plain, (![D_162]: (r1_tarski(k10_relat_1('#skF_3', D_162), '#skF_1'))), inference(resolution, [status(thm)], [c_1365, c_8])).
% 20.49/11.47  tff(c_1389, plain, (r1_tarski(k1_relat_1('#skF_3'), '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_782, c_1382])).
% 20.49/11.47  tff(c_1420, plain, (k1_relat_1('#skF_3')='#skF_1' | ~r1_tarski('#skF_1', k1_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_1389, c_2])).
% 20.49/11.47  tff(c_3863, plain, (~r1_tarski('#skF_1', k1_relat_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_1420])).
% 20.49/11.47  tff(c_104, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_298])).
% 20.49/11.47  tff(c_5010, plain, (![A_366, C_367, B_368]: (k6_partfun1(A_366)=k5_relat_1(C_367, k2_funct_1(C_367)) | k1_xboole_0=B_368 | ~v2_funct_1(C_367) | k2_relset_1(A_366, B_368, C_367)!=B_368 | ~m1_subset_1(C_367, k1_zfmisc_1(k2_zfmisc_1(A_366, B_368))) | ~v1_funct_2(C_367, A_366, B_368) | ~v1_funct_1(C_367))), inference(cnfTransformation, [status(thm)], [f_272])).
% 20.49/11.47  tff(c_5028, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_partfun1('#skF_1') | k1_xboole_0='#skF_2' | ~v2_funct_1('#skF_3') | k2_relset_1('#skF_1', '#skF_2', '#skF_3')!='#skF_2' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_120, c_5010])).
% 20.49/11.47  tff(c_5042, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_partfun1('#skF_1') | k1_xboole_0='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_124, c_122, c_112, c_108, c_5028])).
% 20.49/11.47  tff(c_5043, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_partfun1('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_104, c_5042])).
% 20.49/11.47  tff(c_442, plain, (k2_relat_1(k2_funct_1('#skF_3'))=k1_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_438, c_24])).
% 20.49/11.47  tff(c_455, plain, (k2_relat_1(k2_funct_1('#skF_3'))=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_318, c_442])).
% 20.49/11.47  tff(c_589, plain, (![A_120, B_121]: (r1_tarski(k2_relat_1(k5_relat_1(A_120, B_121)), k2_relat_1(B_121)) | ~v1_relat_1(B_121) | ~v1_relat_1(A_120))), inference(cnfTransformation, [status(thm)], [f_73])).
% 20.49/11.47  tff(c_606, plain, (![A_120]: (r1_tarski(k2_relat_1(k5_relat_1(A_120, k2_funct_1('#skF_3'))), k1_relat_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v1_relat_1(A_120))), inference(superposition, [status(thm), theory('equality')], [c_455, c_589])).
% 20.49/11.47  tff(c_629, plain, (![A_120]: (r1_tarski(k2_relat_1(k5_relat_1(A_120, k2_funct_1('#skF_3'))), k1_relat_1('#skF_3')) | ~v1_relat_1(A_120))), inference(demodulation, [status(thm), theory('equality')], [c_461, c_606])).
% 20.49/11.47  tff(c_5056, plain, (r1_tarski(k2_relat_1(k6_partfun1('#skF_1')), k1_relat_1('#skF_3')) | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_5043, c_629])).
% 20.49/11.47  tff(c_5065, plain, (r1_tarski('#skF_1', k1_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_318, c_131, c_5056])).
% 20.49/11.47  tff(c_5067, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3863, c_5065])).
% 20.49/11.47  tff(c_5068, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(splitRight, [status(thm)], [c_1420])).
% 20.49/11.47  tff(c_5081, plain, (k2_relat_1(k2_funct_1('#skF_3'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_5068, c_455])).
% 20.49/11.47  tff(c_36, plain, (![A_22]: (k4_relat_1(k6_relat_1(A_22))=k6_relat_1(A_22))), inference(cnfTransformation, [status(thm)], [f_86])).
% 20.49/11.47  tff(c_130, plain, (![A_22]: (k4_relat_1(k6_partfun1(A_22))=k6_partfun1(A_22))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_80, c_36])).
% 20.49/11.47  tff(c_14124, plain, (![E_789, D_790, A_791, B_786, C_788, F_787]: (k1_partfun1(A_791, B_786, C_788, D_790, E_789, F_787)=k5_relat_1(E_789, F_787) | ~m1_subset_1(F_787, k1_zfmisc_1(k2_zfmisc_1(C_788, D_790))) | ~v1_funct_1(F_787) | ~m1_subset_1(E_789, k1_zfmisc_1(k2_zfmisc_1(A_791, B_786))) | ~v1_funct_1(E_789))), inference(cnfTransformation, [status(thm)], [f_195])).
% 20.49/11.47  tff(c_14136, plain, (![A_791, B_786, E_789]: (k1_partfun1(A_791, B_786, '#skF_2', '#skF_1', E_789, '#skF_4')=k5_relat_1(E_789, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_789, k1_zfmisc_1(k2_zfmisc_1(A_791, B_786))) | ~v1_funct_1(E_789))), inference(resolution, [status(thm)], [c_114, c_14124])).
% 20.49/11.47  tff(c_14539, plain, (![A_805, B_806, E_807]: (k1_partfun1(A_805, B_806, '#skF_2', '#skF_1', E_807, '#skF_4')=k5_relat_1(E_807, '#skF_4') | ~m1_subset_1(E_807, k1_zfmisc_1(k2_zfmisc_1(A_805, B_806))) | ~v1_funct_1(E_807))), inference(demodulation, [status(thm), theory('equality')], [c_118, c_14136])).
% 20.49/11.47  tff(c_14556, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_120, c_14539])).
% 20.49/11.48  tff(c_14566, plain, (k5_relat_1('#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_124, c_3846, c_14556])).
% 20.49/11.48  tff(c_853, plain, (![B_138, A_139]: (k5_relat_1(k4_relat_1(B_138), k4_relat_1(A_139))=k4_relat_1(k5_relat_1(A_139, B_138)) | ~v1_relat_1(B_138) | ~v1_relat_1(A_139))), inference(cnfTransformation, [status(thm)], [f_80])).
% 20.49/11.48  tff(c_874, plain, (![B_138]: (k5_relat_1(k4_relat_1(B_138), k2_funct_1('#skF_3'))=k4_relat_1(k5_relat_1('#skF_3', B_138)) | ~v1_relat_1(B_138) | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_438, c_853])).
% 20.49/11.48  tff(c_896, plain, (![B_138]: (k5_relat_1(k4_relat_1(B_138), k2_funct_1('#skF_3'))=k4_relat_1(k5_relat_1('#skF_3', B_138)) | ~v1_relat_1(B_138))), inference(demodulation, [status(thm), theory('equality')], [c_318, c_874])).
% 20.49/11.48  tff(c_10932, plain, (k5_relat_1(k2_funct_1('#skF_4'), k2_funct_1('#skF_3'))=k4_relat_1(k5_relat_1('#skF_3', '#skF_4')) | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_10928, c_896])).
% 20.49/11.48  tff(c_10957, plain, (k5_relat_1(k2_funct_1('#skF_4'), k2_funct_1('#skF_3'))=k4_relat_1(k5_relat_1('#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_321, c_10932])).
% 20.49/11.48  tff(c_14571, plain, (k5_relat_1(k2_funct_1('#skF_4'), k2_funct_1('#skF_3'))=k4_relat_1(k6_partfun1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_14566, c_10957])).
% 20.49/11.48  tff(c_14573, plain, (k5_relat_1(k2_funct_1('#skF_4'), k2_funct_1('#skF_3'))=k6_partfun1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_130, c_14571])).
% 20.49/11.48  tff(c_58, plain, (![A_31, B_33]: (k2_funct_1(A_31)=B_33 | k6_relat_1(k2_relat_1(A_31))!=k5_relat_1(B_33, A_31) | k2_relat_1(B_33)!=k1_relat_1(A_31) | ~v2_funct_1(A_31) | ~v1_funct_1(B_33) | ~v1_relat_1(B_33) | ~v1_funct_1(A_31) | ~v1_relat_1(A_31))), inference(cnfTransformation, [status(thm)], [f_149])).
% 20.49/11.48  tff(c_125, plain, (![A_31, B_33]: (k2_funct_1(A_31)=B_33 | k6_partfun1(k2_relat_1(A_31))!=k5_relat_1(B_33, A_31) | k2_relat_1(B_33)!=k1_relat_1(A_31) | ~v2_funct_1(A_31) | ~v1_funct_1(B_33) | ~v1_relat_1(B_33) | ~v1_funct_1(A_31) | ~v1_relat_1(A_31))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_58])).
% 20.49/11.48  tff(c_14590, plain, (k2_funct_1(k2_funct_1('#skF_3'))=k2_funct_1('#skF_4') | k6_partfun1(k2_relat_1(k2_funct_1('#skF_3')))!=k6_partfun1('#skF_1') | k2_relat_1(k2_funct_1('#skF_4'))!=k1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1(k2_funct_1('#skF_3')) | ~v1_funct_1(k2_funct_1('#skF_4')) | ~v1_relat_1(k2_funct_1('#skF_4')) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_14573, c_125])).
% 20.49/11.48  tff(c_14597, plain, (k2_funct_1(k2_funct_1('#skF_3'))=k2_funct_1('#skF_4') | ~v2_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_461, c_5191, c_10971, c_12729, c_13931, c_764, c_5081, c_14590])).
% 20.49/11.48  tff(c_14601, plain, (~v2_funct_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_14597])).
% 20.49/11.48  tff(c_13076, plain, (![C_729, B_730, A_731]: (v1_funct_2(k2_funct_1(C_729), B_730, A_731) | k2_relset_1(A_731, B_730, C_729)!=B_730 | ~v2_funct_1(C_729) | ~m1_subset_1(C_729, k1_zfmisc_1(k2_zfmisc_1(A_731, B_730))) | ~v1_funct_2(C_729, A_731, B_730) | ~v1_funct_1(C_729))), inference(cnfTransformation, [status(thm)], [f_256])).
% 20.49/11.48  tff(c_13090, plain, (v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | k2_relset_1('#skF_1', '#skF_2', '#skF_3')!='#skF_2' | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_120, c_13076])).
% 20.49/11.48  tff(c_13101, plain, (v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_124, c_122, c_108, c_112, c_13090])).
% 20.49/11.48  tff(c_14236, plain, (![C_793, B_794, A_795]: (m1_subset_1(k2_funct_1(C_793), k1_zfmisc_1(k2_zfmisc_1(B_794, A_795))) | k2_relset_1(A_795, B_794, C_793)!=B_794 | ~v2_funct_1(C_793) | ~m1_subset_1(C_793, k1_zfmisc_1(k2_zfmisc_1(A_795, B_794))) | ~v1_funct_2(C_793, A_795, B_794) | ~v1_funct_1(C_793))), inference(cnfTransformation, [status(thm)], [f_256])).
% 20.49/11.48  tff(c_62, plain, (![A_38, B_39, C_40]: (k2_relset_1(A_38, B_39, C_40)=k2_relat_1(C_40) | ~m1_subset_1(C_40, k1_zfmisc_1(k2_zfmisc_1(A_38, B_39))))), inference(cnfTransformation, [status(thm)], [f_157])).
% 20.49/11.48  tff(c_47978, plain, (![B_1578, A_1579, C_1580]: (k2_relset_1(B_1578, A_1579, k2_funct_1(C_1580))=k2_relat_1(k2_funct_1(C_1580)) | k2_relset_1(A_1579, B_1578, C_1580)!=B_1578 | ~v2_funct_1(C_1580) | ~m1_subset_1(C_1580, k1_zfmisc_1(k2_zfmisc_1(A_1579, B_1578))) | ~v1_funct_2(C_1580, A_1579, B_1578) | ~v1_funct_1(C_1580))), inference(resolution, [status(thm)], [c_14236, c_62])).
% 20.49/11.48  tff(c_48039, plain, (k2_relset_1('#skF_2', '#skF_1', k2_funct_1('#skF_3'))=k2_relat_1(k2_funct_1('#skF_3')) | k2_relset_1('#skF_1', '#skF_2', '#skF_3')!='#skF_2' | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_120, c_47978])).
% 20.49/11.48  tff(c_48079, plain, (k2_relset_1('#skF_2', '#skF_1', k2_funct_1('#skF_3'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_124, c_122, c_108, c_112, c_5081, c_48039])).
% 20.49/11.48  tff(c_14437, plain, (![B_802, C_803, A_804]: (k6_partfun1(B_802)=k5_relat_1(k2_funct_1(C_803), C_803) | k1_xboole_0=B_802 | ~v2_funct_1(C_803) | k2_relset_1(A_804, B_802, C_803)!=B_802 | ~m1_subset_1(C_803, k1_zfmisc_1(k2_zfmisc_1(A_804, B_802))) | ~v1_funct_2(C_803, A_804, B_802) | ~v1_funct_1(C_803))), inference(cnfTransformation, [status(thm)], [f_272])).
% 20.49/11.48  tff(c_14449, plain, (k5_relat_1(k2_funct_1('#skF_3'), '#skF_3')=k6_partfun1('#skF_2') | k1_xboole_0='#skF_2' | ~v2_funct_1('#skF_3') | k2_relset_1('#skF_1', '#skF_2', '#skF_3')!='#skF_2' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_120, c_14437])).
% 20.49/11.48  tff(c_14460, plain, (k5_relat_1(k2_funct_1('#skF_3'), '#skF_3')=k6_partfun1('#skF_2') | k1_xboole_0='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_124, c_122, c_112, c_108, c_14449])).
% 20.49/11.48  tff(c_14461, plain, (k5_relat_1(k2_funct_1('#skF_3'), '#skF_3')=k6_partfun1('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_104, c_14460])).
% 20.49/11.48  tff(c_14274, plain, (![C_793, B_794, A_795]: (r1_tarski(k2_funct_1(C_793), k2_zfmisc_1(B_794, A_795)) | k2_relset_1(A_795, B_794, C_793)!=B_794 | ~v2_funct_1(C_793) | ~m1_subset_1(C_793, k1_zfmisc_1(k2_zfmisc_1(A_795, B_794))) | ~v1_funct_2(C_793, A_795, B_794) | ~v1_funct_1(C_793))), inference(resolution, [status(thm)], [c_14236, c_8])).
% 20.49/11.48  tff(c_64, plain, (![A_41, B_42, C_43, D_44]: (k8_relset_1(A_41, B_42, C_43, D_44)=k10_relat_1(C_43, D_44) | ~m1_subset_1(C_43, k1_zfmisc_1(k2_zfmisc_1(A_41, B_42))))), inference(cnfTransformation, [status(thm)], [f_161])).
% 20.49/11.48  tff(c_48391, plain, (![B_1588, A_1589, C_1590, D_1591]: (k8_relset_1(B_1588, A_1589, k2_funct_1(C_1590), D_1591)=k10_relat_1(k2_funct_1(C_1590), D_1591) | k2_relset_1(A_1589, B_1588, C_1590)!=B_1588 | ~v2_funct_1(C_1590) | ~m1_subset_1(C_1590, k1_zfmisc_1(k2_zfmisc_1(A_1589, B_1588))) | ~v1_funct_2(C_1590, A_1589, B_1588) | ~v1_funct_1(C_1590))), inference(resolution, [status(thm)], [c_14236, c_64])).
% 20.49/11.48  tff(c_48436, plain, (![D_1591]: (k8_relset_1('#skF_2', '#skF_1', k2_funct_1('#skF_3'), D_1591)=k10_relat_1(k2_funct_1('#skF_3'), D_1591) | k2_relset_1('#skF_1', '#skF_2', '#skF_3')!='#skF_2' | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_120, c_48391])).
% 20.49/11.48  tff(c_48482, plain, (![D_1592]: (k8_relset_1('#skF_2', '#skF_1', k2_funct_1('#skF_3'), D_1592)=k10_relat_1(k2_funct_1('#skF_3'), D_1592))), inference(demodulation, [status(thm), theory('equality')], [c_124, c_122, c_108, c_112, c_48436])).
% 20.49/11.48  tff(c_10, plain, (![A_3, B_4]: (m1_subset_1(A_3, k1_zfmisc_1(B_4)) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 20.49/11.48  tff(c_1174, plain, (![A_149, B_150, C_151, D_152]: (m1_subset_1(k8_relset_1(A_149, B_150, C_151, D_152), k1_zfmisc_1(A_149)) | ~m1_subset_1(C_151, k1_zfmisc_1(k2_zfmisc_1(A_149, B_150))))), inference(cnfTransformation, [status(thm)], [f_153])).
% 20.49/11.48  tff(c_30476, plain, (![A_1193, B_1194, C_1195, D_1196]: (r1_tarski(k8_relset_1(A_1193, B_1194, C_1195, D_1196), A_1193) | ~m1_subset_1(C_1195, k1_zfmisc_1(k2_zfmisc_1(A_1193, B_1194))))), inference(resolution, [status(thm)], [c_1174, c_8])).
% 20.49/11.48  tff(c_30515, plain, (![A_1193, B_1194, A_3, D_1196]: (r1_tarski(k8_relset_1(A_1193, B_1194, A_3, D_1196), A_1193) | ~r1_tarski(A_3, k2_zfmisc_1(A_1193, B_1194)))), inference(resolution, [status(thm)], [c_10, c_30476])).
% 20.49/11.48  tff(c_48488, plain, (![D_1592]: (r1_tarski(k10_relat_1(k2_funct_1('#skF_3'), D_1592), '#skF_2') | ~r1_tarski(k2_funct_1('#skF_3'), k2_zfmisc_1('#skF_2', '#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_48482, c_30515])).
% 20.49/11.48  tff(c_48512, plain, (~r1_tarski(k2_funct_1('#skF_3'), k2_zfmisc_1('#skF_2', '#skF_1'))), inference(splitLeft, [status(thm)], [c_48488])).
% 20.49/11.48  tff(c_48515, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')!='#skF_2' | ~v2_funct_1('#skF_3') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_14274, c_48512])).
% 20.49/11.48  tff(c_48519, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_124, c_122, c_120, c_108, c_112, c_48515])).
% 20.49/11.48  tff(c_48521, plain, (r1_tarski(k2_funct_1('#skF_3'), k2_zfmisc_1('#skF_2', '#skF_1'))), inference(splitRight, [status(thm)], [c_48488])).
% 20.49/11.48  tff(c_14134, plain, (![A_791, B_786, E_789]: (k1_partfun1(A_791, B_786, '#skF_1', '#skF_2', E_789, '#skF_3')=k5_relat_1(E_789, '#skF_3') | ~v1_funct_1('#skF_3') | ~m1_subset_1(E_789, k1_zfmisc_1(k2_zfmisc_1(A_791, B_786))) | ~v1_funct_1(E_789))), inference(resolution, [status(thm)], [c_120, c_14124])).
% 20.49/11.48  tff(c_14978, plain, (![A_827, B_828, E_829]: (k1_partfun1(A_827, B_828, '#skF_1', '#skF_2', E_829, '#skF_3')=k5_relat_1(E_829, '#skF_3') | ~m1_subset_1(E_829, k1_zfmisc_1(k2_zfmisc_1(A_827, B_828))) | ~v1_funct_1(E_829))), inference(demodulation, [status(thm), theory('equality')], [c_124, c_14134])).
% 20.49/11.48  tff(c_15016, plain, (![A_827, B_828, A_3]: (k1_partfun1(A_827, B_828, '#skF_1', '#skF_2', A_3, '#skF_3')=k5_relat_1(A_3, '#skF_3') | ~v1_funct_1(A_3) | ~r1_tarski(A_3, k2_zfmisc_1(A_827, B_828)))), inference(resolution, [status(thm)], [c_10, c_14978])).
% 20.49/11.48  tff(c_48577, plain, (k1_partfun1('#skF_2', '#skF_1', '#skF_1', '#skF_2', k2_funct_1('#skF_3'), '#skF_3')=k5_relat_1(k2_funct_1('#skF_3'), '#skF_3') | ~v1_funct_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_48521, c_15016])).
% 20.49/11.48  tff(c_48629, plain, (k1_partfun1('#skF_2', '#skF_1', '#skF_1', '#skF_2', k2_funct_1('#skF_3'), '#skF_3')=k6_partfun1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_5191, c_14461, c_48577])).
% 20.49/11.48  tff(c_90, plain, (![C_70, E_73, B_69, D_71, A_68]: (k1_xboole_0=C_70 | v2_funct_1(D_71) | k2_relset_1(A_68, B_69, D_71)!=B_69 | ~v2_funct_1(k1_partfun1(A_68, B_69, B_69, C_70, D_71, E_73)) | ~m1_subset_1(E_73, k1_zfmisc_1(k2_zfmisc_1(B_69, C_70))) | ~v1_funct_2(E_73, B_69, C_70) | ~v1_funct_1(E_73) | ~m1_subset_1(D_71, k1_zfmisc_1(k2_zfmisc_1(A_68, B_69))) | ~v1_funct_2(D_71, A_68, B_69) | ~v1_funct_1(D_71))), inference(cnfTransformation, [status(thm)], [f_240])).
% 20.49/11.48  tff(c_48800, plain, (k1_xboole_0='#skF_2' | v2_funct_1(k2_funct_1('#skF_3')) | k2_relset_1('#skF_2', '#skF_1', k2_funct_1('#skF_3'))!='#skF_1' | ~v2_funct_1(k6_partfun1('#skF_2')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3') | ~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | ~v1_funct_1(k2_funct_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_48629, c_90])).
% 20.49/11.48  tff(c_48814, plain, (k1_xboole_0='#skF_2' | v2_funct_1(k2_funct_1('#skF_3')) | ~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_5191, c_13101, c_124, c_122, c_120, c_126, c_48079, c_48800])).
% 20.49/11.48  tff(c_48815, plain, (~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(negUnitSimplification, [status(thm)], [c_14601, c_104, c_48814])).
% 20.49/11.48  tff(c_48826, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')!='#skF_2' | ~v2_funct_1('#skF_3') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_92, c_48815])).
% 20.49/11.48  tff(c_48833, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_124, c_122, c_120, c_108, c_112, c_48826])).
% 20.49/11.48  tff(c_48835, plain, (v2_funct_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_14597])).
% 20.49/11.48  tff(c_48838, plain, (k4_relat_1(k2_funct_1('#skF_3'))=k2_funct_1(k2_funct_1('#skF_3')) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_48835, c_42])).
% 20.49/11.48  tff(c_48841, plain, (k2_funct_1(k2_funct_1('#skF_3'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_461, c_5191, c_459, c_48838])).
% 20.49/11.48  tff(c_48834, plain, (k2_funct_1(k2_funct_1('#skF_3'))=k2_funct_1('#skF_4')), inference(splitRight, [status(thm)], [c_14597])).
% 20.49/11.48  tff(c_48876, plain, (k2_funct_1('#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_48841, c_48834])).
% 20.49/11.48  tff(c_10950, plain, (k4_relat_1(k2_funct_1('#skF_4'))='#skF_4' | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_10928, c_18])).
% 20.49/11.48  tff(c_10969, plain, (k4_relat_1(k2_funct_1('#skF_4'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_321, c_10950])).
% 20.49/11.48  tff(c_48889, plain, (k4_relat_1('#skF_3')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_48876, c_10969])).
% 20.49/11.48  tff(c_48938, plain, (k2_funct_1('#skF_3')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_48889, c_438])).
% 20.49/11.48  tff(c_48940, plain, $false, inference(negUnitSimplification, [status(thm)], [c_102, c_48938])).
% 20.49/11.48  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 20.49/11.48  
% 20.49/11.48  Inference rules
% 20.49/11.48  ----------------------
% 20.49/11.48  #Ref     : 0
% 20.49/11.48  #Sup     : 11088
% 20.49/11.48  #Fact    : 0
% 20.49/11.48  #Define  : 0
% 20.49/11.48  #Split   : 106
% 20.49/11.48  #Chain   : 0
% 20.49/11.48  #Close   : 0
% 20.49/11.48  
% 20.49/11.48  Ordering : KBO
% 20.49/11.48  
% 20.49/11.48  Simplification rules
% 20.49/11.48  ----------------------
% 20.49/11.48  #Subsume      : 1362
% 20.49/11.48  #Demod        : 20091
% 20.49/11.48  #Tautology    : 3893
% 20.49/11.48  #SimpNegUnit  : 312
% 20.49/11.48  #BackRed      : 134
% 20.49/11.48  
% 20.49/11.48  #Partial instantiations: 0
% 20.49/11.48  #Strategies tried      : 1
% 20.49/11.48  
% 20.49/11.48  Timing (in seconds)
% 20.49/11.48  ----------------------
% 20.49/11.48  Preprocessing        : 0.44
% 20.49/11.48  Parsing              : 0.23
% 20.49/11.48  CNF conversion       : 0.03
% 20.49/11.48  Main loop            : 10.23
% 20.49/11.48  Inferencing          : 2.16
% 20.49/11.48  Reduction            : 5.29
% 20.49/11.48  Demodulation         : 4.46
% 20.49/11.48  BG Simplification    : 0.22
% 20.49/11.48  Subsumption          : 2.04
% 20.49/11.48  Abstraction          : 0.33
% 20.49/11.48  MUC search           : 0.00
% 20.49/11.48  Cooper               : 0.00
% 20.49/11.48  Total                : 10.75
% 20.49/11.48  Index Insertion      : 0.00
% 20.49/11.48  Index Deletion       : 0.00
% 20.49/11.48  Index Matching       : 0.00
% 20.49/11.48  BG Taut test         : 0.00
%------------------------------------------------------------------------------
