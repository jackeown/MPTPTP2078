%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:15:37 EST 2020

% Result     : Theorem 5.35s
% Output     : CNFRefutation 5.60s
% Verified   : 
% Statistics : Number of formulae       :  143 ( 528 expanded)
%              Number of leaves         :   49 ( 204 expanded)
%              Depth                    :   13
%              Number of atoms          :  266 (1650 expanded)
%              Number of equality atoms :   68 ( 303 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k7_relset_1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k5_relat_1 > k2_zfmisc_1 > k11_relat_1 > k10_relat_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_1 > #skF_2 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_relset_1,type,(
    r2_relset_1: ( $i * $i * $i * $i ) > $o )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

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

tff(k11_relat_1,type,(
    k11_relat_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

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

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_176,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_funct_1(B)
          & v1_funct_2(B,A,A)
          & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
       => ! [C] :
            ( ( v1_funct_1(C)
              & v1_funct_2(C,A,A)
              & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
           => ( ( r2_relset_1(A,A,k1_partfun1(A,A,A,A,B,C),B)
                & k2_relset_1(A,A,B) = A )
             => r2_relset_1(A,A,C,k6_partfun1(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_funct_2)).

tff(f_98,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_78,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_86,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_82,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_156,axiom,(
    ! [A,B] :
      ( ( v1_funct_1(B)
        & v1_funct_2(B,A,A)
        & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
     => k1_relset_1(A,A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_funct_2)).

tff(f_48,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k2_relat_1(k5_relat_1(A,B)) = k9_relat_1(B,k2_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t160_relat_1)).

tff(f_90,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_148,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => r1_tarski(k7_relset_1(A,B,D,C),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_funct_2)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_52,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k10_relat_1(A,k2_relat_1(A)) = k1_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_relat_1)).

tff(f_59,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k1_relat_1(k5_relat_1(A,B)) = k10_relat_1(A,k1_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t182_relat_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(A)
        & v1_relat_1(B) )
     => v1_relat_1(k5_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_relat_1)).

tff(f_41,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k9_relat_1(A,k1_relat_1(A)) = k2_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_relat_1)).

tff(f_114,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( ( r1_tarski(k1_relat_1(C),A)
          & r1_tarski(k2_relat_1(C),B) )
       => m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_relset_1)).

tff(f_138,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_140,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_74,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( ( v1_relat_1(B)
            & v1_funct_1(B) )
         => ( ( k2_relat_1(A) = k1_relat_1(B)
              & k5_relat_1(A,B) = A )
           => B = k6_relat_1(k1_relat_1(B)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_funct_1)).

tff(f_116,axiom,(
    ! [A] : m1_subset_1(k6_relat_1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_relset_1)).

tff(f_128,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A)))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,A)))
         => ( ! [D] :
                ( r2_hidden(D,A)
               => k11_relat_1(B,D) = k11_relat_1(C,D) )
           => r2_relset_1(A,A,B,C) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t54_relset_1)).

tff(f_106,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
       => r2_relset_1(A,B,D,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r2_relset_1)).

tff(c_56,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_176])).

tff(c_125,plain,(
    ! [A_75,B_76,D_77] :
      ( r2_relset_1(A_75,B_76,D_77,D_77)
      | ~ m1_subset_1(D_77,k1_zfmisc_1(k2_zfmisc_1(A_75,B_76))) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_134,plain,(
    r2_relset_1('#skF_2','#skF_2','#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_56,c_125])).

tff(c_62,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_176])).

tff(c_102,plain,(
    ! [C_70,A_71,B_72] :
      ( v1_relat_1(C_70)
      | ~ m1_subset_1(C_70,k1_zfmisc_1(k2_zfmisc_1(A_71,B_72))) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_113,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_62,c_102])).

tff(c_66,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_176])).

tff(c_114,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_56,c_102])).

tff(c_60,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_176])).

tff(c_52,plain,(
    k2_relset_1('#skF_2','#skF_2','#skF_3') = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_176])).

tff(c_175,plain,(
    ! [A_85,B_86,C_87] :
      ( k2_relset_1(A_85,B_86,C_87) = k2_relat_1(C_87)
      | ~ m1_subset_1(C_87,k1_zfmisc_1(k2_zfmisc_1(A_85,B_86))) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_181,plain,(
    k2_relset_1('#skF_2','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_62,c_175])).

tff(c_187,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_181])).

tff(c_58,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_176])).

tff(c_145,plain,(
    ! [A_81,B_82,C_83] :
      ( k1_relset_1(A_81,B_82,C_83) = k1_relat_1(C_83)
      | ~ m1_subset_1(C_83,k1_zfmisc_1(k2_zfmisc_1(A_81,B_82))) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_157,plain,(
    k1_relset_1('#skF_2','#skF_2','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_56,c_145])).

tff(c_326,plain,(
    ! [A_110,B_111] :
      ( k1_relset_1(A_110,A_110,B_111) = A_110
      | ~ m1_subset_1(B_111,k1_zfmisc_1(k2_zfmisc_1(A_110,A_110)))
      | ~ v1_funct_2(B_111,A_110,A_110)
      | ~ v1_funct_1(B_111) ) ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_339,plain,
    ( k1_relset_1('#skF_2','#skF_2','#skF_4') = '#skF_2'
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_56,c_326])).

tff(c_348,plain,(
    k1_relat_1('#skF_4') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_157,c_339])).

tff(c_12,plain,(
    ! [B_8,A_6] :
      ( k9_relat_1(B_8,k2_relat_1(A_6)) = k2_relat_1(k5_relat_1(A_6,B_8))
      | ~ v1_relat_1(B_8)
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_244,plain,(
    ! [A_92,B_93,C_94,D_95] :
      ( k7_relset_1(A_92,B_93,C_94,D_95) = k9_relat_1(C_94,D_95)
      | ~ m1_subset_1(C_94,k1_zfmisc_1(k2_zfmisc_1(A_92,B_93))) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_253,plain,(
    ! [D_95] : k7_relset_1('#skF_2','#skF_2','#skF_4',D_95) = k9_relat_1('#skF_4',D_95) ),
    inference(resolution,[status(thm)],[c_56,c_244])).

tff(c_510,plain,(
    ! [A_125,B_126,D_127,C_128] :
      ( r1_tarski(k7_relset_1(A_125,B_126,D_127,C_128),B_126)
      | ~ m1_subset_1(D_127,k1_zfmisc_1(k2_zfmisc_1(A_125,B_126)))
      | ~ v1_funct_2(D_127,A_125,B_126)
      | ~ v1_funct_1(D_127) ) ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_518,plain,(
    ! [C_128] :
      ( r1_tarski(k7_relset_1('#skF_2','#skF_2','#skF_4',C_128),'#skF_2')
      | ~ v1_funct_2('#skF_4','#skF_2','#skF_2')
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_56,c_510])).

tff(c_547,plain,(
    ! [C_130] : r1_tarski(k9_relat_1('#skF_4',C_130),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_253,c_518])).

tff(c_555,plain,(
    ! [A_6] :
      ( r1_tarski(k2_relat_1(k5_relat_1(A_6,'#skF_4')),'#skF_2')
      | ~ v1_relat_1('#skF_4')
      | ~ v1_relat_1(A_6) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_547])).

tff(c_562,plain,(
    ! [A_6] :
      ( r1_tarski(k2_relat_1(k5_relat_1(A_6,'#skF_4')),'#skF_2')
      | ~ v1_relat_1(A_6) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_114,c_555])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_64,plain,(
    v1_funct_2('#skF_3','#skF_2','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_176])).

tff(c_156,plain,(
    k1_relset_1('#skF_2','#skF_2','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_62,c_145])).

tff(c_336,plain,
    ( k1_relset_1('#skF_2','#skF_2','#skF_3') = '#skF_2'
    | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_62,c_326])).

tff(c_345,plain,(
    k1_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_156,c_336])).

tff(c_14,plain,(
    ! [A_9] :
      ( k10_relat_1(A_9,k2_relat_1(A_9)) = k1_relat_1(A_9)
      | ~ v1_relat_1(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_195,plain,
    ( k10_relat_1('#skF_3','#skF_2') = k1_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_187,c_14])).

tff(c_201,plain,(
    k10_relat_1('#skF_3','#skF_2') = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_113,c_195])).

tff(c_351,plain,(
    k10_relat_1('#skF_3','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_345,c_201])).

tff(c_16,plain,(
    ! [A_10,B_12] :
      ( k10_relat_1(A_10,k1_relat_1(B_12)) = k1_relat_1(k5_relat_1(A_10,B_12))
      | ~ v1_relat_1(B_12)
      | ~ v1_relat_1(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_371,plain,(
    ! [A_10] :
      ( k1_relat_1(k5_relat_1(A_10,'#skF_4')) = k10_relat_1(A_10,'#skF_2')
      | ~ v1_relat_1('#skF_4')
      | ~ v1_relat_1(A_10) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_348,c_16])).

tff(c_378,plain,(
    ! [A_10] :
      ( k1_relat_1(k5_relat_1(A_10,'#skF_4')) = k10_relat_1(A_10,'#skF_2')
      | ~ v1_relat_1(A_10) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_114,c_371])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( v1_relat_1(k5_relat_1(A_3,B_4))
      | ~ v1_relat_1(B_4)
      | ~ v1_relat_1(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_456,plain,(
    ! [A_118] :
      ( k1_relat_1(k5_relat_1(A_118,'#skF_4')) = k10_relat_1(A_118,'#skF_2')
      | ~ v1_relat_1(A_118) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_114,c_371])).

tff(c_10,plain,(
    ! [A_5] :
      ( k9_relat_1(A_5,k1_relat_1(A_5)) = k2_relat_1(A_5)
      | ~ v1_relat_1(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_1395,plain,(
    ! [A_193] :
      ( k9_relat_1(k5_relat_1(A_193,'#skF_4'),k10_relat_1(A_193,'#skF_2')) = k2_relat_1(k5_relat_1(A_193,'#skF_4'))
      | ~ v1_relat_1(k5_relat_1(A_193,'#skF_4'))
      | ~ v1_relat_1(A_193) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_456,c_10])).

tff(c_1407,plain,
    ( k9_relat_1(k5_relat_1('#skF_3','#skF_4'),'#skF_2') = k2_relat_1(k5_relat_1('#skF_3','#skF_4'))
    | ~ v1_relat_1(k5_relat_1('#skF_3','#skF_4'))
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_351,c_1395])).

tff(c_1413,plain,
    ( k9_relat_1(k5_relat_1('#skF_3','#skF_4'),'#skF_2') = k2_relat_1(k5_relat_1('#skF_3','#skF_4'))
    | ~ v1_relat_1(k5_relat_1('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_113,c_1407])).

tff(c_1510,plain,(
    ~ v1_relat_1(k5_relat_1('#skF_3','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_1413])).

tff(c_1513,plain,
    ( ~ v1_relat_1('#skF_4')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_8,c_1510])).

tff(c_1517,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_113,c_114,c_1513])).

tff(c_1519,plain,(
    v1_relat_1(k5_relat_1('#skF_3','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_1413])).

tff(c_34,plain,(
    ! [C_39,A_37,B_38] :
      ( m1_subset_1(C_39,k1_zfmisc_1(k2_zfmisc_1(A_37,B_38)))
      | ~ r1_tarski(k2_relat_1(C_39),B_38)
      | ~ r1_tarski(k1_relat_1(C_39),A_37)
      | ~ v1_relat_1(C_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_1640,plain,(
    ! [E_206,B_203,F_201,C_205,A_204,D_202] :
      ( k1_partfun1(A_204,B_203,C_205,D_202,E_206,F_201) = k5_relat_1(E_206,F_201)
      | ~ m1_subset_1(F_201,k1_zfmisc_1(k2_zfmisc_1(C_205,D_202)))
      | ~ v1_funct_1(F_201)
      | ~ m1_subset_1(E_206,k1_zfmisc_1(k2_zfmisc_1(A_204,B_203)))
      | ~ v1_funct_1(E_206) ) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_1648,plain,(
    ! [A_204,B_203,E_206] :
      ( k1_partfun1(A_204,B_203,'#skF_2','#skF_2',E_206,'#skF_4') = k5_relat_1(E_206,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_206,k1_zfmisc_1(k2_zfmisc_1(A_204,B_203)))
      | ~ v1_funct_1(E_206) ) ),
    inference(resolution,[status(thm)],[c_56,c_1640])).

tff(c_1879,plain,(
    ! [A_227,B_228,E_229] :
      ( k1_partfun1(A_227,B_228,'#skF_2','#skF_2',E_229,'#skF_4') = k5_relat_1(E_229,'#skF_4')
      | ~ m1_subset_1(E_229,k1_zfmisc_1(k2_zfmisc_1(A_227,B_228)))
      | ~ v1_funct_1(E_229) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_1648])).

tff(c_1888,plain,
    ( k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_62,c_1879])).

tff(c_1896,plain,(
    k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_1888])).

tff(c_54,plain,(
    r2_relset_1('#skF_2','#skF_2',k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2','#skF_3','#skF_4'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_176])).

tff(c_428,plain,(
    ! [D_114,C_115,A_116,B_117] :
      ( D_114 = C_115
      | ~ r2_relset_1(A_116,B_117,C_115,D_114)
      | ~ m1_subset_1(D_114,k1_zfmisc_1(k2_zfmisc_1(A_116,B_117)))
      | ~ m1_subset_1(C_115,k1_zfmisc_1(k2_zfmisc_1(A_116,B_117))) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_438,plain,
    ( k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2','#skF_3','#skF_4') = '#skF_3'
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2')))
    | ~ m1_subset_1(k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(resolution,[status(thm)],[c_54,c_428])).

tff(c_455,plain,
    ( k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2','#skF_3','#skF_4') = '#skF_3'
    | ~ m1_subset_1(k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_438])).

tff(c_477,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_455])).

tff(c_1901,plain,(
    ~ m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1896,c_477])).

tff(c_1920,plain,
    ( ~ r1_tarski(k2_relat_1(k5_relat_1('#skF_3','#skF_4')),'#skF_2')
    | ~ r1_tarski(k1_relat_1(k5_relat_1('#skF_3','#skF_4')),'#skF_2')
    | ~ v1_relat_1(k5_relat_1('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_34,c_1901])).

tff(c_1923,plain,
    ( ~ r1_tarski(k2_relat_1(k5_relat_1('#skF_3','#skF_4')),'#skF_2')
    | ~ r1_tarski(k1_relat_1(k5_relat_1('#skF_3','#skF_4')),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1519,c_1920])).

tff(c_1977,plain,(
    ~ r1_tarski(k1_relat_1(k5_relat_1('#skF_3','#skF_4')),'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_1923])).

tff(c_1980,plain,
    ( ~ r1_tarski(k10_relat_1('#skF_3','#skF_2'),'#skF_2')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_378,c_1977])).

tff(c_1983,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_113,c_6,c_351,c_1980])).

tff(c_1984,plain,(
    ~ r1_tarski(k2_relat_1(k5_relat_1('#skF_3','#skF_4')),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_1923])).

tff(c_1996,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_562,c_1984])).

tff(c_2003,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_113,c_1996])).

tff(c_2004,plain,(
    k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2','#skF_3','#skF_4') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_455])).

tff(c_2416,plain,(
    ! [A_274,C_275,E_276,F_271,D_272,B_273] :
      ( k1_partfun1(A_274,B_273,C_275,D_272,E_276,F_271) = k5_relat_1(E_276,F_271)
      | ~ m1_subset_1(F_271,k1_zfmisc_1(k2_zfmisc_1(C_275,D_272)))
      | ~ v1_funct_1(F_271)
      | ~ m1_subset_1(E_276,k1_zfmisc_1(k2_zfmisc_1(A_274,B_273)))
      | ~ v1_funct_1(E_276) ) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_2424,plain,(
    ! [A_274,B_273,E_276] :
      ( k1_partfun1(A_274,B_273,'#skF_2','#skF_2',E_276,'#skF_4') = k5_relat_1(E_276,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_276,k1_zfmisc_1(k2_zfmisc_1(A_274,B_273)))
      | ~ v1_funct_1(E_276) ) ),
    inference(resolution,[status(thm)],[c_56,c_2416])).

tff(c_3087,plain,(
    ! [A_315,B_316,E_317] :
      ( k1_partfun1(A_315,B_316,'#skF_2','#skF_2',E_317,'#skF_4') = k5_relat_1(E_317,'#skF_4')
      | ~ m1_subset_1(E_317,k1_zfmisc_1(k2_zfmisc_1(A_315,B_316)))
      | ~ v1_funct_1(E_317) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_2424])).

tff(c_3096,plain,
    ( k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_62,c_3087])).

tff(c_3104,plain,(
    k5_relat_1('#skF_3','#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_2004,c_3096])).

tff(c_44,plain,(
    ! [A_54] : k6_relat_1(A_54) = k6_partfun1(A_54) ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_18,plain,(
    ! [B_15,A_13] :
      ( k6_relat_1(k1_relat_1(B_15)) = B_15
      | k5_relat_1(A_13,B_15) != A_13
      | k2_relat_1(A_13) != k1_relat_1(B_15)
      | ~ v1_funct_1(B_15)
      | ~ v1_relat_1(B_15)
      | ~ v1_funct_1(A_13)
      | ~ v1_relat_1(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_68,plain,(
    ! [B_15,A_13] :
      ( k6_partfun1(k1_relat_1(B_15)) = B_15
      | k5_relat_1(A_13,B_15) != A_13
      | k2_relat_1(A_13) != k1_relat_1(B_15)
      | ~ v1_funct_1(B_15)
      | ~ v1_relat_1(B_15)
      | ~ v1_funct_1(A_13)
      | ~ v1_relat_1(A_13) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_18])).

tff(c_3125,plain,
    ( k6_partfun1(k1_relat_1('#skF_4')) = '#skF_4'
    | k2_relat_1('#skF_3') != k1_relat_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_3104,c_68])).

tff(c_3151,plain,(
    k6_partfun1('#skF_2') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_113,c_66,c_114,c_60,c_187,c_348,c_348,c_3125])).

tff(c_50,plain,(
    ~ r2_relset_1('#skF_2','#skF_2','#skF_4',k6_partfun1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_176])).

tff(c_36,plain,(
    ! [A_40] : m1_subset_1(k6_relat_1(A_40),k1_zfmisc_1(k2_zfmisc_1(A_40,A_40))) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_67,plain,(
    ! [A_40] : m1_subset_1(k6_partfun1(A_40),k1_zfmisc_1(k2_zfmisc_1(A_40,A_40))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_36])).

tff(c_2305,plain,(
    ! [A_265,B_266,C_267] :
      ( r2_hidden('#skF_1'(A_265,B_266,C_267),A_265)
      | r2_relset_1(A_265,A_265,B_266,C_267)
      | ~ m1_subset_1(C_267,k1_zfmisc_1(k2_zfmisc_1(A_265,A_265)))
      | ~ m1_subset_1(B_266,k1_zfmisc_1(k2_zfmisc_1(A_265,A_265))) ) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_2974,plain,(
    ! [B_303] :
      ( r2_hidden('#skF_1'('#skF_2',B_303,'#skF_4'),'#skF_2')
      | r2_relset_1('#skF_2','#skF_2',B_303,'#skF_4')
      | ~ m1_subset_1(B_303,k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ) ),
    inference(resolution,[status(thm)],[c_56,c_2305])).

tff(c_2990,plain,
    ( r2_hidden('#skF_1'('#skF_2',k6_partfun1('#skF_2'),'#skF_4'),'#skF_2')
    | r2_relset_1('#skF_2','#skF_2',k6_partfun1('#skF_2'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_67,c_2974])).

tff(c_3063,plain,(
    r2_relset_1('#skF_2','#skF_2',k6_partfun1('#skF_2'),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_2990])).

tff(c_32,plain,(
    ! [A_33,B_34,D_36,C_35] :
      ( r2_relset_1(A_33,B_34,D_36,C_35)
      | ~ r2_relset_1(A_33,B_34,C_35,D_36)
      | ~ m1_subset_1(D_36,k1_zfmisc_1(k2_zfmisc_1(A_33,B_34)))
      | ~ m1_subset_1(C_35,k1_zfmisc_1(k2_zfmisc_1(A_33,B_34))) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_3065,plain,
    ( r2_relset_1('#skF_2','#skF_2','#skF_4',k6_partfun1('#skF_2'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2')))
    | ~ m1_subset_1(k6_partfun1('#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(resolution,[status(thm)],[c_3063,c_32])).

tff(c_3070,plain,(
    r2_relset_1('#skF_2','#skF_2','#skF_4',k6_partfun1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_67,c_56,c_3065])).

tff(c_3072,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_3070])).

tff(c_3074,plain,(
    ~ r2_relset_1('#skF_2','#skF_2',k6_partfun1('#skF_2'),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_2990])).

tff(c_3164,plain,(
    ~ r2_relset_1('#skF_2','#skF_2','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3151,c_3074])).

tff(c_3170,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_134,c_3164])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 20:09:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.35/2.01  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.35/2.03  
% 5.35/2.03  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.35/2.03  %$ r2_relset_1 > v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k7_relset_1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k5_relat_1 > k2_zfmisc_1 > k11_relat_1 > k10_relat_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_1 > #skF_2 > #skF_3 > #skF_4
% 5.35/2.03  
% 5.35/2.03  %Foreground sorts:
% 5.35/2.03  
% 5.35/2.03  
% 5.35/2.03  %Background operators:
% 5.35/2.03  
% 5.35/2.03  
% 5.35/2.03  %Foreground operators:
% 5.35/2.03  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 5.35/2.03  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 5.35/2.03  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 5.35/2.03  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.35/2.03  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 5.35/2.03  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.35/2.03  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 5.35/2.03  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.35/2.03  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 5.35/2.03  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 5.35/2.03  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 5.35/2.03  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 5.35/2.03  tff(k11_relat_1, type, k11_relat_1: ($i * $i) > $i).
% 5.35/2.03  tff('#skF_2', type, '#skF_2': $i).
% 5.35/2.03  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 5.35/2.03  tff('#skF_3', type, '#skF_3': $i).
% 5.35/2.03  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 5.35/2.03  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.35/2.03  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 5.35/2.03  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.35/2.03  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 5.35/2.03  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.35/2.03  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 5.35/2.03  tff('#skF_4', type, '#skF_4': $i).
% 5.35/2.03  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 5.35/2.03  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.35/2.03  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 5.35/2.03  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.35/2.03  
% 5.60/2.05  tff(f_176, negated_conjecture, ~(![A, B]: (((v1_funct_1(B) & v1_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, A, A)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => ((r2_relset_1(A, A, k1_partfun1(A, A, A, A, B, C), B) & (k2_relset_1(A, A, B) = A)) => r2_relset_1(A, A, C, k6_partfun1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t75_funct_2)).
% 5.60/2.05  tff(f_98, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 5.60/2.05  tff(f_78, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 5.60/2.05  tff(f_86, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 5.60/2.05  tff(f_82, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 5.60/2.05  tff(f_156, axiom, (![A, B]: (((v1_funct_1(B) & v1_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (k1_relset_1(A, A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t67_funct_2)).
% 5.60/2.05  tff(f_48, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k2_relat_1(k5_relat_1(A, B)) = k9_relat_1(B, k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t160_relat_1)).
% 5.60/2.05  tff(f_90, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 5.60/2.05  tff(f_148, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => r1_tarski(k7_relset_1(A, B, D, C), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_funct_2)).
% 5.60/2.05  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 5.60/2.05  tff(f_52, axiom, (![A]: (v1_relat_1(A) => (k10_relat_1(A, k2_relat_1(A)) = k1_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t169_relat_1)).
% 5.60/2.05  tff(f_59, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k1_relat_1(k5_relat_1(A, B)) = k10_relat_1(A, k1_relat_1(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t182_relat_1)).
% 5.60/2.05  tff(f_37, axiom, (![A, B]: ((v1_relat_1(A) & v1_relat_1(B)) => v1_relat_1(k5_relat_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k5_relat_1)).
% 5.60/2.05  tff(f_41, axiom, (![A]: (v1_relat_1(A) => (k9_relat_1(A, k1_relat_1(A)) = k2_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t146_relat_1)).
% 5.60/2.05  tff(f_114, axiom, (![A, B, C]: (v1_relat_1(C) => ((r1_tarski(k1_relat_1(C), A) & r1_tarski(k2_relat_1(C), B)) => m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_relset_1)).
% 5.60/2.05  tff(f_138, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 5.60/2.05  tff(f_140, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 5.60/2.05  tff(f_74, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (((k2_relat_1(A) = k1_relat_1(B)) & (k5_relat_1(A, B) = A)) => (B = k6_relat_1(k1_relat_1(B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_funct_1)).
% 5.60/2.05  tff(f_116, axiom, (![A]: m1_subset_1(k6_relat_1(A), k1_zfmisc_1(k2_zfmisc_1(A, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_relset_1)).
% 5.60/2.05  tff(f_128, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, A))) => ((![D]: (r2_hidden(D, A) => (k11_relat_1(B, D) = k11_relat_1(C, D)))) => r2_relset_1(A, A, B, C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t54_relset_1)).
% 5.60/2.05  tff(f_106, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) => r2_relset_1(A, B, D, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', symmetry_r2_relset_1)).
% 5.60/2.05  tff(c_56, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_176])).
% 5.60/2.05  tff(c_125, plain, (![A_75, B_76, D_77]: (r2_relset_1(A_75, B_76, D_77, D_77) | ~m1_subset_1(D_77, k1_zfmisc_1(k2_zfmisc_1(A_75, B_76))))), inference(cnfTransformation, [status(thm)], [f_98])).
% 5.60/2.05  tff(c_134, plain, (r2_relset_1('#skF_2', '#skF_2', '#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_56, c_125])).
% 5.60/2.05  tff(c_62, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_176])).
% 5.60/2.05  tff(c_102, plain, (![C_70, A_71, B_72]: (v1_relat_1(C_70) | ~m1_subset_1(C_70, k1_zfmisc_1(k2_zfmisc_1(A_71, B_72))))), inference(cnfTransformation, [status(thm)], [f_78])).
% 5.60/2.05  tff(c_113, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_62, c_102])).
% 5.60/2.05  tff(c_66, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_176])).
% 5.60/2.05  tff(c_114, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_56, c_102])).
% 5.60/2.05  tff(c_60, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_176])).
% 5.60/2.05  tff(c_52, plain, (k2_relset_1('#skF_2', '#skF_2', '#skF_3')='#skF_2'), inference(cnfTransformation, [status(thm)], [f_176])).
% 5.60/2.05  tff(c_175, plain, (![A_85, B_86, C_87]: (k2_relset_1(A_85, B_86, C_87)=k2_relat_1(C_87) | ~m1_subset_1(C_87, k1_zfmisc_1(k2_zfmisc_1(A_85, B_86))))), inference(cnfTransformation, [status(thm)], [f_86])).
% 5.60/2.05  tff(c_181, plain, (k2_relset_1('#skF_2', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_62, c_175])).
% 5.60/2.05  tff(c_187, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_52, c_181])).
% 5.60/2.05  tff(c_58, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_176])).
% 5.60/2.05  tff(c_145, plain, (![A_81, B_82, C_83]: (k1_relset_1(A_81, B_82, C_83)=k1_relat_1(C_83) | ~m1_subset_1(C_83, k1_zfmisc_1(k2_zfmisc_1(A_81, B_82))))), inference(cnfTransformation, [status(thm)], [f_82])).
% 5.60/2.05  tff(c_157, plain, (k1_relset_1('#skF_2', '#skF_2', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_56, c_145])).
% 5.60/2.05  tff(c_326, plain, (![A_110, B_111]: (k1_relset_1(A_110, A_110, B_111)=A_110 | ~m1_subset_1(B_111, k1_zfmisc_1(k2_zfmisc_1(A_110, A_110))) | ~v1_funct_2(B_111, A_110, A_110) | ~v1_funct_1(B_111))), inference(cnfTransformation, [status(thm)], [f_156])).
% 5.60/2.05  tff(c_339, plain, (k1_relset_1('#skF_2', '#skF_2', '#skF_4')='#skF_2' | ~v1_funct_2('#skF_4', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_56, c_326])).
% 5.60/2.05  tff(c_348, plain, (k1_relat_1('#skF_4')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_157, c_339])).
% 5.60/2.05  tff(c_12, plain, (![B_8, A_6]: (k9_relat_1(B_8, k2_relat_1(A_6))=k2_relat_1(k5_relat_1(A_6, B_8)) | ~v1_relat_1(B_8) | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_48])).
% 5.60/2.05  tff(c_244, plain, (![A_92, B_93, C_94, D_95]: (k7_relset_1(A_92, B_93, C_94, D_95)=k9_relat_1(C_94, D_95) | ~m1_subset_1(C_94, k1_zfmisc_1(k2_zfmisc_1(A_92, B_93))))), inference(cnfTransformation, [status(thm)], [f_90])).
% 5.60/2.05  tff(c_253, plain, (![D_95]: (k7_relset_1('#skF_2', '#skF_2', '#skF_4', D_95)=k9_relat_1('#skF_4', D_95))), inference(resolution, [status(thm)], [c_56, c_244])).
% 5.60/2.05  tff(c_510, plain, (![A_125, B_126, D_127, C_128]: (r1_tarski(k7_relset_1(A_125, B_126, D_127, C_128), B_126) | ~m1_subset_1(D_127, k1_zfmisc_1(k2_zfmisc_1(A_125, B_126))) | ~v1_funct_2(D_127, A_125, B_126) | ~v1_funct_1(D_127))), inference(cnfTransformation, [status(thm)], [f_148])).
% 5.60/2.05  tff(c_518, plain, (![C_128]: (r1_tarski(k7_relset_1('#skF_2', '#skF_2', '#skF_4', C_128), '#skF_2') | ~v1_funct_2('#skF_4', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_56, c_510])).
% 5.60/2.05  tff(c_547, plain, (![C_130]: (r1_tarski(k9_relat_1('#skF_4', C_130), '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_253, c_518])).
% 5.60/2.05  tff(c_555, plain, (![A_6]: (r1_tarski(k2_relat_1(k5_relat_1(A_6, '#skF_4')), '#skF_2') | ~v1_relat_1('#skF_4') | ~v1_relat_1(A_6))), inference(superposition, [status(thm), theory('equality')], [c_12, c_547])).
% 5.60/2.05  tff(c_562, plain, (![A_6]: (r1_tarski(k2_relat_1(k5_relat_1(A_6, '#skF_4')), '#skF_2') | ~v1_relat_1(A_6))), inference(demodulation, [status(thm), theory('equality')], [c_114, c_555])).
% 5.60/2.05  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.60/2.05  tff(c_64, plain, (v1_funct_2('#skF_3', '#skF_2', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_176])).
% 5.60/2.05  tff(c_156, plain, (k1_relset_1('#skF_2', '#skF_2', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_62, c_145])).
% 5.60/2.05  tff(c_336, plain, (k1_relset_1('#skF_2', '#skF_2', '#skF_3')='#skF_2' | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_62, c_326])).
% 5.60/2.05  tff(c_345, plain, (k1_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_156, c_336])).
% 5.60/2.05  tff(c_14, plain, (![A_9]: (k10_relat_1(A_9, k2_relat_1(A_9))=k1_relat_1(A_9) | ~v1_relat_1(A_9))), inference(cnfTransformation, [status(thm)], [f_52])).
% 5.60/2.05  tff(c_195, plain, (k10_relat_1('#skF_3', '#skF_2')=k1_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_187, c_14])).
% 5.60/2.05  tff(c_201, plain, (k10_relat_1('#skF_3', '#skF_2')=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_113, c_195])).
% 5.60/2.05  tff(c_351, plain, (k10_relat_1('#skF_3', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_345, c_201])).
% 5.60/2.05  tff(c_16, plain, (![A_10, B_12]: (k10_relat_1(A_10, k1_relat_1(B_12))=k1_relat_1(k5_relat_1(A_10, B_12)) | ~v1_relat_1(B_12) | ~v1_relat_1(A_10))), inference(cnfTransformation, [status(thm)], [f_59])).
% 5.60/2.05  tff(c_371, plain, (![A_10]: (k1_relat_1(k5_relat_1(A_10, '#skF_4'))=k10_relat_1(A_10, '#skF_2') | ~v1_relat_1('#skF_4') | ~v1_relat_1(A_10))), inference(superposition, [status(thm), theory('equality')], [c_348, c_16])).
% 5.60/2.05  tff(c_378, plain, (![A_10]: (k1_relat_1(k5_relat_1(A_10, '#skF_4'))=k10_relat_1(A_10, '#skF_2') | ~v1_relat_1(A_10))), inference(demodulation, [status(thm), theory('equality')], [c_114, c_371])).
% 5.60/2.05  tff(c_8, plain, (![A_3, B_4]: (v1_relat_1(k5_relat_1(A_3, B_4)) | ~v1_relat_1(B_4) | ~v1_relat_1(A_3))), inference(cnfTransformation, [status(thm)], [f_37])).
% 5.60/2.05  tff(c_456, plain, (![A_118]: (k1_relat_1(k5_relat_1(A_118, '#skF_4'))=k10_relat_1(A_118, '#skF_2') | ~v1_relat_1(A_118))), inference(demodulation, [status(thm), theory('equality')], [c_114, c_371])).
% 5.60/2.05  tff(c_10, plain, (![A_5]: (k9_relat_1(A_5, k1_relat_1(A_5))=k2_relat_1(A_5) | ~v1_relat_1(A_5))), inference(cnfTransformation, [status(thm)], [f_41])).
% 5.60/2.05  tff(c_1395, plain, (![A_193]: (k9_relat_1(k5_relat_1(A_193, '#skF_4'), k10_relat_1(A_193, '#skF_2'))=k2_relat_1(k5_relat_1(A_193, '#skF_4')) | ~v1_relat_1(k5_relat_1(A_193, '#skF_4')) | ~v1_relat_1(A_193))), inference(superposition, [status(thm), theory('equality')], [c_456, c_10])).
% 5.60/2.05  tff(c_1407, plain, (k9_relat_1(k5_relat_1('#skF_3', '#skF_4'), '#skF_2')=k2_relat_1(k5_relat_1('#skF_3', '#skF_4')) | ~v1_relat_1(k5_relat_1('#skF_3', '#skF_4')) | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_351, c_1395])).
% 5.60/2.05  tff(c_1413, plain, (k9_relat_1(k5_relat_1('#skF_3', '#skF_4'), '#skF_2')=k2_relat_1(k5_relat_1('#skF_3', '#skF_4')) | ~v1_relat_1(k5_relat_1('#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_113, c_1407])).
% 5.60/2.05  tff(c_1510, plain, (~v1_relat_1(k5_relat_1('#skF_3', '#skF_4'))), inference(splitLeft, [status(thm)], [c_1413])).
% 5.60/2.05  tff(c_1513, plain, (~v1_relat_1('#skF_4') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_8, c_1510])).
% 5.60/2.05  tff(c_1517, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_113, c_114, c_1513])).
% 5.60/2.05  tff(c_1519, plain, (v1_relat_1(k5_relat_1('#skF_3', '#skF_4'))), inference(splitRight, [status(thm)], [c_1413])).
% 5.60/2.05  tff(c_34, plain, (![C_39, A_37, B_38]: (m1_subset_1(C_39, k1_zfmisc_1(k2_zfmisc_1(A_37, B_38))) | ~r1_tarski(k2_relat_1(C_39), B_38) | ~r1_tarski(k1_relat_1(C_39), A_37) | ~v1_relat_1(C_39))), inference(cnfTransformation, [status(thm)], [f_114])).
% 5.60/2.05  tff(c_1640, plain, (![E_206, B_203, F_201, C_205, A_204, D_202]: (k1_partfun1(A_204, B_203, C_205, D_202, E_206, F_201)=k5_relat_1(E_206, F_201) | ~m1_subset_1(F_201, k1_zfmisc_1(k2_zfmisc_1(C_205, D_202))) | ~v1_funct_1(F_201) | ~m1_subset_1(E_206, k1_zfmisc_1(k2_zfmisc_1(A_204, B_203))) | ~v1_funct_1(E_206))), inference(cnfTransformation, [status(thm)], [f_138])).
% 5.60/2.05  tff(c_1648, plain, (![A_204, B_203, E_206]: (k1_partfun1(A_204, B_203, '#skF_2', '#skF_2', E_206, '#skF_4')=k5_relat_1(E_206, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_206, k1_zfmisc_1(k2_zfmisc_1(A_204, B_203))) | ~v1_funct_1(E_206))), inference(resolution, [status(thm)], [c_56, c_1640])).
% 5.60/2.05  tff(c_1879, plain, (![A_227, B_228, E_229]: (k1_partfun1(A_227, B_228, '#skF_2', '#skF_2', E_229, '#skF_4')=k5_relat_1(E_229, '#skF_4') | ~m1_subset_1(E_229, k1_zfmisc_1(k2_zfmisc_1(A_227, B_228))) | ~v1_funct_1(E_229))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_1648])).
% 5.60/2.05  tff(c_1888, plain, (k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_62, c_1879])).
% 5.60/2.05  tff(c_1896, plain, (k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_1888])).
% 5.60/2.05  tff(c_54, plain, (r2_relset_1('#skF_2', '#skF_2', k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', '#skF_3', '#skF_4'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_176])).
% 5.60/2.05  tff(c_428, plain, (![D_114, C_115, A_116, B_117]: (D_114=C_115 | ~r2_relset_1(A_116, B_117, C_115, D_114) | ~m1_subset_1(D_114, k1_zfmisc_1(k2_zfmisc_1(A_116, B_117))) | ~m1_subset_1(C_115, k1_zfmisc_1(k2_zfmisc_1(A_116, B_117))))), inference(cnfTransformation, [status(thm)], [f_98])).
% 5.60/2.05  tff(c_438, plain, (k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', '#skF_3', '#skF_4')='#skF_3' | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'))) | ~m1_subset_1(k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(resolution, [status(thm)], [c_54, c_428])).
% 5.60/2.05  tff(c_455, plain, (k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', '#skF_3', '#skF_4')='#skF_3' | ~m1_subset_1(k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_438])).
% 5.60/2.05  tff(c_477, plain, (~m1_subset_1(k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(splitLeft, [status(thm)], [c_455])).
% 5.60/2.05  tff(c_1901, plain, (~m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_1896, c_477])).
% 5.60/2.05  tff(c_1920, plain, (~r1_tarski(k2_relat_1(k5_relat_1('#skF_3', '#skF_4')), '#skF_2') | ~r1_tarski(k1_relat_1(k5_relat_1('#skF_3', '#skF_4')), '#skF_2') | ~v1_relat_1(k5_relat_1('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_34, c_1901])).
% 5.60/2.05  tff(c_1923, plain, (~r1_tarski(k2_relat_1(k5_relat_1('#skF_3', '#skF_4')), '#skF_2') | ~r1_tarski(k1_relat_1(k5_relat_1('#skF_3', '#skF_4')), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1519, c_1920])).
% 5.60/2.05  tff(c_1977, plain, (~r1_tarski(k1_relat_1(k5_relat_1('#skF_3', '#skF_4')), '#skF_2')), inference(splitLeft, [status(thm)], [c_1923])).
% 5.60/2.05  tff(c_1980, plain, (~r1_tarski(k10_relat_1('#skF_3', '#skF_2'), '#skF_2') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_378, c_1977])).
% 5.60/2.05  tff(c_1983, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_113, c_6, c_351, c_1980])).
% 5.60/2.05  tff(c_1984, plain, (~r1_tarski(k2_relat_1(k5_relat_1('#skF_3', '#skF_4')), '#skF_2')), inference(splitRight, [status(thm)], [c_1923])).
% 5.60/2.05  tff(c_1996, plain, (~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_562, c_1984])).
% 5.60/2.05  tff(c_2003, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_113, c_1996])).
% 5.60/2.05  tff(c_2004, plain, (k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', '#skF_3', '#skF_4')='#skF_3'), inference(splitRight, [status(thm)], [c_455])).
% 5.60/2.05  tff(c_2416, plain, (![A_274, C_275, E_276, F_271, D_272, B_273]: (k1_partfun1(A_274, B_273, C_275, D_272, E_276, F_271)=k5_relat_1(E_276, F_271) | ~m1_subset_1(F_271, k1_zfmisc_1(k2_zfmisc_1(C_275, D_272))) | ~v1_funct_1(F_271) | ~m1_subset_1(E_276, k1_zfmisc_1(k2_zfmisc_1(A_274, B_273))) | ~v1_funct_1(E_276))), inference(cnfTransformation, [status(thm)], [f_138])).
% 5.60/2.05  tff(c_2424, plain, (![A_274, B_273, E_276]: (k1_partfun1(A_274, B_273, '#skF_2', '#skF_2', E_276, '#skF_4')=k5_relat_1(E_276, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_276, k1_zfmisc_1(k2_zfmisc_1(A_274, B_273))) | ~v1_funct_1(E_276))), inference(resolution, [status(thm)], [c_56, c_2416])).
% 5.60/2.05  tff(c_3087, plain, (![A_315, B_316, E_317]: (k1_partfun1(A_315, B_316, '#skF_2', '#skF_2', E_317, '#skF_4')=k5_relat_1(E_317, '#skF_4') | ~m1_subset_1(E_317, k1_zfmisc_1(k2_zfmisc_1(A_315, B_316))) | ~v1_funct_1(E_317))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_2424])).
% 5.60/2.05  tff(c_3096, plain, (k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_62, c_3087])).
% 5.60/2.05  tff(c_3104, plain, (k5_relat_1('#skF_3', '#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_66, c_2004, c_3096])).
% 5.60/2.05  tff(c_44, plain, (![A_54]: (k6_relat_1(A_54)=k6_partfun1(A_54))), inference(cnfTransformation, [status(thm)], [f_140])).
% 5.60/2.05  tff(c_18, plain, (![B_15, A_13]: (k6_relat_1(k1_relat_1(B_15))=B_15 | k5_relat_1(A_13, B_15)!=A_13 | k2_relat_1(A_13)!=k1_relat_1(B_15) | ~v1_funct_1(B_15) | ~v1_relat_1(B_15) | ~v1_funct_1(A_13) | ~v1_relat_1(A_13))), inference(cnfTransformation, [status(thm)], [f_74])).
% 5.60/2.05  tff(c_68, plain, (![B_15, A_13]: (k6_partfun1(k1_relat_1(B_15))=B_15 | k5_relat_1(A_13, B_15)!=A_13 | k2_relat_1(A_13)!=k1_relat_1(B_15) | ~v1_funct_1(B_15) | ~v1_relat_1(B_15) | ~v1_funct_1(A_13) | ~v1_relat_1(A_13))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_18])).
% 5.60/2.05  tff(c_3125, plain, (k6_partfun1(k1_relat_1('#skF_4'))='#skF_4' | k2_relat_1('#skF_3')!=k1_relat_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_3104, c_68])).
% 5.60/2.05  tff(c_3151, plain, (k6_partfun1('#skF_2')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_113, c_66, c_114, c_60, c_187, c_348, c_348, c_3125])).
% 5.60/2.05  tff(c_50, plain, (~r2_relset_1('#skF_2', '#skF_2', '#skF_4', k6_partfun1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_176])).
% 5.60/2.05  tff(c_36, plain, (![A_40]: (m1_subset_1(k6_relat_1(A_40), k1_zfmisc_1(k2_zfmisc_1(A_40, A_40))))), inference(cnfTransformation, [status(thm)], [f_116])).
% 5.60/2.05  tff(c_67, plain, (![A_40]: (m1_subset_1(k6_partfun1(A_40), k1_zfmisc_1(k2_zfmisc_1(A_40, A_40))))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_36])).
% 5.60/2.05  tff(c_2305, plain, (![A_265, B_266, C_267]: (r2_hidden('#skF_1'(A_265, B_266, C_267), A_265) | r2_relset_1(A_265, A_265, B_266, C_267) | ~m1_subset_1(C_267, k1_zfmisc_1(k2_zfmisc_1(A_265, A_265))) | ~m1_subset_1(B_266, k1_zfmisc_1(k2_zfmisc_1(A_265, A_265))))), inference(cnfTransformation, [status(thm)], [f_128])).
% 5.60/2.05  tff(c_2974, plain, (![B_303]: (r2_hidden('#skF_1'('#skF_2', B_303, '#skF_4'), '#skF_2') | r2_relset_1('#skF_2', '#skF_2', B_303, '#skF_4') | ~m1_subset_1(B_303, k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'))))), inference(resolution, [status(thm)], [c_56, c_2305])).
% 5.60/2.05  tff(c_2990, plain, (r2_hidden('#skF_1'('#skF_2', k6_partfun1('#skF_2'), '#skF_4'), '#skF_2') | r2_relset_1('#skF_2', '#skF_2', k6_partfun1('#skF_2'), '#skF_4')), inference(resolution, [status(thm)], [c_67, c_2974])).
% 5.60/2.05  tff(c_3063, plain, (r2_relset_1('#skF_2', '#skF_2', k6_partfun1('#skF_2'), '#skF_4')), inference(splitLeft, [status(thm)], [c_2990])).
% 5.60/2.05  tff(c_32, plain, (![A_33, B_34, D_36, C_35]: (r2_relset_1(A_33, B_34, D_36, C_35) | ~r2_relset_1(A_33, B_34, C_35, D_36) | ~m1_subset_1(D_36, k1_zfmisc_1(k2_zfmisc_1(A_33, B_34))) | ~m1_subset_1(C_35, k1_zfmisc_1(k2_zfmisc_1(A_33, B_34))))), inference(cnfTransformation, [status(thm)], [f_106])).
% 5.60/2.05  tff(c_3065, plain, (r2_relset_1('#skF_2', '#skF_2', '#skF_4', k6_partfun1('#skF_2')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'))) | ~m1_subset_1(k6_partfun1('#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(resolution, [status(thm)], [c_3063, c_32])).
% 5.60/2.05  tff(c_3070, plain, (r2_relset_1('#skF_2', '#skF_2', '#skF_4', k6_partfun1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_67, c_56, c_3065])).
% 5.60/2.05  tff(c_3072, plain, $false, inference(negUnitSimplification, [status(thm)], [c_50, c_3070])).
% 5.60/2.05  tff(c_3074, plain, (~r2_relset_1('#skF_2', '#skF_2', k6_partfun1('#skF_2'), '#skF_4')), inference(splitRight, [status(thm)], [c_2990])).
% 5.60/2.05  tff(c_3164, plain, (~r2_relset_1('#skF_2', '#skF_2', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_3151, c_3074])).
% 5.60/2.05  tff(c_3170, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_134, c_3164])).
% 5.60/2.05  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.60/2.05  
% 5.60/2.05  Inference rules
% 5.60/2.05  ----------------------
% 5.60/2.05  #Ref     : 4
% 5.60/2.05  #Sup     : 658
% 5.60/2.05  #Fact    : 0
% 5.60/2.05  #Define  : 0
% 5.60/2.05  #Split   : 21
% 5.60/2.05  #Chain   : 0
% 5.60/2.05  #Close   : 0
% 5.60/2.05  
% 5.60/2.05  Ordering : KBO
% 5.60/2.05  
% 5.60/2.05  Simplification rules
% 5.60/2.05  ----------------------
% 5.60/2.05  #Subsume      : 65
% 5.60/2.05  #Demod        : 1069
% 5.60/2.05  #Tautology    : 336
% 5.60/2.05  #SimpNegUnit  : 8
% 5.60/2.05  #BackRed      : 188
% 5.60/2.05  
% 5.60/2.05  #Partial instantiations: 0
% 5.60/2.05  #Strategies tried      : 1
% 5.60/2.05  
% 5.60/2.05  Timing (in seconds)
% 5.60/2.05  ----------------------
% 5.60/2.06  Preprocessing        : 0.38
% 5.60/2.06  Parsing              : 0.20
% 5.60/2.06  CNF conversion       : 0.03
% 5.60/2.06  Main loop            : 0.88
% 5.60/2.06  Inferencing          : 0.28
% 5.60/2.06  Reduction            : 0.34
% 5.73/2.06  Demodulation         : 0.24
% 5.73/2.06  BG Simplification    : 0.04
% 5.73/2.06  Subsumption          : 0.16
% 5.73/2.06  Abstraction          : 0.04
% 5.73/2.06  MUC search           : 0.00
% 5.73/2.06  Cooper               : 0.00
% 5.73/2.06  Total                : 1.31
% 5.73/2.06  Index Insertion      : 0.00
% 5.73/2.06  Index Deletion       : 0.00
% 5.73/2.06  Index Matching       : 0.00
% 5.73/2.06  BG Taut test         : 0.00
%------------------------------------------------------------------------------
