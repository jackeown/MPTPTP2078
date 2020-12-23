%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:12:57 EST 2020

% Result     : Theorem 12.67s
% Output     : CNFRefutation 12.67s
% Verified   : 
% Statistics : Number of formulae       :  230 (1725 expanded)
%              Number of leaves         :   46 ( 634 expanded)
%              Depth                    :   18
%              Number of atoms          :  572 (7472 expanded)
%              Number of equality atoms :  172 (2394 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_245,negated_conjecture,(
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

tff(f_110,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_203,axiom,(
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

tff(f_144,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_52,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v2_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_funct_1)).

tff(f_142,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_120,axiom,(
    ! [A] : m1_subset_1(k6_relat_1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_relset_1)).

tff(f_118,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_132,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( v1_funct_1(k1_partfun1(A,B,C,D,E,F))
        & m1_subset_1(k1_partfun1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).

tff(f_187,axiom,(
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
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_106,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_48,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_44,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => r1_tarski(k2_relat_1(k5_relat_1(A,B)),k2_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_relat_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_96,axiom,(
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

tff(f_219,axiom,(
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

tff(f_79,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k2_relat_1(A) = k1_relat_1(k2_funct_1(A))
          & k1_relat_1(A) = k2_relat_1(k2_funct_1(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).

tff(c_74,plain,(
    k2_funct_1('#skF_3') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_245])).

tff(c_90,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_245])).

tff(c_88,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_245])).

tff(c_86,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_245])).

tff(c_299,plain,(
    ! [A_101,B_102,C_103] :
      ( k2_relset_1(A_101,B_102,C_103) = k2_relat_1(C_103)
      | ~ m1_subset_1(C_103,k1_zfmisc_1(k2_zfmisc_1(A_101,B_102))) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_313,plain,(
    k2_relset_1('#skF_2','#skF_1','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_86,c_299])).

tff(c_552,plain,(
    ! [C_133,A_134,B_135] :
      ( v1_funct_1(k2_funct_1(C_133))
      | k2_relset_1(A_134,B_135,C_133) != B_135
      | ~ v2_funct_1(C_133)
      | ~ m1_subset_1(C_133,k1_zfmisc_1(k2_zfmisc_1(A_134,B_135)))
      | ~ v1_funct_2(C_133,A_134,B_135)
      | ~ v1_funct_1(C_133) ) ),
    inference(cnfTransformation,[status(thm)],[f_203])).

tff(c_561,plain,
    ( v1_funct_1(k2_funct_1('#skF_4'))
    | k2_relset_1('#skF_2','#skF_1','#skF_4') != '#skF_1'
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_86,c_552])).

tff(c_570,plain,
    ( v1_funct_1(k2_funct_1('#skF_4'))
    | k2_relat_1('#skF_4') != '#skF_1'
    | ~ v2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_88,c_313,c_561])).

tff(c_571,plain,(
    ~ v2_funct_1('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_570])).

tff(c_78,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_245])).

tff(c_96,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_245])).

tff(c_94,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_245])).

tff(c_92,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_245])).

tff(c_52,plain,(
    ! [A_43] : k6_relat_1(A_43) = k6_partfun1(A_43) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_20,plain,(
    ! [A_9] : v2_funct_1(k6_relat_1(A_9)) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_99,plain,(
    ! [A_9] : v2_funct_1(k6_partfun1(A_9)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_20])).

tff(c_84,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_245])).

tff(c_1087,plain,(
    ! [F_192,A_190,B_191,C_195,D_193,E_194] :
      ( k1_partfun1(A_190,B_191,C_195,D_193,E_194,F_192) = k5_relat_1(E_194,F_192)
      | ~ m1_subset_1(F_192,k1_zfmisc_1(k2_zfmisc_1(C_195,D_193)))
      | ~ v1_funct_1(F_192)
      | ~ m1_subset_1(E_194,k1_zfmisc_1(k2_zfmisc_1(A_190,B_191)))
      | ~ v1_funct_1(E_194) ) ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_1095,plain,(
    ! [A_190,B_191,E_194] :
      ( k1_partfun1(A_190,B_191,'#skF_2','#skF_1',E_194,'#skF_4') = k5_relat_1(E_194,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_194,k1_zfmisc_1(k2_zfmisc_1(A_190,B_191)))
      | ~ v1_funct_1(E_194) ) ),
    inference(resolution,[status(thm)],[c_86,c_1087])).

tff(c_1136,plain,(
    ! [A_200,B_201,E_202] :
      ( k1_partfun1(A_200,B_201,'#skF_2','#skF_1',E_202,'#skF_4') = k5_relat_1(E_202,'#skF_4')
      | ~ m1_subset_1(E_202,k1_zfmisc_1(k2_zfmisc_1(A_200,B_201)))
      | ~ v1_funct_1(E_202) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_1095])).

tff(c_1145,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_92,c_1136])).

tff(c_1153,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_1145])).

tff(c_44,plain,(
    ! [A_30] : m1_subset_1(k6_relat_1(A_30),k1_zfmisc_1(k2_zfmisc_1(A_30,A_30))) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_97,plain,(
    ! [A_30] : m1_subset_1(k6_partfun1(A_30),k1_zfmisc_1(k2_zfmisc_1(A_30,A_30))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_44])).

tff(c_82,plain,(
    r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k6_partfun1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_245])).

tff(c_454,plain,(
    ! [D_121,C_122,A_123,B_124] :
      ( D_121 = C_122
      | ~ r2_relset_1(A_123,B_124,C_122,D_121)
      | ~ m1_subset_1(D_121,k1_zfmisc_1(k2_zfmisc_1(A_123,B_124)))
      | ~ m1_subset_1(C_122,k1_zfmisc_1(k2_zfmisc_1(A_123,B_124))) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_462,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_82,c_454])).

tff(c_477,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_97,c_462])).

tff(c_572,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_477])).

tff(c_1158,plain,(
    ~ m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1153,c_572])).

tff(c_1355,plain,(
    ! [C_228,D_223,F_227,B_224,A_226,E_225] :
      ( m1_subset_1(k1_partfun1(A_226,B_224,C_228,D_223,E_225,F_227),k1_zfmisc_1(k2_zfmisc_1(A_226,D_223)))
      | ~ m1_subset_1(F_227,k1_zfmisc_1(k2_zfmisc_1(C_228,D_223)))
      | ~ v1_funct_1(F_227)
      | ~ m1_subset_1(E_225,k1_zfmisc_1(k2_zfmisc_1(A_226,B_224)))
      | ~ v1_funct_1(E_225) ) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_1409,plain,
    ( m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1153,c_1355])).

tff(c_1437,plain,(
    m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_92,c_90,c_86,c_1409])).

tff(c_1439,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1158,c_1437])).

tff(c_1440,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_477])).

tff(c_2816,plain,(
    ! [A_337,E_334,D_338,B_336,C_335] :
      ( k1_xboole_0 = C_335
      | v2_funct_1(E_334)
      | k2_relset_1(A_337,B_336,D_338) != B_336
      | ~ v2_funct_1(k1_partfun1(A_337,B_336,B_336,C_335,D_338,E_334))
      | ~ m1_subset_1(E_334,k1_zfmisc_1(k2_zfmisc_1(B_336,C_335)))
      | ~ v1_funct_2(E_334,B_336,C_335)
      | ~ v1_funct_1(E_334)
      | ~ m1_subset_1(D_338,k1_zfmisc_1(k2_zfmisc_1(A_337,B_336)))
      | ~ v1_funct_2(D_338,A_337,B_336)
      | ~ v1_funct_1(D_338) ) ),
    inference(cnfTransformation,[status(thm)],[f_187])).

tff(c_2820,plain,
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
    inference(superposition,[status(thm),theory(equality)],[c_1440,c_2816])).

tff(c_2825,plain,
    ( k1_xboole_0 = '#skF_1'
    | v2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_94,c_92,c_90,c_88,c_86,c_99,c_84,c_2820])).

tff(c_2827,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_571,c_78,c_2825])).

tff(c_2828,plain,
    ( k2_relat_1('#skF_4') != '#skF_1'
    | v1_funct_1(k2_funct_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_570])).

tff(c_2830,plain,(
    k2_relat_1('#skF_4') != '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_2828])).

tff(c_146,plain,(
    ! [C_71,A_72,B_73] :
      ( v1_relat_1(C_71)
      | ~ m1_subset_1(C_71,k1_zfmisc_1(k2_zfmisc_1(A_72,B_73))) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_158,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_92,c_146])).

tff(c_159,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_86,c_146])).

tff(c_223,plain,(
    ! [C_88,B_89,A_90] :
      ( v5_relat_1(C_88,B_89)
      | ~ m1_subset_1(C_88,k1_zfmisc_1(k2_zfmisc_1(A_90,B_89))) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_236,plain,(
    v5_relat_1('#skF_4','#skF_1') ),
    inference(resolution,[status(thm)],[c_86,c_223])).

tff(c_16,plain,(
    ! [A_8] : k2_relat_1(k6_relat_1(A_8)) = A_8 ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_101,plain,(
    ! [A_8] : k2_relat_1(k6_partfun1(A_8)) = A_8 ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_16])).

tff(c_3346,plain,(
    ! [B_394,D_396,E_397,F_395,C_398,A_393] :
      ( k1_partfun1(A_393,B_394,C_398,D_396,E_397,F_395) = k5_relat_1(E_397,F_395)
      | ~ m1_subset_1(F_395,k1_zfmisc_1(k2_zfmisc_1(C_398,D_396)))
      | ~ v1_funct_1(F_395)
      | ~ m1_subset_1(E_397,k1_zfmisc_1(k2_zfmisc_1(A_393,B_394)))
      | ~ v1_funct_1(E_397) ) ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_3354,plain,(
    ! [A_393,B_394,E_397] :
      ( k1_partfun1(A_393,B_394,'#skF_2','#skF_1',E_397,'#skF_4') = k5_relat_1(E_397,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_397,k1_zfmisc_1(k2_zfmisc_1(A_393,B_394)))
      | ~ v1_funct_1(E_397) ) ),
    inference(resolution,[status(thm)],[c_86,c_3346])).

tff(c_3395,plain,(
    ! [A_403,B_404,E_405] :
      ( k1_partfun1(A_403,B_404,'#skF_2','#skF_1',E_405,'#skF_4') = k5_relat_1(E_405,'#skF_4')
      | ~ m1_subset_1(E_405,k1_zfmisc_1(k2_zfmisc_1(A_403,B_404)))
      | ~ v1_funct_1(E_405) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_3354])).

tff(c_3404,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_92,c_3395])).

tff(c_3412,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_3404])).

tff(c_2831,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_477])).

tff(c_3417,plain,(
    ~ m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3412,c_2831])).

tff(c_3614,plain,(
    ! [D_426,F_430,C_431,A_429,B_427,E_428] :
      ( m1_subset_1(k1_partfun1(A_429,B_427,C_431,D_426,E_428,F_430),k1_zfmisc_1(k2_zfmisc_1(A_429,D_426)))
      | ~ m1_subset_1(F_430,k1_zfmisc_1(k2_zfmisc_1(C_431,D_426)))
      | ~ v1_funct_1(F_430)
      | ~ m1_subset_1(E_428,k1_zfmisc_1(k2_zfmisc_1(A_429,B_427)))
      | ~ v1_funct_1(E_428) ) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_3668,plain,
    ( m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_3412,c_3614])).

tff(c_3696,plain,(
    m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_92,c_90,c_86,c_3668])).

tff(c_3698,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3417,c_3696])).

tff(c_3699,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_477])).

tff(c_4244,plain,(
    ! [F_492,B_491,D_493,E_494,C_495,A_490] :
      ( k1_partfun1(A_490,B_491,C_495,D_493,E_494,F_492) = k5_relat_1(E_494,F_492)
      | ~ m1_subset_1(F_492,k1_zfmisc_1(k2_zfmisc_1(C_495,D_493)))
      | ~ v1_funct_1(F_492)
      | ~ m1_subset_1(E_494,k1_zfmisc_1(k2_zfmisc_1(A_490,B_491)))
      | ~ v1_funct_1(E_494) ) ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_4252,plain,(
    ! [A_490,B_491,E_494] :
      ( k1_partfun1(A_490,B_491,'#skF_2','#skF_1',E_494,'#skF_4') = k5_relat_1(E_494,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_494,k1_zfmisc_1(k2_zfmisc_1(A_490,B_491)))
      | ~ v1_funct_1(E_494) ) ),
    inference(resolution,[status(thm)],[c_86,c_4244])).

tff(c_4374,plain,(
    ! [A_507,B_508,E_509] :
      ( k1_partfun1(A_507,B_508,'#skF_2','#skF_1',E_509,'#skF_4') = k5_relat_1(E_509,'#skF_4')
      | ~ m1_subset_1(E_509,k1_zfmisc_1(k2_zfmisc_1(A_507,B_508)))
      | ~ v1_funct_1(E_509) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_4252])).

tff(c_4383,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_92,c_4374])).

tff(c_4391,plain,(
    k5_relat_1('#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_3699,c_4383])).

tff(c_12,plain,(
    ! [A_5,B_7] :
      ( r1_tarski(k2_relat_1(k5_relat_1(A_5,B_7)),k2_relat_1(B_7))
      | ~ v1_relat_1(B_7)
      | ~ v1_relat_1(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_173,plain,(
    ! [B_77,A_78] :
      ( r1_tarski(k2_relat_1(B_77),A_78)
      | ~ v5_relat_1(B_77,A_78)
      | ~ v1_relat_1(B_77) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_379,plain,(
    ! [B_111,A_112] :
      ( k2_relat_1(B_111) = A_112
      | ~ r1_tarski(A_112,k2_relat_1(B_111))
      | ~ v5_relat_1(B_111,A_112)
      | ~ v1_relat_1(B_111) ) ),
    inference(resolution,[status(thm)],[c_173,c_2])).

tff(c_407,plain,(
    ! [A_5,B_7] :
      ( k2_relat_1(k5_relat_1(A_5,B_7)) = k2_relat_1(B_7)
      | ~ v5_relat_1(B_7,k2_relat_1(k5_relat_1(A_5,B_7)))
      | ~ v1_relat_1(B_7)
      | ~ v1_relat_1(A_5) ) ),
    inference(resolution,[status(thm)],[c_12,c_379])).

tff(c_4401,plain,
    ( k2_relat_1(k5_relat_1('#skF_3','#skF_4')) = k2_relat_1('#skF_4')
    | ~ v5_relat_1('#skF_4',k2_relat_1(k6_partfun1('#skF_1')))
    | ~ v1_relat_1('#skF_4')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_4391,c_407])).

tff(c_4420,plain,(
    k2_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_158,c_159,c_236,c_101,c_101,c_4391,c_4401])).

tff(c_4422,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2830,c_4420])).

tff(c_4424,plain,(
    k2_relat_1('#skF_4') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_2828])).

tff(c_80,plain,(
    v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_245])).

tff(c_305,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_92,c_299])).

tff(c_312,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_305])).

tff(c_30,plain,(
    ! [A_14,B_16] :
      ( k2_funct_1(A_14) = B_16
      | k6_relat_1(k2_relat_1(A_14)) != k5_relat_1(B_16,A_14)
      | k2_relat_1(B_16) != k1_relat_1(A_14)
      | ~ v2_funct_1(A_14)
      | ~ v1_funct_1(B_16)
      | ~ v1_relat_1(B_16)
      | ~ v1_funct_1(A_14)
      | ~ v1_relat_1(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_4475,plain,(
    ! [A_511,B_512] :
      ( k2_funct_1(A_511) = B_512
      | k6_partfun1(k2_relat_1(A_511)) != k5_relat_1(B_512,A_511)
      | k2_relat_1(B_512) != k1_relat_1(A_511)
      | ~ v2_funct_1(A_511)
      | ~ v1_funct_1(B_512)
      | ~ v1_relat_1(B_512)
      | ~ v1_funct_1(A_511)
      | ~ v1_relat_1(A_511) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_30])).

tff(c_4479,plain,(
    ! [B_512] :
      ( k2_funct_1('#skF_3') = B_512
      | k5_relat_1(B_512,'#skF_3') != k6_partfun1('#skF_2')
      | k2_relat_1(B_512) != k1_relat_1('#skF_3')
      | ~ v2_funct_1('#skF_3')
      | ~ v1_funct_1(B_512)
      | ~ v1_relat_1(B_512)
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_312,c_4475])).

tff(c_5488,plain,(
    ! [B_611] :
      ( k2_funct_1('#skF_3') = B_611
      | k5_relat_1(B_611,'#skF_3') != k6_partfun1('#skF_2')
      | k2_relat_1(B_611) != k1_relat_1('#skF_3')
      | ~ v1_funct_1(B_611)
      | ~ v1_relat_1(B_611) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_158,c_96,c_80,c_4479])).

tff(c_5491,plain,
    ( k2_funct_1('#skF_3') = '#skF_4'
    | k5_relat_1('#skF_4','#skF_3') != k6_partfun1('#skF_2')
    | k2_relat_1('#skF_4') != k1_relat_1('#skF_3')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_159,c_5488])).

tff(c_5500,plain,
    ( k2_funct_1('#skF_3') = '#skF_4'
    | k5_relat_1('#skF_4','#skF_3') != k6_partfun1('#skF_2')
    | k1_relat_1('#skF_3') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_4424,c_5491])).

tff(c_5501,plain,
    ( k5_relat_1('#skF_4','#skF_3') != k6_partfun1('#skF_2')
    | k1_relat_1('#skF_3') != '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_5500])).

tff(c_5507,plain,(
    k1_relat_1('#skF_3') != '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_5501])).

tff(c_76,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_245])).

tff(c_5593,plain,(
    ! [A_625,C_626,B_627] :
      ( k6_partfun1(A_625) = k5_relat_1(C_626,k2_funct_1(C_626))
      | k1_xboole_0 = B_627
      | ~ v2_funct_1(C_626)
      | k2_relset_1(A_625,B_627,C_626) != B_627
      | ~ m1_subset_1(C_626,k1_zfmisc_1(k2_zfmisc_1(A_625,B_627)))
      | ~ v1_funct_2(C_626,A_625,B_627)
      | ~ v1_funct_1(C_626) ) ),
    inference(cnfTransformation,[status(thm)],[f_219])).

tff(c_5599,plain,
    ( k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_partfun1('#skF_1')
    | k1_xboole_0 = '#skF_2'
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1('#skF_1','#skF_2','#skF_3') != '#skF_2'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_92,c_5593])).

tff(c_5608,plain,
    ( k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_partfun1('#skF_1')
    | k1_xboole_0 = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_94,c_84,c_80,c_5599])).

tff(c_5609,plain,(
    k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_partfun1('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_5608])).

tff(c_5629,plain,
    ( r1_tarski(k2_relat_1(k6_partfun1('#skF_1')),k2_relat_1(k2_funct_1('#skF_3')))
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_5609,c_12])).

tff(c_5641,plain,
    ( r1_tarski('#skF_1',k2_relat_1(k2_funct_1('#skF_3')))
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_158,c_101,c_5629])).

tff(c_5672,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_5641])).

tff(c_5449,plain,(
    ! [C_608,B_609,A_610] :
      ( m1_subset_1(k2_funct_1(C_608),k1_zfmisc_1(k2_zfmisc_1(B_609,A_610)))
      | k2_relset_1(A_610,B_609,C_608) != B_609
      | ~ v2_funct_1(C_608)
      | ~ m1_subset_1(C_608,k1_zfmisc_1(k2_zfmisc_1(A_610,B_609)))
      | ~ v1_funct_2(C_608,A_610,B_609)
      | ~ v1_funct_1(C_608) ) ),
    inference(cnfTransformation,[status(thm)],[f_203])).

tff(c_32,plain,(
    ! [C_19,A_17,B_18] :
      ( v1_relat_1(C_19)
      | ~ m1_subset_1(C_19,k1_zfmisc_1(k2_zfmisc_1(A_17,B_18))) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_7394,plain,(
    ! [C_681,A_682,B_683] :
      ( v1_relat_1(k2_funct_1(C_681))
      | k2_relset_1(A_682,B_683,C_681) != B_683
      | ~ v2_funct_1(C_681)
      | ~ m1_subset_1(C_681,k1_zfmisc_1(k2_zfmisc_1(A_682,B_683)))
      | ~ v1_funct_2(C_681,A_682,B_683)
      | ~ v1_funct_1(C_681) ) ),
    inference(resolution,[status(thm)],[c_5449,c_32])).

tff(c_7439,plain,
    ( v1_relat_1(k2_funct_1('#skF_3'))
    | k2_relset_1('#skF_1','#skF_2','#skF_3') != '#skF_2'
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_92,c_7394])).

tff(c_7483,plain,(
    v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_94,c_80,c_84,c_7439])).

tff(c_7485,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_5672,c_7483])).

tff(c_7487,plain,(
    v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_5641])).

tff(c_7486,plain,(
    r1_tarski('#skF_1',k2_relat_1(k2_funct_1('#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_5641])).

tff(c_179,plain,(
    ! [B_77,A_78] :
      ( k2_relat_1(B_77) = A_78
      | ~ r1_tarski(A_78,k2_relat_1(B_77))
      | ~ v5_relat_1(B_77,A_78)
      | ~ v1_relat_1(B_77) ) ),
    inference(resolution,[status(thm)],[c_173,c_2])).

tff(c_7503,plain,
    ( k2_relat_1(k2_funct_1('#skF_3')) = '#skF_1'
    | ~ v5_relat_1(k2_funct_1('#skF_3'),'#skF_1')
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_7486,c_179])).

tff(c_7511,plain,
    ( k2_relat_1(k2_funct_1('#skF_3')) = '#skF_1'
    | ~ v5_relat_1(k2_funct_1('#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_7487,c_7503])).

tff(c_9485,plain,(
    ~ v5_relat_1(k2_funct_1('#skF_3'),'#skF_1') ),
    inference(splitLeft,[status(thm)],[c_7511])).

tff(c_34,plain,(
    ! [C_22,B_21,A_20] :
      ( v5_relat_1(C_22,B_21)
      | ~ m1_subset_1(C_22,k1_zfmisc_1(k2_zfmisc_1(A_20,B_21))) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_11769,plain,(
    ! [C_823,A_824,B_825] :
      ( v5_relat_1(k2_funct_1(C_823),A_824)
      | k2_relset_1(A_824,B_825,C_823) != B_825
      | ~ v2_funct_1(C_823)
      | ~ m1_subset_1(C_823,k1_zfmisc_1(k2_zfmisc_1(A_824,B_825)))
      | ~ v1_funct_2(C_823,A_824,B_825)
      | ~ v1_funct_1(C_823) ) ),
    inference(resolution,[status(thm)],[c_5449,c_34])).

tff(c_11811,plain,
    ( v5_relat_1(k2_funct_1('#skF_3'),'#skF_1')
    | k2_relset_1('#skF_1','#skF_2','#skF_3') != '#skF_2'
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_92,c_11769])).

tff(c_11852,plain,(
    v5_relat_1(k2_funct_1('#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_94,c_80,c_84,c_11811])).

tff(c_11854,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_9485,c_11852])).

tff(c_11855,plain,(
    k2_relat_1(k2_funct_1('#skF_3')) = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_7511])).

tff(c_26,plain,(
    ! [A_13] :
      ( k2_relat_1(k2_funct_1(A_13)) = k1_relat_1(A_13)
      | ~ v2_funct_1(A_13)
      | ~ v1_funct_1(A_13)
      | ~ v1_relat_1(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_11881,plain,
    ( k1_relat_1('#skF_3') = '#skF_1'
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_11855,c_26])).

tff(c_11914,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_158,c_96,c_80,c_11881])).

tff(c_11916,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_5507,c_11914])).

tff(c_11917,plain,(
    k5_relat_1('#skF_4','#skF_3') != k6_partfun1('#skF_2') ),
    inference(splitRight,[status(thm)],[c_5501])).

tff(c_4836,plain,(
    ! [D_555,A_552,F_554,E_556,B_553,C_557] :
      ( k1_partfun1(A_552,B_553,C_557,D_555,E_556,F_554) = k5_relat_1(E_556,F_554)
      | ~ m1_subset_1(F_554,k1_zfmisc_1(k2_zfmisc_1(C_557,D_555)))
      | ~ v1_funct_1(F_554)
      | ~ m1_subset_1(E_556,k1_zfmisc_1(k2_zfmisc_1(A_552,B_553)))
      | ~ v1_funct_1(E_556) ) ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_4844,plain,(
    ! [A_552,B_553,E_556] :
      ( k1_partfun1(A_552,B_553,'#skF_2','#skF_1',E_556,'#skF_4') = k5_relat_1(E_556,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_556,k1_zfmisc_1(k2_zfmisc_1(A_552,B_553)))
      | ~ v1_funct_1(E_556) ) ),
    inference(resolution,[status(thm)],[c_86,c_4836])).

tff(c_4872,plain,(
    ! [A_559,B_560,E_561] :
      ( k1_partfun1(A_559,B_560,'#skF_2','#skF_1',E_561,'#skF_4') = k5_relat_1(E_561,'#skF_4')
      | ~ m1_subset_1(E_561,k1_zfmisc_1(k2_zfmisc_1(A_559,B_560)))
      | ~ v1_funct_1(E_561) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_4844])).

tff(c_4881,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_92,c_4872])).

tff(c_4889,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_4881])).

tff(c_4534,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_477])).

tff(c_4894,plain,(
    ~ m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4889,c_4534])).

tff(c_5117,plain,(
    ! [F_575,D_571,C_576,A_574,B_572,E_573] :
      ( m1_subset_1(k1_partfun1(A_574,B_572,C_576,D_571,E_573,F_575),k1_zfmisc_1(k2_zfmisc_1(A_574,D_571)))
      | ~ m1_subset_1(F_575,k1_zfmisc_1(k2_zfmisc_1(C_576,D_571)))
      | ~ v1_funct_1(F_575)
      | ~ m1_subset_1(E_573,k1_zfmisc_1(k2_zfmisc_1(A_574,B_572)))
      | ~ v1_funct_1(E_573) ) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_5172,plain,
    ( m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_4889,c_5117])).

tff(c_5196,plain,(
    m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_92,c_90,c_86,c_5172])).

tff(c_5198,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4894,c_5196])).

tff(c_5199,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_477])).

tff(c_13988,plain,(
    ! [D_909,B_907,A_906,F_908,E_910,C_911] :
      ( k1_partfun1(A_906,B_907,C_911,D_909,E_910,F_908) = k5_relat_1(E_910,F_908)
      | ~ m1_subset_1(F_908,k1_zfmisc_1(k2_zfmisc_1(C_911,D_909)))
      | ~ v1_funct_1(F_908)
      | ~ m1_subset_1(E_910,k1_zfmisc_1(k2_zfmisc_1(A_906,B_907)))
      | ~ v1_funct_1(E_910) ) ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_13996,plain,(
    ! [A_906,B_907,E_910] :
      ( k1_partfun1(A_906,B_907,'#skF_2','#skF_1',E_910,'#skF_4') = k5_relat_1(E_910,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_910,k1_zfmisc_1(k2_zfmisc_1(A_906,B_907)))
      | ~ v1_funct_1(E_910) ) ),
    inference(resolution,[status(thm)],[c_86,c_13988])).

tff(c_18772,plain,(
    ! [A_1073,B_1074,E_1075] :
      ( k1_partfun1(A_1073,B_1074,'#skF_2','#skF_1',E_1075,'#skF_4') = k5_relat_1(E_1075,'#skF_4')
      | ~ m1_subset_1(E_1075,k1_zfmisc_1(k2_zfmisc_1(A_1073,B_1074)))
      | ~ v1_funct_1(E_1075) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_13996])).

tff(c_18784,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_92,c_18772])).

tff(c_18793,plain,(
    k5_relat_1('#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_5199,c_18784])).

tff(c_2829,plain,(
    v2_funct_1('#skF_4') ),
    inference(splitRight,[status(thm)],[c_570])).

tff(c_4477,plain,(
    ! [B_512] :
      ( k2_funct_1('#skF_4') = B_512
      | k5_relat_1(B_512,'#skF_4') != k6_partfun1('#skF_1')
      | k2_relat_1(B_512) != k1_relat_1('#skF_4')
      | ~ v2_funct_1('#skF_4')
      | ~ v1_funct_1(B_512)
      | ~ v1_relat_1(B_512)
      | ~ v1_funct_1('#skF_4')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4424,c_4475])).

tff(c_14005,plain,(
    ! [B_912] :
      ( k2_funct_1('#skF_4') = B_912
      | k5_relat_1(B_912,'#skF_4') != k6_partfun1('#skF_1')
      | k2_relat_1(B_912) != k1_relat_1('#skF_4')
      | ~ v1_funct_1(B_912)
      | ~ v1_relat_1(B_912) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_159,c_90,c_2829,c_4477])).

tff(c_14014,plain,
    ( k2_funct_1('#skF_4') = '#skF_3'
    | k5_relat_1('#skF_3','#skF_4') != k6_partfun1('#skF_1')
    | k2_relat_1('#skF_3') != k1_relat_1('#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_158,c_14005])).

tff(c_14026,plain,
    ( k2_funct_1('#skF_4') = '#skF_3'
    | k5_relat_1('#skF_3','#skF_4') != k6_partfun1('#skF_1')
    | k1_relat_1('#skF_4') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_312,c_14014])).

tff(c_14061,plain,(
    k1_relat_1('#skF_4') != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_14026])).

tff(c_4425,plain,(
    k2_relset_1('#skF_2','#skF_1','#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4424,c_313])).

tff(c_14322,plain,(
    ! [A_922,C_923,B_924] :
      ( k6_partfun1(A_922) = k5_relat_1(C_923,k2_funct_1(C_923))
      | k1_xboole_0 = B_924
      | ~ v2_funct_1(C_923)
      | k2_relset_1(A_922,B_924,C_923) != B_924
      | ~ m1_subset_1(C_923,k1_zfmisc_1(k2_zfmisc_1(A_922,B_924)))
      | ~ v1_funct_2(C_923,A_922,B_924)
      | ~ v1_funct_1(C_923) ) ),
    inference(cnfTransformation,[status(thm)],[f_219])).

tff(c_14330,plain,
    ( k5_relat_1('#skF_4',k2_funct_1('#skF_4')) = k6_partfun1('#skF_2')
    | k1_xboole_0 = '#skF_1'
    | ~ v2_funct_1('#skF_4')
    | k2_relset_1('#skF_2','#skF_1','#skF_4') != '#skF_1'
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_86,c_14322])).

tff(c_14341,plain,
    ( k5_relat_1('#skF_4',k2_funct_1('#skF_4')) = k6_partfun1('#skF_2')
    | k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_88,c_4425,c_2829,c_14330])).

tff(c_14342,plain,(
    k5_relat_1('#skF_4',k2_funct_1('#skF_4')) = k6_partfun1('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_14341])).

tff(c_14387,plain,
    ( r1_tarski(k2_relat_1(k6_partfun1('#skF_2')),k2_relat_1(k2_funct_1('#skF_4')))
    | ~ v1_relat_1(k2_funct_1('#skF_4'))
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_14342,c_12])).

tff(c_14399,plain,
    ( r1_tarski('#skF_2',k2_relat_1(k2_funct_1('#skF_4')))
    | ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_159,c_101,c_14387])).

tff(c_14444,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_14399])).

tff(c_16052,plain,(
    ! [C_982,A_983,B_984] :
      ( v1_relat_1(k2_funct_1(C_982))
      | k2_relset_1(A_983,B_984,C_982) != B_984
      | ~ v2_funct_1(C_982)
      | ~ m1_subset_1(C_982,k1_zfmisc_1(k2_zfmisc_1(A_983,B_984)))
      | ~ v1_funct_2(C_982,A_983,B_984)
      | ~ v1_funct_1(C_982) ) ),
    inference(resolution,[status(thm)],[c_5449,c_32])).

tff(c_16097,plain,
    ( v1_relat_1(k2_funct_1('#skF_4'))
    | k2_relset_1('#skF_2','#skF_1','#skF_4') != '#skF_1'
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_86,c_16052])).

tff(c_16138,plain,(
    v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_88,c_2829,c_4425,c_16097])).

tff(c_16140,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_14444,c_16138])).

tff(c_16142,plain,(
    v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_14399])).

tff(c_18,plain,(
    ! [A_9] : v1_relat_1(k6_relat_1(A_9)) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_100,plain,(
    ! [A_9] : v1_relat_1(k6_partfun1(A_9)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_18])).

tff(c_246,plain,(
    ! [A_92,B_93] :
      ( r1_tarski(k2_relat_1(k5_relat_1(A_92,B_93)),k2_relat_1(B_93))
      | ~ v1_relat_1(B_93)
      | ~ v1_relat_1(A_92) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_8,plain,(
    ! [B_4,A_3] :
      ( v5_relat_1(B_4,A_3)
      | ~ r1_tarski(k2_relat_1(B_4),A_3)
      | ~ v1_relat_1(B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_255,plain,(
    ! [A_92,B_93] :
      ( v5_relat_1(k5_relat_1(A_92,B_93),k2_relat_1(B_93))
      | ~ v1_relat_1(k5_relat_1(A_92,B_93))
      | ~ v1_relat_1(B_93)
      | ~ v1_relat_1(A_92) ) ),
    inference(resolution,[status(thm)],[c_246,c_8])).

tff(c_14378,plain,
    ( v5_relat_1(k6_partfun1('#skF_2'),k2_relat_1(k2_funct_1('#skF_4')))
    | ~ v1_relat_1(k5_relat_1('#skF_4',k2_funct_1('#skF_4')))
    | ~ v1_relat_1(k2_funct_1('#skF_4'))
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_14342,c_255])).

tff(c_14393,plain,
    ( v5_relat_1(k6_partfun1('#skF_2'),k2_relat_1(k2_funct_1('#skF_4')))
    | ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_159,c_100,c_14342,c_14378])).

tff(c_16176,plain,(
    v5_relat_1(k6_partfun1('#skF_2'),k2_relat_1(k2_funct_1('#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16142,c_14393])).

tff(c_10,plain,(
    ! [B_4,A_3] :
      ( r1_tarski(k2_relat_1(B_4),A_3)
      | ~ v5_relat_1(B_4,A_3)
      | ~ v1_relat_1(B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_408,plain,(
    ! [B_4,B_111] :
      ( k2_relat_1(B_4) = k2_relat_1(B_111)
      | ~ v5_relat_1(B_111,k2_relat_1(B_4))
      | ~ v1_relat_1(B_111)
      | ~ v5_relat_1(B_4,k2_relat_1(B_111))
      | ~ v1_relat_1(B_4) ) ),
    inference(resolution,[status(thm)],[c_10,c_379])).

tff(c_16183,plain,
    ( k2_relat_1(k6_partfun1('#skF_2')) = k2_relat_1(k2_funct_1('#skF_4'))
    | ~ v1_relat_1(k6_partfun1('#skF_2'))
    | ~ v5_relat_1(k2_funct_1('#skF_4'),k2_relat_1(k6_partfun1('#skF_2')))
    | ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_16176,c_408])).

tff(c_16199,plain,
    ( k2_relat_1(k2_funct_1('#skF_4')) = '#skF_2'
    | ~ v5_relat_1(k2_funct_1('#skF_4'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16142,c_101,c_100,c_101,c_16183])).

tff(c_16224,plain,(
    ~ v5_relat_1(k2_funct_1('#skF_4'),'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_16199])).

tff(c_17996,plain,(
    ! [C_1048,A_1049,B_1050] :
      ( v5_relat_1(k2_funct_1(C_1048),A_1049)
      | k2_relset_1(A_1049,B_1050,C_1048) != B_1050
      | ~ v2_funct_1(C_1048)
      | ~ m1_subset_1(C_1048,k1_zfmisc_1(k2_zfmisc_1(A_1049,B_1050)))
      | ~ v1_funct_2(C_1048,A_1049,B_1050)
      | ~ v1_funct_1(C_1048) ) ),
    inference(resolution,[status(thm)],[c_5449,c_34])).

tff(c_18041,plain,
    ( v5_relat_1(k2_funct_1('#skF_4'),'#skF_2')
    | k2_relset_1('#skF_2','#skF_1','#skF_4') != '#skF_1'
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_86,c_17996])).

tff(c_18082,plain,(
    v5_relat_1(k2_funct_1('#skF_4'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_88,c_2829,c_4425,c_18041])).

tff(c_18084,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_16224,c_18082])).

tff(c_18085,plain,(
    k2_relat_1(k2_funct_1('#skF_4')) = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_16199])).

tff(c_18113,plain,
    ( k1_relat_1('#skF_4') = '#skF_2'
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_18085,c_26])).

tff(c_18147,plain,(
    k1_relat_1('#skF_4') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_159,c_90,c_2829,c_18113])).

tff(c_18149,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_14061,c_18147])).

tff(c_18150,plain,
    ( k5_relat_1('#skF_3','#skF_4') != k6_partfun1('#skF_1')
    | k2_funct_1('#skF_4') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_14026])).

tff(c_18771,plain,(
    k5_relat_1('#skF_3','#skF_4') != k6_partfun1('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_18150])).

tff(c_18842,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_18793,c_18771])).

tff(c_18843,plain,(
    k2_funct_1('#skF_4') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_18150])).

tff(c_18472,plain,(
    ! [A_1060,C_1061,B_1062] :
      ( k6_partfun1(A_1060) = k5_relat_1(C_1061,k2_funct_1(C_1061))
      | k1_xboole_0 = B_1062
      | ~ v2_funct_1(C_1061)
      | k2_relset_1(A_1060,B_1062,C_1061) != B_1062
      | ~ m1_subset_1(C_1061,k1_zfmisc_1(k2_zfmisc_1(A_1060,B_1062)))
      | ~ v1_funct_2(C_1061,A_1060,B_1062)
      | ~ v1_funct_1(C_1061) ) ),
    inference(cnfTransformation,[status(thm)],[f_219])).

tff(c_18480,plain,
    ( k5_relat_1('#skF_4',k2_funct_1('#skF_4')) = k6_partfun1('#skF_2')
    | k1_xboole_0 = '#skF_1'
    | ~ v2_funct_1('#skF_4')
    | k2_relset_1('#skF_2','#skF_1','#skF_4') != '#skF_1'
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_86,c_18472])).

tff(c_18491,plain,
    ( k5_relat_1('#skF_4',k2_funct_1('#skF_4')) = k6_partfun1('#skF_2')
    | k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_88,c_4425,c_2829,c_18480])).

tff(c_18492,plain,(
    k5_relat_1('#skF_4',k2_funct_1('#skF_4')) = k6_partfun1('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_18491])).

tff(c_18847,plain,(
    k5_relat_1('#skF_4','#skF_3') = k6_partfun1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_18843,c_18492])).

tff(c_18857,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_11917,c_18847])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n001.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 17:50:00 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 12.67/5.48  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 12.67/5.51  
% 12.67/5.51  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 12.67/5.51  %$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 12.67/5.51  
% 12.67/5.51  %Foreground sorts:
% 12.67/5.51  
% 12.67/5.51  
% 12.67/5.51  %Background operators:
% 12.67/5.51  
% 12.67/5.51  
% 12.67/5.51  %Foreground operators:
% 12.67/5.51  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 12.67/5.51  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 12.67/5.51  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 12.67/5.51  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 12.67/5.51  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 12.67/5.51  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 12.67/5.51  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 12.67/5.51  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 12.67/5.51  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 12.67/5.51  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 12.67/5.51  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 12.67/5.51  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 12.67/5.51  tff('#skF_2', type, '#skF_2': $i).
% 12.67/5.51  tff('#skF_3', type, '#skF_3': $i).
% 12.67/5.51  tff('#skF_1', type, '#skF_1': $i).
% 12.67/5.51  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 12.67/5.51  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 12.67/5.51  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 12.67/5.51  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 12.67/5.51  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 12.67/5.51  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 12.67/5.51  tff('#skF_4', type, '#skF_4': $i).
% 12.67/5.51  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 12.67/5.51  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 12.67/5.51  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 12.67/5.51  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 12.67/5.51  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 12.67/5.51  
% 12.67/5.54  tff(f_245, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => ((((k2_relset_1(A, B, C) = B) & r2_relset_1(A, A, k1_partfun1(A, B, B, A, C, D), k6_partfun1(A))) & v2_funct_1(C)) => (((A = k1_xboole_0) | (B = k1_xboole_0)) | (D = k2_funct_1(C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_funct_2)).
% 12.67/5.54  tff(f_110, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 12.67/5.54  tff(f_203, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((v2_funct_1(C) & (k2_relset_1(A, B, C) = B)) => ((v1_funct_1(k2_funct_1(C)) & v1_funct_2(k2_funct_1(C), B, A)) & m1_subset_1(k2_funct_1(C), k1_zfmisc_1(k2_zfmisc_1(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_funct_2)).
% 12.67/5.54  tff(f_144, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 12.67/5.54  tff(f_52, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v2_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc4_funct_1)).
% 12.67/5.54  tff(f_142, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 12.67/5.54  tff(f_120, axiom, (![A]: m1_subset_1(k6_relat_1(A), k1_zfmisc_1(k2_zfmisc_1(A, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_relset_1)).
% 12.67/5.54  tff(f_118, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 12.67/5.54  tff(f_132, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (v1_funct_1(k1_partfun1(A, B, C, D, E, F)) & m1_subset_1(k1_partfun1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 12.67/5.54  tff(f_187, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, B, C)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => ((v2_funct_1(k1_partfun1(A, B, B, C, D, E)) & (k2_relset_1(A, B, D) = B)) => (((C = k1_xboole_0) & ~(B = k1_xboole_0)) | (v2_funct_1(D) & v2_funct_1(E)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t30_funct_2)).
% 12.67/5.54  tff(f_100, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 12.67/5.54  tff(f_106, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 12.67/5.54  tff(f_48, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 12.67/5.54  tff(f_44, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => r1_tarski(k2_relat_1(k5_relat_1(A, B)), k2_relat_1(B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t45_relat_1)).
% 12.67/5.54  tff(f_37, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 12.67/5.54  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 12.67/5.54  tff(f_96, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (((v2_funct_1(A) & (k2_relat_1(B) = k1_relat_1(A))) & (k5_relat_1(B, A) = k6_relat_1(k2_relat_1(A)))) => (B = k2_funct_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_funct_1)).
% 12.67/5.54  tff(f_219, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((k2_relset_1(A, B, C) = B) & v2_funct_1(C)) => ((B = k1_xboole_0) | ((k5_relat_1(C, k2_funct_1(C)) = k6_partfun1(A)) & (k5_relat_1(k2_funct_1(C), C) = k6_partfun1(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t35_funct_2)).
% 12.67/5.54  tff(f_79, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k2_relat_1(A) = k1_relat_1(k2_funct_1(A))) & (k1_relat_1(A) = k2_relat_1(k2_funct_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_funct_1)).
% 12.67/5.54  tff(c_74, plain, (k2_funct_1('#skF_3')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_245])).
% 12.67/5.54  tff(c_90, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_245])).
% 12.67/5.54  tff(c_88, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_245])).
% 12.67/5.54  tff(c_86, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_245])).
% 12.67/5.54  tff(c_299, plain, (![A_101, B_102, C_103]: (k2_relset_1(A_101, B_102, C_103)=k2_relat_1(C_103) | ~m1_subset_1(C_103, k1_zfmisc_1(k2_zfmisc_1(A_101, B_102))))), inference(cnfTransformation, [status(thm)], [f_110])).
% 12.67/5.54  tff(c_313, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_86, c_299])).
% 12.67/5.54  tff(c_552, plain, (![C_133, A_134, B_135]: (v1_funct_1(k2_funct_1(C_133)) | k2_relset_1(A_134, B_135, C_133)!=B_135 | ~v2_funct_1(C_133) | ~m1_subset_1(C_133, k1_zfmisc_1(k2_zfmisc_1(A_134, B_135))) | ~v1_funct_2(C_133, A_134, B_135) | ~v1_funct_1(C_133))), inference(cnfTransformation, [status(thm)], [f_203])).
% 12.67/5.54  tff(c_561, plain, (v1_funct_1(k2_funct_1('#skF_4')) | k2_relset_1('#skF_2', '#skF_1', '#skF_4')!='#skF_1' | ~v2_funct_1('#skF_4') | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_86, c_552])).
% 12.67/5.54  tff(c_570, plain, (v1_funct_1(k2_funct_1('#skF_4')) | k2_relat_1('#skF_4')!='#skF_1' | ~v2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_90, c_88, c_313, c_561])).
% 12.67/5.54  tff(c_571, plain, (~v2_funct_1('#skF_4')), inference(splitLeft, [status(thm)], [c_570])).
% 12.67/5.54  tff(c_78, plain, (k1_xboole_0!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_245])).
% 12.67/5.54  tff(c_96, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_245])).
% 12.67/5.54  tff(c_94, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_245])).
% 12.67/5.54  tff(c_92, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_245])).
% 12.67/5.54  tff(c_52, plain, (![A_43]: (k6_relat_1(A_43)=k6_partfun1(A_43))), inference(cnfTransformation, [status(thm)], [f_144])).
% 12.67/5.54  tff(c_20, plain, (![A_9]: (v2_funct_1(k6_relat_1(A_9)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 12.67/5.54  tff(c_99, plain, (![A_9]: (v2_funct_1(k6_partfun1(A_9)))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_20])).
% 12.67/5.54  tff(c_84, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_2'), inference(cnfTransformation, [status(thm)], [f_245])).
% 12.67/5.54  tff(c_1087, plain, (![F_192, A_190, B_191, C_195, D_193, E_194]: (k1_partfun1(A_190, B_191, C_195, D_193, E_194, F_192)=k5_relat_1(E_194, F_192) | ~m1_subset_1(F_192, k1_zfmisc_1(k2_zfmisc_1(C_195, D_193))) | ~v1_funct_1(F_192) | ~m1_subset_1(E_194, k1_zfmisc_1(k2_zfmisc_1(A_190, B_191))) | ~v1_funct_1(E_194))), inference(cnfTransformation, [status(thm)], [f_142])).
% 12.67/5.54  tff(c_1095, plain, (![A_190, B_191, E_194]: (k1_partfun1(A_190, B_191, '#skF_2', '#skF_1', E_194, '#skF_4')=k5_relat_1(E_194, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_194, k1_zfmisc_1(k2_zfmisc_1(A_190, B_191))) | ~v1_funct_1(E_194))), inference(resolution, [status(thm)], [c_86, c_1087])).
% 12.67/5.54  tff(c_1136, plain, (![A_200, B_201, E_202]: (k1_partfun1(A_200, B_201, '#skF_2', '#skF_1', E_202, '#skF_4')=k5_relat_1(E_202, '#skF_4') | ~m1_subset_1(E_202, k1_zfmisc_1(k2_zfmisc_1(A_200, B_201))) | ~v1_funct_1(E_202))), inference(demodulation, [status(thm), theory('equality')], [c_90, c_1095])).
% 12.67/5.54  tff(c_1145, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_92, c_1136])).
% 12.67/5.54  tff(c_1153, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_96, c_1145])).
% 12.67/5.54  tff(c_44, plain, (![A_30]: (m1_subset_1(k6_relat_1(A_30), k1_zfmisc_1(k2_zfmisc_1(A_30, A_30))))), inference(cnfTransformation, [status(thm)], [f_120])).
% 12.67/5.54  tff(c_97, plain, (![A_30]: (m1_subset_1(k6_partfun1(A_30), k1_zfmisc_1(k2_zfmisc_1(A_30, A_30))))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_44])).
% 12.67/5.54  tff(c_82, plain, (r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k6_partfun1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_245])).
% 12.67/5.54  tff(c_454, plain, (![D_121, C_122, A_123, B_124]: (D_121=C_122 | ~r2_relset_1(A_123, B_124, C_122, D_121) | ~m1_subset_1(D_121, k1_zfmisc_1(k2_zfmisc_1(A_123, B_124))) | ~m1_subset_1(C_122, k1_zfmisc_1(k2_zfmisc_1(A_123, B_124))))), inference(cnfTransformation, [status(thm)], [f_118])).
% 12.67/5.54  tff(c_462, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_82, c_454])).
% 12.67/5.54  tff(c_477, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_97, c_462])).
% 12.67/5.54  tff(c_572, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_477])).
% 12.67/5.54  tff(c_1158, plain, (~m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_1153, c_572])).
% 12.67/5.54  tff(c_1355, plain, (![C_228, D_223, F_227, B_224, A_226, E_225]: (m1_subset_1(k1_partfun1(A_226, B_224, C_228, D_223, E_225, F_227), k1_zfmisc_1(k2_zfmisc_1(A_226, D_223))) | ~m1_subset_1(F_227, k1_zfmisc_1(k2_zfmisc_1(C_228, D_223))) | ~v1_funct_1(F_227) | ~m1_subset_1(E_225, k1_zfmisc_1(k2_zfmisc_1(A_226, B_224))) | ~v1_funct_1(E_225))), inference(cnfTransformation, [status(thm)], [f_132])).
% 12.67/5.54  tff(c_1409, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1153, c_1355])).
% 12.67/5.54  tff(c_1437, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_96, c_92, c_90, c_86, c_1409])).
% 12.67/5.54  tff(c_1439, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1158, c_1437])).
% 12.67/5.54  tff(c_1440, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_477])).
% 12.67/5.54  tff(c_2816, plain, (![A_337, E_334, D_338, B_336, C_335]: (k1_xboole_0=C_335 | v2_funct_1(E_334) | k2_relset_1(A_337, B_336, D_338)!=B_336 | ~v2_funct_1(k1_partfun1(A_337, B_336, B_336, C_335, D_338, E_334)) | ~m1_subset_1(E_334, k1_zfmisc_1(k2_zfmisc_1(B_336, C_335))) | ~v1_funct_2(E_334, B_336, C_335) | ~v1_funct_1(E_334) | ~m1_subset_1(D_338, k1_zfmisc_1(k2_zfmisc_1(A_337, B_336))) | ~v1_funct_2(D_338, A_337, B_336) | ~v1_funct_1(D_338))), inference(cnfTransformation, [status(thm)], [f_187])).
% 12.67/5.54  tff(c_2820, plain, (k1_xboole_0='#skF_1' | v2_funct_1('#skF_4') | k2_relset_1('#skF_1', '#skF_2', '#skF_3')!='#skF_2' | ~v2_funct_1(k6_partfun1('#skF_1')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1440, c_2816])).
% 12.67/5.54  tff(c_2825, plain, (k1_xboole_0='#skF_1' | v2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_96, c_94, c_92, c_90, c_88, c_86, c_99, c_84, c_2820])).
% 12.67/5.54  tff(c_2827, plain, $false, inference(negUnitSimplification, [status(thm)], [c_571, c_78, c_2825])).
% 12.67/5.54  tff(c_2828, plain, (k2_relat_1('#skF_4')!='#skF_1' | v1_funct_1(k2_funct_1('#skF_4'))), inference(splitRight, [status(thm)], [c_570])).
% 12.67/5.54  tff(c_2830, plain, (k2_relat_1('#skF_4')!='#skF_1'), inference(splitLeft, [status(thm)], [c_2828])).
% 12.67/5.54  tff(c_146, plain, (![C_71, A_72, B_73]: (v1_relat_1(C_71) | ~m1_subset_1(C_71, k1_zfmisc_1(k2_zfmisc_1(A_72, B_73))))), inference(cnfTransformation, [status(thm)], [f_100])).
% 12.67/5.54  tff(c_158, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_92, c_146])).
% 12.67/5.54  tff(c_159, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_86, c_146])).
% 12.67/5.54  tff(c_223, plain, (![C_88, B_89, A_90]: (v5_relat_1(C_88, B_89) | ~m1_subset_1(C_88, k1_zfmisc_1(k2_zfmisc_1(A_90, B_89))))), inference(cnfTransformation, [status(thm)], [f_106])).
% 12.67/5.54  tff(c_236, plain, (v5_relat_1('#skF_4', '#skF_1')), inference(resolution, [status(thm)], [c_86, c_223])).
% 12.67/5.54  tff(c_16, plain, (![A_8]: (k2_relat_1(k6_relat_1(A_8))=A_8)), inference(cnfTransformation, [status(thm)], [f_48])).
% 12.67/5.54  tff(c_101, plain, (![A_8]: (k2_relat_1(k6_partfun1(A_8))=A_8)), inference(demodulation, [status(thm), theory('equality')], [c_52, c_16])).
% 12.67/5.54  tff(c_3346, plain, (![B_394, D_396, E_397, F_395, C_398, A_393]: (k1_partfun1(A_393, B_394, C_398, D_396, E_397, F_395)=k5_relat_1(E_397, F_395) | ~m1_subset_1(F_395, k1_zfmisc_1(k2_zfmisc_1(C_398, D_396))) | ~v1_funct_1(F_395) | ~m1_subset_1(E_397, k1_zfmisc_1(k2_zfmisc_1(A_393, B_394))) | ~v1_funct_1(E_397))), inference(cnfTransformation, [status(thm)], [f_142])).
% 12.67/5.54  tff(c_3354, plain, (![A_393, B_394, E_397]: (k1_partfun1(A_393, B_394, '#skF_2', '#skF_1', E_397, '#skF_4')=k5_relat_1(E_397, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_397, k1_zfmisc_1(k2_zfmisc_1(A_393, B_394))) | ~v1_funct_1(E_397))), inference(resolution, [status(thm)], [c_86, c_3346])).
% 12.67/5.54  tff(c_3395, plain, (![A_403, B_404, E_405]: (k1_partfun1(A_403, B_404, '#skF_2', '#skF_1', E_405, '#skF_4')=k5_relat_1(E_405, '#skF_4') | ~m1_subset_1(E_405, k1_zfmisc_1(k2_zfmisc_1(A_403, B_404))) | ~v1_funct_1(E_405))), inference(demodulation, [status(thm), theory('equality')], [c_90, c_3354])).
% 12.67/5.54  tff(c_3404, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_92, c_3395])).
% 12.67/5.54  tff(c_3412, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_96, c_3404])).
% 12.67/5.54  tff(c_2831, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_477])).
% 12.67/5.54  tff(c_3417, plain, (~m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_3412, c_2831])).
% 12.67/5.54  tff(c_3614, plain, (![D_426, F_430, C_431, A_429, B_427, E_428]: (m1_subset_1(k1_partfun1(A_429, B_427, C_431, D_426, E_428, F_430), k1_zfmisc_1(k2_zfmisc_1(A_429, D_426))) | ~m1_subset_1(F_430, k1_zfmisc_1(k2_zfmisc_1(C_431, D_426))) | ~v1_funct_1(F_430) | ~m1_subset_1(E_428, k1_zfmisc_1(k2_zfmisc_1(A_429, B_427))) | ~v1_funct_1(E_428))), inference(cnfTransformation, [status(thm)], [f_132])).
% 12.67/5.54  tff(c_3668, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_3412, c_3614])).
% 12.67/5.54  tff(c_3696, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_96, c_92, c_90, c_86, c_3668])).
% 12.67/5.54  tff(c_3698, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3417, c_3696])).
% 12.67/5.54  tff(c_3699, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_477])).
% 12.67/5.54  tff(c_4244, plain, (![F_492, B_491, D_493, E_494, C_495, A_490]: (k1_partfun1(A_490, B_491, C_495, D_493, E_494, F_492)=k5_relat_1(E_494, F_492) | ~m1_subset_1(F_492, k1_zfmisc_1(k2_zfmisc_1(C_495, D_493))) | ~v1_funct_1(F_492) | ~m1_subset_1(E_494, k1_zfmisc_1(k2_zfmisc_1(A_490, B_491))) | ~v1_funct_1(E_494))), inference(cnfTransformation, [status(thm)], [f_142])).
% 12.67/5.54  tff(c_4252, plain, (![A_490, B_491, E_494]: (k1_partfun1(A_490, B_491, '#skF_2', '#skF_1', E_494, '#skF_4')=k5_relat_1(E_494, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_494, k1_zfmisc_1(k2_zfmisc_1(A_490, B_491))) | ~v1_funct_1(E_494))), inference(resolution, [status(thm)], [c_86, c_4244])).
% 12.67/5.54  tff(c_4374, plain, (![A_507, B_508, E_509]: (k1_partfun1(A_507, B_508, '#skF_2', '#skF_1', E_509, '#skF_4')=k5_relat_1(E_509, '#skF_4') | ~m1_subset_1(E_509, k1_zfmisc_1(k2_zfmisc_1(A_507, B_508))) | ~v1_funct_1(E_509))), inference(demodulation, [status(thm), theory('equality')], [c_90, c_4252])).
% 12.67/5.54  tff(c_4383, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_92, c_4374])).
% 12.67/5.54  tff(c_4391, plain, (k5_relat_1('#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_96, c_3699, c_4383])).
% 12.67/5.54  tff(c_12, plain, (![A_5, B_7]: (r1_tarski(k2_relat_1(k5_relat_1(A_5, B_7)), k2_relat_1(B_7)) | ~v1_relat_1(B_7) | ~v1_relat_1(A_5))), inference(cnfTransformation, [status(thm)], [f_44])).
% 12.67/5.54  tff(c_173, plain, (![B_77, A_78]: (r1_tarski(k2_relat_1(B_77), A_78) | ~v5_relat_1(B_77, A_78) | ~v1_relat_1(B_77))), inference(cnfTransformation, [status(thm)], [f_37])).
% 12.67/5.54  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 12.67/5.54  tff(c_379, plain, (![B_111, A_112]: (k2_relat_1(B_111)=A_112 | ~r1_tarski(A_112, k2_relat_1(B_111)) | ~v5_relat_1(B_111, A_112) | ~v1_relat_1(B_111))), inference(resolution, [status(thm)], [c_173, c_2])).
% 12.67/5.54  tff(c_407, plain, (![A_5, B_7]: (k2_relat_1(k5_relat_1(A_5, B_7))=k2_relat_1(B_7) | ~v5_relat_1(B_7, k2_relat_1(k5_relat_1(A_5, B_7))) | ~v1_relat_1(B_7) | ~v1_relat_1(A_5))), inference(resolution, [status(thm)], [c_12, c_379])).
% 12.67/5.54  tff(c_4401, plain, (k2_relat_1(k5_relat_1('#skF_3', '#skF_4'))=k2_relat_1('#skF_4') | ~v5_relat_1('#skF_4', k2_relat_1(k6_partfun1('#skF_1'))) | ~v1_relat_1('#skF_4') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_4391, c_407])).
% 12.67/5.54  tff(c_4420, plain, (k2_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_158, c_159, c_236, c_101, c_101, c_4391, c_4401])).
% 12.67/5.54  tff(c_4422, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2830, c_4420])).
% 12.67/5.54  tff(c_4424, plain, (k2_relat_1('#skF_4')='#skF_1'), inference(splitRight, [status(thm)], [c_2828])).
% 12.67/5.54  tff(c_80, plain, (v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_245])).
% 12.67/5.54  tff(c_305, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_92, c_299])).
% 12.67/5.54  tff(c_312, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_84, c_305])).
% 12.67/5.54  tff(c_30, plain, (![A_14, B_16]: (k2_funct_1(A_14)=B_16 | k6_relat_1(k2_relat_1(A_14))!=k5_relat_1(B_16, A_14) | k2_relat_1(B_16)!=k1_relat_1(A_14) | ~v2_funct_1(A_14) | ~v1_funct_1(B_16) | ~v1_relat_1(B_16) | ~v1_funct_1(A_14) | ~v1_relat_1(A_14))), inference(cnfTransformation, [status(thm)], [f_96])).
% 12.67/5.54  tff(c_4475, plain, (![A_511, B_512]: (k2_funct_1(A_511)=B_512 | k6_partfun1(k2_relat_1(A_511))!=k5_relat_1(B_512, A_511) | k2_relat_1(B_512)!=k1_relat_1(A_511) | ~v2_funct_1(A_511) | ~v1_funct_1(B_512) | ~v1_relat_1(B_512) | ~v1_funct_1(A_511) | ~v1_relat_1(A_511))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_30])).
% 12.67/5.54  tff(c_4479, plain, (![B_512]: (k2_funct_1('#skF_3')=B_512 | k5_relat_1(B_512, '#skF_3')!=k6_partfun1('#skF_2') | k2_relat_1(B_512)!=k1_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_1(B_512) | ~v1_relat_1(B_512) | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_312, c_4475])).
% 12.67/5.54  tff(c_5488, plain, (![B_611]: (k2_funct_1('#skF_3')=B_611 | k5_relat_1(B_611, '#skF_3')!=k6_partfun1('#skF_2') | k2_relat_1(B_611)!=k1_relat_1('#skF_3') | ~v1_funct_1(B_611) | ~v1_relat_1(B_611))), inference(demodulation, [status(thm), theory('equality')], [c_158, c_96, c_80, c_4479])).
% 12.67/5.54  tff(c_5491, plain, (k2_funct_1('#skF_3')='#skF_4' | k5_relat_1('#skF_4', '#skF_3')!=k6_partfun1('#skF_2') | k2_relat_1('#skF_4')!=k1_relat_1('#skF_3') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_159, c_5488])).
% 12.67/5.54  tff(c_5500, plain, (k2_funct_1('#skF_3')='#skF_4' | k5_relat_1('#skF_4', '#skF_3')!=k6_partfun1('#skF_2') | k1_relat_1('#skF_3')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_90, c_4424, c_5491])).
% 12.67/5.54  tff(c_5501, plain, (k5_relat_1('#skF_4', '#skF_3')!=k6_partfun1('#skF_2') | k1_relat_1('#skF_3')!='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_74, c_5500])).
% 12.67/5.54  tff(c_5507, plain, (k1_relat_1('#skF_3')!='#skF_1'), inference(splitLeft, [status(thm)], [c_5501])).
% 12.67/5.54  tff(c_76, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_245])).
% 12.67/5.54  tff(c_5593, plain, (![A_625, C_626, B_627]: (k6_partfun1(A_625)=k5_relat_1(C_626, k2_funct_1(C_626)) | k1_xboole_0=B_627 | ~v2_funct_1(C_626) | k2_relset_1(A_625, B_627, C_626)!=B_627 | ~m1_subset_1(C_626, k1_zfmisc_1(k2_zfmisc_1(A_625, B_627))) | ~v1_funct_2(C_626, A_625, B_627) | ~v1_funct_1(C_626))), inference(cnfTransformation, [status(thm)], [f_219])).
% 12.67/5.54  tff(c_5599, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_partfun1('#skF_1') | k1_xboole_0='#skF_2' | ~v2_funct_1('#skF_3') | k2_relset_1('#skF_1', '#skF_2', '#skF_3')!='#skF_2' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_92, c_5593])).
% 12.67/5.54  tff(c_5608, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_partfun1('#skF_1') | k1_xboole_0='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_96, c_94, c_84, c_80, c_5599])).
% 12.67/5.54  tff(c_5609, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_partfun1('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_76, c_5608])).
% 12.67/5.54  tff(c_5629, plain, (r1_tarski(k2_relat_1(k6_partfun1('#skF_1')), k2_relat_1(k2_funct_1('#skF_3'))) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_5609, c_12])).
% 12.67/5.54  tff(c_5641, plain, (r1_tarski('#skF_1', k2_relat_1(k2_funct_1('#skF_3'))) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_158, c_101, c_5629])).
% 12.67/5.54  tff(c_5672, plain, (~v1_relat_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_5641])).
% 12.67/5.54  tff(c_5449, plain, (![C_608, B_609, A_610]: (m1_subset_1(k2_funct_1(C_608), k1_zfmisc_1(k2_zfmisc_1(B_609, A_610))) | k2_relset_1(A_610, B_609, C_608)!=B_609 | ~v2_funct_1(C_608) | ~m1_subset_1(C_608, k1_zfmisc_1(k2_zfmisc_1(A_610, B_609))) | ~v1_funct_2(C_608, A_610, B_609) | ~v1_funct_1(C_608))), inference(cnfTransformation, [status(thm)], [f_203])).
% 12.67/5.54  tff(c_32, plain, (![C_19, A_17, B_18]: (v1_relat_1(C_19) | ~m1_subset_1(C_19, k1_zfmisc_1(k2_zfmisc_1(A_17, B_18))))), inference(cnfTransformation, [status(thm)], [f_100])).
% 12.67/5.54  tff(c_7394, plain, (![C_681, A_682, B_683]: (v1_relat_1(k2_funct_1(C_681)) | k2_relset_1(A_682, B_683, C_681)!=B_683 | ~v2_funct_1(C_681) | ~m1_subset_1(C_681, k1_zfmisc_1(k2_zfmisc_1(A_682, B_683))) | ~v1_funct_2(C_681, A_682, B_683) | ~v1_funct_1(C_681))), inference(resolution, [status(thm)], [c_5449, c_32])).
% 12.67/5.54  tff(c_7439, plain, (v1_relat_1(k2_funct_1('#skF_3')) | k2_relset_1('#skF_1', '#skF_2', '#skF_3')!='#skF_2' | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_92, c_7394])).
% 12.67/5.54  tff(c_7483, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_96, c_94, c_80, c_84, c_7439])).
% 12.67/5.54  tff(c_7485, plain, $false, inference(negUnitSimplification, [status(thm)], [c_5672, c_7483])).
% 12.67/5.54  tff(c_7487, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_5641])).
% 12.67/5.54  tff(c_7486, plain, (r1_tarski('#skF_1', k2_relat_1(k2_funct_1('#skF_3')))), inference(splitRight, [status(thm)], [c_5641])).
% 12.67/5.54  tff(c_179, plain, (![B_77, A_78]: (k2_relat_1(B_77)=A_78 | ~r1_tarski(A_78, k2_relat_1(B_77)) | ~v5_relat_1(B_77, A_78) | ~v1_relat_1(B_77))), inference(resolution, [status(thm)], [c_173, c_2])).
% 12.67/5.54  tff(c_7503, plain, (k2_relat_1(k2_funct_1('#skF_3'))='#skF_1' | ~v5_relat_1(k2_funct_1('#skF_3'), '#skF_1') | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_7486, c_179])).
% 12.67/5.54  tff(c_7511, plain, (k2_relat_1(k2_funct_1('#skF_3'))='#skF_1' | ~v5_relat_1(k2_funct_1('#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_7487, c_7503])).
% 12.67/5.54  tff(c_9485, plain, (~v5_relat_1(k2_funct_1('#skF_3'), '#skF_1')), inference(splitLeft, [status(thm)], [c_7511])).
% 12.67/5.54  tff(c_34, plain, (![C_22, B_21, A_20]: (v5_relat_1(C_22, B_21) | ~m1_subset_1(C_22, k1_zfmisc_1(k2_zfmisc_1(A_20, B_21))))), inference(cnfTransformation, [status(thm)], [f_106])).
% 12.67/5.54  tff(c_11769, plain, (![C_823, A_824, B_825]: (v5_relat_1(k2_funct_1(C_823), A_824) | k2_relset_1(A_824, B_825, C_823)!=B_825 | ~v2_funct_1(C_823) | ~m1_subset_1(C_823, k1_zfmisc_1(k2_zfmisc_1(A_824, B_825))) | ~v1_funct_2(C_823, A_824, B_825) | ~v1_funct_1(C_823))), inference(resolution, [status(thm)], [c_5449, c_34])).
% 12.67/5.54  tff(c_11811, plain, (v5_relat_1(k2_funct_1('#skF_3'), '#skF_1') | k2_relset_1('#skF_1', '#skF_2', '#skF_3')!='#skF_2' | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_92, c_11769])).
% 12.67/5.54  tff(c_11852, plain, (v5_relat_1(k2_funct_1('#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_96, c_94, c_80, c_84, c_11811])).
% 12.67/5.54  tff(c_11854, plain, $false, inference(negUnitSimplification, [status(thm)], [c_9485, c_11852])).
% 12.67/5.54  tff(c_11855, plain, (k2_relat_1(k2_funct_1('#skF_3'))='#skF_1'), inference(splitRight, [status(thm)], [c_7511])).
% 12.67/5.54  tff(c_26, plain, (![A_13]: (k2_relat_1(k2_funct_1(A_13))=k1_relat_1(A_13) | ~v2_funct_1(A_13) | ~v1_funct_1(A_13) | ~v1_relat_1(A_13))), inference(cnfTransformation, [status(thm)], [f_79])).
% 12.67/5.54  tff(c_11881, plain, (k1_relat_1('#skF_3')='#skF_1' | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_11855, c_26])).
% 12.67/5.54  tff(c_11914, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_158, c_96, c_80, c_11881])).
% 12.67/5.54  tff(c_11916, plain, $false, inference(negUnitSimplification, [status(thm)], [c_5507, c_11914])).
% 12.67/5.54  tff(c_11917, plain, (k5_relat_1('#skF_4', '#skF_3')!=k6_partfun1('#skF_2')), inference(splitRight, [status(thm)], [c_5501])).
% 12.67/5.54  tff(c_4836, plain, (![D_555, A_552, F_554, E_556, B_553, C_557]: (k1_partfun1(A_552, B_553, C_557, D_555, E_556, F_554)=k5_relat_1(E_556, F_554) | ~m1_subset_1(F_554, k1_zfmisc_1(k2_zfmisc_1(C_557, D_555))) | ~v1_funct_1(F_554) | ~m1_subset_1(E_556, k1_zfmisc_1(k2_zfmisc_1(A_552, B_553))) | ~v1_funct_1(E_556))), inference(cnfTransformation, [status(thm)], [f_142])).
% 12.67/5.54  tff(c_4844, plain, (![A_552, B_553, E_556]: (k1_partfun1(A_552, B_553, '#skF_2', '#skF_1', E_556, '#skF_4')=k5_relat_1(E_556, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_556, k1_zfmisc_1(k2_zfmisc_1(A_552, B_553))) | ~v1_funct_1(E_556))), inference(resolution, [status(thm)], [c_86, c_4836])).
% 12.67/5.54  tff(c_4872, plain, (![A_559, B_560, E_561]: (k1_partfun1(A_559, B_560, '#skF_2', '#skF_1', E_561, '#skF_4')=k5_relat_1(E_561, '#skF_4') | ~m1_subset_1(E_561, k1_zfmisc_1(k2_zfmisc_1(A_559, B_560))) | ~v1_funct_1(E_561))), inference(demodulation, [status(thm), theory('equality')], [c_90, c_4844])).
% 12.67/5.54  tff(c_4881, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_92, c_4872])).
% 12.67/5.54  tff(c_4889, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_96, c_4881])).
% 12.67/5.54  tff(c_4534, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_477])).
% 12.67/5.54  tff(c_4894, plain, (~m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_4889, c_4534])).
% 12.67/5.54  tff(c_5117, plain, (![F_575, D_571, C_576, A_574, B_572, E_573]: (m1_subset_1(k1_partfun1(A_574, B_572, C_576, D_571, E_573, F_575), k1_zfmisc_1(k2_zfmisc_1(A_574, D_571))) | ~m1_subset_1(F_575, k1_zfmisc_1(k2_zfmisc_1(C_576, D_571))) | ~v1_funct_1(F_575) | ~m1_subset_1(E_573, k1_zfmisc_1(k2_zfmisc_1(A_574, B_572))) | ~v1_funct_1(E_573))), inference(cnfTransformation, [status(thm)], [f_132])).
% 12.67/5.54  tff(c_5172, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_4889, c_5117])).
% 12.67/5.54  tff(c_5196, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_96, c_92, c_90, c_86, c_5172])).
% 12.67/5.54  tff(c_5198, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4894, c_5196])).
% 12.67/5.54  tff(c_5199, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_477])).
% 12.67/5.54  tff(c_13988, plain, (![D_909, B_907, A_906, F_908, E_910, C_911]: (k1_partfun1(A_906, B_907, C_911, D_909, E_910, F_908)=k5_relat_1(E_910, F_908) | ~m1_subset_1(F_908, k1_zfmisc_1(k2_zfmisc_1(C_911, D_909))) | ~v1_funct_1(F_908) | ~m1_subset_1(E_910, k1_zfmisc_1(k2_zfmisc_1(A_906, B_907))) | ~v1_funct_1(E_910))), inference(cnfTransformation, [status(thm)], [f_142])).
% 12.67/5.54  tff(c_13996, plain, (![A_906, B_907, E_910]: (k1_partfun1(A_906, B_907, '#skF_2', '#skF_1', E_910, '#skF_4')=k5_relat_1(E_910, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_910, k1_zfmisc_1(k2_zfmisc_1(A_906, B_907))) | ~v1_funct_1(E_910))), inference(resolution, [status(thm)], [c_86, c_13988])).
% 12.67/5.54  tff(c_18772, plain, (![A_1073, B_1074, E_1075]: (k1_partfun1(A_1073, B_1074, '#skF_2', '#skF_1', E_1075, '#skF_4')=k5_relat_1(E_1075, '#skF_4') | ~m1_subset_1(E_1075, k1_zfmisc_1(k2_zfmisc_1(A_1073, B_1074))) | ~v1_funct_1(E_1075))), inference(demodulation, [status(thm), theory('equality')], [c_90, c_13996])).
% 12.67/5.54  tff(c_18784, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_92, c_18772])).
% 12.67/5.54  tff(c_18793, plain, (k5_relat_1('#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_96, c_5199, c_18784])).
% 12.67/5.54  tff(c_2829, plain, (v2_funct_1('#skF_4')), inference(splitRight, [status(thm)], [c_570])).
% 12.67/5.54  tff(c_4477, plain, (![B_512]: (k2_funct_1('#skF_4')=B_512 | k5_relat_1(B_512, '#skF_4')!=k6_partfun1('#skF_1') | k2_relat_1(B_512)!=k1_relat_1('#skF_4') | ~v2_funct_1('#skF_4') | ~v1_funct_1(B_512) | ~v1_relat_1(B_512) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_4424, c_4475])).
% 12.67/5.54  tff(c_14005, plain, (![B_912]: (k2_funct_1('#skF_4')=B_912 | k5_relat_1(B_912, '#skF_4')!=k6_partfun1('#skF_1') | k2_relat_1(B_912)!=k1_relat_1('#skF_4') | ~v1_funct_1(B_912) | ~v1_relat_1(B_912))), inference(demodulation, [status(thm), theory('equality')], [c_159, c_90, c_2829, c_4477])).
% 12.67/5.54  tff(c_14014, plain, (k2_funct_1('#skF_4')='#skF_3' | k5_relat_1('#skF_3', '#skF_4')!=k6_partfun1('#skF_1') | k2_relat_1('#skF_3')!=k1_relat_1('#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_158, c_14005])).
% 12.67/5.54  tff(c_14026, plain, (k2_funct_1('#skF_4')='#skF_3' | k5_relat_1('#skF_3', '#skF_4')!=k6_partfun1('#skF_1') | k1_relat_1('#skF_4')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_96, c_312, c_14014])).
% 12.67/5.54  tff(c_14061, plain, (k1_relat_1('#skF_4')!='#skF_2'), inference(splitLeft, [status(thm)], [c_14026])).
% 12.67/5.54  tff(c_4425, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_4424, c_313])).
% 12.67/5.54  tff(c_14322, plain, (![A_922, C_923, B_924]: (k6_partfun1(A_922)=k5_relat_1(C_923, k2_funct_1(C_923)) | k1_xboole_0=B_924 | ~v2_funct_1(C_923) | k2_relset_1(A_922, B_924, C_923)!=B_924 | ~m1_subset_1(C_923, k1_zfmisc_1(k2_zfmisc_1(A_922, B_924))) | ~v1_funct_2(C_923, A_922, B_924) | ~v1_funct_1(C_923))), inference(cnfTransformation, [status(thm)], [f_219])).
% 12.67/5.54  tff(c_14330, plain, (k5_relat_1('#skF_4', k2_funct_1('#skF_4'))=k6_partfun1('#skF_2') | k1_xboole_0='#skF_1' | ~v2_funct_1('#skF_4') | k2_relset_1('#skF_2', '#skF_1', '#skF_4')!='#skF_1' | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_86, c_14322])).
% 12.67/5.54  tff(c_14341, plain, (k5_relat_1('#skF_4', k2_funct_1('#skF_4'))=k6_partfun1('#skF_2') | k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_90, c_88, c_4425, c_2829, c_14330])).
% 12.67/5.54  tff(c_14342, plain, (k5_relat_1('#skF_4', k2_funct_1('#skF_4'))=k6_partfun1('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_78, c_14341])).
% 12.67/5.54  tff(c_14387, plain, (r1_tarski(k2_relat_1(k6_partfun1('#skF_2')), k2_relat_1(k2_funct_1('#skF_4'))) | ~v1_relat_1(k2_funct_1('#skF_4')) | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_14342, c_12])).
% 12.67/5.54  tff(c_14399, plain, (r1_tarski('#skF_2', k2_relat_1(k2_funct_1('#skF_4'))) | ~v1_relat_1(k2_funct_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_159, c_101, c_14387])).
% 12.67/5.54  tff(c_14444, plain, (~v1_relat_1(k2_funct_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_14399])).
% 12.67/5.54  tff(c_16052, plain, (![C_982, A_983, B_984]: (v1_relat_1(k2_funct_1(C_982)) | k2_relset_1(A_983, B_984, C_982)!=B_984 | ~v2_funct_1(C_982) | ~m1_subset_1(C_982, k1_zfmisc_1(k2_zfmisc_1(A_983, B_984))) | ~v1_funct_2(C_982, A_983, B_984) | ~v1_funct_1(C_982))), inference(resolution, [status(thm)], [c_5449, c_32])).
% 12.67/5.54  tff(c_16097, plain, (v1_relat_1(k2_funct_1('#skF_4')) | k2_relset_1('#skF_2', '#skF_1', '#skF_4')!='#skF_1' | ~v2_funct_1('#skF_4') | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_86, c_16052])).
% 12.67/5.54  tff(c_16138, plain, (v1_relat_1(k2_funct_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_90, c_88, c_2829, c_4425, c_16097])).
% 12.67/5.54  tff(c_16140, plain, $false, inference(negUnitSimplification, [status(thm)], [c_14444, c_16138])).
% 12.67/5.54  tff(c_16142, plain, (v1_relat_1(k2_funct_1('#skF_4'))), inference(splitRight, [status(thm)], [c_14399])).
% 12.67/5.54  tff(c_18, plain, (![A_9]: (v1_relat_1(k6_relat_1(A_9)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 12.67/5.54  tff(c_100, plain, (![A_9]: (v1_relat_1(k6_partfun1(A_9)))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_18])).
% 12.67/5.54  tff(c_246, plain, (![A_92, B_93]: (r1_tarski(k2_relat_1(k5_relat_1(A_92, B_93)), k2_relat_1(B_93)) | ~v1_relat_1(B_93) | ~v1_relat_1(A_92))), inference(cnfTransformation, [status(thm)], [f_44])).
% 12.67/5.54  tff(c_8, plain, (![B_4, A_3]: (v5_relat_1(B_4, A_3) | ~r1_tarski(k2_relat_1(B_4), A_3) | ~v1_relat_1(B_4))), inference(cnfTransformation, [status(thm)], [f_37])).
% 12.67/5.54  tff(c_255, plain, (![A_92, B_93]: (v5_relat_1(k5_relat_1(A_92, B_93), k2_relat_1(B_93)) | ~v1_relat_1(k5_relat_1(A_92, B_93)) | ~v1_relat_1(B_93) | ~v1_relat_1(A_92))), inference(resolution, [status(thm)], [c_246, c_8])).
% 12.67/5.54  tff(c_14378, plain, (v5_relat_1(k6_partfun1('#skF_2'), k2_relat_1(k2_funct_1('#skF_4'))) | ~v1_relat_1(k5_relat_1('#skF_4', k2_funct_1('#skF_4'))) | ~v1_relat_1(k2_funct_1('#skF_4')) | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_14342, c_255])).
% 12.67/5.54  tff(c_14393, plain, (v5_relat_1(k6_partfun1('#skF_2'), k2_relat_1(k2_funct_1('#skF_4'))) | ~v1_relat_1(k2_funct_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_159, c_100, c_14342, c_14378])).
% 12.67/5.54  tff(c_16176, plain, (v5_relat_1(k6_partfun1('#skF_2'), k2_relat_1(k2_funct_1('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_16142, c_14393])).
% 12.67/5.54  tff(c_10, plain, (![B_4, A_3]: (r1_tarski(k2_relat_1(B_4), A_3) | ~v5_relat_1(B_4, A_3) | ~v1_relat_1(B_4))), inference(cnfTransformation, [status(thm)], [f_37])).
% 12.67/5.54  tff(c_408, plain, (![B_4, B_111]: (k2_relat_1(B_4)=k2_relat_1(B_111) | ~v5_relat_1(B_111, k2_relat_1(B_4)) | ~v1_relat_1(B_111) | ~v5_relat_1(B_4, k2_relat_1(B_111)) | ~v1_relat_1(B_4))), inference(resolution, [status(thm)], [c_10, c_379])).
% 12.67/5.54  tff(c_16183, plain, (k2_relat_1(k6_partfun1('#skF_2'))=k2_relat_1(k2_funct_1('#skF_4')) | ~v1_relat_1(k6_partfun1('#skF_2')) | ~v5_relat_1(k2_funct_1('#skF_4'), k2_relat_1(k6_partfun1('#skF_2'))) | ~v1_relat_1(k2_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_16176, c_408])).
% 12.67/5.54  tff(c_16199, plain, (k2_relat_1(k2_funct_1('#skF_4'))='#skF_2' | ~v5_relat_1(k2_funct_1('#skF_4'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_16142, c_101, c_100, c_101, c_16183])).
% 12.67/5.54  tff(c_16224, plain, (~v5_relat_1(k2_funct_1('#skF_4'), '#skF_2')), inference(splitLeft, [status(thm)], [c_16199])).
% 12.67/5.54  tff(c_17996, plain, (![C_1048, A_1049, B_1050]: (v5_relat_1(k2_funct_1(C_1048), A_1049) | k2_relset_1(A_1049, B_1050, C_1048)!=B_1050 | ~v2_funct_1(C_1048) | ~m1_subset_1(C_1048, k1_zfmisc_1(k2_zfmisc_1(A_1049, B_1050))) | ~v1_funct_2(C_1048, A_1049, B_1050) | ~v1_funct_1(C_1048))), inference(resolution, [status(thm)], [c_5449, c_34])).
% 12.67/5.54  tff(c_18041, plain, (v5_relat_1(k2_funct_1('#skF_4'), '#skF_2') | k2_relset_1('#skF_2', '#skF_1', '#skF_4')!='#skF_1' | ~v2_funct_1('#skF_4') | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_86, c_17996])).
% 12.67/5.54  tff(c_18082, plain, (v5_relat_1(k2_funct_1('#skF_4'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_90, c_88, c_2829, c_4425, c_18041])).
% 12.67/5.54  tff(c_18084, plain, $false, inference(negUnitSimplification, [status(thm)], [c_16224, c_18082])).
% 12.67/5.54  tff(c_18085, plain, (k2_relat_1(k2_funct_1('#skF_4'))='#skF_2'), inference(splitRight, [status(thm)], [c_16199])).
% 12.67/5.54  tff(c_18113, plain, (k1_relat_1('#skF_4')='#skF_2' | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_18085, c_26])).
% 12.67/5.54  tff(c_18147, plain, (k1_relat_1('#skF_4')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_159, c_90, c_2829, c_18113])).
% 12.67/5.54  tff(c_18149, plain, $false, inference(negUnitSimplification, [status(thm)], [c_14061, c_18147])).
% 12.67/5.54  tff(c_18150, plain, (k5_relat_1('#skF_3', '#skF_4')!=k6_partfun1('#skF_1') | k2_funct_1('#skF_4')='#skF_3'), inference(splitRight, [status(thm)], [c_14026])).
% 12.67/5.54  tff(c_18771, plain, (k5_relat_1('#skF_3', '#skF_4')!=k6_partfun1('#skF_1')), inference(splitLeft, [status(thm)], [c_18150])).
% 12.67/5.54  tff(c_18842, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_18793, c_18771])).
% 12.67/5.54  tff(c_18843, plain, (k2_funct_1('#skF_4')='#skF_3'), inference(splitRight, [status(thm)], [c_18150])).
% 12.67/5.54  tff(c_18472, plain, (![A_1060, C_1061, B_1062]: (k6_partfun1(A_1060)=k5_relat_1(C_1061, k2_funct_1(C_1061)) | k1_xboole_0=B_1062 | ~v2_funct_1(C_1061) | k2_relset_1(A_1060, B_1062, C_1061)!=B_1062 | ~m1_subset_1(C_1061, k1_zfmisc_1(k2_zfmisc_1(A_1060, B_1062))) | ~v1_funct_2(C_1061, A_1060, B_1062) | ~v1_funct_1(C_1061))), inference(cnfTransformation, [status(thm)], [f_219])).
% 12.67/5.54  tff(c_18480, plain, (k5_relat_1('#skF_4', k2_funct_1('#skF_4'))=k6_partfun1('#skF_2') | k1_xboole_0='#skF_1' | ~v2_funct_1('#skF_4') | k2_relset_1('#skF_2', '#skF_1', '#skF_4')!='#skF_1' | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_86, c_18472])).
% 12.67/5.54  tff(c_18491, plain, (k5_relat_1('#skF_4', k2_funct_1('#skF_4'))=k6_partfun1('#skF_2') | k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_90, c_88, c_4425, c_2829, c_18480])).
% 12.67/5.54  tff(c_18492, plain, (k5_relat_1('#skF_4', k2_funct_1('#skF_4'))=k6_partfun1('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_78, c_18491])).
% 12.67/5.54  tff(c_18847, plain, (k5_relat_1('#skF_4', '#skF_3')=k6_partfun1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_18843, c_18492])).
% 12.67/5.54  tff(c_18857, plain, $false, inference(negUnitSimplification, [status(thm)], [c_11917, c_18847])).
% 12.67/5.54  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 12.67/5.54  
% 12.67/5.54  Inference rules
% 12.67/5.54  ----------------------
% 12.67/5.54  #Ref     : 0
% 12.67/5.54  #Sup     : 3797
% 12.67/5.54  #Fact    : 0
% 12.67/5.54  #Define  : 0
% 12.67/5.54  #Split   : 124
% 12.67/5.54  #Chain   : 0
% 12.67/5.54  #Close   : 0
% 12.67/5.54  
% 12.67/5.54  Ordering : KBO
% 12.67/5.54  
% 12.67/5.54  Simplification rules
% 12.67/5.54  ----------------------
% 12.67/5.54  #Subsume      : 580
% 12.67/5.54  #Demod        : 5952
% 12.67/5.54  #Tautology    : 918
% 12.67/5.54  #SimpNegUnit  : 298
% 12.67/5.54  #BackRed      : 100
% 12.67/5.54  
% 12.67/5.54  #Partial instantiations: 0
% 12.67/5.54  #Strategies tried      : 1
% 12.67/5.54  
% 12.67/5.54  Timing (in seconds)
% 12.67/5.54  ----------------------
% 12.67/5.55  Preprocessing        : 0.41
% 12.67/5.55  Parsing              : 0.21
% 12.67/5.55  CNF conversion       : 0.03
% 12.67/5.55  Main loop            : 4.32
% 12.67/5.55  Inferencing          : 1.31
% 12.67/5.55  Reduction            : 1.85
% 12.67/5.55  Demodulation         : 1.39
% 12.67/5.55  BG Simplification    : 0.09
% 12.67/5.55  Subsumption          : 0.78
% 12.67/5.55  Abstraction          : 0.15
% 12.67/5.55  MUC search           : 0.00
% 12.67/5.55  Cooper               : 0.00
% 12.67/5.55  Total                : 4.80
% 12.67/5.55  Index Insertion      : 0.00
% 12.67/5.55  Index Deletion       : 0.00
% 12.67/5.55  Index Matching       : 0.00
% 12.67/5.55  BG Taut test         : 0.00
%------------------------------------------------------------------------------
