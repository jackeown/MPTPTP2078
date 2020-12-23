%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:16:12 EST 2020

% Result     : Theorem 5.81s
% Output     : CNFRefutation 5.81s
% Verified   : 
% Statistics : Number of formulae       :  182 (13336 expanded)
%              Number of leaves         :   43 (5384 expanded)
%              Depth                    :   23
%              Number of atoms          :  441 (48877 expanded)
%              Number of equality atoms :   61 (2450 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    6 (   2 average)

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_102,axiom,(
    ! [A] :
      ( v1_partfun1(k6_partfun1(A),A)
      & m1_subset_1(k6_partfun1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_partfun1)).

tff(f_115,axiom,(
    ! [A,B] :
    ? [C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
      & v1_relat_1(C)
      & v4_relat_1(C,A)
      & v5_relat_1(C,B)
      & v1_funct_1(C)
      & v1_funct_2(C,A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc1_funct_2)).

tff(f_70,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => r2_relset_1(A,B,C,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',reflexivity_r2_relset_1)).

tff(f_158,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_funct_1(B)
          & v1_funct_2(B,A,A)
          & v3_funct_2(B,A,A)
          & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
       => ( r2_relset_1(A,A,k1_partfun1(A,A,A,A,B,k2_funct_2(A,B)),k6_partfun1(A))
          & r2_relset_1(A,A,k1_partfun1(A,A,A,A,k2_funct_2(A,B),B),k6_partfun1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_funct_2)).

tff(f_135,axiom,(
    ! [A,B] :
      ( ( v1_funct_1(B)
        & v1_funct_2(B,A,A)
        & v3_funct_2(B,A,A)
        & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
     => k2_funct_2(A,B) = k2_funct_1(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_funct_2)).

tff(f_98,axiom,(
    ! [A,B] :
      ( ( v1_funct_1(B)
        & v1_funct_2(B,A,A)
        & v3_funct_2(B,A,A)
        & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
     => ( v1_funct_1(k2_funct_2(A,B))
        & v1_funct_2(k2_funct_2(A,B),A,A)
        & v3_funct_2(k2_funct_2(A,B),A,A)
        & m1_subset_1(k2_funct_2(A,B),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_2)).

tff(f_34,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_32,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_82,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( ( v1_funct_1(C)
          & v3_funct_2(C,A,B) )
       => ( v1_funct_1(C)
          & v2_funct_1(C)
          & v2_funct_2(C,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_funct_2)).

tff(f_145,axiom,(
    ! [A,B] :
      ( ( v1_funct_1(B)
        & v1_funct_2(B,A,A)
        & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
     => k1_relset_1(A,A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_funct_2)).

tff(f_64,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_60,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => k2_funct_1(k2_funct_1(A)) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_funct_1)).

tff(f_137,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_44,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k5_relat_1(A,k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))
          & k5_relat_1(k2_funct_1(A),A) = k6_relat_1(k2_relat_1(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_funct_1)).

tff(f_125,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(c_34,plain,(
    ! [A_21] : m1_subset_1(k6_partfun1(A_21),k1_zfmisc_1(k2_zfmisc_1(A_21,A_21))) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_46,plain,(
    ! [A_22,B_23] : m1_subset_1('#skF_1'(A_22,B_23),k1_zfmisc_1(k2_zfmisc_1(A_22,B_23))) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_2488,plain,(
    ! [A_203,B_204,C_205,D_206] :
      ( r2_relset_1(A_203,B_204,C_205,C_205)
      | ~ m1_subset_1(D_206,k1_zfmisc_1(k2_zfmisc_1(A_203,B_204)))
      | ~ m1_subset_1(C_205,k1_zfmisc_1(k2_zfmisc_1(A_203,B_204))) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_2498,plain,(
    ! [A_207,B_208,C_209] :
      ( r2_relset_1(A_207,B_208,C_209,C_209)
      | ~ m1_subset_1(C_209,k1_zfmisc_1(k2_zfmisc_1(A_207,B_208))) ) ),
    inference(resolution,[status(thm)],[c_46,c_2488])).

tff(c_2506,plain,(
    ! [A_21] : r2_relset_1(A_21,A_21,k6_partfun1(A_21),k6_partfun1(A_21)) ),
    inference(resolution,[status(thm)],[c_34,c_2498])).

tff(c_64,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_62,plain,(
    v1_funct_2('#skF_3','#skF_2','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_60,plain,(
    v3_funct_2('#skF_3','#skF_2','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_58,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_2568,plain,(
    ! [A_221,B_222] :
      ( k2_funct_2(A_221,B_222) = k2_funct_1(B_222)
      | ~ m1_subset_1(B_222,k1_zfmisc_1(k2_zfmisc_1(A_221,A_221)))
      | ~ v3_funct_2(B_222,A_221,A_221)
      | ~ v1_funct_2(B_222,A_221,A_221)
      | ~ v1_funct_1(B_222) ) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_2578,plain,
    ( k2_funct_2('#skF_2','#skF_3') = k2_funct_1('#skF_3')
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_58,c_2568])).

tff(c_2585,plain,(
    k2_funct_2('#skF_2','#skF_3') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_60,c_2578])).

tff(c_2548,plain,(
    ! [A_217,B_218] :
      ( v1_funct_1(k2_funct_2(A_217,B_218))
      | ~ m1_subset_1(B_218,k1_zfmisc_1(k2_zfmisc_1(A_217,A_217)))
      | ~ v3_funct_2(B_218,A_217,A_217)
      | ~ v1_funct_2(B_218,A_217,A_217)
      | ~ v1_funct_1(B_218) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_2558,plain,
    ( v1_funct_1(k2_funct_2('#skF_2','#skF_3'))
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_58,c_2548])).

tff(c_2565,plain,(
    v1_funct_1(k2_funct_2('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_60,c_2558])).

tff(c_2586,plain,(
    v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2585,c_2565])).

tff(c_4,plain,(
    ! [A_4,B_5] : v1_relat_1(k2_zfmisc_1(A_4,B_5)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_84,plain,(
    ! [B_51,A_52] :
      ( v1_relat_1(B_51)
      | ~ m1_subset_1(B_51,k1_zfmisc_1(A_52))
      | ~ v1_relat_1(A_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_90,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_2')) ),
    inference(resolution,[status(thm)],[c_58,c_84])).

tff(c_96,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_90])).

tff(c_2450,plain,(
    ! [C_191,A_192,B_193] :
      ( v2_funct_1(C_191)
      | ~ v3_funct_2(C_191,A_192,B_193)
      | ~ v1_funct_1(C_191)
      | ~ m1_subset_1(C_191,k1_zfmisc_1(k2_zfmisc_1(A_192,B_193))) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_2459,plain,
    ( v2_funct_1('#skF_3')
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_58,c_2450])).

tff(c_2466,plain,(
    v2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_60,c_2459])).

tff(c_2692,plain,(
    ! [A_234,B_235] :
      ( m1_subset_1(k2_funct_2(A_234,B_235),k1_zfmisc_1(k2_zfmisc_1(A_234,A_234)))
      | ~ m1_subset_1(B_235,k1_zfmisc_1(k2_zfmisc_1(A_234,A_234)))
      | ~ v3_funct_2(B_235,A_234,A_234)
      | ~ v1_funct_2(B_235,A_234,A_234)
      | ~ v1_funct_1(B_235) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_2722,plain,
    ( m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2')))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2')))
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_2585,c_2692])).

tff(c_2736,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_60,c_58,c_2722])).

tff(c_2,plain,(
    ! [B_3,A_1] :
      ( v1_relat_1(B_3)
      | ~ m1_subset_1(B_3,k1_zfmisc_1(A_1))
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_2763,plain,
    ( v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_2')) ),
    inference(resolution,[status(thm)],[c_2736,c_2])).

tff(c_2789,plain,(
    v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_2763])).

tff(c_2611,plain,(
    ! [A_228,B_229] :
      ( v3_funct_2(k2_funct_2(A_228,B_229),A_228,A_228)
      | ~ m1_subset_1(B_229,k1_zfmisc_1(k2_zfmisc_1(A_228,A_228)))
      | ~ v3_funct_2(B_229,A_228,A_228)
      | ~ v1_funct_2(B_229,A_228,A_228)
      | ~ v1_funct_1(B_229) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_2618,plain,
    ( v3_funct_2(k2_funct_2('#skF_2','#skF_3'),'#skF_2','#skF_2')
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_58,c_2611])).

tff(c_2625,plain,(
    v3_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_60,c_2585,c_2618])).

tff(c_20,plain,(
    ! [C_18,A_16,B_17] :
      ( v2_funct_1(C_18)
      | ~ v3_funct_2(C_18,A_16,B_17)
      | ~ v1_funct_1(C_18)
      | ~ m1_subset_1(C_18,k1_zfmisc_1(k2_zfmisc_1(A_16,B_17))) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_2757,plain,
    ( v2_funct_1(k2_funct_1('#skF_3'))
    | ~ v3_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_2')
    | ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_2736,c_20])).

tff(c_2785,plain,(
    v2_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2586,c_2625,c_2757])).

tff(c_2594,plain,(
    ! [A_224,B_225] :
      ( v1_funct_2(k2_funct_2(A_224,B_225),A_224,A_224)
      | ~ m1_subset_1(B_225,k1_zfmisc_1(k2_zfmisc_1(A_224,A_224)))
      | ~ v3_funct_2(B_225,A_224,A_224)
      | ~ v1_funct_2(B_225,A_224,A_224)
      | ~ v1_funct_1(B_225) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_2601,plain,
    ( v1_funct_2(k2_funct_2('#skF_2','#skF_3'),'#skF_2','#skF_2')
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_58,c_2594])).

tff(c_2608,plain,(
    v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_60,c_2585,c_2601])).

tff(c_54,plain,(
    ! [A_34,B_35] :
      ( k1_relset_1(A_34,A_34,B_35) = A_34
      | ~ m1_subset_1(B_35,k1_zfmisc_1(k2_zfmisc_1(A_34,A_34)))
      | ~ v1_funct_2(B_35,A_34,A_34)
      | ~ v1_funct_1(B_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_2749,plain,
    ( k1_relset_1('#skF_2','#skF_2',k2_funct_1('#skF_3')) = '#skF_2'
    | ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_2')
    | ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_2736,c_54])).

tff(c_2778,plain,(
    k1_relset_1('#skF_2','#skF_2',k2_funct_1('#skF_3')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2586,c_2608,c_2749])).

tff(c_14,plain,(
    ! [A_9,B_10,C_11] :
      ( k1_relset_1(A_9,B_10,C_11) = k1_relat_1(C_11)
      | ~ m1_subset_1(C_11,k1_zfmisc_1(k2_zfmisc_1(A_9,B_10))) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_2786,plain,(
    k1_relset_1('#skF_2','#skF_2',k2_funct_1('#skF_3')) = k1_relat_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_2736,c_14])).

tff(c_2843,plain,(
    k1_relat_1(k2_funct_1('#skF_3')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2778,c_2786])).

tff(c_12,plain,(
    ! [A_8] :
      ( k2_funct_1(k2_funct_1(A_8)) = A_8
      | ~ v2_funct_1(A_8)
      | ~ v1_funct_1(A_8)
      | ~ v1_relat_1(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_52,plain,(
    ! [A_33] : k6_relat_1(A_33) = k6_partfun1(A_33) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_8,plain,(
    ! [A_6] :
      ( k5_relat_1(A_6,k2_funct_1(A_6)) = k6_relat_1(k1_relat_1(A_6))
      | ~ v2_funct_1(A_6)
      | ~ v1_funct_1(A_6)
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_2426,plain,(
    ! [A_189] :
      ( k5_relat_1(A_189,k2_funct_1(A_189)) = k6_partfun1(k1_relat_1(A_189))
      | ~ v2_funct_1(A_189)
      | ~ v1_funct_1(A_189)
      | ~ v1_relat_1(A_189) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_8])).

tff(c_2435,plain,(
    ! [A_8] :
      ( k6_partfun1(k1_relat_1(k2_funct_1(A_8))) = k5_relat_1(k2_funct_1(A_8),A_8)
      | ~ v2_funct_1(k2_funct_1(A_8))
      | ~ v1_funct_1(k2_funct_1(A_8))
      | ~ v1_relat_1(k2_funct_1(A_8))
      | ~ v2_funct_1(A_8)
      | ~ v1_funct_1(A_8)
      | ~ v1_relat_1(A_8) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_2426])).

tff(c_2847,plain,
    ( k5_relat_1(k2_funct_1('#skF_3'),'#skF_3') = k6_partfun1('#skF_2')
    | ~ v2_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_2843,c_2435])).

tff(c_2851,plain,(
    k5_relat_1(k2_funct_1('#skF_3'),'#skF_3') = k6_partfun1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_64,c_2466,c_2789,c_2586,c_2785,c_2847])).

tff(c_24,plain,(
    ! [A_19,B_20] :
      ( m1_subset_1(k2_funct_2(A_19,B_20),k1_zfmisc_1(k2_zfmisc_1(A_19,A_19)))
      | ~ m1_subset_1(B_20,k1_zfmisc_1(k2_zfmisc_1(A_19,A_19)))
      | ~ v3_funct_2(B_20,A_19,A_19)
      | ~ v1_funct_2(B_20,A_19,A_19)
      | ~ v1_funct_1(B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_2809,plain,(
    ! [C_238,B_240,E_241,F_239,A_237,D_236] :
      ( k1_partfun1(A_237,B_240,C_238,D_236,E_241,F_239) = k5_relat_1(E_241,F_239)
      | ~ m1_subset_1(F_239,k1_zfmisc_1(k2_zfmisc_1(C_238,D_236)))
      | ~ v1_funct_1(F_239)
      | ~ m1_subset_1(E_241,k1_zfmisc_1(k2_zfmisc_1(A_237,B_240)))
      | ~ v1_funct_1(E_241) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_2819,plain,(
    ! [A_237,B_240,E_241] :
      ( k1_partfun1(A_237,B_240,'#skF_2','#skF_2',E_241,'#skF_3') = k5_relat_1(E_241,'#skF_3')
      | ~ v1_funct_1('#skF_3')
      | ~ m1_subset_1(E_241,k1_zfmisc_1(k2_zfmisc_1(A_237,B_240)))
      | ~ v1_funct_1(E_241) ) ),
    inference(resolution,[status(thm)],[c_58,c_2809])).

tff(c_2853,plain,(
    ! [A_242,B_243,E_244] :
      ( k1_partfun1(A_242,B_243,'#skF_2','#skF_2',E_244,'#skF_3') = k5_relat_1(E_244,'#skF_3')
      | ~ m1_subset_1(E_244,k1_zfmisc_1(k2_zfmisc_1(A_242,B_243)))
      | ~ v1_funct_1(E_244) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_2819])).

tff(c_3662,plain,(
    ! [A_262,B_263] :
      ( k1_partfun1(A_262,A_262,'#skF_2','#skF_2',k2_funct_2(A_262,B_263),'#skF_3') = k5_relat_1(k2_funct_2(A_262,B_263),'#skF_3')
      | ~ v1_funct_1(k2_funct_2(A_262,B_263))
      | ~ m1_subset_1(B_263,k1_zfmisc_1(k2_zfmisc_1(A_262,A_262)))
      | ~ v3_funct_2(B_263,A_262,A_262)
      | ~ v1_funct_2(B_263,A_262,A_262)
      | ~ v1_funct_1(B_263) ) ),
    inference(resolution,[status(thm)],[c_24,c_2853])).

tff(c_3677,plain,
    ( k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2',k2_funct_2('#skF_2','#skF_3'),'#skF_3') = k5_relat_1(k2_funct_2('#skF_2','#skF_3'),'#skF_3')
    | ~ v1_funct_1(k2_funct_2('#skF_2','#skF_3'))
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_58,c_3662])).

tff(c_3692,plain,(
    k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2',k2_funct_1('#skF_3'),'#skF_3') = k6_partfun1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_60,c_2586,c_2585,c_2851,c_2585,c_2585,c_3677])).

tff(c_224,plain,(
    ! [A_78,B_79,C_80,D_81] :
      ( r2_relset_1(A_78,B_79,C_80,C_80)
      | ~ m1_subset_1(D_81,k1_zfmisc_1(k2_zfmisc_1(A_78,B_79)))
      | ~ m1_subset_1(C_80,k1_zfmisc_1(k2_zfmisc_1(A_78,B_79))) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_234,plain,(
    ! [A_82,B_83,C_84] :
      ( r2_relset_1(A_82,B_83,C_84,C_84)
      | ~ m1_subset_1(C_84,k1_zfmisc_1(k2_zfmisc_1(A_82,B_83))) ) ),
    inference(resolution,[status(thm)],[c_46,c_224])).

tff(c_242,plain,(
    ! [A_21] : r2_relset_1(A_21,A_21,k6_partfun1(A_21),k6_partfun1(A_21)) ),
    inference(resolution,[status(thm)],[c_34,c_234])).

tff(c_302,plain,(
    ! [A_94,B_95] :
      ( k2_funct_2(A_94,B_95) = k2_funct_1(B_95)
      | ~ m1_subset_1(B_95,k1_zfmisc_1(k2_zfmisc_1(A_94,A_94)))
      | ~ v3_funct_2(B_95,A_94,A_94)
      | ~ v1_funct_2(B_95,A_94,A_94)
      | ~ v1_funct_1(B_95) ) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_312,plain,
    ( k2_funct_2('#skF_2','#skF_3') = k2_funct_1('#skF_3')
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_58,c_302])).

tff(c_319,plain,(
    k2_funct_2('#skF_2','#skF_3') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_60,c_312])).

tff(c_364,plain,(
    ! [A_108,B_109] :
      ( m1_subset_1(k2_funct_2(A_108,B_109),k1_zfmisc_1(k2_zfmisc_1(A_108,A_108)))
      | ~ m1_subset_1(B_109,k1_zfmisc_1(k2_zfmisc_1(A_108,A_108)))
      | ~ v3_funct_2(B_109,A_108,A_108)
      | ~ v1_funct_2(B_109,A_108,A_108)
      | ~ v1_funct_1(B_109) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_394,plain,
    ( m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2')))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2')))
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_319,c_364])).

tff(c_408,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_60,c_58,c_394])).

tff(c_435,plain,
    ( v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_2')) ),
    inference(resolution,[status(thm)],[c_408,c_2])).

tff(c_461,plain,(
    v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_435])).

tff(c_279,plain,(
    ! [A_91,B_92] :
      ( v1_funct_1(k2_funct_2(A_91,B_92))
      | ~ m1_subset_1(B_92,k1_zfmisc_1(k2_zfmisc_1(A_91,A_91)))
      | ~ v3_funct_2(B_92,A_91,A_91)
      | ~ v1_funct_2(B_92,A_91,A_91)
      | ~ v1_funct_1(B_92) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_289,plain,
    ( v1_funct_1(k2_funct_2('#skF_2','#skF_3'))
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_58,c_279])).

tff(c_296,plain,(
    v1_funct_1(k2_funct_2('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_60,c_289])).

tff(c_320,plain,(
    v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_319,c_296])).

tff(c_345,plain,(
    ! [A_102,B_103] :
      ( v3_funct_2(k2_funct_2(A_102,B_103),A_102,A_102)
      | ~ m1_subset_1(B_103,k1_zfmisc_1(k2_zfmisc_1(A_102,A_102)))
      | ~ v3_funct_2(B_103,A_102,A_102)
      | ~ v1_funct_2(B_103,A_102,A_102)
      | ~ v1_funct_1(B_103) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_352,plain,
    ( v3_funct_2(k2_funct_2('#skF_2','#skF_3'),'#skF_2','#skF_2')
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_58,c_345])).

tff(c_359,plain,(
    v3_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_60,c_319,c_352])).

tff(c_429,plain,
    ( v2_funct_1(k2_funct_1('#skF_3'))
    | ~ v3_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_2')
    | ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_408,c_20])).

tff(c_457,plain,(
    v2_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_320,c_359,c_429])).

tff(c_328,plain,(
    ! [A_98,B_99] :
      ( v1_funct_2(k2_funct_2(A_98,B_99),A_98,A_98)
      | ~ m1_subset_1(B_99,k1_zfmisc_1(k2_zfmisc_1(A_98,A_98)))
      | ~ v3_funct_2(B_99,A_98,A_98)
      | ~ v1_funct_2(B_99,A_98,A_98)
      | ~ v1_funct_1(B_99) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_335,plain,
    ( v1_funct_2(k2_funct_2('#skF_2','#skF_3'),'#skF_2','#skF_2')
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_58,c_328])).

tff(c_342,plain,(
    v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_60,c_319,c_335])).

tff(c_50,plain,(
    ! [A_31,B_32] :
      ( k2_funct_2(A_31,B_32) = k2_funct_1(B_32)
      | ~ m1_subset_1(B_32,k1_zfmisc_1(k2_zfmisc_1(A_31,A_31)))
      | ~ v3_funct_2(B_32,A_31,A_31)
      | ~ v1_funct_2(B_32,A_31,A_31)
      | ~ v1_funct_1(B_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_415,plain,
    ( k2_funct_2('#skF_2',k2_funct_1('#skF_3')) = k2_funct_1(k2_funct_1('#skF_3'))
    | ~ v3_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_2')
    | ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_2')
    | ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_408,c_50])).

tff(c_444,plain,(
    k2_funct_2('#skF_2',k2_funct_1('#skF_3')) = k2_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_320,c_342,c_359,c_415])).

tff(c_494,plain,
    ( m1_subset_1(k2_funct_1(k2_funct_1('#skF_3')),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2')))
    | ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2')))
    | ~ v3_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_2')
    | ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_2')
    | ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_444,c_24])).

tff(c_498,plain,(
    m1_subset_1(k2_funct_1(k2_funct_1('#skF_3')),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_320,c_342,c_359,c_408,c_494])).

tff(c_578,plain,
    ( v1_relat_1(k2_funct_1(k2_funct_1('#skF_3')))
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_2')) ),
    inference(resolution,[status(thm)],[c_498,c_2])).

tff(c_613,plain,(
    v1_relat_1(k2_funct_1(k2_funct_1('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_578])).

tff(c_30,plain,(
    ! [A_19,B_20] :
      ( v1_funct_1(k2_funct_2(A_19,B_20))
      | ~ m1_subset_1(B_20,k1_zfmisc_1(k2_zfmisc_1(A_19,A_19)))
      | ~ v3_funct_2(B_20,A_19,A_19)
      | ~ v1_funct_2(B_20,A_19,A_19)
      | ~ v1_funct_1(B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_418,plain,
    ( v1_funct_1(k2_funct_2('#skF_2',k2_funct_1('#skF_3')))
    | ~ v3_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_2')
    | ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_2')
    | ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_408,c_30])).

tff(c_447,plain,(
    v1_funct_1(k2_funct_2('#skF_2',k2_funct_1('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_320,c_342,c_359,c_418])).

tff(c_490,plain,(
    v1_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_444,c_447])).

tff(c_26,plain,(
    ! [A_19,B_20] :
      ( v3_funct_2(k2_funct_2(A_19,B_20),A_19,A_19)
      | ~ m1_subset_1(B_20,k1_zfmisc_1(k2_zfmisc_1(A_19,A_19)))
      | ~ v3_funct_2(B_20,A_19,A_19)
      | ~ v1_funct_2(B_20,A_19,A_19)
      | ~ v1_funct_1(B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_410,plain,
    ( v3_funct_2(k2_funct_2('#skF_2',k2_funct_1('#skF_3')),'#skF_2','#skF_2')
    | ~ v3_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_2')
    | ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_2')
    | ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_408,c_26])).

tff(c_438,plain,(
    v3_funct_2(k2_funct_2('#skF_2',k2_funct_1('#skF_3')),'#skF_2','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_320,c_342,c_359,c_410])).

tff(c_489,plain,(
    v3_funct_2(k2_funct_1(k2_funct_1('#skF_3')),'#skF_2','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_444,c_438])).

tff(c_572,plain,
    ( v2_funct_1(k2_funct_1(k2_funct_1('#skF_3')))
    | ~ v3_funct_2(k2_funct_1(k2_funct_1('#skF_3')),'#skF_2','#skF_2')
    | ~ v1_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) ),
    inference(resolution,[status(thm)],[c_498,c_20])).

tff(c_609,plain,(
    v2_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_490,c_489,c_572])).

tff(c_28,plain,(
    ! [A_19,B_20] :
      ( v1_funct_2(k2_funct_2(A_19,B_20),A_19,A_19)
      | ~ m1_subset_1(B_20,k1_zfmisc_1(k2_zfmisc_1(A_19,A_19)))
      | ~ v3_funct_2(B_20,A_19,A_19)
      | ~ v1_funct_2(B_20,A_19,A_19)
      | ~ v1_funct_1(B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_412,plain,
    ( v1_funct_2(k2_funct_2('#skF_2',k2_funct_1('#skF_3')),'#skF_2','#skF_2')
    | ~ v3_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_2')
    | ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_2')
    | ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_408,c_28])).

tff(c_441,plain,(
    v1_funct_2(k2_funct_2('#skF_2',k2_funct_1('#skF_3')),'#skF_2','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_320,c_342,c_359,c_412])).

tff(c_488,plain,(
    v1_funct_2(k2_funct_1(k2_funct_1('#skF_3')),'#skF_2','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_444,c_441])).

tff(c_564,plain,
    ( k1_relset_1('#skF_2','#skF_2',k2_funct_1(k2_funct_1('#skF_3'))) = '#skF_2'
    | ~ v1_funct_2(k2_funct_1(k2_funct_1('#skF_3')),'#skF_2','#skF_2')
    | ~ v1_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) ),
    inference(resolution,[status(thm)],[c_498,c_54])).

tff(c_602,plain,(
    k1_relset_1('#skF_2','#skF_2',k2_funct_1(k2_funct_1('#skF_3'))) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_490,c_488,c_564])).

tff(c_610,plain,(
    k1_relset_1('#skF_2','#skF_2',k2_funct_1(k2_funct_1('#skF_3'))) = k1_relat_1(k2_funct_1(k2_funct_1('#skF_3'))) ),
    inference(resolution,[status(thm)],[c_498,c_14])).

tff(c_925,plain,(
    k1_relat_1(k2_funct_1(k2_funct_1('#skF_3'))) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_602,c_610])).

tff(c_174,plain,(
    ! [A_65] :
      ( k5_relat_1(A_65,k2_funct_1(A_65)) = k6_partfun1(k1_relat_1(A_65))
      | ~ v2_funct_1(A_65)
      | ~ v1_funct_1(A_65)
      | ~ v1_relat_1(A_65) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_8])).

tff(c_1056,plain,(
    ! [A_130] :
      ( k6_partfun1(k1_relat_1(k2_funct_1(A_130))) = k5_relat_1(k2_funct_1(A_130),A_130)
      | ~ v2_funct_1(k2_funct_1(A_130))
      | ~ v1_funct_1(k2_funct_1(A_130))
      | ~ v1_relat_1(k2_funct_1(A_130))
      | ~ v2_funct_1(A_130)
      | ~ v1_funct_1(A_130)
      | ~ v1_relat_1(A_130) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_174])).

tff(c_186,plain,(
    ! [C_66,A_67,B_68] :
      ( v2_funct_1(C_66)
      | ~ v3_funct_2(C_66,A_67,B_68)
      | ~ v1_funct_1(C_66)
      | ~ m1_subset_1(C_66,k1_zfmisc_1(k2_zfmisc_1(A_67,B_68))) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_195,plain,
    ( v2_funct_1('#skF_3')
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_58,c_186])).

tff(c_202,plain,(
    v2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_60,c_195])).

tff(c_558,plain,
    ( k2_funct_2('#skF_2',k2_funct_1(k2_funct_1('#skF_3'))) = k2_funct_1(k2_funct_1(k2_funct_1('#skF_3')))
    | ~ v3_funct_2(k2_funct_1(k2_funct_1('#skF_3')),'#skF_2','#skF_2')
    | ~ v1_funct_2(k2_funct_1(k2_funct_1('#skF_3')),'#skF_2','#skF_2')
    | ~ v1_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) ),
    inference(resolution,[status(thm)],[c_498,c_50])).

tff(c_596,plain,(
    k2_funct_2('#skF_2',k2_funct_1(k2_funct_1('#skF_3'))) = k2_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_490,c_488,c_489,c_558])).

tff(c_709,plain,
    ( k2_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) = k2_funct_2('#skF_2','#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_596])).

tff(c_715,plain,(
    k2_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_64,c_202,c_319,c_709])).

tff(c_6,plain,(
    ! [A_6] :
      ( k5_relat_1(k2_funct_1(A_6),A_6) = k6_relat_1(k2_relat_1(A_6))
      | ~ v2_funct_1(A_6)
      | ~ v1_funct_1(A_6)
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_162,plain,(
    ! [A_64] :
      ( k5_relat_1(k2_funct_1(A_64),A_64) = k6_partfun1(k2_relat_1(A_64))
      | ~ v2_funct_1(A_64)
      | ~ v1_funct_1(A_64)
      | ~ v1_relat_1(A_64) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_6])).

tff(c_856,plain,(
    ! [A_128] :
      ( k6_partfun1(k2_relat_1(k2_funct_1(A_128))) = k5_relat_1(A_128,k2_funct_1(A_128))
      | ~ v2_funct_1(k2_funct_1(A_128))
      | ~ v1_funct_1(k2_funct_1(A_128))
      | ~ v1_relat_1(k2_funct_1(A_128))
      | ~ v2_funct_1(A_128)
      | ~ v1_funct_1(A_128)
      | ~ v1_relat_1(A_128) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_162])).

tff(c_911,plain,
    ( k6_partfun1(k2_relat_1(k2_funct_1(k2_funct_1(k2_funct_1('#skF_3'))))) = k5_relat_1(k2_funct_1(k2_funct_1('#skF_3')),k2_funct_1('#skF_3'))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1('#skF_3'))))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1('#skF_3'))))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1('#skF_3'))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1('#skF_3')))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1('#skF_3')))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1('#skF_3'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_715,c_856])).

tff(c_923,plain,(
    k5_relat_1(k2_funct_1(k2_funct_1('#skF_3')),k2_funct_1('#skF_3')) = k6_partfun1(k2_relat_1(k2_funct_1('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_613,c_490,c_609,c_461,c_715,c_320,c_715,c_457,c_715,c_715,c_911])).

tff(c_945,plain,
    ( k6_partfun1(k2_relat_1(k2_funct_1('#skF_3'))) = k5_relat_1('#skF_3',k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_923])).

tff(c_955,plain,(
    k6_partfun1(k2_relat_1(k2_funct_1('#skF_3'))) = k5_relat_1('#skF_3',k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_64,c_202,c_945])).

tff(c_959,plain,(
    k5_relat_1(k2_funct_1(k2_funct_1('#skF_3')),k2_funct_1('#skF_3')) = k5_relat_1('#skF_3',k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_955,c_923])).

tff(c_1065,plain,
    ( k6_partfun1(k1_relat_1(k2_funct_1(k2_funct_1('#skF_3')))) = k5_relat_1('#skF_3',k2_funct_1('#skF_3'))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1('#skF_3')))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1('#skF_3')))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1('#skF_3')))
    | ~ v2_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1056,c_959])).

tff(c_1132,plain,(
    k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_partfun1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_461,c_320,c_457,c_613,c_490,c_609,c_925,c_1065])).

tff(c_466,plain,(
    ! [E_115,F_113,A_111,B_114,D_110,C_112] :
      ( k1_partfun1(A_111,B_114,C_112,D_110,E_115,F_113) = k5_relat_1(E_115,F_113)
      | ~ m1_subset_1(F_113,k1_zfmisc_1(k2_zfmisc_1(C_112,D_110)))
      | ~ v1_funct_1(F_113)
      | ~ m1_subset_1(E_115,k1_zfmisc_1(k2_zfmisc_1(A_111,B_114)))
      | ~ v1_funct_1(E_115) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_468,plain,(
    ! [A_111,B_114,E_115] :
      ( k1_partfun1(A_111,B_114,'#skF_2','#skF_2',E_115,k2_funct_1('#skF_3')) = k5_relat_1(E_115,k2_funct_1('#skF_3'))
      | ~ v1_funct_1(k2_funct_1('#skF_3'))
      | ~ m1_subset_1(E_115,k1_zfmisc_1(k2_zfmisc_1(A_111,B_114)))
      | ~ v1_funct_1(E_115) ) ),
    inference(resolution,[status(thm)],[c_408,c_466])).

tff(c_2306,plain,(
    ! [A_178,B_179,E_180] :
      ( k1_partfun1(A_178,B_179,'#skF_2','#skF_2',E_180,k2_funct_1('#skF_3')) = k5_relat_1(E_180,k2_funct_1('#skF_3'))
      | ~ m1_subset_1(E_180,k1_zfmisc_1(k2_zfmisc_1(A_178,B_179)))
      | ~ v1_funct_1(E_180) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_320,c_468])).

tff(c_2339,plain,
    ( k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2','#skF_3',k2_funct_1('#skF_3')) = k5_relat_1('#skF_3',k2_funct_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_58,c_2306])).

tff(c_2358,plain,(
    k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2','#skF_3',k2_funct_1('#skF_3')) = k6_partfun1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_1132,c_2339])).

tff(c_56,plain,
    ( ~ r2_relset_1('#skF_2','#skF_2',k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2',k2_funct_2('#skF_2','#skF_3'),'#skF_3'),k6_partfun1('#skF_2'))
    | ~ r2_relset_1('#skF_2','#skF_2',k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2','#skF_3',k2_funct_2('#skF_2','#skF_3')),k6_partfun1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_126,plain,(
    ~ r2_relset_1('#skF_2','#skF_2',k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2','#skF_3',k2_funct_2('#skF_2','#skF_3')),k6_partfun1('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_56])).

tff(c_321,plain,(
    ~ r2_relset_1('#skF_2','#skF_2',k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2','#skF_3',k2_funct_1('#skF_3')),k6_partfun1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_319,c_126])).

tff(c_2385,plain,(
    ~ r2_relset_1('#skF_2','#skF_2',k6_partfun1('#skF_2'),k6_partfun1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2358,c_321])).

tff(c_2388,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_242,c_2385])).

tff(c_2389,plain,(
    ~ r2_relset_1('#skF_2','#skF_2',k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2',k2_funct_2('#skF_2','#skF_3'),'#skF_3'),k6_partfun1('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_2587,plain,(
    ~ r2_relset_1('#skF_2','#skF_2',k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2',k2_funct_1('#skF_3'),'#skF_3'),k6_partfun1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2585,c_2389])).

tff(c_3724,plain,(
    ~ r2_relset_1('#skF_2','#skF_2',k6_partfun1('#skF_2'),k6_partfun1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3692,c_2587])).

tff(c_3727,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2506,c_3724])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n021.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 09:33:34 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.81/2.14  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.81/2.15  
% 5.81/2.15  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.81/2.16  %$ r2_relset_1 > v3_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > v1_partfun1 > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > k2_funct_2 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 5.81/2.16  
% 5.81/2.16  %Foreground sorts:
% 5.81/2.16  
% 5.81/2.16  
% 5.81/2.16  %Background operators:
% 5.81/2.16  
% 5.81/2.16  
% 5.81/2.16  %Foreground operators:
% 5.81/2.16  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 5.81/2.16  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 5.81/2.16  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 5.81/2.16  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.81/2.16  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 5.81/2.16  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 5.81/2.16  tff(k2_funct_2, type, k2_funct_2: ($i * $i) > $i).
% 5.81/2.16  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 5.81/2.16  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 5.81/2.16  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 5.81/2.16  tff('#skF_2', type, '#skF_2': $i).
% 5.81/2.16  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 5.81/2.16  tff('#skF_3', type, '#skF_3': $i).
% 5.81/2.16  tff(v2_funct_2, type, v2_funct_2: ($i * $i) > $o).
% 5.81/2.16  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 5.81/2.16  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 5.81/2.16  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.81/2.16  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 5.81/2.16  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.81/2.16  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.81/2.16  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 5.81/2.16  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 5.81/2.16  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.81/2.16  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 5.81/2.16  tff(v3_funct_2, type, v3_funct_2: ($i * $i * $i) > $o).
% 5.81/2.16  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 5.81/2.16  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 5.81/2.16  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.81/2.16  
% 5.81/2.18  tff(f_102, axiom, (![A]: (v1_partfun1(k6_partfun1(A), A) & m1_subset_1(k6_partfun1(A), k1_zfmisc_1(k2_zfmisc_1(A, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_partfun1)).
% 5.81/2.18  tff(f_115, axiom, (![A, B]: (?[C]: (((((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & v1_relat_1(C)) & v4_relat_1(C, A)) & v5_relat_1(C, B)) & v1_funct_1(C)) & v1_funct_2(C, A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', rc1_funct_2)).
% 5.81/2.18  tff(f_70, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => r2_relset_1(A, B, C, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', reflexivity_r2_relset_1)).
% 5.81/2.18  tff(f_158, negated_conjecture, ~(![A, B]: ((((v1_funct_1(B) & v1_funct_2(B, A, A)) & v3_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (r2_relset_1(A, A, k1_partfun1(A, A, A, A, B, k2_funct_2(A, B)), k6_partfun1(A)) & r2_relset_1(A, A, k1_partfun1(A, A, A, A, k2_funct_2(A, B), B), k6_partfun1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t88_funct_2)).
% 5.81/2.18  tff(f_135, axiom, (![A, B]: ((((v1_funct_1(B) & v1_funct_2(B, A, A)) & v3_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (k2_funct_2(A, B) = k2_funct_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_funct_2)).
% 5.81/2.18  tff(f_98, axiom, (![A, B]: ((((v1_funct_1(B) & v1_funct_2(B, A, A)) & v3_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (((v1_funct_1(k2_funct_2(A, B)) & v1_funct_2(k2_funct_2(A, B), A, A)) & v3_funct_2(k2_funct_2(A, B), A, A)) & m1_subset_1(k2_funct_2(A, B), k1_zfmisc_1(k2_zfmisc_1(A, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_funct_2)).
% 5.81/2.18  tff(f_34, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 5.81/2.18  tff(f_32, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 5.81/2.18  tff(f_82, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v3_funct_2(C, A, B)) => ((v1_funct_1(C) & v2_funct_1(C)) & v2_funct_2(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_funct_2)).
% 5.81/2.18  tff(f_145, axiom, (![A, B]: (((v1_funct_1(B) & v1_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (k1_relset_1(A, A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t67_funct_2)).
% 5.81/2.18  tff(f_64, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 5.81/2.18  tff(f_60, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => (k2_funct_1(k2_funct_1(A)) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_funct_1)).
% 5.81/2.18  tff(f_137, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 5.81/2.18  tff(f_44, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k5_relat_1(A, k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))) & (k5_relat_1(k2_funct_1(A), A) = k6_relat_1(k2_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t61_funct_1)).
% 5.81/2.18  tff(f_125, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 5.81/2.18  tff(c_34, plain, (![A_21]: (m1_subset_1(k6_partfun1(A_21), k1_zfmisc_1(k2_zfmisc_1(A_21, A_21))))), inference(cnfTransformation, [status(thm)], [f_102])).
% 5.81/2.18  tff(c_46, plain, (![A_22, B_23]: (m1_subset_1('#skF_1'(A_22, B_23), k1_zfmisc_1(k2_zfmisc_1(A_22, B_23))))), inference(cnfTransformation, [status(thm)], [f_115])).
% 5.81/2.18  tff(c_2488, plain, (![A_203, B_204, C_205, D_206]: (r2_relset_1(A_203, B_204, C_205, C_205) | ~m1_subset_1(D_206, k1_zfmisc_1(k2_zfmisc_1(A_203, B_204))) | ~m1_subset_1(C_205, k1_zfmisc_1(k2_zfmisc_1(A_203, B_204))))), inference(cnfTransformation, [status(thm)], [f_70])).
% 5.81/2.18  tff(c_2498, plain, (![A_207, B_208, C_209]: (r2_relset_1(A_207, B_208, C_209, C_209) | ~m1_subset_1(C_209, k1_zfmisc_1(k2_zfmisc_1(A_207, B_208))))), inference(resolution, [status(thm)], [c_46, c_2488])).
% 5.81/2.18  tff(c_2506, plain, (![A_21]: (r2_relset_1(A_21, A_21, k6_partfun1(A_21), k6_partfun1(A_21)))), inference(resolution, [status(thm)], [c_34, c_2498])).
% 5.81/2.18  tff(c_64, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_158])).
% 5.81/2.18  tff(c_62, plain, (v1_funct_2('#skF_3', '#skF_2', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_158])).
% 5.81/2.18  tff(c_60, plain, (v3_funct_2('#skF_3', '#skF_2', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_158])).
% 5.81/2.18  tff(c_58, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_158])).
% 5.81/2.18  tff(c_2568, plain, (![A_221, B_222]: (k2_funct_2(A_221, B_222)=k2_funct_1(B_222) | ~m1_subset_1(B_222, k1_zfmisc_1(k2_zfmisc_1(A_221, A_221))) | ~v3_funct_2(B_222, A_221, A_221) | ~v1_funct_2(B_222, A_221, A_221) | ~v1_funct_1(B_222))), inference(cnfTransformation, [status(thm)], [f_135])).
% 5.81/2.18  tff(c_2578, plain, (k2_funct_2('#skF_2', '#skF_3')=k2_funct_1('#skF_3') | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_58, c_2568])).
% 5.81/2.18  tff(c_2585, plain, (k2_funct_2('#skF_2', '#skF_3')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_60, c_2578])).
% 5.81/2.18  tff(c_2548, plain, (![A_217, B_218]: (v1_funct_1(k2_funct_2(A_217, B_218)) | ~m1_subset_1(B_218, k1_zfmisc_1(k2_zfmisc_1(A_217, A_217))) | ~v3_funct_2(B_218, A_217, A_217) | ~v1_funct_2(B_218, A_217, A_217) | ~v1_funct_1(B_218))), inference(cnfTransformation, [status(thm)], [f_98])).
% 5.81/2.18  tff(c_2558, plain, (v1_funct_1(k2_funct_2('#skF_2', '#skF_3')) | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_58, c_2548])).
% 5.81/2.18  tff(c_2565, plain, (v1_funct_1(k2_funct_2('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_60, c_2558])).
% 5.81/2.18  tff(c_2586, plain, (v1_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_2585, c_2565])).
% 5.81/2.18  tff(c_4, plain, (![A_4, B_5]: (v1_relat_1(k2_zfmisc_1(A_4, B_5)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 5.81/2.18  tff(c_84, plain, (![B_51, A_52]: (v1_relat_1(B_51) | ~m1_subset_1(B_51, k1_zfmisc_1(A_52)) | ~v1_relat_1(A_52))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.81/2.18  tff(c_90, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_2'))), inference(resolution, [status(thm)], [c_58, c_84])).
% 5.81/2.18  tff(c_96, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_90])).
% 5.81/2.18  tff(c_2450, plain, (![C_191, A_192, B_193]: (v2_funct_1(C_191) | ~v3_funct_2(C_191, A_192, B_193) | ~v1_funct_1(C_191) | ~m1_subset_1(C_191, k1_zfmisc_1(k2_zfmisc_1(A_192, B_193))))), inference(cnfTransformation, [status(thm)], [f_82])).
% 5.81/2.18  tff(c_2459, plain, (v2_funct_1('#skF_3') | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_58, c_2450])).
% 5.81/2.18  tff(c_2466, plain, (v2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_60, c_2459])).
% 5.81/2.18  tff(c_2692, plain, (![A_234, B_235]: (m1_subset_1(k2_funct_2(A_234, B_235), k1_zfmisc_1(k2_zfmisc_1(A_234, A_234))) | ~m1_subset_1(B_235, k1_zfmisc_1(k2_zfmisc_1(A_234, A_234))) | ~v3_funct_2(B_235, A_234, A_234) | ~v1_funct_2(B_235, A_234, A_234) | ~v1_funct_1(B_235))), inference(cnfTransformation, [status(thm)], [f_98])).
% 5.81/2.18  tff(c_2722, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'))) | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_2585, c_2692])).
% 5.81/2.18  tff(c_2736, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_60, c_58, c_2722])).
% 5.81/2.18  tff(c_2, plain, (![B_3, A_1]: (v1_relat_1(B_3) | ~m1_subset_1(B_3, k1_zfmisc_1(A_1)) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.81/2.18  tff(c_2763, plain, (v1_relat_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_2'))), inference(resolution, [status(thm)], [c_2736, c_2])).
% 5.81/2.18  tff(c_2789, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_2763])).
% 5.81/2.18  tff(c_2611, plain, (![A_228, B_229]: (v3_funct_2(k2_funct_2(A_228, B_229), A_228, A_228) | ~m1_subset_1(B_229, k1_zfmisc_1(k2_zfmisc_1(A_228, A_228))) | ~v3_funct_2(B_229, A_228, A_228) | ~v1_funct_2(B_229, A_228, A_228) | ~v1_funct_1(B_229))), inference(cnfTransformation, [status(thm)], [f_98])).
% 5.81/2.18  tff(c_2618, plain, (v3_funct_2(k2_funct_2('#skF_2', '#skF_3'), '#skF_2', '#skF_2') | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_58, c_2611])).
% 5.81/2.18  tff(c_2625, plain, (v3_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_60, c_2585, c_2618])).
% 5.81/2.18  tff(c_20, plain, (![C_18, A_16, B_17]: (v2_funct_1(C_18) | ~v3_funct_2(C_18, A_16, B_17) | ~v1_funct_1(C_18) | ~m1_subset_1(C_18, k1_zfmisc_1(k2_zfmisc_1(A_16, B_17))))), inference(cnfTransformation, [status(thm)], [f_82])).
% 5.81/2.18  tff(c_2757, plain, (v2_funct_1(k2_funct_1('#skF_3')) | ~v3_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_2') | ~v1_funct_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_2736, c_20])).
% 5.81/2.18  tff(c_2785, plain, (v2_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_2586, c_2625, c_2757])).
% 5.81/2.18  tff(c_2594, plain, (![A_224, B_225]: (v1_funct_2(k2_funct_2(A_224, B_225), A_224, A_224) | ~m1_subset_1(B_225, k1_zfmisc_1(k2_zfmisc_1(A_224, A_224))) | ~v3_funct_2(B_225, A_224, A_224) | ~v1_funct_2(B_225, A_224, A_224) | ~v1_funct_1(B_225))), inference(cnfTransformation, [status(thm)], [f_98])).
% 5.81/2.18  tff(c_2601, plain, (v1_funct_2(k2_funct_2('#skF_2', '#skF_3'), '#skF_2', '#skF_2') | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_58, c_2594])).
% 5.81/2.18  tff(c_2608, plain, (v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_60, c_2585, c_2601])).
% 5.81/2.18  tff(c_54, plain, (![A_34, B_35]: (k1_relset_1(A_34, A_34, B_35)=A_34 | ~m1_subset_1(B_35, k1_zfmisc_1(k2_zfmisc_1(A_34, A_34))) | ~v1_funct_2(B_35, A_34, A_34) | ~v1_funct_1(B_35))), inference(cnfTransformation, [status(thm)], [f_145])).
% 5.81/2.18  tff(c_2749, plain, (k1_relset_1('#skF_2', '#skF_2', k2_funct_1('#skF_3'))='#skF_2' | ~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_2') | ~v1_funct_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_2736, c_54])).
% 5.81/2.18  tff(c_2778, plain, (k1_relset_1('#skF_2', '#skF_2', k2_funct_1('#skF_3'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_2586, c_2608, c_2749])).
% 5.81/2.18  tff(c_14, plain, (![A_9, B_10, C_11]: (k1_relset_1(A_9, B_10, C_11)=k1_relat_1(C_11) | ~m1_subset_1(C_11, k1_zfmisc_1(k2_zfmisc_1(A_9, B_10))))), inference(cnfTransformation, [status(thm)], [f_64])).
% 5.81/2.18  tff(c_2786, plain, (k1_relset_1('#skF_2', '#skF_2', k2_funct_1('#skF_3'))=k1_relat_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_2736, c_14])).
% 5.81/2.18  tff(c_2843, plain, (k1_relat_1(k2_funct_1('#skF_3'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_2778, c_2786])).
% 5.81/2.18  tff(c_12, plain, (![A_8]: (k2_funct_1(k2_funct_1(A_8))=A_8 | ~v2_funct_1(A_8) | ~v1_funct_1(A_8) | ~v1_relat_1(A_8))), inference(cnfTransformation, [status(thm)], [f_60])).
% 5.81/2.18  tff(c_52, plain, (![A_33]: (k6_relat_1(A_33)=k6_partfun1(A_33))), inference(cnfTransformation, [status(thm)], [f_137])).
% 5.81/2.18  tff(c_8, plain, (![A_6]: (k5_relat_1(A_6, k2_funct_1(A_6))=k6_relat_1(k1_relat_1(A_6)) | ~v2_funct_1(A_6) | ~v1_funct_1(A_6) | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_44])).
% 5.81/2.18  tff(c_2426, plain, (![A_189]: (k5_relat_1(A_189, k2_funct_1(A_189))=k6_partfun1(k1_relat_1(A_189)) | ~v2_funct_1(A_189) | ~v1_funct_1(A_189) | ~v1_relat_1(A_189))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_8])).
% 5.81/2.18  tff(c_2435, plain, (![A_8]: (k6_partfun1(k1_relat_1(k2_funct_1(A_8)))=k5_relat_1(k2_funct_1(A_8), A_8) | ~v2_funct_1(k2_funct_1(A_8)) | ~v1_funct_1(k2_funct_1(A_8)) | ~v1_relat_1(k2_funct_1(A_8)) | ~v2_funct_1(A_8) | ~v1_funct_1(A_8) | ~v1_relat_1(A_8))), inference(superposition, [status(thm), theory('equality')], [c_12, c_2426])).
% 5.81/2.18  tff(c_2847, plain, (k5_relat_1(k2_funct_1('#skF_3'), '#skF_3')=k6_partfun1('#skF_2') | ~v2_funct_1(k2_funct_1('#skF_3')) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_2843, c_2435])).
% 5.81/2.18  tff(c_2851, plain, (k5_relat_1(k2_funct_1('#skF_3'), '#skF_3')=k6_partfun1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_96, c_64, c_2466, c_2789, c_2586, c_2785, c_2847])).
% 5.81/2.18  tff(c_24, plain, (![A_19, B_20]: (m1_subset_1(k2_funct_2(A_19, B_20), k1_zfmisc_1(k2_zfmisc_1(A_19, A_19))) | ~m1_subset_1(B_20, k1_zfmisc_1(k2_zfmisc_1(A_19, A_19))) | ~v3_funct_2(B_20, A_19, A_19) | ~v1_funct_2(B_20, A_19, A_19) | ~v1_funct_1(B_20))), inference(cnfTransformation, [status(thm)], [f_98])).
% 5.81/2.18  tff(c_2809, plain, (![C_238, B_240, E_241, F_239, A_237, D_236]: (k1_partfun1(A_237, B_240, C_238, D_236, E_241, F_239)=k5_relat_1(E_241, F_239) | ~m1_subset_1(F_239, k1_zfmisc_1(k2_zfmisc_1(C_238, D_236))) | ~v1_funct_1(F_239) | ~m1_subset_1(E_241, k1_zfmisc_1(k2_zfmisc_1(A_237, B_240))) | ~v1_funct_1(E_241))), inference(cnfTransformation, [status(thm)], [f_125])).
% 5.81/2.18  tff(c_2819, plain, (![A_237, B_240, E_241]: (k1_partfun1(A_237, B_240, '#skF_2', '#skF_2', E_241, '#skF_3')=k5_relat_1(E_241, '#skF_3') | ~v1_funct_1('#skF_3') | ~m1_subset_1(E_241, k1_zfmisc_1(k2_zfmisc_1(A_237, B_240))) | ~v1_funct_1(E_241))), inference(resolution, [status(thm)], [c_58, c_2809])).
% 5.81/2.18  tff(c_2853, plain, (![A_242, B_243, E_244]: (k1_partfun1(A_242, B_243, '#skF_2', '#skF_2', E_244, '#skF_3')=k5_relat_1(E_244, '#skF_3') | ~m1_subset_1(E_244, k1_zfmisc_1(k2_zfmisc_1(A_242, B_243))) | ~v1_funct_1(E_244))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_2819])).
% 5.81/2.18  tff(c_3662, plain, (![A_262, B_263]: (k1_partfun1(A_262, A_262, '#skF_2', '#skF_2', k2_funct_2(A_262, B_263), '#skF_3')=k5_relat_1(k2_funct_2(A_262, B_263), '#skF_3') | ~v1_funct_1(k2_funct_2(A_262, B_263)) | ~m1_subset_1(B_263, k1_zfmisc_1(k2_zfmisc_1(A_262, A_262))) | ~v3_funct_2(B_263, A_262, A_262) | ~v1_funct_2(B_263, A_262, A_262) | ~v1_funct_1(B_263))), inference(resolution, [status(thm)], [c_24, c_2853])).
% 5.81/2.18  tff(c_3677, plain, (k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', k2_funct_2('#skF_2', '#skF_3'), '#skF_3')=k5_relat_1(k2_funct_2('#skF_2', '#skF_3'), '#skF_3') | ~v1_funct_1(k2_funct_2('#skF_2', '#skF_3')) | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_58, c_3662])).
% 5.81/2.18  tff(c_3692, plain, (k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', k2_funct_1('#skF_3'), '#skF_3')=k6_partfun1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_60, c_2586, c_2585, c_2851, c_2585, c_2585, c_3677])).
% 5.81/2.18  tff(c_224, plain, (![A_78, B_79, C_80, D_81]: (r2_relset_1(A_78, B_79, C_80, C_80) | ~m1_subset_1(D_81, k1_zfmisc_1(k2_zfmisc_1(A_78, B_79))) | ~m1_subset_1(C_80, k1_zfmisc_1(k2_zfmisc_1(A_78, B_79))))), inference(cnfTransformation, [status(thm)], [f_70])).
% 5.81/2.18  tff(c_234, plain, (![A_82, B_83, C_84]: (r2_relset_1(A_82, B_83, C_84, C_84) | ~m1_subset_1(C_84, k1_zfmisc_1(k2_zfmisc_1(A_82, B_83))))), inference(resolution, [status(thm)], [c_46, c_224])).
% 5.81/2.18  tff(c_242, plain, (![A_21]: (r2_relset_1(A_21, A_21, k6_partfun1(A_21), k6_partfun1(A_21)))), inference(resolution, [status(thm)], [c_34, c_234])).
% 5.81/2.18  tff(c_302, plain, (![A_94, B_95]: (k2_funct_2(A_94, B_95)=k2_funct_1(B_95) | ~m1_subset_1(B_95, k1_zfmisc_1(k2_zfmisc_1(A_94, A_94))) | ~v3_funct_2(B_95, A_94, A_94) | ~v1_funct_2(B_95, A_94, A_94) | ~v1_funct_1(B_95))), inference(cnfTransformation, [status(thm)], [f_135])).
% 5.81/2.18  tff(c_312, plain, (k2_funct_2('#skF_2', '#skF_3')=k2_funct_1('#skF_3') | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_58, c_302])).
% 5.81/2.18  tff(c_319, plain, (k2_funct_2('#skF_2', '#skF_3')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_60, c_312])).
% 5.81/2.18  tff(c_364, plain, (![A_108, B_109]: (m1_subset_1(k2_funct_2(A_108, B_109), k1_zfmisc_1(k2_zfmisc_1(A_108, A_108))) | ~m1_subset_1(B_109, k1_zfmisc_1(k2_zfmisc_1(A_108, A_108))) | ~v3_funct_2(B_109, A_108, A_108) | ~v1_funct_2(B_109, A_108, A_108) | ~v1_funct_1(B_109))), inference(cnfTransformation, [status(thm)], [f_98])).
% 5.81/2.18  tff(c_394, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'))) | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_319, c_364])).
% 5.81/2.18  tff(c_408, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_60, c_58, c_394])).
% 5.81/2.18  tff(c_435, plain, (v1_relat_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_2'))), inference(resolution, [status(thm)], [c_408, c_2])).
% 5.81/2.18  tff(c_461, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_435])).
% 5.81/2.18  tff(c_279, plain, (![A_91, B_92]: (v1_funct_1(k2_funct_2(A_91, B_92)) | ~m1_subset_1(B_92, k1_zfmisc_1(k2_zfmisc_1(A_91, A_91))) | ~v3_funct_2(B_92, A_91, A_91) | ~v1_funct_2(B_92, A_91, A_91) | ~v1_funct_1(B_92))), inference(cnfTransformation, [status(thm)], [f_98])).
% 5.81/2.18  tff(c_289, plain, (v1_funct_1(k2_funct_2('#skF_2', '#skF_3')) | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_58, c_279])).
% 5.81/2.18  tff(c_296, plain, (v1_funct_1(k2_funct_2('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_60, c_289])).
% 5.81/2.18  tff(c_320, plain, (v1_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_319, c_296])).
% 5.81/2.18  tff(c_345, plain, (![A_102, B_103]: (v3_funct_2(k2_funct_2(A_102, B_103), A_102, A_102) | ~m1_subset_1(B_103, k1_zfmisc_1(k2_zfmisc_1(A_102, A_102))) | ~v3_funct_2(B_103, A_102, A_102) | ~v1_funct_2(B_103, A_102, A_102) | ~v1_funct_1(B_103))), inference(cnfTransformation, [status(thm)], [f_98])).
% 5.81/2.18  tff(c_352, plain, (v3_funct_2(k2_funct_2('#skF_2', '#skF_3'), '#skF_2', '#skF_2') | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_58, c_345])).
% 5.81/2.18  tff(c_359, plain, (v3_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_60, c_319, c_352])).
% 5.81/2.18  tff(c_429, plain, (v2_funct_1(k2_funct_1('#skF_3')) | ~v3_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_2') | ~v1_funct_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_408, c_20])).
% 5.81/2.18  tff(c_457, plain, (v2_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_320, c_359, c_429])).
% 5.81/2.18  tff(c_328, plain, (![A_98, B_99]: (v1_funct_2(k2_funct_2(A_98, B_99), A_98, A_98) | ~m1_subset_1(B_99, k1_zfmisc_1(k2_zfmisc_1(A_98, A_98))) | ~v3_funct_2(B_99, A_98, A_98) | ~v1_funct_2(B_99, A_98, A_98) | ~v1_funct_1(B_99))), inference(cnfTransformation, [status(thm)], [f_98])).
% 5.81/2.18  tff(c_335, plain, (v1_funct_2(k2_funct_2('#skF_2', '#skF_3'), '#skF_2', '#skF_2') | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_58, c_328])).
% 5.81/2.18  tff(c_342, plain, (v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_60, c_319, c_335])).
% 5.81/2.18  tff(c_50, plain, (![A_31, B_32]: (k2_funct_2(A_31, B_32)=k2_funct_1(B_32) | ~m1_subset_1(B_32, k1_zfmisc_1(k2_zfmisc_1(A_31, A_31))) | ~v3_funct_2(B_32, A_31, A_31) | ~v1_funct_2(B_32, A_31, A_31) | ~v1_funct_1(B_32))), inference(cnfTransformation, [status(thm)], [f_135])).
% 5.81/2.18  tff(c_415, plain, (k2_funct_2('#skF_2', k2_funct_1('#skF_3'))=k2_funct_1(k2_funct_1('#skF_3')) | ~v3_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_2') | ~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_2') | ~v1_funct_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_408, c_50])).
% 5.81/2.18  tff(c_444, plain, (k2_funct_2('#skF_2', k2_funct_1('#skF_3'))=k2_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_320, c_342, c_359, c_415])).
% 5.81/2.18  tff(c_494, plain, (m1_subset_1(k2_funct_1(k2_funct_1('#skF_3')), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'))) | ~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'))) | ~v3_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_2') | ~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_2') | ~v1_funct_1(k2_funct_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_444, c_24])).
% 5.81/2.18  tff(c_498, plain, (m1_subset_1(k2_funct_1(k2_funct_1('#skF_3')), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_320, c_342, c_359, c_408, c_494])).
% 5.81/2.18  tff(c_578, plain, (v1_relat_1(k2_funct_1(k2_funct_1('#skF_3'))) | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_2'))), inference(resolution, [status(thm)], [c_498, c_2])).
% 5.81/2.18  tff(c_613, plain, (v1_relat_1(k2_funct_1(k2_funct_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_578])).
% 5.81/2.18  tff(c_30, plain, (![A_19, B_20]: (v1_funct_1(k2_funct_2(A_19, B_20)) | ~m1_subset_1(B_20, k1_zfmisc_1(k2_zfmisc_1(A_19, A_19))) | ~v3_funct_2(B_20, A_19, A_19) | ~v1_funct_2(B_20, A_19, A_19) | ~v1_funct_1(B_20))), inference(cnfTransformation, [status(thm)], [f_98])).
% 5.81/2.18  tff(c_418, plain, (v1_funct_1(k2_funct_2('#skF_2', k2_funct_1('#skF_3'))) | ~v3_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_2') | ~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_2') | ~v1_funct_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_408, c_30])).
% 5.81/2.18  tff(c_447, plain, (v1_funct_1(k2_funct_2('#skF_2', k2_funct_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_320, c_342, c_359, c_418])).
% 5.81/2.18  tff(c_490, plain, (v1_funct_1(k2_funct_1(k2_funct_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_444, c_447])).
% 5.81/2.18  tff(c_26, plain, (![A_19, B_20]: (v3_funct_2(k2_funct_2(A_19, B_20), A_19, A_19) | ~m1_subset_1(B_20, k1_zfmisc_1(k2_zfmisc_1(A_19, A_19))) | ~v3_funct_2(B_20, A_19, A_19) | ~v1_funct_2(B_20, A_19, A_19) | ~v1_funct_1(B_20))), inference(cnfTransformation, [status(thm)], [f_98])).
% 5.81/2.18  tff(c_410, plain, (v3_funct_2(k2_funct_2('#skF_2', k2_funct_1('#skF_3')), '#skF_2', '#skF_2') | ~v3_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_2') | ~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_2') | ~v1_funct_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_408, c_26])).
% 5.81/2.18  tff(c_438, plain, (v3_funct_2(k2_funct_2('#skF_2', k2_funct_1('#skF_3')), '#skF_2', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_320, c_342, c_359, c_410])).
% 5.81/2.18  tff(c_489, plain, (v3_funct_2(k2_funct_1(k2_funct_1('#skF_3')), '#skF_2', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_444, c_438])).
% 5.81/2.18  tff(c_572, plain, (v2_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) | ~v3_funct_2(k2_funct_1(k2_funct_1('#skF_3')), '#skF_2', '#skF_2') | ~v1_funct_1(k2_funct_1(k2_funct_1('#skF_3')))), inference(resolution, [status(thm)], [c_498, c_20])).
% 5.81/2.18  tff(c_609, plain, (v2_funct_1(k2_funct_1(k2_funct_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_490, c_489, c_572])).
% 5.81/2.18  tff(c_28, plain, (![A_19, B_20]: (v1_funct_2(k2_funct_2(A_19, B_20), A_19, A_19) | ~m1_subset_1(B_20, k1_zfmisc_1(k2_zfmisc_1(A_19, A_19))) | ~v3_funct_2(B_20, A_19, A_19) | ~v1_funct_2(B_20, A_19, A_19) | ~v1_funct_1(B_20))), inference(cnfTransformation, [status(thm)], [f_98])).
% 5.81/2.18  tff(c_412, plain, (v1_funct_2(k2_funct_2('#skF_2', k2_funct_1('#skF_3')), '#skF_2', '#skF_2') | ~v3_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_2') | ~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_2') | ~v1_funct_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_408, c_28])).
% 5.81/2.18  tff(c_441, plain, (v1_funct_2(k2_funct_2('#skF_2', k2_funct_1('#skF_3')), '#skF_2', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_320, c_342, c_359, c_412])).
% 5.81/2.18  tff(c_488, plain, (v1_funct_2(k2_funct_1(k2_funct_1('#skF_3')), '#skF_2', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_444, c_441])).
% 5.81/2.18  tff(c_564, plain, (k1_relset_1('#skF_2', '#skF_2', k2_funct_1(k2_funct_1('#skF_3')))='#skF_2' | ~v1_funct_2(k2_funct_1(k2_funct_1('#skF_3')), '#skF_2', '#skF_2') | ~v1_funct_1(k2_funct_1(k2_funct_1('#skF_3')))), inference(resolution, [status(thm)], [c_498, c_54])).
% 5.81/2.18  tff(c_602, plain, (k1_relset_1('#skF_2', '#skF_2', k2_funct_1(k2_funct_1('#skF_3')))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_490, c_488, c_564])).
% 5.81/2.18  tff(c_610, plain, (k1_relset_1('#skF_2', '#skF_2', k2_funct_1(k2_funct_1('#skF_3')))=k1_relat_1(k2_funct_1(k2_funct_1('#skF_3')))), inference(resolution, [status(thm)], [c_498, c_14])).
% 5.81/2.18  tff(c_925, plain, (k1_relat_1(k2_funct_1(k2_funct_1('#skF_3')))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_602, c_610])).
% 5.81/2.18  tff(c_174, plain, (![A_65]: (k5_relat_1(A_65, k2_funct_1(A_65))=k6_partfun1(k1_relat_1(A_65)) | ~v2_funct_1(A_65) | ~v1_funct_1(A_65) | ~v1_relat_1(A_65))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_8])).
% 5.81/2.18  tff(c_1056, plain, (![A_130]: (k6_partfun1(k1_relat_1(k2_funct_1(A_130)))=k5_relat_1(k2_funct_1(A_130), A_130) | ~v2_funct_1(k2_funct_1(A_130)) | ~v1_funct_1(k2_funct_1(A_130)) | ~v1_relat_1(k2_funct_1(A_130)) | ~v2_funct_1(A_130) | ~v1_funct_1(A_130) | ~v1_relat_1(A_130))), inference(superposition, [status(thm), theory('equality')], [c_12, c_174])).
% 5.81/2.18  tff(c_186, plain, (![C_66, A_67, B_68]: (v2_funct_1(C_66) | ~v3_funct_2(C_66, A_67, B_68) | ~v1_funct_1(C_66) | ~m1_subset_1(C_66, k1_zfmisc_1(k2_zfmisc_1(A_67, B_68))))), inference(cnfTransformation, [status(thm)], [f_82])).
% 5.81/2.18  tff(c_195, plain, (v2_funct_1('#skF_3') | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_58, c_186])).
% 5.81/2.18  tff(c_202, plain, (v2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_60, c_195])).
% 5.81/2.18  tff(c_558, plain, (k2_funct_2('#skF_2', k2_funct_1(k2_funct_1('#skF_3')))=k2_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) | ~v3_funct_2(k2_funct_1(k2_funct_1('#skF_3')), '#skF_2', '#skF_2') | ~v1_funct_2(k2_funct_1(k2_funct_1('#skF_3')), '#skF_2', '#skF_2') | ~v1_funct_1(k2_funct_1(k2_funct_1('#skF_3')))), inference(resolution, [status(thm)], [c_498, c_50])).
% 5.81/2.18  tff(c_596, plain, (k2_funct_2('#skF_2', k2_funct_1(k2_funct_1('#skF_3')))=k2_funct_1(k2_funct_1(k2_funct_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_490, c_488, c_489, c_558])).
% 5.81/2.18  tff(c_709, plain, (k2_funct_1(k2_funct_1(k2_funct_1('#skF_3')))=k2_funct_2('#skF_2', '#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_12, c_596])).
% 5.81/2.18  tff(c_715, plain, (k2_funct_1(k2_funct_1(k2_funct_1('#skF_3')))=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_96, c_64, c_202, c_319, c_709])).
% 5.81/2.18  tff(c_6, plain, (![A_6]: (k5_relat_1(k2_funct_1(A_6), A_6)=k6_relat_1(k2_relat_1(A_6)) | ~v2_funct_1(A_6) | ~v1_funct_1(A_6) | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_44])).
% 5.81/2.18  tff(c_162, plain, (![A_64]: (k5_relat_1(k2_funct_1(A_64), A_64)=k6_partfun1(k2_relat_1(A_64)) | ~v2_funct_1(A_64) | ~v1_funct_1(A_64) | ~v1_relat_1(A_64))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_6])).
% 5.81/2.18  tff(c_856, plain, (![A_128]: (k6_partfun1(k2_relat_1(k2_funct_1(A_128)))=k5_relat_1(A_128, k2_funct_1(A_128)) | ~v2_funct_1(k2_funct_1(A_128)) | ~v1_funct_1(k2_funct_1(A_128)) | ~v1_relat_1(k2_funct_1(A_128)) | ~v2_funct_1(A_128) | ~v1_funct_1(A_128) | ~v1_relat_1(A_128))), inference(superposition, [status(thm), theory('equality')], [c_12, c_162])).
% 5.81/2.18  tff(c_911, plain, (k6_partfun1(k2_relat_1(k2_funct_1(k2_funct_1(k2_funct_1('#skF_3')))))=k5_relat_1(k2_funct_1(k2_funct_1('#skF_3')), k2_funct_1('#skF_3')) | ~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1('#skF_3')))) | ~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1('#skF_3')))) | ~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1('#skF_3')))) | ~v2_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) | ~v1_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) | ~v1_relat_1(k2_funct_1(k2_funct_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_715, c_856])).
% 5.81/2.18  tff(c_923, plain, (k5_relat_1(k2_funct_1(k2_funct_1('#skF_3')), k2_funct_1('#skF_3'))=k6_partfun1(k2_relat_1(k2_funct_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_613, c_490, c_609, c_461, c_715, c_320, c_715, c_457, c_715, c_715, c_911])).
% 5.81/2.18  tff(c_945, plain, (k6_partfun1(k2_relat_1(k2_funct_1('#skF_3')))=k5_relat_1('#skF_3', k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_12, c_923])).
% 5.81/2.18  tff(c_955, plain, (k6_partfun1(k2_relat_1(k2_funct_1('#skF_3')))=k5_relat_1('#skF_3', k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_96, c_64, c_202, c_945])).
% 5.81/2.18  tff(c_959, plain, (k5_relat_1(k2_funct_1(k2_funct_1('#skF_3')), k2_funct_1('#skF_3'))=k5_relat_1('#skF_3', k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_955, c_923])).
% 5.81/2.18  tff(c_1065, plain, (k6_partfun1(k1_relat_1(k2_funct_1(k2_funct_1('#skF_3'))))=k5_relat_1('#skF_3', k2_funct_1('#skF_3')) | ~v2_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) | ~v1_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) | ~v1_relat_1(k2_funct_1(k2_funct_1('#skF_3'))) | ~v2_funct_1(k2_funct_1('#skF_3')) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_1056, c_959])).
% 5.81/2.18  tff(c_1132, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_partfun1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_461, c_320, c_457, c_613, c_490, c_609, c_925, c_1065])).
% 5.81/2.18  tff(c_466, plain, (![E_115, F_113, A_111, B_114, D_110, C_112]: (k1_partfun1(A_111, B_114, C_112, D_110, E_115, F_113)=k5_relat_1(E_115, F_113) | ~m1_subset_1(F_113, k1_zfmisc_1(k2_zfmisc_1(C_112, D_110))) | ~v1_funct_1(F_113) | ~m1_subset_1(E_115, k1_zfmisc_1(k2_zfmisc_1(A_111, B_114))) | ~v1_funct_1(E_115))), inference(cnfTransformation, [status(thm)], [f_125])).
% 5.81/2.18  tff(c_468, plain, (![A_111, B_114, E_115]: (k1_partfun1(A_111, B_114, '#skF_2', '#skF_2', E_115, k2_funct_1('#skF_3'))=k5_relat_1(E_115, k2_funct_1('#skF_3')) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~m1_subset_1(E_115, k1_zfmisc_1(k2_zfmisc_1(A_111, B_114))) | ~v1_funct_1(E_115))), inference(resolution, [status(thm)], [c_408, c_466])).
% 5.81/2.18  tff(c_2306, plain, (![A_178, B_179, E_180]: (k1_partfun1(A_178, B_179, '#skF_2', '#skF_2', E_180, k2_funct_1('#skF_3'))=k5_relat_1(E_180, k2_funct_1('#skF_3')) | ~m1_subset_1(E_180, k1_zfmisc_1(k2_zfmisc_1(A_178, B_179))) | ~v1_funct_1(E_180))), inference(demodulation, [status(thm), theory('equality')], [c_320, c_468])).
% 5.81/2.18  tff(c_2339, plain, (k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', '#skF_3', k2_funct_1('#skF_3'))=k5_relat_1('#skF_3', k2_funct_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_58, c_2306])).
% 5.81/2.18  tff(c_2358, plain, (k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', '#skF_3', k2_funct_1('#skF_3'))=k6_partfun1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_1132, c_2339])).
% 5.81/2.18  tff(c_56, plain, (~r2_relset_1('#skF_2', '#skF_2', k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', k2_funct_2('#skF_2', '#skF_3'), '#skF_3'), k6_partfun1('#skF_2')) | ~r2_relset_1('#skF_2', '#skF_2', k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', '#skF_3', k2_funct_2('#skF_2', '#skF_3')), k6_partfun1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_158])).
% 5.81/2.18  tff(c_126, plain, (~r2_relset_1('#skF_2', '#skF_2', k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', '#skF_3', k2_funct_2('#skF_2', '#skF_3')), k6_partfun1('#skF_2'))), inference(splitLeft, [status(thm)], [c_56])).
% 5.81/2.18  tff(c_321, plain, (~r2_relset_1('#skF_2', '#skF_2', k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', '#skF_3', k2_funct_1('#skF_3')), k6_partfun1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_319, c_126])).
% 5.81/2.18  tff(c_2385, plain, (~r2_relset_1('#skF_2', '#skF_2', k6_partfun1('#skF_2'), k6_partfun1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_2358, c_321])).
% 5.81/2.18  tff(c_2388, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_242, c_2385])).
% 5.81/2.18  tff(c_2389, plain, (~r2_relset_1('#skF_2', '#skF_2', k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', k2_funct_2('#skF_2', '#skF_3'), '#skF_3'), k6_partfun1('#skF_2'))), inference(splitRight, [status(thm)], [c_56])).
% 5.81/2.18  tff(c_2587, plain, (~r2_relset_1('#skF_2', '#skF_2', k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', k2_funct_1('#skF_3'), '#skF_3'), k6_partfun1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_2585, c_2389])).
% 5.81/2.18  tff(c_3724, plain, (~r2_relset_1('#skF_2', '#skF_2', k6_partfun1('#skF_2'), k6_partfun1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_3692, c_2587])).
% 5.81/2.18  tff(c_3727, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2506, c_3724])).
% 5.81/2.18  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.81/2.18  
% 5.81/2.18  Inference rules
% 5.81/2.18  ----------------------
% 5.81/2.18  #Ref     : 0
% 5.81/2.18  #Sup     : 871
% 5.81/2.18  #Fact    : 0
% 5.81/2.18  #Define  : 0
% 5.81/2.18  #Split   : 3
% 5.81/2.18  #Chain   : 0
% 5.81/2.18  #Close   : 0
% 5.81/2.18  
% 5.81/2.18  Ordering : KBO
% 5.81/2.18  
% 5.81/2.18  Simplification rules
% 5.81/2.18  ----------------------
% 5.81/2.18  #Subsume      : 95
% 5.81/2.18  #Demod        : 1755
% 5.81/2.18  #Tautology    : 374
% 5.81/2.18  #SimpNegUnit  : 0
% 5.81/2.18  #BackRed      : 35
% 5.81/2.18  
% 5.81/2.18  #Partial instantiations: 0
% 5.81/2.18  #Strategies tried      : 1
% 5.81/2.18  
% 5.81/2.18  Timing (in seconds)
% 5.81/2.18  ----------------------
% 5.81/2.19  Preprocessing        : 0.35
% 5.81/2.19  Parsing              : 0.20
% 5.81/2.19  CNF conversion       : 0.02
% 5.81/2.19  Main loop            : 0.99
% 5.81/2.19  Inferencing          : 0.33
% 5.81/2.19  Reduction            : 0.41
% 5.81/2.19  Demodulation         : 0.32
% 5.81/2.19  BG Simplification    : 0.04
% 5.81/2.19  Subsumption          : 0.15
% 5.81/2.19  Abstraction          : 0.04
% 5.81/2.19  MUC search           : 0.00
% 5.81/2.19  Cooper               : 0.00
% 5.81/2.19  Total                : 1.40
% 5.81/2.19  Index Insertion      : 0.00
% 5.81/2.19  Index Deletion       : 0.00
% 5.81/2.19  Index Matching       : 0.00
% 5.81/2.19  BG Taut test         : 0.00
%------------------------------------------------------------------------------
