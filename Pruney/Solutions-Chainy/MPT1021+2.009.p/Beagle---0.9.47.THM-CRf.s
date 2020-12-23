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
% DateTime   : Thu Dec  3 10:16:00 EST 2020

% Result     : Theorem 5.74s
% Output     : CNFRefutation 5.95s
% Verified   : 
% Statistics : Number of formulae       :  183 (8125 expanded)
%              Number of leaves         :   42 (3286 expanded)
%              Depth                    :   22
%              Number of atoms          :  455 (29752 expanded)
%              Number of equality atoms :   61 (1506 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v3_funct_2 > v1_funct_2 > v2_funct_2 > v1_partfun1 > r2_hidden > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > k2_funct_2 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1

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

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

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

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(v2_funct_2,type,(
    v2_funct_2: ( $i * $i ) > $o )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

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

tff(v3_funct_2,type,(
    v3_funct_2: ( $i * $i * $i ) > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_114,axiom,(
    ! [A] :
      ( v1_partfun1(k6_partfun1(A),A)
      & m1_subset_1(k6_partfun1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).

tff(f_82,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => r2_relset_1(A,B,C,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',reflexivity_r2_relset_1)).

tff(f_157,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_funct_1(B)
          & v1_funct_2(B,A,A)
          & v3_funct_2(B,A,A)
          & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
       => ( r2_relset_1(A,A,k1_partfun1(A,A,A,A,B,k2_funct_2(A,B)),k6_partfun1(A))
          & r2_relset_1(A,A,k1_partfun1(A,A,A,A,k2_funct_2(A,B),B),k6_partfun1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_funct_2)).

tff(f_134,axiom,(
    ! [A,B] :
      ( ( v1_funct_1(B)
        & v1_funct_2(B,A,A)
        & v3_funct_2(B,A,A)
        & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
     => k2_funct_2(A,B) = k2_funct_1(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_funct_2)).

tff(f_110,axiom,(
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

tff(f_72,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_94,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( ( v1_funct_1(C)
          & v3_funct_2(C,A,B) )
       => ( v1_funct_1(C)
          & v2_funct_1(C)
          & v2_funct_2(C,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_funct_2)).

tff(f_42,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_40,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_144,axiom,(
    ! [A,B] :
      ( ( v1_funct_1(B)
        & v1_funct_2(B,A,A)
        & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
     => k1_relset_1(A,A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_funct_2)).

tff(f_76,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_68,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => k2_funct_1(k2_funct_1(A)) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_funct_1)).

tff(f_136,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_52,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k5_relat_1(A,k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))
          & k5_relat_1(k2_funct_1(A),A) = k6_relat_1(k2_relat_1(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_1)).

tff(f_124,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(c_40,plain,(
    ! [A_28] : m1_subset_1(k6_partfun1(A_28),k1_zfmisc_1(k2_zfmisc_1(A_28,A_28))) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_2426,plain,(
    ! [A_198,B_199,C_200,D_201] :
      ( r2_relset_1(A_198,B_199,C_200,C_200)
      | ~ m1_subset_1(D_201,k1_zfmisc_1(k2_zfmisc_1(A_198,B_199)))
      | ~ m1_subset_1(C_200,k1_zfmisc_1(k2_zfmisc_1(A_198,B_199))) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_2436,plain,(
    ! [A_202,C_203] :
      ( r2_relset_1(A_202,A_202,C_203,C_203)
      | ~ m1_subset_1(C_203,k1_zfmisc_1(k2_zfmisc_1(A_202,A_202))) ) ),
    inference(resolution,[status(thm)],[c_40,c_2426])).

tff(c_2444,plain,(
    ! [A_28] : r2_relset_1(A_28,A_28,k6_partfun1(A_28),k6_partfun1(A_28)) ),
    inference(resolution,[status(thm)],[c_40,c_2436])).

tff(c_58,plain,(
    v1_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_56,plain,(
    v1_funct_2('#skF_2','#skF_1','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_54,plain,(
    v3_funct_2('#skF_2','#skF_1','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_52,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_2480,plain,(
    ! [A_213,B_214] :
      ( k2_funct_2(A_213,B_214) = k2_funct_1(B_214)
      | ~ m1_subset_1(B_214,k1_zfmisc_1(k2_zfmisc_1(A_213,A_213)))
      | ~ v3_funct_2(B_214,A_213,A_213)
      | ~ v1_funct_2(B_214,A_213,A_213)
      | ~ v1_funct_1(B_214) ) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_2486,plain,
    ( k2_funct_2('#skF_1','#skF_2') = k2_funct_1('#skF_2')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_52,c_2480])).

tff(c_2494,plain,(
    k2_funct_2('#skF_1','#skF_2') = k2_funct_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_54,c_2486])).

tff(c_2449,plain,(
    ! [A_206,B_207] :
      ( v1_funct_1(k2_funct_2(A_206,B_207))
      | ~ m1_subset_1(B_207,k1_zfmisc_1(k2_zfmisc_1(A_206,A_206)))
      | ~ v3_funct_2(B_207,A_206,A_206)
      | ~ v1_funct_2(B_207,A_206,A_206)
      | ~ v1_funct_1(B_207) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_2455,plain,
    ( v1_funct_1(k2_funct_2('#skF_1','#skF_2'))
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_52,c_2449])).

tff(c_2463,plain,(
    v1_funct_1(k2_funct_2('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_54,c_2455])).

tff(c_2496,plain,(
    v1_funct_1(k2_funct_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2494,c_2463])).

tff(c_2238,plain,(
    ! [C_163,A_164,B_165] :
      ( v1_relat_1(C_163)
      | ~ m1_subset_1(C_163,k1_zfmisc_1(k2_zfmisc_1(A_164,B_165))) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_2250,plain,(
    v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_52,c_2238])).

tff(c_2363,plain,(
    ! [C_187,A_188,B_189] :
      ( v2_funct_1(C_187)
      | ~ v3_funct_2(C_187,A_188,B_189)
      | ~ v1_funct_1(C_187)
      | ~ m1_subset_1(C_187,k1_zfmisc_1(k2_zfmisc_1(A_188,B_189))) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_2369,plain,
    ( v2_funct_1('#skF_2')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_52,c_2363])).

tff(c_2377,plain,(
    v2_funct_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_54,c_2369])).

tff(c_8,plain,(
    ! [A_8,B_9] : v1_relat_1(k2_zfmisc_1(A_8,B_9)) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_2675,plain,(
    ! [A_226,B_227] :
      ( m1_subset_1(k2_funct_2(A_226,B_227),k1_zfmisc_1(k2_zfmisc_1(A_226,A_226)))
      | ~ m1_subset_1(B_227,k1_zfmisc_1(k2_zfmisc_1(A_226,A_226)))
      | ~ v3_funct_2(B_227,A_226,A_226)
      | ~ v1_funct_2(B_227,A_226,A_226)
      | ~ v1_funct_1(B_227) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_2710,plain,
    ( m1_subset_1(k2_funct_1('#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_2494,c_2675])).

tff(c_2726,plain,(
    m1_subset_1(k2_funct_1('#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_54,c_52,c_2710])).

tff(c_6,plain,(
    ! [B_7,A_5] :
      ( v1_relat_1(B_7)
      | ~ m1_subset_1(B_7,k1_zfmisc_1(A_5))
      | ~ v1_relat_1(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_2755,plain,
    ( v1_relat_1(k2_funct_1('#skF_2'))
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_1')) ),
    inference(resolution,[status(thm)],[c_2726,c_6])).

tff(c_2785,plain,(
    v1_relat_1(k2_funct_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_2755])).

tff(c_2504,plain,(
    ! [A_216,B_217] :
      ( v3_funct_2(k2_funct_2(A_216,B_217),A_216,A_216)
      | ~ m1_subset_1(B_217,k1_zfmisc_1(k2_zfmisc_1(A_216,A_216)))
      | ~ v3_funct_2(B_217,A_216,A_216)
      | ~ v1_funct_2(B_217,A_216,A_216)
      | ~ v1_funct_1(B_217) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_2508,plain,
    ( v3_funct_2(k2_funct_2('#skF_1','#skF_2'),'#skF_1','#skF_1')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_52,c_2504])).

tff(c_2515,plain,(
    v3_funct_2(k2_funct_1('#skF_2'),'#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_54,c_2494,c_2508])).

tff(c_26,plain,(
    ! [C_25,A_23,B_24] :
      ( v2_funct_1(C_25)
      | ~ v3_funct_2(C_25,A_23,B_24)
      | ~ v1_funct_1(C_25)
      | ~ m1_subset_1(C_25,k1_zfmisc_1(k2_zfmisc_1(A_23,B_24))) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_2747,plain,
    ( v2_funct_1(k2_funct_1('#skF_2'))
    | ~ v3_funct_2(k2_funct_1('#skF_2'),'#skF_1','#skF_1')
    | ~ v1_funct_1(k2_funct_1('#skF_2')) ),
    inference(resolution,[status(thm)],[c_2726,c_26])).

tff(c_2780,plain,(
    v2_funct_1(k2_funct_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2496,c_2515,c_2747])).

tff(c_2519,plain,(
    ! [A_220,B_221] :
      ( v1_funct_2(k2_funct_2(A_220,B_221),A_220,A_220)
      | ~ m1_subset_1(B_221,k1_zfmisc_1(k2_zfmisc_1(A_220,A_220)))
      | ~ v3_funct_2(B_221,A_220,A_220)
      | ~ v1_funct_2(B_221,A_220,A_220)
      | ~ v1_funct_1(B_221) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_2523,plain,
    ( v1_funct_2(k2_funct_2('#skF_1','#skF_2'),'#skF_1','#skF_1')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_52,c_2519])).

tff(c_2530,plain,(
    v1_funct_2(k2_funct_1('#skF_2'),'#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_54,c_2494,c_2523])).

tff(c_48,plain,(
    ! [A_38,B_39] :
      ( k1_relset_1(A_38,A_38,B_39) = A_38
      | ~ m1_subset_1(B_39,k1_zfmisc_1(k2_zfmisc_1(A_38,A_38)))
      | ~ v1_funct_2(B_39,A_38,A_38)
      | ~ v1_funct_1(B_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_2741,plain,
    ( k1_relset_1('#skF_1','#skF_1',k2_funct_1('#skF_2')) = '#skF_1'
    | ~ v1_funct_2(k2_funct_1('#skF_2'),'#skF_1','#skF_1')
    | ~ v1_funct_1(k2_funct_1('#skF_2')) ),
    inference(resolution,[status(thm)],[c_2726,c_48])).

tff(c_2774,plain,(
    k1_relset_1('#skF_1','#skF_1',k2_funct_1('#skF_2')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2496,c_2530,c_2741])).

tff(c_20,plain,(
    ! [A_16,B_17,C_18] :
      ( k1_relset_1(A_16,B_17,C_18) = k1_relat_1(C_18)
      | ~ m1_subset_1(C_18,k1_zfmisc_1(k2_zfmisc_1(A_16,B_17))) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_2781,plain,(
    k1_relset_1('#skF_1','#skF_1',k2_funct_1('#skF_2')) = k1_relat_1(k2_funct_1('#skF_2')) ),
    inference(resolution,[status(thm)],[c_2726,c_20])).

tff(c_2866,plain,(
    k1_relat_1(k2_funct_1('#skF_2')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2774,c_2781])).

tff(c_16,plain,(
    ! [A_12] :
      ( k2_funct_1(k2_funct_1(A_12)) = A_12
      | ~ v2_funct_1(A_12)
      | ~ v1_funct_1(A_12)
      | ~ v1_relat_1(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_46,plain,(
    ! [A_37] : k6_relat_1(A_37) = k6_partfun1(A_37) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_12,plain,(
    ! [A_10] :
      ( k5_relat_1(A_10,k2_funct_1(A_10)) = k6_relat_1(k1_relat_1(A_10))
      | ~ v2_funct_1(A_10)
      | ~ v1_funct_1(A_10)
      | ~ v1_relat_1(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_2339,plain,(
    ! [A_185] :
      ( k5_relat_1(A_185,k2_funct_1(A_185)) = k6_partfun1(k1_relat_1(A_185))
      | ~ v2_funct_1(A_185)
      | ~ v1_funct_1(A_185)
      | ~ v1_relat_1(A_185) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_12])).

tff(c_2348,plain,(
    ! [A_12] :
      ( k6_partfun1(k1_relat_1(k2_funct_1(A_12))) = k5_relat_1(k2_funct_1(A_12),A_12)
      | ~ v2_funct_1(k2_funct_1(A_12))
      | ~ v1_funct_1(k2_funct_1(A_12))
      | ~ v1_relat_1(k2_funct_1(A_12))
      | ~ v2_funct_1(A_12)
      | ~ v1_funct_1(A_12)
      | ~ v1_relat_1(A_12) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_2339])).

tff(c_2870,plain,
    ( k5_relat_1(k2_funct_1('#skF_2'),'#skF_2') = k6_partfun1('#skF_1')
    | ~ v2_funct_1(k2_funct_1('#skF_2'))
    | ~ v1_funct_1(k2_funct_1('#skF_2'))
    | ~ v1_relat_1(k2_funct_1('#skF_2'))
    | ~ v2_funct_1('#skF_2')
    | ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_2866,c_2348])).

tff(c_2874,plain,(
    k5_relat_1(k2_funct_1('#skF_2'),'#skF_2') = k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2250,c_58,c_2377,c_2785,c_2496,c_2780,c_2870])).

tff(c_30,plain,(
    ! [A_26,B_27] :
      ( m1_subset_1(k2_funct_2(A_26,B_27),k1_zfmisc_1(k2_zfmisc_1(A_26,A_26)))
      | ~ m1_subset_1(B_27,k1_zfmisc_1(k2_zfmisc_1(A_26,A_26)))
      | ~ v3_funct_2(B_27,A_26,A_26)
      | ~ v1_funct_2(B_27,A_26,A_26)
      | ~ v1_funct_1(B_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_2792,plain,(
    ! [D_228,F_231,C_233,A_230,E_232,B_229] :
      ( k1_partfun1(A_230,B_229,C_233,D_228,E_232,F_231) = k5_relat_1(E_232,F_231)
      | ~ m1_subset_1(F_231,k1_zfmisc_1(k2_zfmisc_1(C_233,D_228)))
      | ~ v1_funct_1(F_231)
      | ~ m1_subset_1(E_232,k1_zfmisc_1(k2_zfmisc_1(A_230,B_229)))
      | ~ v1_funct_1(E_232) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_2800,plain,(
    ! [A_230,B_229,E_232] :
      ( k1_partfun1(A_230,B_229,'#skF_1','#skF_1',E_232,'#skF_2') = k5_relat_1(E_232,'#skF_2')
      | ~ v1_funct_1('#skF_2')
      | ~ m1_subset_1(E_232,k1_zfmisc_1(k2_zfmisc_1(A_230,B_229)))
      | ~ v1_funct_1(E_232) ) ),
    inference(resolution,[status(thm)],[c_52,c_2792])).

tff(c_2835,plain,(
    ! [A_234,B_235,E_236] :
      ( k1_partfun1(A_234,B_235,'#skF_1','#skF_1',E_236,'#skF_2') = k5_relat_1(E_236,'#skF_2')
      | ~ m1_subset_1(E_236,k1_zfmisc_1(k2_zfmisc_1(A_234,B_235)))
      | ~ v1_funct_1(E_236) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_2800])).

tff(c_3241,plain,(
    ! [A_245,B_246] :
      ( k1_partfun1(A_245,A_245,'#skF_1','#skF_1',k2_funct_2(A_245,B_246),'#skF_2') = k5_relat_1(k2_funct_2(A_245,B_246),'#skF_2')
      | ~ v1_funct_1(k2_funct_2(A_245,B_246))
      | ~ m1_subset_1(B_246,k1_zfmisc_1(k2_zfmisc_1(A_245,A_245)))
      | ~ v3_funct_2(B_246,A_245,A_245)
      | ~ v1_funct_2(B_246,A_245,A_245)
      | ~ v1_funct_1(B_246) ) ),
    inference(resolution,[status(thm)],[c_30,c_2835])).

tff(c_3251,plain,
    ( k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1',k2_funct_2('#skF_1','#skF_2'),'#skF_2') = k5_relat_1(k2_funct_2('#skF_1','#skF_2'),'#skF_2')
    | ~ v1_funct_1(k2_funct_2('#skF_1','#skF_2'))
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_52,c_3241])).

tff(c_3265,plain,(
    k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1',k2_funct_1('#skF_2'),'#skF_2') = k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_54,c_2496,c_2494,c_2874,c_2494,c_2494,c_3251])).

tff(c_234,plain,(
    ! [A_77,B_78,C_79,D_80] :
      ( r2_relset_1(A_77,B_78,C_79,C_79)
      | ~ m1_subset_1(D_80,k1_zfmisc_1(k2_zfmisc_1(A_77,B_78)))
      | ~ m1_subset_1(C_79,k1_zfmisc_1(k2_zfmisc_1(A_77,B_78))) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_244,plain,(
    ! [A_81,C_82] :
      ( r2_relset_1(A_81,A_81,C_82,C_82)
      | ~ m1_subset_1(C_82,k1_zfmisc_1(k2_zfmisc_1(A_81,A_81))) ) ),
    inference(resolution,[status(thm)],[c_40,c_234])).

tff(c_252,plain,(
    ! [A_28] : r2_relset_1(A_28,A_28,k6_partfun1(A_28),k6_partfun1(A_28)) ),
    inference(resolution,[status(thm)],[c_40,c_244])).

tff(c_75,plain,(
    ! [C_46,A_47,B_48] :
      ( v1_relat_1(C_46)
      | ~ m1_subset_1(C_46,k1_zfmisc_1(k2_zfmisc_1(A_47,B_48))) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_87,plain,(
    v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_52,c_75])).

tff(c_200,plain,(
    ! [C_70,A_71,B_72] :
      ( v2_funct_1(C_70)
      | ~ v3_funct_2(C_70,A_71,B_72)
      | ~ v1_funct_1(C_70)
      | ~ m1_subset_1(C_70,k1_zfmisc_1(k2_zfmisc_1(A_71,B_72))) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_206,plain,
    ( v2_funct_1('#skF_2')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_52,c_200])).

tff(c_214,plain,(
    v2_funct_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_54,c_206])).

tff(c_316,plain,(
    ! [A_95,B_96] :
      ( k2_funct_2(A_95,B_96) = k2_funct_1(B_96)
      | ~ m1_subset_1(B_96,k1_zfmisc_1(k2_zfmisc_1(A_95,A_95)))
      | ~ v3_funct_2(B_96,A_95,A_95)
      | ~ v1_funct_2(B_96,A_95,A_95)
      | ~ v1_funct_1(B_96) ) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_322,plain,
    ( k2_funct_2('#skF_1','#skF_2') = k2_funct_1('#skF_2')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_52,c_316])).

tff(c_330,plain,(
    k2_funct_2('#skF_1','#skF_2') = k2_funct_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_54,c_322])).

tff(c_511,plain,(
    ! [A_109,B_110] :
      ( m1_subset_1(k2_funct_2(A_109,B_110),k1_zfmisc_1(k2_zfmisc_1(A_109,A_109)))
      | ~ m1_subset_1(B_110,k1_zfmisc_1(k2_zfmisc_1(A_109,A_109)))
      | ~ v3_funct_2(B_110,A_109,A_109)
      | ~ v1_funct_2(B_110,A_109,A_109)
      | ~ v1_funct_1(B_110) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_546,plain,
    ( m1_subset_1(k2_funct_1('#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_330,c_511])).

tff(c_562,plain,(
    m1_subset_1(k2_funct_1('#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_54,c_52,c_546])).

tff(c_591,plain,
    ( v1_relat_1(k2_funct_1('#skF_2'))
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_1')) ),
    inference(resolution,[status(thm)],[c_562,c_6])).

tff(c_621,plain,(
    v1_relat_1(k2_funct_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_591])).

tff(c_291,plain,(
    ! [A_93,B_94] :
      ( v1_funct_1(k2_funct_2(A_93,B_94))
      | ~ m1_subset_1(B_94,k1_zfmisc_1(k2_zfmisc_1(A_93,A_93)))
      | ~ v3_funct_2(B_94,A_93,A_93)
      | ~ v1_funct_2(B_94,A_93,A_93)
      | ~ v1_funct_1(B_94) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_297,plain,
    ( v1_funct_1(k2_funct_2('#skF_1','#skF_2'))
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_52,c_291])).

tff(c_305,plain,(
    v1_funct_1(k2_funct_2('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_54,c_297])).

tff(c_332,plain,(
    v1_funct_1(k2_funct_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_330,c_305])).

tff(c_355,plain,(
    ! [A_103,B_104] :
      ( v3_funct_2(k2_funct_2(A_103,B_104),A_103,A_103)
      | ~ m1_subset_1(B_104,k1_zfmisc_1(k2_zfmisc_1(A_103,A_103)))
      | ~ v3_funct_2(B_104,A_103,A_103)
      | ~ v1_funct_2(B_104,A_103,A_103)
      | ~ v1_funct_1(B_104) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_359,plain,
    ( v3_funct_2(k2_funct_2('#skF_1','#skF_2'),'#skF_1','#skF_1')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_52,c_355])).

tff(c_366,plain,(
    v3_funct_2(k2_funct_1('#skF_2'),'#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_54,c_330,c_359])).

tff(c_583,plain,
    ( v2_funct_1(k2_funct_1('#skF_2'))
    | ~ v3_funct_2(k2_funct_1('#skF_2'),'#skF_1','#skF_1')
    | ~ v1_funct_1(k2_funct_1('#skF_2')) ),
    inference(resolution,[status(thm)],[c_562,c_26])).

tff(c_616,plain,(
    v2_funct_1(k2_funct_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_332,c_366,c_583])).

tff(c_10,plain,(
    ! [A_10] :
      ( k5_relat_1(k2_funct_1(A_10),A_10) = k6_relat_1(k2_relat_1(A_10))
      | ~ v2_funct_1(A_10)
      | ~ v1_funct_1(A_10)
      | ~ v1_relat_1(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_188,plain,(
    ! [A_69] :
      ( k5_relat_1(k2_funct_1(A_69),A_69) = k6_partfun1(k2_relat_1(A_69))
      | ~ v2_funct_1(A_69)
      | ~ v1_funct_1(A_69)
      | ~ v1_relat_1(A_69) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_10])).

tff(c_197,plain,(
    ! [A_12] :
      ( k6_partfun1(k2_relat_1(k2_funct_1(A_12))) = k5_relat_1(A_12,k2_funct_1(A_12))
      | ~ v2_funct_1(k2_funct_1(A_12))
      | ~ v1_funct_1(k2_funct_1(A_12))
      | ~ v1_relat_1(k2_funct_1(A_12))
      | ~ v2_funct_1(A_12)
      | ~ v1_funct_1(A_12)
      | ~ v1_relat_1(A_12) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_188])).

tff(c_340,plain,(
    ! [A_99,B_100] :
      ( v1_funct_2(k2_funct_2(A_99,B_100),A_99,A_99)
      | ~ m1_subset_1(B_100,k1_zfmisc_1(k2_zfmisc_1(A_99,A_99)))
      | ~ v3_funct_2(B_100,A_99,A_99)
      | ~ v1_funct_2(B_100,A_99,A_99)
      | ~ v1_funct_1(B_100) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_344,plain,
    ( v1_funct_2(k2_funct_2('#skF_1','#skF_2'),'#skF_1','#skF_1')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_52,c_340])).

tff(c_351,plain,(
    v1_funct_2(k2_funct_1('#skF_2'),'#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_54,c_330,c_344])).

tff(c_44,plain,(
    ! [A_35,B_36] :
      ( k2_funct_2(A_35,B_36) = k2_funct_1(B_36)
      | ~ m1_subset_1(B_36,k1_zfmisc_1(k2_zfmisc_1(A_35,A_35)))
      | ~ v3_funct_2(B_36,A_35,A_35)
      | ~ v1_funct_2(B_36,A_35,A_35)
      | ~ v1_funct_1(B_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_569,plain,
    ( k2_funct_2('#skF_1',k2_funct_1('#skF_2')) = k2_funct_1(k2_funct_1('#skF_2'))
    | ~ v3_funct_2(k2_funct_1('#skF_2'),'#skF_1','#skF_1')
    | ~ v1_funct_2(k2_funct_1('#skF_2'),'#skF_1','#skF_1')
    | ~ v1_funct_1(k2_funct_1('#skF_2')) ),
    inference(resolution,[status(thm)],[c_562,c_44])).

tff(c_603,plain,(
    k2_funct_2('#skF_1',k2_funct_1('#skF_2')) = k2_funct_1(k2_funct_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_332,c_351,c_366,c_569])).

tff(c_18,plain,(
    ! [C_15,A_13,B_14] :
      ( v1_relat_1(C_15)
      | ~ m1_subset_1(C_15,k1_zfmisc_1(k2_zfmisc_1(A_13,B_14))) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_780,plain,(
    ! [A_120,B_121] :
      ( v1_relat_1(k2_funct_2(A_120,B_121))
      | ~ m1_subset_1(B_121,k1_zfmisc_1(k2_zfmisc_1(A_120,A_120)))
      | ~ v3_funct_2(B_121,A_120,A_120)
      | ~ v1_funct_2(B_121,A_120,A_120)
      | ~ v1_funct_1(B_121) ) ),
    inference(resolution,[status(thm)],[c_511,c_18])).

tff(c_783,plain,
    ( v1_relat_1(k2_funct_2('#skF_1',k2_funct_1('#skF_2')))
    | ~ v3_funct_2(k2_funct_1('#skF_2'),'#skF_1','#skF_1')
    | ~ v1_funct_2(k2_funct_1('#skF_2'),'#skF_1','#skF_1')
    | ~ v1_funct_1(k2_funct_1('#skF_2')) ),
    inference(resolution,[status(thm)],[c_562,c_780])).

tff(c_799,plain,(
    v1_relat_1(k2_funct_1(k2_funct_1('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_332,c_351,c_366,c_603,c_783])).

tff(c_36,plain,(
    ! [A_26,B_27] :
      ( v1_funct_1(k2_funct_2(A_26,B_27))
      | ~ m1_subset_1(B_27,k1_zfmisc_1(k2_zfmisc_1(A_26,A_26)))
      | ~ v3_funct_2(B_27,A_26,A_26)
      | ~ v1_funct_2(B_27,A_26,A_26)
      | ~ v1_funct_1(B_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_572,plain,
    ( v1_funct_1(k2_funct_2('#skF_1',k2_funct_1('#skF_2')))
    | ~ v3_funct_2(k2_funct_1('#skF_2'),'#skF_1','#skF_1')
    | ~ v1_funct_2(k2_funct_1('#skF_2'),'#skF_1','#skF_1')
    | ~ v1_funct_1(k2_funct_1('#skF_2')) ),
    inference(resolution,[status(thm)],[c_562,c_36])).

tff(c_606,plain,(
    v1_funct_1(k2_funct_2('#skF_1',k2_funct_1('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_332,c_351,c_366,c_572])).

tff(c_651,plain,(
    v1_funct_1(k2_funct_1(k2_funct_1('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_603,c_606])).

tff(c_32,plain,(
    ! [A_26,B_27] :
      ( v3_funct_2(k2_funct_2(A_26,B_27),A_26,A_26)
      | ~ m1_subset_1(B_27,k1_zfmisc_1(k2_zfmisc_1(A_26,A_26)))
      | ~ v3_funct_2(B_27,A_26,A_26)
      | ~ v1_funct_2(B_27,A_26,A_26)
      | ~ v1_funct_1(B_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_564,plain,
    ( v3_funct_2(k2_funct_2('#skF_1',k2_funct_1('#skF_2')),'#skF_1','#skF_1')
    | ~ v3_funct_2(k2_funct_1('#skF_2'),'#skF_1','#skF_1')
    | ~ v1_funct_2(k2_funct_1('#skF_2'),'#skF_1','#skF_1')
    | ~ v1_funct_1(k2_funct_1('#skF_2')) ),
    inference(resolution,[status(thm)],[c_562,c_32])).

tff(c_597,plain,(
    v3_funct_2(k2_funct_2('#skF_1',k2_funct_1('#skF_2')),'#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_332,c_351,c_366,c_564])).

tff(c_649,plain,(
    v3_funct_2(k2_funct_1(k2_funct_1('#skF_2')),'#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_603,c_597])).

tff(c_655,plain,
    ( m1_subset_1(k2_funct_1(k2_funct_1('#skF_2')),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k2_funct_1('#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ v3_funct_2(k2_funct_1('#skF_2'),'#skF_1','#skF_1')
    | ~ v1_funct_2(k2_funct_1('#skF_2'),'#skF_1','#skF_1')
    | ~ v1_funct_1(k2_funct_1('#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_603,c_30])).

tff(c_659,plain,(
    m1_subset_1(k2_funct_1(k2_funct_1('#skF_2')),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_332,c_351,c_366,c_562,c_655])).

tff(c_844,plain,
    ( v2_funct_1(k2_funct_1(k2_funct_1('#skF_2')))
    | ~ v3_funct_2(k2_funct_1(k2_funct_1('#skF_2')),'#skF_1','#skF_1')
    | ~ v1_funct_1(k2_funct_1(k2_funct_1('#skF_2'))) ),
    inference(resolution,[status(thm)],[c_659,c_26])).

tff(c_889,plain,(
    v2_funct_1(k2_funct_1(k2_funct_1('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_651,c_649,c_844])).

tff(c_34,plain,(
    ! [A_26,B_27] :
      ( v1_funct_2(k2_funct_2(A_26,B_27),A_26,A_26)
      | ~ m1_subset_1(B_27,k1_zfmisc_1(k2_zfmisc_1(A_26,A_26)))
      | ~ v3_funct_2(B_27,A_26,A_26)
      | ~ v1_funct_2(B_27,A_26,A_26)
      | ~ v1_funct_1(B_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_566,plain,
    ( v1_funct_2(k2_funct_2('#skF_1',k2_funct_1('#skF_2')),'#skF_1','#skF_1')
    | ~ v3_funct_2(k2_funct_1('#skF_2'),'#skF_1','#skF_1')
    | ~ v1_funct_2(k2_funct_1('#skF_2'),'#skF_1','#skF_1')
    | ~ v1_funct_1(k2_funct_1('#skF_2')) ),
    inference(resolution,[status(thm)],[c_562,c_34])).

tff(c_600,plain,(
    v1_funct_2(k2_funct_2('#skF_1',k2_funct_1('#skF_2')),'#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_332,c_351,c_366,c_566])).

tff(c_650,plain,(
    v1_funct_2(k2_funct_1(k2_funct_1('#skF_2')),'#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_603,c_600])).

tff(c_836,plain,
    ( k1_relset_1('#skF_1','#skF_1',k2_funct_1(k2_funct_1('#skF_2'))) = '#skF_1'
    | ~ v1_funct_2(k2_funct_1(k2_funct_1('#skF_2')),'#skF_1','#skF_1')
    | ~ v1_funct_1(k2_funct_1(k2_funct_1('#skF_2'))) ),
    inference(resolution,[status(thm)],[c_659,c_48])).

tff(c_882,plain,(
    k1_relset_1('#skF_1','#skF_1',k2_funct_1(k2_funct_1('#skF_2'))) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_651,c_650,c_836])).

tff(c_1218,plain,(
    ! [A_130,B_131] :
      ( k1_relset_1(A_130,A_130,k2_funct_2(A_130,B_131)) = k1_relat_1(k2_funct_2(A_130,B_131))
      | ~ m1_subset_1(B_131,k1_zfmisc_1(k2_zfmisc_1(A_130,A_130)))
      | ~ v3_funct_2(B_131,A_130,A_130)
      | ~ v1_funct_2(B_131,A_130,A_130)
      | ~ v1_funct_1(B_131) ) ),
    inference(resolution,[status(thm)],[c_511,c_20])).

tff(c_1222,plain,
    ( k1_relset_1('#skF_1','#skF_1',k2_funct_2('#skF_1',k2_funct_1('#skF_2'))) = k1_relat_1(k2_funct_2('#skF_1',k2_funct_1('#skF_2')))
    | ~ v3_funct_2(k2_funct_1('#skF_2'),'#skF_1','#skF_1')
    | ~ v1_funct_2(k2_funct_1('#skF_2'),'#skF_1','#skF_1')
    | ~ v1_funct_1(k2_funct_1('#skF_2')) ),
    inference(resolution,[status(thm)],[c_562,c_1218])).

tff(c_1237,plain,(
    k1_relat_1(k2_funct_1(k2_funct_1('#skF_2'))) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_332,c_351,c_366,c_882,c_603,c_603,c_1222])).

tff(c_830,plain,
    ( k2_funct_2('#skF_1',k2_funct_1(k2_funct_1('#skF_2'))) = k2_funct_1(k2_funct_1(k2_funct_1('#skF_2')))
    | ~ v3_funct_2(k2_funct_1(k2_funct_1('#skF_2')),'#skF_1','#skF_1')
    | ~ v1_funct_2(k2_funct_1(k2_funct_1('#skF_2')),'#skF_1','#skF_1')
    | ~ v1_funct_1(k2_funct_1(k2_funct_1('#skF_2'))) ),
    inference(resolution,[status(thm)],[c_659,c_44])).

tff(c_876,plain,(
    k2_funct_2('#skF_1',k2_funct_1(k2_funct_1('#skF_2'))) = k2_funct_1(k2_funct_1(k2_funct_1('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_651,c_650,c_649,c_830])).

tff(c_958,plain,
    ( k2_funct_1(k2_funct_1(k2_funct_1('#skF_2'))) = k2_funct_2('#skF_1','#skF_2')
    | ~ v2_funct_1('#skF_2')
    | ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_876])).

tff(c_964,plain,(
    k2_funct_1(k2_funct_1(k2_funct_1('#skF_2'))) = k2_funct_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_87,c_58,c_214,c_330,c_958])).

tff(c_999,plain,
    ( k6_partfun1(k2_relat_1(k2_funct_1(k2_funct_1(k2_funct_1('#skF_2'))))) = k5_relat_1(k2_funct_1(k2_funct_1('#skF_2')),k2_funct_1('#skF_2'))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1('#skF_2'))))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1('#skF_2'))))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1('#skF_2'))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1('#skF_2')))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1('#skF_2')))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1('#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_964,c_197])).

tff(c_1028,plain,(
    k5_relat_1(k2_funct_1(k2_funct_1('#skF_2')),k2_funct_1('#skF_2')) = k6_partfun1(k2_relat_1(k2_funct_1('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_799,c_651,c_889,c_621,c_964,c_332,c_964,c_616,c_964,c_964,c_999])).

tff(c_176,plain,(
    ! [A_68] :
      ( k5_relat_1(A_68,k2_funct_1(A_68)) = k6_partfun1(k1_relat_1(A_68))
      | ~ v2_funct_1(A_68)
      | ~ v1_funct_1(A_68)
      | ~ v1_relat_1(A_68) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_12])).

tff(c_185,plain,(
    ! [A_12] :
      ( k6_partfun1(k1_relat_1(k2_funct_1(A_12))) = k5_relat_1(k2_funct_1(A_12),A_12)
      | ~ v2_funct_1(k2_funct_1(A_12))
      | ~ v1_funct_1(k2_funct_1(A_12))
      | ~ v1_relat_1(k2_funct_1(A_12))
      | ~ v2_funct_1(A_12)
      | ~ v1_funct_1(A_12)
      | ~ v1_relat_1(A_12) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_176])).

tff(c_1399,plain,
    ( k6_partfun1(k1_relat_1(k2_funct_1(k2_funct_1('#skF_2')))) = k6_partfun1(k2_relat_1(k2_funct_1('#skF_2')))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1('#skF_2')))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1('#skF_2')))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1('#skF_2')))
    | ~ v2_funct_1(k2_funct_1('#skF_2'))
    | ~ v1_funct_1(k2_funct_1('#skF_2'))
    | ~ v1_relat_1(k2_funct_1('#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1028,c_185])).

tff(c_1415,plain,(
    k6_partfun1(k2_relat_1(k2_funct_1('#skF_2'))) = k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_621,c_332,c_616,c_799,c_651,c_889,c_1237,c_1399])).

tff(c_1478,plain,
    ( k5_relat_1('#skF_2',k2_funct_1('#skF_2')) = k6_partfun1('#skF_1')
    | ~ v2_funct_1(k2_funct_1('#skF_2'))
    | ~ v1_funct_1(k2_funct_1('#skF_2'))
    | ~ v1_relat_1(k2_funct_1('#skF_2'))
    | ~ v2_funct_1('#skF_2')
    | ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_197,c_1415])).

tff(c_1497,plain,(
    k5_relat_1('#skF_2',k2_funct_1('#skF_2')) = k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_87,c_58,c_214,c_621,c_332,c_616,c_1478])).

tff(c_628,plain,(
    ! [E_115,A_113,D_111,C_116,F_114,B_112] :
      ( k1_partfun1(A_113,B_112,C_116,D_111,E_115,F_114) = k5_relat_1(E_115,F_114)
      | ~ m1_subset_1(F_114,k1_zfmisc_1(k2_zfmisc_1(C_116,D_111)))
      | ~ v1_funct_1(F_114)
      | ~ m1_subset_1(E_115,k1_zfmisc_1(k2_zfmisc_1(A_113,B_112)))
      | ~ v1_funct_1(E_115) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_630,plain,(
    ! [A_113,B_112,E_115] :
      ( k1_partfun1(A_113,B_112,'#skF_1','#skF_1',E_115,k2_funct_1('#skF_2')) = k5_relat_1(E_115,k2_funct_1('#skF_2'))
      | ~ v1_funct_1(k2_funct_1('#skF_2'))
      | ~ m1_subset_1(E_115,k1_zfmisc_1(k2_zfmisc_1(A_113,B_112)))
      | ~ v1_funct_1(E_115) ) ),
    inference(resolution,[status(thm)],[c_562,c_628])).

tff(c_2180,plain,(
    ! [A_160,B_161,E_162] :
      ( k1_partfun1(A_160,B_161,'#skF_1','#skF_1',E_162,k2_funct_1('#skF_2')) = k5_relat_1(E_162,k2_funct_1('#skF_2'))
      | ~ m1_subset_1(E_162,k1_zfmisc_1(k2_zfmisc_1(A_160,B_161)))
      | ~ v1_funct_1(E_162) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_332,c_630])).

tff(c_2210,plain,
    ( k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2',k2_funct_1('#skF_2')) = k5_relat_1('#skF_2',k2_funct_1('#skF_2'))
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_52,c_2180])).

tff(c_2230,plain,(
    k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2',k2_funct_1('#skF_2')) = k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_1497,c_2210])).

tff(c_50,plain,
    ( ~ r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1',k2_funct_2('#skF_1','#skF_2'),'#skF_2'),k6_partfun1('#skF_1'))
    | ~ r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2',k2_funct_2('#skF_1','#skF_2')),k6_partfun1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_74,plain,(
    ~ r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2',k2_funct_2('#skF_1','#skF_2')),k6_partfun1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_50])).

tff(c_333,plain,(
    ~ r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2',k2_funct_1('#skF_2')),k6_partfun1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_330,c_74])).

tff(c_2232,plain,(
    ~ r2_relset_1('#skF_1','#skF_1',k6_partfun1('#skF_1'),k6_partfun1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2230,c_333])).

tff(c_2235,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_252,c_2232])).

tff(c_2236,plain,(
    ~ r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1',k2_funct_2('#skF_1','#skF_2'),'#skF_2'),k6_partfun1('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_2498,plain,(
    ~ r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1',k2_funct_1('#skF_2'),'#skF_2'),k6_partfun1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2494,c_2236])).

tff(c_3417,plain,(
    ~ r2_relset_1('#skF_1','#skF_1',k6_partfun1('#skF_1'),k6_partfun1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3265,c_2498])).

tff(c_3420,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2444,c_3417])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:34:38 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.74/2.11  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.74/2.14  
% 5.74/2.14  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.74/2.14  %$ r2_relset_1 > v3_funct_2 > v1_funct_2 > v2_funct_2 > v1_partfun1 > r2_hidden > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > k2_funct_2 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1
% 5.74/2.14  
% 5.74/2.14  %Foreground sorts:
% 5.74/2.14  
% 5.74/2.14  
% 5.74/2.14  %Background operators:
% 5.74/2.14  
% 5.74/2.14  
% 5.74/2.14  %Foreground operators:
% 5.74/2.14  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 5.74/2.14  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 5.74/2.14  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 5.74/2.14  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.74/2.14  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 5.74/2.14  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.74/2.14  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.74/2.14  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 5.74/2.14  tff(k2_funct_2, type, k2_funct_2: ($i * $i) > $i).
% 5.74/2.14  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 5.74/2.14  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 5.74/2.14  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 5.74/2.14  tff('#skF_2', type, '#skF_2': $i).
% 5.74/2.14  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 5.74/2.14  tff('#skF_1', type, '#skF_1': $i).
% 5.74/2.14  tff(v2_funct_2, type, v2_funct_2: ($i * $i) > $o).
% 5.74/2.14  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 5.74/2.14  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.74/2.14  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 5.74/2.14  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.74/2.14  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.74/2.14  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 5.74/2.14  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 5.74/2.14  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.74/2.14  tff(v3_funct_2, type, v3_funct_2: ($i * $i * $i) > $o).
% 5.74/2.14  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 5.74/2.14  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.74/2.14  
% 5.95/2.17  tff(f_114, axiom, (![A]: (v1_partfun1(k6_partfun1(A), A) & m1_subset_1(k6_partfun1(A), k1_zfmisc_1(k2_zfmisc_1(A, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_partfun1)).
% 5.95/2.17  tff(f_82, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => r2_relset_1(A, B, C, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', reflexivity_r2_relset_1)).
% 5.95/2.17  tff(f_157, negated_conjecture, ~(![A, B]: ((((v1_funct_1(B) & v1_funct_2(B, A, A)) & v3_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (r2_relset_1(A, A, k1_partfun1(A, A, A, A, B, k2_funct_2(A, B)), k6_partfun1(A)) & r2_relset_1(A, A, k1_partfun1(A, A, A, A, k2_funct_2(A, B), B), k6_partfun1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t88_funct_2)).
% 5.95/2.17  tff(f_134, axiom, (![A, B]: ((((v1_funct_1(B) & v1_funct_2(B, A, A)) & v3_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (k2_funct_2(A, B) = k2_funct_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_funct_2)).
% 5.95/2.17  tff(f_110, axiom, (![A, B]: ((((v1_funct_1(B) & v1_funct_2(B, A, A)) & v3_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (((v1_funct_1(k2_funct_2(A, B)) & v1_funct_2(k2_funct_2(A, B), A, A)) & v3_funct_2(k2_funct_2(A, B), A, A)) & m1_subset_1(k2_funct_2(A, B), k1_zfmisc_1(k2_zfmisc_1(A, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_funct_2)).
% 5.95/2.17  tff(f_72, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 5.95/2.17  tff(f_94, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v3_funct_2(C, A, B)) => ((v1_funct_1(C) & v2_funct_1(C)) & v2_funct_2(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_funct_2)).
% 5.95/2.17  tff(f_42, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 5.95/2.17  tff(f_40, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 5.95/2.17  tff(f_144, axiom, (![A, B]: (((v1_funct_1(B) & v1_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (k1_relset_1(A, A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t67_funct_2)).
% 5.95/2.17  tff(f_76, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 5.95/2.17  tff(f_68, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => (k2_funct_1(k2_funct_1(A)) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_funct_1)).
% 5.95/2.17  tff(f_136, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 5.95/2.17  tff(f_52, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k5_relat_1(A, k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))) & (k5_relat_1(k2_funct_1(A), A) = k6_relat_1(k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t61_funct_1)).
% 5.95/2.17  tff(f_124, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 5.95/2.17  tff(c_40, plain, (![A_28]: (m1_subset_1(k6_partfun1(A_28), k1_zfmisc_1(k2_zfmisc_1(A_28, A_28))))), inference(cnfTransformation, [status(thm)], [f_114])).
% 5.95/2.17  tff(c_2426, plain, (![A_198, B_199, C_200, D_201]: (r2_relset_1(A_198, B_199, C_200, C_200) | ~m1_subset_1(D_201, k1_zfmisc_1(k2_zfmisc_1(A_198, B_199))) | ~m1_subset_1(C_200, k1_zfmisc_1(k2_zfmisc_1(A_198, B_199))))), inference(cnfTransformation, [status(thm)], [f_82])).
% 5.95/2.17  tff(c_2436, plain, (![A_202, C_203]: (r2_relset_1(A_202, A_202, C_203, C_203) | ~m1_subset_1(C_203, k1_zfmisc_1(k2_zfmisc_1(A_202, A_202))))), inference(resolution, [status(thm)], [c_40, c_2426])).
% 5.95/2.17  tff(c_2444, plain, (![A_28]: (r2_relset_1(A_28, A_28, k6_partfun1(A_28), k6_partfun1(A_28)))), inference(resolution, [status(thm)], [c_40, c_2436])).
% 5.95/2.17  tff(c_58, plain, (v1_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_157])).
% 5.95/2.17  tff(c_56, plain, (v1_funct_2('#skF_2', '#skF_1', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_157])).
% 5.95/2.17  tff(c_54, plain, (v3_funct_2('#skF_2', '#skF_1', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_157])).
% 5.95/2.17  tff(c_52, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_157])).
% 5.95/2.17  tff(c_2480, plain, (![A_213, B_214]: (k2_funct_2(A_213, B_214)=k2_funct_1(B_214) | ~m1_subset_1(B_214, k1_zfmisc_1(k2_zfmisc_1(A_213, A_213))) | ~v3_funct_2(B_214, A_213, A_213) | ~v1_funct_2(B_214, A_213, A_213) | ~v1_funct_1(B_214))), inference(cnfTransformation, [status(thm)], [f_134])).
% 5.95/2.17  tff(c_2486, plain, (k2_funct_2('#skF_1', '#skF_2')=k2_funct_1('#skF_2') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_52, c_2480])).
% 5.95/2.17  tff(c_2494, plain, (k2_funct_2('#skF_1', '#skF_2')=k2_funct_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_54, c_2486])).
% 5.95/2.17  tff(c_2449, plain, (![A_206, B_207]: (v1_funct_1(k2_funct_2(A_206, B_207)) | ~m1_subset_1(B_207, k1_zfmisc_1(k2_zfmisc_1(A_206, A_206))) | ~v3_funct_2(B_207, A_206, A_206) | ~v1_funct_2(B_207, A_206, A_206) | ~v1_funct_1(B_207))), inference(cnfTransformation, [status(thm)], [f_110])).
% 5.95/2.17  tff(c_2455, plain, (v1_funct_1(k2_funct_2('#skF_1', '#skF_2')) | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_52, c_2449])).
% 5.95/2.17  tff(c_2463, plain, (v1_funct_1(k2_funct_2('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_54, c_2455])).
% 5.95/2.17  tff(c_2496, plain, (v1_funct_1(k2_funct_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_2494, c_2463])).
% 5.95/2.17  tff(c_2238, plain, (![C_163, A_164, B_165]: (v1_relat_1(C_163) | ~m1_subset_1(C_163, k1_zfmisc_1(k2_zfmisc_1(A_164, B_165))))), inference(cnfTransformation, [status(thm)], [f_72])).
% 5.95/2.17  tff(c_2250, plain, (v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_52, c_2238])).
% 5.95/2.17  tff(c_2363, plain, (![C_187, A_188, B_189]: (v2_funct_1(C_187) | ~v3_funct_2(C_187, A_188, B_189) | ~v1_funct_1(C_187) | ~m1_subset_1(C_187, k1_zfmisc_1(k2_zfmisc_1(A_188, B_189))))), inference(cnfTransformation, [status(thm)], [f_94])).
% 5.95/2.17  tff(c_2369, plain, (v2_funct_1('#skF_2') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_52, c_2363])).
% 5.95/2.17  tff(c_2377, plain, (v2_funct_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_54, c_2369])).
% 5.95/2.17  tff(c_8, plain, (![A_8, B_9]: (v1_relat_1(k2_zfmisc_1(A_8, B_9)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 5.95/2.17  tff(c_2675, plain, (![A_226, B_227]: (m1_subset_1(k2_funct_2(A_226, B_227), k1_zfmisc_1(k2_zfmisc_1(A_226, A_226))) | ~m1_subset_1(B_227, k1_zfmisc_1(k2_zfmisc_1(A_226, A_226))) | ~v3_funct_2(B_227, A_226, A_226) | ~v1_funct_2(B_227, A_226, A_226) | ~v1_funct_1(B_227))), inference(cnfTransformation, [status(thm)], [f_110])).
% 5.95/2.17  tff(c_2710, plain, (m1_subset_1(k2_funct_1('#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_2494, c_2675])).
% 5.95/2.17  tff(c_2726, plain, (m1_subset_1(k2_funct_1('#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_54, c_52, c_2710])).
% 5.95/2.17  tff(c_6, plain, (![B_7, A_5]: (v1_relat_1(B_7) | ~m1_subset_1(B_7, k1_zfmisc_1(A_5)) | ~v1_relat_1(A_5))), inference(cnfTransformation, [status(thm)], [f_40])).
% 5.95/2.17  tff(c_2755, plain, (v1_relat_1(k2_funct_1('#skF_2')) | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_1'))), inference(resolution, [status(thm)], [c_2726, c_6])).
% 5.95/2.17  tff(c_2785, plain, (v1_relat_1(k2_funct_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_2755])).
% 5.95/2.17  tff(c_2504, plain, (![A_216, B_217]: (v3_funct_2(k2_funct_2(A_216, B_217), A_216, A_216) | ~m1_subset_1(B_217, k1_zfmisc_1(k2_zfmisc_1(A_216, A_216))) | ~v3_funct_2(B_217, A_216, A_216) | ~v1_funct_2(B_217, A_216, A_216) | ~v1_funct_1(B_217))), inference(cnfTransformation, [status(thm)], [f_110])).
% 5.95/2.17  tff(c_2508, plain, (v3_funct_2(k2_funct_2('#skF_1', '#skF_2'), '#skF_1', '#skF_1') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_52, c_2504])).
% 5.95/2.17  tff(c_2515, plain, (v3_funct_2(k2_funct_1('#skF_2'), '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_54, c_2494, c_2508])).
% 5.95/2.17  tff(c_26, plain, (![C_25, A_23, B_24]: (v2_funct_1(C_25) | ~v3_funct_2(C_25, A_23, B_24) | ~v1_funct_1(C_25) | ~m1_subset_1(C_25, k1_zfmisc_1(k2_zfmisc_1(A_23, B_24))))), inference(cnfTransformation, [status(thm)], [f_94])).
% 5.95/2.17  tff(c_2747, plain, (v2_funct_1(k2_funct_1('#skF_2')) | ~v3_funct_2(k2_funct_1('#skF_2'), '#skF_1', '#skF_1') | ~v1_funct_1(k2_funct_1('#skF_2'))), inference(resolution, [status(thm)], [c_2726, c_26])).
% 5.95/2.17  tff(c_2780, plain, (v2_funct_1(k2_funct_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_2496, c_2515, c_2747])).
% 5.95/2.17  tff(c_2519, plain, (![A_220, B_221]: (v1_funct_2(k2_funct_2(A_220, B_221), A_220, A_220) | ~m1_subset_1(B_221, k1_zfmisc_1(k2_zfmisc_1(A_220, A_220))) | ~v3_funct_2(B_221, A_220, A_220) | ~v1_funct_2(B_221, A_220, A_220) | ~v1_funct_1(B_221))), inference(cnfTransformation, [status(thm)], [f_110])).
% 5.95/2.17  tff(c_2523, plain, (v1_funct_2(k2_funct_2('#skF_1', '#skF_2'), '#skF_1', '#skF_1') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_52, c_2519])).
% 5.95/2.17  tff(c_2530, plain, (v1_funct_2(k2_funct_1('#skF_2'), '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_54, c_2494, c_2523])).
% 5.95/2.17  tff(c_48, plain, (![A_38, B_39]: (k1_relset_1(A_38, A_38, B_39)=A_38 | ~m1_subset_1(B_39, k1_zfmisc_1(k2_zfmisc_1(A_38, A_38))) | ~v1_funct_2(B_39, A_38, A_38) | ~v1_funct_1(B_39))), inference(cnfTransformation, [status(thm)], [f_144])).
% 5.95/2.17  tff(c_2741, plain, (k1_relset_1('#skF_1', '#skF_1', k2_funct_1('#skF_2'))='#skF_1' | ~v1_funct_2(k2_funct_1('#skF_2'), '#skF_1', '#skF_1') | ~v1_funct_1(k2_funct_1('#skF_2'))), inference(resolution, [status(thm)], [c_2726, c_48])).
% 5.95/2.17  tff(c_2774, plain, (k1_relset_1('#skF_1', '#skF_1', k2_funct_1('#skF_2'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_2496, c_2530, c_2741])).
% 5.95/2.17  tff(c_20, plain, (![A_16, B_17, C_18]: (k1_relset_1(A_16, B_17, C_18)=k1_relat_1(C_18) | ~m1_subset_1(C_18, k1_zfmisc_1(k2_zfmisc_1(A_16, B_17))))), inference(cnfTransformation, [status(thm)], [f_76])).
% 5.95/2.17  tff(c_2781, plain, (k1_relset_1('#skF_1', '#skF_1', k2_funct_1('#skF_2'))=k1_relat_1(k2_funct_1('#skF_2'))), inference(resolution, [status(thm)], [c_2726, c_20])).
% 5.95/2.17  tff(c_2866, plain, (k1_relat_1(k2_funct_1('#skF_2'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_2774, c_2781])).
% 5.95/2.17  tff(c_16, plain, (![A_12]: (k2_funct_1(k2_funct_1(A_12))=A_12 | ~v2_funct_1(A_12) | ~v1_funct_1(A_12) | ~v1_relat_1(A_12))), inference(cnfTransformation, [status(thm)], [f_68])).
% 5.95/2.17  tff(c_46, plain, (![A_37]: (k6_relat_1(A_37)=k6_partfun1(A_37))), inference(cnfTransformation, [status(thm)], [f_136])).
% 5.95/2.17  tff(c_12, plain, (![A_10]: (k5_relat_1(A_10, k2_funct_1(A_10))=k6_relat_1(k1_relat_1(A_10)) | ~v2_funct_1(A_10) | ~v1_funct_1(A_10) | ~v1_relat_1(A_10))), inference(cnfTransformation, [status(thm)], [f_52])).
% 5.95/2.17  tff(c_2339, plain, (![A_185]: (k5_relat_1(A_185, k2_funct_1(A_185))=k6_partfun1(k1_relat_1(A_185)) | ~v2_funct_1(A_185) | ~v1_funct_1(A_185) | ~v1_relat_1(A_185))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_12])).
% 5.95/2.17  tff(c_2348, plain, (![A_12]: (k6_partfun1(k1_relat_1(k2_funct_1(A_12)))=k5_relat_1(k2_funct_1(A_12), A_12) | ~v2_funct_1(k2_funct_1(A_12)) | ~v1_funct_1(k2_funct_1(A_12)) | ~v1_relat_1(k2_funct_1(A_12)) | ~v2_funct_1(A_12) | ~v1_funct_1(A_12) | ~v1_relat_1(A_12))), inference(superposition, [status(thm), theory('equality')], [c_16, c_2339])).
% 5.95/2.17  tff(c_2870, plain, (k5_relat_1(k2_funct_1('#skF_2'), '#skF_2')=k6_partfun1('#skF_1') | ~v2_funct_1(k2_funct_1('#skF_2')) | ~v1_funct_1(k2_funct_1('#skF_2')) | ~v1_relat_1(k2_funct_1('#skF_2')) | ~v2_funct_1('#skF_2') | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_2866, c_2348])).
% 5.95/2.17  tff(c_2874, plain, (k5_relat_1(k2_funct_1('#skF_2'), '#skF_2')=k6_partfun1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2250, c_58, c_2377, c_2785, c_2496, c_2780, c_2870])).
% 5.95/2.17  tff(c_30, plain, (![A_26, B_27]: (m1_subset_1(k2_funct_2(A_26, B_27), k1_zfmisc_1(k2_zfmisc_1(A_26, A_26))) | ~m1_subset_1(B_27, k1_zfmisc_1(k2_zfmisc_1(A_26, A_26))) | ~v3_funct_2(B_27, A_26, A_26) | ~v1_funct_2(B_27, A_26, A_26) | ~v1_funct_1(B_27))), inference(cnfTransformation, [status(thm)], [f_110])).
% 5.95/2.17  tff(c_2792, plain, (![D_228, F_231, C_233, A_230, E_232, B_229]: (k1_partfun1(A_230, B_229, C_233, D_228, E_232, F_231)=k5_relat_1(E_232, F_231) | ~m1_subset_1(F_231, k1_zfmisc_1(k2_zfmisc_1(C_233, D_228))) | ~v1_funct_1(F_231) | ~m1_subset_1(E_232, k1_zfmisc_1(k2_zfmisc_1(A_230, B_229))) | ~v1_funct_1(E_232))), inference(cnfTransformation, [status(thm)], [f_124])).
% 5.95/2.17  tff(c_2800, plain, (![A_230, B_229, E_232]: (k1_partfun1(A_230, B_229, '#skF_1', '#skF_1', E_232, '#skF_2')=k5_relat_1(E_232, '#skF_2') | ~v1_funct_1('#skF_2') | ~m1_subset_1(E_232, k1_zfmisc_1(k2_zfmisc_1(A_230, B_229))) | ~v1_funct_1(E_232))), inference(resolution, [status(thm)], [c_52, c_2792])).
% 5.95/2.17  tff(c_2835, plain, (![A_234, B_235, E_236]: (k1_partfun1(A_234, B_235, '#skF_1', '#skF_1', E_236, '#skF_2')=k5_relat_1(E_236, '#skF_2') | ~m1_subset_1(E_236, k1_zfmisc_1(k2_zfmisc_1(A_234, B_235))) | ~v1_funct_1(E_236))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_2800])).
% 5.95/2.17  tff(c_3241, plain, (![A_245, B_246]: (k1_partfun1(A_245, A_245, '#skF_1', '#skF_1', k2_funct_2(A_245, B_246), '#skF_2')=k5_relat_1(k2_funct_2(A_245, B_246), '#skF_2') | ~v1_funct_1(k2_funct_2(A_245, B_246)) | ~m1_subset_1(B_246, k1_zfmisc_1(k2_zfmisc_1(A_245, A_245))) | ~v3_funct_2(B_246, A_245, A_245) | ~v1_funct_2(B_246, A_245, A_245) | ~v1_funct_1(B_246))), inference(resolution, [status(thm)], [c_30, c_2835])).
% 5.95/2.17  tff(c_3251, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', k2_funct_2('#skF_1', '#skF_2'), '#skF_2')=k5_relat_1(k2_funct_2('#skF_1', '#skF_2'), '#skF_2') | ~v1_funct_1(k2_funct_2('#skF_1', '#skF_2')) | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_52, c_3241])).
% 5.95/2.17  tff(c_3265, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', k2_funct_1('#skF_2'), '#skF_2')=k6_partfun1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_54, c_2496, c_2494, c_2874, c_2494, c_2494, c_3251])).
% 5.95/2.17  tff(c_234, plain, (![A_77, B_78, C_79, D_80]: (r2_relset_1(A_77, B_78, C_79, C_79) | ~m1_subset_1(D_80, k1_zfmisc_1(k2_zfmisc_1(A_77, B_78))) | ~m1_subset_1(C_79, k1_zfmisc_1(k2_zfmisc_1(A_77, B_78))))), inference(cnfTransformation, [status(thm)], [f_82])).
% 5.95/2.17  tff(c_244, plain, (![A_81, C_82]: (r2_relset_1(A_81, A_81, C_82, C_82) | ~m1_subset_1(C_82, k1_zfmisc_1(k2_zfmisc_1(A_81, A_81))))), inference(resolution, [status(thm)], [c_40, c_234])).
% 5.95/2.17  tff(c_252, plain, (![A_28]: (r2_relset_1(A_28, A_28, k6_partfun1(A_28), k6_partfun1(A_28)))), inference(resolution, [status(thm)], [c_40, c_244])).
% 5.95/2.17  tff(c_75, plain, (![C_46, A_47, B_48]: (v1_relat_1(C_46) | ~m1_subset_1(C_46, k1_zfmisc_1(k2_zfmisc_1(A_47, B_48))))), inference(cnfTransformation, [status(thm)], [f_72])).
% 5.95/2.17  tff(c_87, plain, (v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_52, c_75])).
% 5.95/2.17  tff(c_200, plain, (![C_70, A_71, B_72]: (v2_funct_1(C_70) | ~v3_funct_2(C_70, A_71, B_72) | ~v1_funct_1(C_70) | ~m1_subset_1(C_70, k1_zfmisc_1(k2_zfmisc_1(A_71, B_72))))), inference(cnfTransformation, [status(thm)], [f_94])).
% 5.95/2.17  tff(c_206, plain, (v2_funct_1('#skF_2') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_52, c_200])).
% 5.95/2.17  tff(c_214, plain, (v2_funct_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_54, c_206])).
% 5.95/2.17  tff(c_316, plain, (![A_95, B_96]: (k2_funct_2(A_95, B_96)=k2_funct_1(B_96) | ~m1_subset_1(B_96, k1_zfmisc_1(k2_zfmisc_1(A_95, A_95))) | ~v3_funct_2(B_96, A_95, A_95) | ~v1_funct_2(B_96, A_95, A_95) | ~v1_funct_1(B_96))), inference(cnfTransformation, [status(thm)], [f_134])).
% 5.95/2.17  tff(c_322, plain, (k2_funct_2('#skF_1', '#skF_2')=k2_funct_1('#skF_2') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_52, c_316])).
% 5.95/2.17  tff(c_330, plain, (k2_funct_2('#skF_1', '#skF_2')=k2_funct_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_54, c_322])).
% 5.95/2.17  tff(c_511, plain, (![A_109, B_110]: (m1_subset_1(k2_funct_2(A_109, B_110), k1_zfmisc_1(k2_zfmisc_1(A_109, A_109))) | ~m1_subset_1(B_110, k1_zfmisc_1(k2_zfmisc_1(A_109, A_109))) | ~v3_funct_2(B_110, A_109, A_109) | ~v1_funct_2(B_110, A_109, A_109) | ~v1_funct_1(B_110))), inference(cnfTransformation, [status(thm)], [f_110])).
% 5.95/2.17  tff(c_546, plain, (m1_subset_1(k2_funct_1('#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_330, c_511])).
% 5.95/2.17  tff(c_562, plain, (m1_subset_1(k2_funct_1('#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_54, c_52, c_546])).
% 5.95/2.17  tff(c_591, plain, (v1_relat_1(k2_funct_1('#skF_2')) | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_1'))), inference(resolution, [status(thm)], [c_562, c_6])).
% 5.95/2.17  tff(c_621, plain, (v1_relat_1(k2_funct_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_591])).
% 5.95/2.17  tff(c_291, plain, (![A_93, B_94]: (v1_funct_1(k2_funct_2(A_93, B_94)) | ~m1_subset_1(B_94, k1_zfmisc_1(k2_zfmisc_1(A_93, A_93))) | ~v3_funct_2(B_94, A_93, A_93) | ~v1_funct_2(B_94, A_93, A_93) | ~v1_funct_1(B_94))), inference(cnfTransformation, [status(thm)], [f_110])).
% 5.95/2.17  tff(c_297, plain, (v1_funct_1(k2_funct_2('#skF_1', '#skF_2')) | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_52, c_291])).
% 5.95/2.17  tff(c_305, plain, (v1_funct_1(k2_funct_2('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_54, c_297])).
% 5.95/2.17  tff(c_332, plain, (v1_funct_1(k2_funct_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_330, c_305])).
% 5.95/2.17  tff(c_355, plain, (![A_103, B_104]: (v3_funct_2(k2_funct_2(A_103, B_104), A_103, A_103) | ~m1_subset_1(B_104, k1_zfmisc_1(k2_zfmisc_1(A_103, A_103))) | ~v3_funct_2(B_104, A_103, A_103) | ~v1_funct_2(B_104, A_103, A_103) | ~v1_funct_1(B_104))), inference(cnfTransformation, [status(thm)], [f_110])).
% 5.95/2.17  tff(c_359, plain, (v3_funct_2(k2_funct_2('#skF_1', '#skF_2'), '#skF_1', '#skF_1') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_52, c_355])).
% 5.95/2.17  tff(c_366, plain, (v3_funct_2(k2_funct_1('#skF_2'), '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_54, c_330, c_359])).
% 5.95/2.17  tff(c_583, plain, (v2_funct_1(k2_funct_1('#skF_2')) | ~v3_funct_2(k2_funct_1('#skF_2'), '#skF_1', '#skF_1') | ~v1_funct_1(k2_funct_1('#skF_2'))), inference(resolution, [status(thm)], [c_562, c_26])).
% 5.95/2.17  tff(c_616, plain, (v2_funct_1(k2_funct_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_332, c_366, c_583])).
% 5.95/2.17  tff(c_10, plain, (![A_10]: (k5_relat_1(k2_funct_1(A_10), A_10)=k6_relat_1(k2_relat_1(A_10)) | ~v2_funct_1(A_10) | ~v1_funct_1(A_10) | ~v1_relat_1(A_10))), inference(cnfTransformation, [status(thm)], [f_52])).
% 5.95/2.17  tff(c_188, plain, (![A_69]: (k5_relat_1(k2_funct_1(A_69), A_69)=k6_partfun1(k2_relat_1(A_69)) | ~v2_funct_1(A_69) | ~v1_funct_1(A_69) | ~v1_relat_1(A_69))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_10])).
% 5.95/2.17  tff(c_197, plain, (![A_12]: (k6_partfun1(k2_relat_1(k2_funct_1(A_12)))=k5_relat_1(A_12, k2_funct_1(A_12)) | ~v2_funct_1(k2_funct_1(A_12)) | ~v1_funct_1(k2_funct_1(A_12)) | ~v1_relat_1(k2_funct_1(A_12)) | ~v2_funct_1(A_12) | ~v1_funct_1(A_12) | ~v1_relat_1(A_12))), inference(superposition, [status(thm), theory('equality')], [c_16, c_188])).
% 5.95/2.17  tff(c_340, plain, (![A_99, B_100]: (v1_funct_2(k2_funct_2(A_99, B_100), A_99, A_99) | ~m1_subset_1(B_100, k1_zfmisc_1(k2_zfmisc_1(A_99, A_99))) | ~v3_funct_2(B_100, A_99, A_99) | ~v1_funct_2(B_100, A_99, A_99) | ~v1_funct_1(B_100))), inference(cnfTransformation, [status(thm)], [f_110])).
% 5.95/2.17  tff(c_344, plain, (v1_funct_2(k2_funct_2('#skF_1', '#skF_2'), '#skF_1', '#skF_1') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_52, c_340])).
% 5.95/2.17  tff(c_351, plain, (v1_funct_2(k2_funct_1('#skF_2'), '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_54, c_330, c_344])).
% 5.95/2.17  tff(c_44, plain, (![A_35, B_36]: (k2_funct_2(A_35, B_36)=k2_funct_1(B_36) | ~m1_subset_1(B_36, k1_zfmisc_1(k2_zfmisc_1(A_35, A_35))) | ~v3_funct_2(B_36, A_35, A_35) | ~v1_funct_2(B_36, A_35, A_35) | ~v1_funct_1(B_36))), inference(cnfTransformation, [status(thm)], [f_134])).
% 5.95/2.17  tff(c_569, plain, (k2_funct_2('#skF_1', k2_funct_1('#skF_2'))=k2_funct_1(k2_funct_1('#skF_2')) | ~v3_funct_2(k2_funct_1('#skF_2'), '#skF_1', '#skF_1') | ~v1_funct_2(k2_funct_1('#skF_2'), '#skF_1', '#skF_1') | ~v1_funct_1(k2_funct_1('#skF_2'))), inference(resolution, [status(thm)], [c_562, c_44])).
% 5.95/2.17  tff(c_603, plain, (k2_funct_2('#skF_1', k2_funct_1('#skF_2'))=k2_funct_1(k2_funct_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_332, c_351, c_366, c_569])).
% 5.95/2.17  tff(c_18, plain, (![C_15, A_13, B_14]: (v1_relat_1(C_15) | ~m1_subset_1(C_15, k1_zfmisc_1(k2_zfmisc_1(A_13, B_14))))), inference(cnfTransformation, [status(thm)], [f_72])).
% 5.95/2.17  tff(c_780, plain, (![A_120, B_121]: (v1_relat_1(k2_funct_2(A_120, B_121)) | ~m1_subset_1(B_121, k1_zfmisc_1(k2_zfmisc_1(A_120, A_120))) | ~v3_funct_2(B_121, A_120, A_120) | ~v1_funct_2(B_121, A_120, A_120) | ~v1_funct_1(B_121))), inference(resolution, [status(thm)], [c_511, c_18])).
% 5.95/2.17  tff(c_783, plain, (v1_relat_1(k2_funct_2('#skF_1', k2_funct_1('#skF_2'))) | ~v3_funct_2(k2_funct_1('#skF_2'), '#skF_1', '#skF_1') | ~v1_funct_2(k2_funct_1('#skF_2'), '#skF_1', '#skF_1') | ~v1_funct_1(k2_funct_1('#skF_2'))), inference(resolution, [status(thm)], [c_562, c_780])).
% 5.95/2.17  tff(c_799, plain, (v1_relat_1(k2_funct_1(k2_funct_1('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_332, c_351, c_366, c_603, c_783])).
% 5.95/2.17  tff(c_36, plain, (![A_26, B_27]: (v1_funct_1(k2_funct_2(A_26, B_27)) | ~m1_subset_1(B_27, k1_zfmisc_1(k2_zfmisc_1(A_26, A_26))) | ~v3_funct_2(B_27, A_26, A_26) | ~v1_funct_2(B_27, A_26, A_26) | ~v1_funct_1(B_27))), inference(cnfTransformation, [status(thm)], [f_110])).
% 5.95/2.17  tff(c_572, plain, (v1_funct_1(k2_funct_2('#skF_1', k2_funct_1('#skF_2'))) | ~v3_funct_2(k2_funct_1('#skF_2'), '#skF_1', '#skF_1') | ~v1_funct_2(k2_funct_1('#skF_2'), '#skF_1', '#skF_1') | ~v1_funct_1(k2_funct_1('#skF_2'))), inference(resolution, [status(thm)], [c_562, c_36])).
% 5.95/2.17  tff(c_606, plain, (v1_funct_1(k2_funct_2('#skF_1', k2_funct_1('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_332, c_351, c_366, c_572])).
% 5.95/2.17  tff(c_651, plain, (v1_funct_1(k2_funct_1(k2_funct_1('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_603, c_606])).
% 5.95/2.17  tff(c_32, plain, (![A_26, B_27]: (v3_funct_2(k2_funct_2(A_26, B_27), A_26, A_26) | ~m1_subset_1(B_27, k1_zfmisc_1(k2_zfmisc_1(A_26, A_26))) | ~v3_funct_2(B_27, A_26, A_26) | ~v1_funct_2(B_27, A_26, A_26) | ~v1_funct_1(B_27))), inference(cnfTransformation, [status(thm)], [f_110])).
% 5.95/2.17  tff(c_564, plain, (v3_funct_2(k2_funct_2('#skF_1', k2_funct_1('#skF_2')), '#skF_1', '#skF_1') | ~v3_funct_2(k2_funct_1('#skF_2'), '#skF_1', '#skF_1') | ~v1_funct_2(k2_funct_1('#skF_2'), '#skF_1', '#skF_1') | ~v1_funct_1(k2_funct_1('#skF_2'))), inference(resolution, [status(thm)], [c_562, c_32])).
% 5.95/2.17  tff(c_597, plain, (v3_funct_2(k2_funct_2('#skF_1', k2_funct_1('#skF_2')), '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_332, c_351, c_366, c_564])).
% 5.95/2.17  tff(c_649, plain, (v3_funct_2(k2_funct_1(k2_funct_1('#skF_2')), '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_603, c_597])).
% 5.95/2.17  tff(c_655, plain, (m1_subset_1(k2_funct_1(k2_funct_1('#skF_2')), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k2_funct_1('#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v3_funct_2(k2_funct_1('#skF_2'), '#skF_1', '#skF_1') | ~v1_funct_2(k2_funct_1('#skF_2'), '#skF_1', '#skF_1') | ~v1_funct_1(k2_funct_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_603, c_30])).
% 5.95/2.17  tff(c_659, plain, (m1_subset_1(k2_funct_1(k2_funct_1('#skF_2')), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_332, c_351, c_366, c_562, c_655])).
% 5.95/2.17  tff(c_844, plain, (v2_funct_1(k2_funct_1(k2_funct_1('#skF_2'))) | ~v3_funct_2(k2_funct_1(k2_funct_1('#skF_2')), '#skF_1', '#skF_1') | ~v1_funct_1(k2_funct_1(k2_funct_1('#skF_2')))), inference(resolution, [status(thm)], [c_659, c_26])).
% 5.95/2.17  tff(c_889, plain, (v2_funct_1(k2_funct_1(k2_funct_1('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_651, c_649, c_844])).
% 5.95/2.17  tff(c_34, plain, (![A_26, B_27]: (v1_funct_2(k2_funct_2(A_26, B_27), A_26, A_26) | ~m1_subset_1(B_27, k1_zfmisc_1(k2_zfmisc_1(A_26, A_26))) | ~v3_funct_2(B_27, A_26, A_26) | ~v1_funct_2(B_27, A_26, A_26) | ~v1_funct_1(B_27))), inference(cnfTransformation, [status(thm)], [f_110])).
% 5.95/2.17  tff(c_566, plain, (v1_funct_2(k2_funct_2('#skF_1', k2_funct_1('#skF_2')), '#skF_1', '#skF_1') | ~v3_funct_2(k2_funct_1('#skF_2'), '#skF_1', '#skF_1') | ~v1_funct_2(k2_funct_1('#skF_2'), '#skF_1', '#skF_1') | ~v1_funct_1(k2_funct_1('#skF_2'))), inference(resolution, [status(thm)], [c_562, c_34])).
% 5.95/2.17  tff(c_600, plain, (v1_funct_2(k2_funct_2('#skF_1', k2_funct_1('#skF_2')), '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_332, c_351, c_366, c_566])).
% 5.95/2.17  tff(c_650, plain, (v1_funct_2(k2_funct_1(k2_funct_1('#skF_2')), '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_603, c_600])).
% 5.95/2.17  tff(c_836, plain, (k1_relset_1('#skF_1', '#skF_1', k2_funct_1(k2_funct_1('#skF_2')))='#skF_1' | ~v1_funct_2(k2_funct_1(k2_funct_1('#skF_2')), '#skF_1', '#skF_1') | ~v1_funct_1(k2_funct_1(k2_funct_1('#skF_2')))), inference(resolution, [status(thm)], [c_659, c_48])).
% 5.95/2.17  tff(c_882, plain, (k1_relset_1('#skF_1', '#skF_1', k2_funct_1(k2_funct_1('#skF_2')))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_651, c_650, c_836])).
% 5.95/2.17  tff(c_1218, plain, (![A_130, B_131]: (k1_relset_1(A_130, A_130, k2_funct_2(A_130, B_131))=k1_relat_1(k2_funct_2(A_130, B_131)) | ~m1_subset_1(B_131, k1_zfmisc_1(k2_zfmisc_1(A_130, A_130))) | ~v3_funct_2(B_131, A_130, A_130) | ~v1_funct_2(B_131, A_130, A_130) | ~v1_funct_1(B_131))), inference(resolution, [status(thm)], [c_511, c_20])).
% 5.95/2.17  tff(c_1222, plain, (k1_relset_1('#skF_1', '#skF_1', k2_funct_2('#skF_1', k2_funct_1('#skF_2')))=k1_relat_1(k2_funct_2('#skF_1', k2_funct_1('#skF_2'))) | ~v3_funct_2(k2_funct_1('#skF_2'), '#skF_1', '#skF_1') | ~v1_funct_2(k2_funct_1('#skF_2'), '#skF_1', '#skF_1') | ~v1_funct_1(k2_funct_1('#skF_2'))), inference(resolution, [status(thm)], [c_562, c_1218])).
% 5.95/2.17  tff(c_1237, plain, (k1_relat_1(k2_funct_1(k2_funct_1('#skF_2')))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_332, c_351, c_366, c_882, c_603, c_603, c_1222])).
% 5.95/2.17  tff(c_830, plain, (k2_funct_2('#skF_1', k2_funct_1(k2_funct_1('#skF_2')))=k2_funct_1(k2_funct_1(k2_funct_1('#skF_2'))) | ~v3_funct_2(k2_funct_1(k2_funct_1('#skF_2')), '#skF_1', '#skF_1') | ~v1_funct_2(k2_funct_1(k2_funct_1('#skF_2')), '#skF_1', '#skF_1') | ~v1_funct_1(k2_funct_1(k2_funct_1('#skF_2')))), inference(resolution, [status(thm)], [c_659, c_44])).
% 5.95/2.17  tff(c_876, plain, (k2_funct_2('#skF_1', k2_funct_1(k2_funct_1('#skF_2')))=k2_funct_1(k2_funct_1(k2_funct_1('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_651, c_650, c_649, c_830])).
% 5.95/2.17  tff(c_958, plain, (k2_funct_1(k2_funct_1(k2_funct_1('#skF_2')))=k2_funct_2('#skF_1', '#skF_2') | ~v2_funct_1('#skF_2') | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_16, c_876])).
% 5.95/2.17  tff(c_964, plain, (k2_funct_1(k2_funct_1(k2_funct_1('#skF_2')))=k2_funct_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_87, c_58, c_214, c_330, c_958])).
% 5.95/2.17  tff(c_999, plain, (k6_partfun1(k2_relat_1(k2_funct_1(k2_funct_1(k2_funct_1('#skF_2')))))=k5_relat_1(k2_funct_1(k2_funct_1('#skF_2')), k2_funct_1('#skF_2')) | ~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1('#skF_2')))) | ~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1('#skF_2')))) | ~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1('#skF_2')))) | ~v2_funct_1(k2_funct_1(k2_funct_1('#skF_2'))) | ~v1_funct_1(k2_funct_1(k2_funct_1('#skF_2'))) | ~v1_relat_1(k2_funct_1(k2_funct_1('#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_964, c_197])).
% 5.95/2.17  tff(c_1028, plain, (k5_relat_1(k2_funct_1(k2_funct_1('#skF_2')), k2_funct_1('#skF_2'))=k6_partfun1(k2_relat_1(k2_funct_1('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_799, c_651, c_889, c_621, c_964, c_332, c_964, c_616, c_964, c_964, c_999])).
% 5.95/2.17  tff(c_176, plain, (![A_68]: (k5_relat_1(A_68, k2_funct_1(A_68))=k6_partfun1(k1_relat_1(A_68)) | ~v2_funct_1(A_68) | ~v1_funct_1(A_68) | ~v1_relat_1(A_68))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_12])).
% 5.95/2.17  tff(c_185, plain, (![A_12]: (k6_partfun1(k1_relat_1(k2_funct_1(A_12)))=k5_relat_1(k2_funct_1(A_12), A_12) | ~v2_funct_1(k2_funct_1(A_12)) | ~v1_funct_1(k2_funct_1(A_12)) | ~v1_relat_1(k2_funct_1(A_12)) | ~v2_funct_1(A_12) | ~v1_funct_1(A_12) | ~v1_relat_1(A_12))), inference(superposition, [status(thm), theory('equality')], [c_16, c_176])).
% 5.95/2.17  tff(c_1399, plain, (k6_partfun1(k1_relat_1(k2_funct_1(k2_funct_1('#skF_2'))))=k6_partfun1(k2_relat_1(k2_funct_1('#skF_2'))) | ~v2_funct_1(k2_funct_1(k2_funct_1('#skF_2'))) | ~v1_funct_1(k2_funct_1(k2_funct_1('#skF_2'))) | ~v1_relat_1(k2_funct_1(k2_funct_1('#skF_2'))) | ~v2_funct_1(k2_funct_1('#skF_2')) | ~v1_funct_1(k2_funct_1('#skF_2')) | ~v1_relat_1(k2_funct_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_1028, c_185])).
% 5.95/2.17  tff(c_1415, plain, (k6_partfun1(k2_relat_1(k2_funct_1('#skF_2')))=k6_partfun1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_621, c_332, c_616, c_799, c_651, c_889, c_1237, c_1399])).
% 5.95/2.17  tff(c_1478, plain, (k5_relat_1('#skF_2', k2_funct_1('#skF_2'))=k6_partfun1('#skF_1') | ~v2_funct_1(k2_funct_1('#skF_2')) | ~v1_funct_1(k2_funct_1('#skF_2')) | ~v1_relat_1(k2_funct_1('#skF_2')) | ~v2_funct_1('#skF_2') | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_197, c_1415])).
% 5.95/2.17  tff(c_1497, plain, (k5_relat_1('#skF_2', k2_funct_1('#skF_2'))=k6_partfun1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_87, c_58, c_214, c_621, c_332, c_616, c_1478])).
% 5.95/2.17  tff(c_628, plain, (![E_115, A_113, D_111, C_116, F_114, B_112]: (k1_partfun1(A_113, B_112, C_116, D_111, E_115, F_114)=k5_relat_1(E_115, F_114) | ~m1_subset_1(F_114, k1_zfmisc_1(k2_zfmisc_1(C_116, D_111))) | ~v1_funct_1(F_114) | ~m1_subset_1(E_115, k1_zfmisc_1(k2_zfmisc_1(A_113, B_112))) | ~v1_funct_1(E_115))), inference(cnfTransformation, [status(thm)], [f_124])).
% 5.95/2.17  tff(c_630, plain, (![A_113, B_112, E_115]: (k1_partfun1(A_113, B_112, '#skF_1', '#skF_1', E_115, k2_funct_1('#skF_2'))=k5_relat_1(E_115, k2_funct_1('#skF_2')) | ~v1_funct_1(k2_funct_1('#skF_2')) | ~m1_subset_1(E_115, k1_zfmisc_1(k2_zfmisc_1(A_113, B_112))) | ~v1_funct_1(E_115))), inference(resolution, [status(thm)], [c_562, c_628])).
% 5.95/2.17  tff(c_2180, plain, (![A_160, B_161, E_162]: (k1_partfun1(A_160, B_161, '#skF_1', '#skF_1', E_162, k2_funct_1('#skF_2'))=k5_relat_1(E_162, k2_funct_1('#skF_2')) | ~m1_subset_1(E_162, k1_zfmisc_1(k2_zfmisc_1(A_160, B_161))) | ~v1_funct_1(E_162))), inference(demodulation, [status(thm), theory('equality')], [c_332, c_630])).
% 5.95/2.17  tff(c_2210, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', k2_funct_1('#skF_2'))=k5_relat_1('#skF_2', k2_funct_1('#skF_2')) | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_52, c_2180])).
% 5.95/2.17  tff(c_2230, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', k2_funct_1('#skF_2'))=k6_partfun1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_1497, c_2210])).
% 5.95/2.17  tff(c_50, plain, (~r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', k2_funct_2('#skF_1', '#skF_2'), '#skF_2'), k6_partfun1('#skF_1')) | ~r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', k2_funct_2('#skF_1', '#skF_2')), k6_partfun1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_157])).
% 5.95/2.17  tff(c_74, plain, (~r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', k2_funct_2('#skF_1', '#skF_2')), k6_partfun1('#skF_1'))), inference(splitLeft, [status(thm)], [c_50])).
% 5.95/2.17  tff(c_333, plain, (~r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', k2_funct_1('#skF_2')), k6_partfun1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_330, c_74])).
% 5.95/2.17  tff(c_2232, plain, (~r2_relset_1('#skF_1', '#skF_1', k6_partfun1('#skF_1'), k6_partfun1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_2230, c_333])).
% 5.95/2.17  tff(c_2235, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_252, c_2232])).
% 5.95/2.17  tff(c_2236, plain, (~r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', k2_funct_2('#skF_1', '#skF_2'), '#skF_2'), k6_partfun1('#skF_1'))), inference(splitRight, [status(thm)], [c_50])).
% 5.95/2.17  tff(c_2498, plain, (~r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', k2_funct_1('#skF_2'), '#skF_2'), k6_partfun1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_2494, c_2236])).
% 5.95/2.17  tff(c_3417, plain, (~r2_relset_1('#skF_1', '#skF_1', k6_partfun1('#skF_1'), k6_partfun1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_3265, c_2498])).
% 5.95/2.17  tff(c_3420, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2444, c_3417])).
% 5.95/2.17  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.95/2.17  
% 5.95/2.17  Inference rules
% 5.95/2.17  ----------------------
% 5.95/2.17  #Ref     : 0
% 5.95/2.17  #Sup     : 808
% 5.95/2.17  #Fact    : 0
% 5.95/2.17  #Define  : 0
% 5.95/2.17  #Split   : 4
% 5.95/2.17  #Chain   : 0
% 5.95/2.17  #Close   : 0
% 5.95/2.17  
% 5.95/2.17  Ordering : KBO
% 5.95/2.17  
% 5.95/2.17  Simplification rules
% 5.95/2.17  ----------------------
% 5.95/2.17  #Subsume      : 119
% 5.95/2.17  #Demod        : 1583
% 5.95/2.17  #Tautology    : 333
% 5.95/2.17  #SimpNegUnit  : 0
% 5.95/2.17  #BackRed      : 34
% 5.95/2.17  
% 5.95/2.17  #Partial instantiations: 0
% 5.95/2.17  #Strategies tried      : 1
% 5.95/2.17  
% 5.95/2.17  Timing (in seconds)
% 5.95/2.17  ----------------------
% 5.95/2.17  Preprocessing        : 0.37
% 5.95/2.17  Parsing              : 0.20
% 5.95/2.17  CNF conversion       : 0.02
% 5.95/2.17  Main loop            : 0.97
% 5.95/2.17  Inferencing          : 0.33
% 5.95/2.17  Reduction            : 0.37
% 5.95/2.17  Demodulation         : 0.28
% 5.95/2.17  BG Simplification    : 0.04
% 5.95/2.17  Subsumption          : 0.15
% 5.95/2.17  Abstraction          : 0.04
% 5.95/2.17  MUC search           : 0.00
% 5.95/2.18  Cooper               : 0.00
% 5.95/2.18  Total                : 1.40
% 5.95/2.18  Index Insertion      : 0.00
% 5.95/2.18  Index Deletion       : 0.00
% 5.95/2.18  Index Matching       : 0.00
% 5.95/2.18  BG Taut test         : 0.00
%------------------------------------------------------------------------------
