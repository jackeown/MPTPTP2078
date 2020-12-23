%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:16:08 EST 2020

% Result     : Theorem 5.42s
% Output     : CNFRefutation 5.42s
% Verified   : 
% Statistics : Number of formulae       :  173 (8012 expanded)
%              Number of leaves         :   39 (3240 expanded)
%              Depth                    :   22
%              Number of atoms          :  432 (29353 expanded)
%              Number of equality atoms :   60 (1485 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v3_funct_2 > v1_funct_2 > v2_funct_2 > v1_partfun1 > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k1_relset_1 > k6_subset_1 > k5_relat_1 > k2_zfmisc_1 > k2_funct_2 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_1

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

tff(k6_subset_1,type,(
    k6_subset_1: ( $i * $i ) > $i )).

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

tff(f_103,axiom,(
    ! [A] :
      ( v1_partfun1(k6_partfun1(A),A)
      & m1_subset_1(k6_partfun1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_partfun1)).

tff(f_71,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => r2_relset_1(A,B,C,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',reflexivity_r2_relset_1)).

tff(f_146,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_funct_1(B)
          & v1_funct_2(B,A,A)
          & v3_funct_2(B,A,A)
          & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
       => ( r2_relset_1(A,A,k1_partfun1(A,A,A,A,B,k2_funct_2(A,B)),k6_partfun1(A))
          & r2_relset_1(A,A,k1_partfun1(A,A,A,A,k2_funct_2(A,B),B),k6_partfun1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_funct_2)).

tff(f_123,axiom,(
    ! [A,B] :
      ( ( v1_funct_1(B)
        & v1_funct_2(B,A,A)
        & v3_funct_2(B,A,A)
        & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
     => k2_funct_2(A,B) = k2_funct_1(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_funct_2)).

tff(f_99,axiom,(
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

tff(f_61,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_83,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( ( v1_funct_1(C)
          & v3_funct_2(C,A,B) )
       => ( v1_funct_1(C)
          & v2_funct_1(C)
          & v2_funct_2(C,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_funct_2)).

tff(f_133,axiom,(
    ! [A,B] :
      ( ( v1_funct_1(B)
        & v1_funct_2(B,A,A)
        & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
     => k1_relset_1(A,A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_funct_2)).

tff(f_65,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_57,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => k2_funct_1(k2_funct_1(A)) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_funct_1)).

tff(f_125,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_49,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k5_relat_1(A,k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))
          & k5_relat_1(k2_funct_1(A),A) = k6_relat_1(k2_relat_1(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_funct_1)).

tff(f_113,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(c_38,plain,(
    ! [A_21] : m1_subset_1(k6_partfun1(A_21),k1_zfmisc_1(k2_zfmisc_1(A_21,A_21))) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_2113,plain,(
    ! [A_179,B_180,C_181,D_182] :
      ( r2_relset_1(A_179,B_180,C_181,C_181)
      | ~ m1_subset_1(D_182,k1_zfmisc_1(k2_zfmisc_1(A_179,B_180)))
      | ~ m1_subset_1(C_181,k1_zfmisc_1(k2_zfmisc_1(A_179,B_180))) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_2150,plain,(
    ! [A_185,C_186] :
      ( r2_relset_1(A_185,A_185,C_186,C_186)
      | ~ m1_subset_1(C_186,k1_zfmisc_1(k2_zfmisc_1(A_185,A_185))) ) ),
    inference(resolution,[status(thm)],[c_38,c_2113])).

tff(c_2158,plain,(
    ! [A_21] : r2_relset_1(A_21,A_21,k6_partfun1(A_21),k6_partfun1(A_21)) ),
    inference(resolution,[status(thm)],[c_38,c_2150])).

tff(c_56,plain,(
    v1_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_54,plain,(
    v1_funct_2('#skF_2','#skF_1','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_52,plain,(
    v3_funct_2('#skF_2','#skF_1','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_50,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_2195,plain,(
    ! [A_198,B_199] :
      ( k2_funct_2(A_198,B_199) = k2_funct_1(B_199)
      | ~ m1_subset_1(B_199,k1_zfmisc_1(k2_zfmisc_1(A_198,A_198)))
      | ~ v3_funct_2(B_199,A_198,A_198)
      | ~ v1_funct_2(B_199,A_198,A_198)
      | ~ v1_funct_1(B_199) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_2205,plain,
    ( k2_funct_2('#skF_1','#skF_2') = k2_funct_1('#skF_2')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_50,c_2195])).

tff(c_2210,plain,(
    k2_funct_2('#skF_1','#skF_2') = k2_funct_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_52,c_2205])).

tff(c_2177,plain,(
    ! [A_195,B_196] :
      ( v1_funct_1(k2_funct_2(A_195,B_196))
      | ~ m1_subset_1(B_196,k1_zfmisc_1(k2_zfmisc_1(A_195,A_195)))
      | ~ v3_funct_2(B_196,A_195,A_195)
      | ~ v1_funct_2(B_196,A_195,A_195)
      | ~ v1_funct_1(B_196) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_2187,plain,
    ( v1_funct_1(k2_funct_2('#skF_1','#skF_2'))
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_50,c_2177])).

tff(c_2192,plain,(
    v1_funct_1(k2_funct_2('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_52,c_2187])).

tff(c_2211,plain,(
    v1_funct_1(k2_funct_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2210,c_2192])).

tff(c_71,plain,(
    ! [C_38,A_39,B_40] :
      ( v1_relat_1(C_38)
      | ~ m1_subset_1(C_38,k1_zfmisc_1(k2_zfmisc_1(A_39,B_40))) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_84,plain,(
    v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_50,c_71])).

tff(c_2070,plain,(
    ! [C_168,A_169,B_170] :
      ( v2_funct_1(C_168)
      | ~ v3_funct_2(C_168,A_169,B_170)
      | ~ v1_funct_1(C_168)
      | ~ m1_subset_1(C_168,k1_zfmisc_1(k2_zfmisc_1(A_169,B_170))) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_2080,plain,
    ( v2_funct_1('#skF_2')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_50,c_2070])).

tff(c_2085,plain,(
    v2_funct_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_52,c_2080])).

tff(c_2313,plain,(
    ! [A_216,B_217] :
      ( m1_subset_1(k2_funct_2(A_216,B_217),k1_zfmisc_1(k2_zfmisc_1(A_216,A_216)))
      | ~ m1_subset_1(B_217,k1_zfmisc_1(k2_zfmisc_1(A_216,A_216)))
      | ~ v3_funct_2(B_217,A_216,A_216)
      | ~ v1_funct_2(B_217,A_216,A_216)
      | ~ v1_funct_1(B_217) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_2343,plain,
    ( m1_subset_1(k2_funct_1('#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_2210,c_2313])).

tff(c_2355,plain,(
    m1_subset_1(k2_funct_1('#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_52,c_50,c_2343])).

tff(c_16,plain,(
    ! [C_8,A_6,B_7] :
      ( v1_relat_1(C_8)
      | ~ m1_subset_1(C_8,k1_zfmisc_1(k2_zfmisc_1(A_6,B_7))) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_2406,plain,(
    v1_relat_1(k2_funct_1('#skF_2')) ),
    inference(resolution,[status(thm)],[c_2355,c_16])).

tff(c_2219,plain,(
    ! [A_203,B_204] :
      ( v3_funct_2(k2_funct_2(A_203,B_204),A_203,A_203)
      | ~ m1_subset_1(B_204,k1_zfmisc_1(k2_zfmisc_1(A_203,A_203)))
      | ~ v3_funct_2(B_204,A_203,A_203)
      | ~ v1_funct_2(B_204,A_203,A_203)
      | ~ v1_funct_1(B_204) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_2226,plain,
    ( v3_funct_2(k2_funct_2('#skF_1','#skF_2'),'#skF_1','#skF_1')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_50,c_2219])).

tff(c_2231,plain,(
    v3_funct_2(k2_funct_1('#skF_2'),'#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_52,c_2210,c_2226])).

tff(c_24,plain,(
    ! [C_18,A_16,B_17] :
      ( v2_funct_1(C_18)
      | ~ v3_funct_2(C_18,A_16,B_17)
      | ~ v1_funct_1(C_18)
      | ~ m1_subset_1(C_18,k1_zfmisc_1(k2_zfmisc_1(A_16,B_17))) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_2376,plain,
    ( v2_funct_1(k2_funct_1('#skF_2'))
    | ~ v3_funct_2(k2_funct_1('#skF_2'),'#skF_1','#skF_1')
    | ~ v1_funct_1(k2_funct_1('#skF_2')) ),
    inference(resolution,[status(thm)],[c_2355,c_24])).

tff(c_2404,plain,(
    v2_funct_1(k2_funct_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2211,c_2231,c_2376])).

tff(c_2234,plain,(
    ! [A_207,B_208] :
      ( v1_funct_2(k2_funct_2(A_207,B_208),A_207,A_207)
      | ~ m1_subset_1(B_208,k1_zfmisc_1(k2_zfmisc_1(A_207,A_207)))
      | ~ v3_funct_2(B_208,A_207,A_207)
      | ~ v1_funct_2(B_208,A_207,A_207)
      | ~ v1_funct_1(B_208) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_2241,plain,
    ( v1_funct_2(k2_funct_2('#skF_1','#skF_2'),'#skF_1','#skF_1')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_50,c_2234])).

tff(c_2246,plain,(
    v1_funct_2(k2_funct_1('#skF_2'),'#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_52,c_2210,c_2241])).

tff(c_46,plain,(
    ! [A_31,B_32] :
      ( k1_relset_1(A_31,A_31,B_32) = A_31
      | ~ m1_subset_1(B_32,k1_zfmisc_1(k2_zfmisc_1(A_31,A_31)))
      | ~ v1_funct_2(B_32,A_31,A_31)
      | ~ v1_funct_1(B_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_2370,plain,
    ( k1_relset_1('#skF_1','#skF_1',k2_funct_1('#skF_2')) = '#skF_1'
    | ~ v1_funct_2(k2_funct_1('#skF_2'),'#skF_1','#skF_1')
    | ~ v1_funct_1(k2_funct_1('#skF_2')) ),
    inference(resolution,[status(thm)],[c_2355,c_46])).

tff(c_2398,plain,(
    k1_relset_1('#skF_1','#skF_1',k2_funct_1('#skF_2')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2211,c_2246,c_2370])).

tff(c_18,plain,(
    ! [A_9,B_10,C_11] :
      ( k1_relset_1(A_9,B_10,C_11) = k1_relat_1(C_11)
      | ~ m1_subset_1(C_11,k1_zfmisc_1(k2_zfmisc_1(A_9,B_10))) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_2405,plain,(
    k1_relset_1('#skF_1','#skF_1',k2_funct_1('#skF_2')) = k1_relat_1(k2_funct_1('#skF_2')) ),
    inference(resolution,[status(thm)],[c_2355,c_18])).

tff(c_2459,plain,(
    k1_relat_1(k2_funct_1('#skF_2')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2398,c_2405])).

tff(c_14,plain,(
    ! [A_5] :
      ( k2_funct_1(k2_funct_1(A_5)) = A_5
      | ~ v2_funct_1(A_5)
      | ~ v1_funct_1(A_5)
      | ~ v1_relat_1(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_44,plain,(
    ! [A_30] : k6_relat_1(A_30) = k6_partfun1(A_30) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_12,plain,(
    ! [A_4] :
      ( k5_relat_1(A_4,k2_funct_1(A_4)) = k6_relat_1(k1_relat_1(A_4))
      | ~ v2_funct_1(A_4)
      | ~ v1_funct_1(A_4)
      | ~ v1_relat_1(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_2046,plain,(
    ! [A_166] :
      ( k5_relat_1(A_166,k2_funct_1(A_166)) = k6_partfun1(k1_relat_1(A_166))
      | ~ v2_funct_1(A_166)
      | ~ v1_funct_1(A_166)
      | ~ v1_relat_1(A_166) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_12])).

tff(c_2791,plain,(
    ! [A_234] :
      ( k6_partfun1(k1_relat_1(k2_funct_1(A_234))) = k5_relat_1(k2_funct_1(A_234),A_234)
      | ~ v2_funct_1(k2_funct_1(A_234))
      | ~ v1_funct_1(k2_funct_1(A_234))
      | ~ v1_relat_1(k2_funct_1(A_234))
      | ~ v2_funct_1(A_234)
      | ~ v1_funct_1(A_234)
      | ~ v1_relat_1(A_234) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_2046])).

tff(c_2853,plain,
    ( k5_relat_1(k2_funct_1('#skF_2'),'#skF_2') = k6_partfun1('#skF_1')
    | ~ v2_funct_1(k2_funct_1('#skF_2'))
    | ~ v1_funct_1(k2_funct_1('#skF_2'))
    | ~ v1_relat_1(k2_funct_1('#skF_2'))
    | ~ v2_funct_1('#skF_2')
    | ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_2459,c_2791])).

tff(c_2867,plain,(
    k5_relat_1(k2_funct_1('#skF_2'),'#skF_2') = k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_56,c_2085,c_2406,c_2211,c_2404,c_2853])).

tff(c_28,plain,(
    ! [A_19,B_20] :
      ( m1_subset_1(k2_funct_2(A_19,B_20),k1_zfmisc_1(k2_zfmisc_1(A_19,A_19)))
      | ~ m1_subset_1(B_20,k1_zfmisc_1(k2_zfmisc_1(A_19,A_19)))
      | ~ v3_funct_2(B_20,A_19,A_19)
      | ~ v1_funct_2(B_20,A_19,A_19)
      | ~ v1_funct_1(B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_2426,plain,(
    ! [A_218,F_221,D_222,B_223,C_219,E_220] :
      ( k1_partfun1(A_218,B_223,C_219,D_222,E_220,F_221) = k5_relat_1(E_220,F_221)
      | ~ m1_subset_1(F_221,k1_zfmisc_1(k2_zfmisc_1(C_219,D_222)))
      | ~ v1_funct_1(F_221)
      | ~ m1_subset_1(E_220,k1_zfmisc_1(k2_zfmisc_1(A_218,B_223)))
      | ~ v1_funct_1(E_220) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_2437,plain,(
    ! [A_218,B_223,E_220] :
      ( k1_partfun1(A_218,B_223,'#skF_1','#skF_1',E_220,'#skF_2') = k5_relat_1(E_220,'#skF_2')
      | ~ v1_funct_1('#skF_2')
      | ~ m1_subset_1(E_220,k1_zfmisc_1(k2_zfmisc_1(A_218,B_223)))
      | ~ v1_funct_1(E_220) ) ),
    inference(resolution,[status(thm)],[c_50,c_2426])).

tff(c_2464,plain,(
    ! [A_224,B_225,E_226] :
      ( k1_partfun1(A_224,B_225,'#skF_1','#skF_1',E_226,'#skF_2') = k5_relat_1(E_226,'#skF_2')
      | ~ m1_subset_1(E_226,k1_zfmisc_1(k2_zfmisc_1(A_224,B_225)))
      | ~ v1_funct_1(E_226) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_2437])).

tff(c_3259,plain,(
    ! [A_242,B_243] :
      ( k1_partfun1(A_242,A_242,'#skF_1','#skF_1',k2_funct_2(A_242,B_243),'#skF_2') = k5_relat_1(k2_funct_2(A_242,B_243),'#skF_2')
      | ~ v1_funct_1(k2_funct_2(A_242,B_243))
      | ~ m1_subset_1(B_243,k1_zfmisc_1(k2_zfmisc_1(A_242,A_242)))
      | ~ v3_funct_2(B_243,A_242,A_242)
      | ~ v1_funct_2(B_243,A_242,A_242)
      | ~ v1_funct_1(B_243) ) ),
    inference(resolution,[status(thm)],[c_28,c_2464])).

tff(c_3274,plain,
    ( k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1',k2_funct_2('#skF_1','#skF_2'),'#skF_2') = k5_relat_1(k2_funct_2('#skF_1','#skF_2'),'#skF_2')
    | ~ v1_funct_1(k2_funct_2('#skF_1','#skF_2'))
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_50,c_3259])).

tff(c_3287,plain,(
    k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1',k2_funct_1('#skF_2'),'#skF_2') = k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_52,c_2211,c_2210,c_2867,c_2210,c_2210,c_3274])).

tff(c_238,plain,(
    ! [A_69,B_70,C_71,D_72] :
      ( r2_relset_1(A_69,B_70,C_71,C_71)
      | ~ m1_subset_1(D_72,k1_zfmisc_1(k2_zfmisc_1(A_69,B_70)))
      | ~ m1_subset_1(C_71,k1_zfmisc_1(k2_zfmisc_1(A_69,B_70))) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_264,plain,(
    ! [A_75,C_76] :
      ( r2_relset_1(A_75,A_75,C_76,C_76)
      | ~ m1_subset_1(C_76,k1_zfmisc_1(k2_zfmisc_1(A_75,A_75))) ) ),
    inference(resolution,[status(thm)],[c_38,c_238])).

tff(c_272,plain,(
    ! [A_21] : r2_relset_1(A_21,A_21,k6_partfun1(A_21),k6_partfun1(A_21)) ),
    inference(resolution,[status(thm)],[c_38,c_264])).

tff(c_168,plain,(
    ! [C_55,A_56,B_57] :
      ( v2_funct_1(C_55)
      | ~ v3_funct_2(C_55,A_56,B_57)
      | ~ v1_funct_1(C_55)
      | ~ m1_subset_1(C_55,k1_zfmisc_1(k2_zfmisc_1(A_56,B_57))) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_178,plain,
    ( v2_funct_1('#skF_2')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_50,c_168])).

tff(c_183,plain,(
    v2_funct_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_52,c_178])).

tff(c_293,plain,(
    ! [A_87,B_88] :
      ( k2_funct_2(A_87,B_88) = k2_funct_1(B_88)
      | ~ m1_subset_1(B_88,k1_zfmisc_1(k2_zfmisc_1(A_87,A_87)))
      | ~ v3_funct_2(B_88,A_87,A_87)
      | ~ v1_funct_2(B_88,A_87,A_87)
      | ~ v1_funct_1(B_88) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_303,plain,
    ( k2_funct_2('#skF_1','#skF_2') = k2_funct_1('#skF_2')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_50,c_293])).

tff(c_308,plain,(
    k2_funct_2('#skF_1','#skF_2') = k2_funct_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_52,c_303])).

tff(c_409,plain,(
    ! [A_103,B_104] :
      ( m1_subset_1(k2_funct_2(A_103,B_104),k1_zfmisc_1(k2_zfmisc_1(A_103,A_103)))
      | ~ m1_subset_1(B_104,k1_zfmisc_1(k2_zfmisc_1(A_103,A_103)))
      | ~ v3_funct_2(B_104,A_103,A_103)
      | ~ v1_funct_2(B_104,A_103,A_103)
      | ~ v1_funct_1(B_104) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_439,plain,
    ( m1_subset_1(k2_funct_1('#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_308,c_409])).

tff(c_451,plain,(
    m1_subset_1(k2_funct_1('#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_52,c_50,c_439])).

tff(c_502,plain,(
    v1_relat_1(k2_funct_1('#skF_2')) ),
    inference(resolution,[status(thm)],[c_451,c_16])).

tff(c_248,plain,(
    ! [A_73,B_74] :
      ( v1_funct_1(k2_funct_2(A_73,B_74))
      | ~ m1_subset_1(B_74,k1_zfmisc_1(k2_zfmisc_1(A_73,A_73)))
      | ~ v3_funct_2(B_74,A_73,A_73)
      | ~ v1_funct_2(B_74,A_73,A_73)
      | ~ v1_funct_1(B_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_258,plain,
    ( v1_funct_1(k2_funct_2('#skF_1','#skF_2'))
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_50,c_248])).

tff(c_263,plain,(
    v1_funct_1(k2_funct_2('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_52,c_258])).

tff(c_309,plain,(
    v1_funct_1(k2_funct_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_308,c_263])).

tff(c_332,plain,(
    ! [A_99,B_100] :
      ( v3_funct_2(k2_funct_2(A_99,B_100),A_99,A_99)
      | ~ m1_subset_1(B_100,k1_zfmisc_1(k2_zfmisc_1(A_99,A_99)))
      | ~ v3_funct_2(B_100,A_99,A_99)
      | ~ v1_funct_2(B_100,A_99,A_99)
      | ~ v1_funct_1(B_100) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_339,plain,
    ( v3_funct_2(k2_funct_2('#skF_1','#skF_2'),'#skF_1','#skF_1')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_50,c_332])).

tff(c_344,plain,(
    v3_funct_2(k2_funct_1('#skF_2'),'#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_52,c_308,c_339])).

tff(c_472,plain,
    ( v2_funct_1(k2_funct_1('#skF_2'))
    | ~ v3_funct_2(k2_funct_1('#skF_2'),'#skF_1','#skF_1')
    | ~ v1_funct_1(k2_funct_1('#skF_2')) ),
    inference(resolution,[status(thm)],[c_451,c_24])).

tff(c_500,plain,(
    v2_funct_1(k2_funct_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_309,c_344,c_472])).

tff(c_315,plain,(
    ! [A_89,B_90] :
      ( v1_funct_2(k2_funct_2(A_89,B_90),A_89,A_89)
      | ~ m1_subset_1(B_90,k1_zfmisc_1(k2_zfmisc_1(A_89,A_89)))
      | ~ v3_funct_2(B_90,A_89,A_89)
      | ~ v1_funct_2(B_90,A_89,A_89)
      | ~ v1_funct_1(B_90) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_322,plain,
    ( v1_funct_2(k2_funct_2('#skF_1','#skF_2'),'#skF_1','#skF_1')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_50,c_315])).

tff(c_327,plain,(
    v1_funct_2(k2_funct_1('#skF_2'),'#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_52,c_308,c_322])).

tff(c_42,plain,(
    ! [A_28,B_29] :
      ( k2_funct_2(A_28,B_29) = k2_funct_1(B_29)
      | ~ m1_subset_1(B_29,k1_zfmisc_1(k2_zfmisc_1(A_28,A_28)))
      | ~ v3_funct_2(B_29,A_28,A_28)
      | ~ v1_funct_2(B_29,A_28,A_28)
      | ~ v1_funct_1(B_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_458,plain,
    ( k2_funct_2('#skF_1',k2_funct_1('#skF_2')) = k2_funct_1(k2_funct_1('#skF_2'))
    | ~ v3_funct_2(k2_funct_1('#skF_2'),'#skF_1','#skF_1')
    | ~ v1_funct_2(k2_funct_1('#skF_2'),'#skF_1','#skF_1')
    | ~ v1_funct_1(k2_funct_1('#skF_2')) ),
    inference(resolution,[status(thm)],[c_451,c_42])).

tff(c_487,plain,(
    k2_funct_2('#skF_1',k2_funct_1('#skF_2')) = k2_funct_1(k2_funct_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_309,c_327,c_344,c_458])).

tff(c_605,plain,(
    ! [A_114,B_115] :
      ( v1_relat_1(k2_funct_2(A_114,B_115))
      | ~ m1_subset_1(B_115,k1_zfmisc_1(k2_zfmisc_1(A_114,A_114)))
      | ~ v3_funct_2(B_115,A_114,A_114)
      | ~ v1_funct_2(B_115,A_114,A_114)
      | ~ v1_funct_1(B_115) ) ),
    inference(resolution,[status(thm)],[c_409,c_16])).

tff(c_608,plain,
    ( v1_relat_1(k2_funct_2('#skF_1',k2_funct_1('#skF_2')))
    | ~ v3_funct_2(k2_funct_1('#skF_2'),'#skF_1','#skF_1')
    | ~ v1_funct_2(k2_funct_1('#skF_2'),'#skF_1','#skF_1')
    | ~ v1_funct_1(k2_funct_1('#skF_2')) ),
    inference(resolution,[status(thm)],[c_451,c_605])).

tff(c_624,plain,(
    v1_relat_1(k2_funct_1(k2_funct_1('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_309,c_327,c_344,c_487,c_608])).

tff(c_34,plain,(
    ! [A_19,B_20] :
      ( v1_funct_1(k2_funct_2(A_19,B_20))
      | ~ m1_subset_1(B_20,k1_zfmisc_1(k2_zfmisc_1(A_19,A_19)))
      | ~ v3_funct_2(B_20,A_19,A_19)
      | ~ v1_funct_2(B_20,A_19,A_19)
      | ~ v1_funct_1(B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_463,plain,
    ( v1_funct_1(k2_funct_2('#skF_1',k2_funct_1('#skF_2')))
    | ~ v3_funct_2(k2_funct_1('#skF_2'),'#skF_1','#skF_1')
    | ~ v1_funct_2(k2_funct_1('#skF_2'),'#skF_1','#skF_1')
    | ~ v1_funct_1(k2_funct_1('#skF_2')) ),
    inference(resolution,[status(thm)],[c_451,c_34])).

tff(c_491,plain,(
    v1_funct_1(k2_funct_2('#skF_1',k2_funct_1('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_309,c_327,c_344,c_463])).

tff(c_528,plain,(
    v1_funct_1(k2_funct_1(k2_funct_1('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_487,c_491])).

tff(c_30,plain,(
    ! [A_19,B_20] :
      ( v3_funct_2(k2_funct_2(A_19,B_20),A_19,A_19)
      | ~ m1_subset_1(B_20,k1_zfmisc_1(k2_zfmisc_1(A_19,A_19)))
      | ~ v3_funct_2(B_20,A_19,A_19)
      | ~ v1_funct_2(B_20,A_19,A_19)
      | ~ v1_funct_1(B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_453,plain,
    ( v3_funct_2(k2_funct_2('#skF_1',k2_funct_1('#skF_2')),'#skF_1','#skF_1')
    | ~ v3_funct_2(k2_funct_1('#skF_2'),'#skF_1','#skF_1')
    | ~ v1_funct_2(k2_funct_1('#skF_2'),'#skF_1','#skF_1')
    | ~ v1_funct_1(k2_funct_1('#skF_2')) ),
    inference(resolution,[status(thm)],[c_451,c_30])).

tff(c_481,plain,(
    v3_funct_2(k2_funct_2('#skF_1',k2_funct_1('#skF_2')),'#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_309,c_327,c_344,c_453])).

tff(c_575,plain,(
    v3_funct_2(k2_funct_1(k2_funct_1('#skF_2')),'#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_487,c_481])).

tff(c_532,plain,
    ( m1_subset_1(k2_funct_1(k2_funct_1('#skF_2')),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k2_funct_1('#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ v3_funct_2(k2_funct_1('#skF_2'),'#skF_1','#skF_1')
    | ~ v1_funct_2(k2_funct_1('#skF_2'),'#skF_1','#skF_1')
    | ~ v1_funct_1(k2_funct_1('#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_487,c_28])).

tff(c_536,plain,(
    m1_subset_1(k2_funct_1(k2_funct_1('#skF_2')),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_309,c_327,c_344,c_451,c_532])).

tff(c_721,plain,
    ( v2_funct_1(k2_funct_1(k2_funct_1('#skF_2')))
    | ~ v3_funct_2(k2_funct_1(k2_funct_1('#skF_2')),'#skF_1','#skF_1')
    | ~ v1_funct_1(k2_funct_1(k2_funct_1('#skF_2'))) ),
    inference(resolution,[status(thm)],[c_536,c_24])).

tff(c_761,plain,(
    v2_funct_1(k2_funct_1(k2_funct_1('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_528,c_575,c_721])).

tff(c_32,plain,(
    ! [A_19,B_20] :
      ( v1_funct_2(k2_funct_2(A_19,B_20),A_19,A_19)
      | ~ m1_subset_1(B_20,k1_zfmisc_1(k2_zfmisc_1(A_19,A_19)))
      | ~ v3_funct_2(B_20,A_19,A_19)
      | ~ v1_funct_2(B_20,A_19,A_19)
      | ~ v1_funct_1(B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_455,plain,
    ( v1_funct_2(k2_funct_2('#skF_1',k2_funct_1('#skF_2')),'#skF_1','#skF_1')
    | ~ v3_funct_2(k2_funct_1('#skF_2'),'#skF_1','#skF_1')
    | ~ v1_funct_2(k2_funct_1('#skF_2'),'#skF_1','#skF_1')
    | ~ v1_funct_1(k2_funct_1('#skF_2')) ),
    inference(resolution,[status(thm)],[c_451,c_32])).

tff(c_484,plain,(
    v1_funct_2(k2_funct_2('#skF_1',k2_funct_1('#skF_2')),'#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_309,c_327,c_344,c_455])).

tff(c_569,plain,(
    v1_funct_2(k2_funct_1(k2_funct_1('#skF_2')),'#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_487,c_484])).

tff(c_715,plain,
    ( k1_relset_1('#skF_1','#skF_1',k2_funct_1(k2_funct_1('#skF_2'))) = '#skF_1'
    | ~ v1_funct_2(k2_funct_1(k2_funct_1('#skF_2')),'#skF_1','#skF_1')
    | ~ v1_funct_1(k2_funct_1(k2_funct_1('#skF_2'))) ),
    inference(resolution,[status(thm)],[c_536,c_46])).

tff(c_755,plain,(
    k1_relset_1('#skF_1','#skF_1',k2_funct_1(k2_funct_1('#skF_2'))) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_528,c_569,c_715])).

tff(c_762,plain,(
    k1_relset_1('#skF_1','#skF_1',k2_funct_1(k2_funct_1('#skF_2'))) = k1_relat_1(k2_funct_1(k2_funct_1('#skF_2'))) ),
    inference(resolution,[status(thm)],[c_536,c_18])).

tff(c_1213,plain,(
    k1_relat_1(k2_funct_1(k2_funct_1('#skF_2'))) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_755,c_762])).

tff(c_707,plain,
    ( k2_funct_2('#skF_1',k2_funct_1(k2_funct_1('#skF_2'))) = k2_funct_1(k2_funct_1(k2_funct_1('#skF_2')))
    | ~ v3_funct_2(k2_funct_1(k2_funct_1('#skF_2')),'#skF_1','#skF_1')
    | ~ v1_funct_2(k2_funct_1(k2_funct_1('#skF_2')),'#skF_1','#skF_1')
    | ~ v1_funct_1(k2_funct_1(k2_funct_1('#skF_2'))) ),
    inference(resolution,[status(thm)],[c_536,c_42])).

tff(c_748,plain,(
    k2_funct_2('#skF_1',k2_funct_1(k2_funct_1('#skF_2'))) = k2_funct_1(k2_funct_1(k2_funct_1('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_528,c_569,c_575,c_707])).

tff(c_845,plain,
    ( k2_funct_1(k2_funct_1(k2_funct_1('#skF_2'))) = k2_funct_2('#skF_1','#skF_2')
    | ~ v2_funct_1('#skF_2')
    | ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_748])).

tff(c_851,plain,(
    k2_funct_1(k2_funct_1(k2_funct_1('#skF_2'))) = k2_funct_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_56,c_183,c_308,c_845])).

tff(c_10,plain,(
    ! [A_4] :
      ( k5_relat_1(k2_funct_1(A_4),A_4) = k6_relat_1(k2_relat_1(A_4))
      | ~ v2_funct_1(A_4)
      | ~ v1_funct_1(A_4)
      | ~ v1_relat_1(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_156,plain,(
    ! [A_54] :
      ( k5_relat_1(k2_funct_1(A_54),A_54) = k6_partfun1(k2_relat_1(A_54))
      | ~ v2_funct_1(A_54)
      | ~ v1_funct_1(A_54)
      | ~ v1_relat_1(A_54) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_10])).

tff(c_165,plain,(
    ! [A_5] :
      ( k6_partfun1(k2_relat_1(k2_funct_1(A_5))) = k5_relat_1(A_5,k2_funct_1(A_5))
      | ~ v2_funct_1(k2_funct_1(A_5))
      | ~ v1_funct_1(k2_funct_1(A_5))
      | ~ v1_relat_1(k2_funct_1(A_5))
      | ~ v2_funct_1(A_5)
      | ~ v1_funct_1(A_5)
      | ~ v1_relat_1(A_5) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_156])).

tff(c_945,plain,
    ( k6_partfun1(k2_relat_1(k2_funct_1(k2_funct_1(k2_funct_1('#skF_2'))))) = k5_relat_1(k2_funct_1(k2_funct_1('#skF_2')),k2_funct_1('#skF_2'))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1('#skF_2'))))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1('#skF_2'))))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1('#skF_2'))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1('#skF_2')))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1('#skF_2')))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1('#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_851,c_165])).

tff(c_979,plain,(
    k5_relat_1(k2_funct_1(k2_funct_1('#skF_2')),k2_funct_1('#skF_2')) = k6_partfun1(k2_relat_1(k2_funct_1('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_624,c_528,c_761,c_502,c_851,c_309,c_851,c_500,c_851,c_851,c_945])).

tff(c_144,plain,(
    ! [A_53] :
      ( k5_relat_1(A_53,k2_funct_1(A_53)) = k6_partfun1(k1_relat_1(A_53))
      | ~ v2_funct_1(A_53)
      | ~ v1_funct_1(A_53)
      | ~ v1_relat_1(A_53) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_12])).

tff(c_153,plain,(
    ! [A_5] :
      ( k6_partfun1(k1_relat_1(k2_funct_1(A_5))) = k5_relat_1(k2_funct_1(A_5),A_5)
      | ~ v2_funct_1(k2_funct_1(A_5))
      | ~ v1_funct_1(k2_funct_1(A_5))
      | ~ v1_relat_1(k2_funct_1(A_5))
      | ~ v2_funct_1(A_5)
      | ~ v1_funct_1(A_5)
      | ~ v1_relat_1(A_5) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_144])).

tff(c_1262,plain,
    ( k6_partfun1(k1_relat_1(k2_funct_1(k2_funct_1('#skF_2')))) = k6_partfun1(k2_relat_1(k2_funct_1('#skF_2')))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1('#skF_2')))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1('#skF_2')))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1('#skF_2')))
    | ~ v2_funct_1(k2_funct_1('#skF_2'))
    | ~ v1_funct_1(k2_funct_1('#skF_2'))
    | ~ v1_relat_1(k2_funct_1('#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_979,c_153])).

tff(c_1278,plain,(
    k6_partfun1(k2_relat_1(k2_funct_1('#skF_2'))) = k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_502,c_309,c_500,c_624,c_528,c_761,c_1213,c_1262])).

tff(c_1296,plain,
    ( k5_relat_1('#skF_2',k2_funct_1('#skF_2')) = k6_partfun1('#skF_1')
    | ~ v2_funct_1(k2_funct_1('#skF_2'))
    | ~ v1_funct_1(k2_funct_1('#skF_2'))
    | ~ v1_relat_1(k2_funct_1('#skF_2'))
    | ~ v2_funct_1('#skF_2')
    | ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_1278,c_165])).

tff(c_1343,plain,(
    k5_relat_1('#skF_2',k2_funct_1('#skF_2')) = k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_56,c_183,c_502,c_309,c_500,c_1296])).

tff(c_503,plain,(
    ! [D_109,F_108,B_110,A_105,C_106,E_107] :
      ( k1_partfun1(A_105,B_110,C_106,D_109,E_107,F_108) = k5_relat_1(E_107,F_108)
      | ~ m1_subset_1(F_108,k1_zfmisc_1(k2_zfmisc_1(C_106,D_109)))
      | ~ v1_funct_1(F_108)
      | ~ m1_subset_1(E_107,k1_zfmisc_1(k2_zfmisc_1(A_105,B_110)))
      | ~ v1_funct_1(E_107) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_505,plain,(
    ! [A_105,B_110,E_107] :
      ( k1_partfun1(A_105,B_110,'#skF_1','#skF_1',E_107,k2_funct_1('#skF_2')) = k5_relat_1(E_107,k2_funct_1('#skF_2'))
      | ~ v1_funct_1(k2_funct_1('#skF_2'))
      | ~ m1_subset_1(E_107,k1_zfmisc_1(k2_zfmisc_1(A_105,B_110)))
      | ~ v1_funct_1(E_107) ) ),
    inference(resolution,[status(thm)],[c_451,c_503])).

tff(c_1930,plain,(
    ! [A_151,B_152,E_153] :
      ( k1_partfun1(A_151,B_152,'#skF_1','#skF_1',E_153,k2_funct_1('#skF_2')) = k5_relat_1(E_153,k2_funct_1('#skF_2'))
      | ~ m1_subset_1(E_153,k1_zfmisc_1(k2_zfmisc_1(A_151,B_152)))
      | ~ v1_funct_1(E_153) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_309,c_505])).

tff(c_1964,plain,
    ( k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2',k2_funct_1('#skF_2')) = k5_relat_1('#skF_2',k2_funct_1('#skF_2'))
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_50,c_1930])).

tff(c_1981,plain,(
    k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2',k2_funct_1('#skF_2')) = k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_1343,c_1964])).

tff(c_48,plain,
    ( ~ r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1',k2_funct_2('#skF_1','#skF_2'),'#skF_2'),k6_partfun1('#skF_1'))
    | ~ r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2',k2_funct_2('#skF_1','#skF_2')),k6_partfun1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_85,plain,(
    ~ r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2',k2_funct_2('#skF_1','#skF_2')),k6_partfun1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_48])).

tff(c_310,plain,(
    ~ r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2',k2_funct_1('#skF_2')),k6_partfun1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_308,c_85])).

tff(c_1982,plain,(
    ~ r2_relset_1('#skF_1','#skF_1',k6_partfun1('#skF_1'),k6_partfun1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1981,c_310])).

tff(c_1985,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_272,c_1982])).

tff(c_1986,plain,(
    ~ r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1',k2_funct_2('#skF_1','#skF_2'),'#skF_2'),k6_partfun1('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_2213,plain,(
    ~ r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1',k2_funct_1('#skF_2'),'#skF_2'),k6_partfun1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2210,c_1986])).

tff(c_3319,plain,(
    ~ r2_relset_1('#skF_1','#skF_1',k6_partfun1('#skF_1'),k6_partfun1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3287,c_2213])).

tff(c_3322,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2158,c_3319])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n017.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 14:05:01 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.42/2.00  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.42/2.02  
% 5.42/2.02  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.42/2.02  %$ r2_relset_1 > v3_funct_2 > v1_funct_2 > v2_funct_2 > v1_partfun1 > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k1_relset_1 > k6_subset_1 > k5_relat_1 > k2_zfmisc_1 > k2_funct_2 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_1
% 5.42/2.02  
% 5.42/2.02  %Foreground sorts:
% 5.42/2.02  
% 5.42/2.02  
% 5.42/2.02  %Background operators:
% 5.42/2.02  
% 5.42/2.02  
% 5.42/2.02  %Foreground operators:
% 5.42/2.02  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 5.42/2.02  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 5.42/2.02  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 5.42/2.02  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.42/2.02  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 5.42/2.02  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 5.42/2.02  tff(k2_funct_2, type, k2_funct_2: ($i * $i) > $i).
% 5.42/2.02  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 5.42/2.02  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 5.42/2.02  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 5.42/2.02  tff('#skF_2', type, '#skF_2': $i).
% 5.42/2.02  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 5.42/2.02  tff(k6_subset_1, type, k6_subset_1: ($i * $i) > $i).
% 5.42/2.02  tff('#skF_1', type, '#skF_1': $i).
% 5.42/2.02  tff(v2_funct_2, type, v2_funct_2: ($i * $i) > $o).
% 5.42/2.02  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 5.42/2.02  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.42/2.02  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 5.42/2.02  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.42/2.02  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.42/2.02  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 5.42/2.02  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 5.42/2.02  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.42/2.02  tff(v3_funct_2, type, v3_funct_2: ($i * $i * $i) > $o).
% 5.42/2.02  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 5.42/2.02  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.42/2.02  
% 5.42/2.05  tff(f_103, axiom, (![A]: (v1_partfun1(k6_partfun1(A), A) & m1_subset_1(k6_partfun1(A), k1_zfmisc_1(k2_zfmisc_1(A, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_partfun1)).
% 5.42/2.05  tff(f_71, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => r2_relset_1(A, B, C, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', reflexivity_r2_relset_1)).
% 5.42/2.05  tff(f_146, negated_conjecture, ~(![A, B]: ((((v1_funct_1(B) & v1_funct_2(B, A, A)) & v3_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (r2_relset_1(A, A, k1_partfun1(A, A, A, A, B, k2_funct_2(A, B)), k6_partfun1(A)) & r2_relset_1(A, A, k1_partfun1(A, A, A, A, k2_funct_2(A, B), B), k6_partfun1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t88_funct_2)).
% 5.42/2.05  tff(f_123, axiom, (![A, B]: ((((v1_funct_1(B) & v1_funct_2(B, A, A)) & v3_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (k2_funct_2(A, B) = k2_funct_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_funct_2)).
% 5.42/2.05  tff(f_99, axiom, (![A, B]: ((((v1_funct_1(B) & v1_funct_2(B, A, A)) & v3_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (((v1_funct_1(k2_funct_2(A, B)) & v1_funct_2(k2_funct_2(A, B), A, A)) & v3_funct_2(k2_funct_2(A, B), A, A)) & m1_subset_1(k2_funct_2(A, B), k1_zfmisc_1(k2_zfmisc_1(A, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_funct_2)).
% 5.42/2.05  tff(f_61, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 5.42/2.05  tff(f_83, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v3_funct_2(C, A, B)) => ((v1_funct_1(C) & v2_funct_1(C)) & v2_funct_2(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_funct_2)).
% 5.42/2.05  tff(f_133, axiom, (![A, B]: (((v1_funct_1(B) & v1_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (k1_relset_1(A, A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t67_funct_2)).
% 5.42/2.05  tff(f_65, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 5.42/2.05  tff(f_57, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => (k2_funct_1(k2_funct_1(A)) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_funct_1)).
% 5.42/2.05  tff(f_125, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 5.42/2.05  tff(f_49, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k5_relat_1(A, k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))) & (k5_relat_1(k2_funct_1(A), A) = k6_relat_1(k2_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t61_funct_1)).
% 5.42/2.05  tff(f_113, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 5.42/2.05  tff(c_38, plain, (![A_21]: (m1_subset_1(k6_partfun1(A_21), k1_zfmisc_1(k2_zfmisc_1(A_21, A_21))))), inference(cnfTransformation, [status(thm)], [f_103])).
% 5.42/2.05  tff(c_2113, plain, (![A_179, B_180, C_181, D_182]: (r2_relset_1(A_179, B_180, C_181, C_181) | ~m1_subset_1(D_182, k1_zfmisc_1(k2_zfmisc_1(A_179, B_180))) | ~m1_subset_1(C_181, k1_zfmisc_1(k2_zfmisc_1(A_179, B_180))))), inference(cnfTransformation, [status(thm)], [f_71])).
% 5.42/2.05  tff(c_2150, plain, (![A_185, C_186]: (r2_relset_1(A_185, A_185, C_186, C_186) | ~m1_subset_1(C_186, k1_zfmisc_1(k2_zfmisc_1(A_185, A_185))))), inference(resolution, [status(thm)], [c_38, c_2113])).
% 5.42/2.05  tff(c_2158, plain, (![A_21]: (r2_relset_1(A_21, A_21, k6_partfun1(A_21), k6_partfun1(A_21)))), inference(resolution, [status(thm)], [c_38, c_2150])).
% 5.42/2.05  tff(c_56, plain, (v1_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_146])).
% 5.42/2.05  tff(c_54, plain, (v1_funct_2('#skF_2', '#skF_1', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_146])).
% 5.42/2.05  tff(c_52, plain, (v3_funct_2('#skF_2', '#skF_1', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_146])).
% 5.42/2.05  tff(c_50, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_146])).
% 5.42/2.05  tff(c_2195, plain, (![A_198, B_199]: (k2_funct_2(A_198, B_199)=k2_funct_1(B_199) | ~m1_subset_1(B_199, k1_zfmisc_1(k2_zfmisc_1(A_198, A_198))) | ~v3_funct_2(B_199, A_198, A_198) | ~v1_funct_2(B_199, A_198, A_198) | ~v1_funct_1(B_199))), inference(cnfTransformation, [status(thm)], [f_123])).
% 5.42/2.05  tff(c_2205, plain, (k2_funct_2('#skF_1', '#skF_2')=k2_funct_1('#skF_2') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_50, c_2195])).
% 5.42/2.05  tff(c_2210, plain, (k2_funct_2('#skF_1', '#skF_2')=k2_funct_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_52, c_2205])).
% 5.42/2.05  tff(c_2177, plain, (![A_195, B_196]: (v1_funct_1(k2_funct_2(A_195, B_196)) | ~m1_subset_1(B_196, k1_zfmisc_1(k2_zfmisc_1(A_195, A_195))) | ~v3_funct_2(B_196, A_195, A_195) | ~v1_funct_2(B_196, A_195, A_195) | ~v1_funct_1(B_196))), inference(cnfTransformation, [status(thm)], [f_99])).
% 5.42/2.05  tff(c_2187, plain, (v1_funct_1(k2_funct_2('#skF_1', '#skF_2')) | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_50, c_2177])).
% 5.42/2.05  tff(c_2192, plain, (v1_funct_1(k2_funct_2('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_52, c_2187])).
% 5.42/2.05  tff(c_2211, plain, (v1_funct_1(k2_funct_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_2210, c_2192])).
% 5.42/2.05  tff(c_71, plain, (![C_38, A_39, B_40]: (v1_relat_1(C_38) | ~m1_subset_1(C_38, k1_zfmisc_1(k2_zfmisc_1(A_39, B_40))))), inference(cnfTransformation, [status(thm)], [f_61])).
% 5.42/2.05  tff(c_84, plain, (v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_50, c_71])).
% 5.42/2.05  tff(c_2070, plain, (![C_168, A_169, B_170]: (v2_funct_1(C_168) | ~v3_funct_2(C_168, A_169, B_170) | ~v1_funct_1(C_168) | ~m1_subset_1(C_168, k1_zfmisc_1(k2_zfmisc_1(A_169, B_170))))), inference(cnfTransformation, [status(thm)], [f_83])).
% 5.42/2.05  tff(c_2080, plain, (v2_funct_1('#skF_2') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_50, c_2070])).
% 5.42/2.05  tff(c_2085, plain, (v2_funct_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_52, c_2080])).
% 5.42/2.05  tff(c_2313, plain, (![A_216, B_217]: (m1_subset_1(k2_funct_2(A_216, B_217), k1_zfmisc_1(k2_zfmisc_1(A_216, A_216))) | ~m1_subset_1(B_217, k1_zfmisc_1(k2_zfmisc_1(A_216, A_216))) | ~v3_funct_2(B_217, A_216, A_216) | ~v1_funct_2(B_217, A_216, A_216) | ~v1_funct_1(B_217))), inference(cnfTransformation, [status(thm)], [f_99])).
% 5.42/2.05  tff(c_2343, plain, (m1_subset_1(k2_funct_1('#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_2210, c_2313])).
% 5.42/2.05  tff(c_2355, plain, (m1_subset_1(k2_funct_1('#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_52, c_50, c_2343])).
% 5.42/2.05  tff(c_16, plain, (![C_8, A_6, B_7]: (v1_relat_1(C_8) | ~m1_subset_1(C_8, k1_zfmisc_1(k2_zfmisc_1(A_6, B_7))))), inference(cnfTransformation, [status(thm)], [f_61])).
% 5.42/2.05  tff(c_2406, plain, (v1_relat_1(k2_funct_1('#skF_2'))), inference(resolution, [status(thm)], [c_2355, c_16])).
% 5.42/2.05  tff(c_2219, plain, (![A_203, B_204]: (v3_funct_2(k2_funct_2(A_203, B_204), A_203, A_203) | ~m1_subset_1(B_204, k1_zfmisc_1(k2_zfmisc_1(A_203, A_203))) | ~v3_funct_2(B_204, A_203, A_203) | ~v1_funct_2(B_204, A_203, A_203) | ~v1_funct_1(B_204))), inference(cnfTransformation, [status(thm)], [f_99])).
% 5.42/2.05  tff(c_2226, plain, (v3_funct_2(k2_funct_2('#skF_1', '#skF_2'), '#skF_1', '#skF_1') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_50, c_2219])).
% 5.42/2.05  tff(c_2231, plain, (v3_funct_2(k2_funct_1('#skF_2'), '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_52, c_2210, c_2226])).
% 5.42/2.05  tff(c_24, plain, (![C_18, A_16, B_17]: (v2_funct_1(C_18) | ~v3_funct_2(C_18, A_16, B_17) | ~v1_funct_1(C_18) | ~m1_subset_1(C_18, k1_zfmisc_1(k2_zfmisc_1(A_16, B_17))))), inference(cnfTransformation, [status(thm)], [f_83])).
% 5.42/2.05  tff(c_2376, plain, (v2_funct_1(k2_funct_1('#skF_2')) | ~v3_funct_2(k2_funct_1('#skF_2'), '#skF_1', '#skF_1') | ~v1_funct_1(k2_funct_1('#skF_2'))), inference(resolution, [status(thm)], [c_2355, c_24])).
% 5.42/2.05  tff(c_2404, plain, (v2_funct_1(k2_funct_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_2211, c_2231, c_2376])).
% 5.42/2.05  tff(c_2234, plain, (![A_207, B_208]: (v1_funct_2(k2_funct_2(A_207, B_208), A_207, A_207) | ~m1_subset_1(B_208, k1_zfmisc_1(k2_zfmisc_1(A_207, A_207))) | ~v3_funct_2(B_208, A_207, A_207) | ~v1_funct_2(B_208, A_207, A_207) | ~v1_funct_1(B_208))), inference(cnfTransformation, [status(thm)], [f_99])).
% 5.42/2.05  tff(c_2241, plain, (v1_funct_2(k2_funct_2('#skF_1', '#skF_2'), '#skF_1', '#skF_1') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_50, c_2234])).
% 5.42/2.05  tff(c_2246, plain, (v1_funct_2(k2_funct_1('#skF_2'), '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_52, c_2210, c_2241])).
% 5.42/2.05  tff(c_46, plain, (![A_31, B_32]: (k1_relset_1(A_31, A_31, B_32)=A_31 | ~m1_subset_1(B_32, k1_zfmisc_1(k2_zfmisc_1(A_31, A_31))) | ~v1_funct_2(B_32, A_31, A_31) | ~v1_funct_1(B_32))), inference(cnfTransformation, [status(thm)], [f_133])).
% 5.42/2.05  tff(c_2370, plain, (k1_relset_1('#skF_1', '#skF_1', k2_funct_1('#skF_2'))='#skF_1' | ~v1_funct_2(k2_funct_1('#skF_2'), '#skF_1', '#skF_1') | ~v1_funct_1(k2_funct_1('#skF_2'))), inference(resolution, [status(thm)], [c_2355, c_46])).
% 5.42/2.05  tff(c_2398, plain, (k1_relset_1('#skF_1', '#skF_1', k2_funct_1('#skF_2'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_2211, c_2246, c_2370])).
% 5.42/2.05  tff(c_18, plain, (![A_9, B_10, C_11]: (k1_relset_1(A_9, B_10, C_11)=k1_relat_1(C_11) | ~m1_subset_1(C_11, k1_zfmisc_1(k2_zfmisc_1(A_9, B_10))))), inference(cnfTransformation, [status(thm)], [f_65])).
% 5.42/2.05  tff(c_2405, plain, (k1_relset_1('#skF_1', '#skF_1', k2_funct_1('#skF_2'))=k1_relat_1(k2_funct_1('#skF_2'))), inference(resolution, [status(thm)], [c_2355, c_18])).
% 5.42/2.05  tff(c_2459, plain, (k1_relat_1(k2_funct_1('#skF_2'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_2398, c_2405])).
% 5.42/2.05  tff(c_14, plain, (![A_5]: (k2_funct_1(k2_funct_1(A_5))=A_5 | ~v2_funct_1(A_5) | ~v1_funct_1(A_5) | ~v1_relat_1(A_5))), inference(cnfTransformation, [status(thm)], [f_57])).
% 5.42/2.05  tff(c_44, plain, (![A_30]: (k6_relat_1(A_30)=k6_partfun1(A_30))), inference(cnfTransformation, [status(thm)], [f_125])).
% 5.42/2.05  tff(c_12, plain, (![A_4]: (k5_relat_1(A_4, k2_funct_1(A_4))=k6_relat_1(k1_relat_1(A_4)) | ~v2_funct_1(A_4) | ~v1_funct_1(A_4) | ~v1_relat_1(A_4))), inference(cnfTransformation, [status(thm)], [f_49])).
% 5.42/2.05  tff(c_2046, plain, (![A_166]: (k5_relat_1(A_166, k2_funct_1(A_166))=k6_partfun1(k1_relat_1(A_166)) | ~v2_funct_1(A_166) | ~v1_funct_1(A_166) | ~v1_relat_1(A_166))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_12])).
% 5.42/2.05  tff(c_2791, plain, (![A_234]: (k6_partfun1(k1_relat_1(k2_funct_1(A_234)))=k5_relat_1(k2_funct_1(A_234), A_234) | ~v2_funct_1(k2_funct_1(A_234)) | ~v1_funct_1(k2_funct_1(A_234)) | ~v1_relat_1(k2_funct_1(A_234)) | ~v2_funct_1(A_234) | ~v1_funct_1(A_234) | ~v1_relat_1(A_234))), inference(superposition, [status(thm), theory('equality')], [c_14, c_2046])).
% 5.42/2.05  tff(c_2853, plain, (k5_relat_1(k2_funct_1('#skF_2'), '#skF_2')=k6_partfun1('#skF_1') | ~v2_funct_1(k2_funct_1('#skF_2')) | ~v1_funct_1(k2_funct_1('#skF_2')) | ~v1_relat_1(k2_funct_1('#skF_2')) | ~v2_funct_1('#skF_2') | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_2459, c_2791])).
% 5.42/2.05  tff(c_2867, plain, (k5_relat_1(k2_funct_1('#skF_2'), '#skF_2')=k6_partfun1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_84, c_56, c_2085, c_2406, c_2211, c_2404, c_2853])).
% 5.42/2.05  tff(c_28, plain, (![A_19, B_20]: (m1_subset_1(k2_funct_2(A_19, B_20), k1_zfmisc_1(k2_zfmisc_1(A_19, A_19))) | ~m1_subset_1(B_20, k1_zfmisc_1(k2_zfmisc_1(A_19, A_19))) | ~v3_funct_2(B_20, A_19, A_19) | ~v1_funct_2(B_20, A_19, A_19) | ~v1_funct_1(B_20))), inference(cnfTransformation, [status(thm)], [f_99])).
% 5.42/2.05  tff(c_2426, plain, (![A_218, F_221, D_222, B_223, C_219, E_220]: (k1_partfun1(A_218, B_223, C_219, D_222, E_220, F_221)=k5_relat_1(E_220, F_221) | ~m1_subset_1(F_221, k1_zfmisc_1(k2_zfmisc_1(C_219, D_222))) | ~v1_funct_1(F_221) | ~m1_subset_1(E_220, k1_zfmisc_1(k2_zfmisc_1(A_218, B_223))) | ~v1_funct_1(E_220))), inference(cnfTransformation, [status(thm)], [f_113])).
% 5.42/2.05  tff(c_2437, plain, (![A_218, B_223, E_220]: (k1_partfun1(A_218, B_223, '#skF_1', '#skF_1', E_220, '#skF_2')=k5_relat_1(E_220, '#skF_2') | ~v1_funct_1('#skF_2') | ~m1_subset_1(E_220, k1_zfmisc_1(k2_zfmisc_1(A_218, B_223))) | ~v1_funct_1(E_220))), inference(resolution, [status(thm)], [c_50, c_2426])).
% 5.42/2.05  tff(c_2464, plain, (![A_224, B_225, E_226]: (k1_partfun1(A_224, B_225, '#skF_1', '#skF_1', E_226, '#skF_2')=k5_relat_1(E_226, '#skF_2') | ~m1_subset_1(E_226, k1_zfmisc_1(k2_zfmisc_1(A_224, B_225))) | ~v1_funct_1(E_226))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_2437])).
% 5.42/2.05  tff(c_3259, plain, (![A_242, B_243]: (k1_partfun1(A_242, A_242, '#skF_1', '#skF_1', k2_funct_2(A_242, B_243), '#skF_2')=k5_relat_1(k2_funct_2(A_242, B_243), '#skF_2') | ~v1_funct_1(k2_funct_2(A_242, B_243)) | ~m1_subset_1(B_243, k1_zfmisc_1(k2_zfmisc_1(A_242, A_242))) | ~v3_funct_2(B_243, A_242, A_242) | ~v1_funct_2(B_243, A_242, A_242) | ~v1_funct_1(B_243))), inference(resolution, [status(thm)], [c_28, c_2464])).
% 5.42/2.05  tff(c_3274, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', k2_funct_2('#skF_1', '#skF_2'), '#skF_2')=k5_relat_1(k2_funct_2('#skF_1', '#skF_2'), '#skF_2') | ~v1_funct_1(k2_funct_2('#skF_1', '#skF_2')) | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_50, c_3259])).
% 5.42/2.05  tff(c_3287, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', k2_funct_1('#skF_2'), '#skF_2')=k6_partfun1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_52, c_2211, c_2210, c_2867, c_2210, c_2210, c_3274])).
% 5.42/2.05  tff(c_238, plain, (![A_69, B_70, C_71, D_72]: (r2_relset_1(A_69, B_70, C_71, C_71) | ~m1_subset_1(D_72, k1_zfmisc_1(k2_zfmisc_1(A_69, B_70))) | ~m1_subset_1(C_71, k1_zfmisc_1(k2_zfmisc_1(A_69, B_70))))), inference(cnfTransformation, [status(thm)], [f_71])).
% 5.42/2.05  tff(c_264, plain, (![A_75, C_76]: (r2_relset_1(A_75, A_75, C_76, C_76) | ~m1_subset_1(C_76, k1_zfmisc_1(k2_zfmisc_1(A_75, A_75))))), inference(resolution, [status(thm)], [c_38, c_238])).
% 5.42/2.05  tff(c_272, plain, (![A_21]: (r2_relset_1(A_21, A_21, k6_partfun1(A_21), k6_partfun1(A_21)))), inference(resolution, [status(thm)], [c_38, c_264])).
% 5.42/2.05  tff(c_168, plain, (![C_55, A_56, B_57]: (v2_funct_1(C_55) | ~v3_funct_2(C_55, A_56, B_57) | ~v1_funct_1(C_55) | ~m1_subset_1(C_55, k1_zfmisc_1(k2_zfmisc_1(A_56, B_57))))), inference(cnfTransformation, [status(thm)], [f_83])).
% 5.42/2.05  tff(c_178, plain, (v2_funct_1('#skF_2') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_50, c_168])).
% 5.42/2.05  tff(c_183, plain, (v2_funct_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_52, c_178])).
% 5.42/2.05  tff(c_293, plain, (![A_87, B_88]: (k2_funct_2(A_87, B_88)=k2_funct_1(B_88) | ~m1_subset_1(B_88, k1_zfmisc_1(k2_zfmisc_1(A_87, A_87))) | ~v3_funct_2(B_88, A_87, A_87) | ~v1_funct_2(B_88, A_87, A_87) | ~v1_funct_1(B_88))), inference(cnfTransformation, [status(thm)], [f_123])).
% 5.42/2.05  tff(c_303, plain, (k2_funct_2('#skF_1', '#skF_2')=k2_funct_1('#skF_2') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_50, c_293])).
% 5.42/2.05  tff(c_308, plain, (k2_funct_2('#skF_1', '#skF_2')=k2_funct_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_52, c_303])).
% 5.42/2.05  tff(c_409, plain, (![A_103, B_104]: (m1_subset_1(k2_funct_2(A_103, B_104), k1_zfmisc_1(k2_zfmisc_1(A_103, A_103))) | ~m1_subset_1(B_104, k1_zfmisc_1(k2_zfmisc_1(A_103, A_103))) | ~v3_funct_2(B_104, A_103, A_103) | ~v1_funct_2(B_104, A_103, A_103) | ~v1_funct_1(B_104))), inference(cnfTransformation, [status(thm)], [f_99])).
% 5.42/2.05  tff(c_439, plain, (m1_subset_1(k2_funct_1('#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_308, c_409])).
% 5.42/2.05  tff(c_451, plain, (m1_subset_1(k2_funct_1('#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_52, c_50, c_439])).
% 5.42/2.05  tff(c_502, plain, (v1_relat_1(k2_funct_1('#skF_2'))), inference(resolution, [status(thm)], [c_451, c_16])).
% 5.42/2.05  tff(c_248, plain, (![A_73, B_74]: (v1_funct_1(k2_funct_2(A_73, B_74)) | ~m1_subset_1(B_74, k1_zfmisc_1(k2_zfmisc_1(A_73, A_73))) | ~v3_funct_2(B_74, A_73, A_73) | ~v1_funct_2(B_74, A_73, A_73) | ~v1_funct_1(B_74))), inference(cnfTransformation, [status(thm)], [f_99])).
% 5.42/2.05  tff(c_258, plain, (v1_funct_1(k2_funct_2('#skF_1', '#skF_2')) | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_50, c_248])).
% 5.42/2.05  tff(c_263, plain, (v1_funct_1(k2_funct_2('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_52, c_258])).
% 5.42/2.05  tff(c_309, plain, (v1_funct_1(k2_funct_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_308, c_263])).
% 5.42/2.05  tff(c_332, plain, (![A_99, B_100]: (v3_funct_2(k2_funct_2(A_99, B_100), A_99, A_99) | ~m1_subset_1(B_100, k1_zfmisc_1(k2_zfmisc_1(A_99, A_99))) | ~v3_funct_2(B_100, A_99, A_99) | ~v1_funct_2(B_100, A_99, A_99) | ~v1_funct_1(B_100))), inference(cnfTransformation, [status(thm)], [f_99])).
% 5.42/2.05  tff(c_339, plain, (v3_funct_2(k2_funct_2('#skF_1', '#skF_2'), '#skF_1', '#skF_1') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_50, c_332])).
% 5.42/2.05  tff(c_344, plain, (v3_funct_2(k2_funct_1('#skF_2'), '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_52, c_308, c_339])).
% 5.42/2.05  tff(c_472, plain, (v2_funct_1(k2_funct_1('#skF_2')) | ~v3_funct_2(k2_funct_1('#skF_2'), '#skF_1', '#skF_1') | ~v1_funct_1(k2_funct_1('#skF_2'))), inference(resolution, [status(thm)], [c_451, c_24])).
% 5.42/2.05  tff(c_500, plain, (v2_funct_1(k2_funct_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_309, c_344, c_472])).
% 5.42/2.05  tff(c_315, plain, (![A_89, B_90]: (v1_funct_2(k2_funct_2(A_89, B_90), A_89, A_89) | ~m1_subset_1(B_90, k1_zfmisc_1(k2_zfmisc_1(A_89, A_89))) | ~v3_funct_2(B_90, A_89, A_89) | ~v1_funct_2(B_90, A_89, A_89) | ~v1_funct_1(B_90))), inference(cnfTransformation, [status(thm)], [f_99])).
% 5.42/2.05  tff(c_322, plain, (v1_funct_2(k2_funct_2('#skF_1', '#skF_2'), '#skF_1', '#skF_1') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_50, c_315])).
% 5.42/2.05  tff(c_327, plain, (v1_funct_2(k2_funct_1('#skF_2'), '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_52, c_308, c_322])).
% 5.42/2.05  tff(c_42, plain, (![A_28, B_29]: (k2_funct_2(A_28, B_29)=k2_funct_1(B_29) | ~m1_subset_1(B_29, k1_zfmisc_1(k2_zfmisc_1(A_28, A_28))) | ~v3_funct_2(B_29, A_28, A_28) | ~v1_funct_2(B_29, A_28, A_28) | ~v1_funct_1(B_29))), inference(cnfTransformation, [status(thm)], [f_123])).
% 5.42/2.05  tff(c_458, plain, (k2_funct_2('#skF_1', k2_funct_1('#skF_2'))=k2_funct_1(k2_funct_1('#skF_2')) | ~v3_funct_2(k2_funct_1('#skF_2'), '#skF_1', '#skF_1') | ~v1_funct_2(k2_funct_1('#skF_2'), '#skF_1', '#skF_1') | ~v1_funct_1(k2_funct_1('#skF_2'))), inference(resolution, [status(thm)], [c_451, c_42])).
% 5.42/2.05  tff(c_487, plain, (k2_funct_2('#skF_1', k2_funct_1('#skF_2'))=k2_funct_1(k2_funct_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_309, c_327, c_344, c_458])).
% 5.42/2.05  tff(c_605, plain, (![A_114, B_115]: (v1_relat_1(k2_funct_2(A_114, B_115)) | ~m1_subset_1(B_115, k1_zfmisc_1(k2_zfmisc_1(A_114, A_114))) | ~v3_funct_2(B_115, A_114, A_114) | ~v1_funct_2(B_115, A_114, A_114) | ~v1_funct_1(B_115))), inference(resolution, [status(thm)], [c_409, c_16])).
% 5.42/2.05  tff(c_608, plain, (v1_relat_1(k2_funct_2('#skF_1', k2_funct_1('#skF_2'))) | ~v3_funct_2(k2_funct_1('#skF_2'), '#skF_1', '#skF_1') | ~v1_funct_2(k2_funct_1('#skF_2'), '#skF_1', '#skF_1') | ~v1_funct_1(k2_funct_1('#skF_2'))), inference(resolution, [status(thm)], [c_451, c_605])).
% 5.42/2.05  tff(c_624, plain, (v1_relat_1(k2_funct_1(k2_funct_1('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_309, c_327, c_344, c_487, c_608])).
% 5.42/2.05  tff(c_34, plain, (![A_19, B_20]: (v1_funct_1(k2_funct_2(A_19, B_20)) | ~m1_subset_1(B_20, k1_zfmisc_1(k2_zfmisc_1(A_19, A_19))) | ~v3_funct_2(B_20, A_19, A_19) | ~v1_funct_2(B_20, A_19, A_19) | ~v1_funct_1(B_20))), inference(cnfTransformation, [status(thm)], [f_99])).
% 5.42/2.05  tff(c_463, plain, (v1_funct_1(k2_funct_2('#skF_1', k2_funct_1('#skF_2'))) | ~v3_funct_2(k2_funct_1('#skF_2'), '#skF_1', '#skF_1') | ~v1_funct_2(k2_funct_1('#skF_2'), '#skF_1', '#skF_1') | ~v1_funct_1(k2_funct_1('#skF_2'))), inference(resolution, [status(thm)], [c_451, c_34])).
% 5.42/2.05  tff(c_491, plain, (v1_funct_1(k2_funct_2('#skF_1', k2_funct_1('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_309, c_327, c_344, c_463])).
% 5.42/2.05  tff(c_528, plain, (v1_funct_1(k2_funct_1(k2_funct_1('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_487, c_491])).
% 5.42/2.05  tff(c_30, plain, (![A_19, B_20]: (v3_funct_2(k2_funct_2(A_19, B_20), A_19, A_19) | ~m1_subset_1(B_20, k1_zfmisc_1(k2_zfmisc_1(A_19, A_19))) | ~v3_funct_2(B_20, A_19, A_19) | ~v1_funct_2(B_20, A_19, A_19) | ~v1_funct_1(B_20))), inference(cnfTransformation, [status(thm)], [f_99])).
% 5.42/2.05  tff(c_453, plain, (v3_funct_2(k2_funct_2('#skF_1', k2_funct_1('#skF_2')), '#skF_1', '#skF_1') | ~v3_funct_2(k2_funct_1('#skF_2'), '#skF_1', '#skF_1') | ~v1_funct_2(k2_funct_1('#skF_2'), '#skF_1', '#skF_1') | ~v1_funct_1(k2_funct_1('#skF_2'))), inference(resolution, [status(thm)], [c_451, c_30])).
% 5.42/2.05  tff(c_481, plain, (v3_funct_2(k2_funct_2('#skF_1', k2_funct_1('#skF_2')), '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_309, c_327, c_344, c_453])).
% 5.42/2.05  tff(c_575, plain, (v3_funct_2(k2_funct_1(k2_funct_1('#skF_2')), '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_487, c_481])).
% 5.42/2.05  tff(c_532, plain, (m1_subset_1(k2_funct_1(k2_funct_1('#skF_2')), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k2_funct_1('#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v3_funct_2(k2_funct_1('#skF_2'), '#skF_1', '#skF_1') | ~v1_funct_2(k2_funct_1('#skF_2'), '#skF_1', '#skF_1') | ~v1_funct_1(k2_funct_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_487, c_28])).
% 5.42/2.05  tff(c_536, plain, (m1_subset_1(k2_funct_1(k2_funct_1('#skF_2')), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_309, c_327, c_344, c_451, c_532])).
% 5.42/2.05  tff(c_721, plain, (v2_funct_1(k2_funct_1(k2_funct_1('#skF_2'))) | ~v3_funct_2(k2_funct_1(k2_funct_1('#skF_2')), '#skF_1', '#skF_1') | ~v1_funct_1(k2_funct_1(k2_funct_1('#skF_2')))), inference(resolution, [status(thm)], [c_536, c_24])).
% 5.42/2.05  tff(c_761, plain, (v2_funct_1(k2_funct_1(k2_funct_1('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_528, c_575, c_721])).
% 5.42/2.05  tff(c_32, plain, (![A_19, B_20]: (v1_funct_2(k2_funct_2(A_19, B_20), A_19, A_19) | ~m1_subset_1(B_20, k1_zfmisc_1(k2_zfmisc_1(A_19, A_19))) | ~v3_funct_2(B_20, A_19, A_19) | ~v1_funct_2(B_20, A_19, A_19) | ~v1_funct_1(B_20))), inference(cnfTransformation, [status(thm)], [f_99])).
% 5.42/2.05  tff(c_455, plain, (v1_funct_2(k2_funct_2('#skF_1', k2_funct_1('#skF_2')), '#skF_1', '#skF_1') | ~v3_funct_2(k2_funct_1('#skF_2'), '#skF_1', '#skF_1') | ~v1_funct_2(k2_funct_1('#skF_2'), '#skF_1', '#skF_1') | ~v1_funct_1(k2_funct_1('#skF_2'))), inference(resolution, [status(thm)], [c_451, c_32])).
% 5.42/2.05  tff(c_484, plain, (v1_funct_2(k2_funct_2('#skF_1', k2_funct_1('#skF_2')), '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_309, c_327, c_344, c_455])).
% 5.42/2.05  tff(c_569, plain, (v1_funct_2(k2_funct_1(k2_funct_1('#skF_2')), '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_487, c_484])).
% 5.42/2.05  tff(c_715, plain, (k1_relset_1('#skF_1', '#skF_1', k2_funct_1(k2_funct_1('#skF_2')))='#skF_1' | ~v1_funct_2(k2_funct_1(k2_funct_1('#skF_2')), '#skF_1', '#skF_1') | ~v1_funct_1(k2_funct_1(k2_funct_1('#skF_2')))), inference(resolution, [status(thm)], [c_536, c_46])).
% 5.42/2.05  tff(c_755, plain, (k1_relset_1('#skF_1', '#skF_1', k2_funct_1(k2_funct_1('#skF_2')))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_528, c_569, c_715])).
% 5.42/2.05  tff(c_762, plain, (k1_relset_1('#skF_1', '#skF_1', k2_funct_1(k2_funct_1('#skF_2')))=k1_relat_1(k2_funct_1(k2_funct_1('#skF_2')))), inference(resolution, [status(thm)], [c_536, c_18])).
% 5.42/2.05  tff(c_1213, plain, (k1_relat_1(k2_funct_1(k2_funct_1('#skF_2')))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_755, c_762])).
% 5.42/2.05  tff(c_707, plain, (k2_funct_2('#skF_1', k2_funct_1(k2_funct_1('#skF_2')))=k2_funct_1(k2_funct_1(k2_funct_1('#skF_2'))) | ~v3_funct_2(k2_funct_1(k2_funct_1('#skF_2')), '#skF_1', '#skF_1') | ~v1_funct_2(k2_funct_1(k2_funct_1('#skF_2')), '#skF_1', '#skF_1') | ~v1_funct_1(k2_funct_1(k2_funct_1('#skF_2')))), inference(resolution, [status(thm)], [c_536, c_42])).
% 5.42/2.05  tff(c_748, plain, (k2_funct_2('#skF_1', k2_funct_1(k2_funct_1('#skF_2')))=k2_funct_1(k2_funct_1(k2_funct_1('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_528, c_569, c_575, c_707])).
% 5.42/2.05  tff(c_845, plain, (k2_funct_1(k2_funct_1(k2_funct_1('#skF_2')))=k2_funct_2('#skF_1', '#skF_2') | ~v2_funct_1('#skF_2') | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_14, c_748])).
% 5.42/2.05  tff(c_851, plain, (k2_funct_1(k2_funct_1(k2_funct_1('#skF_2')))=k2_funct_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_84, c_56, c_183, c_308, c_845])).
% 5.42/2.05  tff(c_10, plain, (![A_4]: (k5_relat_1(k2_funct_1(A_4), A_4)=k6_relat_1(k2_relat_1(A_4)) | ~v2_funct_1(A_4) | ~v1_funct_1(A_4) | ~v1_relat_1(A_4))), inference(cnfTransformation, [status(thm)], [f_49])).
% 5.42/2.05  tff(c_156, plain, (![A_54]: (k5_relat_1(k2_funct_1(A_54), A_54)=k6_partfun1(k2_relat_1(A_54)) | ~v2_funct_1(A_54) | ~v1_funct_1(A_54) | ~v1_relat_1(A_54))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_10])).
% 5.42/2.05  tff(c_165, plain, (![A_5]: (k6_partfun1(k2_relat_1(k2_funct_1(A_5)))=k5_relat_1(A_5, k2_funct_1(A_5)) | ~v2_funct_1(k2_funct_1(A_5)) | ~v1_funct_1(k2_funct_1(A_5)) | ~v1_relat_1(k2_funct_1(A_5)) | ~v2_funct_1(A_5) | ~v1_funct_1(A_5) | ~v1_relat_1(A_5))), inference(superposition, [status(thm), theory('equality')], [c_14, c_156])).
% 5.42/2.05  tff(c_945, plain, (k6_partfun1(k2_relat_1(k2_funct_1(k2_funct_1(k2_funct_1('#skF_2')))))=k5_relat_1(k2_funct_1(k2_funct_1('#skF_2')), k2_funct_1('#skF_2')) | ~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1('#skF_2')))) | ~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1('#skF_2')))) | ~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1('#skF_2')))) | ~v2_funct_1(k2_funct_1(k2_funct_1('#skF_2'))) | ~v1_funct_1(k2_funct_1(k2_funct_1('#skF_2'))) | ~v1_relat_1(k2_funct_1(k2_funct_1('#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_851, c_165])).
% 5.42/2.05  tff(c_979, plain, (k5_relat_1(k2_funct_1(k2_funct_1('#skF_2')), k2_funct_1('#skF_2'))=k6_partfun1(k2_relat_1(k2_funct_1('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_624, c_528, c_761, c_502, c_851, c_309, c_851, c_500, c_851, c_851, c_945])).
% 5.42/2.05  tff(c_144, plain, (![A_53]: (k5_relat_1(A_53, k2_funct_1(A_53))=k6_partfun1(k1_relat_1(A_53)) | ~v2_funct_1(A_53) | ~v1_funct_1(A_53) | ~v1_relat_1(A_53))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_12])).
% 5.42/2.05  tff(c_153, plain, (![A_5]: (k6_partfun1(k1_relat_1(k2_funct_1(A_5)))=k5_relat_1(k2_funct_1(A_5), A_5) | ~v2_funct_1(k2_funct_1(A_5)) | ~v1_funct_1(k2_funct_1(A_5)) | ~v1_relat_1(k2_funct_1(A_5)) | ~v2_funct_1(A_5) | ~v1_funct_1(A_5) | ~v1_relat_1(A_5))), inference(superposition, [status(thm), theory('equality')], [c_14, c_144])).
% 5.42/2.05  tff(c_1262, plain, (k6_partfun1(k1_relat_1(k2_funct_1(k2_funct_1('#skF_2'))))=k6_partfun1(k2_relat_1(k2_funct_1('#skF_2'))) | ~v2_funct_1(k2_funct_1(k2_funct_1('#skF_2'))) | ~v1_funct_1(k2_funct_1(k2_funct_1('#skF_2'))) | ~v1_relat_1(k2_funct_1(k2_funct_1('#skF_2'))) | ~v2_funct_1(k2_funct_1('#skF_2')) | ~v1_funct_1(k2_funct_1('#skF_2')) | ~v1_relat_1(k2_funct_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_979, c_153])).
% 5.42/2.05  tff(c_1278, plain, (k6_partfun1(k2_relat_1(k2_funct_1('#skF_2')))=k6_partfun1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_502, c_309, c_500, c_624, c_528, c_761, c_1213, c_1262])).
% 5.42/2.05  tff(c_1296, plain, (k5_relat_1('#skF_2', k2_funct_1('#skF_2'))=k6_partfun1('#skF_1') | ~v2_funct_1(k2_funct_1('#skF_2')) | ~v1_funct_1(k2_funct_1('#skF_2')) | ~v1_relat_1(k2_funct_1('#skF_2')) | ~v2_funct_1('#skF_2') | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_1278, c_165])).
% 5.42/2.05  tff(c_1343, plain, (k5_relat_1('#skF_2', k2_funct_1('#skF_2'))=k6_partfun1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_84, c_56, c_183, c_502, c_309, c_500, c_1296])).
% 5.42/2.05  tff(c_503, plain, (![D_109, F_108, B_110, A_105, C_106, E_107]: (k1_partfun1(A_105, B_110, C_106, D_109, E_107, F_108)=k5_relat_1(E_107, F_108) | ~m1_subset_1(F_108, k1_zfmisc_1(k2_zfmisc_1(C_106, D_109))) | ~v1_funct_1(F_108) | ~m1_subset_1(E_107, k1_zfmisc_1(k2_zfmisc_1(A_105, B_110))) | ~v1_funct_1(E_107))), inference(cnfTransformation, [status(thm)], [f_113])).
% 5.42/2.05  tff(c_505, plain, (![A_105, B_110, E_107]: (k1_partfun1(A_105, B_110, '#skF_1', '#skF_1', E_107, k2_funct_1('#skF_2'))=k5_relat_1(E_107, k2_funct_1('#skF_2')) | ~v1_funct_1(k2_funct_1('#skF_2')) | ~m1_subset_1(E_107, k1_zfmisc_1(k2_zfmisc_1(A_105, B_110))) | ~v1_funct_1(E_107))), inference(resolution, [status(thm)], [c_451, c_503])).
% 5.42/2.05  tff(c_1930, plain, (![A_151, B_152, E_153]: (k1_partfun1(A_151, B_152, '#skF_1', '#skF_1', E_153, k2_funct_1('#skF_2'))=k5_relat_1(E_153, k2_funct_1('#skF_2')) | ~m1_subset_1(E_153, k1_zfmisc_1(k2_zfmisc_1(A_151, B_152))) | ~v1_funct_1(E_153))), inference(demodulation, [status(thm), theory('equality')], [c_309, c_505])).
% 5.42/2.05  tff(c_1964, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', k2_funct_1('#skF_2'))=k5_relat_1('#skF_2', k2_funct_1('#skF_2')) | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_50, c_1930])).
% 5.42/2.05  tff(c_1981, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', k2_funct_1('#skF_2'))=k6_partfun1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_1343, c_1964])).
% 5.42/2.05  tff(c_48, plain, (~r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', k2_funct_2('#skF_1', '#skF_2'), '#skF_2'), k6_partfun1('#skF_1')) | ~r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', k2_funct_2('#skF_1', '#skF_2')), k6_partfun1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_146])).
% 5.42/2.05  tff(c_85, plain, (~r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', k2_funct_2('#skF_1', '#skF_2')), k6_partfun1('#skF_1'))), inference(splitLeft, [status(thm)], [c_48])).
% 5.42/2.05  tff(c_310, plain, (~r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', k2_funct_1('#skF_2')), k6_partfun1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_308, c_85])).
% 5.42/2.05  tff(c_1982, plain, (~r2_relset_1('#skF_1', '#skF_1', k6_partfun1('#skF_1'), k6_partfun1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_1981, c_310])).
% 5.42/2.05  tff(c_1985, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_272, c_1982])).
% 5.42/2.05  tff(c_1986, plain, (~r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', k2_funct_2('#skF_1', '#skF_2'), '#skF_2'), k6_partfun1('#skF_1'))), inference(splitRight, [status(thm)], [c_48])).
% 5.42/2.05  tff(c_2213, plain, (~r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', k2_funct_1('#skF_2'), '#skF_2'), k6_partfun1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_2210, c_1986])).
% 5.42/2.05  tff(c_3319, plain, (~r2_relset_1('#skF_1', '#skF_1', k6_partfun1('#skF_1'), k6_partfun1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_3287, c_2213])).
% 5.42/2.05  tff(c_3322, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2158, c_3319])).
% 5.42/2.05  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.42/2.05  
% 5.42/2.05  Inference rules
% 5.42/2.05  ----------------------
% 5.42/2.05  #Ref     : 0
% 5.42/2.05  #Sup     : 793
% 5.42/2.05  #Fact    : 0
% 5.42/2.05  #Define  : 0
% 5.42/2.05  #Split   : 3
% 5.42/2.05  #Chain   : 0
% 5.42/2.05  #Close   : 0
% 5.42/2.05  
% 5.42/2.05  Ordering : KBO
% 5.42/2.05  
% 5.42/2.05  Simplification rules
% 5.42/2.05  ----------------------
% 5.42/2.05  #Subsume      : 91
% 5.42/2.05  #Demod        : 1462
% 5.42/2.05  #Tautology    : 337
% 5.42/2.05  #SimpNegUnit  : 0
% 5.42/2.05  #BackRed      : 28
% 5.42/2.05  
% 5.42/2.05  #Partial instantiations: 0
% 5.42/2.05  #Strategies tried      : 1
% 5.42/2.05  
% 5.42/2.05  Timing (in seconds)
% 5.42/2.05  ----------------------
% 5.42/2.05  Preprocessing        : 0.34
% 5.42/2.05  Parsing              : 0.18
% 5.42/2.05  CNF conversion       : 0.02
% 5.42/2.05  Main loop            : 0.92
% 5.42/2.05  Inferencing          : 0.30
% 5.42/2.05  Reduction            : 0.37
% 5.42/2.05  Demodulation         : 0.29
% 5.42/2.05  BG Simplification    : 0.04
% 5.42/2.05  Subsumption          : 0.15
% 5.42/2.05  Abstraction          : 0.04
% 5.42/2.05  MUC search           : 0.00
% 5.42/2.05  Cooper               : 0.00
% 5.42/2.05  Total                : 1.32
% 5.42/2.05  Index Insertion      : 0.00
% 5.42/2.05  Index Deletion       : 0.00
% 5.42/2.05  Index Matching       : 0.00
% 5.42/2.05  BG Taut test         : 0.00
%------------------------------------------------------------------------------
