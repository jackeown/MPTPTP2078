%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
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
%$ r2_relset_1 > v3_funct_2 > v1_funct_2 > v2_funct_2 > v1_partfun1 > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > k2_funct_2 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > #skF_1 > #skF_2 > #skF_3

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

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

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

tff(f_104,axiom,(
    ! [A] :
      ( v1_partfun1(k6_partfun1(A),A)
      & m1_subset_1(k6_partfun1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).

tff(f_72,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => r2_relset_1(A,B,C,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',reflexivity_r2_relset_1)).

tff(f_147,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_funct_1(B)
          & v1_funct_2(B,A,A)
          & v3_funct_2(B,A,A)
          & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
       => ( r2_relset_1(A,A,k1_partfun1(A,A,A,A,B,k2_funct_2(A,B)),k6_partfun1(A))
          & r2_relset_1(A,A,k1_partfun1(A,A,A,A,k2_funct_2(A,B),B),k6_partfun1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_funct_2)).

tff(f_124,axiom,(
    ! [A,B] :
      ( ( v1_funct_1(B)
        & v1_funct_2(B,A,A)
        & v3_funct_2(B,A,A)
        & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
     => k2_funct_2(A,B) = k2_funct_1(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_funct_2)).

tff(f_100,axiom,(
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

tff(f_62,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_84,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( ( v1_funct_1(C)
          & v3_funct_2(C,A,B) )
       => ( v1_funct_1(C)
          & v2_funct_1(C)
          & v2_funct_2(C,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_funct_2)).

tff(f_134,axiom,(
    ! [A,B] :
      ( ( v1_funct_1(B)
        & v1_funct_2(B,A,A)
        & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
     => k1_relset_1(A,A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_funct_2)).

tff(f_66,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_58,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => k2_funct_1(k2_funct_1(A)) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_funct_1)).

tff(f_126,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_50,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k5_relat_1(A,k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))
          & k5_relat_1(k2_funct_1(A),A) = k6_relat_1(k2_relat_1(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_1)).

tff(f_114,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(c_38,plain,(
    ! [A_21] : m1_subset_1(k6_partfun1(A_21),k1_zfmisc_1(k2_zfmisc_1(A_21,A_21))) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_2113,plain,(
    ! [A_161,B_162,C_163,D_164] :
      ( r2_relset_1(A_161,B_162,C_163,C_163)
      | ~ m1_subset_1(D_164,k1_zfmisc_1(k2_zfmisc_1(A_161,B_162)))
      | ~ m1_subset_1(C_163,k1_zfmisc_1(k2_zfmisc_1(A_161,B_162))) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_2150,plain,(
    ! [A_167,C_168] :
      ( r2_relset_1(A_167,A_167,C_168,C_168)
      | ~ m1_subset_1(C_168,k1_zfmisc_1(k2_zfmisc_1(A_167,A_167))) ) ),
    inference(resolution,[status(thm)],[c_38,c_2113])).

tff(c_2158,plain,(
    ! [A_21] : r2_relset_1(A_21,A_21,k6_partfun1(A_21),k6_partfun1(A_21)) ),
    inference(resolution,[status(thm)],[c_38,c_2150])).

tff(c_56,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_54,plain,(
    v1_funct_2('#skF_3','#skF_2','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_52,plain,(
    v3_funct_2('#skF_3','#skF_2','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_50,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_2195,plain,(
    ! [A_179,B_180] :
      ( k2_funct_2(A_179,B_180) = k2_funct_1(B_180)
      | ~ m1_subset_1(B_180,k1_zfmisc_1(k2_zfmisc_1(A_179,A_179)))
      | ~ v3_funct_2(B_180,A_179,A_179)
      | ~ v1_funct_2(B_180,A_179,A_179)
      | ~ v1_funct_1(B_180) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_2201,plain,
    ( k2_funct_2('#skF_2','#skF_3') = k2_funct_1('#skF_3')
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_50,c_2195])).

tff(c_2209,plain,(
    k2_funct_2('#skF_2','#skF_3') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_52,c_2201])).

tff(c_2177,plain,(
    ! [A_176,B_177] :
      ( v1_funct_1(k2_funct_2(A_176,B_177))
      | ~ m1_subset_1(B_177,k1_zfmisc_1(k2_zfmisc_1(A_176,A_176)))
      | ~ v3_funct_2(B_177,A_176,A_176)
      | ~ v1_funct_2(B_177,A_176,A_176)
      | ~ v1_funct_1(B_177) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_2183,plain,
    ( v1_funct_1(k2_funct_2('#skF_2','#skF_3'))
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_50,c_2177])).

tff(c_2191,plain,(
    v1_funct_1(k2_funct_2('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_52,c_2183])).

tff(c_2211,plain,(
    v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2209,c_2191])).

tff(c_71,plain,(
    ! [C_37,A_38,B_39] :
      ( v1_relat_1(C_37)
      | ~ m1_subset_1(C_37,k1_zfmisc_1(k2_zfmisc_1(A_38,B_39))) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_83,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_50,c_71])).

tff(c_2070,plain,(
    ! [C_151,A_152,B_153] :
      ( v2_funct_1(C_151)
      | ~ v3_funct_2(C_151,A_152,B_153)
      | ~ v1_funct_1(C_151)
      | ~ m1_subset_1(C_151,k1_zfmisc_1(k2_zfmisc_1(A_152,B_153))) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_2076,plain,
    ( v2_funct_1('#skF_3')
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_50,c_2070])).

tff(c_2084,plain,(
    v2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_52,c_2076])).

tff(c_2313,plain,(
    ! [A_194,B_195] :
      ( m1_subset_1(k2_funct_2(A_194,B_195),k1_zfmisc_1(k2_zfmisc_1(A_194,A_194)))
      | ~ m1_subset_1(B_195,k1_zfmisc_1(k2_zfmisc_1(A_194,A_194)))
      | ~ v3_funct_2(B_195,A_194,A_194)
      | ~ v1_funct_2(B_195,A_194,A_194)
      | ~ v1_funct_1(B_195) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_2343,plain,
    ( m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2')))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2')))
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_2209,c_2313])).

tff(c_2355,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_52,c_50,c_2343])).

tff(c_16,plain,(
    ! [C_8,A_6,B_7] :
      ( v1_relat_1(C_8)
      | ~ m1_subset_1(C_8,k1_zfmisc_1(k2_zfmisc_1(A_6,B_7))) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_2406,plain,(
    v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_2355,c_16])).

tff(c_2234,plain,(
    ! [A_187,B_188] :
      ( v3_funct_2(k2_funct_2(A_187,B_188),A_187,A_187)
      | ~ m1_subset_1(B_188,k1_zfmisc_1(k2_zfmisc_1(A_187,A_187)))
      | ~ v3_funct_2(B_188,A_187,A_187)
      | ~ v1_funct_2(B_188,A_187,A_187)
      | ~ v1_funct_1(B_188) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_2238,plain,
    ( v3_funct_2(k2_funct_2('#skF_2','#skF_3'),'#skF_2','#skF_2')
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_50,c_2234])).

tff(c_2245,plain,(
    v3_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_52,c_2209,c_2238])).

tff(c_24,plain,(
    ! [C_18,A_16,B_17] :
      ( v2_funct_1(C_18)
      | ~ v3_funct_2(C_18,A_16,B_17)
      | ~ v1_funct_1(C_18)
      | ~ m1_subset_1(C_18,k1_zfmisc_1(k2_zfmisc_1(A_16,B_17))) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_2376,plain,
    ( v2_funct_1(k2_funct_1('#skF_3'))
    | ~ v3_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_2')
    | ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_2355,c_24])).

tff(c_2404,plain,(
    v2_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2211,c_2245,c_2376])).

tff(c_2219,plain,(
    ! [A_183,B_184] :
      ( v1_funct_2(k2_funct_2(A_183,B_184),A_183,A_183)
      | ~ m1_subset_1(B_184,k1_zfmisc_1(k2_zfmisc_1(A_183,A_183)))
      | ~ v3_funct_2(B_184,A_183,A_183)
      | ~ v1_funct_2(B_184,A_183,A_183)
      | ~ v1_funct_1(B_184) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_2223,plain,
    ( v1_funct_2(k2_funct_2('#skF_2','#skF_3'),'#skF_2','#skF_2')
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_50,c_2219])).

tff(c_2230,plain,(
    v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_52,c_2209,c_2223])).

tff(c_46,plain,(
    ! [A_31,B_32] :
      ( k1_relset_1(A_31,A_31,B_32) = A_31
      | ~ m1_subset_1(B_32,k1_zfmisc_1(k2_zfmisc_1(A_31,A_31)))
      | ~ v1_funct_2(B_32,A_31,A_31)
      | ~ v1_funct_1(B_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_2370,plain,
    ( k1_relset_1('#skF_2','#skF_2',k2_funct_1('#skF_3')) = '#skF_2'
    | ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_2')
    | ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_2355,c_46])).

tff(c_2398,plain,(
    k1_relset_1('#skF_2','#skF_2',k2_funct_1('#skF_3')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2211,c_2230,c_2370])).

tff(c_18,plain,(
    ! [A_9,B_10,C_11] :
      ( k1_relset_1(A_9,B_10,C_11) = k1_relat_1(C_11)
      | ~ m1_subset_1(C_11,k1_zfmisc_1(k2_zfmisc_1(A_9,B_10))) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_2405,plain,(
    k1_relset_1('#skF_2','#skF_2',k2_funct_1('#skF_3')) = k1_relat_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_2355,c_18])).

tff(c_2459,plain,(
    k1_relat_1(k2_funct_1('#skF_3')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2398,c_2405])).

tff(c_14,plain,(
    ! [A_5] :
      ( k2_funct_1(k2_funct_1(A_5)) = A_5
      | ~ v2_funct_1(A_5)
      | ~ v1_funct_1(A_5)
      | ~ v1_relat_1(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_44,plain,(
    ! [A_30] : k6_relat_1(A_30) = k6_partfun1(A_30) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_12,plain,(
    ! [A_4] :
      ( k5_relat_1(A_4,k2_funct_1(A_4)) = k6_relat_1(k1_relat_1(A_4))
      | ~ v2_funct_1(A_4)
      | ~ v1_funct_1(A_4)
      | ~ v1_relat_1(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_2058,plain,(
    ! [A_150] :
      ( k5_relat_1(A_150,k2_funct_1(A_150)) = k6_partfun1(k1_relat_1(A_150))
      | ~ v2_funct_1(A_150)
      | ~ v1_funct_1(A_150)
      | ~ v1_relat_1(A_150) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_12])).

tff(c_2791,plain,(
    ! [A_212] :
      ( k6_partfun1(k1_relat_1(k2_funct_1(A_212))) = k5_relat_1(k2_funct_1(A_212),A_212)
      | ~ v2_funct_1(k2_funct_1(A_212))
      | ~ v1_funct_1(k2_funct_1(A_212))
      | ~ v1_relat_1(k2_funct_1(A_212))
      | ~ v2_funct_1(A_212)
      | ~ v1_funct_1(A_212)
      | ~ v1_relat_1(A_212) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_2058])).

tff(c_2853,plain,
    ( k5_relat_1(k2_funct_1('#skF_3'),'#skF_3') = k6_partfun1('#skF_2')
    | ~ v2_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_2459,c_2791])).

tff(c_2867,plain,(
    k5_relat_1(k2_funct_1('#skF_3'),'#skF_3') = k6_partfun1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_83,c_56,c_2084,c_2406,c_2211,c_2404,c_2853])).

tff(c_28,plain,(
    ! [A_19,B_20] :
      ( m1_subset_1(k2_funct_2(A_19,B_20),k1_zfmisc_1(k2_zfmisc_1(A_19,A_19)))
      | ~ m1_subset_1(B_20,k1_zfmisc_1(k2_zfmisc_1(A_19,A_19)))
      | ~ v3_funct_2(B_20,A_19,A_19)
      | ~ v1_funct_2(B_20,A_19,A_19)
      | ~ v1_funct_1(B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_2426,plain,(
    ! [F_199,E_198,C_197,D_200,A_196,B_201] :
      ( k1_partfun1(A_196,B_201,C_197,D_200,E_198,F_199) = k5_relat_1(E_198,F_199)
      | ~ m1_subset_1(F_199,k1_zfmisc_1(k2_zfmisc_1(C_197,D_200)))
      | ~ v1_funct_1(F_199)
      | ~ m1_subset_1(E_198,k1_zfmisc_1(k2_zfmisc_1(A_196,B_201)))
      | ~ v1_funct_1(E_198) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_2434,plain,(
    ! [A_196,B_201,E_198] :
      ( k1_partfun1(A_196,B_201,'#skF_2','#skF_2',E_198,'#skF_3') = k5_relat_1(E_198,'#skF_3')
      | ~ v1_funct_1('#skF_3')
      | ~ m1_subset_1(E_198,k1_zfmisc_1(k2_zfmisc_1(A_196,B_201)))
      | ~ v1_funct_1(E_198) ) ),
    inference(resolution,[status(thm)],[c_50,c_2426])).

tff(c_2464,plain,(
    ! [A_202,B_203,E_204] :
      ( k1_partfun1(A_202,B_203,'#skF_2','#skF_2',E_204,'#skF_3') = k5_relat_1(E_204,'#skF_3')
      | ~ m1_subset_1(E_204,k1_zfmisc_1(k2_zfmisc_1(A_202,B_203)))
      | ~ v1_funct_1(E_204) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_2434])).

tff(c_3259,plain,(
    ! [A_219,B_220] :
      ( k1_partfun1(A_219,A_219,'#skF_2','#skF_2',k2_funct_2(A_219,B_220),'#skF_3') = k5_relat_1(k2_funct_2(A_219,B_220),'#skF_3')
      | ~ v1_funct_1(k2_funct_2(A_219,B_220))
      | ~ m1_subset_1(B_220,k1_zfmisc_1(k2_zfmisc_1(A_219,A_219)))
      | ~ v3_funct_2(B_220,A_219,A_219)
      | ~ v1_funct_2(B_220,A_219,A_219)
      | ~ v1_funct_1(B_220) ) ),
    inference(resolution,[status(thm)],[c_28,c_2464])).

tff(c_3271,plain,
    ( k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2',k2_funct_2('#skF_2','#skF_3'),'#skF_3') = k5_relat_1(k2_funct_2('#skF_2','#skF_3'),'#skF_3')
    | ~ v1_funct_1(k2_funct_2('#skF_2','#skF_3'))
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_50,c_3259])).

tff(c_3286,plain,(
    k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2',k2_funct_1('#skF_3'),'#skF_3') = k6_partfun1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_52,c_2211,c_2209,c_2867,c_2209,c_2209,c_3271])).

tff(c_238,plain,(
    ! [A_66,B_67,C_68,D_69] :
      ( r2_relset_1(A_66,B_67,C_68,C_68)
      | ~ m1_subset_1(D_69,k1_zfmisc_1(k2_zfmisc_1(A_66,B_67)))
      | ~ m1_subset_1(C_68,k1_zfmisc_1(k2_zfmisc_1(A_66,B_67))) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_264,plain,(
    ! [A_72,C_73] :
      ( r2_relset_1(A_72,A_72,C_73,C_73)
      | ~ m1_subset_1(C_73,k1_zfmisc_1(k2_zfmisc_1(A_72,A_72))) ) ),
    inference(resolution,[status(thm)],[c_38,c_238])).

tff(c_272,plain,(
    ! [A_21] : r2_relset_1(A_21,A_21,k6_partfun1(A_21),k6_partfun1(A_21)) ),
    inference(resolution,[status(thm)],[c_38,c_264])).

tff(c_168,plain,(
    ! [C_53,A_54,B_55] :
      ( v2_funct_1(C_53)
      | ~ v3_funct_2(C_53,A_54,B_55)
      | ~ v1_funct_1(C_53)
      | ~ m1_subset_1(C_53,k1_zfmisc_1(k2_zfmisc_1(A_54,B_55))) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_174,plain,
    ( v2_funct_1('#skF_3')
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_50,c_168])).

tff(c_182,plain,(
    v2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_52,c_174])).

tff(c_293,plain,(
    ! [A_82,B_83] :
      ( k2_funct_2(A_82,B_83) = k2_funct_1(B_83)
      | ~ m1_subset_1(B_83,k1_zfmisc_1(k2_zfmisc_1(A_82,A_82)))
      | ~ v3_funct_2(B_83,A_82,A_82)
      | ~ v1_funct_2(B_83,A_82,A_82)
      | ~ v1_funct_1(B_83) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_299,plain,
    ( k2_funct_2('#skF_2','#skF_3') = k2_funct_1('#skF_3')
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_50,c_293])).

tff(c_307,plain,(
    k2_funct_2('#skF_2','#skF_3') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_52,c_299])).

tff(c_409,plain,(
    ! [A_96,B_97] :
      ( m1_subset_1(k2_funct_2(A_96,B_97),k1_zfmisc_1(k2_zfmisc_1(A_96,A_96)))
      | ~ m1_subset_1(B_97,k1_zfmisc_1(k2_zfmisc_1(A_96,A_96)))
      | ~ v3_funct_2(B_97,A_96,A_96)
      | ~ v1_funct_2(B_97,A_96,A_96)
      | ~ v1_funct_1(B_97) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_439,plain,
    ( m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2')))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2')))
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_307,c_409])).

tff(c_451,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_52,c_50,c_439])).

tff(c_502,plain,(
    v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_451,c_16])).

tff(c_248,plain,(
    ! [A_70,B_71] :
      ( v1_funct_1(k2_funct_2(A_70,B_71))
      | ~ m1_subset_1(B_71,k1_zfmisc_1(k2_zfmisc_1(A_70,A_70)))
      | ~ v3_funct_2(B_71,A_70,A_70)
      | ~ v1_funct_2(B_71,A_70,A_70)
      | ~ v1_funct_1(B_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_254,plain,
    ( v1_funct_1(k2_funct_2('#skF_2','#skF_3'))
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_50,c_248])).

tff(c_262,plain,(
    v1_funct_1(k2_funct_2('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_52,c_254])).

tff(c_309,plain,(
    v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_307,c_262])).

tff(c_315,plain,(
    ! [A_84,B_85] :
      ( v3_funct_2(k2_funct_2(A_84,B_85),A_84,A_84)
      | ~ m1_subset_1(B_85,k1_zfmisc_1(k2_zfmisc_1(A_84,A_84)))
      | ~ v3_funct_2(B_85,A_84,A_84)
      | ~ v1_funct_2(B_85,A_84,A_84)
      | ~ v1_funct_1(B_85) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_319,plain,
    ( v3_funct_2(k2_funct_2('#skF_2','#skF_3'),'#skF_2','#skF_2')
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_50,c_315])).

tff(c_326,plain,(
    v3_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_52,c_307,c_319])).

tff(c_472,plain,
    ( v2_funct_1(k2_funct_1('#skF_3'))
    | ~ v3_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_2')
    | ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_451,c_24])).

tff(c_500,plain,(
    v2_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_309,c_326,c_472])).

tff(c_332,plain,(
    ! [A_92,B_93] :
      ( v1_funct_2(k2_funct_2(A_92,B_93),A_92,A_92)
      | ~ m1_subset_1(B_93,k1_zfmisc_1(k2_zfmisc_1(A_92,A_92)))
      | ~ v3_funct_2(B_93,A_92,A_92)
      | ~ v1_funct_2(B_93,A_92,A_92)
      | ~ v1_funct_1(B_93) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_336,plain,
    ( v1_funct_2(k2_funct_2('#skF_2','#skF_3'),'#skF_2','#skF_2')
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_50,c_332])).

tff(c_343,plain,(
    v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_52,c_307,c_336])).

tff(c_42,plain,(
    ! [A_28,B_29] :
      ( k2_funct_2(A_28,B_29) = k2_funct_1(B_29)
      | ~ m1_subset_1(B_29,k1_zfmisc_1(k2_zfmisc_1(A_28,A_28)))
      | ~ v3_funct_2(B_29,A_28,A_28)
      | ~ v1_funct_2(B_29,A_28,A_28)
      | ~ v1_funct_1(B_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_458,plain,
    ( k2_funct_2('#skF_2',k2_funct_1('#skF_3')) = k2_funct_1(k2_funct_1('#skF_3'))
    | ~ v3_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_2')
    | ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_2')
    | ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_451,c_42])).

tff(c_487,plain,(
    k2_funct_2('#skF_2',k2_funct_1('#skF_3')) = k2_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_309,c_343,c_326,c_458])).

tff(c_605,plain,(
    ! [A_107,B_108] :
      ( v1_relat_1(k2_funct_2(A_107,B_108))
      | ~ m1_subset_1(B_108,k1_zfmisc_1(k2_zfmisc_1(A_107,A_107)))
      | ~ v3_funct_2(B_108,A_107,A_107)
      | ~ v1_funct_2(B_108,A_107,A_107)
      | ~ v1_funct_1(B_108) ) ),
    inference(resolution,[status(thm)],[c_409,c_16])).

tff(c_608,plain,
    ( v1_relat_1(k2_funct_2('#skF_2',k2_funct_1('#skF_3')))
    | ~ v3_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_2')
    | ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_2')
    | ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_451,c_605])).

tff(c_624,plain,(
    v1_relat_1(k2_funct_1(k2_funct_1('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_309,c_343,c_326,c_487,c_608])).

tff(c_34,plain,(
    ! [A_19,B_20] :
      ( v1_funct_1(k2_funct_2(A_19,B_20))
      | ~ m1_subset_1(B_20,k1_zfmisc_1(k2_zfmisc_1(A_19,A_19)))
      | ~ v3_funct_2(B_20,A_19,A_19)
      | ~ v1_funct_2(B_20,A_19,A_19)
      | ~ v1_funct_1(B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_463,plain,
    ( v1_funct_1(k2_funct_2('#skF_2',k2_funct_1('#skF_3')))
    | ~ v3_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_2')
    | ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_2')
    | ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_451,c_34])).

tff(c_491,plain,(
    v1_funct_1(k2_funct_2('#skF_2',k2_funct_1('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_309,c_343,c_326,c_463])).

tff(c_528,plain,(
    v1_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_487,c_491])).

tff(c_30,plain,(
    ! [A_19,B_20] :
      ( v3_funct_2(k2_funct_2(A_19,B_20),A_19,A_19)
      | ~ m1_subset_1(B_20,k1_zfmisc_1(k2_zfmisc_1(A_19,A_19)))
      | ~ v3_funct_2(B_20,A_19,A_19)
      | ~ v1_funct_2(B_20,A_19,A_19)
      | ~ v1_funct_1(B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_455,plain,
    ( v3_funct_2(k2_funct_2('#skF_2',k2_funct_1('#skF_3')),'#skF_2','#skF_2')
    | ~ v3_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_2')
    | ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_2')
    | ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_451,c_30])).

tff(c_484,plain,(
    v3_funct_2(k2_funct_2('#skF_2',k2_funct_1('#skF_3')),'#skF_2','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_309,c_343,c_326,c_455])).

tff(c_569,plain,(
    v3_funct_2(k2_funct_1(k2_funct_1('#skF_3')),'#skF_2','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_487,c_484])).

tff(c_532,plain,
    ( m1_subset_1(k2_funct_1(k2_funct_1('#skF_3')),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2')))
    | ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2')))
    | ~ v3_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_2')
    | ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_2')
    | ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_487,c_28])).

tff(c_536,plain,(
    m1_subset_1(k2_funct_1(k2_funct_1('#skF_3')),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_309,c_343,c_326,c_451,c_532])).

tff(c_721,plain,
    ( v2_funct_1(k2_funct_1(k2_funct_1('#skF_3')))
    | ~ v3_funct_2(k2_funct_1(k2_funct_1('#skF_3')),'#skF_2','#skF_2')
    | ~ v1_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) ),
    inference(resolution,[status(thm)],[c_536,c_24])).

tff(c_761,plain,(
    v2_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_528,c_569,c_721])).

tff(c_32,plain,(
    ! [A_19,B_20] :
      ( v1_funct_2(k2_funct_2(A_19,B_20),A_19,A_19)
      | ~ m1_subset_1(B_20,k1_zfmisc_1(k2_zfmisc_1(A_19,A_19)))
      | ~ v3_funct_2(B_20,A_19,A_19)
      | ~ v1_funct_2(B_20,A_19,A_19)
      | ~ v1_funct_1(B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_453,plain,
    ( v1_funct_2(k2_funct_2('#skF_2',k2_funct_1('#skF_3')),'#skF_2','#skF_2')
    | ~ v3_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_2')
    | ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_2')
    | ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_451,c_32])).

tff(c_481,plain,(
    v1_funct_2(k2_funct_2('#skF_2',k2_funct_1('#skF_3')),'#skF_2','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_309,c_343,c_326,c_453])).

tff(c_575,plain,(
    v1_funct_2(k2_funct_1(k2_funct_1('#skF_3')),'#skF_2','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_487,c_481])).

tff(c_715,plain,
    ( k1_relset_1('#skF_2','#skF_2',k2_funct_1(k2_funct_1('#skF_3'))) = '#skF_2'
    | ~ v1_funct_2(k2_funct_1(k2_funct_1('#skF_3')),'#skF_2','#skF_2')
    | ~ v1_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) ),
    inference(resolution,[status(thm)],[c_536,c_46])).

tff(c_755,plain,(
    k1_relset_1('#skF_2','#skF_2',k2_funct_1(k2_funct_1('#skF_3'))) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_528,c_575,c_715])).

tff(c_762,plain,(
    k1_relset_1('#skF_2','#skF_2',k2_funct_1(k2_funct_1('#skF_3'))) = k1_relat_1(k2_funct_1(k2_funct_1('#skF_3'))) ),
    inference(resolution,[status(thm)],[c_536,c_18])).

tff(c_1213,plain,(
    k1_relat_1(k2_funct_1(k2_funct_1('#skF_3'))) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_755,c_762])).

tff(c_707,plain,
    ( k2_funct_2('#skF_2',k2_funct_1(k2_funct_1('#skF_3'))) = k2_funct_1(k2_funct_1(k2_funct_1('#skF_3')))
    | ~ v3_funct_2(k2_funct_1(k2_funct_1('#skF_3')),'#skF_2','#skF_2')
    | ~ v1_funct_2(k2_funct_1(k2_funct_1('#skF_3')),'#skF_2','#skF_2')
    | ~ v1_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) ),
    inference(resolution,[status(thm)],[c_536,c_42])).

tff(c_748,plain,(
    k2_funct_2('#skF_2',k2_funct_1(k2_funct_1('#skF_3'))) = k2_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_528,c_575,c_569,c_707])).

tff(c_908,plain,
    ( k2_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) = k2_funct_2('#skF_2','#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_748])).

tff(c_914,plain,(
    k2_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_83,c_56,c_182,c_307,c_908])).

tff(c_10,plain,(
    ! [A_4] :
      ( k5_relat_1(k2_funct_1(A_4),A_4) = k6_relat_1(k2_relat_1(A_4))
      | ~ v2_funct_1(A_4)
      | ~ v1_funct_1(A_4)
      | ~ v1_relat_1(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_144,plain,(
    ! [A_51] :
      ( k5_relat_1(k2_funct_1(A_51),A_51) = k6_partfun1(k2_relat_1(A_51))
      | ~ v2_funct_1(A_51)
      | ~ v1_funct_1(A_51)
      | ~ v1_relat_1(A_51) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_10])).

tff(c_153,plain,(
    ! [A_5] :
      ( k6_partfun1(k2_relat_1(k2_funct_1(A_5))) = k5_relat_1(A_5,k2_funct_1(A_5))
      | ~ v2_funct_1(k2_funct_1(A_5))
      | ~ v1_funct_1(k2_funct_1(A_5))
      | ~ v1_relat_1(k2_funct_1(A_5))
      | ~ v2_funct_1(A_5)
      | ~ v1_funct_1(A_5)
      | ~ v1_relat_1(A_5) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_144])).

tff(c_945,plain,
    ( k6_partfun1(k2_relat_1(k2_funct_1(k2_funct_1(k2_funct_1('#skF_3'))))) = k5_relat_1(k2_funct_1(k2_funct_1('#skF_3')),k2_funct_1('#skF_3'))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1('#skF_3'))))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1('#skF_3'))))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1('#skF_3'))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1('#skF_3')))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1('#skF_3')))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1('#skF_3'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_914,c_153])).

tff(c_979,plain,(
    k5_relat_1(k2_funct_1(k2_funct_1('#skF_3')),k2_funct_1('#skF_3')) = k6_partfun1(k2_relat_1(k2_funct_1('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_624,c_528,c_761,c_502,c_914,c_309,c_914,c_500,c_914,c_914,c_945])).

tff(c_156,plain,(
    ! [A_52] :
      ( k5_relat_1(A_52,k2_funct_1(A_52)) = k6_partfun1(k1_relat_1(A_52))
      | ~ v2_funct_1(A_52)
      | ~ v1_funct_1(A_52)
      | ~ v1_relat_1(A_52) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_12])).

tff(c_165,plain,(
    ! [A_5] :
      ( k6_partfun1(k1_relat_1(k2_funct_1(A_5))) = k5_relat_1(k2_funct_1(A_5),A_5)
      | ~ v2_funct_1(k2_funct_1(A_5))
      | ~ v1_funct_1(k2_funct_1(A_5))
      | ~ v1_relat_1(k2_funct_1(A_5))
      | ~ v2_funct_1(A_5)
      | ~ v1_funct_1(A_5)
      | ~ v1_relat_1(A_5) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_156])).

tff(c_1262,plain,
    ( k6_partfun1(k1_relat_1(k2_funct_1(k2_funct_1('#skF_3')))) = k6_partfun1(k2_relat_1(k2_funct_1('#skF_3')))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1('#skF_3')))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1('#skF_3')))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1('#skF_3')))
    | ~ v2_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_979,c_165])).

tff(c_1278,plain,(
    k6_partfun1(k2_relat_1(k2_funct_1('#skF_3'))) = k6_partfun1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_502,c_309,c_500,c_624,c_528,c_761,c_1213,c_1262])).

tff(c_1298,plain,
    ( k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_partfun1('#skF_2')
    | ~ v2_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1278,c_153])).

tff(c_1344,plain,(
    k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_partfun1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_83,c_56,c_182,c_502,c_309,c_500,c_1298])).

tff(c_503,plain,(
    ! [C_99,A_98,E_100,B_103,F_101,D_102] :
      ( k1_partfun1(A_98,B_103,C_99,D_102,E_100,F_101) = k5_relat_1(E_100,F_101)
      | ~ m1_subset_1(F_101,k1_zfmisc_1(k2_zfmisc_1(C_99,D_102)))
      | ~ v1_funct_1(F_101)
      | ~ m1_subset_1(E_100,k1_zfmisc_1(k2_zfmisc_1(A_98,B_103)))
      | ~ v1_funct_1(E_100) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_505,plain,(
    ! [A_98,B_103,E_100] :
      ( k1_partfun1(A_98,B_103,'#skF_2','#skF_2',E_100,k2_funct_1('#skF_3')) = k5_relat_1(E_100,k2_funct_1('#skF_3'))
      | ~ v1_funct_1(k2_funct_1('#skF_3'))
      | ~ m1_subset_1(E_100,k1_zfmisc_1(k2_zfmisc_1(A_98,B_103)))
      | ~ v1_funct_1(E_100) ) ),
    inference(resolution,[status(thm)],[c_451,c_503])).

tff(c_1930,plain,(
    ! [A_135,B_136,E_137] :
      ( k1_partfun1(A_135,B_136,'#skF_2','#skF_2',E_137,k2_funct_1('#skF_3')) = k5_relat_1(E_137,k2_funct_1('#skF_3'))
      | ~ m1_subset_1(E_137,k1_zfmisc_1(k2_zfmisc_1(A_135,B_136)))
      | ~ v1_funct_1(E_137) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_309,c_505])).

tff(c_1960,plain,
    ( k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2','#skF_3',k2_funct_1('#skF_3')) = k5_relat_1('#skF_3',k2_funct_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_50,c_1930])).

tff(c_1980,plain,(
    k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2','#skF_3',k2_funct_1('#skF_3')) = k6_partfun1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_1344,c_1960])).

tff(c_48,plain,
    ( ~ r2_relset_1('#skF_2','#skF_2',k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2',k2_funct_2('#skF_2','#skF_3'),'#skF_3'),k6_partfun1('#skF_2'))
    | ~ r2_relset_1('#skF_2','#skF_2',k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2','#skF_3',k2_funct_2('#skF_2','#skF_3')),k6_partfun1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_85,plain,(
    ~ r2_relset_1('#skF_2','#skF_2',k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2','#skF_3',k2_funct_2('#skF_2','#skF_3')),k6_partfun1('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_48])).

tff(c_310,plain,(
    ~ r2_relset_1('#skF_2','#skF_2',k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2','#skF_3',k2_funct_1('#skF_3')),k6_partfun1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_307,c_85])).

tff(c_1982,plain,(
    ~ r2_relset_1('#skF_2','#skF_2',k6_partfun1('#skF_2'),k6_partfun1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1980,c_310])).

tff(c_1985,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_272,c_1982])).

tff(c_1986,plain,(
    ~ r2_relset_1('#skF_2','#skF_2',k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2',k2_funct_2('#skF_2','#skF_3'),'#skF_3'),k6_partfun1('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_2213,plain,(
    ~ r2_relset_1('#skF_2','#skF_2',k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2',k2_funct_1('#skF_3'),'#skF_3'),k6_partfun1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2209,c_1986])).

tff(c_3319,plain,(
    ~ r2_relset_1('#skF_2','#skF_2',k6_partfun1('#skF_2'),k6_partfun1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3286,c_2213])).

tff(c_3322,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2158,c_3319])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n008.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 18:14:45 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.42/2.03  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.42/2.05  
% 5.42/2.05  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.42/2.05  %$ r2_relset_1 > v3_funct_2 > v1_funct_2 > v2_funct_2 > v1_partfun1 > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > k2_funct_2 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > #skF_1 > #skF_2 > #skF_3
% 5.42/2.05  
% 5.42/2.05  %Foreground sorts:
% 5.42/2.05  
% 5.42/2.05  
% 5.42/2.05  %Background operators:
% 5.42/2.05  
% 5.42/2.05  
% 5.42/2.05  %Foreground operators:
% 5.42/2.05  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 5.42/2.05  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 5.42/2.05  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 5.42/2.05  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.42/2.05  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 5.42/2.05  tff('#skF_1', type, '#skF_1': $i > $i).
% 5.42/2.05  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 5.42/2.05  tff(k2_funct_2, type, k2_funct_2: ($i * $i) > $i).
% 5.42/2.05  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 5.42/2.05  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 5.42/2.05  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 5.42/2.05  tff('#skF_2', type, '#skF_2': $i).
% 5.42/2.05  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 5.42/2.05  tff('#skF_3', type, '#skF_3': $i).
% 5.42/2.05  tff(v2_funct_2, type, v2_funct_2: ($i * $i) > $o).
% 5.42/2.05  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 5.42/2.05  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.42/2.05  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 5.42/2.05  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.42/2.05  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.42/2.05  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 5.42/2.05  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 5.42/2.05  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.42/2.05  tff(v3_funct_2, type, v3_funct_2: ($i * $i * $i) > $o).
% 5.42/2.05  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 5.42/2.05  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.42/2.05  
% 5.42/2.07  tff(f_104, axiom, (![A]: (v1_partfun1(k6_partfun1(A), A) & m1_subset_1(k6_partfun1(A), k1_zfmisc_1(k2_zfmisc_1(A, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_partfun1)).
% 5.42/2.07  tff(f_72, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => r2_relset_1(A, B, C, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', reflexivity_r2_relset_1)).
% 5.42/2.07  tff(f_147, negated_conjecture, ~(![A, B]: ((((v1_funct_1(B) & v1_funct_2(B, A, A)) & v3_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (r2_relset_1(A, A, k1_partfun1(A, A, A, A, B, k2_funct_2(A, B)), k6_partfun1(A)) & r2_relset_1(A, A, k1_partfun1(A, A, A, A, k2_funct_2(A, B), B), k6_partfun1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t88_funct_2)).
% 5.42/2.07  tff(f_124, axiom, (![A, B]: ((((v1_funct_1(B) & v1_funct_2(B, A, A)) & v3_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (k2_funct_2(A, B) = k2_funct_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_funct_2)).
% 5.42/2.07  tff(f_100, axiom, (![A, B]: ((((v1_funct_1(B) & v1_funct_2(B, A, A)) & v3_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (((v1_funct_1(k2_funct_2(A, B)) & v1_funct_2(k2_funct_2(A, B), A, A)) & v3_funct_2(k2_funct_2(A, B), A, A)) & m1_subset_1(k2_funct_2(A, B), k1_zfmisc_1(k2_zfmisc_1(A, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_funct_2)).
% 5.42/2.07  tff(f_62, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 5.42/2.07  tff(f_84, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v3_funct_2(C, A, B)) => ((v1_funct_1(C) & v2_funct_1(C)) & v2_funct_2(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_funct_2)).
% 5.42/2.07  tff(f_134, axiom, (![A, B]: (((v1_funct_1(B) & v1_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (k1_relset_1(A, A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t67_funct_2)).
% 5.42/2.07  tff(f_66, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 5.42/2.07  tff(f_58, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => (k2_funct_1(k2_funct_1(A)) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_funct_1)).
% 5.42/2.07  tff(f_126, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 5.42/2.07  tff(f_50, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k5_relat_1(A, k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))) & (k5_relat_1(k2_funct_1(A), A) = k6_relat_1(k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t61_funct_1)).
% 5.42/2.07  tff(f_114, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 5.42/2.07  tff(c_38, plain, (![A_21]: (m1_subset_1(k6_partfun1(A_21), k1_zfmisc_1(k2_zfmisc_1(A_21, A_21))))), inference(cnfTransformation, [status(thm)], [f_104])).
% 5.42/2.07  tff(c_2113, plain, (![A_161, B_162, C_163, D_164]: (r2_relset_1(A_161, B_162, C_163, C_163) | ~m1_subset_1(D_164, k1_zfmisc_1(k2_zfmisc_1(A_161, B_162))) | ~m1_subset_1(C_163, k1_zfmisc_1(k2_zfmisc_1(A_161, B_162))))), inference(cnfTransformation, [status(thm)], [f_72])).
% 5.42/2.07  tff(c_2150, plain, (![A_167, C_168]: (r2_relset_1(A_167, A_167, C_168, C_168) | ~m1_subset_1(C_168, k1_zfmisc_1(k2_zfmisc_1(A_167, A_167))))), inference(resolution, [status(thm)], [c_38, c_2113])).
% 5.42/2.07  tff(c_2158, plain, (![A_21]: (r2_relset_1(A_21, A_21, k6_partfun1(A_21), k6_partfun1(A_21)))), inference(resolution, [status(thm)], [c_38, c_2150])).
% 5.42/2.07  tff(c_56, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_147])).
% 5.42/2.07  tff(c_54, plain, (v1_funct_2('#skF_3', '#skF_2', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_147])).
% 5.42/2.07  tff(c_52, plain, (v3_funct_2('#skF_3', '#skF_2', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_147])).
% 5.42/2.07  tff(c_50, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_147])).
% 5.42/2.07  tff(c_2195, plain, (![A_179, B_180]: (k2_funct_2(A_179, B_180)=k2_funct_1(B_180) | ~m1_subset_1(B_180, k1_zfmisc_1(k2_zfmisc_1(A_179, A_179))) | ~v3_funct_2(B_180, A_179, A_179) | ~v1_funct_2(B_180, A_179, A_179) | ~v1_funct_1(B_180))), inference(cnfTransformation, [status(thm)], [f_124])).
% 5.42/2.07  tff(c_2201, plain, (k2_funct_2('#skF_2', '#skF_3')=k2_funct_1('#skF_3') | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_50, c_2195])).
% 5.42/2.07  tff(c_2209, plain, (k2_funct_2('#skF_2', '#skF_3')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_52, c_2201])).
% 5.42/2.07  tff(c_2177, plain, (![A_176, B_177]: (v1_funct_1(k2_funct_2(A_176, B_177)) | ~m1_subset_1(B_177, k1_zfmisc_1(k2_zfmisc_1(A_176, A_176))) | ~v3_funct_2(B_177, A_176, A_176) | ~v1_funct_2(B_177, A_176, A_176) | ~v1_funct_1(B_177))), inference(cnfTransformation, [status(thm)], [f_100])).
% 5.42/2.07  tff(c_2183, plain, (v1_funct_1(k2_funct_2('#skF_2', '#skF_3')) | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_50, c_2177])).
% 5.42/2.07  tff(c_2191, plain, (v1_funct_1(k2_funct_2('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_52, c_2183])).
% 5.42/2.07  tff(c_2211, plain, (v1_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_2209, c_2191])).
% 5.42/2.07  tff(c_71, plain, (![C_37, A_38, B_39]: (v1_relat_1(C_37) | ~m1_subset_1(C_37, k1_zfmisc_1(k2_zfmisc_1(A_38, B_39))))), inference(cnfTransformation, [status(thm)], [f_62])).
% 5.42/2.07  tff(c_83, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_50, c_71])).
% 5.42/2.07  tff(c_2070, plain, (![C_151, A_152, B_153]: (v2_funct_1(C_151) | ~v3_funct_2(C_151, A_152, B_153) | ~v1_funct_1(C_151) | ~m1_subset_1(C_151, k1_zfmisc_1(k2_zfmisc_1(A_152, B_153))))), inference(cnfTransformation, [status(thm)], [f_84])).
% 5.42/2.07  tff(c_2076, plain, (v2_funct_1('#skF_3') | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_50, c_2070])).
% 5.42/2.07  tff(c_2084, plain, (v2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_52, c_2076])).
% 5.42/2.07  tff(c_2313, plain, (![A_194, B_195]: (m1_subset_1(k2_funct_2(A_194, B_195), k1_zfmisc_1(k2_zfmisc_1(A_194, A_194))) | ~m1_subset_1(B_195, k1_zfmisc_1(k2_zfmisc_1(A_194, A_194))) | ~v3_funct_2(B_195, A_194, A_194) | ~v1_funct_2(B_195, A_194, A_194) | ~v1_funct_1(B_195))), inference(cnfTransformation, [status(thm)], [f_100])).
% 5.42/2.07  tff(c_2343, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'))) | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_2209, c_2313])).
% 5.42/2.07  tff(c_2355, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_52, c_50, c_2343])).
% 5.42/2.07  tff(c_16, plain, (![C_8, A_6, B_7]: (v1_relat_1(C_8) | ~m1_subset_1(C_8, k1_zfmisc_1(k2_zfmisc_1(A_6, B_7))))), inference(cnfTransformation, [status(thm)], [f_62])).
% 5.42/2.07  tff(c_2406, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_2355, c_16])).
% 5.42/2.07  tff(c_2234, plain, (![A_187, B_188]: (v3_funct_2(k2_funct_2(A_187, B_188), A_187, A_187) | ~m1_subset_1(B_188, k1_zfmisc_1(k2_zfmisc_1(A_187, A_187))) | ~v3_funct_2(B_188, A_187, A_187) | ~v1_funct_2(B_188, A_187, A_187) | ~v1_funct_1(B_188))), inference(cnfTransformation, [status(thm)], [f_100])).
% 5.42/2.07  tff(c_2238, plain, (v3_funct_2(k2_funct_2('#skF_2', '#skF_3'), '#skF_2', '#skF_2') | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_50, c_2234])).
% 5.42/2.07  tff(c_2245, plain, (v3_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_52, c_2209, c_2238])).
% 5.42/2.07  tff(c_24, plain, (![C_18, A_16, B_17]: (v2_funct_1(C_18) | ~v3_funct_2(C_18, A_16, B_17) | ~v1_funct_1(C_18) | ~m1_subset_1(C_18, k1_zfmisc_1(k2_zfmisc_1(A_16, B_17))))), inference(cnfTransformation, [status(thm)], [f_84])).
% 5.42/2.07  tff(c_2376, plain, (v2_funct_1(k2_funct_1('#skF_3')) | ~v3_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_2') | ~v1_funct_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_2355, c_24])).
% 5.42/2.07  tff(c_2404, plain, (v2_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_2211, c_2245, c_2376])).
% 5.42/2.07  tff(c_2219, plain, (![A_183, B_184]: (v1_funct_2(k2_funct_2(A_183, B_184), A_183, A_183) | ~m1_subset_1(B_184, k1_zfmisc_1(k2_zfmisc_1(A_183, A_183))) | ~v3_funct_2(B_184, A_183, A_183) | ~v1_funct_2(B_184, A_183, A_183) | ~v1_funct_1(B_184))), inference(cnfTransformation, [status(thm)], [f_100])).
% 5.42/2.07  tff(c_2223, plain, (v1_funct_2(k2_funct_2('#skF_2', '#skF_3'), '#skF_2', '#skF_2') | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_50, c_2219])).
% 5.42/2.07  tff(c_2230, plain, (v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_52, c_2209, c_2223])).
% 5.42/2.07  tff(c_46, plain, (![A_31, B_32]: (k1_relset_1(A_31, A_31, B_32)=A_31 | ~m1_subset_1(B_32, k1_zfmisc_1(k2_zfmisc_1(A_31, A_31))) | ~v1_funct_2(B_32, A_31, A_31) | ~v1_funct_1(B_32))), inference(cnfTransformation, [status(thm)], [f_134])).
% 5.42/2.07  tff(c_2370, plain, (k1_relset_1('#skF_2', '#skF_2', k2_funct_1('#skF_3'))='#skF_2' | ~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_2') | ~v1_funct_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_2355, c_46])).
% 5.42/2.07  tff(c_2398, plain, (k1_relset_1('#skF_2', '#skF_2', k2_funct_1('#skF_3'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_2211, c_2230, c_2370])).
% 5.42/2.07  tff(c_18, plain, (![A_9, B_10, C_11]: (k1_relset_1(A_9, B_10, C_11)=k1_relat_1(C_11) | ~m1_subset_1(C_11, k1_zfmisc_1(k2_zfmisc_1(A_9, B_10))))), inference(cnfTransformation, [status(thm)], [f_66])).
% 5.42/2.07  tff(c_2405, plain, (k1_relset_1('#skF_2', '#skF_2', k2_funct_1('#skF_3'))=k1_relat_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_2355, c_18])).
% 5.42/2.07  tff(c_2459, plain, (k1_relat_1(k2_funct_1('#skF_3'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_2398, c_2405])).
% 5.42/2.07  tff(c_14, plain, (![A_5]: (k2_funct_1(k2_funct_1(A_5))=A_5 | ~v2_funct_1(A_5) | ~v1_funct_1(A_5) | ~v1_relat_1(A_5))), inference(cnfTransformation, [status(thm)], [f_58])).
% 5.42/2.07  tff(c_44, plain, (![A_30]: (k6_relat_1(A_30)=k6_partfun1(A_30))), inference(cnfTransformation, [status(thm)], [f_126])).
% 5.42/2.07  tff(c_12, plain, (![A_4]: (k5_relat_1(A_4, k2_funct_1(A_4))=k6_relat_1(k1_relat_1(A_4)) | ~v2_funct_1(A_4) | ~v1_funct_1(A_4) | ~v1_relat_1(A_4))), inference(cnfTransformation, [status(thm)], [f_50])).
% 5.42/2.07  tff(c_2058, plain, (![A_150]: (k5_relat_1(A_150, k2_funct_1(A_150))=k6_partfun1(k1_relat_1(A_150)) | ~v2_funct_1(A_150) | ~v1_funct_1(A_150) | ~v1_relat_1(A_150))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_12])).
% 5.42/2.07  tff(c_2791, plain, (![A_212]: (k6_partfun1(k1_relat_1(k2_funct_1(A_212)))=k5_relat_1(k2_funct_1(A_212), A_212) | ~v2_funct_1(k2_funct_1(A_212)) | ~v1_funct_1(k2_funct_1(A_212)) | ~v1_relat_1(k2_funct_1(A_212)) | ~v2_funct_1(A_212) | ~v1_funct_1(A_212) | ~v1_relat_1(A_212))), inference(superposition, [status(thm), theory('equality')], [c_14, c_2058])).
% 5.42/2.07  tff(c_2853, plain, (k5_relat_1(k2_funct_1('#skF_3'), '#skF_3')=k6_partfun1('#skF_2') | ~v2_funct_1(k2_funct_1('#skF_3')) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_2459, c_2791])).
% 5.42/2.07  tff(c_2867, plain, (k5_relat_1(k2_funct_1('#skF_3'), '#skF_3')=k6_partfun1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_83, c_56, c_2084, c_2406, c_2211, c_2404, c_2853])).
% 5.42/2.07  tff(c_28, plain, (![A_19, B_20]: (m1_subset_1(k2_funct_2(A_19, B_20), k1_zfmisc_1(k2_zfmisc_1(A_19, A_19))) | ~m1_subset_1(B_20, k1_zfmisc_1(k2_zfmisc_1(A_19, A_19))) | ~v3_funct_2(B_20, A_19, A_19) | ~v1_funct_2(B_20, A_19, A_19) | ~v1_funct_1(B_20))), inference(cnfTransformation, [status(thm)], [f_100])).
% 5.42/2.07  tff(c_2426, plain, (![F_199, E_198, C_197, D_200, A_196, B_201]: (k1_partfun1(A_196, B_201, C_197, D_200, E_198, F_199)=k5_relat_1(E_198, F_199) | ~m1_subset_1(F_199, k1_zfmisc_1(k2_zfmisc_1(C_197, D_200))) | ~v1_funct_1(F_199) | ~m1_subset_1(E_198, k1_zfmisc_1(k2_zfmisc_1(A_196, B_201))) | ~v1_funct_1(E_198))), inference(cnfTransformation, [status(thm)], [f_114])).
% 5.42/2.07  tff(c_2434, plain, (![A_196, B_201, E_198]: (k1_partfun1(A_196, B_201, '#skF_2', '#skF_2', E_198, '#skF_3')=k5_relat_1(E_198, '#skF_3') | ~v1_funct_1('#skF_3') | ~m1_subset_1(E_198, k1_zfmisc_1(k2_zfmisc_1(A_196, B_201))) | ~v1_funct_1(E_198))), inference(resolution, [status(thm)], [c_50, c_2426])).
% 5.42/2.07  tff(c_2464, plain, (![A_202, B_203, E_204]: (k1_partfun1(A_202, B_203, '#skF_2', '#skF_2', E_204, '#skF_3')=k5_relat_1(E_204, '#skF_3') | ~m1_subset_1(E_204, k1_zfmisc_1(k2_zfmisc_1(A_202, B_203))) | ~v1_funct_1(E_204))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_2434])).
% 5.42/2.07  tff(c_3259, plain, (![A_219, B_220]: (k1_partfun1(A_219, A_219, '#skF_2', '#skF_2', k2_funct_2(A_219, B_220), '#skF_3')=k5_relat_1(k2_funct_2(A_219, B_220), '#skF_3') | ~v1_funct_1(k2_funct_2(A_219, B_220)) | ~m1_subset_1(B_220, k1_zfmisc_1(k2_zfmisc_1(A_219, A_219))) | ~v3_funct_2(B_220, A_219, A_219) | ~v1_funct_2(B_220, A_219, A_219) | ~v1_funct_1(B_220))), inference(resolution, [status(thm)], [c_28, c_2464])).
% 5.42/2.07  tff(c_3271, plain, (k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', k2_funct_2('#skF_2', '#skF_3'), '#skF_3')=k5_relat_1(k2_funct_2('#skF_2', '#skF_3'), '#skF_3') | ~v1_funct_1(k2_funct_2('#skF_2', '#skF_3')) | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_50, c_3259])).
% 5.42/2.07  tff(c_3286, plain, (k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', k2_funct_1('#skF_3'), '#skF_3')=k6_partfun1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_52, c_2211, c_2209, c_2867, c_2209, c_2209, c_3271])).
% 5.42/2.07  tff(c_238, plain, (![A_66, B_67, C_68, D_69]: (r2_relset_1(A_66, B_67, C_68, C_68) | ~m1_subset_1(D_69, k1_zfmisc_1(k2_zfmisc_1(A_66, B_67))) | ~m1_subset_1(C_68, k1_zfmisc_1(k2_zfmisc_1(A_66, B_67))))), inference(cnfTransformation, [status(thm)], [f_72])).
% 5.42/2.07  tff(c_264, plain, (![A_72, C_73]: (r2_relset_1(A_72, A_72, C_73, C_73) | ~m1_subset_1(C_73, k1_zfmisc_1(k2_zfmisc_1(A_72, A_72))))), inference(resolution, [status(thm)], [c_38, c_238])).
% 5.42/2.07  tff(c_272, plain, (![A_21]: (r2_relset_1(A_21, A_21, k6_partfun1(A_21), k6_partfun1(A_21)))), inference(resolution, [status(thm)], [c_38, c_264])).
% 5.42/2.07  tff(c_168, plain, (![C_53, A_54, B_55]: (v2_funct_1(C_53) | ~v3_funct_2(C_53, A_54, B_55) | ~v1_funct_1(C_53) | ~m1_subset_1(C_53, k1_zfmisc_1(k2_zfmisc_1(A_54, B_55))))), inference(cnfTransformation, [status(thm)], [f_84])).
% 5.42/2.07  tff(c_174, plain, (v2_funct_1('#skF_3') | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_50, c_168])).
% 5.42/2.07  tff(c_182, plain, (v2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_52, c_174])).
% 5.42/2.07  tff(c_293, plain, (![A_82, B_83]: (k2_funct_2(A_82, B_83)=k2_funct_1(B_83) | ~m1_subset_1(B_83, k1_zfmisc_1(k2_zfmisc_1(A_82, A_82))) | ~v3_funct_2(B_83, A_82, A_82) | ~v1_funct_2(B_83, A_82, A_82) | ~v1_funct_1(B_83))), inference(cnfTransformation, [status(thm)], [f_124])).
% 5.42/2.07  tff(c_299, plain, (k2_funct_2('#skF_2', '#skF_3')=k2_funct_1('#skF_3') | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_50, c_293])).
% 5.42/2.07  tff(c_307, plain, (k2_funct_2('#skF_2', '#skF_3')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_52, c_299])).
% 5.42/2.07  tff(c_409, plain, (![A_96, B_97]: (m1_subset_1(k2_funct_2(A_96, B_97), k1_zfmisc_1(k2_zfmisc_1(A_96, A_96))) | ~m1_subset_1(B_97, k1_zfmisc_1(k2_zfmisc_1(A_96, A_96))) | ~v3_funct_2(B_97, A_96, A_96) | ~v1_funct_2(B_97, A_96, A_96) | ~v1_funct_1(B_97))), inference(cnfTransformation, [status(thm)], [f_100])).
% 5.42/2.07  tff(c_439, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'))) | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_307, c_409])).
% 5.42/2.07  tff(c_451, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_52, c_50, c_439])).
% 5.42/2.07  tff(c_502, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_451, c_16])).
% 5.42/2.07  tff(c_248, plain, (![A_70, B_71]: (v1_funct_1(k2_funct_2(A_70, B_71)) | ~m1_subset_1(B_71, k1_zfmisc_1(k2_zfmisc_1(A_70, A_70))) | ~v3_funct_2(B_71, A_70, A_70) | ~v1_funct_2(B_71, A_70, A_70) | ~v1_funct_1(B_71))), inference(cnfTransformation, [status(thm)], [f_100])).
% 5.42/2.07  tff(c_254, plain, (v1_funct_1(k2_funct_2('#skF_2', '#skF_3')) | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_50, c_248])).
% 5.42/2.07  tff(c_262, plain, (v1_funct_1(k2_funct_2('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_52, c_254])).
% 5.42/2.07  tff(c_309, plain, (v1_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_307, c_262])).
% 5.42/2.07  tff(c_315, plain, (![A_84, B_85]: (v3_funct_2(k2_funct_2(A_84, B_85), A_84, A_84) | ~m1_subset_1(B_85, k1_zfmisc_1(k2_zfmisc_1(A_84, A_84))) | ~v3_funct_2(B_85, A_84, A_84) | ~v1_funct_2(B_85, A_84, A_84) | ~v1_funct_1(B_85))), inference(cnfTransformation, [status(thm)], [f_100])).
% 5.42/2.07  tff(c_319, plain, (v3_funct_2(k2_funct_2('#skF_2', '#skF_3'), '#skF_2', '#skF_2') | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_50, c_315])).
% 5.42/2.07  tff(c_326, plain, (v3_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_52, c_307, c_319])).
% 5.42/2.07  tff(c_472, plain, (v2_funct_1(k2_funct_1('#skF_3')) | ~v3_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_2') | ~v1_funct_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_451, c_24])).
% 5.42/2.07  tff(c_500, plain, (v2_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_309, c_326, c_472])).
% 5.42/2.07  tff(c_332, plain, (![A_92, B_93]: (v1_funct_2(k2_funct_2(A_92, B_93), A_92, A_92) | ~m1_subset_1(B_93, k1_zfmisc_1(k2_zfmisc_1(A_92, A_92))) | ~v3_funct_2(B_93, A_92, A_92) | ~v1_funct_2(B_93, A_92, A_92) | ~v1_funct_1(B_93))), inference(cnfTransformation, [status(thm)], [f_100])).
% 5.42/2.07  tff(c_336, plain, (v1_funct_2(k2_funct_2('#skF_2', '#skF_3'), '#skF_2', '#skF_2') | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_50, c_332])).
% 5.42/2.07  tff(c_343, plain, (v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_52, c_307, c_336])).
% 5.42/2.07  tff(c_42, plain, (![A_28, B_29]: (k2_funct_2(A_28, B_29)=k2_funct_1(B_29) | ~m1_subset_1(B_29, k1_zfmisc_1(k2_zfmisc_1(A_28, A_28))) | ~v3_funct_2(B_29, A_28, A_28) | ~v1_funct_2(B_29, A_28, A_28) | ~v1_funct_1(B_29))), inference(cnfTransformation, [status(thm)], [f_124])).
% 5.42/2.07  tff(c_458, plain, (k2_funct_2('#skF_2', k2_funct_1('#skF_3'))=k2_funct_1(k2_funct_1('#skF_3')) | ~v3_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_2') | ~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_2') | ~v1_funct_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_451, c_42])).
% 5.42/2.07  tff(c_487, plain, (k2_funct_2('#skF_2', k2_funct_1('#skF_3'))=k2_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_309, c_343, c_326, c_458])).
% 5.42/2.07  tff(c_605, plain, (![A_107, B_108]: (v1_relat_1(k2_funct_2(A_107, B_108)) | ~m1_subset_1(B_108, k1_zfmisc_1(k2_zfmisc_1(A_107, A_107))) | ~v3_funct_2(B_108, A_107, A_107) | ~v1_funct_2(B_108, A_107, A_107) | ~v1_funct_1(B_108))), inference(resolution, [status(thm)], [c_409, c_16])).
% 5.42/2.07  tff(c_608, plain, (v1_relat_1(k2_funct_2('#skF_2', k2_funct_1('#skF_3'))) | ~v3_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_2') | ~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_2') | ~v1_funct_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_451, c_605])).
% 5.42/2.07  tff(c_624, plain, (v1_relat_1(k2_funct_1(k2_funct_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_309, c_343, c_326, c_487, c_608])).
% 5.42/2.07  tff(c_34, plain, (![A_19, B_20]: (v1_funct_1(k2_funct_2(A_19, B_20)) | ~m1_subset_1(B_20, k1_zfmisc_1(k2_zfmisc_1(A_19, A_19))) | ~v3_funct_2(B_20, A_19, A_19) | ~v1_funct_2(B_20, A_19, A_19) | ~v1_funct_1(B_20))), inference(cnfTransformation, [status(thm)], [f_100])).
% 5.42/2.07  tff(c_463, plain, (v1_funct_1(k2_funct_2('#skF_2', k2_funct_1('#skF_3'))) | ~v3_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_2') | ~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_2') | ~v1_funct_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_451, c_34])).
% 5.42/2.07  tff(c_491, plain, (v1_funct_1(k2_funct_2('#skF_2', k2_funct_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_309, c_343, c_326, c_463])).
% 5.42/2.07  tff(c_528, plain, (v1_funct_1(k2_funct_1(k2_funct_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_487, c_491])).
% 5.42/2.07  tff(c_30, plain, (![A_19, B_20]: (v3_funct_2(k2_funct_2(A_19, B_20), A_19, A_19) | ~m1_subset_1(B_20, k1_zfmisc_1(k2_zfmisc_1(A_19, A_19))) | ~v3_funct_2(B_20, A_19, A_19) | ~v1_funct_2(B_20, A_19, A_19) | ~v1_funct_1(B_20))), inference(cnfTransformation, [status(thm)], [f_100])).
% 5.42/2.07  tff(c_455, plain, (v3_funct_2(k2_funct_2('#skF_2', k2_funct_1('#skF_3')), '#skF_2', '#skF_2') | ~v3_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_2') | ~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_2') | ~v1_funct_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_451, c_30])).
% 5.42/2.07  tff(c_484, plain, (v3_funct_2(k2_funct_2('#skF_2', k2_funct_1('#skF_3')), '#skF_2', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_309, c_343, c_326, c_455])).
% 5.42/2.07  tff(c_569, plain, (v3_funct_2(k2_funct_1(k2_funct_1('#skF_3')), '#skF_2', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_487, c_484])).
% 5.42/2.07  tff(c_532, plain, (m1_subset_1(k2_funct_1(k2_funct_1('#skF_3')), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'))) | ~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'))) | ~v3_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_2') | ~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_2') | ~v1_funct_1(k2_funct_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_487, c_28])).
% 5.42/2.07  tff(c_536, plain, (m1_subset_1(k2_funct_1(k2_funct_1('#skF_3')), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_309, c_343, c_326, c_451, c_532])).
% 5.42/2.07  tff(c_721, plain, (v2_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) | ~v3_funct_2(k2_funct_1(k2_funct_1('#skF_3')), '#skF_2', '#skF_2') | ~v1_funct_1(k2_funct_1(k2_funct_1('#skF_3')))), inference(resolution, [status(thm)], [c_536, c_24])).
% 5.42/2.07  tff(c_761, plain, (v2_funct_1(k2_funct_1(k2_funct_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_528, c_569, c_721])).
% 5.42/2.08  tff(c_32, plain, (![A_19, B_20]: (v1_funct_2(k2_funct_2(A_19, B_20), A_19, A_19) | ~m1_subset_1(B_20, k1_zfmisc_1(k2_zfmisc_1(A_19, A_19))) | ~v3_funct_2(B_20, A_19, A_19) | ~v1_funct_2(B_20, A_19, A_19) | ~v1_funct_1(B_20))), inference(cnfTransformation, [status(thm)], [f_100])).
% 5.42/2.08  tff(c_453, plain, (v1_funct_2(k2_funct_2('#skF_2', k2_funct_1('#skF_3')), '#skF_2', '#skF_2') | ~v3_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_2') | ~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_2') | ~v1_funct_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_451, c_32])).
% 5.42/2.08  tff(c_481, plain, (v1_funct_2(k2_funct_2('#skF_2', k2_funct_1('#skF_3')), '#skF_2', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_309, c_343, c_326, c_453])).
% 5.42/2.08  tff(c_575, plain, (v1_funct_2(k2_funct_1(k2_funct_1('#skF_3')), '#skF_2', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_487, c_481])).
% 5.42/2.08  tff(c_715, plain, (k1_relset_1('#skF_2', '#skF_2', k2_funct_1(k2_funct_1('#skF_3')))='#skF_2' | ~v1_funct_2(k2_funct_1(k2_funct_1('#skF_3')), '#skF_2', '#skF_2') | ~v1_funct_1(k2_funct_1(k2_funct_1('#skF_3')))), inference(resolution, [status(thm)], [c_536, c_46])).
% 5.42/2.08  tff(c_755, plain, (k1_relset_1('#skF_2', '#skF_2', k2_funct_1(k2_funct_1('#skF_3')))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_528, c_575, c_715])).
% 5.42/2.08  tff(c_762, plain, (k1_relset_1('#skF_2', '#skF_2', k2_funct_1(k2_funct_1('#skF_3')))=k1_relat_1(k2_funct_1(k2_funct_1('#skF_3')))), inference(resolution, [status(thm)], [c_536, c_18])).
% 5.42/2.08  tff(c_1213, plain, (k1_relat_1(k2_funct_1(k2_funct_1('#skF_3')))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_755, c_762])).
% 5.42/2.08  tff(c_707, plain, (k2_funct_2('#skF_2', k2_funct_1(k2_funct_1('#skF_3')))=k2_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) | ~v3_funct_2(k2_funct_1(k2_funct_1('#skF_3')), '#skF_2', '#skF_2') | ~v1_funct_2(k2_funct_1(k2_funct_1('#skF_3')), '#skF_2', '#skF_2') | ~v1_funct_1(k2_funct_1(k2_funct_1('#skF_3')))), inference(resolution, [status(thm)], [c_536, c_42])).
% 5.42/2.08  tff(c_748, plain, (k2_funct_2('#skF_2', k2_funct_1(k2_funct_1('#skF_3')))=k2_funct_1(k2_funct_1(k2_funct_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_528, c_575, c_569, c_707])).
% 5.42/2.08  tff(c_908, plain, (k2_funct_1(k2_funct_1(k2_funct_1('#skF_3')))=k2_funct_2('#skF_2', '#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_14, c_748])).
% 5.42/2.08  tff(c_914, plain, (k2_funct_1(k2_funct_1(k2_funct_1('#skF_3')))=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_83, c_56, c_182, c_307, c_908])).
% 5.42/2.08  tff(c_10, plain, (![A_4]: (k5_relat_1(k2_funct_1(A_4), A_4)=k6_relat_1(k2_relat_1(A_4)) | ~v2_funct_1(A_4) | ~v1_funct_1(A_4) | ~v1_relat_1(A_4))), inference(cnfTransformation, [status(thm)], [f_50])).
% 5.42/2.08  tff(c_144, plain, (![A_51]: (k5_relat_1(k2_funct_1(A_51), A_51)=k6_partfun1(k2_relat_1(A_51)) | ~v2_funct_1(A_51) | ~v1_funct_1(A_51) | ~v1_relat_1(A_51))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_10])).
% 5.42/2.08  tff(c_153, plain, (![A_5]: (k6_partfun1(k2_relat_1(k2_funct_1(A_5)))=k5_relat_1(A_5, k2_funct_1(A_5)) | ~v2_funct_1(k2_funct_1(A_5)) | ~v1_funct_1(k2_funct_1(A_5)) | ~v1_relat_1(k2_funct_1(A_5)) | ~v2_funct_1(A_5) | ~v1_funct_1(A_5) | ~v1_relat_1(A_5))), inference(superposition, [status(thm), theory('equality')], [c_14, c_144])).
% 5.42/2.08  tff(c_945, plain, (k6_partfun1(k2_relat_1(k2_funct_1(k2_funct_1(k2_funct_1('#skF_3')))))=k5_relat_1(k2_funct_1(k2_funct_1('#skF_3')), k2_funct_1('#skF_3')) | ~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1('#skF_3')))) | ~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1('#skF_3')))) | ~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1('#skF_3')))) | ~v2_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) | ~v1_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) | ~v1_relat_1(k2_funct_1(k2_funct_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_914, c_153])).
% 5.42/2.08  tff(c_979, plain, (k5_relat_1(k2_funct_1(k2_funct_1('#skF_3')), k2_funct_1('#skF_3'))=k6_partfun1(k2_relat_1(k2_funct_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_624, c_528, c_761, c_502, c_914, c_309, c_914, c_500, c_914, c_914, c_945])).
% 5.42/2.08  tff(c_156, plain, (![A_52]: (k5_relat_1(A_52, k2_funct_1(A_52))=k6_partfun1(k1_relat_1(A_52)) | ~v2_funct_1(A_52) | ~v1_funct_1(A_52) | ~v1_relat_1(A_52))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_12])).
% 5.42/2.08  tff(c_165, plain, (![A_5]: (k6_partfun1(k1_relat_1(k2_funct_1(A_5)))=k5_relat_1(k2_funct_1(A_5), A_5) | ~v2_funct_1(k2_funct_1(A_5)) | ~v1_funct_1(k2_funct_1(A_5)) | ~v1_relat_1(k2_funct_1(A_5)) | ~v2_funct_1(A_5) | ~v1_funct_1(A_5) | ~v1_relat_1(A_5))), inference(superposition, [status(thm), theory('equality')], [c_14, c_156])).
% 5.42/2.08  tff(c_1262, plain, (k6_partfun1(k1_relat_1(k2_funct_1(k2_funct_1('#skF_3'))))=k6_partfun1(k2_relat_1(k2_funct_1('#skF_3'))) | ~v2_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) | ~v1_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) | ~v1_relat_1(k2_funct_1(k2_funct_1('#skF_3'))) | ~v2_funct_1(k2_funct_1('#skF_3')) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_979, c_165])).
% 5.42/2.08  tff(c_1278, plain, (k6_partfun1(k2_relat_1(k2_funct_1('#skF_3')))=k6_partfun1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_502, c_309, c_500, c_624, c_528, c_761, c_1213, c_1262])).
% 5.42/2.08  tff(c_1298, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_partfun1('#skF_2') | ~v2_funct_1(k2_funct_1('#skF_3')) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1278, c_153])).
% 5.42/2.08  tff(c_1344, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_partfun1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_83, c_56, c_182, c_502, c_309, c_500, c_1298])).
% 5.42/2.08  tff(c_503, plain, (![C_99, A_98, E_100, B_103, F_101, D_102]: (k1_partfun1(A_98, B_103, C_99, D_102, E_100, F_101)=k5_relat_1(E_100, F_101) | ~m1_subset_1(F_101, k1_zfmisc_1(k2_zfmisc_1(C_99, D_102))) | ~v1_funct_1(F_101) | ~m1_subset_1(E_100, k1_zfmisc_1(k2_zfmisc_1(A_98, B_103))) | ~v1_funct_1(E_100))), inference(cnfTransformation, [status(thm)], [f_114])).
% 5.42/2.08  tff(c_505, plain, (![A_98, B_103, E_100]: (k1_partfun1(A_98, B_103, '#skF_2', '#skF_2', E_100, k2_funct_1('#skF_3'))=k5_relat_1(E_100, k2_funct_1('#skF_3')) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~m1_subset_1(E_100, k1_zfmisc_1(k2_zfmisc_1(A_98, B_103))) | ~v1_funct_1(E_100))), inference(resolution, [status(thm)], [c_451, c_503])).
% 5.42/2.08  tff(c_1930, plain, (![A_135, B_136, E_137]: (k1_partfun1(A_135, B_136, '#skF_2', '#skF_2', E_137, k2_funct_1('#skF_3'))=k5_relat_1(E_137, k2_funct_1('#skF_3')) | ~m1_subset_1(E_137, k1_zfmisc_1(k2_zfmisc_1(A_135, B_136))) | ~v1_funct_1(E_137))), inference(demodulation, [status(thm), theory('equality')], [c_309, c_505])).
% 5.42/2.08  tff(c_1960, plain, (k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', '#skF_3', k2_funct_1('#skF_3'))=k5_relat_1('#skF_3', k2_funct_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_50, c_1930])).
% 5.42/2.08  tff(c_1980, plain, (k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', '#skF_3', k2_funct_1('#skF_3'))=k6_partfun1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_1344, c_1960])).
% 5.42/2.08  tff(c_48, plain, (~r2_relset_1('#skF_2', '#skF_2', k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', k2_funct_2('#skF_2', '#skF_3'), '#skF_3'), k6_partfun1('#skF_2')) | ~r2_relset_1('#skF_2', '#skF_2', k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', '#skF_3', k2_funct_2('#skF_2', '#skF_3')), k6_partfun1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_147])).
% 5.42/2.08  tff(c_85, plain, (~r2_relset_1('#skF_2', '#skF_2', k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', '#skF_3', k2_funct_2('#skF_2', '#skF_3')), k6_partfun1('#skF_2'))), inference(splitLeft, [status(thm)], [c_48])).
% 5.42/2.08  tff(c_310, plain, (~r2_relset_1('#skF_2', '#skF_2', k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', '#skF_3', k2_funct_1('#skF_3')), k6_partfun1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_307, c_85])).
% 5.42/2.08  tff(c_1982, plain, (~r2_relset_1('#skF_2', '#skF_2', k6_partfun1('#skF_2'), k6_partfun1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_1980, c_310])).
% 5.42/2.08  tff(c_1985, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_272, c_1982])).
% 5.42/2.08  tff(c_1986, plain, (~r2_relset_1('#skF_2', '#skF_2', k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', k2_funct_2('#skF_2', '#skF_3'), '#skF_3'), k6_partfun1('#skF_2'))), inference(splitRight, [status(thm)], [c_48])).
% 5.42/2.08  tff(c_2213, plain, (~r2_relset_1('#skF_2', '#skF_2', k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', k2_funct_1('#skF_3'), '#skF_3'), k6_partfun1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_2209, c_1986])).
% 5.42/2.08  tff(c_3319, plain, (~r2_relset_1('#skF_2', '#skF_2', k6_partfun1('#skF_2'), k6_partfun1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_3286, c_2213])).
% 5.42/2.08  tff(c_3322, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2158, c_3319])).
% 5.42/2.08  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.42/2.08  
% 5.42/2.08  Inference rules
% 5.42/2.08  ----------------------
% 5.42/2.08  #Ref     : 0
% 5.42/2.08  #Sup     : 793
% 5.42/2.08  #Fact    : 0
% 5.42/2.08  #Define  : 0
% 5.42/2.08  #Split   : 3
% 5.42/2.08  #Chain   : 0
% 5.42/2.08  #Close   : 0
% 5.42/2.08  
% 5.42/2.08  Ordering : KBO
% 5.42/2.08  
% 5.42/2.08  Simplification rules
% 5.42/2.08  ----------------------
% 5.42/2.08  #Subsume      : 91
% 5.42/2.08  #Demod        : 1462
% 5.42/2.08  #Tautology    : 337
% 5.42/2.08  #SimpNegUnit  : 0
% 5.42/2.08  #BackRed      : 28
% 5.42/2.08  
% 5.42/2.08  #Partial instantiations: 0
% 5.42/2.08  #Strategies tried      : 1
% 5.42/2.08  
% 5.42/2.08  Timing (in seconds)
% 5.42/2.08  ----------------------
% 5.42/2.08  Preprocessing        : 0.36
% 5.42/2.08  Parsing              : 0.20
% 5.42/2.08  CNF conversion       : 0.02
% 5.42/2.08  Main loop            : 0.93
% 5.42/2.08  Inferencing          : 0.30
% 5.42/2.08  Reduction            : 0.36
% 5.42/2.08  Demodulation         : 0.27
% 5.42/2.08  BG Simplification    : 0.04
% 5.42/2.08  Subsumption          : 0.16
% 5.82/2.08  Abstraction          : 0.05
% 5.82/2.08  MUC search           : 0.00
% 5.82/2.08  Cooper               : 0.00
% 5.82/2.08  Total                : 1.34
% 5.82/2.08  Index Insertion      : 0.00
% 5.82/2.08  Index Deletion       : 0.00
% 5.82/2.08  Index Matching       : 0.00
% 5.82/2.08  BG Taut test         : 0.00
%------------------------------------------------------------------------------
