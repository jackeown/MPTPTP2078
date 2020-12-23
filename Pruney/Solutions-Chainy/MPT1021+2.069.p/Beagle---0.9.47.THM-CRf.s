%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:16:10 EST 2020

% Result     : Theorem 5.94s
% Output     : CNFRefutation 6.25s
% Verified   : 
% Statistics : Number of formulae       :  125 ( 358 expanded)
%              Number of leaves         :   44 ( 154 expanded)
%              Depth                    :    9
%              Number of atoms          :  277 (1091 expanded)
%              Number of equality atoms :   40 (  82 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    3 (   1 average)

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

tff(f_34,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_156,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_funct_1(B)
          & v1_funct_2(B,A,A)
          & v3_funct_2(B,A,A)
          & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
       => ( r2_relset_1(A,A,k1_partfun1(A,A,A,A,B,k2_funct_2(A,B)),k6_partfun1(A))
          & r2_relset_1(A,A,k1_partfun1(A,A,A,A,k2_funct_2(A,B),B),k6_partfun1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_funct_2)).

tff(f_32,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_72,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( ( v1_funct_1(C)
          & v3_funct_2(C,A,B) )
       => ( v1_funct_1(C)
          & v2_funct_1(C)
          & v2_funct_2(C,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_funct_2)).

tff(f_100,axiom,(
    ! [A] :
      ( v1_partfun1(k6_partfun1(A),A)
      & m1_subset_1(k6_partfun1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).

tff(f_113,axiom,(
    ! [A,B] :
    ? [C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
      & v1_relat_1(C)
      & v4_relat_1(C,A)
      & v5_relat_1(C,B)
      & v1_funct_1(C)
      & v1_funct_2(C,A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc1_funct_2)).

tff(f_60,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => r2_relset_1(A,B,C,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',reflexivity_r2_relset_1)).

tff(f_50,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_80,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A) )
     => ( v2_funct_2(B,A)
      <=> k2_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_funct_2)).

tff(f_135,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_44,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k5_relat_1(A,k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))
          & k5_relat_1(k2_funct_1(A),A) = k6_relat_1(k2_relat_1(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_1)).

tff(f_133,axiom,(
    ! [A,B] :
      ( ( v1_funct_1(B)
        & v1_funct_2(B,A,A)
        & v3_funct_2(B,A,A)
        & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
     => k2_funct_2(A,B) = k2_funct_1(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_funct_2)).

tff(f_96,axiom,(
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

tff(f_123,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_54,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_143,axiom,(
    ! [A,B] :
      ( ( v1_funct_1(B)
        & v1_funct_2(B,A,A)
        & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
     => k1_relset_1(A,A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_funct_2)).

tff(c_4,plain,(
    ! [A_4,B_5] : v1_relat_1(k2_zfmisc_1(A_4,B_5)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_62,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_89,plain,(
    ! [B_56,A_57] :
      ( v1_relat_1(B_56)
      | ~ m1_subset_1(B_56,k1_zfmisc_1(A_57))
      | ~ v1_relat_1(A_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_98,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_2')) ),
    inference(resolution,[status(thm)],[c_62,c_89])).

tff(c_107,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_98])).

tff(c_68,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_64,plain,(
    v3_funct_2('#skF_3','#skF_2','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_2298,plain,(
    ! [C_240,A_241,B_242] :
      ( v2_funct_1(C_240)
      | ~ v3_funct_2(C_240,A_241,B_242)
      | ~ v1_funct_1(C_240)
      | ~ m1_subset_1(C_240,k1_zfmisc_1(k2_zfmisc_1(A_241,B_242))) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_2307,plain,
    ( v2_funct_1('#skF_3')
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_62,c_2298])).

tff(c_2314,plain,(
    v2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_64,c_2307])).

tff(c_38,plain,(
    ! [A_24] : m1_subset_1(k6_partfun1(A_24),k1_zfmisc_1(k2_zfmisc_1(A_24,A_24))) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_50,plain,(
    ! [A_25,B_26] : m1_subset_1('#skF_1'(A_25,B_26),k1_zfmisc_1(k2_zfmisc_1(A_25,B_26))) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_2373,plain,(
    ! [A_255,B_256,C_257,D_258] :
      ( r2_relset_1(A_255,B_256,C_257,C_257)
      | ~ m1_subset_1(D_258,k1_zfmisc_1(k2_zfmisc_1(A_255,B_256)))
      | ~ m1_subset_1(C_257,k1_zfmisc_1(k2_zfmisc_1(A_255,B_256))) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_2383,plain,(
    ! [A_259,B_260,C_261] :
      ( r2_relset_1(A_259,B_260,C_261,C_261)
      | ~ m1_subset_1(C_261,k1_zfmisc_1(k2_zfmisc_1(A_259,B_260))) ) ),
    inference(resolution,[status(thm)],[c_50,c_2373])).

tff(c_2391,plain,(
    ! [A_24] : r2_relset_1(A_24,A_24,k6_partfun1(A_24),k6_partfun1(A_24)) ),
    inference(resolution,[status(thm)],[c_38,c_2383])).

tff(c_2103,plain,(
    ! [C_203,B_204,A_205] :
      ( v5_relat_1(C_203,B_204)
      | ~ m1_subset_1(C_203,k1_zfmisc_1(k2_zfmisc_1(A_205,B_204))) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_2116,plain,(
    v5_relat_1('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_62,c_2103])).

tff(c_2119,plain,(
    ! [B_208,A_209] :
      ( k2_relat_1(B_208) = A_209
      | ~ v2_funct_2(B_208,A_209)
      | ~ v5_relat_1(B_208,A_209)
      | ~ v1_relat_1(B_208) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_2125,plain,
    ( k2_relat_1('#skF_3') = '#skF_2'
    | ~ v2_funct_2('#skF_3','#skF_2')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_2116,c_2119])).

tff(c_2134,plain,
    ( k2_relat_1('#skF_3') = '#skF_2'
    | ~ v2_funct_2('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_107,c_2125])).

tff(c_2138,plain,(
    ~ v2_funct_2('#skF_3','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_2134])).

tff(c_2212,plain,(
    ! [C_226,B_227,A_228] :
      ( v2_funct_2(C_226,B_227)
      | ~ v3_funct_2(C_226,A_228,B_227)
      | ~ v1_funct_1(C_226)
      | ~ m1_subset_1(C_226,k1_zfmisc_1(k2_zfmisc_1(A_228,B_227))) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_2221,plain,
    ( v2_funct_2('#skF_3','#skF_2')
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_62,c_2212])).

tff(c_2228,plain,(
    v2_funct_2('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_64,c_2221])).

tff(c_2230,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2138,c_2228])).

tff(c_2231,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_2134])).

tff(c_56,plain,(
    ! [A_36] : k6_relat_1(A_36) = k6_partfun1(A_36) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_6,plain,(
    ! [A_6] :
      ( k5_relat_1(k2_funct_1(A_6),A_6) = k6_relat_1(k2_relat_1(A_6))
      | ~ v2_funct_1(A_6)
      | ~ v1_funct_1(A_6)
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_70,plain,(
    ! [A_6] :
      ( k5_relat_1(k2_funct_1(A_6),A_6) = k6_partfun1(k2_relat_1(A_6))
      | ~ v2_funct_1(A_6)
      | ~ v1_funct_1(A_6)
      | ~ v1_relat_1(A_6) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_6])).

tff(c_66,plain,(
    v1_funct_2('#skF_3','#skF_2','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_2414,plain,(
    ! [A_268,B_269] :
      ( k2_funct_2(A_268,B_269) = k2_funct_1(B_269)
      | ~ m1_subset_1(B_269,k1_zfmisc_1(k2_zfmisc_1(A_268,A_268)))
      | ~ v3_funct_2(B_269,A_268,A_268)
      | ~ v1_funct_2(B_269,A_268,A_268)
      | ~ v1_funct_1(B_269) ) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_2424,plain,
    ( k2_funct_2('#skF_2','#skF_3') = k2_funct_1('#skF_3')
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_62,c_2414])).

tff(c_2431,plain,(
    k2_funct_2('#skF_2','#skF_3') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_64,c_2424])).

tff(c_2395,plain,(
    ! [A_265,B_266] :
      ( v1_funct_1(k2_funct_2(A_265,B_266))
      | ~ m1_subset_1(B_266,k1_zfmisc_1(k2_zfmisc_1(A_265,A_265)))
      | ~ v3_funct_2(B_266,A_265,A_265)
      | ~ v1_funct_2(B_266,A_265,A_265)
      | ~ v1_funct_1(B_266) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_2405,plain,
    ( v1_funct_1(k2_funct_2('#skF_2','#skF_3'))
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_62,c_2395])).

tff(c_2412,plain,(
    v1_funct_1(k2_funct_2('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_64,c_2405])).

tff(c_2432,plain,(
    v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2431,c_2412])).

tff(c_28,plain,(
    ! [A_22,B_23] :
      ( m1_subset_1(k2_funct_2(A_22,B_23),k1_zfmisc_1(k2_zfmisc_1(A_22,A_22)))
      | ~ m1_subset_1(B_23,k1_zfmisc_1(k2_zfmisc_1(A_22,A_22)))
      | ~ v3_funct_2(B_23,A_22,A_22)
      | ~ v1_funct_2(B_23,A_22,A_22)
      | ~ v1_funct_1(B_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_2610,plain,(
    ! [A_285,D_288,B_287,C_286,E_284,F_283] :
      ( k1_partfun1(A_285,B_287,C_286,D_288,E_284,F_283) = k5_relat_1(E_284,F_283)
      | ~ m1_subset_1(F_283,k1_zfmisc_1(k2_zfmisc_1(C_286,D_288)))
      | ~ v1_funct_1(F_283)
      | ~ m1_subset_1(E_284,k1_zfmisc_1(k2_zfmisc_1(A_285,B_287)))
      | ~ v1_funct_1(E_284) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_2620,plain,(
    ! [A_285,B_287,E_284] :
      ( k1_partfun1(A_285,B_287,'#skF_2','#skF_2',E_284,'#skF_3') = k5_relat_1(E_284,'#skF_3')
      | ~ v1_funct_1('#skF_3')
      | ~ m1_subset_1(E_284,k1_zfmisc_1(k2_zfmisc_1(A_285,B_287)))
      | ~ v1_funct_1(E_284) ) ),
    inference(resolution,[status(thm)],[c_62,c_2610])).

tff(c_2633,plain,(
    ! [A_289,B_290,E_291] :
      ( k1_partfun1(A_289,B_290,'#skF_2','#skF_2',E_291,'#skF_3') = k5_relat_1(E_291,'#skF_3')
      | ~ m1_subset_1(E_291,k1_zfmisc_1(k2_zfmisc_1(A_289,B_290)))
      | ~ v1_funct_1(E_291) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_2620])).

tff(c_2936,plain,(
    ! [A_298,B_299] :
      ( k1_partfun1(A_298,A_298,'#skF_2','#skF_2',k2_funct_2(A_298,B_299),'#skF_3') = k5_relat_1(k2_funct_2(A_298,B_299),'#skF_3')
      | ~ v1_funct_1(k2_funct_2(A_298,B_299))
      | ~ m1_subset_1(B_299,k1_zfmisc_1(k2_zfmisc_1(A_298,A_298)))
      | ~ v3_funct_2(B_299,A_298,A_298)
      | ~ v1_funct_2(B_299,A_298,A_298)
      | ~ v1_funct_1(B_299) ) ),
    inference(resolution,[status(thm)],[c_28,c_2633])).

tff(c_2951,plain,
    ( k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2',k2_funct_2('#skF_2','#skF_3'),'#skF_3') = k5_relat_1(k2_funct_2('#skF_2','#skF_3'),'#skF_3')
    | ~ v1_funct_1(k2_funct_2('#skF_2','#skF_3'))
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_62,c_2936])).

tff(c_2968,plain,(
    k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2',k2_funct_1('#skF_3'),'#skF_3') = k5_relat_1(k2_funct_1('#skF_3'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_64,c_2432,c_2431,c_2431,c_2431,c_2951])).

tff(c_319,plain,(
    ! [C_98,A_99,B_100] :
      ( v2_funct_1(C_98)
      | ~ v3_funct_2(C_98,A_99,B_100)
      | ~ v1_funct_1(C_98)
      | ~ m1_subset_1(C_98,k1_zfmisc_1(k2_zfmisc_1(A_99,B_100))) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_328,plain,
    ( v2_funct_1('#skF_3')
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_62,c_319])).

tff(c_335,plain,(
    v2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_64,c_328])).

tff(c_357,plain,(
    ! [A_110,B_111,C_112,D_113] :
      ( r2_relset_1(A_110,B_111,C_112,C_112)
      | ~ m1_subset_1(D_113,k1_zfmisc_1(k2_zfmisc_1(A_110,B_111)))
      | ~ m1_subset_1(C_112,k1_zfmisc_1(k2_zfmisc_1(A_110,B_111))) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_367,plain,(
    ! [A_114,B_115,C_116] :
      ( r2_relset_1(A_114,B_115,C_116,C_116)
      | ~ m1_subset_1(C_116,k1_zfmisc_1(k2_zfmisc_1(A_114,B_115))) ) ),
    inference(resolution,[status(thm)],[c_50,c_357])).

tff(c_375,plain,(
    ! [A_24] : r2_relset_1(A_24,A_24,k6_partfun1(A_24),k6_partfun1(A_24)) ),
    inference(resolution,[status(thm)],[c_38,c_367])).

tff(c_266,plain,(
    ! [A_90,B_91,C_92] :
      ( k1_relset_1(A_90,B_91,C_92) = k1_relat_1(C_92)
      | ~ m1_subset_1(C_92,k1_zfmisc_1(k2_zfmisc_1(A_90,B_91))) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_278,plain,(
    k1_relset_1('#skF_2','#skF_2','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_62,c_266])).

tff(c_379,plain,(
    ! [A_120,B_121] :
      ( k1_relset_1(A_120,A_120,B_121) = A_120
      | ~ m1_subset_1(B_121,k1_zfmisc_1(k2_zfmisc_1(A_120,A_120)))
      | ~ v1_funct_2(B_121,A_120,A_120)
      | ~ v1_funct_1(B_121) ) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_389,plain,
    ( k1_relset_1('#skF_2','#skF_2','#skF_3') = '#skF_2'
    | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_62,c_379])).

tff(c_397,plain,(
    k1_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_278,c_389])).

tff(c_8,plain,(
    ! [A_6] :
      ( k5_relat_1(A_6,k2_funct_1(A_6)) = k6_relat_1(k1_relat_1(A_6))
      | ~ v2_funct_1(A_6)
      | ~ v1_funct_1(A_6)
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_69,plain,(
    ! [A_6] :
      ( k5_relat_1(A_6,k2_funct_1(A_6)) = k6_partfun1(k1_relat_1(A_6))
      | ~ v2_funct_1(A_6)
      | ~ v1_funct_1(A_6)
      | ~ v1_relat_1(A_6) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_8])).

tff(c_437,plain,(
    ! [A_128,B_129] :
      ( k2_funct_2(A_128,B_129) = k2_funct_1(B_129)
      | ~ m1_subset_1(B_129,k1_zfmisc_1(k2_zfmisc_1(A_128,A_128)))
      | ~ v3_funct_2(B_129,A_128,A_128)
      | ~ v1_funct_2(B_129,A_128,A_128)
      | ~ v1_funct_1(B_129) ) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_447,plain,
    ( k2_funct_2('#skF_2','#skF_3') = k2_funct_1('#skF_3')
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_62,c_437])).

tff(c_454,plain,(
    k2_funct_2('#skF_2','#skF_3') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_64,c_447])).

tff(c_416,plain,(
    ! [A_123,B_124] :
      ( v1_funct_1(k2_funct_2(A_123,B_124))
      | ~ m1_subset_1(B_124,k1_zfmisc_1(k2_zfmisc_1(A_123,A_123)))
      | ~ v3_funct_2(B_124,A_123,A_123)
      | ~ v1_funct_2(B_124,A_123,A_123)
      | ~ v1_funct_1(B_124) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_426,plain,
    ( v1_funct_1(k2_funct_2('#skF_2','#skF_3'))
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_62,c_416])).

tff(c_433,plain,(
    v1_funct_1(k2_funct_2('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_64,c_426])).

tff(c_455,plain,(
    v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_454,c_433])).

tff(c_617,plain,(
    ! [E_143,F_142,A_144,D_147,C_145,B_146] :
      ( k1_partfun1(A_144,B_146,C_145,D_147,E_143,F_142) = k5_relat_1(E_143,F_142)
      | ~ m1_subset_1(F_142,k1_zfmisc_1(k2_zfmisc_1(C_145,D_147)))
      | ~ v1_funct_1(F_142)
      | ~ m1_subset_1(E_143,k1_zfmisc_1(k2_zfmisc_1(A_144,B_146)))
      | ~ v1_funct_1(E_143) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_1984,plain,(
    ! [A_195,B_199,E_198,B_197,A_196] :
      ( k1_partfun1(A_196,B_197,A_195,A_195,E_198,k2_funct_2(A_195,B_199)) = k5_relat_1(E_198,k2_funct_2(A_195,B_199))
      | ~ v1_funct_1(k2_funct_2(A_195,B_199))
      | ~ m1_subset_1(E_198,k1_zfmisc_1(k2_zfmisc_1(A_196,B_197)))
      | ~ v1_funct_1(E_198)
      | ~ m1_subset_1(B_199,k1_zfmisc_1(k2_zfmisc_1(A_195,A_195)))
      | ~ v3_funct_2(B_199,A_195,A_195)
      | ~ v1_funct_2(B_199,A_195,A_195)
      | ~ v1_funct_1(B_199) ) ),
    inference(resolution,[status(thm)],[c_28,c_617])).

tff(c_2004,plain,(
    ! [A_195,B_199] :
      ( k1_partfun1('#skF_2','#skF_2',A_195,A_195,'#skF_3',k2_funct_2(A_195,B_199)) = k5_relat_1('#skF_3',k2_funct_2(A_195,B_199))
      | ~ v1_funct_1(k2_funct_2(A_195,B_199))
      | ~ v1_funct_1('#skF_3')
      | ~ m1_subset_1(B_199,k1_zfmisc_1(k2_zfmisc_1(A_195,A_195)))
      | ~ v3_funct_2(B_199,A_195,A_195)
      | ~ v1_funct_2(B_199,A_195,A_195)
      | ~ v1_funct_1(B_199) ) ),
    inference(resolution,[status(thm)],[c_62,c_1984])).

tff(c_2035,plain,(
    ! [A_200,B_201] :
      ( k1_partfun1('#skF_2','#skF_2',A_200,A_200,'#skF_3',k2_funct_2(A_200,B_201)) = k5_relat_1('#skF_3',k2_funct_2(A_200,B_201))
      | ~ v1_funct_1(k2_funct_2(A_200,B_201))
      | ~ m1_subset_1(B_201,k1_zfmisc_1(k2_zfmisc_1(A_200,A_200)))
      | ~ v3_funct_2(B_201,A_200,A_200)
      | ~ v1_funct_2(B_201,A_200,A_200)
      | ~ v1_funct_1(B_201) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_2004])).

tff(c_2056,plain,
    ( k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2','#skF_3',k2_funct_2('#skF_2','#skF_3')) = k5_relat_1('#skF_3',k2_funct_2('#skF_2','#skF_3'))
    | ~ v1_funct_1(k2_funct_2('#skF_2','#skF_3'))
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_62,c_2035])).

tff(c_2082,plain,(
    k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2','#skF_3',k2_funct_1('#skF_3')) = k5_relat_1('#skF_3',k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_64,c_455,c_454,c_454,c_454,c_2056])).

tff(c_60,plain,
    ( ~ r2_relset_1('#skF_2','#skF_2',k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2',k2_funct_2('#skF_2','#skF_3'),'#skF_3'),k6_partfun1('#skF_2'))
    | ~ r2_relset_1('#skF_2','#skF_2',k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2','#skF_3',k2_funct_2('#skF_2','#skF_3')),k6_partfun1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_123,plain,(
    ~ r2_relset_1('#skF_2','#skF_2',k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2','#skF_3',k2_funct_2('#skF_2','#skF_3')),k6_partfun1('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_60])).

tff(c_456,plain,(
    ~ r2_relset_1('#skF_2','#skF_2',k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2','#skF_3',k2_funct_1('#skF_3')),k6_partfun1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_454,c_123])).

tff(c_2089,plain,(
    ~ r2_relset_1('#skF_2','#skF_2',k5_relat_1('#skF_3',k2_funct_1('#skF_3')),k6_partfun1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2082,c_456])).

tff(c_2096,plain,
    ( ~ r2_relset_1('#skF_2','#skF_2',k6_partfun1(k1_relat_1('#skF_3')),k6_partfun1('#skF_2'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_69,c_2089])).

tff(c_2099,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_107,c_68,c_335,c_375,c_397,c_2096])).

tff(c_2100,plain,(
    ~ r2_relset_1('#skF_2','#skF_2',k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2',k2_funct_2('#skF_2','#skF_3'),'#skF_3'),k6_partfun1('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_60])).

tff(c_2433,plain,(
    ~ r2_relset_1('#skF_2','#skF_2',k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2',k2_funct_1('#skF_3'),'#skF_3'),k6_partfun1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2431,c_2100])).

tff(c_3020,plain,(
    ~ r2_relset_1('#skF_2','#skF_2',k5_relat_1(k2_funct_1('#skF_3'),'#skF_3'),k6_partfun1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2968,c_2433])).

tff(c_3027,plain,
    ( ~ r2_relset_1('#skF_2','#skF_2',k6_partfun1(k2_relat_1('#skF_3')),k6_partfun1('#skF_2'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_70,c_3020])).

tff(c_3030,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_107,c_68,c_2314,c_2391,c_2231,c_3027])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n022.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 11:42:41 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.94/2.19  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.94/2.21  
% 5.94/2.21  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.94/2.21  %$ r2_relset_1 > v3_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > v1_partfun1 > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > k2_funct_2 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 5.94/2.21  
% 5.94/2.21  %Foreground sorts:
% 5.94/2.21  
% 5.94/2.21  
% 5.94/2.21  %Background operators:
% 5.94/2.21  
% 5.94/2.21  
% 5.94/2.21  %Foreground operators:
% 5.94/2.21  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 5.94/2.21  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 5.94/2.21  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 5.94/2.21  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.94/2.21  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 5.94/2.21  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 5.94/2.21  tff(k2_funct_2, type, k2_funct_2: ($i * $i) > $i).
% 5.94/2.21  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 5.94/2.21  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 5.94/2.21  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 5.94/2.21  tff('#skF_2', type, '#skF_2': $i).
% 5.94/2.21  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 5.94/2.21  tff('#skF_3', type, '#skF_3': $i).
% 5.94/2.21  tff(v2_funct_2, type, v2_funct_2: ($i * $i) > $o).
% 5.94/2.21  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 5.94/2.21  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 5.94/2.21  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.94/2.21  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 5.94/2.21  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.94/2.21  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.94/2.21  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 5.94/2.21  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 5.94/2.21  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.94/2.21  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 5.94/2.21  tff(v3_funct_2, type, v3_funct_2: ($i * $i * $i) > $o).
% 5.94/2.21  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 5.94/2.21  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 5.94/2.21  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.94/2.21  
% 6.25/2.23  tff(f_34, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 6.25/2.23  tff(f_156, negated_conjecture, ~(![A, B]: ((((v1_funct_1(B) & v1_funct_2(B, A, A)) & v3_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (r2_relset_1(A, A, k1_partfun1(A, A, A, A, B, k2_funct_2(A, B)), k6_partfun1(A)) & r2_relset_1(A, A, k1_partfun1(A, A, A, A, k2_funct_2(A, B), B), k6_partfun1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t88_funct_2)).
% 6.25/2.23  tff(f_32, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 6.25/2.23  tff(f_72, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v3_funct_2(C, A, B)) => ((v1_funct_1(C) & v2_funct_1(C)) & v2_funct_2(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_funct_2)).
% 6.25/2.23  tff(f_100, axiom, (![A]: (v1_partfun1(k6_partfun1(A), A) & m1_subset_1(k6_partfun1(A), k1_zfmisc_1(k2_zfmisc_1(A, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_partfun1)).
% 6.25/2.23  tff(f_113, axiom, (![A, B]: (?[C]: (((((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & v1_relat_1(C)) & v4_relat_1(C, A)) & v5_relat_1(C, B)) & v1_funct_1(C)) & v1_funct_2(C, A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', rc1_funct_2)).
% 6.25/2.23  tff(f_60, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => r2_relset_1(A, B, C, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', reflexivity_r2_relset_1)).
% 6.25/2.23  tff(f_50, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 6.25/2.23  tff(f_80, axiom, (![A, B]: ((v1_relat_1(B) & v5_relat_1(B, A)) => (v2_funct_2(B, A) <=> (k2_relat_1(B) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_funct_2)).
% 6.25/2.23  tff(f_135, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 6.25/2.23  tff(f_44, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k5_relat_1(A, k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))) & (k5_relat_1(k2_funct_1(A), A) = k6_relat_1(k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t61_funct_1)).
% 6.25/2.23  tff(f_133, axiom, (![A, B]: ((((v1_funct_1(B) & v1_funct_2(B, A, A)) & v3_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (k2_funct_2(A, B) = k2_funct_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_funct_2)).
% 6.25/2.23  tff(f_96, axiom, (![A, B]: ((((v1_funct_1(B) & v1_funct_2(B, A, A)) & v3_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (((v1_funct_1(k2_funct_2(A, B)) & v1_funct_2(k2_funct_2(A, B), A, A)) & v3_funct_2(k2_funct_2(A, B), A, A)) & m1_subset_1(k2_funct_2(A, B), k1_zfmisc_1(k2_zfmisc_1(A, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_funct_2)).
% 6.25/2.23  tff(f_123, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 6.25/2.23  tff(f_54, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 6.25/2.23  tff(f_143, axiom, (![A, B]: (((v1_funct_1(B) & v1_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (k1_relset_1(A, A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t67_funct_2)).
% 6.25/2.23  tff(c_4, plain, (![A_4, B_5]: (v1_relat_1(k2_zfmisc_1(A_4, B_5)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 6.25/2.23  tff(c_62, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_156])).
% 6.25/2.23  tff(c_89, plain, (![B_56, A_57]: (v1_relat_1(B_56) | ~m1_subset_1(B_56, k1_zfmisc_1(A_57)) | ~v1_relat_1(A_57))), inference(cnfTransformation, [status(thm)], [f_32])).
% 6.25/2.23  tff(c_98, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_2'))), inference(resolution, [status(thm)], [c_62, c_89])).
% 6.25/2.23  tff(c_107, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_98])).
% 6.25/2.23  tff(c_68, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_156])).
% 6.25/2.23  tff(c_64, plain, (v3_funct_2('#skF_3', '#skF_2', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_156])).
% 6.25/2.23  tff(c_2298, plain, (![C_240, A_241, B_242]: (v2_funct_1(C_240) | ~v3_funct_2(C_240, A_241, B_242) | ~v1_funct_1(C_240) | ~m1_subset_1(C_240, k1_zfmisc_1(k2_zfmisc_1(A_241, B_242))))), inference(cnfTransformation, [status(thm)], [f_72])).
% 6.25/2.23  tff(c_2307, plain, (v2_funct_1('#skF_3') | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_62, c_2298])).
% 6.25/2.23  tff(c_2314, plain, (v2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_64, c_2307])).
% 6.25/2.23  tff(c_38, plain, (![A_24]: (m1_subset_1(k6_partfun1(A_24), k1_zfmisc_1(k2_zfmisc_1(A_24, A_24))))), inference(cnfTransformation, [status(thm)], [f_100])).
% 6.25/2.23  tff(c_50, plain, (![A_25, B_26]: (m1_subset_1('#skF_1'(A_25, B_26), k1_zfmisc_1(k2_zfmisc_1(A_25, B_26))))), inference(cnfTransformation, [status(thm)], [f_113])).
% 6.25/2.23  tff(c_2373, plain, (![A_255, B_256, C_257, D_258]: (r2_relset_1(A_255, B_256, C_257, C_257) | ~m1_subset_1(D_258, k1_zfmisc_1(k2_zfmisc_1(A_255, B_256))) | ~m1_subset_1(C_257, k1_zfmisc_1(k2_zfmisc_1(A_255, B_256))))), inference(cnfTransformation, [status(thm)], [f_60])).
% 6.25/2.23  tff(c_2383, plain, (![A_259, B_260, C_261]: (r2_relset_1(A_259, B_260, C_261, C_261) | ~m1_subset_1(C_261, k1_zfmisc_1(k2_zfmisc_1(A_259, B_260))))), inference(resolution, [status(thm)], [c_50, c_2373])).
% 6.25/2.23  tff(c_2391, plain, (![A_24]: (r2_relset_1(A_24, A_24, k6_partfun1(A_24), k6_partfun1(A_24)))), inference(resolution, [status(thm)], [c_38, c_2383])).
% 6.25/2.23  tff(c_2103, plain, (![C_203, B_204, A_205]: (v5_relat_1(C_203, B_204) | ~m1_subset_1(C_203, k1_zfmisc_1(k2_zfmisc_1(A_205, B_204))))), inference(cnfTransformation, [status(thm)], [f_50])).
% 6.25/2.23  tff(c_2116, plain, (v5_relat_1('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_62, c_2103])).
% 6.25/2.23  tff(c_2119, plain, (![B_208, A_209]: (k2_relat_1(B_208)=A_209 | ~v2_funct_2(B_208, A_209) | ~v5_relat_1(B_208, A_209) | ~v1_relat_1(B_208))), inference(cnfTransformation, [status(thm)], [f_80])).
% 6.25/2.23  tff(c_2125, plain, (k2_relat_1('#skF_3')='#skF_2' | ~v2_funct_2('#skF_3', '#skF_2') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_2116, c_2119])).
% 6.25/2.23  tff(c_2134, plain, (k2_relat_1('#skF_3')='#skF_2' | ~v2_funct_2('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_107, c_2125])).
% 6.25/2.23  tff(c_2138, plain, (~v2_funct_2('#skF_3', '#skF_2')), inference(splitLeft, [status(thm)], [c_2134])).
% 6.25/2.23  tff(c_2212, plain, (![C_226, B_227, A_228]: (v2_funct_2(C_226, B_227) | ~v3_funct_2(C_226, A_228, B_227) | ~v1_funct_1(C_226) | ~m1_subset_1(C_226, k1_zfmisc_1(k2_zfmisc_1(A_228, B_227))))), inference(cnfTransformation, [status(thm)], [f_72])).
% 6.25/2.23  tff(c_2221, plain, (v2_funct_2('#skF_3', '#skF_2') | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_62, c_2212])).
% 6.25/2.23  tff(c_2228, plain, (v2_funct_2('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_64, c_2221])).
% 6.25/2.23  tff(c_2230, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2138, c_2228])).
% 6.25/2.23  tff(c_2231, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(splitRight, [status(thm)], [c_2134])).
% 6.25/2.23  tff(c_56, plain, (![A_36]: (k6_relat_1(A_36)=k6_partfun1(A_36))), inference(cnfTransformation, [status(thm)], [f_135])).
% 6.25/2.23  tff(c_6, plain, (![A_6]: (k5_relat_1(k2_funct_1(A_6), A_6)=k6_relat_1(k2_relat_1(A_6)) | ~v2_funct_1(A_6) | ~v1_funct_1(A_6) | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_44])).
% 6.25/2.24  tff(c_70, plain, (![A_6]: (k5_relat_1(k2_funct_1(A_6), A_6)=k6_partfun1(k2_relat_1(A_6)) | ~v2_funct_1(A_6) | ~v1_funct_1(A_6) | ~v1_relat_1(A_6))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_6])).
% 6.25/2.24  tff(c_66, plain, (v1_funct_2('#skF_3', '#skF_2', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_156])).
% 6.25/2.24  tff(c_2414, plain, (![A_268, B_269]: (k2_funct_2(A_268, B_269)=k2_funct_1(B_269) | ~m1_subset_1(B_269, k1_zfmisc_1(k2_zfmisc_1(A_268, A_268))) | ~v3_funct_2(B_269, A_268, A_268) | ~v1_funct_2(B_269, A_268, A_268) | ~v1_funct_1(B_269))), inference(cnfTransformation, [status(thm)], [f_133])).
% 6.25/2.24  tff(c_2424, plain, (k2_funct_2('#skF_2', '#skF_3')=k2_funct_1('#skF_3') | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_62, c_2414])).
% 6.25/2.24  tff(c_2431, plain, (k2_funct_2('#skF_2', '#skF_3')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_66, c_64, c_2424])).
% 6.25/2.24  tff(c_2395, plain, (![A_265, B_266]: (v1_funct_1(k2_funct_2(A_265, B_266)) | ~m1_subset_1(B_266, k1_zfmisc_1(k2_zfmisc_1(A_265, A_265))) | ~v3_funct_2(B_266, A_265, A_265) | ~v1_funct_2(B_266, A_265, A_265) | ~v1_funct_1(B_266))), inference(cnfTransformation, [status(thm)], [f_96])).
% 6.25/2.24  tff(c_2405, plain, (v1_funct_1(k2_funct_2('#skF_2', '#skF_3')) | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_62, c_2395])).
% 6.25/2.24  tff(c_2412, plain, (v1_funct_1(k2_funct_2('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_66, c_64, c_2405])).
% 6.25/2.24  tff(c_2432, plain, (v1_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_2431, c_2412])).
% 6.25/2.24  tff(c_28, plain, (![A_22, B_23]: (m1_subset_1(k2_funct_2(A_22, B_23), k1_zfmisc_1(k2_zfmisc_1(A_22, A_22))) | ~m1_subset_1(B_23, k1_zfmisc_1(k2_zfmisc_1(A_22, A_22))) | ~v3_funct_2(B_23, A_22, A_22) | ~v1_funct_2(B_23, A_22, A_22) | ~v1_funct_1(B_23))), inference(cnfTransformation, [status(thm)], [f_96])).
% 6.25/2.24  tff(c_2610, plain, (![A_285, D_288, B_287, C_286, E_284, F_283]: (k1_partfun1(A_285, B_287, C_286, D_288, E_284, F_283)=k5_relat_1(E_284, F_283) | ~m1_subset_1(F_283, k1_zfmisc_1(k2_zfmisc_1(C_286, D_288))) | ~v1_funct_1(F_283) | ~m1_subset_1(E_284, k1_zfmisc_1(k2_zfmisc_1(A_285, B_287))) | ~v1_funct_1(E_284))), inference(cnfTransformation, [status(thm)], [f_123])).
% 6.25/2.24  tff(c_2620, plain, (![A_285, B_287, E_284]: (k1_partfun1(A_285, B_287, '#skF_2', '#skF_2', E_284, '#skF_3')=k5_relat_1(E_284, '#skF_3') | ~v1_funct_1('#skF_3') | ~m1_subset_1(E_284, k1_zfmisc_1(k2_zfmisc_1(A_285, B_287))) | ~v1_funct_1(E_284))), inference(resolution, [status(thm)], [c_62, c_2610])).
% 6.25/2.24  tff(c_2633, plain, (![A_289, B_290, E_291]: (k1_partfun1(A_289, B_290, '#skF_2', '#skF_2', E_291, '#skF_3')=k5_relat_1(E_291, '#skF_3') | ~m1_subset_1(E_291, k1_zfmisc_1(k2_zfmisc_1(A_289, B_290))) | ~v1_funct_1(E_291))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_2620])).
% 6.25/2.24  tff(c_2936, plain, (![A_298, B_299]: (k1_partfun1(A_298, A_298, '#skF_2', '#skF_2', k2_funct_2(A_298, B_299), '#skF_3')=k5_relat_1(k2_funct_2(A_298, B_299), '#skF_3') | ~v1_funct_1(k2_funct_2(A_298, B_299)) | ~m1_subset_1(B_299, k1_zfmisc_1(k2_zfmisc_1(A_298, A_298))) | ~v3_funct_2(B_299, A_298, A_298) | ~v1_funct_2(B_299, A_298, A_298) | ~v1_funct_1(B_299))), inference(resolution, [status(thm)], [c_28, c_2633])).
% 6.25/2.24  tff(c_2951, plain, (k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', k2_funct_2('#skF_2', '#skF_3'), '#skF_3')=k5_relat_1(k2_funct_2('#skF_2', '#skF_3'), '#skF_3') | ~v1_funct_1(k2_funct_2('#skF_2', '#skF_3')) | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_62, c_2936])).
% 6.25/2.24  tff(c_2968, plain, (k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', k2_funct_1('#skF_3'), '#skF_3')=k5_relat_1(k2_funct_1('#skF_3'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_66, c_64, c_2432, c_2431, c_2431, c_2431, c_2951])).
% 6.25/2.24  tff(c_319, plain, (![C_98, A_99, B_100]: (v2_funct_1(C_98) | ~v3_funct_2(C_98, A_99, B_100) | ~v1_funct_1(C_98) | ~m1_subset_1(C_98, k1_zfmisc_1(k2_zfmisc_1(A_99, B_100))))), inference(cnfTransformation, [status(thm)], [f_72])).
% 6.25/2.24  tff(c_328, plain, (v2_funct_1('#skF_3') | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_62, c_319])).
% 6.25/2.24  tff(c_335, plain, (v2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_64, c_328])).
% 6.25/2.24  tff(c_357, plain, (![A_110, B_111, C_112, D_113]: (r2_relset_1(A_110, B_111, C_112, C_112) | ~m1_subset_1(D_113, k1_zfmisc_1(k2_zfmisc_1(A_110, B_111))) | ~m1_subset_1(C_112, k1_zfmisc_1(k2_zfmisc_1(A_110, B_111))))), inference(cnfTransformation, [status(thm)], [f_60])).
% 6.25/2.24  tff(c_367, plain, (![A_114, B_115, C_116]: (r2_relset_1(A_114, B_115, C_116, C_116) | ~m1_subset_1(C_116, k1_zfmisc_1(k2_zfmisc_1(A_114, B_115))))), inference(resolution, [status(thm)], [c_50, c_357])).
% 6.25/2.24  tff(c_375, plain, (![A_24]: (r2_relset_1(A_24, A_24, k6_partfun1(A_24), k6_partfun1(A_24)))), inference(resolution, [status(thm)], [c_38, c_367])).
% 6.25/2.24  tff(c_266, plain, (![A_90, B_91, C_92]: (k1_relset_1(A_90, B_91, C_92)=k1_relat_1(C_92) | ~m1_subset_1(C_92, k1_zfmisc_1(k2_zfmisc_1(A_90, B_91))))), inference(cnfTransformation, [status(thm)], [f_54])).
% 6.25/2.24  tff(c_278, plain, (k1_relset_1('#skF_2', '#skF_2', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_62, c_266])).
% 6.25/2.24  tff(c_379, plain, (![A_120, B_121]: (k1_relset_1(A_120, A_120, B_121)=A_120 | ~m1_subset_1(B_121, k1_zfmisc_1(k2_zfmisc_1(A_120, A_120))) | ~v1_funct_2(B_121, A_120, A_120) | ~v1_funct_1(B_121))), inference(cnfTransformation, [status(thm)], [f_143])).
% 6.25/2.24  tff(c_389, plain, (k1_relset_1('#skF_2', '#skF_2', '#skF_3')='#skF_2' | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_62, c_379])).
% 6.25/2.24  tff(c_397, plain, (k1_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_68, c_66, c_278, c_389])).
% 6.25/2.24  tff(c_8, plain, (![A_6]: (k5_relat_1(A_6, k2_funct_1(A_6))=k6_relat_1(k1_relat_1(A_6)) | ~v2_funct_1(A_6) | ~v1_funct_1(A_6) | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_44])).
% 6.25/2.24  tff(c_69, plain, (![A_6]: (k5_relat_1(A_6, k2_funct_1(A_6))=k6_partfun1(k1_relat_1(A_6)) | ~v2_funct_1(A_6) | ~v1_funct_1(A_6) | ~v1_relat_1(A_6))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_8])).
% 6.25/2.24  tff(c_437, plain, (![A_128, B_129]: (k2_funct_2(A_128, B_129)=k2_funct_1(B_129) | ~m1_subset_1(B_129, k1_zfmisc_1(k2_zfmisc_1(A_128, A_128))) | ~v3_funct_2(B_129, A_128, A_128) | ~v1_funct_2(B_129, A_128, A_128) | ~v1_funct_1(B_129))), inference(cnfTransformation, [status(thm)], [f_133])).
% 6.25/2.24  tff(c_447, plain, (k2_funct_2('#skF_2', '#skF_3')=k2_funct_1('#skF_3') | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_62, c_437])).
% 6.25/2.24  tff(c_454, plain, (k2_funct_2('#skF_2', '#skF_3')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_66, c_64, c_447])).
% 6.25/2.24  tff(c_416, plain, (![A_123, B_124]: (v1_funct_1(k2_funct_2(A_123, B_124)) | ~m1_subset_1(B_124, k1_zfmisc_1(k2_zfmisc_1(A_123, A_123))) | ~v3_funct_2(B_124, A_123, A_123) | ~v1_funct_2(B_124, A_123, A_123) | ~v1_funct_1(B_124))), inference(cnfTransformation, [status(thm)], [f_96])).
% 6.25/2.24  tff(c_426, plain, (v1_funct_1(k2_funct_2('#skF_2', '#skF_3')) | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_62, c_416])).
% 6.25/2.24  tff(c_433, plain, (v1_funct_1(k2_funct_2('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_66, c_64, c_426])).
% 6.25/2.24  tff(c_455, plain, (v1_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_454, c_433])).
% 6.25/2.24  tff(c_617, plain, (![E_143, F_142, A_144, D_147, C_145, B_146]: (k1_partfun1(A_144, B_146, C_145, D_147, E_143, F_142)=k5_relat_1(E_143, F_142) | ~m1_subset_1(F_142, k1_zfmisc_1(k2_zfmisc_1(C_145, D_147))) | ~v1_funct_1(F_142) | ~m1_subset_1(E_143, k1_zfmisc_1(k2_zfmisc_1(A_144, B_146))) | ~v1_funct_1(E_143))), inference(cnfTransformation, [status(thm)], [f_123])).
% 6.25/2.24  tff(c_1984, plain, (![A_195, B_199, E_198, B_197, A_196]: (k1_partfun1(A_196, B_197, A_195, A_195, E_198, k2_funct_2(A_195, B_199))=k5_relat_1(E_198, k2_funct_2(A_195, B_199)) | ~v1_funct_1(k2_funct_2(A_195, B_199)) | ~m1_subset_1(E_198, k1_zfmisc_1(k2_zfmisc_1(A_196, B_197))) | ~v1_funct_1(E_198) | ~m1_subset_1(B_199, k1_zfmisc_1(k2_zfmisc_1(A_195, A_195))) | ~v3_funct_2(B_199, A_195, A_195) | ~v1_funct_2(B_199, A_195, A_195) | ~v1_funct_1(B_199))), inference(resolution, [status(thm)], [c_28, c_617])).
% 6.25/2.24  tff(c_2004, plain, (![A_195, B_199]: (k1_partfun1('#skF_2', '#skF_2', A_195, A_195, '#skF_3', k2_funct_2(A_195, B_199))=k5_relat_1('#skF_3', k2_funct_2(A_195, B_199)) | ~v1_funct_1(k2_funct_2(A_195, B_199)) | ~v1_funct_1('#skF_3') | ~m1_subset_1(B_199, k1_zfmisc_1(k2_zfmisc_1(A_195, A_195))) | ~v3_funct_2(B_199, A_195, A_195) | ~v1_funct_2(B_199, A_195, A_195) | ~v1_funct_1(B_199))), inference(resolution, [status(thm)], [c_62, c_1984])).
% 6.25/2.24  tff(c_2035, plain, (![A_200, B_201]: (k1_partfun1('#skF_2', '#skF_2', A_200, A_200, '#skF_3', k2_funct_2(A_200, B_201))=k5_relat_1('#skF_3', k2_funct_2(A_200, B_201)) | ~v1_funct_1(k2_funct_2(A_200, B_201)) | ~m1_subset_1(B_201, k1_zfmisc_1(k2_zfmisc_1(A_200, A_200))) | ~v3_funct_2(B_201, A_200, A_200) | ~v1_funct_2(B_201, A_200, A_200) | ~v1_funct_1(B_201))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_2004])).
% 6.25/2.24  tff(c_2056, plain, (k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', '#skF_3', k2_funct_2('#skF_2', '#skF_3'))=k5_relat_1('#skF_3', k2_funct_2('#skF_2', '#skF_3')) | ~v1_funct_1(k2_funct_2('#skF_2', '#skF_3')) | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_62, c_2035])).
% 6.25/2.24  tff(c_2082, plain, (k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', '#skF_3', k2_funct_1('#skF_3'))=k5_relat_1('#skF_3', k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_66, c_64, c_455, c_454, c_454, c_454, c_2056])).
% 6.25/2.24  tff(c_60, plain, (~r2_relset_1('#skF_2', '#skF_2', k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', k2_funct_2('#skF_2', '#skF_3'), '#skF_3'), k6_partfun1('#skF_2')) | ~r2_relset_1('#skF_2', '#skF_2', k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', '#skF_3', k2_funct_2('#skF_2', '#skF_3')), k6_partfun1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_156])).
% 6.25/2.24  tff(c_123, plain, (~r2_relset_1('#skF_2', '#skF_2', k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', '#skF_3', k2_funct_2('#skF_2', '#skF_3')), k6_partfun1('#skF_2'))), inference(splitLeft, [status(thm)], [c_60])).
% 6.25/2.24  tff(c_456, plain, (~r2_relset_1('#skF_2', '#skF_2', k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', '#skF_3', k2_funct_1('#skF_3')), k6_partfun1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_454, c_123])).
% 6.25/2.24  tff(c_2089, plain, (~r2_relset_1('#skF_2', '#skF_2', k5_relat_1('#skF_3', k2_funct_1('#skF_3')), k6_partfun1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_2082, c_456])).
% 6.25/2.24  tff(c_2096, plain, (~r2_relset_1('#skF_2', '#skF_2', k6_partfun1(k1_relat_1('#skF_3')), k6_partfun1('#skF_2')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_69, c_2089])).
% 6.25/2.24  tff(c_2099, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_107, c_68, c_335, c_375, c_397, c_2096])).
% 6.25/2.24  tff(c_2100, plain, (~r2_relset_1('#skF_2', '#skF_2', k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', k2_funct_2('#skF_2', '#skF_3'), '#skF_3'), k6_partfun1('#skF_2'))), inference(splitRight, [status(thm)], [c_60])).
% 6.25/2.24  tff(c_2433, plain, (~r2_relset_1('#skF_2', '#skF_2', k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', k2_funct_1('#skF_3'), '#skF_3'), k6_partfun1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_2431, c_2100])).
% 6.25/2.24  tff(c_3020, plain, (~r2_relset_1('#skF_2', '#skF_2', k5_relat_1(k2_funct_1('#skF_3'), '#skF_3'), k6_partfun1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_2968, c_2433])).
% 6.25/2.24  tff(c_3027, plain, (~r2_relset_1('#skF_2', '#skF_2', k6_partfun1(k2_relat_1('#skF_3')), k6_partfun1('#skF_2')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_70, c_3020])).
% 6.25/2.24  tff(c_3030, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_107, c_68, c_2314, c_2391, c_2231, c_3027])).
% 6.25/2.24  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.25/2.24  
% 6.25/2.24  Inference rules
% 6.25/2.24  ----------------------
% 6.25/2.24  #Ref     : 0
% 6.25/2.24  #Sup     : 625
% 6.25/2.24  #Fact    : 0
% 6.25/2.24  #Define  : 0
% 6.25/2.24  #Split   : 3
% 6.25/2.24  #Chain   : 0
% 6.25/2.24  #Close   : 0
% 6.25/2.24  
% 6.25/2.24  Ordering : KBO
% 6.25/2.24  
% 6.25/2.24  Simplification rules
% 6.25/2.24  ----------------------
% 6.25/2.24  #Subsume      : 6
% 6.25/2.24  #Demod        : 1340
% 6.25/2.24  #Tautology    : 236
% 6.25/2.24  #SimpNegUnit  : 2
% 6.25/2.24  #BackRed      : 46
% 6.25/2.24  
% 6.25/2.24  #Partial instantiations: 0
% 6.25/2.24  #Strategies tried      : 1
% 6.25/2.24  
% 6.25/2.24  Timing (in seconds)
% 6.25/2.24  ----------------------
% 6.25/2.24  Preprocessing        : 0.37
% 6.25/2.24  Parsing              : 0.21
% 6.25/2.24  CNF conversion       : 0.02
% 6.25/2.24  Main loop            : 1.04
% 6.25/2.24  Inferencing          : 0.34
% 6.25/2.24  Reduction            : 0.41
% 6.25/2.24  Demodulation         : 0.31
% 6.25/2.24  BG Simplification    : 0.03
% 6.25/2.24  Subsumption          : 0.18
% 6.25/2.24  Abstraction          : 0.04
% 6.25/2.24  MUC search           : 0.00
% 6.25/2.24  Cooper               : 0.00
% 6.25/2.24  Total                : 1.47
% 6.25/2.24  Index Insertion      : 0.00
% 6.25/2.24  Index Deletion       : 0.00
% 6.25/2.24  Index Matching       : 0.00
% 6.25/2.24  BG Taut test         : 0.00
%------------------------------------------------------------------------------
