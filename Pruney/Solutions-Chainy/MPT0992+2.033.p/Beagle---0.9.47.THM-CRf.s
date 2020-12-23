%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:13:36 EST 2020

% Result     : Theorem 7.11s
% Output     : CNFRefutation 7.44s
% Verified   : 
% Statistics : Number of formulae       :  199 (2856 expanded)
%              Number of leaves         :   39 ( 881 expanded)
%              Depth                    :   16
%              Number of atoms          :  315 (8866 expanded)
%              Number of equality atoms :   89 (3460 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_partfun1 > k1_relset_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_partfun1,type,(
    k2_partfun1: ( $i * $i * $i * $i ) > $i )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_143,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( r1_tarski(C,A)
         => ( ( B = k1_xboole_0
              & A != k1_xboole_0 )
            | ( v1_funct_1(k2_partfun1(A,B,D,C))
              & v1_funct_2(k2_partfun1(A,B,D,C),C,B)
              & m1_subset_1(k2_partfun1(A,B,D,C),k1_zfmisc_1(k2_zfmisc_1(C,B))) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_funct_2)).

tff(f_73,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_83,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_109,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).

tff(f_69,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(A,k1_relat_1(B))
       => k1_relat_1(k7_relat_1(B,A)) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_relat_1)).

tff(f_123,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => k2_partfun1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_117,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( v1_funct_1(k2_partfun1(A,B,C,D))
        & m1_subset_1(k2_partfun1(A,B,C,D),k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_partfun1)).

tff(f_79,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k7_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).

tff(f_91,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( ( r1_tarski(k1_relat_1(C),A)
          & r1_tarski(k2_relat_1(C),B) )
       => m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_relset_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_35,axiom,(
    ! [A] :
      ( r1_tarski(A,k1_xboole_0)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).

tff(f_63,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k7_relat_1(B,A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_relat_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k1_relat_1(k7_relat_1(B,A)),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_relat_1)).

tff(c_64,plain,(
    r1_tarski('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_66,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_759,plain,(
    ! [C_136,A_137,B_138] :
      ( v1_relat_1(C_136)
      | ~ m1_subset_1(C_136,k1_zfmisc_1(k2_zfmisc_1(A_137,B_138))) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_772,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_66,c_759])).

tff(c_62,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_77,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_62])).

tff(c_68,plain,(
    v1_funct_2('#skF_4','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_3166,plain,(
    ! [A_404,B_405,C_406] :
      ( k1_relset_1(A_404,B_405,C_406) = k1_relat_1(C_406)
      | ~ m1_subset_1(C_406,k1_zfmisc_1(k2_zfmisc_1(A_404,B_405))) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_3185,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_66,c_3166])).

tff(c_3820,plain,(
    ! [B_478,A_479,C_480] :
      ( k1_xboole_0 = B_478
      | k1_relset_1(A_479,B_478,C_480) = A_479
      | ~ v1_funct_2(C_480,A_479,B_478)
      | ~ m1_subset_1(C_480,k1_zfmisc_1(k2_zfmisc_1(A_479,B_478))) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_3833,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1('#skF_1','#skF_2','#skF_4') = '#skF_1'
    | ~ v1_funct_2('#skF_4','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_66,c_3820])).

tff(c_3847,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_3185,c_3833])).

tff(c_3848,plain,(
    k1_relat_1('#skF_4') = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_77,c_3847])).

tff(c_30,plain,(
    ! [B_17,A_16] :
      ( k1_relat_1(k7_relat_1(B_17,A_16)) = A_16
      | ~ r1_tarski(A_16,k1_relat_1(B_17))
      | ~ v1_relat_1(B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_3857,plain,(
    ! [A_16] :
      ( k1_relat_1(k7_relat_1('#skF_4',A_16)) = A_16
      | ~ r1_tarski(A_16,'#skF_1')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3848,c_30])).

tff(c_3863,plain,(
    ! [A_16] :
      ( k1_relat_1(k7_relat_1('#skF_4',A_16)) = A_16
      | ~ r1_tarski(A_16,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_772,c_3857])).

tff(c_70,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_3513,plain,(
    ! [A_448,B_449,C_450,D_451] :
      ( k2_partfun1(A_448,B_449,C_450,D_451) = k7_relat_1(C_450,D_451)
      | ~ m1_subset_1(C_450,k1_zfmisc_1(k2_zfmisc_1(A_448,B_449)))
      | ~ v1_funct_1(C_450) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_3520,plain,(
    ! [D_451] :
      ( k2_partfun1('#skF_1','#skF_2','#skF_4',D_451) = k7_relat_1('#skF_4',D_451)
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_66,c_3513])).

tff(c_3531,plain,(
    ! [D_451] : k2_partfun1('#skF_1','#skF_2','#skF_4',D_451) = k7_relat_1('#skF_4',D_451) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_3520])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_1351,plain,(
    ! [A_205,B_206,C_207] :
      ( k1_relset_1(A_205,B_206,C_207) = k1_relat_1(C_207)
      | ~ m1_subset_1(C_207,k1_zfmisc_1(k2_zfmisc_1(A_205,B_206))) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_1366,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_66,c_1351])).

tff(c_2087,plain,(
    ! [B_301,A_302,C_303] :
      ( k1_xboole_0 = B_301
      | k1_relset_1(A_302,B_301,C_303) = A_302
      | ~ v1_funct_2(C_303,A_302,B_301)
      | ~ m1_subset_1(C_303,k1_zfmisc_1(k2_zfmisc_1(A_302,B_301))) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_2097,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1('#skF_1','#skF_2','#skF_4') = '#skF_1'
    | ~ v1_funct_2('#skF_4','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_66,c_2087])).

tff(c_2108,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_1366,c_2097])).

tff(c_2109,plain,(
    k1_relat_1('#skF_4') = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_77,c_2108])).

tff(c_2118,plain,(
    ! [A_16] :
      ( k1_relat_1(k7_relat_1('#skF_4',A_16)) = A_16
      | ~ r1_tarski(A_16,'#skF_1')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2109,c_30])).

tff(c_2124,plain,(
    ! [A_16] :
      ( k1_relat_1(k7_relat_1('#skF_4',A_16)) = A_16
      | ~ r1_tarski(A_16,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_772,c_2118])).

tff(c_1996,plain,(
    ! [A_291,B_292,C_293,D_294] :
      ( k2_partfun1(A_291,B_292,C_293,D_294) = k7_relat_1(C_293,D_294)
      | ~ m1_subset_1(C_293,k1_zfmisc_1(k2_zfmisc_1(A_291,B_292)))
      | ~ v1_funct_1(C_293) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_2003,plain,(
    ! [D_294] :
      ( k2_partfun1('#skF_1','#skF_2','#skF_4',D_294) = k7_relat_1('#skF_4',D_294)
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_66,c_1996])).

tff(c_2012,plain,(
    ! [D_294] : k2_partfun1('#skF_1','#skF_2','#skF_4',D_294) = k7_relat_1('#skF_4',D_294) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_2003])).

tff(c_2419,plain,(
    ! [A_325,B_326,C_327,D_328] :
      ( m1_subset_1(k2_partfun1(A_325,B_326,C_327,D_328),k1_zfmisc_1(k2_zfmisc_1(A_325,B_326)))
      | ~ m1_subset_1(C_327,k1_zfmisc_1(k2_zfmisc_1(A_325,B_326)))
      | ~ v1_funct_1(C_327) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_2447,plain,(
    ! [D_294] :
      ( m1_subset_1(k7_relat_1('#skF_4',D_294),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
      | ~ v1_funct_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2012,c_2419])).

tff(c_2467,plain,(
    ! [D_329] : m1_subset_1(k7_relat_1('#skF_4',D_329),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_66,c_2447])).

tff(c_34,plain,(
    ! [C_23,B_22,A_21] :
      ( v5_relat_1(C_23,B_22)
      | ~ m1_subset_1(C_23,k1_zfmisc_1(k2_zfmisc_1(A_21,B_22))) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_2506,plain,(
    ! [D_329] : v5_relat_1(k7_relat_1('#skF_4',D_329),'#skF_2') ),
    inference(resolution,[status(thm)],[c_2467,c_34])).

tff(c_24,plain,(
    ! [A_10,B_11] :
      ( v1_relat_1(k7_relat_1(A_10,B_11))
      | ~ v1_relat_1(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_1865,plain,(
    ! [A_274,B_275,C_276,D_277] :
      ( k2_partfun1(A_274,B_275,C_276,D_277) = k7_relat_1(C_276,D_277)
      | ~ m1_subset_1(C_276,k1_zfmisc_1(k2_zfmisc_1(A_274,B_275)))
      | ~ v1_funct_1(C_276) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_1872,plain,(
    ! [D_277] :
      ( k2_partfun1('#skF_1','#skF_2','#skF_4',D_277) = k7_relat_1('#skF_4',D_277)
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_66,c_1865])).

tff(c_1881,plain,(
    ! [D_277] : k2_partfun1('#skF_1','#skF_2','#skF_4',D_277) = k7_relat_1('#skF_4',D_277) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_1872])).

tff(c_1612,plain,(
    ! [C_244,A_245,B_246] :
      ( m1_subset_1(C_244,k1_zfmisc_1(k2_zfmisc_1(A_245,B_246)))
      | ~ r1_tarski(k2_relat_1(C_244),B_246)
      | ~ r1_tarski(k1_relat_1(C_244),A_245)
      | ~ v1_relat_1(C_244) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_735,plain,(
    ! [A_130,B_131,C_132,D_133] :
      ( v1_funct_1(k2_partfun1(A_130,B_131,C_132,D_133))
      | ~ m1_subset_1(C_132,k1_zfmisc_1(k2_zfmisc_1(A_130,B_131)))
      | ~ v1_funct_1(C_132) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_740,plain,(
    ! [D_133] :
      ( v1_funct_1(k2_partfun1('#skF_1','#skF_2','#skF_4',D_133))
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_66,c_735])).

tff(c_748,plain,(
    ! [D_133] : v1_funct_1(k2_partfun1('#skF_1','#skF_2','#skF_4',D_133)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_740])).

tff(c_60,plain,
    ( ~ m1_subset_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2')))
    | ~ v1_funct_2(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),'#skF_3','#skF_2')
    | ~ v1_funct_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_207,plain,(
    ~ v1_funct_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_60])).

tff(c_751,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_748,c_207])).

tff(c_752,plain,
    ( ~ v1_funct_2(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),'#skF_3','#skF_2')
    | ~ m1_subset_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_60])).

tff(c_802,plain,(
    ~ m1_subset_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_752])).

tff(c_1641,plain,
    ( ~ r1_tarski(k2_relat_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3')),'#skF_2')
    | ~ r1_tarski(k1_relat_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3')),'#skF_3')
    | ~ v1_relat_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3')) ),
    inference(resolution,[status(thm)],[c_1612,c_802])).

tff(c_1813,plain,(
    ~ v1_relat_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_1641])).

tff(c_1882,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_4','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1881,c_1813])).

tff(c_1898,plain,(
    ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_24,c_1882])).

tff(c_1902,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_772,c_1898])).

tff(c_1904,plain,(
    v1_relat_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_1641])).

tff(c_2013,plain,(
    v1_relat_1(k7_relat_1('#skF_4','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2012,c_1904])).

tff(c_22,plain,(
    ! [B_9,A_8] :
      ( r1_tarski(k2_relat_1(B_9),A_8)
      | ~ v5_relat_1(B_9,A_8)
      | ~ v1_relat_1(B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_1903,plain,
    ( ~ r1_tarski(k1_relat_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3')),'#skF_3')
    | ~ r1_tarski(k2_relat_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3')),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_1641])).

tff(c_2398,plain,
    ( ~ r1_tarski(k1_relat_1(k7_relat_1('#skF_4','#skF_3')),'#skF_3')
    | ~ r1_tarski(k2_relat_1(k7_relat_1('#skF_4','#skF_3')),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2012,c_2012,c_1903])).

tff(c_2399,plain,(
    ~ r1_tarski(k2_relat_1(k7_relat_1('#skF_4','#skF_3')),'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_2398])).

tff(c_2402,plain,
    ( ~ v5_relat_1(k7_relat_1('#skF_4','#skF_3'),'#skF_2')
    | ~ v1_relat_1(k7_relat_1('#skF_4','#skF_3')) ),
    inference(resolution,[status(thm)],[c_22,c_2399])).

tff(c_2405,plain,(
    ~ v5_relat_1(k7_relat_1('#skF_4','#skF_3'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2013,c_2402])).

tff(c_2516,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2506,c_2405])).

tff(c_2517,plain,(
    ~ r1_tarski(k1_relat_1(k7_relat_1('#skF_4','#skF_3')),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_2398])).

tff(c_2530,plain,
    ( ~ r1_tarski('#skF_3','#skF_3')
    | ~ r1_tarski('#skF_3','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_2124,c_2517])).

tff(c_2536,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_6,c_2530])).

tff(c_2537,plain,(
    ~ v1_funct_2(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),'#skF_3','#skF_2') ),
    inference(splitRight,[status(thm)],[c_752])).

tff(c_3541,plain,(
    ~ v1_funct_2(k7_relat_1('#skF_4','#skF_3'),'#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3531,c_2537])).

tff(c_2538,plain,(
    m1_subset_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_752])).

tff(c_3183,plain,(
    k1_relset_1('#skF_3','#skF_2',k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3')) = k1_relat_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3')) ),
    inference(resolution,[status(thm)],[c_2538,c_3166])).

tff(c_3534,plain,(
    k1_relset_1('#skF_3','#skF_2',k7_relat_1('#skF_4','#skF_3')) = k1_relat_1(k7_relat_1('#skF_4','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3531,c_3531,c_3183])).

tff(c_3540,plain,(
    m1_subset_1(k7_relat_1('#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3531,c_2538])).

tff(c_4004,plain,(
    ! [B_486,C_487,A_488] :
      ( k1_xboole_0 = B_486
      | v1_funct_2(C_487,A_488,B_486)
      | k1_relset_1(A_488,B_486,C_487) != A_488
      | ~ m1_subset_1(C_487,k1_zfmisc_1(k2_zfmisc_1(A_488,B_486))) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_4010,plain,
    ( k1_xboole_0 = '#skF_2'
    | v1_funct_2(k7_relat_1('#skF_4','#skF_3'),'#skF_3','#skF_2')
    | k1_relset_1('#skF_3','#skF_2',k7_relat_1('#skF_4','#skF_3')) != '#skF_3' ),
    inference(resolution,[status(thm)],[c_3540,c_4004])).

tff(c_4026,plain,
    ( k1_xboole_0 = '#skF_2'
    | v1_funct_2(k7_relat_1('#skF_4','#skF_3'),'#skF_3','#skF_2')
    | k1_relat_1(k7_relat_1('#skF_4','#skF_3')) != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3534,c_4010])).

tff(c_4027,plain,(
    k1_relat_1(k7_relat_1('#skF_4','#skF_3')) != '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_3541,c_77,c_4026])).

tff(c_4036,plain,(
    ~ r1_tarski('#skF_3','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_3863,c_4027])).

tff(c_4040,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_4036])).

tff(c_4041,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_62])).

tff(c_14,plain,(
    ! [B_5] : k2_zfmisc_1(k1_xboole_0,B_5) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_4054,plain,(
    ! [B_5] : k2_zfmisc_1('#skF_1',B_5) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4041,c_4041,c_14])).

tff(c_4042,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_62])).

tff(c_4047,plain,(
    '#skF_2' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4041,c_4042])).

tff(c_4053,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4047,c_66])).

tff(c_4055,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4054,c_4053])).

tff(c_5672,plain,(
    ! [A_690,B_691] :
      ( r1_tarski(A_690,B_691)
      | ~ m1_subset_1(A_690,k1_zfmisc_1(B_691)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_5676,plain,(
    r1_tarski('#skF_4','#skF_1') ),
    inference(resolution,[status(thm)],[c_4055,c_5672])).

tff(c_8,plain,(
    ! [A_3] :
      ( k1_xboole_0 = A_3
      | ~ r1_tarski(A_3,k1_xboole_0) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_4079,plain,(
    ! [A_3] :
      ( A_3 = '#skF_1'
      | ~ r1_tarski(A_3,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4041,c_4041,c_8])).

tff(c_5685,plain,(
    '#skF_1' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_5676,c_4079])).

tff(c_4048,plain,(
    v1_funct_2('#skF_4','#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4047,c_68])).

tff(c_5695,plain,(
    v1_funct_2('#skF_4','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5685,c_5685,c_4048])).

tff(c_4107,plain,(
    ! [A_496,B_497] :
      ( r1_tarski(A_496,B_497)
      | ~ m1_subset_1(A_496,k1_zfmisc_1(B_497)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_4111,plain,(
    r1_tarski('#skF_4','#skF_1') ),
    inference(resolution,[status(thm)],[c_4055,c_4107])).

tff(c_4115,plain,(
    '#skF_1' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_4111,c_4079])).

tff(c_4098,plain,(
    ! [B_494,A_495] :
      ( r1_tarski(k7_relat_1(B_494,A_495),B_494)
      | ~ v1_relat_1(B_494) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_4103,plain,(
    ! [A_495] :
      ( k7_relat_1('#skF_1',A_495) = '#skF_1'
      | ~ v1_relat_1('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_4098,c_4079])).

tff(c_4104,plain,(
    ~ v1_relat_1('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_4103])).

tff(c_4118,plain,(
    ~ v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4115,c_4104])).

tff(c_4121,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4115,c_4055])).

tff(c_12,plain,(
    ! [A_4] : k2_zfmisc_1(A_4,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_4063,plain,(
    ! [A_4] : k2_zfmisc_1(A_4,'#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4041,c_4041,c_12])).

tff(c_4122,plain,(
    ! [A_4] : k2_zfmisc_1(A_4,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4115,c_4115,c_4063])).

tff(c_4188,plain,(
    ! [C_503,A_504,B_505] :
      ( v1_relat_1(C_503)
      | ~ m1_subset_1(C_503,k1_zfmisc_1(k2_zfmisc_1(A_504,B_505))) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_4198,plain,(
    ! [C_506] :
      ( v1_relat_1(C_506)
      | ~ m1_subset_1(C_506,k1_zfmisc_1('#skF_4')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4122,c_4188])).

tff(c_4201,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_4121,c_4198])).

tff(c_4209,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4118,c_4201])).

tff(c_4211,plain,(
    v1_relat_1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_4103])).

tff(c_5689,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5685,c_4211])).

tff(c_4210,plain,(
    ! [A_495] : k7_relat_1('#skF_1',A_495) = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_4103])).

tff(c_5688,plain,(
    ! [A_495] : k7_relat_1('#skF_4',A_495) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5685,c_5685,c_4210])).

tff(c_9591,plain,(
    ! [B_1012,A_1013] :
      ( r1_tarski(k1_relat_1(k7_relat_1(B_1012,A_1013)),A_1013)
      | ~ v1_relat_1(B_1012) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_9598,plain,(
    ! [A_495] :
      ( r1_tarski(k1_relat_1('#skF_4'),A_495)
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5688,c_9591])).

tff(c_9602,plain,(
    ! [A_1014] : r1_tarski(k1_relat_1('#skF_4'),A_1014) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5689,c_9598])).

tff(c_5691,plain,(
    ! [A_3] :
      ( A_3 = '#skF_4'
      | ~ r1_tarski(A_3,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5685,c_5685,c_4079])).

tff(c_9607,plain,(
    k1_relat_1('#skF_4') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_9602,c_5691])).

tff(c_9601,plain,(
    ! [A_495] : r1_tarski(k1_relat_1('#skF_4'),A_495) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5689,c_9598])).

tff(c_9608,plain,(
    ! [A_495] : r1_tarski('#skF_4',A_495) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9607,c_9601])).

tff(c_5787,plain,(
    ! [B_700,A_701] :
      ( r1_tarski(k1_relat_1(k7_relat_1(B_700,A_701)),A_701)
      | ~ v1_relat_1(B_700) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_5794,plain,(
    ! [A_495] :
      ( r1_tarski(k1_relat_1('#skF_4'),A_495)
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5688,c_5787])).

tff(c_5798,plain,(
    ! [A_702] : r1_tarski(k1_relat_1('#skF_4'),A_702) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5689,c_5794])).

tff(c_5803,plain,(
    k1_relat_1('#skF_4') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_5798,c_5691])).

tff(c_5797,plain,(
    ! [A_495] : r1_tarski(k1_relat_1('#skF_4'),A_495) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5689,c_5794])).

tff(c_5804,plain,(
    ! [A_495] : r1_tarski('#skF_4',A_495) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5803,c_5797])).

tff(c_18,plain,(
    ! [A_6,B_7] :
      ( m1_subset_1(A_6,k1_zfmisc_1(B_7))
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_6855,plain,(
    ! [A_835,B_836,C_837,D_838] :
      ( k2_partfun1(A_835,B_836,C_837,D_838) = k7_relat_1(C_837,D_838)
      | ~ m1_subset_1(C_837,k1_zfmisc_1(k2_zfmisc_1(A_835,B_836)))
      | ~ v1_funct_1(C_837) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_9546,plain,(
    ! [A_1008,B_1009,A_1010,D_1011] :
      ( k2_partfun1(A_1008,B_1009,A_1010,D_1011) = k7_relat_1(A_1010,D_1011)
      | ~ v1_funct_1(A_1010)
      | ~ r1_tarski(A_1010,k2_zfmisc_1(A_1008,B_1009)) ) ),
    inference(resolution,[status(thm)],[c_18,c_6855])).

tff(c_9554,plain,(
    ! [A_1008,B_1009,D_1011] :
      ( k2_partfun1(A_1008,B_1009,'#skF_4',D_1011) = k7_relat_1('#skF_4',D_1011)
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_5804,c_9546])).

tff(c_9572,plain,(
    ! [A_1008,B_1009,D_1011] : k2_partfun1(A_1008,B_1009,'#skF_4',D_1011) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_5688,c_9554])).

tff(c_4231,plain,(
    ! [A_508,B_509] :
      ( r1_tarski(A_508,B_509)
      | ~ m1_subset_1(A_508,k1_zfmisc_1(B_509)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_4235,plain,(
    r1_tarski('#skF_4','#skF_1') ),
    inference(resolution,[status(thm)],[c_4055,c_4231])).

tff(c_4239,plain,(
    '#skF_1' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_4235,c_4079])).

tff(c_4246,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4239,c_4055])).

tff(c_4248,plain,(
    ! [B_5] : k2_zfmisc_1('#skF_4',B_5) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4239,c_4239,c_4054])).

tff(c_5224,plain,(
    ! [A_630,B_631,C_632,D_633] :
      ( v1_funct_1(k2_partfun1(A_630,B_631,C_632,D_633))
      | ~ m1_subset_1(C_632,k1_zfmisc_1(k2_zfmisc_1(A_630,B_631)))
      | ~ v1_funct_1(C_632) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_5640,plain,(
    ! [B_686,C_687,D_688] :
      ( v1_funct_1(k2_partfun1('#skF_4',B_686,C_687,D_688))
      | ~ m1_subset_1(C_687,k1_zfmisc_1('#skF_4'))
      | ~ v1_funct_1(C_687) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4248,c_5224])).

tff(c_5642,plain,(
    ! [B_686,D_688] :
      ( v1_funct_1(k2_partfun1('#skF_4',B_686,'#skF_4',D_688))
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_4246,c_5640])).

tff(c_5648,plain,(
    ! [B_686,D_688] : v1_funct_1(k2_partfun1('#skF_4',B_686,'#skF_4',D_688)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_5642])).

tff(c_4080,plain,(
    ! [A_491] :
      ( A_491 = '#skF_1'
      | ~ r1_tarski(A_491,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4041,c_4041,c_8])).

tff(c_4090,plain,(
    '#skF_3' = '#skF_1' ),
    inference(resolution,[status(thm)],[c_64,c_4080])).

tff(c_4212,plain,
    ( ~ m1_subset_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1'),k1_zfmisc_1('#skF_1'))
    | ~ v1_funct_2(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1'),'#skF_1','#skF_1')
    | ~ v1_funct_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4047,c_4090,c_4047,c_4047,c_4090,c_4090,c_4047,c_4054,c_4090,c_4090,c_60])).

tff(c_4213,plain,(
    ~ v1_funct_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_4212])).

tff(c_4241,plain,(
    ~ v1_funct_1(k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4239,c_4239,c_4239,c_4213])).

tff(c_5652,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_5648,c_4241])).

tff(c_5653,plain,
    ( ~ v1_funct_2(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1'),'#skF_1','#skF_1')
    | ~ m1_subset_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1'),k1_zfmisc_1('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_4212])).

tff(c_5785,plain,
    ( ~ v1_funct_2(k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_4'),'#skF_4','#skF_4')
    | ~ m1_subset_1(k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_4'),k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5685,c_5685,c_5685,c_5685,c_5685,c_5685,c_5685,c_5685,c_5685,c_5653])).

tff(c_5786,plain,(
    ~ m1_subset_1(k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_4'),k1_zfmisc_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_5785])).

tff(c_5865,plain,(
    ~ r1_tarski(k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_4'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_18,c_5786])).

tff(c_9581,plain,(
    ~ r1_tarski('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_9572,c_5865])).

tff(c_9588,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_9581])).

tff(c_9590,plain,(
    m1_subset_1(k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_4'),k1_zfmisc_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_5785])).

tff(c_16,plain,(
    ! [A_6,B_7] :
      ( r1_tarski(A_6,B_7)
      | ~ m1_subset_1(A_6,k1_zfmisc_1(B_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_9708,plain,(
    r1_tarski(k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_4'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_9590,c_16])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_9746,plain,
    ( k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_4') = '#skF_4'
    | ~ r1_tarski('#skF_4',k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_4')) ),
    inference(resolution,[status(thm)],[c_9708,c_2])).

tff(c_9754,plain,(
    k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9608,c_9746])).

tff(c_9589,plain,(
    ~ v1_funct_2(k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_4'),'#skF_4','#skF_4') ),
    inference(splitRight,[status(thm)],[c_5785])).

tff(c_9759,plain,(
    ~ v1_funct_2('#skF_4','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_9754,c_9589])).

tff(c_9766,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_5695,c_9759])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n025.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 18:29:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.11/2.59  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.44/2.63  
% 7.44/2.63  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.44/2.63  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_partfun1 > k1_relset_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 7.44/2.63  
% 7.44/2.63  %Foreground sorts:
% 7.44/2.63  
% 7.44/2.63  
% 7.44/2.63  %Background operators:
% 7.44/2.63  
% 7.44/2.63  
% 7.44/2.63  %Foreground operators:
% 7.44/2.63  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 7.44/2.63  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.44/2.63  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 7.44/2.63  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 7.44/2.63  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.44/2.63  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 7.44/2.63  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 7.44/2.63  tff('#skF_2', type, '#skF_2': $i).
% 7.44/2.63  tff('#skF_3', type, '#skF_3': $i).
% 7.44/2.63  tff('#skF_1', type, '#skF_1': $i).
% 7.44/2.63  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 7.44/2.63  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 7.44/2.63  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 7.44/2.63  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.44/2.63  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 7.44/2.63  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 7.44/2.63  tff('#skF_4', type, '#skF_4': $i).
% 7.44/2.63  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.44/2.63  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 7.44/2.63  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 7.44/2.63  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 7.44/2.63  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 7.44/2.63  
% 7.44/2.66  tff(f_143, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r1_tarski(C, A) => (((B = k1_xboole_0) & ~(A = k1_xboole_0)) | ((v1_funct_1(k2_partfun1(A, B, D, C)) & v1_funct_2(k2_partfun1(A, B, D, C), C, B)) & m1_subset_1(k2_partfun1(A, B, D, C), k1_zfmisc_1(k2_zfmisc_1(C, B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_funct_2)).
% 7.44/2.66  tff(f_73, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 7.44/2.66  tff(f_83, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 7.44/2.66  tff(f_109, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 7.44/2.66  tff(f_69, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(A, k1_relat_1(B)) => (k1_relat_1(k7_relat_1(B, A)) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_relat_1)).
% 7.44/2.66  tff(f_123, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (k2_partfun1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_partfun1)).
% 7.44/2.66  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 7.44/2.66  tff(f_117, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (v1_funct_1(k2_partfun1(A, B, C, D)) & m1_subset_1(k2_partfun1(A, B, C, D), k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_partfun1)).
% 7.44/2.66  tff(f_79, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 7.44/2.66  tff(f_55, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k7_relat_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 7.44/2.66  tff(f_91, axiom, (![A, B, C]: (v1_relat_1(C) => ((r1_tarski(k1_relat_1(C), A) & r1_tarski(k2_relat_1(C), B)) => m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_relset_1)).
% 7.44/2.66  tff(f_51, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 7.44/2.66  tff(f_41, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 7.44/2.66  tff(f_45, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 7.44/2.66  tff(f_35, axiom, (![A]: (r1_tarski(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_1)).
% 7.44/2.66  tff(f_63, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k7_relat_1(B, A), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t88_relat_1)).
% 7.44/2.66  tff(f_59, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k7_relat_1(B, A)), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t87_relat_1)).
% 7.44/2.66  tff(c_64, plain, (r1_tarski('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_143])).
% 7.44/2.66  tff(c_66, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_143])).
% 7.44/2.66  tff(c_759, plain, (![C_136, A_137, B_138]: (v1_relat_1(C_136) | ~m1_subset_1(C_136, k1_zfmisc_1(k2_zfmisc_1(A_137, B_138))))), inference(cnfTransformation, [status(thm)], [f_73])).
% 7.44/2.66  tff(c_772, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_66, c_759])).
% 7.44/2.66  tff(c_62, plain, (k1_xboole_0='#skF_1' | k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_143])).
% 7.44/2.66  tff(c_77, plain, (k1_xboole_0!='#skF_2'), inference(splitLeft, [status(thm)], [c_62])).
% 7.44/2.66  tff(c_68, plain, (v1_funct_2('#skF_4', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_143])).
% 7.44/2.66  tff(c_3166, plain, (![A_404, B_405, C_406]: (k1_relset_1(A_404, B_405, C_406)=k1_relat_1(C_406) | ~m1_subset_1(C_406, k1_zfmisc_1(k2_zfmisc_1(A_404, B_405))))), inference(cnfTransformation, [status(thm)], [f_83])).
% 7.44/2.66  tff(c_3185, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_66, c_3166])).
% 7.44/2.66  tff(c_3820, plain, (![B_478, A_479, C_480]: (k1_xboole_0=B_478 | k1_relset_1(A_479, B_478, C_480)=A_479 | ~v1_funct_2(C_480, A_479, B_478) | ~m1_subset_1(C_480, k1_zfmisc_1(k2_zfmisc_1(A_479, B_478))))), inference(cnfTransformation, [status(thm)], [f_109])).
% 7.44/2.66  tff(c_3833, plain, (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', '#skF_4')='#skF_1' | ~v1_funct_2('#skF_4', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_66, c_3820])).
% 7.44/2.66  tff(c_3847, plain, (k1_xboole_0='#skF_2' | k1_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_68, c_3185, c_3833])).
% 7.44/2.66  tff(c_3848, plain, (k1_relat_1('#skF_4')='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_77, c_3847])).
% 7.44/2.66  tff(c_30, plain, (![B_17, A_16]: (k1_relat_1(k7_relat_1(B_17, A_16))=A_16 | ~r1_tarski(A_16, k1_relat_1(B_17)) | ~v1_relat_1(B_17))), inference(cnfTransformation, [status(thm)], [f_69])).
% 7.44/2.66  tff(c_3857, plain, (![A_16]: (k1_relat_1(k7_relat_1('#skF_4', A_16))=A_16 | ~r1_tarski(A_16, '#skF_1') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_3848, c_30])).
% 7.44/2.66  tff(c_3863, plain, (![A_16]: (k1_relat_1(k7_relat_1('#skF_4', A_16))=A_16 | ~r1_tarski(A_16, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_772, c_3857])).
% 7.44/2.66  tff(c_70, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_143])).
% 7.44/2.66  tff(c_3513, plain, (![A_448, B_449, C_450, D_451]: (k2_partfun1(A_448, B_449, C_450, D_451)=k7_relat_1(C_450, D_451) | ~m1_subset_1(C_450, k1_zfmisc_1(k2_zfmisc_1(A_448, B_449))) | ~v1_funct_1(C_450))), inference(cnfTransformation, [status(thm)], [f_123])).
% 7.44/2.66  tff(c_3520, plain, (![D_451]: (k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_451)=k7_relat_1('#skF_4', D_451) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_66, c_3513])).
% 7.44/2.66  tff(c_3531, plain, (![D_451]: (k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_451)=k7_relat_1('#skF_4', D_451))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_3520])).
% 7.44/2.66  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 7.44/2.66  tff(c_1351, plain, (![A_205, B_206, C_207]: (k1_relset_1(A_205, B_206, C_207)=k1_relat_1(C_207) | ~m1_subset_1(C_207, k1_zfmisc_1(k2_zfmisc_1(A_205, B_206))))), inference(cnfTransformation, [status(thm)], [f_83])).
% 7.44/2.66  tff(c_1366, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_66, c_1351])).
% 7.44/2.66  tff(c_2087, plain, (![B_301, A_302, C_303]: (k1_xboole_0=B_301 | k1_relset_1(A_302, B_301, C_303)=A_302 | ~v1_funct_2(C_303, A_302, B_301) | ~m1_subset_1(C_303, k1_zfmisc_1(k2_zfmisc_1(A_302, B_301))))), inference(cnfTransformation, [status(thm)], [f_109])).
% 7.44/2.66  tff(c_2097, plain, (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', '#skF_4')='#skF_1' | ~v1_funct_2('#skF_4', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_66, c_2087])).
% 7.44/2.66  tff(c_2108, plain, (k1_xboole_0='#skF_2' | k1_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_68, c_1366, c_2097])).
% 7.44/2.66  tff(c_2109, plain, (k1_relat_1('#skF_4')='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_77, c_2108])).
% 7.44/2.66  tff(c_2118, plain, (![A_16]: (k1_relat_1(k7_relat_1('#skF_4', A_16))=A_16 | ~r1_tarski(A_16, '#skF_1') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_2109, c_30])).
% 7.44/2.66  tff(c_2124, plain, (![A_16]: (k1_relat_1(k7_relat_1('#skF_4', A_16))=A_16 | ~r1_tarski(A_16, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_772, c_2118])).
% 7.44/2.66  tff(c_1996, plain, (![A_291, B_292, C_293, D_294]: (k2_partfun1(A_291, B_292, C_293, D_294)=k7_relat_1(C_293, D_294) | ~m1_subset_1(C_293, k1_zfmisc_1(k2_zfmisc_1(A_291, B_292))) | ~v1_funct_1(C_293))), inference(cnfTransformation, [status(thm)], [f_123])).
% 7.44/2.66  tff(c_2003, plain, (![D_294]: (k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_294)=k7_relat_1('#skF_4', D_294) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_66, c_1996])).
% 7.44/2.66  tff(c_2012, plain, (![D_294]: (k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_294)=k7_relat_1('#skF_4', D_294))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_2003])).
% 7.44/2.66  tff(c_2419, plain, (![A_325, B_326, C_327, D_328]: (m1_subset_1(k2_partfun1(A_325, B_326, C_327, D_328), k1_zfmisc_1(k2_zfmisc_1(A_325, B_326))) | ~m1_subset_1(C_327, k1_zfmisc_1(k2_zfmisc_1(A_325, B_326))) | ~v1_funct_1(C_327))), inference(cnfTransformation, [status(thm)], [f_117])).
% 7.44/2.66  tff(c_2447, plain, (![D_294]: (m1_subset_1(k7_relat_1('#skF_4', D_294), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_2012, c_2419])).
% 7.44/2.66  tff(c_2467, plain, (![D_329]: (m1_subset_1(k7_relat_1('#skF_4', D_329), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_66, c_2447])).
% 7.44/2.66  tff(c_34, plain, (![C_23, B_22, A_21]: (v5_relat_1(C_23, B_22) | ~m1_subset_1(C_23, k1_zfmisc_1(k2_zfmisc_1(A_21, B_22))))), inference(cnfTransformation, [status(thm)], [f_79])).
% 7.44/2.66  tff(c_2506, plain, (![D_329]: (v5_relat_1(k7_relat_1('#skF_4', D_329), '#skF_2'))), inference(resolution, [status(thm)], [c_2467, c_34])).
% 7.44/2.66  tff(c_24, plain, (![A_10, B_11]: (v1_relat_1(k7_relat_1(A_10, B_11)) | ~v1_relat_1(A_10))), inference(cnfTransformation, [status(thm)], [f_55])).
% 7.44/2.66  tff(c_1865, plain, (![A_274, B_275, C_276, D_277]: (k2_partfun1(A_274, B_275, C_276, D_277)=k7_relat_1(C_276, D_277) | ~m1_subset_1(C_276, k1_zfmisc_1(k2_zfmisc_1(A_274, B_275))) | ~v1_funct_1(C_276))), inference(cnfTransformation, [status(thm)], [f_123])).
% 7.44/2.66  tff(c_1872, plain, (![D_277]: (k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_277)=k7_relat_1('#skF_4', D_277) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_66, c_1865])).
% 7.44/2.66  tff(c_1881, plain, (![D_277]: (k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_277)=k7_relat_1('#skF_4', D_277))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_1872])).
% 7.44/2.66  tff(c_1612, plain, (![C_244, A_245, B_246]: (m1_subset_1(C_244, k1_zfmisc_1(k2_zfmisc_1(A_245, B_246))) | ~r1_tarski(k2_relat_1(C_244), B_246) | ~r1_tarski(k1_relat_1(C_244), A_245) | ~v1_relat_1(C_244))), inference(cnfTransformation, [status(thm)], [f_91])).
% 7.44/2.66  tff(c_735, plain, (![A_130, B_131, C_132, D_133]: (v1_funct_1(k2_partfun1(A_130, B_131, C_132, D_133)) | ~m1_subset_1(C_132, k1_zfmisc_1(k2_zfmisc_1(A_130, B_131))) | ~v1_funct_1(C_132))), inference(cnfTransformation, [status(thm)], [f_117])).
% 7.44/2.66  tff(c_740, plain, (![D_133]: (v1_funct_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_133)) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_66, c_735])).
% 7.44/2.66  tff(c_748, plain, (![D_133]: (v1_funct_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_133)))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_740])).
% 7.44/2.66  tff(c_60, plain, (~m1_subset_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2'))) | ~v1_funct_2(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), '#skF_3', '#skF_2') | ~v1_funct_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_143])).
% 7.44/2.66  tff(c_207, plain, (~v1_funct_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'))), inference(splitLeft, [status(thm)], [c_60])).
% 7.44/2.66  tff(c_751, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_748, c_207])).
% 7.44/2.66  tff(c_752, plain, (~v1_funct_2(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), '#skF_3', '#skF_2') | ~m1_subset_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(splitRight, [status(thm)], [c_60])).
% 7.44/2.66  tff(c_802, plain, (~m1_subset_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(splitLeft, [status(thm)], [c_752])).
% 7.44/2.66  tff(c_1641, plain, (~r1_tarski(k2_relat_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3')), '#skF_2') | ~r1_tarski(k1_relat_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3')), '#skF_3') | ~v1_relat_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'))), inference(resolution, [status(thm)], [c_1612, c_802])).
% 7.44/2.66  tff(c_1813, plain, (~v1_relat_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'))), inference(splitLeft, [status(thm)], [c_1641])).
% 7.44/2.66  tff(c_1882, plain, (~v1_relat_1(k7_relat_1('#skF_4', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_1881, c_1813])).
% 7.44/2.66  tff(c_1898, plain, (~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_24, c_1882])).
% 7.44/2.66  tff(c_1902, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_772, c_1898])).
% 7.44/2.66  tff(c_1904, plain, (v1_relat_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'))), inference(splitRight, [status(thm)], [c_1641])).
% 7.44/2.66  tff(c_2013, plain, (v1_relat_1(k7_relat_1('#skF_4', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_2012, c_1904])).
% 7.44/2.66  tff(c_22, plain, (![B_9, A_8]: (r1_tarski(k2_relat_1(B_9), A_8) | ~v5_relat_1(B_9, A_8) | ~v1_relat_1(B_9))), inference(cnfTransformation, [status(thm)], [f_51])).
% 7.44/2.66  tff(c_1903, plain, (~r1_tarski(k1_relat_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3')), '#skF_3') | ~r1_tarski(k2_relat_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3')), '#skF_2')), inference(splitRight, [status(thm)], [c_1641])).
% 7.44/2.66  tff(c_2398, plain, (~r1_tarski(k1_relat_1(k7_relat_1('#skF_4', '#skF_3')), '#skF_3') | ~r1_tarski(k2_relat_1(k7_relat_1('#skF_4', '#skF_3')), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2012, c_2012, c_1903])).
% 7.44/2.66  tff(c_2399, plain, (~r1_tarski(k2_relat_1(k7_relat_1('#skF_4', '#skF_3')), '#skF_2')), inference(splitLeft, [status(thm)], [c_2398])).
% 7.44/2.66  tff(c_2402, plain, (~v5_relat_1(k7_relat_1('#skF_4', '#skF_3'), '#skF_2') | ~v1_relat_1(k7_relat_1('#skF_4', '#skF_3'))), inference(resolution, [status(thm)], [c_22, c_2399])).
% 7.44/2.66  tff(c_2405, plain, (~v5_relat_1(k7_relat_1('#skF_4', '#skF_3'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2013, c_2402])).
% 7.44/2.66  tff(c_2516, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2506, c_2405])).
% 7.44/2.66  tff(c_2517, plain, (~r1_tarski(k1_relat_1(k7_relat_1('#skF_4', '#skF_3')), '#skF_3')), inference(splitRight, [status(thm)], [c_2398])).
% 7.44/2.66  tff(c_2530, plain, (~r1_tarski('#skF_3', '#skF_3') | ~r1_tarski('#skF_3', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_2124, c_2517])).
% 7.44/2.66  tff(c_2536, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_64, c_6, c_2530])).
% 7.44/2.66  tff(c_2537, plain, (~v1_funct_2(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), '#skF_3', '#skF_2')), inference(splitRight, [status(thm)], [c_752])).
% 7.44/2.66  tff(c_3541, plain, (~v1_funct_2(k7_relat_1('#skF_4', '#skF_3'), '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_3531, c_2537])).
% 7.44/2.66  tff(c_2538, plain, (m1_subset_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(splitRight, [status(thm)], [c_752])).
% 7.44/2.66  tff(c_3183, plain, (k1_relset_1('#skF_3', '#skF_2', k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'))=k1_relat_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'))), inference(resolution, [status(thm)], [c_2538, c_3166])).
% 7.44/2.66  tff(c_3534, plain, (k1_relset_1('#skF_3', '#skF_2', k7_relat_1('#skF_4', '#skF_3'))=k1_relat_1(k7_relat_1('#skF_4', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_3531, c_3531, c_3183])).
% 7.44/2.66  tff(c_3540, plain, (m1_subset_1(k7_relat_1('#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_3531, c_2538])).
% 7.44/2.66  tff(c_4004, plain, (![B_486, C_487, A_488]: (k1_xboole_0=B_486 | v1_funct_2(C_487, A_488, B_486) | k1_relset_1(A_488, B_486, C_487)!=A_488 | ~m1_subset_1(C_487, k1_zfmisc_1(k2_zfmisc_1(A_488, B_486))))), inference(cnfTransformation, [status(thm)], [f_109])).
% 7.44/2.66  tff(c_4010, plain, (k1_xboole_0='#skF_2' | v1_funct_2(k7_relat_1('#skF_4', '#skF_3'), '#skF_3', '#skF_2') | k1_relset_1('#skF_3', '#skF_2', k7_relat_1('#skF_4', '#skF_3'))!='#skF_3'), inference(resolution, [status(thm)], [c_3540, c_4004])).
% 7.44/2.66  tff(c_4026, plain, (k1_xboole_0='#skF_2' | v1_funct_2(k7_relat_1('#skF_4', '#skF_3'), '#skF_3', '#skF_2') | k1_relat_1(k7_relat_1('#skF_4', '#skF_3'))!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_3534, c_4010])).
% 7.44/2.66  tff(c_4027, plain, (k1_relat_1(k7_relat_1('#skF_4', '#skF_3'))!='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_3541, c_77, c_4026])).
% 7.44/2.66  tff(c_4036, plain, (~r1_tarski('#skF_3', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_3863, c_4027])).
% 7.44/2.66  tff(c_4040, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_64, c_4036])).
% 7.44/2.66  tff(c_4041, plain, (k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_62])).
% 7.44/2.66  tff(c_14, plain, (![B_5]: (k2_zfmisc_1(k1_xboole_0, B_5)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_41])).
% 7.44/2.66  tff(c_4054, plain, (![B_5]: (k2_zfmisc_1('#skF_1', B_5)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_4041, c_4041, c_14])).
% 7.44/2.66  tff(c_4042, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_62])).
% 7.44/2.66  tff(c_4047, plain, ('#skF_2'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_4041, c_4042])).
% 7.44/2.66  tff(c_4053, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_4047, c_66])).
% 7.44/2.66  tff(c_4055, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_4054, c_4053])).
% 7.44/2.66  tff(c_5672, plain, (![A_690, B_691]: (r1_tarski(A_690, B_691) | ~m1_subset_1(A_690, k1_zfmisc_1(B_691)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 7.44/2.66  tff(c_5676, plain, (r1_tarski('#skF_4', '#skF_1')), inference(resolution, [status(thm)], [c_4055, c_5672])).
% 7.44/2.66  tff(c_8, plain, (![A_3]: (k1_xboole_0=A_3 | ~r1_tarski(A_3, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_35])).
% 7.44/2.66  tff(c_4079, plain, (![A_3]: (A_3='#skF_1' | ~r1_tarski(A_3, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_4041, c_4041, c_8])).
% 7.44/2.66  tff(c_5685, plain, ('#skF_1'='#skF_4'), inference(resolution, [status(thm)], [c_5676, c_4079])).
% 7.44/2.66  tff(c_4048, plain, (v1_funct_2('#skF_4', '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_4047, c_68])).
% 7.44/2.66  tff(c_5695, plain, (v1_funct_2('#skF_4', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_5685, c_5685, c_4048])).
% 7.44/2.66  tff(c_4107, plain, (![A_496, B_497]: (r1_tarski(A_496, B_497) | ~m1_subset_1(A_496, k1_zfmisc_1(B_497)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 7.44/2.66  tff(c_4111, plain, (r1_tarski('#skF_4', '#skF_1')), inference(resolution, [status(thm)], [c_4055, c_4107])).
% 7.44/2.66  tff(c_4115, plain, ('#skF_1'='#skF_4'), inference(resolution, [status(thm)], [c_4111, c_4079])).
% 7.44/2.66  tff(c_4098, plain, (![B_494, A_495]: (r1_tarski(k7_relat_1(B_494, A_495), B_494) | ~v1_relat_1(B_494))), inference(cnfTransformation, [status(thm)], [f_63])).
% 7.44/2.66  tff(c_4103, plain, (![A_495]: (k7_relat_1('#skF_1', A_495)='#skF_1' | ~v1_relat_1('#skF_1'))), inference(resolution, [status(thm)], [c_4098, c_4079])).
% 7.44/2.66  tff(c_4104, plain, (~v1_relat_1('#skF_1')), inference(splitLeft, [status(thm)], [c_4103])).
% 7.44/2.66  tff(c_4118, plain, (~v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_4115, c_4104])).
% 7.44/2.66  tff(c_4121, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_4115, c_4055])).
% 7.44/2.66  tff(c_12, plain, (![A_4]: (k2_zfmisc_1(A_4, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_41])).
% 7.44/2.66  tff(c_4063, plain, (![A_4]: (k2_zfmisc_1(A_4, '#skF_1')='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_4041, c_4041, c_12])).
% 7.44/2.66  tff(c_4122, plain, (![A_4]: (k2_zfmisc_1(A_4, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_4115, c_4115, c_4063])).
% 7.44/2.66  tff(c_4188, plain, (![C_503, A_504, B_505]: (v1_relat_1(C_503) | ~m1_subset_1(C_503, k1_zfmisc_1(k2_zfmisc_1(A_504, B_505))))), inference(cnfTransformation, [status(thm)], [f_73])).
% 7.44/2.66  tff(c_4198, plain, (![C_506]: (v1_relat_1(C_506) | ~m1_subset_1(C_506, k1_zfmisc_1('#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_4122, c_4188])).
% 7.44/2.66  tff(c_4201, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_4121, c_4198])).
% 7.44/2.66  tff(c_4209, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4118, c_4201])).
% 7.44/2.66  tff(c_4211, plain, (v1_relat_1('#skF_1')), inference(splitRight, [status(thm)], [c_4103])).
% 7.44/2.66  tff(c_5689, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_5685, c_4211])).
% 7.44/2.66  tff(c_4210, plain, (![A_495]: (k7_relat_1('#skF_1', A_495)='#skF_1')), inference(splitRight, [status(thm)], [c_4103])).
% 7.44/2.66  tff(c_5688, plain, (![A_495]: (k7_relat_1('#skF_4', A_495)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_5685, c_5685, c_4210])).
% 7.44/2.66  tff(c_9591, plain, (![B_1012, A_1013]: (r1_tarski(k1_relat_1(k7_relat_1(B_1012, A_1013)), A_1013) | ~v1_relat_1(B_1012))), inference(cnfTransformation, [status(thm)], [f_59])).
% 7.44/2.66  tff(c_9598, plain, (![A_495]: (r1_tarski(k1_relat_1('#skF_4'), A_495) | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_5688, c_9591])).
% 7.44/2.66  tff(c_9602, plain, (![A_1014]: (r1_tarski(k1_relat_1('#skF_4'), A_1014))), inference(demodulation, [status(thm), theory('equality')], [c_5689, c_9598])).
% 7.44/2.66  tff(c_5691, plain, (![A_3]: (A_3='#skF_4' | ~r1_tarski(A_3, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_5685, c_5685, c_4079])).
% 7.44/2.66  tff(c_9607, plain, (k1_relat_1('#skF_4')='#skF_4'), inference(resolution, [status(thm)], [c_9602, c_5691])).
% 7.44/2.66  tff(c_9601, plain, (![A_495]: (r1_tarski(k1_relat_1('#skF_4'), A_495))), inference(demodulation, [status(thm), theory('equality')], [c_5689, c_9598])).
% 7.44/2.66  tff(c_9608, plain, (![A_495]: (r1_tarski('#skF_4', A_495))), inference(demodulation, [status(thm), theory('equality')], [c_9607, c_9601])).
% 7.44/2.66  tff(c_5787, plain, (![B_700, A_701]: (r1_tarski(k1_relat_1(k7_relat_1(B_700, A_701)), A_701) | ~v1_relat_1(B_700))), inference(cnfTransformation, [status(thm)], [f_59])).
% 7.44/2.66  tff(c_5794, plain, (![A_495]: (r1_tarski(k1_relat_1('#skF_4'), A_495) | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_5688, c_5787])).
% 7.44/2.66  tff(c_5798, plain, (![A_702]: (r1_tarski(k1_relat_1('#skF_4'), A_702))), inference(demodulation, [status(thm), theory('equality')], [c_5689, c_5794])).
% 7.44/2.66  tff(c_5803, plain, (k1_relat_1('#skF_4')='#skF_4'), inference(resolution, [status(thm)], [c_5798, c_5691])).
% 7.44/2.66  tff(c_5797, plain, (![A_495]: (r1_tarski(k1_relat_1('#skF_4'), A_495))), inference(demodulation, [status(thm), theory('equality')], [c_5689, c_5794])).
% 7.44/2.66  tff(c_5804, plain, (![A_495]: (r1_tarski('#skF_4', A_495))), inference(demodulation, [status(thm), theory('equality')], [c_5803, c_5797])).
% 7.44/2.66  tff(c_18, plain, (![A_6, B_7]: (m1_subset_1(A_6, k1_zfmisc_1(B_7)) | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_45])).
% 7.44/2.66  tff(c_6855, plain, (![A_835, B_836, C_837, D_838]: (k2_partfun1(A_835, B_836, C_837, D_838)=k7_relat_1(C_837, D_838) | ~m1_subset_1(C_837, k1_zfmisc_1(k2_zfmisc_1(A_835, B_836))) | ~v1_funct_1(C_837))), inference(cnfTransformation, [status(thm)], [f_123])).
% 7.44/2.66  tff(c_9546, plain, (![A_1008, B_1009, A_1010, D_1011]: (k2_partfun1(A_1008, B_1009, A_1010, D_1011)=k7_relat_1(A_1010, D_1011) | ~v1_funct_1(A_1010) | ~r1_tarski(A_1010, k2_zfmisc_1(A_1008, B_1009)))), inference(resolution, [status(thm)], [c_18, c_6855])).
% 7.44/2.66  tff(c_9554, plain, (![A_1008, B_1009, D_1011]: (k2_partfun1(A_1008, B_1009, '#skF_4', D_1011)=k7_relat_1('#skF_4', D_1011) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_5804, c_9546])).
% 7.44/2.66  tff(c_9572, plain, (![A_1008, B_1009, D_1011]: (k2_partfun1(A_1008, B_1009, '#skF_4', D_1011)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_5688, c_9554])).
% 7.44/2.66  tff(c_4231, plain, (![A_508, B_509]: (r1_tarski(A_508, B_509) | ~m1_subset_1(A_508, k1_zfmisc_1(B_509)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 7.44/2.66  tff(c_4235, plain, (r1_tarski('#skF_4', '#skF_1')), inference(resolution, [status(thm)], [c_4055, c_4231])).
% 7.44/2.66  tff(c_4239, plain, ('#skF_1'='#skF_4'), inference(resolution, [status(thm)], [c_4235, c_4079])).
% 7.44/2.66  tff(c_4246, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_4239, c_4055])).
% 7.44/2.66  tff(c_4248, plain, (![B_5]: (k2_zfmisc_1('#skF_4', B_5)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_4239, c_4239, c_4054])).
% 7.44/2.66  tff(c_5224, plain, (![A_630, B_631, C_632, D_633]: (v1_funct_1(k2_partfun1(A_630, B_631, C_632, D_633)) | ~m1_subset_1(C_632, k1_zfmisc_1(k2_zfmisc_1(A_630, B_631))) | ~v1_funct_1(C_632))), inference(cnfTransformation, [status(thm)], [f_117])).
% 7.44/2.66  tff(c_5640, plain, (![B_686, C_687, D_688]: (v1_funct_1(k2_partfun1('#skF_4', B_686, C_687, D_688)) | ~m1_subset_1(C_687, k1_zfmisc_1('#skF_4')) | ~v1_funct_1(C_687))), inference(superposition, [status(thm), theory('equality')], [c_4248, c_5224])).
% 7.44/2.66  tff(c_5642, plain, (![B_686, D_688]: (v1_funct_1(k2_partfun1('#skF_4', B_686, '#skF_4', D_688)) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_4246, c_5640])).
% 7.44/2.66  tff(c_5648, plain, (![B_686, D_688]: (v1_funct_1(k2_partfun1('#skF_4', B_686, '#skF_4', D_688)))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_5642])).
% 7.44/2.66  tff(c_4080, plain, (![A_491]: (A_491='#skF_1' | ~r1_tarski(A_491, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_4041, c_4041, c_8])).
% 7.44/2.66  tff(c_4090, plain, ('#skF_3'='#skF_1'), inference(resolution, [status(thm)], [c_64, c_4080])).
% 7.44/2.66  tff(c_4212, plain, (~m1_subset_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'), k1_zfmisc_1('#skF_1')) | ~v1_funct_2(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'), '#skF_1', '#skF_1') | ~v1_funct_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_4047, c_4090, c_4047, c_4047, c_4090, c_4090, c_4047, c_4054, c_4090, c_4090, c_60])).
% 7.44/2.66  tff(c_4213, plain, (~v1_funct_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'))), inference(splitLeft, [status(thm)], [c_4212])).
% 7.44/2.66  tff(c_4241, plain, (~v1_funct_1(k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_4239, c_4239, c_4239, c_4213])).
% 7.44/2.66  tff(c_5652, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_5648, c_4241])).
% 7.44/2.66  tff(c_5653, plain, (~v1_funct_2(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'), '#skF_1', '#skF_1') | ~m1_subset_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'), k1_zfmisc_1('#skF_1'))), inference(splitRight, [status(thm)], [c_4212])).
% 7.44/2.66  tff(c_5785, plain, (~v1_funct_2(k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_4'), '#skF_4', '#skF_4') | ~m1_subset_1(k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_4'), k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_5685, c_5685, c_5685, c_5685, c_5685, c_5685, c_5685, c_5685, c_5685, c_5653])).
% 7.44/2.66  tff(c_5786, plain, (~m1_subset_1(k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_4'), k1_zfmisc_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_5785])).
% 7.44/2.66  tff(c_5865, plain, (~r1_tarski(k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_4'), '#skF_4')), inference(resolution, [status(thm)], [c_18, c_5786])).
% 7.44/2.66  tff(c_9581, plain, (~r1_tarski('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_9572, c_5865])).
% 7.44/2.66  tff(c_9588, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_9581])).
% 7.44/2.66  tff(c_9590, plain, (m1_subset_1(k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_4'), k1_zfmisc_1('#skF_4'))), inference(splitRight, [status(thm)], [c_5785])).
% 7.44/2.66  tff(c_16, plain, (![A_6, B_7]: (r1_tarski(A_6, B_7) | ~m1_subset_1(A_6, k1_zfmisc_1(B_7)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 7.44/2.66  tff(c_9708, plain, (r1_tarski(k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_4'), '#skF_4')), inference(resolution, [status(thm)], [c_9590, c_16])).
% 7.44/2.66  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 7.44/2.66  tff(c_9746, plain, (k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_4')='#skF_4' | ~r1_tarski('#skF_4', k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_4'))), inference(resolution, [status(thm)], [c_9708, c_2])).
% 7.44/2.66  tff(c_9754, plain, (k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_9608, c_9746])).
% 7.44/2.66  tff(c_9589, plain, (~v1_funct_2(k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_4'), '#skF_4', '#skF_4')), inference(splitRight, [status(thm)], [c_5785])).
% 7.44/2.66  tff(c_9759, plain, (~v1_funct_2('#skF_4', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_9754, c_9589])).
% 7.44/2.66  tff(c_9766, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_5695, c_9759])).
% 7.44/2.66  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.44/2.66  
% 7.44/2.66  Inference rules
% 7.44/2.66  ----------------------
% 7.44/2.66  #Ref     : 0
% 7.44/2.66  #Sup     : 2081
% 7.44/2.66  #Fact    : 0
% 7.44/2.66  #Define  : 0
% 7.44/2.66  #Split   : 25
% 7.44/2.66  #Chain   : 0
% 7.44/2.66  #Close   : 0
% 7.44/2.66  
% 7.44/2.66  Ordering : KBO
% 7.44/2.66  
% 7.44/2.66  Simplification rules
% 7.44/2.66  ----------------------
% 7.44/2.66  #Subsume      : 199
% 7.44/2.66  #Demod        : 2345
% 7.44/2.66  #Tautology    : 1112
% 7.44/2.66  #SimpNegUnit  : 10
% 7.44/2.66  #BackRed      : 78
% 7.44/2.66  
% 7.44/2.66  #Partial instantiations: 0
% 7.44/2.66  #Strategies tried      : 1
% 7.44/2.66  
% 7.44/2.66  Timing (in seconds)
% 7.44/2.66  ----------------------
% 7.44/2.66  Preprocessing        : 0.36
% 7.44/2.66  Parsing              : 0.20
% 7.44/2.66  CNF conversion       : 0.02
% 7.44/2.66  Main loop            : 1.42
% 7.44/2.66  Inferencing          : 0.50
% 7.44/2.66  Reduction            : 0.49
% 7.44/2.66  Demodulation         : 0.36
% 7.44/2.66  BG Simplification    : 0.05
% 7.44/2.67  Subsumption          : 0.26
% 7.44/2.67  Abstraction          : 0.06
% 7.44/2.67  MUC search           : 0.00
% 7.44/2.67  Cooper               : 0.00
% 7.44/2.67  Total                : 1.86
% 7.44/2.67  Index Insertion      : 0.00
% 7.44/2.67  Index Deletion       : 0.00
% 7.44/2.67  Index Matching       : 0.00
% 7.44/2.67  BG Taut test         : 0.00
%------------------------------------------------------------------------------
