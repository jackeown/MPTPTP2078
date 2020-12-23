%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:13:32 EST 2020

% Result     : Theorem 7.40s
% Output     : CNFRefutation 7.52s
% Verified   : 
% Statistics : Number of formulae       :  162 (2529 expanded)
%              Number of leaves         :   38 ( 793 expanded)
%              Depth                    :   13
%              Number of atoms          :  270 (7978 expanded)
%              Number of equality atoms :   71 (3147 expanded)
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

tff(f_146,negated_conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_funct_2)).

tff(f_76,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_86,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_112,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).

tff(f_72,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(A,k1_relat_1(B))
       => k1_relat_1(k7_relat_1(B,A)) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_relat_1)).

tff(f_126,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => k2_partfun1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

tff(f_62,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k1_relat_1(k7_relat_1(B,A)),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_relat_1)).

tff(f_120,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( v1_funct_1(k2_partfun1(A,B,C,D))
        & m1_subset_1(k2_partfun1(A,B,C,D),k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_partfun1)).

tff(f_82,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_66,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k7_relat_1(B,A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_relat_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_46,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_94,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( ( r1_tarski(k1_relat_1(C),A)
          & r1_tarski(k2_relat_1(C),B) )
       => m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_relset_1)).

tff(f_52,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_29,axiom,(
    ! [A] :
      ( r1_tarski(A,k1_xboole_0)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).

tff(c_60,plain,(
    r1_tarski('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_62,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_1086,plain,(
    ! [C_180,A_181,B_182] :
      ( v1_relat_1(C_180)
      | ~ m1_subset_1(C_180,k1_zfmisc_1(k2_zfmisc_1(A_181,B_182))) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_1099,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_62,c_1086])).

tff(c_58,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_71,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_58])).

tff(c_64,plain,(
    v1_funct_2('#skF_4','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_3286,plain,(
    ! [A_404,B_405,C_406] :
      ( k1_relset_1(A_404,B_405,C_406) = k1_relat_1(C_406)
      | ~ m1_subset_1(C_406,k1_zfmisc_1(k2_zfmisc_1(A_404,B_405))) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_3305,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_62,c_3286])).

tff(c_3878,plain,(
    ! [B_482,A_483,C_484] :
      ( k1_xboole_0 = B_482
      | k1_relset_1(A_483,B_482,C_484) = A_483
      | ~ v1_funct_2(C_484,A_483,B_482)
      | ~ m1_subset_1(C_484,k1_zfmisc_1(k2_zfmisc_1(A_483,B_482))) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_3888,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1('#skF_1','#skF_2','#skF_4') = '#skF_1'
    | ~ v1_funct_2('#skF_4','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_62,c_3878])).

tff(c_3899,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_3305,c_3888])).

tff(c_3900,plain,(
    k1_relat_1('#skF_4') = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_71,c_3899])).

tff(c_26,plain,(
    ! [B_18,A_17] :
      ( k1_relat_1(k7_relat_1(B_18,A_17)) = A_17
      | ~ r1_tarski(A_17,k1_relat_1(B_18))
      | ~ v1_relat_1(B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_3907,plain,(
    ! [A_17] :
      ( k1_relat_1(k7_relat_1('#skF_4',A_17)) = A_17
      | ~ r1_tarski(A_17,'#skF_1')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3900,c_26])).

tff(c_3911,plain,(
    ! [A_17] :
      ( k1_relat_1(k7_relat_1('#skF_4',A_17)) = A_17
      | ~ r1_tarski(A_17,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1099,c_3907])).

tff(c_66,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_3820,plain,(
    ! [A_476,B_477,C_478,D_479] :
      ( k2_partfun1(A_476,B_477,C_478,D_479) = k7_relat_1(C_478,D_479)
      | ~ m1_subset_1(C_478,k1_zfmisc_1(k2_zfmisc_1(A_476,B_477)))
      | ~ v1_funct_1(C_478) ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_3829,plain,(
    ! [D_479] :
      ( k2_partfun1('#skF_1','#skF_2','#skF_4',D_479) = k7_relat_1('#skF_4',D_479)
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_62,c_3820])).

tff(c_3841,plain,(
    ! [D_479] : k2_partfun1('#skF_1','#skF_2','#skF_4',D_479) = k7_relat_1('#skF_4',D_479) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_3829])).

tff(c_1563,plain,(
    ! [A_235,B_236,C_237] :
      ( k1_relset_1(A_235,B_236,C_237) = k1_relat_1(C_237)
      | ~ m1_subset_1(C_237,k1_zfmisc_1(k2_zfmisc_1(A_235,B_236))) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_1578,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_62,c_1563])).

tff(c_2134,plain,(
    ! [B_307,A_308,C_309] :
      ( k1_xboole_0 = B_307
      | k1_relset_1(A_308,B_307,C_309) = A_308
      | ~ v1_funct_2(C_309,A_308,B_307)
      | ~ m1_subset_1(C_309,k1_zfmisc_1(k2_zfmisc_1(A_308,B_307))) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_2144,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1('#skF_1','#skF_2','#skF_4') = '#skF_1'
    | ~ v1_funct_2('#skF_4','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_62,c_2134])).

tff(c_2155,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_1578,c_2144])).

tff(c_2156,plain,(
    k1_relat_1('#skF_4') = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_71,c_2155])).

tff(c_2163,plain,(
    ! [A_17] :
      ( k1_relat_1(k7_relat_1('#skF_4',A_17)) = A_17
      | ~ r1_tarski(A_17,'#skF_1')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2156,c_26])).

tff(c_2178,plain,(
    ! [A_310] :
      ( k1_relat_1(k7_relat_1('#skF_4',A_310)) = A_310
      | ~ r1_tarski(A_310,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1099,c_2163])).

tff(c_22,plain,(
    ! [B_14,A_13] :
      ( r1_tarski(k1_relat_1(k7_relat_1(B_14,A_13)),A_13)
      | ~ v1_relat_1(B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_2218,plain,(
    ! [A_310] :
      ( r1_tarski(A_310,A_310)
      | ~ v1_relat_1('#skF_4')
      | ~ r1_tarski(A_310,'#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2178,c_22])).

tff(c_2255,plain,(
    ! [A_311] :
      ( r1_tarski(A_311,A_311)
      | ~ r1_tarski(A_311,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1099,c_2218])).

tff(c_2279,plain,(
    r1_tarski('#skF_3','#skF_3') ),
    inference(resolution,[status(thm)],[c_60,c_2255])).

tff(c_2167,plain,(
    ! [A_17] :
      ( k1_relat_1(k7_relat_1('#skF_4',A_17)) = A_17
      | ~ r1_tarski(A_17,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1099,c_2163])).

tff(c_1907,plain,(
    ! [A_283,B_284,C_285,D_286] :
      ( k2_partfun1(A_283,B_284,C_285,D_286) = k7_relat_1(C_285,D_286)
      | ~ m1_subset_1(C_285,k1_zfmisc_1(k2_zfmisc_1(A_283,B_284)))
      | ~ v1_funct_1(C_285) ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_1912,plain,(
    ! [D_286] :
      ( k2_partfun1('#skF_1','#skF_2','#skF_4',D_286) = k7_relat_1('#skF_4',D_286)
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_62,c_1907])).

tff(c_1920,plain,(
    ! [D_286] : k2_partfun1('#skF_1','#skF_2','#skF_4',D_286) = k7_relat_1('#skF_4',D_286) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_1912])).

tff(c_2456,plain,(
    ! [A_329,B_330,C_331,D_332] :
      ( m1_subset_1(k2_partfun1(A_329,B_330,C_331,D_332),k1_zfmisc_1(k2_zfmisc_1(A_329,B_330)))
      | ~ m1_subset_1(C_331,k1_zfmisc_1(k2_zfmisc_1(A_329,B_330)))
      | ~ v1_funct_1(C_331) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_2487,plain,(
    ! [D_286] :
      ( m1_subset_1(k7_relat_1('#skF_4',D_286),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
      | ~ v1_funct_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1920,c_2456])).

tff(c_2508,plain,(
    ! [D_333] : m1_subset_1(k7_relat_1('#skF_4',D_333),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_62,c_2487])).

tff(c_30,plain,(
    ! [C_24,B_23,A_22] :
      ( v5_relat_1(C_24,B_23)
      | ~ m1_subset_1(C_24,k1_zfmisc_1(k2_zfmisc_1(A_22,B_23))) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_2552,plain,(
    ! [D_333] : v5_relat_1(k7_relat_1('#skF_4',D_333),'#skF_2') ),
    inference(resolution,[status(thm)],[c_2508,c_30])).

tff(c_24,plain,(
    ! [B_16,A_15] :
      ( r1_tarski(k7_relat_1(B_16,A_15),B_16)
      | ~ v1_relat_1(B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_12,plain,(
    ! [A_4,B_5] :
      ( m1_subset_1(A_4,k1_zfmisc_1(B_5))
      | ~ r1_tarski(A_4,B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_1155,plain,(
    ! [B_190,A_191] :
      ( v1_relat_1(B_190)
      | ~ m1_subset_1(B_190,k1_zfmisc_1(A_191))
      | ~ v1_relat_1(A_191) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_1210,plain,(
    ! [A_194,B_195] :
      ( v1_relat_1(A_194)
      | ~ v1_relat_1(B_195)
      | ~ r1_tarski(A_194,B_195) ) ),
    inference(resolution,[status(thm)],[c_12,c_1155])).

tff(c_1229,plain,(
    ! [B_16,A_15] :
      ( v1_relat_1(k7_relat_1(B_16,A_15))
      | ~ v1_relat_1(B_16) ) ),
    inference(resolution,[status(thm)],[c_24,c_1210])).

tff(c_1965,plain,(
    ! [C_291,A_292,B_293] :
      ( m1_subset_1(C_291,k1_zfmisc_1(k2_zfmisc_1(A_292,B_293)))
      | ~ r1_tarski(k2_relat_1(C_291),B_293)
      | ~ r1_tarski(k1_relat_1(C_291),A_292)
      | ~ v1_relat_1(C_291) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_904,plain,(
    ! [A_150,B_151,C_152,D_153] :
      ( v1_funct_1(k2_partfun1(A_150,B_151,C_152,D_153))
      | ~ m1_subset_1(C_152,k1_zfmisc_1(k2_zfmisc_1(A_150,B_151)))
      | ~ v1_funct_1(C_152) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_909,plain,(
    ! [D_153] :
      ( v1_funct_1(k2_partfun1('#skF_1','#skF_2','#skF_4',D_153))
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_62,c_904])).

tff(c_917,plain,(
    ! [D_153] : v1_funct_1(k2_partfun1('#skF_1','#skF_2','#skF_4',D_153)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_909])).

tff(c_56,plain,
    ( ~ m1_subset_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2')))
    | ~ v1_funct_2(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),'#skF_3','#skF_2')
    | ~ v1_funct_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_95,plain,(
    ~ v1_funct_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_56])).

tff(c_927,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_917,c_95])).

tff(c_928,plain,
    ( ~ v1_funct_2(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),'#skF_3','#skF_2')
    | ~ m1_subset_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_1182,plain,(
    ~ m1_subset_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_928])).

tff(c_1923,plain,(
    ~ m1_subset_1(k7_relat_1('#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1920,c_1182])).

tff(c_1997,plain,
    ( ~ r1_tarski(k2_relat_1(k7_relat_1('#skF_4','#skF_3')),'#skF_2')
    | ~ r1_tarski(k1_relat_1(k7_relat_1('#skF_4','#skF_3')),'#skF_3')
    | ~ v1_relat_1(k7_relat_1('#skF_4','#skF_3')) ),
    inference(resolution,[status(thm)],[c_1965,c_1923])).

tff(c_2048,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_4','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_1997])).

tff(c_2051,plain,(
    ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_1229,c_2048])).

tff(c_2055,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1099,c_2051])).

tff(c_2057,plain,(
    v1_relat_1(k7_relat_1('#skF_4','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_1997])).

tff(c_18,plain,(
    ! [B_10,A_9] :
      ( r1_tarski(k2_relat_1(B_10),A_9)
      | ~ v5_relat_1(B_10,A_9)
      | ~ v1_relat_1(B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_2056,plain,
    ( ~ r1_tarski(k1_relat_1(k7_relat_1('#skF_4','#skF_3')),'#skF_3')
    | ~ r1_tarski(k2_relat_1(k7_relat_1('#skF_4','#skF_3')),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_1997])).

tff(c_2421,plain,(
    ~ r1_tarski(k2_relat_1(k7_relat_1('#skF_4','#skF_3')),'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_2056])).

tff(c_2424,plain,
    ( ~ v5_relat_1(k7_relat_1('#skF_4','#skF_3'),'#skF_2')
    | ~ v1_relat_1(k7_relat_1('#skF_4','#skF_3')) ),
    inference(resolution,[status(thm)],[c_18,c_2421])).

tff(c_2427,plain,(
    ~ v5_relat_1(k7_relat_1('#skF_4','#skF_3'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2057,c_2424])).

tff(c_2565,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2552,c_2427])).

tff(c_2566,plain,(
    ~ r1_tarski(k1_relat_1(k7_relat_1('#skF_4','#skF_3')),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_2056])).

tff(c_2652,plain,
    ( ~ r1_tarski('#skF_3','#skF_3')
    | ~ r1_tarski('#skF_3','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_2167,c_2566])).

tff(c_2658,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_2279,c_2652])).

tff(c_2660,plain,(
    m1_subset_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_928])).

tff(c_3303,plain,(
    k1_relset_1('#skF_3','#skF_2',k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3')) = k1_relat_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3')) ),
    inference(resolution,[status(thm)],[c_2660,c_3286])).

tff(c_3847,plain,(
    k1_relset_1('#skF_3','#skF_2',k7_relat_1('#skF_4','#skF_3')) = k1_relat_1(k7_relat_1('#skF_4','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3841,c_3841,c_3303])).

tff(c_2659,plain,(
    ~ v1_funct_2(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),'#skF_3','#skF_2') ),
    inference(splitRight,[status(thm)],[c_928])).

tff(c_3853,plain,(
    ~ v1_funct_2(k7_relat_1('#skF_4','#skF_3'),'#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3841,c_2659])).

tff(c_3852,plain,(
    m1_subset_1(k7_relat_1('#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3841,c_2660])).

tff(c_4001,plain,(
    ! [B_486,C_487,A_488] :
      ( k1_xboole_0 = B_486
      | v1_funct_2(C_487,A_488,B_486)
      | k1_relset_1(A_488,B_486,C_487) != A_488
      | ~ m1_subset_1(C_487,k1_zfmisc_1(k2_zfmisc_1(A_488,B_486))) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_4004,plain,
    ( k1_xboole_0 = '#skF_2'
    | v1_funct_2(k7_relat_1('#skF_4','#skF_3'),'#skF_3','#skF_2')
    | k1_relset_1('#skF_3','#skF_2',k7_relat_1('#skF_4','#skF_3')) != '#skF_3' ),
    inference(resolution,[status(thm)],[c_3852,c_4001])).

tff(c_4023,plain,(
    k1_relset_1('#skF_3','#skF_2',k7_relat_1('#skF_4','#skF_3')) != '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_3853,c_71,c_4004])).

tff(c_4118,plain,(
    k1_relat_1(k7_relat_1('#skF_4','#skF_3')) != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3847,c_4023])).

tff(c_4125,plain,(
    ~ r1_tarski('#skF_3','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_3911,c_4118])).

tff(c_4129,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_4125])).

tff(c_4130,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_8,plain,(
    ! [B_3] : k2_zfmisc_1(k1_xboole_0,B_3) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_4142,plain,(
    ! [B_3] : k2_zfmisc_1('#skF_1',B_3) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4130,c_4130,c_8])).

tff(c_4131,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_4136,plain,(
    '#skF_2' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4130,c_4131])).

tff(c_4182,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4142,c_4136,c_62])).

tff(c_4315,plain,(
    ! [A_509,B_510] :
      ( r1_tarski(A_509,B_510)
      | ~ m1_subset_1(A_509,k1_zfmisc_1(B_510)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_4319,plain,(
    r1_tarski('#skF_4','#skF_1') ),
    inference(resolution,[status(thm)],[c_4182,c_4315])).

tff(c_2,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ r1_tarski(A_1,k1_xboole_0) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_4166,plain,(
    ! [A_1] :
      ( A_1 = '#skF_1'
      | ~ r1_tarski(A_1,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4130,c_4130,c_2])).

tff(c_4323,plain,(
    '#skF_1' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_4319,c_4166])).

tff(c_4137,plain,(
    v1_funct_2('#skF_4','#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4136,c_64])).

tff(c_4330,plain,(
    v1_funct_2('#skF_4','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4323,c_4323,c_4137])).

tff(c_4326,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4323,c_4182])).

tff(c_4332,plain,(
    ! [B_3] : k2_zfmisc_1('#skF_4',B_3) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4323,c_4323,c_4142])).

tff(c_6648,plain,(
    ! [A_838,B_839,C_840,D_841] :
      ( m1_subset_1(k2_partfun1(A_838,B_839,C_840,D_841),k1_zfmisc_1(k2_zfmisc_1(A_838,B_839)))
      | ~ m1_subset_1(C_840,k1_zfmisc_1(k2_zfmisc_1(A_838,B_839)))
      | ~ v1_funct_1(C_840) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_6682,plain,(
    ! [B_3,C_840,D_841] :
      ( m1_subset_1(k2_partfun1('#skF_4',B_3,C_840,D_841),k1_zfmisc_1('#skF_4'))
      | ~ m1_subset_1(C_840,k1_zfmisc_1(k2_zfmisc_1('#skF_4',B_3)))
      | ~ v1_funct_1(C_840) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4332,c_6648])).

tff(c_7445,plain,(
    ! [B_926,C_927,D_928] :
      ( m1_subset_1(k2_partfun1('#skF_4',B_926,C_927,D_928),k1_zfmisc_1('#skF_4'))
      | ~ m1_subset_1(C_927,k1_zfmisc_1('#skF_4'))
      | ~ v1_funct_1(C_927) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4332,c_6682])).

tff(c_4333,plain,(
    '#skF_2' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4323,c_4136])).

tff(c_4167,plain,(
    ! [A_492] :
      ( A_492 = '#skF_1'
      | ~ r1_tarski(A_492,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4130,c_4130,c_2])).

tff(c_4171,plain,(
    '#skF_3' = '#skF_1' ),
    inference(resolution,[status(thm)],[c_60,c_4167])).

tff(c_4328,plain,(
    '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4323,c_4171])).

tff(c_5041,plain,(
    ! [A_607,B_608,C_609,D_610] :
      ( v1_funct_1(k2_partfun1(A_607,B_608,C_609,D_610))
      | ~ m1_subset_1(C_609,k1_zfmisc_1(k2_zfmisc_1(A_607,B_608)))
      | ~ v1_funct_1(C_609) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_5452,plain,(
    ! [B_662,C_663,D_664] :
      ( v1_funct_1(k2_partfun1('#skF_4',B_662,C_663,D_664))
      | ~ m1_subset_1(C_663,k1_zfmisc_1('#skF_4'))
      | ~ v1_funct_1(C_663) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4332,c_5041])).

tff(c_5454,plain,(
    ! [B_662,D_664] :
      ( v1_funct_1(k2_partfun1('#skF_4',B_662,'#skF_4',D_664))
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_4326,c_5452])).

tff(c_5460,plain,(
    ! [B_662,D_664] : v1_funct_1(k2_partfun1('#skF_4',B_662,'#skF_4',D_664)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_5454])).

tff(c_4339,plain,
    ( ~ m1_subset_1(k2_partfun1('#skF_4','#skF_2','#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2')))
    | ~ v1_funct_2(k2_partfun1('#skF_4','#skF_2','#skF_4','#skF_3'),'#skF_3','#skF_2')
    | ~ v1_funct_1(k2_partfun1('#skF_4','#skF_2','#skF_4','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4323,c_4323,c_4323,c_56])).

tff(c_4340,plain,(
    ~ v1_funct_1(k2_partfun1('#skF_4','#skF_2','#skF_4','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_4339])).

tff(c_4412,plain,(
    ~ v1_funct_1(k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4333,c_4328,c_4340])).

tff(c_5482,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_5460,c_4412])).

tff(c_5483,plain,
    ( ~ v1_funct_2(k2_partfun1('#skF_4','#skF_2','#skF_4','#skF_3'),'#skF_3','#skF_2')
    | ~ m1_subset_1(k2_partfun1('#skF_4','#skF_2','#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_4339])).

tff(c_5649,plain,
    ( ~ v1_funct_2(k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_4'),'#skF_4','#skF_4')
    | ~ m1_subset_1(k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_4'),k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4332,c_4333,c_4333,c_4328,c_4328,c_4333,c_4333,c_4328,c_4328,c_5483])).

tff(c_5650,plain,(
    ~ m1_subset_1(k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_4'),k1_zfmisc_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_5649])).

tff(c_7466,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_4'))
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_7445,c_5650])).

tff(c_7488,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_4326,c_7466])).

tff(c_7490,plain,(
    m1_subset_1(k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_4'),k1_zfmisc_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_5649])).

tff(c_10,plain,(
    ! [A_4,B_5] :
      ( r1_tarski(A_4,B_5)
      | ~ m1_subset_1(A_4,k1_zfmisc_1(B_5)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_7559,plain,(
    r1_tarski(k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_4'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_7490,c_10])).

tff(c_4329,plain,(
    ! [A_1] :
      ( A_1 = '#skF_4'
      | ~ r1_tarski(A_1,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4323,c_4323,c_4166])).

tff(c_7601,plain,(
    k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_4') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_7559,c_4329])).

tff(c_7489,plain,(
    ~ v1_funct_2(k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_4'),'#skF_4','#skF_4') ),
    inference(splitRight,[status(thm)],[c_5649])).

tff(c_7638,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4330,c_7601,c_7489])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n009.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 15:54:56 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.40/2.58  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.52/2.60  
% 7.52/2.60  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.52/2.60  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_partfun1 > k1_relset_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 7.52/2.60  
% 7.52/2.60  %Foreground sorts:
% 7.52/2.60  
% 7.52/2.60  
% 7.52/2.60  %Background operators:
% 7.52/2.60  
% 7.52/2.60  
% 7.52/2.60  %Foreground operators:
% 7.52/2.60  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 7.52/2.60  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.52/2.60  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 7.52/2.60  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 7.52/2.60  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.52/2.60  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 7.52/2.60  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 7.52/2.60  tff('#skF_2', type, '#skF_2': $i).
% 7.52/2.60  tff('#skF_3', type, '#skF_3': $i).
% 7.52/2.60  tff('#skF_1', type, '#skF_1': $i).
% 7.52/2.60  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 7.52/2.60  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 7.52/2.60  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 7.52/2.60  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.52/2.60  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 7.52/2.60  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 7.52/2.60  tff('#skF_4', type, '#skF_4': $i).
% 7.52/2.60  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.52/2.60  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 7.52/2.60  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 7.52/2.60  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 7.52/2.60  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 7.52/2.60  
% 7.52/2.62  tff(f_146, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r1_tarski(C, A) => (((B = k1_xboole_0) & ~(A = k1_xboole_0)) | ((v1_funct_1(k2_partfun1(A, B, D, C)) & v1_funct_2(k2_partfun1(A, B, D, C), C, B)) & m1_subset_1(k2_partfun1(A, B, D, C), k1_zfmisc_1(k2_zfmisc_1(C, B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_funct_2)).
% 7.52/2.62  tff(f_76, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 7.52/2.62  tff(f_86, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 7.52/2.62  tff(f_112, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 7.52/2.62  tff(f_72, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(A, k1_relat_1(B)) => (k1_relat_1(k7_relat_1(B, A)) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_relat_1)).
% 7.52/2.62  tff(f_126, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (k2_partfun1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_partfun1)).
% 7.52/2.62  tff(f_62, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k7_relat_1(B, A)), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t87_relat_1)).
% 7.52/2.62  tff(f_120, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (v1_funct_1(k2_partfun1(A, B, C, D)) & m1_subset_1(k2_partfun1(A, B, C, D), k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_partfun1)).
% 7.52/2.62  tff(f_82, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 7.52/2.62  tff(f_66, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k7_relat_1(B, A), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t88_relat_1)).
% 7.52/2.62  tff(f_39, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 7.52/2.62  tff(f_46, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 7.52/2.62  tff(f_94, axiom, (![A, B, C]: (v1_relat_1(C) => ((r1_tarski(k1_relat_1(C), A) & r1_tarski(k2_relat_1(C), B)) => m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_relset_1)).
% 7.52/2.62  tff(f_52, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 7.52/2.62  tff(f_35, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 7.52/2.62  tff(f_29, axiom, (![A]: (r1_tarski(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_1)).
% 7.52/2.62  tff(c_60, plain, (r1_tarski('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_146])).
% 7.52/2.62  tff(c_62, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_146])).
% 7.52/2.62  tff(c_1086, plain, (![C_180, A_181, B_182]: (v1_relat_1(C_180) | ~m1_subset_1(C_180, k1_zfmisc_1(k2_zfmisc_1(A_181, B_182))))), inference(cnfTransformation, [status(thm)], [f_76])).
% 7.52/2.62  tff(c_1099, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_62, c_1086])).
% 7.52/2.62  tff(c_58, plain, (k1_xboole_0='#skF_1' | k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_146])).
% 7.52/2.62  tff(c_71, plain, (k1_xboole_0!='#skF_2'), inference(splitLeft, [status(thm)], [c_58])).
% 7.52/2.62  tff(c_64, plain, (v1_funct_2('#skF_4', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_146])).
% 7.52/2.62  tff(c_3286, plain, (![A_404, B_405, C_406]: (k1_relset_1(A_404, B_405, C_406)=k1_relat_1(C_406) | ~m1_subset_1(C_406, k1_zfmisc_1(k2_zfmisc_1(A_404, B_405))))), inference(cnfTransformation, [status(thm)], [f_86])).
% 7.52/2.62  tff(c_3305, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_62, c_3286])).
% 7.52/2.62  tff(c_3878, plain, (![B_482, A_483, C_484]: (k1_xboole_0=B_482 | k1_relset_1(A_483, B_482, C_484)=A_483 | ~v1_funct_2(C_484, A_483, B_482) | ~m1_subset_1(C_484, k1_zfmisc_1(k2_zfmisc_1(A_483, B_482))))), inference(cnfTransformation, [status(thm)], [f_112])).
% 7.52/2.62  tff(c_3888, plain, (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', '#skF_4')='#skF_1' | ~v1_funct_2('#skF_4', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_62, c_3878])).
% 7.52/2.62  tff(c_3899, plain, (k1_xboole_0='#skF_2' | k1_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_64, c_3305, c_3888])).
% 7.52/2.62  tff(c_3900, plain, (k1_relat_1('#skF_4')='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_71, c_3899])).
% 7.52/2.62  tff(c_26, plain, (![B_18, A_17]: (k1_relat_1(k7_relat_1(B_18, A_17))=A_17 | ~r1_tarski(A_17, k1_relat_1(B_18)) | ~v1_relat_1(B_18))), inference(cnfTransformation, [status(thm)], [f_72])).
% 7.52/2.62  tff(c_3907, plain, (![A_17]: (k1_relat_1(k7_relat_1('#skF_4', A_17))=A_17 | ~r1_tarski(A_17, '#skF_1') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_3900, c_26])).
% 7.52/2.62  tff(c_3911, plain, (![A_17]: (k1_relat_1(k7_relat_1('#skF_4', A_17))=A_17 | ~r1_tarski(A_17, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_1099, c_3907])).
% 7.52/2.62  tff(c_66, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_146])).
% 7.52/2.62  tff(c_3820, plain, (![A_476, B_477, C_478, D_479]: (k2_partfun1(A_476, B_477, C_478, D_479)=k7_relat_1(C_478, D_479) | ~m1_subset_1(C_478, k1_zfmisc_1(k2_zfmisc_1(A_476, B_477))) | ~v1_funct_1(C_478))), inference(cnfTransformation, [status(thm)], [f_126])).
% 7.52/2.62  tff(c_3829, plain, (![D_479]: (k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_479)=k7_relat_1('#skF_4', D_479) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_62, c_3820])).
% 7.52/2.62  tff(c_3841, plain, (![D_479]: (k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_479)=k7_relat_1('#skF_4', D_479))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_3829])).
% 7.52/2.62  tff(c_1563, plain, (![A_235, B_236, C_237]: (k1_relset_1(A_235, B_236, C_237)=k1_relat_1(C_237) | ~m1_subset_1(C_237, k1_zfmisc_1(k2_zfmisc_1(A_235, B_236))))), inference(cnfTransformation, [status(thm)], [f_86])).
% 7.52/2.62  tff(c_1578, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_62, c_1563])).
% 7.52/2.62  tff(c_2134, plain, (![B_307, A_308, C_309]: (k1_xboole_0=B_307 | k1_relset_1(A_308, B_307, C_309)=A_308 | ~v1_funct_2(C_309, A_308, B_307) | ~m1_subset_1(C_309, k1_zfmisc_1(k2_zfmisc_1(A_308, B_307))))), inference(cnfTransformation, [status(thm)], [f_112])).
% 7.52/2.62  tff(c_2144, plain, (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', '#skF_4')='#skF_1' | ~v1_funct_2('#skF_4', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_62, c_2134])).
% 7.52/2.62  tff(c_2155, plain, (k1_xboole_0='#skF_2' | k1_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_64, c_1578, c_2144])).
% 7.52/2.62  tff(c_2156, plain, (k1_relat_1('#skF_4')='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_71, c_2155])).
% 7.52/2.62  tff(c_2163, plain, (![A_17]: (k1_relat_1(k7_relat_1('#skF_4', A_17))=A_17 | ~r1_tarski(A_17, '#skF_1') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_2156, c_26])).
% 7.52/2.62  tff(c_2178, plain, (![A_310]: (k1_relat_1(k7_relat_1('#skF_4', A_310))=A_310 | ~r1_tarski(A_310, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_1099, c_2163])).
% 7.52/2.62  tff(c_22, plain, (![B_14, A_13]: (r1_tarski(k1_relat_1(k7_relat_1(B_14, A_13)), A_13) | ~v1_relat_1(B_14))), inference(cnfTransformation, [status(thm)], [f_62])).
% 7.52/2.62  tff(c_2218, plain, (![A_310]: (r1_tarski(A_310, A_310) | ~v1_relat_1('#skF_4') | ~r1_tarski(A_310, '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_2178, c_22])).
% 7.52/2.62  tff(c_2255, plain, (![A_311]: (r1_tarski(A_311, A_311) | ~r1_tarski(A_311, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_1099, c_2218])).
% 7.52/2.62  tff(c_2279, plain, (r1_tarski('#skF_3', '#skF_3')), inference(resolution, [status(thm)], [c_60, c_2255])).
% 7.52/2.62  tff(c_2167, plain, (![A_17]: (k1_relat_1(k7_relat_1('#skF_4', A_17))=A_17 | ~r1_tarski(A_17, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_1099, c_2163])).
% 7.52/2.62  tff(c_1907, plain, (![A_283, B_284, C_285, D_286]: (k2_partfun1(A_283, B_284, C_285, D_286)=k7_relat_1(C_285, D_286) | ~m1_subset_1(C_285, k1_zfmisc_1(k2_zfmisc_1(A_283, B_284))) | ~v1_funct_1(C_285))), inference(cnfTransformation, [status(thm)], [f_126])).
% 7.52/2.62  tff(c_1912, plain, (![D_286]: (k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_286)=k7_relat_1('#skF_4', D_286) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_62, c_1907])).
% 7.52/2.62  tff(c_1920, plain, (![D_286]: (k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_286)=k7_relat_1('#skF_4', D_286))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_1912])).
% 7.52/2.62  tff(c_2456, plain, (![A_329, B_330, C_331, D_332]: (m1_subset_1(k2_partfun1(A_329, B_330, C_331, D_332), k1_zfmisc_1(k2_zfmisc_1(A_329, B_330))) | ~m1_subset_1(C_331, k1_zfmisc_1(k2_zfmisc_1(A_329, B_330))) | ~v1_funct_1(C_331))), inference(cnfTransformation, [status(thm)], [f_120])).
% 7.52/2.62  tff(c_2487, plain, (![D_286]: (m1_subset_1(k7_relat_1('#skF_4', D_286), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_1920, c_2456])).
% 7.52/2.62  tff(c_2508, plain, (![D_333]: (m1_subset_1(k7_relat_1('#skF_4', D_333), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_62, c_2487])).
% 7.52/2.62  tff(c_30, plain, (![C_24, B_23, A_22]: (v5_relat_1(C_24, B_23) | ~m1_subset_1(C_24, k1_zfmisc_1(k2_zfmisc_1(A_22, B_23))))), inference(cnfTransformation, [status(thm)], [f_82])).
% 7.52/2.62  tff(c_2552, plain, (![D_333]: (v5_relat_1(k7_relat_1('#skF_4', D_333), '#skF_2'))), inference(resolution, [status(thm)], [c_2508, c_30])).
% 7.52/2.62  tff(c_24, plain, (![B_16, A_15]: (r1_tarski(k7_relat_1(B_16, A_15), B_16) | ~v1_relat_1(B_16))), inference(cnfTransformation, [status(thm)], [f_66])).
% 7.52/2.62  tff(c_12, plain, (![A_4, B_5]: (m1_subset_1(A_4, k1_zfmisc_1(B_5)) | ~r1_tarski(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_39])).
% 7.52/2.62  tff(c_1155, plain, (![B_190, A_191]: (v1_relat_1(B_190) | ~m1_subset_1(B_190, k1_zfmisc_1(A_191)) | ~v1_relat_1(A_191))), inference(cnfTransformation, [status(thm)], [f_46])).
% 7.52/2.62  tff(c_1210, plain, (![A_194, B_195]: (v1_relat_1(A_194) | ~v1_relat_1(B_195) | ~r1_tarski(A_194, B_195))), inference(resolution, [status(thm)], [c_12, c_1155])).
% 7.52/2.62  tff(c_1229, plain, (![B_16, A_15]: (v1_relat_1(k7_relat_1(B_16, A_15)) | ~v1_relat_1(B_16))), inference(resolution, [status(thm)], [c_24, c_1210])).
% 7.52/2.62  tff(c_1965, plain, (![C_291, A_292, B_293]: (m1_subset_1(C_291, k1_zfmisc_1(k2_zfmisc_1(A_292, B_293))) | ~r1_tarski(k2_relat_1(C_291), B_293) | ~r1_tarski(k1_relat_1(C_291), A_292) | ~v1_relat_1(C_291))), inference(cnfTransformation, [status(thm)], [f_94])).
% 7.52/2.62  tff(c_904, plain, (![A_150, B_151, C_152, D_153]: (v1_funct_1(k2_partfun1(A_150, B_151, C_152, D_153)) | ~m1_subset_1(C_152, k1_zfmisc_1(k2_zfmisc_1(A_150, B_151))) | ~v1_funct_1(C_152))), inference(cnfTransformation, [status(thm)], [f_120])).
% 7.52/2.62  tff(c_909, plain, (![D_153]: (v1_funct_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_153)) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_62, c_904])).
% 7.52/2.62  tff(c_917, plain, (![D_153]: (v1_funct_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_153)))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_909])).
% 7.52/2.62  tff(c_56, plain, (~m1_subset_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2'))) | ~v1_funct_2(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), '#skF_3', '#skF_2') | ~v1_funct_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_146])).
% 7.52/2.62  tff(c_95, plain, (~v1_funct_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'))), inference(splitLeft, [status(thm)], [c_56])).
% 7.52/2.62  tff(c_927, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_917, c_95])).
% 7.52/2.62  tff(c_928, plain, (~v1_funct_2(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), '#skF_3', '#skF_2') | ~m1_subset_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(splitRight, [status(thm)], [c_56])).
% 7.52/2.62  tff(c_1182, plain, (~m1_subset_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(splitLeft, [status(thm)], [c_928])).
% 7.52/2.62  tff(c_1923, plain, (~m1_subset_1(k7_relat_1('#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_1920, c_1182])).
% 7.52/2.62  tff(c_1997, plain, (~r1_tarski(k2_relat_1(k7_relat_1('#skF_4', '#skF_3')), '#skF_2') | ~r1_tarski(k1_relat_1(k7_relat_1('#skF_4', '#skF_3')), '#skF_3') | ~v1_relat_1(k7_relat_1('#skF_4', '#skF_3'))), inference(resolution, [status(thm)], [c_1965, c_1923])).
% 7.52/2.62  tff(c_2048, plain, (~v1_relat_1(k7_relat_1('#skF_4', '#skF_3'))), inference(splitLeft, [status(thm)], [c_1997])).
% 7.52/2.62  tff(c_2051, plain, (~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_1229, c_2048])).
% 7.52/2.62  tff(c_2055, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1099, c_2051])).
% 7.52/2.62  tff(c_2057, plain, (v1_relat_1(k7_relat_1('#skF_4', '#skF_3'))), inference(splitRight, [status(thm)], [c_1997])).
% 7.52/2.62  tff(c_18, plain, (![B_10, A_9]: (r1_tarski(k2_relat_1(B_10), A_9) | ~v5_relat_1(B_10, A_9) | ~v1_relat_1(B_10))), inference(cnfTransformation, [status(thm)], [f_52])).
% 7.52/2.62  tff(c_2056, plain, (~r1_tarski(k1_relat_1(k7_relat_1('#skF_4', '#skF_3')), '#skF_3') | ~r1_tarski(k2_relat_1(k7_relat_1('#skF_4', '#skF_3')), '#skF_2')), inference(splitRight, [status(thm)], [c_1997])).
% 7.52/2.62  tff(c_2421, plain, (~r1_tarski(k2_relat_1(k7_relat_1('#skF_4', '#skF_3')), '#skF_2')), inference(splitLeft, [status(thm)], [c_2056])).
% 7.52/2.62  tff(c_2424, plain, (~v5_relat_1(k7_relat_1('#skF_4', '#skF_3'), '#skF_2') | ~v1_relat_1(k7_relat_1('#skF_4', '#skF_3'))), inference(resolution, [status(thm)], [c_18, c_2421])).
% 7.52/2.62  tff(c_2427, plain, (~v5_relat_1(k7_relat_1('#skF_4', '#skF_3'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2057, c_2424])).
% 7.52/2.62  tff(c_2565, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2552, c_2427])).
% 7.52/2.62  tff(c_2566, plain, (~r1_tarski(k1_relat_1(k7_relat_1('#skF_4', '#skF_3')), '#skF_3')), inference(splitRight, [status(thm)], [c_2056])).
% 7.52/2.62  tff(c_2652, plain, (~r1_tarski('#skF_3', '#skF_3') | ~r1_tarski('#skF_3', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_2167, c_2566])).
% 7.52/2.62  tff(c_2658, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_60, c_2279, c_2652])).
% 7.52/2.62  tff(c_2660, plain, (m1_subset_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(splitRight, [status(thm)], [c_928])).
% 7.52/2.62  tff(c_3303, plain, (k1_relset_1('#skF_3', '#skF_2', k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'))=k1_relat_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'))), inference(resolution, [status(thm)], [c_2660, c_3286])).
% 7.52/2.62  tff(c_3847, plain, (k1_relset_1('#skF_3', '#skF_2', k7_relat_1('#skF_4', '#skF_3'))=k1_relat_1(k7_relat_1('#skF_4', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_3841, c_3841, c_3303])).
% 7.52/2.62  tff(c_2659, plain, (~v1_funct_2(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), '#skF_3', '#skF_2')), inference(splitRight, [status(thm)], [c_928])).
% 7.52/2.62  tff(c_3853, plain, (~v1_funct_2(k7_relat_1('#skF_4', '#skF_3'), '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_3841, c_2659])).
% 7.52/2.62  tff(c_3852, plain, (m1_subset_1(k7_relat_1('#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_3841, c_2660])).
% 7.52/2.62  tff(c_4001, plain, (![B_486, C_487, A_488]: (k1_xboole_0=B_486 | v1_funct_2(C_487, A_488, B_486) | k1_relset_1(A_488, B_486, C_487)!=A_488 | ~m1_subset_1(C_487, k1_zfmisc_1(k2_zfmisc_1(A_488, B_486))))), inference(cnfTransformation, [status(thm)], [f_112])).
% 7.52/2.62  tff(c_4004, plain, (k1_xboole_0='#skF_2' | v1_funct_2(k7_relat_1('#skF_4', '#skF_3'), '#skF_3', '#skF_2') | k1_relset_1('#skF_3', '#skF_2', k7_relat_1('#skF_4', '#skF_3'))!='#skF_3'), inference(resolution, [status(thm)], [c_3852, c_4001])).
% 7.52/2.62  tff(c_4023, plain, (k1_relset_1('#skF_3', '#skF_2', k7_relat_1('#skF_4', '#skF_3'))!='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_3853, c_71, c_4004])).
% 7.52/2.62  tff(c_4118, plain, (k1_relat_1(k7_relat_1('#skF_4', '#skF_3'))!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_3847, c_4023])).
% 7.52/2.62  tff(c_4125, plain, (~r1_tarski('#skF_3', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_3911, c_4118])).
% 7.52/2.62  tff(c_4129, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_60, c_4125])).
% 7.52/2.62  tff(c_4130, plain, (k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_58])).
% 7.52/2.62  tff(c_8, plain, (![B_3]: (k2_zfmisc_1(k1_xboole_0, B_3)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_35])).
% 7.52/2.62  tff(c_4142, plain, (![B_3]: (k2_zfmisc_1('#skF_1', B_3)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_4130, c_4130, c_8])).
% 7.52/2.62  tff(c_4131, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_58])).
% 7.52/2.62  tff(c_4136, plain, ('#skF_2'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_4130, c_4131])).
% 7.52/2.62  tff(c_4182, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_4142, c_4136, c_62])).
% 7.52/2.62  tff(c_4315, plain, (![A_509, B_510]: (r1_tarski(A_509, B_510) | ~m1_subset_1(A_509, k1_zfmisc_1(B_510)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 7.52/2.62  tff(c_4319, plain, (r1_tarski('#skF_4', '#skF_1')), inference(resolution, [status(thm)], [c_4182, c_4315])).
% 7.52/2.62  tff(c_2, plain, (![A_1]: (k1_xboole_0=A_1 | ~r1_tarski(A_1, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_29])).
% 7.52/2.62  tff(c_4166, plain, (![A_1]: (A_1='#skF_1' | ~r1_tarski(A_1, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_4130, c_4130, c_2])).
% 7.52/2.62  tff(c_4323, plain, ('#skF_1'='#skF_4'), inference(resolution, [status(thm)], [c_4319, c_4166])).
% 7.52/2.62  tff(c_4137, plain, (v1_funct_2('#skF_4', '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_4136, c_64])).
% 7.52/2.62  tff(c_4330, plain, (v1_funct_2('#skF_4', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_4323, c_4323, c_4137])).
% 7.52/2.62  tff(c_4326, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_4323, c_4182])).
% 7.52/2.62  tff(c_4332, plain, (![B_3]: (k2_zfmisc_1('#skF_4', B_3)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_4323, c_4323, c_4142])).
% 7.52/2.62  tff(c_6648, plain, (![A_838, B_839, C_840, D_841]: (m1_subset_1(k2_partfun1(A_838, B_839, C_840, D_841), k1_zfmisc_1(k2_zfmisc_1(A_838, B_839))) | ~m1_subset_1(C_840, k1_zfmisc_1(k2_zfmisc_1(A_838, B_839))) | ~v1_funct_1(C_840))), inference(cnfTransformation, [status(thm)], [f_120])).
% 7.52/2.62  tff(c_6682, plain, (![B_3, C_840, D_841]: (m1_subset_1(k2_partfun1('#skF_4', B_3, C_840, D_841), k1_zfmisc_1('#skF_4')) | ~m1_subset_1(C_840, k1_zfmisc_1(k2_zfmisc_1('#skF_4', B_3))) | ~v1_funct_1(C_840))), inference(superposition, [status(thm), theory('equality')], [c_4332, c_6648])).
% 7.52/2.62  tff(c_7445, plain, (![B_926, C_927, D_928]: (m1_subset_1(k2_partfun1('#skF_4', B_926, C_927, D_928), k1_zfmisc_1('#skF_4')) | ~m1_subset_1(C_927, k1_zfmisc_1('#skF_4')) | ~v1_funct_1(C_927))), inference(demodulation, [status(thm), theory('equality')], [c_4332, c_6682])).
% 7.52/2.62  tff(c_4333, plain, ('#skF_2'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_4323, c_4136])).
% 7.52/2.62  tff(c_4167, plain, (![A_492]: (A_492='#skF_1' | ~r1_tarski(A_492, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_4130, c_4130, c_2])).
% 7.52/2.62  tff(c_4171, plain, ('#skF_3'='#skF_1'), inference(resolution, [status(thm)], [c_60, c_4167])).
% 7.52/2.62  tff(c_4328, plain, ('#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_4323, c_4171])).
% 7.52/2.62  tff(c_5041, plain, (![A_607, B_608, C_609, D_610]: (v1_funct_1(k2_partfun1(A_607, B_608, C_609, D_610)) | ~m1_subset_1(C_609, k1_zfmisc_1(k2_zfmisc_1(A_607, B_608))) | ~v1_funct_1(C_609))), inference(cnfTransformation, [status(thm)], [f_120])).
% 7.52/2.62  tff(c_5452, plain, (![B_662, C_663, D_664]: (v1_funct_1(k2_partfun1('#skF_4', B_662, C_663, D_664)) | ~m1_subset_1(C_663, k1_zfmisc_1('#skF_4')) | ~v1_funct_1(C_663))), inference(superposition, [status(thm), theory('equality')], [c_4332, c_5041])).
% 7.52/2.62  tff(c_5454, plain, (![B_662, D_664]: (v1_funct_1(k2_partfun1('#skF_4', B_662, '#skF_4', D_664)) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_4326, c_5452])).
% 7.52/2.62  tff(c_5460, plain, (![B_662, D_664]: (v1_funct_1(k2_partfun1('#skF_4', B_662, '#skF_4', D_664)))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_5454])).
% 7.52/2.62  tff(c_4339, plain, (~m1_subset_1(k2_partfun1('#skF_4', '#skF_2', '#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2'))) | ~v1_funct_2(k2_partfun1('#skF_4', '#skF_2', '#skF_4', '#skF_3'), '#skF_3', '#skF_2') | ~v1_funct_1(k2_partfun1('#skF_4', '#skF_2', '#skF_4', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_4323, c_4323, c_4323, c_56])).
% 7.52/2.62  tff(c_4340, plain, (~v1_funct_1(k2_partfun1('#skF_4', '#skF_2', '#skF_4', '#skF_3'))), inference(splitLeft, [status(thm)], [c_4339])).
% 7.52/2.62  tff(c_4412, plain, (~v1_funct_1(k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_4333, c_4328, c_4340])).
% 7.52/2.62  tff(c_5482, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_5460, c_4412])).
% 7.52/2.62  tff(c_5483, plain, (~v1_funct_2(k2_partfun1('#skF_4', '#skF_2', '#skF_4', '#skF_3'), '#skF_3', '#skF_2') | ~m1_subset_1(k2_partfun1('#skF_4', '#skF_2', '#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(splitRight, [status(thm)], [c_4339])).
% 7.52/2.62  tff(c_5649, plain, (~v1_funct_2(k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_4'), '#skF_4', '#skF_4') | ~m1_subset_1(k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_4'), k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_4332, c_4333, c_4333, c_4328, c_4328, c_4333, c_4333, c_4328, c_4328, c_5483])).
% 7.52/2.62  tff(c_5650, plain, (~m1_subset_1(k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_4'), k1_zfmisc_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_5649])).
% 7.52/2.62  tff(c_7466, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_4')) | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_7445, c_5650])).
% 7.52/2.62  tff(c_7488, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_66, c_4326, c_7466])).
% 7.52/2.62  tff(c_7490, plain, (m1_subset_1(k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_4'), k1_zfmisc_1('#skF_4'))), inference(splitRight, [status(thm)], [c_5649])).
% 7.52/2.62  tff(c_10, plain, (![A_4, B_5]: (r1_tarski(A_4, B_5) | ~m1_subset_1(A_4, k1_zfmisc_1(B_5)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 7.52/2.62  tff(c_7559, plain, (r1_tarski(k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_4'), '#skF_4')), inference(resolution, [status(thm)], [c_7490, c_10])).
% 7.52/2.62  tff(c_4329, plain, (![A_1]: (A_1='#skF_4' | ~r1_tarski(A_1, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_4323, c_4323, c_4166])).
% 7.52/2.62  tff(c_7601, plain, (k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_4')='#skF_4'), inference(resolution, [status(thm)], [c_7559, c_4329])).
% 7.52/2.62  tff(c_7489, plain, (~v1_funct_2(k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_4'), '#skF_4', '#skF_4')), inference(splitRight, [status(thm)], [c_5649])).
% 7.52/2.62  tff(c_7638, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4330, c_7601, c_7489])).
% 7.52/2.62  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.52/2.62  
% 7.52/2.62  Inference rules
% 7.52/2.62  ----------------------
% 7.52/2.62  #Ref     : 0
% 7.52/2.62  #Sup     : 1622
% 7.52/2.62  #Fact    : 0
% 7.52/2.62  #Define  : 0
% 7.52/2.62  #Split   : 25
% 7.52/2.62  #Chain   : 0
% 7.52/2.62  #Close   : 0
% 7.52/2.62  
% 7.52/2.62  Ordering : KBO
% 7.52/2.62  
% 7.52/2.62  Simplification rules
% 7.52/2.62  ----------------------
% 7.52/2.62  #Subsume      : 185
% 7.52/2.62  #Demod        : 1332
% 7.52/2.62  #Tautology    : 711
% 7.52/2.62  #SimpNegUnit  : 15
% 7.52/2.62  #BackRed      : 60
% 7.52/2.62  
% 7.52/2.62  #Partial instantiations: 0
% 7.52/2.62  #Strategies tried      : 1
% 7.52/2.62  
% 7.52/2.62  Timing (in seconds)
% 7.52/2.62  ----------------------
% 7.52/2.63  Preprocessing        : 0.37
% 7.52/2.63  Parsing              : 0.20
% 7.52/2.63  CNF conversion       : 0.02
% 7.52/2.63  Main loop            : 1.42
% 7.52/2.63  Inferencing          : 0.54
% 7.52/2.63  Reduction            : 0.44
% 7.52/2.63  Demodulation         : 0.31
% 7.52/2.63  BG Simplification    : 0.05
% 7.52/2.63  Subsumption          : 0.25
% 7.52/2.63  Abstraction          : 0.06
% 7.71/2.63  MUC search           : 0.00
% 7.71/2.63  Cooper               : 0.00
% 7.71/2.63  Total                : 1.84
% 7.71/2.63  Index Insertion      : 0.00
% 7.71/2.63  Index Deletion       : 0.00
% 7.71/2.63  Index Matching       : 0.00
% 7.71/2.63  BG Taut test         : 0.00
%------------------------------------------------------------------------------
