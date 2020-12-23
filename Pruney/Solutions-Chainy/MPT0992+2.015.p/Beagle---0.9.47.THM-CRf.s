%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:13:33 EST 2020

% Result     : Theorem 9.71s
% Output     : CNFRefutation 9.91s
% Verified   : 
% Statistics : Number of formulae       :  163 (2190 expanded)
%              Number of leaves         :   38 ( 704 expanded)
%              Depth                    :   14
%              Number of atoms          :  271 (6326 expanded)
%              Number of equality atoms :   74 (2212 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_partfun1 > k1_relset_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_160,negated_conjecture,(
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

tff(f_86,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_96,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_114,axiom,(
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

tff(f_73,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(A,k1_relat_1(B))
       => k1_relat_1(k7_relat_1(B,A)) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_relat_1)).

tff(f_128,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => k2_partfun1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

tff(f_122,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( v1_funct_1(k2_partfun1(A,B,C,D))
        & m1_subset_1(k2_partfun1(A,B,C,D),k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_partfun1)).

tff(f_92,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_64,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_140,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r1_tarski(k2_relat_1(B),A)
       => ( v1_funct_1(B)
          & v1_funct_2(B,k1_relat_1(B),A)
          & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B),A))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_funct_2)).

tff(f_52,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_48,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_46,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(c_74,plain,(
    r1_tarski('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_76,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_924,plain,(
    ! [C_157,A_158,B_159] :
      ( v1_relat_1(C_157)
      | ~ m1_subset_1(C_157,k1_zfmisc_1(k2_zfmisc_1(A_158,B_159))) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_941,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_76,c_924])).

tff(c_72,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_119,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_72])).

tff(c_78,plain,(
    v1_funct_2('#skF_4','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_9260,plain,(
    ! [A_838,B_839,C_840] :
      ( k1_relset_1(A_838,B_839,C_840) = k1_relat_1(C_840)
      | ~ m1_subset_1(C_840,k1_zfmisc_1(k2_zfmisc_1(A_838,B_839))) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_9283,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_76,c_9260])).

tff(c_10152,plain,(
    ! [B_943,A_944,C_945] :
      ( k1_xboole_0 = B_943
      | k1_relset_1(A_944,B_943,C_945) = A_944
      | ~ v1_funct_2(C_945,A_944,B_943)
      | ~ m1_subset_1(C_945,k1_zfmisc_1(k2_zfmisc_1(A_944,B_943))) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_10165,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1('#skF_1','#skF_2','#skF_4') = '#skF_1'
    | ~ v1_funct_2('#skF_4','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_76,c_10152])).

tff(c_10182,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_9283,c_10165])).

tff(c_10183,plain,(
    k1_relat_1('#skF_4') = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_119,c_10182])).

tff(c_34,plain,(
    ! [B_16,A_15] :
      ( k1_relat_1(k7_relat_1(B_16,A_15)) = A_15
      | ~ r1_tarski(A_15,k1_relat_1(B_16))
      | ~ v1_relat_1(B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_10200,plain,(
    ! [A_15] :
      ( k1_relat_1(k7_relat_1('#skF_4',A_15)) = A_15
      | ~ r1_tarski(A_15,'#skF_1')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10183,c_34])).

tff(c_10210,plain,(
    ! [A_15] :
      ( k1_relat_1(k7_relat_1('#skF_4',A_15)) = A_15
      | ~ r1_tarski(A_15,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_941,c_10200])).

tff(c_80,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_9958,plain,(
    ! [A_928,B_929,C_930,D_931] :
      ( k2_partfun1(A_928,B_929,C_930,D_931) = k7_relat_1(C_930,D_931)
      | ~ m1_subset_1(C_930,k1_zfmisc_1(k2_zfmisc_1(A_928,B_929)))
      | ~ v1_funct_1(C_930) ) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_9967,plain,(
    ! [D_931] :
      ( k2_partfun1('#skF_1','#skF_2','#skF_4',D_931) = k7_relat_1('#skF_4',D_931)
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_76,c_9958])).

tff(c_9982,plain,(
    ! [D_931] : k2_partfun1('#skF_1','#skF_2','#skF_4',D_931) = k7_relat_1('#skF_4',D_931) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_9967])).

tff(c_2050,plain,(
    ! [A_304,B_305,C_306,D_307] :
      ( k2_partfun1(A_304,B_305,C_306,D_307) = k7_relat_1(C_306,D_307)
      | ~ m1_subset_1(C_306,k1_zfmisc_1(k2_zfmisc_1(A_304,B_305)))
      | ~ v1_funct_1(C_306) ) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_2057,plain,(
    ! [D_307] :
      ( k2_partfun1('#skF_1','#skF_2','#skF_4',D_307) = k7_relat_1('#skF_4',D_307)
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_76,c_2050])).

tff(c_2069,plain,(
    ! [D_307] : k2_partfun1('#skF_1','#skF_2','#skF_4',D_307) = k7_relat_1('#skF_4',D_307) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_2057])).

tff(c_2485,plain,(
    ! [A_334,B_335,C_336,D_337] :
      ( m1_subset_1(k2_partfun1(A_334,B_335,C_336,D_337),k1_zfmisc_1(k2_zfmisc_1(A_334,B_335)))
      | ~ m1_subset_1(C_336,k1_zfmisc_1(k2_zfmisc_1(A_334,B_335)))
      | ~ v1_funct_1(C_336) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_2521,plain,(
    ! [D_307] :
      ( m1_subset_1(k7_relat_1('#skF_4',D_307),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
      | ~ v1_funct_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2069,c_2485])).

tff(c_2628,plain,(
    ! [D_344] : m1_subset_1(k7_relat_1('#skF_4',D_344),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_76,c_2521])).

tff(c_40,plain,(
    ! [C_25,B_24,A_23] :
      ( v5_relat_1(C_25,B_24)
      | ~ m1_subset_1(C_25,k1_zfmisc_1(k2_zfmisc_1(A_23,B_24))) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_2676,plain,(
    ! [D_344] : v5_relat_1(k7_relat_1('#skF_4',D_344),'#skF_2') ),
    inference(resolution,[status(thm)],[c_2628,c_40])).

tff(c_38,plain,(
    ! [C_22,A_20,B_21] :
      ( v1_relat_1(C_22)
      | ~ m1_subset_1(C_22,k1_zfmisc_1(k2_zfmisc_1(A_20,B_21))) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_2678,plain,(
    ! [D_344] : v1_relat_1(k7_relat_1('#skF_4',D_344)) ),
    inference(resolution,[status(thm)],[c_2628,c_38])).

tff(c_28,plain,(
    ! [B_14,A_13] :
      ( r1_tarski(k2_relat_1(B_14),A_13)
      | ~ v5_relat_1(B_14,A_13)
      | ~ v1_relat_1(B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_1749,plain,(
    ! [A_265,B_266,C_267,D_268] :
      ( v1_funct_1(k2_partfun1(A_265,B_266,C_267,D_268))
      | ~ m1_subset_1(C_267,k1_zfmisc_1(k2_zfmisc_1(A_265,B_266)))
      | ~ v1_funct_1(C_267) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_1754,plain,(
    ! [D_268] :
      ( v1_funct_1(k2_partfun1('#skF_1','#skF_2','#skF_4',D_268))
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_76,c_1749])).

tff(c_1765,plain,(
    ! [D_268] : v1_funct_1(k2_partfun1('#skF_1','#skF_2','#skF_4',D_268)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_1754])).

tff(c_2073,plain,(
    ! [D_268] : v1_funct_1(k7_relat_1('#skF_4',D_268)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2069,c_1765])).

tff(c_1417,plain,(
    ! [A_226,B_227,C_228] :
      ( k1_relset_1(A_226,B_227,C_228) = k1_relat_1(C_228)
      | ~ m1_subset_1(C_228,k1_zfmisc_1(k2_zfmisc_1(A_226,B_227))) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_1436,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_76,c_1417])).

tff(c_2153,plain,(
    ! [B_318,A_319,C_320] :
      ( k1_xboole_0 = B_318
      | k1_relset_1(A_319,B_318,C_320) = A_319
      | ~ v1_funct_2(C_320,A_319,B_318)
      | ~ m1_subset_1(C_320,k1_zfmisc_1(k2_zfmisc_1(A_319,B_318))) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_2163,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1('#skF_1','#skF_2','#skF_4') = '#skF_1'
    | ~ v1_funct_2('#skF_4','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_76,c_2153])).

tff(c_2178,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_1436,c_2163])).

tff(c_2179,plain,(
    k1_relat_1('#skF_4') = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_119,c_2178])).

tff(c_2196,plain,(
    ! [A_15] :
      ( k1_relat_1(k7_relat_1('#skF_4',A_15)) = A_15
      | ~ r1_tarski(A_15,'#skF_1')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2179,c_34])).

tff(c_2206,plain,(
    ! [A_15] :
      ( k1_relat_1(k7_relat_1('#skF_4',A_15)) = A_15
      | ~ r1_tarski(A_15,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_941,c_2196])).

tff(c_1868,plain,(
    ! [B_286,A_287] :
      ( m1_subset_1(B_286,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B_286),A_287)))
      | ~ r1_tarski(k2_relat_1(B_286),A_287)
      | ~ v1_funct_1(B_286)
      | ~ v1_relat_1(B_286) ) ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_20,plain,(
    ! [A_8,B_9] :
      ( r1_tarski(A_8,B_9)
      | ~ m1_subset_1(A_8,k1_zfmisc_1(B_9)) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_3834,plain,(
    ! [B_470,A_471] :
      ( r1_tarski(B_470,k2_zfmisc_1(k1_relat_1(B_470),A_471))
      | ~ r1_tarski(k2_relat_1(B_470),A_471)
      | ~ v1_funct_1(B_470)
      | ~ v1_relat_1(B_470) ) ),
    inference(resolution,[status(thm)],[c_1868,c_20])).

tff(c_3891,plain,(
    ! [A_15,A_471] :
      ( r1_tarski(k7_relat_1('#skF_4',A_15),k2_zfmisc_1(A_15,A_471))
      | ~ r1_tarski(k2_relat_1(k7_relat_1('#skF_4',A_15)),A_471)
      | ~ v1_funct_1(k7_relat_1('#skF_4',A_15))
      | ~ v1_relat_1(k7_relat_1('#skF_4',A_15))
      | ~ r1_tarski(A_15,'#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2206,c_3834])).

tff(c_6382,plain,(
    ! [A_606,A_607] :
      ( r1_tarski(k7_relat_1('#skF_4',A_606),k2_zfmisc_1(A_606,A_607))
      | ~ r1_tarski(k2_relat_1(k7_relat_1('#skF_4',A_606)),A_607)
      | ~ r1_tarski(A_606,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2678,c_2073,c_3891])).

tff(c_6390,plain,(
    ! [A_606,A_13] :
      ( r1_tarski(k7_relat_1('#skF_4',A_606),k2_zfmisc_1(A_606,A_13))
      | ~ r1_tarski(A_606,'#skF_1')
      | ~ v5_relat_1(k7_relat_1('#skF_4',A_606),A_13)
      | ~ v1_relat_1(k7_relat_1('#skF_4',A_606)) ) ),
    inference(resolution,[status(thm)],[c_28,c_6382])).

tff(c_8691,plain,(
    ! [A_767,A_768] :
      ( r1_tarski(k7_relat_1('#skF_4',A_767),k2_zfmisc_1(A_767,A_768))
      | ~ r1_tarski(A_767,'#skF_1')
      | ~ v5_relat_1(k7_relat_1('#skF_4',A_767),A_768) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2678,c_6390])).

tff(c_22,plain,(
    ! [A_8,B_9] :
      ( m1_subset_1(A_8,k1_zfmisc_1(B_9))
      | ~ r1_tarski(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_882,plain,(
    ! [A_151,B_152,C_153,D_154] :
      ( v1_funct_1(k2_partfun1(A_151,B_152,C_153,D_154))
      | ~ m1_subset_1(C_153,k1_zfmisc_1(k2_zfmisc_1(A_151,B_152)))
      | ~ v1_funct_1(C_153) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_887,plain,(
    ! [D_154] :
      ( v1_funct_1(k2_partfun1('#skF_1','#skF_2','#skF_4',D_154))
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_76,c_882])).

tff(c_898,plain,(
    ! [D_154] : v1_funct_1(k2_partfun1('#skF_1','#skF_2','#skF_4',D_154)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_887])).

tff(c_70,plain,
    ( ~ m1_subset_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2')))
    | ~ v1_funct_2(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),'#skF_3','#skF_2')
    | ~ v1_funct_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_146,plain,(
    ~ v1_funct_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_70])).

tff(c_904,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_898,c_146])).

tff(c_905,plain,
    ( ~ v1_funct_2(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),'#skF_3','#skF_2')
    | ~ m1_subset_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_70])).

tff(c_943,plain,(
    ~ m1_subset_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_905])).

tff(c_1093,plain,(
    ~ r1_tarski(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),k2_zfmisc_1('#skF_3','#skF_2')) ),
    inference(resolution,[status(thm)],[c_22,c_943])).

tff(c_2074,plain,(
    ~ r1_tarski(k7_relat_1('#skF_4','#skF_3'),k2_zfmisc_1('#skF_3','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2069,c_1093])).

tff(c_8706,plain,
    ( ~ r1_tarski('#skF_3','#skF_1')
    | ~ v5_relat_1(k7_relat_1('#skF_4','#skF_3'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_8691,c_2074])).

tff(c_8747,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2676,c_74,c_8706])).

tff(c_8749,plain,(
    m1_subset_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_905])).

tff(c_9281,plain,(
    k1_relset_1('#skF_3','#skF_2',k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3')) = k1_relat_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3')) ),
    inference(resolution,[status(thm)],[c_8749,c_9260])).

tff(c_9989,plain,(
    k1_relset_1('#skF_3','#skF_2',k7_relat_1('#skF_4','#skF_3')) = k1_relat_1(k7_relat_1('#skF_4','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9982,c_9982,c_9281])).

tff(c_8748,plain,(
    ~ v1_funct_2(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),'#skF_3','#skF_2') ),
    inference(splitRight,[status(thm)],[c_905])).

tff(c_9996,plain,(
    ~ v1_funct_2(k7_relat_1('#skF_4','#skF_3'),'#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_9982,c_8748])).

tff(c_9995,plain,(
    m1_subset_1(k7_relat_1('#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9982,c_8749])).

tff(c_52,plain,(
    ! [B_30,C_31,A_29] :
      ( k1_xboole_0 = B_30
      | v1_funct_2(C_31,A_29,B_30)
      | k1_relset_1(A_29,B_30,C_31) != A_29
      | ~ m1_subset_1(C_31,k1_zfmisc_1(k2_zfmisc_1(A_29,B_30))) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_10066,plain,
    ( k1_xboole_0 = '#skF_2'
    | v1_funct_2(k7_relat_1('#skF_4','#skF_3'),'#skF_3','#skF_2')
    | k1_relset_1('#skF_3','#skF_2',k7_relat_1('#skF_4','#skF_3')) != '#skF_3' ),
    inference(resolution,[status(thm)],[c_9995,c_52])).

tff(c_10093,plain,(
    k1_relset_1('#skF_3','#skF_2',k7_relat_1('#skF_4','#skF_3')) != '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_9996,c_119,c_10066])).

tff(c_10767,plain,(
    k1_relat_1(k7_relat_1('#skF_4','#skF_3')) != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9989,c_10093])).

tff(c_10775,plain,(
    ~ r1_tarski('#skF_3','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_10210,c_10767])).

tff(c_10779,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_10775])).

tff(c_10780,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_72])).

tff(c_18,plain,(
    ! [A_7] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_7)) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_10782,plain,(
    ! [A_7] : m1_subset_1('#skF_1',k1_zfmisc_1(A_7)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10780,c_18])).

tff(c_10843,plain,(
    ! [A_986,B_987] :
      ( r1_tarski(A_986,B_987)
      | ~ m1_subset_1(A_986,k1_zfmisc_1(B_987)) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_10855,plain,(
    ! [A_7] : r1_tarski('#skF_1',A_7) ),
    inference(resolution,[status(thm)],[c_10782,c_10843])).

tff(c_14,plain,(
    ! [A_5] : k2_zfmisc_1(A_5,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_10783,plain,(
    ! [A_5] : k2_zfmisc_1(A_5,'#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10780,c_10780,c_14])).

tff(c_10781,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_72])).

tff(c_10792,plain,(
    '#skF_2' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10780,c_10781])).

tff(c_10833,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10783,c_10792,c_76])).

tff(c_10854,plain,(
    r1_tarski('#skF_4','#skF_1') ),
    inference(resolution,[status(thm)],[c_10833,c_10843])).

tff(c_10869,plain,(
    ! [B_991,A_992] :
      ( B_991 = A_992
      | ~ r1_tarski(B_991,A_992)
      | ~ r1_tarski(A_992,B_991) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_10873,plain,
    ( '#skF_1' = '#skF_4'
    | ~ r1_tarski('#skF_1','#skF_4') ),
    inference(resolution,[status(thm)],[c_10854,c_10869])).

tff(c_10881,plain,(
    '#skF_1' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10855,c_10873])).

tff(c_10793,plain,(
    v1_funct_2('#skF_4','#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10792,c_78])).

tff(c_11642,plain,(
    v1_funct_2('#skF_4','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10881,c_10881,c_10793])).

tff(c_16,plain,(
    ! [B_6] : k2_zfmisc_1(k1_xboole_0,B_6) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_10784,plain,(
    ! [B_6] : k2_zfmisc_1('#skF_1',B_6) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10780,c_10780,c_16])).

tff(c_11640,plain,(
    ! [B_6] : k2_zfmisc_1('#skF_4',B_6) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10881,c_10881,c_10784])).

tff(c_11639,plain,(
    ! [A_7] : m1_subset_1('#skF_4',k1_zfmisc_1(A_7)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10881,c_10782])).

tff(c_12779,plain,(
    ! [A_1243,B_1244,C_1245,D_1246] :
      ( k2_partfun1(A_1243,B_1244,C_1245,D_1246) = k7_relat_1(C_1245,D_1246)
      | ~ m1_subset_1(C_1245,k1_zfmisc_1(k2_zfmisc_1(A_1243,B_1244)))
      | ~ v1_funct_1(C_1245) ) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_12786,plain,(
    ! [A_1243,B_1244,D_1246] :
      ( k2_partfun1(A_1243,B_1244,'#skF_4',D_1246) = k7_relat_1('#skF_4',D_1246)
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_11639,c_12779])).

tff(c_12795,plain,(
    ! [A_1243,B_1244,D_1246] : k2_partfun1(A_1243,B_1244,'#skF_4',D_1246) = k7_relat_1('#skF_4',D_1246) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_12786])).

tff(c_13023,plain,(
    ! [A_1281,B_1282,C_1283,D_1284] :
      ( m1_subset_1(k2_partfun1(A_1281,B_1282,C_1283,D_1284),k1_zfmisc_1(k2_zfmisc_1(A_1281,B_1282)))
      | ~ m1_subset_1(C_1283,k1_zfmisc_1(k2_zfmisc_1(A_1281,B_1282)))
      | ~ v1_funct_1(C_1283) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_13056,plain,(
    ! [D_1246,A_1243,B_1244] :
      ( m1_subset_1(k7_relat_1('#skF_4',D_1246),k1_zfmisc_1(k2_zfmisc_1(A_1243,B_1244)))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(A_1243,B_1244)))
      | ~ v1_funct_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12795,c_13023])).

tff(c_13080,plain,(
    ! [D_1285,A_1286,B_1287] : m1_subset_1(k7_relat_1('#skF_4',D_1285),k1_zfmisc_1(k2_zfmisc_1(A_1286,B_1287))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_11639,c_13056])).

tff(c_13114,plain,(
    ! [D_1285] : m1_subset_1(k7_relat_1('#skF_4',D_1285),k1_zfmisc_1('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_11640,c_13080])).

tff(c_10904,plain,(
    ! [A_7] : m1_subset_1('#skF_4',k1_zfmisc_1(A_7)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10881,c_10782])).

tff(c_11612,plain,(
    ! [A_1088,B_1089,C_1090,D_1091] :
      ( v1_funct_1(k2_partfun1(A_1088,B_1089,C_1090,D_1091))
      | ~ m1_subset_1(C_1090,k1_zfmisc_1(k2_zfmisc_1(A_1088,B_1089)))
      | ~ v1_funct_1(C_1090) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_11617,plain,(
    ! [A_1088,B_1089,D_1091] :
      ( v1_funct_1(k2_partfun1(A_1088,B_1089,'#skF_4',D_1091))
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_10904,c_11612])).

tff(c_11625,plain,(
    ! [A_1088,B_1089,D_1091] : v1_funct_1(k2_partfun1(A_1088,B_1089,'#skF_4',D_1091)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_11617])).

tff(c_10877,plain,
    ( '#skF_3' = '#skF_1'
    | ~ r1_tarski('#skF_1','#skF_3') ),
    inference(resolution,[status(thm)],[c_74,c_10869])).

tff(c_10888,plain,(
    '#skF_3' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10855,c_10877])).

tff(c_10895,plain,
    ( ~ m1_subset_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1'),k1_zfmisc_1('#skF_1'))
    | ~ v1_funct_2(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1'),'#skF_1','#skF_1')
    | ~ v1_funct_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10888,c_10792,c_10888,c_10888,c_10792,c_10792,c_10888,c_10783,c_10792,c_10792,c_70])).

tff(c_10896,plain,(
    ~ v1_funct_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_10895])).

tff(c_11028,plain,(
    ~ v1_funct_1(k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10881,c_10881,c_10881,c_10896])).

tff(c_11629,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_11625,c_11028])).

tff(c_11630,plain,
    ( ~ v1_funct_2(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1'),'#skF_1','#skF_1')
    | ~ m1_subset_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1'),k1_zfmisc_1('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_10895])).

tff(c_11829,plain,
    ( ~ v1_funct_2(k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_4'),'#skF_4','#skF_4')
    | ~ m1_subset_1(k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_4'),k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10881,c_10881,c_10881,c_10881,c_10881,c_10881,c_10881,c_10881,c_10881,c_11630])).

tff(c_11830,plain,(
    ~ m1_subset_1(k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_4'),k1_zfmisc_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_11829])).

tff(c_12817,plain,(
    ~ m1_subset_1(k7_relat_1('#skF_4','#skF_4'),k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12795,c_11830])).

tff(c_13234,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_13114,c_12817])).

tff(c_13236,plain,(
    m1_subset_1(k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_4'),k1_zfmisc_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_11829])).

tff(c_13382,plain,(
    r1_tarski(k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_4'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_13236,c_20])).

tff(c_10878,plain,(
    ! [A_7] :
      ( A_7 = '#skF_1'
      | ~ r1_tarski(A_7,'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_10855,c_10869])).

tff(c_11740,plain,(
    ! [A_7] :
      ( A_7 = '#skF_4'
      | ~ r1_tarski(A_7,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10881,c_10881,c_10878])).

tff(c_13393,plain,(
    k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_4') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_13382,c_11740])).

tff(c_13235,plain,(
    ~ v1_funct_2(k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_4'),'#skF_4','#skF_4') ),
    inference(splitRight,[status(thm)],[c_11829])).

tff(c_13400,plain,(
    ~ v1_funct_2('#skF_4','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_13393,c_13235])).

tff(c_13407,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_11642,c_13400])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n024.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 16:21:21 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 9.71/3.37  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.91/3.38  
% 9.91/3.38  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.91/3.38  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_partfun1 > k1_relset_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 9.91/3.38  
% 9.91/3.38  %Foreground sorts:
% 9.91/3.38  
% 9.91/3.38  
% 9.91/3.38  %Background operators:
% 9.91/3.38  
% 9.91/3.38  
% 9.91/3.38  %Foreground operators:
% 9.91/3.38  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 9.91/3.38  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 9.91/3.38  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 9.91/3.38  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 9.91/3.38  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 9.91/3.38  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 9.91/3.38  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 9.91/3.38  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 9.91/3.38  tff('#skF_2', type, '#skF_2': $i).
% 9.91/3.38  tff('#skF_3', type, '#skF_3': $i).
% 9.91/3.38  tff('#skF_1', type, '#skF_1': $i).
% 9.91/3.38  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 9.91/3.38  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 9.91/3.38  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 9.91/3.38  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 9.91/3.38  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 9.91/3.38  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 9.91/3.38  tff('#skF_4', type, '#skF_4': $i).
% 9.91/3.38  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 9.91/3.38  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 9.91/3.38  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 9.91/3.38  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 9.91/3.38  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 9.91/3.38  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 9.91/3.38  
% 9.91/3.40  tff(f_160, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r1_tarski(C, A) => (((B = k1_xboole_0) & ~(A = k1_xboole_0)) | ((v1_funct_1(k2_partfun1(A, B, D, C)) & v1_funct_2(k2_partfun1(A, B, D, C), C, B)) & m1_subset_1(k2_partfun1(A, B, D, C), k1_zfmisc_1(k2_zfmisc_1(C, B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_funct_2)).
% 9.91/3.40  tff(f_86, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 9.91/3.40  tff(f_96, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 9.91/3.40  tff(f_114, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 9.91/3.40  tff(f_73, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(A, k1_relat_1(B)) => (k1_relat_1(k7_relat_1(B, A)) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_relat_1)).
% 9.91/3.40  tff(f_128, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (k2_partfun1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_partfun1)).
% 9.91/3.40  tff(f_122, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (v1_funct_1(k2_partfun1(A, B, C, D)) & m1_subset_1(k2_partfun1(A, B, C, D), k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_partfun1)).
% 9.91/3.40  tff(f_92, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 9.91/3.41  tff(f_64, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 9.91/3.41  tff(f_140, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r1_tarski(k2_relat_1(B), A) => ((v1_funct_1(B) & v1_funct_2(B, k1_relat_1(B), A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B), A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_funct_2)).
% 9.91/3.41  tff(f_52, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 9.91/3.41  tff(f_48, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 9.91/3.41  tff(f_46, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 9.91/3.41  tff(f_32, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 9.91/3.41  tff(c_74, plain, (r1_tarski('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_160])).
% 9.91/3.41  tff(c_76, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_160])).
% 9.91/3.41  tff(c_924, plain, (![C_157, A_158, B_159]: (v1_relat_1(C_157) | ~m1_subset_1(C_157, k1_zfmisc_1(k2_zfmisc_1(A_158, B_159))))), inference(cnfTransformation, [status(thm)], [f_86])).
% 9.91/3.41  tff(c_941, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_76, c_924])).
% 9.91/3.41  tff(c_72, plain, (k1_xboole_0='#skF_1' | k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_160])).
% 9.91/3.41  tff(c_119, plain, (k1_xboole_0!='#skF_2'), inference(splitLeft, [status(thm)], [c_72])).
% 9.91/3.41  tff(c_78, plain, (v1_funct_2('#skF_4', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_160])).
% 9.91/3.41  tff(c_9260, plain, (![A_838, B_839, C_840]: (k1_relset_1(A_838, B_839, C_840)=k1_relat_1(C_840) | ~m1_subset_1(C_840, k1_zfmisc_1(k2_zfmisc_1(A_838, B_839))))), inference(cnfTransformation, [status(thm)], [f_96])).
% 9.91/3.41  tff(c_9283, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_76, c_9260])).
% 9.91/3.41  tff(c_10152, plain, (![B_943, A_944, C_945]: (k1_xboole_0=B_943 | k1_relset_1(A_944, B_943, C_945)=A_944 | ~v1_funct_2(C_945, A_944, B_943) | ~m1_subset_1(C_945, k1_zfmisc_1(k2_zfmisc_1(A_944, B_943))))), inference(cnfTransformation, [status(thm)], [f_114])).
% 9.91/3.41  tff(c_10165, plain, (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', '#skF_4')='#skF_1' | ~v1_funct_2('#skF_4', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_76, c_10152])).
% 9.91/3.41  tff(c_10182, plain, (k1_xboole_0='#skF_2' | k1_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_78, c_9283, c_10165])).
% 9.91/3.41  tff(c_10183, plain, (k1_relat_1('#skF_4')='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_119, c_10182])).
% 9.91/3.41  tff(c_34, plain, (![B_16, A_15]: (k1_relat_1(k7_relat_1(B_16, A_15))=A_15 | ~r1_tarski(A_15, k1_relat_1(B_16)) | ~v1_relat_1(B_16))), inference(cnfTransformation, [status(thm)], [f_73])).
% 9.91/3.41  tff(c_10200, plain, (![A_15]: (k1_relat_1(k7_relat_1('#skF_4', A_15))=A_15 | ~r1_tarski(A_15, '#skF_1') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_10183, c_34])).
% 9.91/3.41  tff(c_10210, plain, (![A_15]: (k1_relat_1(k7_relat_1('#skF_4', A_15))=A_15 | ~r1_tarski(A_15, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_941, c_10200])).
% 9.91/3.41  tff(c_80, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_160])).
% 9.91/3.41  tff(c_9958, plain, (![A_928, B_929, C_930, D_931]: (k2_partfun1(A_928, B_929, C_930, D_931)=k7_relat_1(C_930, D_931) | ~m1_subset_1(C_930, k1_zfmisc_1(k2_zfmisc_1(A_928, B_929))) | ~v1_funct_1(C_930))), inference(cnfTransformation, [status(thm)], [f_128])).
% 9.91/3.41  tff(c_9967, plain, (![D_931]: (k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_931)=k7_relat_1('#skF_4', D_931) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_76, c_9958])).
% 9.91/3.41  tff(c_9982, plain, (![D_931]: (k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_931)=k7_relat_1('#skF_4', D_931))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_9967])).
% 9.91/3.41  tff(c_2050, plain, (![A_304, B_305, C_306, D_307]: (k2_partfun1(A_304, B_305, C_306, D_307)=k7_relat_1(C_306, D_307) | ~m1_subset_1(C_306, k1_zfmisc_1(k2_zfmisc_1(A_304, B_305))) | ~v1_funct_1(C_306))), inference(cnfTransformation, [status(thm)], [f_128])).
% 9.91/3.41  tff(c_2057, plain, (![D_307]: (k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_307)=k7_relat_1('#skF_4', D_307) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_76, c_2050])).
% 9.91/3.41  tff(c_2069, plain, (![D_307]: (k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_307)=k7_relat_1('#skF_4', D_307))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_2057])).
% 9.91/3.41  tff(c_2485, plain, (![A_334, B_335, C_336, D_337]: (m1_subset_1(k2_partfun1(A_334, B_335, C_336, D_337), k1_zfmisc_1(k2_zfmisc_1(A_334, B_335))) | ~m1_subset_1(C_336, k1_zfmisc_1(k2_zfmisc_1(A_334, B_335))) | ~v1_funct_1(C_336))), inference(cnfTransformation, [status(thm)], [f_122])).
% 9.91/3.41  tff(c_2521, plain, (![D_307]: (m1_subset_1(k7_relat_1('#skF_4', D_307), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_2069, c_2485])).
% 9.91/3.41  tff(c_2628, plain, (![D_344]: (m1_subset_1(k7_relat_1('#skF_4', D_344), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_76, c_2521])).
% 9.91/3.41  tff(c_40, plain, (![C_25, B_24, A_23]: (v5_relat_1(C_25, B_24) | ~m1_subset_1(C_25, k1_zfmisc_1(k2_zfmisc_1(A_23, B_24))))), inference(cnfTransformation, [status(thm)], [f_92])).
% 9.91/3.41  tff(c_2676, plain, (![D_344]: (v5_relat_1(k7_relat_1('#skF_4', D_344), '#skF_2'))), inference(resolution, [status(thm)], [c_2628, c_40])).
% 9.91/3.41  tff(c_38, plain, (![C_22, A_20, B_21]: (v1_relat_1(C_22) | ~m1_subset_1(C_22, k1_zfmisc_1(k2_zfmisc_1(A_20, B_21))))), inference(cnfTransformation, [status(thm)], [f_86])).
% 9.91/3.41  tff(c_2678, plain, (![D_344]: (v1_relat_1(k7_relat_1('#skF_4', D_344)))), inference(resolution, [status(thm)], [c_2628, c_38])).
% 9.91/3.41  tff(c_28, plain, (![B_14, A_13]: (r1_tarski(k2_relat_1(B_14), A_13) | ~v5_relat_1(B_14, A_13) | ~v1_relat_1(B_14))), inference(cnfTransformation, [status(thm)], [f_64])).
% 9.91/3.41  tff(c_1749, plain, (![A_265, B_266, C_267, D_268]: (v1_funct_1(k2_partfun1(A_265, B_266, C_267, D_268)) | ~m1_subset_1(C_267, k1_zfmisc_1(k2_zfmisc_1(A_265, B_266))) | ~v1_funct_1(C_267))), inference(cnfTransformation, [status(thm)], [f_122])).
% 9.91/3.41  tff(c_1754, plain, (![D_268]: (v1_funct_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_268)) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_76, c_1749])).
% 9.91/3.41  tff(c_1765, plain, (![D_268]: (v1_funct_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_268)))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_1754])).
% 9.91/3.41  tff(c_2073, plain, (![D_268]: (v1_funct_1(k7_relat_1('#skF_4', D_268)))), inference(demodulation, [status(thm), theory('equality')], [c_2069, c_1765])).
% 9.91/3.41  tff(c_1417, plain, (![A_226, B_227, C_228]: (k1_relset_1(A_226, B_227, C_228)=k1_relat_1(C_228) | ~m1_subset_1(C_228, k1_zfmisc_1(k2_zfmisc_1(A_226, B_227))))), inference(cnfTransformation, [status(thm)], [f_96])).
% 9.91/3.41  tff(c_1436, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_76, c_1417])).
% 9.91/3.41  tff(c_2153, plain, (![B_318, A_319, C_320]: (k1_xboole_0=B_318 | k1_relset_1(A_319, B_318, C_320)=A_319 | ~v1_funct_2(C_320, A_319, B_318) | ~m1_subset_1(C_320, k1_zfmisc_1(k2_zfmisc_1(A_319, B_318))))), inference(cnfTransformation, [status(thm)], [f_114])).
% 9.91/3.41  tff(c_2163, plain, (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', '#skF_4')='#skF_1' | ~v1_funct_2('#skF_4', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_76, c_2153])).
% 9.91/3.41  tff(c_2178, plain, (k1_xboole_0='#skF_2' | k1_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_78, c_1436, c_2163])).
% 9.91/3.41  tff(c_2179, plain, (k1_relat_1('#skF_4')='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_119, c_2178])).
% 9.91/3.41  tff(c_2196, plain, (![A_15]: (k1_relat_1(k7_relat_1('#skF_4', A_15))=A_15 | ~r1_tarski(A_15, '#skF_1') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_2179, c_34])).
% 9.91/3.41  tff(c_2206, plain, (![A_15]: (k1_relat_1(k7_relat_1('#skF_4', A_15))=A_15 | ~r1_tarski(A_15, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_941, c_2196])).
% 9.91/3.41  tff(c_1868, plain, (![B_286, A_287]: (m1_subset_1(B_286, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B_286), A_287))) | ~r1_tarski(k2_relat_1(B_286), A_287) | ~v1_funct_1(B_286) | ~v1_relat_1(B_286))), inference(cnfTransformation, [status(thm)], [f_140])).
% 9.91/3.41  tff(c_20, plain, (![A_8, B_9]: (r1_tarski(A_8, B_9) | ~m1_subset_1(A_8, k1_zfmisc_1(B_9)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 9.91/3.41  tff(c_3834, plain, (![B_470, A_471]: (r1_tarski(B_470, k2_zfmisc_1(k1_relat_1(B_470), A_471)) | ~r1_tarski(k2_relat_1(B_470), A_471) | ~v1_funct_1(B_470) | ~v1_relat_1(B_470))), inference(resolution, [status(thm)], [c_1868, c_20])).
% 9.91/3.41  tff(c_3891, plain, (![A_15, A_471]: (r1_tarski(k7_relat_1('#skF_4', A_15), k2_zfmisc_1(A_15, A_471)) | ~r1_tarski(k2_relat_1(k7_relat_1('#skF_4', A_15)), A_471) | ~v1_funct_1(k7_relat_1('#skF_4', A_15)) | ~v1_relat_1(k7_relat_1('#skF_4', A_15)) | ~r1_tarski(A_15, '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_2206, c_3834])).
% 9.91/3.41  tff(c_6382, plain, (![A_606, A_607]: (r1_tarski(k7_relat_1('#skF_4', A_606), k2_zfmisc_1(A_606, A_607)) | ~r1_tarski(k2_relat_1(k7_relat_1('#skF_4', A_606)), A_607) | ~r1_tarski(A_606, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_2678, c_2073, c_3891])).
% 9.91/3.41  tff(c_6390, plain, (![A_606, A_13]: (r1_tarski(k7_relat_1('#skF_4', A_606), k2_zfmisc_1(A_606, A_13)) | ~r1_tarski(A_606, '#skF_1') | ~v5_relat_1(k7_relat_1('#skF_4', A_606), A_13) | ~v1_relat_1(k7_relat_1('#skF_4', A_606)))), inference(resolution, [status(thm)], [c_28, c_6382])).
% 9.91/3.41  tff(c_8691, plain, (![A_767, A_768]: (r1_tarski(k7_relat_1('#skF_4', A_767), k2_zfmisc_1(A_767, A_768)) | ~r1_tarski(A_767, '#skF_1') | ~v5_relat_1(k7_relat_1('#skF_4', A_767), A_768))), inference(demodulation, [status(thm), theory('equality')], [c_2678, c_6390])).
% 9.91/3.41  tff(c_22, plain, (![A_8, B_9]: (m1_subset_1(A_8, k1_zfmisc_1(B_9)) | ~r1_tarski(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_52])).
% 9.91/3.41  tff(c_882, plain, (![A_151, B_152, C_153, D_154]: (v1_funct_1(k2_partfun1(A_151, B_152, C_153, D_154)) | ~m1_subset_1(C_153, k1_zfmisc_1(k2_zfmisc_1(A_151, B_152))) | ~v1_funct_1(C_153))), inference(cnfTransformation, [status(thm)], [f_122])).
% 9.91/3.41  tff(c_887, plain, (![D_154]: (v1_funct_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_154)) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_76, c_882])).
% 9.91/3.41  tff(c_898, plain, (![D_154]: (v1_funct_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_154)))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_887])).
% 9.91/3.41  tff(c_70, plain, (~m1_subset_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2'))) | ~v1_funct_2(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), '#skF_3', '#skF_2') | ~v1_funct_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_160])).
% 9.91/3.41  tff(c_146, plain, (~v1_funct_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'))), inference(splitLeft, [status(thm)], [c_70])).
% 9.91/3.41  tff(c_904, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_898, c_146])).
% 9.91/3.41  tff(c_905, plain, (~v1_funct_2(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), '#skF_3', '#skF_2') | ~m1_subset_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(splitRight, [status(thm)], [c_70])).
% 9.91/3.41  tff(c_943, plain, (~m1_subset_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(splitLeft, [status(thm)], [c_905])).
% 9.91/3.41  tff(c_1093, plain, (~r1_tarski(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), k2_zfmisc_1('#skF_3', '#skF_2'))), inference(resolution, [status(thm)], [c_22, c_943])).
% 9.91/3.41  tff(c_2074, plain, (~r1_tarski(k7_relat_1('#skF_4', '#skF_3'), k2_zfmisc_1('#skF_3', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_2069, c_1093])).
% 9.91/3.41  tff(c_8706, plain, (~r1_tarski('#skF_3', '#skF_1') | ~v5_relat_1(k7_relat_1('#skF_4', '#skF_3'), '#skF_2')), inference(resolution, [status(thm)], [c_8691, c_2074])).
% 9.91/3.41  tff(c_8747, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2676, c_74, c_8706])).
% 9.91/3.41  tff(c_8749, plain, (m1_subset_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(splitRight, [status(thm)], [c_905])).
% 9.91/3.41  tff(c_9281, plain, (k1_relset_1('#skF_3', '#skF_2', k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'))=k1_relat_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'))), inference(resolution, [status(thm)], [c_8749, c_9260])).
% 9.91/3.41  tff(c_9989, plain, (k1_relset_1('#skF_3', '#skF_2', k7_relat_1('#skF_4', '#skF_3'))=k1_relat_1(k7_relat_1('#skF_4', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_9982, c_9982, c_9281])).
% 9.91/3.41  tff(c_8748, plain, (~v1_funct_2(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), '#skF_3', '#skF_2')), inference(splitRight, [status(thm)], [c_905])).
% 9.91/3.41  tff(c_9996, plain, (~v1_funct_2(k7_relat_1('#skF_4', '#skF_3'), '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_9982, c_8748])).
% 9.91/3.41  tff(c_9995, plain, (m1_subset_1(k7_relat_1('#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_9982, c_8749])).
% 9.91/3.41  tff(c_52, plain, (![B_30, C_31, A_29]: (k1_xboole_0=B_30 | v1_funct_2(C_31, A_29, B_30) | k1_relset_1(A_29, B_30, C_31)!=A_29 | ~m1_subset_1(C_31, k1_zfmisc_1(k2_zfmisc_1(A_29, B_30))))), inference(cnfTransformation, [status(thm)], [f_114])).
% 9.91/3.41  tff(c_10066, plain, (k1_xboole_0='#skF_2' | v1_funct_2(k7_relat_1('#skF_4', '#skF_3'), '#skF_3', '#skF_2') | k1_relset_1('#skF_3', '#skF_2', k7_relat_1('#skF_4', '#skF_3'))!='#skF_3'), inference(resolution, [status(thm)], [c_9995, c_52])).
% 9.91/3.41  tff(c_10093, plain, (k1_relset_1('#skF_3', '#skF_2', k7_relat_1('#skF_4', '#skF_3'))!='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_9996, c_119, c_10066])).
% 9.91/3.41  tff(c_10767, plain, (k1_relat_1(k7_relat_1('#skF_4', '#skF_3'))!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_9989, c_10093])).
% 9.91/3.41  tff(c_10775, plain, (~r1_tarski('#skF_3', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_10210, c_10767])).
% 9.91/3.41  tff(c_10779, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_74, c_10775])).
% 9.91/3.41  tff(c_10780, plain, (k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_72])).
% 9.91/3.41  tff(c_18, plain, (![A_7]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_7)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 9.91/3.41  tff(c_10782, plain, (![A_7]: (m1_subset_1('#skF_1', k1_zfmisc_1(A_7)))), inference(demodulation, [status(thm), theory('equality')], [c_10780, c_18])).
% 9.91/3.41  tff(c_10843, plain, (![A_986, B_987]: (r1_tarski(A_986, B_987) | ~m1_subset_1(A_986, k1_zfmisc_1(B_987)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 9.91/3.41  tff(c_10855, plain, (![A_7]: (r1_tarski('#skF_1', A_7))), inference(resolution, [status(thm)], [c_10782, c_10843])).
% 9.91/3.41  tff(c_14, plain, (![A_5]: (k2_zfmisc_1(A_5, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_46])).
% 9.91/3.41  tff(c_10783, plain, (![A_5]: (k2_zfmisc_1(A_5, '#skF_1')='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_10780, c_10780, c_14])).
% 9.91/3.41  tff(c_10781, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_72])).
% 9.91/3.41  tff(c_10792, plain, ('#skF_2'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_10780, c_10781])).
% 9.91/3.41  tff(c_10833, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_10783, c_10792, c_76])).
% 9.91/3.41  tff(c_10854, plain, (r1_tarski('#skF_4', '#skF_1')), inference(resolution, [status(thm)], [c_10833, c_10843])).
% 9.91/3.41  tff(c_10869, plain, (![B_991, A_992]: (B_991=A_992 | ~r1_tarski(B_991, A_992) | ~r1_tarski(A_992, B_991))), inference(cnfTransformation, [status(thm)], [f_32])).
% 9.91/3.41  tff(c_10873, plain, ('#skF_1'='#skF_4' | ~r1_tarski('#skF_1', '#skF_4')), inference(resolution, [status(thm)], [c_10854, c_10869])).
% 9.91/3.41  tff(c_10881, plain, ('#skF_1'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_10855, c_10873])).
% 9.91/3.41  tff(c_10793, plain, (v1_funct_2('#skF_4', '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_10792, c_78])).
% 9.91/3.41  tff(c_11642, plain, (v1_funct_2('#skF_4', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_10881, c_10881, c_10793])).
% 9.91/3.41  tff(c_16, plain, (![B_6]: (k2_zfmisc_1(k1_xboole_0, B_6)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_46])).
% 9.91/3.41  tff(c_10784, plain, (![B_6]: (k2_zfmisc_1('#skF_1', B_6)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_10780, c_10780, c_16])).
% 9.91/3.41  tff(c_11640, plain, (![B_6]: (k2_zfmisc_1('#skF_4', B_6)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_10881, c_10881, c_10784])).
% 9.91/3.41  tff(c_11639, plain, (![A_7]: (m1_subset_1('#skF_4', k1_zfmisc_1(A_7)))), inference(demodulation, [status(thm), theory('equality')], [c_10881, c_10782])).
% 9.91/3.41  tff(c_12779, plain, (![A_1243, B_1244, C_1245, D_1246]: (k2_partfun1(A_1243, B_1244, C_1245, D_1246)=k7_relat_1(C_1245, D_1246) | ~m1_subset_1(C_1245, k1_zfmisc_1(k2_zfmisc_1(A_1243, B_1244))) | ~v1_funct_1(C_1245))), inference(cnfTransformation, [status(thm)], [f_128])).
% 9.91/3.41  tff(c_12786, plain, (![A_1243, B_1244, D_1246]: (k2_partfun1(A_1243, B_1244, '#skF_4', D_1246)=k7_relat_1('#skF_4', D_1246) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_11639, c_12779])).
% 9.91/3.41  tff(c_12795, plain, (![A_1243, B_1244, D_1246]: (k2_partfun1(A_1243, B_1244, '#skF_4', D_1246)=k7_relat_1('#skF_4', D_1246))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_12786])).
% 9.91/3.41  tff(c_13023, plain, (![A_1281, B_1282, C_1283, D_1284]: (m1_subset_1(k2_partfun1(A_1281, B_1282, C_1283, D_1284), k1_zfmisc_1(k2_zfmisc_1(A_1281, B_1282))) | ~m1_subset_1(C_1283, k1_zfmisc_1(k2_zfmisc_1(A_1281, B_1282))) | ~v1_funct_1(C_1283))), inference(cnfTransformation, [status(thm)], [f_122])).
% 9.91/3.41  tff(c_13056, plain, (![D_1246, A_1243, B_1244]: (m1_subset_1(k7_relat_1('#skF_4', D_1246), k1_zfmisc_1(k2_zfmisc_1(A_1243, B_1244))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(A_1243, B_1244))) | ~v1_funct_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_12795, c_13023])).
% 9.91/3.41  tff(c_13080, plain, (![D_1285, A_1286, B_1287]: (m1_subset_1(k7_relat_1('#skF_4', D_1285), k1_zfmisc_1(k2_zfmisc_1(A_1286, B_1287))))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_11639, c_13056])).
% 9.91/3.41  tff(c_13114, plain, (![D_1285]: (m1_subset_1(k7_relat_1('#skF_4', D_1285), k1_zfmisc_1('#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_11640, c_13080])).
% 9.91/3.41  tff(c_10904, plain, (![A_7]: (m1_subset_1('#skF_4', k1_zfmisc_1(A_7)))), inference(demodulation, [status(thm), theory('equality')], [c_10881, c_10782])).
% 9.91/3.41  tff(c_11612, plain, (![A_1088, B_1089, C_1090, D_1091]: (v1_funct_1(k2_partfun1(A_1088, B_1089, C_1090, D_1091)) | ~m1_subset_1(C_1090, k1_zfmisc_1(k2_zfmisc_1(A_1088, B_1089))) | ~v1_funct_1(C_1090))), inference(cnfTransformation, [status(thm)], [f_122])).
% 9.91/3.41  tff(c_11617, plain, (![A_1088, B_1089, D_1091]: (v1_funct_1(k2_partfun1(A_1088, B_1089, '#skF_4', D_1091)) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_10904, c_11612])).
% 9.91/3.41  tff(c_11625, plain, (![A_1088, B_1089, D_1091]: (v1_funct_1(k2_partfun1(A_1088, B_1089, '#skF_4', D_1091)))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_11617])).
% 9.91/3.41  tff(c_10877, plain, ('#skF_3'='#skF_1' | ~r1_tarski('#skF_1', '#skF_3')), inference(resolution, [status(thm)], [c_74, c_10869])).
% 9.91/3.41  tff(c_10888, plain, ('#skF_3'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_10855, c_10877])).
% 9.91/3.41  tff(c_10895, plain, (~m1_subset_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'), k1_zfmisc_1('#skF_1')) | ~v1_funct_2(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'), '#skF_1', '#skF_1') | ~v1_funct_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_10888, c_10792, c_10888, c_10888, c_10792, c_10792, c_10888, c_10783, c_10792, c_10792, c_70])).
% 9.91/3.41  tff(c_10896, plain, (~v1_funct_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'))), inference(splitLeft, [status(thm)], [c_10895])).
% 9.91/3.41  tff(c_11028, plain, (~v1_funct_1(k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_10881, c_10881, c_10881, c_10896])).
% 9.91/3.41  tff(c_11629, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_11625, c_11028])).
% 9.91/3.41  tff(c_11630, plain, (~v1_funct_2(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'), '#skF_1', '#skF_1') | ~m1_subset_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'), k1_zfmisc_1('#skF_1'))), inference(splitRight, [status(thm)], [c_10895])).
% 9.91/3.41  tff(c_11829, plain, (~v1_funct_2(k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_4'), '#skF_4', '#skF_4') | ~m1_subset_1(k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_4'), k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_10881, c_10881, c_10881, c_10881, c_10881, c_10881, c_10881, c_10881, c_10881, c_11630])).
% 9.91/3.41  tff(c_11830, plain, (~m1_subset_1(k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_4'), k1_zfmisc_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_11829])).
% 9.91/3.41  tff(c_12817, plain, (~m1_subset_1(k7_relat_1('#skF_4', '#skF_4'), k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_12795, c_11830])).
% 9.91/3.41  tff(c_13234, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_13114, c_12817])).
% 9.91/3.41  tff(c_13236, plain, (m1_subset_1(k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_4'), k1_zfmisc_1('#skF_4'))), inference(splitRight, [status(thm)], [c_11829])).
% 9.91/3.41  tff(c_13382, plain, (r1_tarski(k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_4'), '#skF_4')), inference(resolution, [status(thm)], [c_13236, c_20])).
% 9.91/3.41  tff(c_10878, plain, (![A_7]: (A_7='#skF_1' | ~r1_tarski(A_7, '#skF_1'))), inference(resolution, [status(thm)], [c_10855, c_10869])).
% 9.91/3.41  tff(c_11740, plain, (![A_7]: (A_7='#skF_4' | ~r1_tarski(A_7, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_10881, c_10881, c_10878])).
% 9.91/3.41  tff(c_13393, plain, (k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_4')='#skF_4'), inference(resolution, [status(thm)], [c_13382, c_11740])).
% 9.91/3.41  tff(c_13235, plain, (~v1_funct_2(k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_4'), '#skF_4', '#skF_4')), inference(splitRight, [status(thm)], [c_11829])).
% 9.91/3.41  tff(c_13400, plain, (~v1_funct_2('#skF_4', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_13393, c_13235])).
% 9.91/3.41  tff(c_13407, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_11642, c_13400])).
% 9.91/3.41  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.91/3.41  
% 9.91/3.41  Inference rules
% 9.91/3.41  ----------------------
% 9.91/3.41  #Ref     : 0
% 9.91/3.41  #Sup     : 2791
% 9.91/3.41  #Fact    : 0
% 9.91/3.41  #Define  : 0
% 9.91/3.41  #Split   : 25
% 9.91/3.41  #Chain   : 0
% 9.91/3.41  #Close   : 0
% 9.91/3.41  
% 9.91/3.41  Ordering : KBO
% 9.91/3.41  
% 9.91/3.41  Simplification rules
% 9.91/3.41  ----------------------
% 9.91/3.41  #Subsume      : 322
% 9.91/3.41  #Demod        : 3744
% 9.91/3.41  #Tautology    : 1327
% 9.91/3.41  #SimpNegUnit  : 28
% 9.91/3.41  #BackRed      : 112
% 9.91/3.41  
% 9.91/3.41  #Partial instantiations: 0
% 9.91/3.41  #Strategies tried      : 1
% 9.91/3.41  
% 9.91/3.41  Timing (in seconds)
% 9.91/3.41  ----------------------
% 9.91/3.41  Preprocessing        : 0.35
% 9.91/3.41  Parsing              : 0.19
% 9.91/3.41  CNF conversion       : 0.02
% 9.91/3.41  Main loop            : 2.27
% 9.91/3.41  Inferencing          : 0.75
% 9.91/3.41  Reduction            : 0.87
% 9.91/3.41  Demodulation         : 0.65
% 9.91/3.41  BG Simplification    : 0.06
% 9.91/3.41  Subsumption          : 0.42
% 9.91/3.41  Abstraction          : 0.08
% 9.91/3.41  MUC search           : 0.00
% 9.91/3.41  Cooper               : 0.00
% 9.91/3.41  Total                : 2.66
% 9.91/3.41  Index Insertion      : 0.00
% 9.91/3.41  Index Deletion       : 0.00
% 9.91/3.41  Index Matching       : 0.00
% 9.91/3.41  BG Taut test         : 0.00
%------------------------------------------------------------------------------
