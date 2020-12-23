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
% DateTime   : Thu Dec  3 10:13:41 EST 2020

% Result     : Theorem 5.92s
% Output     : CNFRefutation 6.41s
% Verified   : 
% Statistics : Number of formulae       :  153 (2794 expanded)
%              Number of leaves         :   38 ( 874 expanded)
%              Depth                    :   14
%              Number of atoms          :  245 (8786 expanded)
%              Number of equality atoms :   61 (3490 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal term depth       :    3 (   2 average)

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

tff(f_138,negated_conjecture,(
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

tff(f_54,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_46,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_78,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_104,axiom,(
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

tff(f_68,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(A,k1_relat_1(B))
       => k1_relat_1(k7_relat_1(B,A)) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_relat_1)).

tff(f_118,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => k2_partfun1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

tff(f_58,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k1_relat_1(k7_relat_1(B,A)),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_relat_1)).

tff(f_112,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( v1_funct_1(k2_partfun1(A,B,C,D))
        & m1_subset_1(k2_partfun1(A,B,C,D),k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_partfun1)).

tff(f_74,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_62,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k7_relat_1(B,A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_relat_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_86,axiom,(
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

tff(c_58,plain,(
    r1_tarski('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_20,plain,(
    ! [A_11,B_12] : v1_relat_1(k2_zfmisc_1(A_11,B_12)) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_60,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_679,plain,(
    ! [B_126,A_127] :
      ( v1_relat_1(B_126)
      | ~ m1_subset_1(B_126,k1_zfmisc_1(A_127))
      | ~ v1_relat_1(A_127) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_685,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_60,c_679])).

tff(c_689,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_685])).

tff(c_56,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_69,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_56])).

tff(c_62,plain,(
    v1_funct_2('#skF_4','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_2408,plain,(
    ! [A_324,B_325,C_326] :
      ( k1_relset_1(A_324,B_325,C_326) = k1_relat_1(C_326)
      | ~ m1_subset_1(C_326,k1_zfmisc_1(k2_zfmisc_1(A_324,B_325))) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_2427,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_60,c_2408])).

tff(c_2977,plain,(
    ! [B_389,A_390,C_391] :
      ( k1_xboole_0 = B_389
      | k1_relset_1(A_390,B_389,C_391) = A_390
      | ~ v1_funct_2(C_391,A_390,B_389)
      | ~ m1_subset_1(C_391,k1_zfmisc_1(k2_zfmisc_1(A_390,B_389))) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_2990,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1('#skF_1','#skF_2','#skF_4') = '#skF_1'
    | ~ v1_funct_2('#skF_4','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_60,c_2977])).

tff(c_3003,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_2427,c_2990])).

tff(c_3004,plain,(
    k1_relat_1('#skF_4') = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_69,c_3003])).

tff(c_26,plain,(
    ! [B_18,A_17] :
      ( k1_relat_1(k7_relat_1(B_18,A_17)) = A_17
      | ~ r1_tarski(A_17,k1_relat_1(B_18))
      | ~ v1_relat_1(B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_3010,plain,(
    ! [A_17] :
      ( k1_relat_1(k7_relat_1('#skF_4',A_17)) = A_17
      | ~ r1_tarski(A_17,'#skF_1')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3004,c_26])).

tff(c_3014,plain,(
    ! [A_17] :
      ( k1_relat_1(k7_relat_1('#skF_4',A_17)) = A_17
      | ~ r1_tarski(A_17,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_689,c_3010])).

tff(c_64,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_2799,plain,(
    ! [A_375,B_376,C_377,D_378] :
      ( k2_partfun1(A_375,B_376,C_377,D_378) = k7_relat_1(C_377,D_378)
      | ~ m1_subset_1(C_377,k1_zfmisc_1(k2_zfmisc_1(A_375,B_376)))
      | ~ v1_funct_1(C_377) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_2808,plain,(
    ! [D_378] :
      ( k2_partfun1('#skF_1','#skF_2','#skF_4',D_378) = k7_relat_1('#skF_4',D_378)
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_60,c_2799])).

tff(c_2820,plain,(
    ! [D_378] : k2_partfun1('#skF_1','#skF_2','#skF_4',D_378) = k7_relat_1('#skF_4',D_378) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_2808])).

tff(c_22,plain,(
    ! [B_14,A_13] :
      ( r1_tarski(k1_relat_1(k7_relat_1(B_14,A_13)),A_13)
      | ~ v1_relat_1(B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_1169,plain,(
    ! [A_199,B_200,C_201,D_202] :
      ( k2_partfun1(A_199,B_200,C_201,D_202) = k7_relat_1(C_201,D_202)
      | ~ m1_subset_1(C_201,k1_zfmisc_1(k2_zfmisc_1(A_199,B_200)))
      | ~ v1_funct_1(C_201) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_1174,plain,(
    ! [D_202] :
      ( k2_partfun1('#skF_1','#skF_2','#skF_4',D_202) = k7_relat_1('#skF_4',D_202)
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_60,c_1169])).

tff(c_1182,plain,(
    ! [D_202] : k2_partfun1('#skF_1','#skF_2','#skF_4',D_202) = k7_relat_1('#skF_4',D_202) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_1174])).

tff(c_1827,plain,(
    ! [A_261,B_262,C_263,D_264] :
      ( m1_subset_1(k2_partfun1(A_261,B_262,C_263,D_264),k1_zfmisc_1(k2_zfmisc_1(A_261,B_262)))
      | ~ m1_subset_1(C_263,k1_zfmisc_1(k2_zfmisc_1(A_261,B_262)))
      | ~ v1_funct_1(C_263) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_1855,plain,(
    ! [D_202] :
      ( m1_subset_1(k7_relat_1('#skF_4',D_202),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
      | ~ v1_funct_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1182,c_1827])).

tff(c_1877,plain,(
    ! [D_265] : m1_subset_1(k7_relat_1('#skF_4',D_265),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_60,c_1855])).

tff(c_28,plain,(
    ! [C_21,B_20,A_19] :
      ( v5_relat_1(C_21,B_20)
      | ~ m1_subset_1(C_21,k1_zfmisc_1(k2_zfmisc_1(A_19,B_20))) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_1916,plain,(
    ! [D_265] : v5_relat_1(k7_relat_1('#skF_4',D_265),'#skF_2') ),
    inference(resolution,[status(thm)],[c_1877,c_28])).

tff(c_24,plain,(
    ! [B_16,A_15] :
      ( r1_tarski(k7_relat_1(B_16,A_15),B_16)
      | ~ v1_relat_1(B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_12,plain,(
    ! [A_4,B_5] :
      ( m1_subset_1(A_4,k1_zfmisc_1(B_5))
      | ~ r1_tarski(A_4,B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_690,plain,(
    ! [A_128,B_129] :
      ( v1_relat_1(A_128)
      | ~ v1_relat_1(B_129)
      | ~ r1_tarski(A_128,B_129) ) ),
    inference(resolution,[status(thm)],[c_12,c_679])).

tff(c_712,plain,(
    ! [B_16,A_15] :
      ( v1_relat_1(k7_relat_1(B_16,A_15))
      | ~ v1_relat_1(B_16) ) ),
    inference(resolution,[status(thm)],[c_24,c_690])).

tff(c_1265,plain,(
    ! [C_216,A_217,B_218] :
      ( m1_subset_1(C_216,k1_zfmisc_1(k2_zfmisc_1(A_217,B_218)))
      | ~ r1_tarski(k2_relat_1(C_216),B_218)
      | ~ r1_tarski(k1_relat_1(C_216),A_217)
      | ~ v1_relat_1(C_216) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_628,plain,(
    ! [A_120,B_121,C_122,D_123] :
      ( v1_funct_1(k2_partfun1(A_120,B_121,C_122,D_123))
      | ~ m1_subset_1(C_122,k1_zfmisc_1(k2_zfmisc_1(A_120,B_121)))
      | ~ v1_funct_1(C_122) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_633,plain,(
    ! [D_123] :
      ( v1_funct_1(k2_partfun1('#skF_1','#skF_2','#skF_4',D_123))
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_60,c_628])).

tff(c_641,plain,(
    ! [D_123] : v1_funct_1(k2_partfun1('#skF_1','#skF_2','#skF_4',D_123)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_633])).

tff(c_54,plain,
    ( ~ m1_subset_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2')))
    | ~ v1_funct_2(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),'#skF_3','#skF_2')
    | ~ v1_funct_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_151,plain,(
    ~ v1_funct_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_54])).

tff(c_644,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_641,c_151])).

tff(c_645,plain,
    ( ~ v1_funct_2(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),'#skF_3','#skF_2')
    | ~ m1_subset_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_715,plain,(
    ~ m1_subset_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_645])).

tff(c_1185,plain,(
    ~ m1_subset_1(k7_relat_1('#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1182,c_715])).

tff(c_1294,plain,
    ( ~ r1_tarski(k2_relat_1(k7_relat_1('#skF_4','#skF_3')),'#skF_2')
    | ~ r1_tarski(k1_relat_1(k7_relat_1('#skF_4','#skF_3')),'#skF_3')
    | ~ v1_relat_1(k7_relat_1('#skF_4','#skF_3')) ),
    inference(resolution,[status(thm)],[c_1265,c_1185])).

tff(c_1407,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_4','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_1294])).

tff(c_1410,plain,(
    ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_712,c_1407])).

tff(c_1414,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_689,c_1410])).

tff(c_1416,plain,(
    v1_relat_1(k7_relat_1('#skF_4','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_1294])).

tff(c_18,plain,(
    ! [B_10,A_9] :
      ( r1_tarski(k2_relat_1(B_10),A_9)
      | ~ v5_relat_1(B_10,A_9)
      | ~ v1_relat_1(B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_1415,plain,
    ( ~ r1_tarski(k1_relat_1(k7_relat_1('#skF_4','#skF_3')),'#skF_3')
    | ~ r1_tarski(k2_relat_1(k7_relat_1('#skF_4','#skF_3')),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_1294])).

tff(c_1561,plain,(
    ~ r1_tarski(k2_relat_1(k7_relat_1('#skF_4','#skF_3')),'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_1415])).

tff(c_1564,plain,
    ( ~ v5_relat_1(k7_relat_1('#skF_4','#skF_3'),'#skF_2')
    | ~ v1_relat_1(k7_relat_1('#skF_4','#skF_3')) ),
    inference(resolution,[status(thm)],[c_18,c_1561])).

tff(c_1567,plain,(
    ~ v5_relat_1(k7_relat_1('#skF_4','#skF_3'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1416,c_1564])).

tff(c_1928,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1916,c_1567])).

tff(c_1929,plain,(
    ~ r1_tarski(k1_relat_1(k7_relat_1('#skF_4','#skF_3')),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_1415])).

tff(c_2003,plain,(
    ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_22,c_1929])).

tff(c_2009,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_689,c_2003])).

tff(c_2011,plain,(
    m1_subset_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_645])).

tff(c_2425,plain,(
    k1_relset_1('#skF_3','#skF_2',k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3')) = k1_relat_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3')) ),
    inference(resolution,[status(thm)],[c_2011,c_2408])).

tff(c_2823,plain,(
    k1_relset_1('#skF_3','#skF_2',k7_relat_1('#skF_4','#skF_3')) = k1_relat_1(k7_relat_1('#skF_4','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2820,c_2820,c_2425])).

tff(c_2010,plain,(
    ~ v1_funct_2(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),'#skF_3','#skF_2') ),
    inference(splitRight,[status(thm)],[c_645])).

tff(c_2829,plain,(
    ~ v1_funct_2(k7_relat_1('#skF_4','#skF_3'),'#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2820,c_2010])).

tff(c_2828,plain,(
    m1_subset_1(k7_relat_1('#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2820,c_2011])).

tff(c_42,plain,(
    ! [B_29,C_30,A_28] :
      ( k1_xboole_0 = B_29
      | v1_funct_2(C_30,A_28,B_29)
      | k1_relset_1(A_28,B_29,C_30) != A_28
      | ~ m1_subset_1(C_30,k1_zfmisc_1(k2_zfmisc_1(A_28,B_29))) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_2890,plain,
    ( k1_xboole_0 = '#skF_2'
    | v1_funct_2(k7_relat_1('#skF_4','#skF_3'),'#skF_3','#skF_2')
    | k1_relset_1('#skF_3','#skF_2',k7_relat_1('#skF_4','#skF_3')) != '#skF_3' ),
    inference(resolution,[status(thm)],[c_2828,c_42])).

tff(c_2912,plain,(
    k1_relset_1('#skF_3','#skF_2',k7_relat_1('#skF_4','#skF_3')) != '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_2829,c_69,c_2890])).

tff(c_3080,plain,(
    k1_relat_1(k7_relat_1('#skF_4','#skF_3')) != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2823,c_2912])).

tff(c_3087,plain,(
    ~ r1_tarski('#skF_3','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_3014,c_3080])).

tff(c_3091,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_3087])).

tff(c_3092,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_6,plain,(
    ! [A_2] : k2_zfmisc_1(A_2,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_3105,plain,(
    ! [A_2] : k2_zfmisc_1(A_2,'#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3092,c_3092,c_6])).

tff(c_3093,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_3098,plain,(
    '#skF_2' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3092,c_3093])).

tff(c_3134,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3105,c_3098,c_60])).

tff(c_3160,plain,(
    ! [A_402,B_403] :
      ( r1_tarski(A_402,B_403)
      | ~ m1_subset_1(A_402,k1_zfmisc_1(B_403)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_3168,plain,(
    r1_tarski('#skF_4','#skF_1') ),
    inference(resolution,[status(thm)],[c_3134,c_3160])).

tff(c_2,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ r1_tarski(A_1,k1_xboole_0) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_3135,plain,(
    ! [A_1] :
      ( A_1 = '#skF_1'
      | ~ r1_tarski(A_1,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3092,c_3092,c_2])).

tff(c_3172,plain,(
    '#skF_1' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_3168,c_3135])).

tff(c_3099,plain,(
    v1_funct_2('#skF_4','#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3098,c_62])).

tff(c_3178,plain,(
    v1_funct_2('#skF_4','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3172,c_3172,c_3099])).

tff(c_3177,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3172,c_3134])).

tff(c_8,plain,(
    ! [B_3] : k2_zfmisc_1(k1_xboole_0,B_3) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_3115,plain,(
    ! [B_3] : k2_zfmisc_1('#skF_1',B_3) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3092,c_3092,c_8])).

tff(c_3180,plain,(
    ! [B_3] : k2_zfmisc_1('#skF_4',B_3) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3172,c_3172,c_3115])).

tff(c_5275,plain,(
    ! [A_694,B_695,C_696,D_697] :
      ( m1_subset_1(k2_partfun1(A_694,B_695,C_696,D_697),k1_zfmisc_1(k2_zfmisc_1(A_694,B_695)))
      | ~ m1_subset_1(C_696,k1_zfmisc_1(k2_zfmisc_1(A_694,B_695)))
      | ~ v1_funct_1(C_696) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_5306,plain,(
    ! [B_3,C_696,D_697] :
      ( m1_subset_1(k2_partfun1('#skF_4',B_3,C_696,D_697),k1_zfmisc_1('#skF_4'))
      | ~ m1_subset_1(C_696,k1_zfmisc_1(k2_zfmisc_1('#skF_4',B_3)))
      | ~ v1_funct_1(C_696) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3180,c_5275])).

tff(c_5726,plain,(
    ! [B_751,C_752,D_753] :
      ( m1_subset_1(k2_partfun1('#skF_4',B_751,C_752,D_753),k1_zfmisc_1('#skF_4'))
      | ~ m1_subset_1(C_752,k1_zfmisc_1('#skF_4'))
      | ~ v1_funct_1(C_752) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3180,c_5306])).

tff(c_3182,plain,(
    '#skF_2' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3172,c_3098])).

tff(c_3919,plain,(
    ! [A_502,B_503,C_504,D_505] :
      ( v1_funct_1(k2_partfun1(A_502,B_503,C_504,D_505))
      | ~ m1_subset_1(C_504,k1_zfmisc_1(k2_zfmisc_1(A_502,B_503)))
      | ~ v1_funct_1(C_504) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_4059,plain,(
    ! [B_526,C_527,D_528] :
      ( v1_funct_1(k2_partfun1('#skF_4',B_526,C_527,D_528))
      | ~ m1_subset_1(C_527,k1_zfmisc_1('#skF_4'))
      | ~ v1_funct_1(C_527) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3180,c_3919])).

tff(c_4061,plain,(
    ! [B_526,D_528] :
      ( v1_funct_1(k2_partfun1('#skF_4',B_526,'#skF_4',D_528))
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_3177,c_4059])).

tff(c_4067,plain,(
    ! [B_526,D_528] : v1_funct_1(k2_partfun1('#skF_4',B_526,'#skF_4',D_528)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_4061])).

tff(c_3136,plain,(
    ! [A_397] :
      ( A_397 = '#skF_1'
      | ~ r1_tarski(A_397,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3092,c_3092,c_2])).

tff(c_3140,plain,(
    '#skF_3' = '#skF_1' ),
    inference(resolution,[status(thm)],[c_58,c_3136])).

tff(c_3175,plain,(
    '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3172,c_3140])).

tff(c_3192,plain,
    ( ~ m1_subset_1(k2_partfun1('#skF_4','#skF_2','#skF_4','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_2')))
    | ~ v1_funct_2(k2_partfun1('#skF_4','#skF_2','#skF_4','#skF_4'),'#skF_4','#skF_2')
    | ~ v1_funct_1(k2_partfun1('#skF_4','#skF_2','#skF_4','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3175,c_3172,c_3175,c_3175,c_3172,c_3175,c_3175,c_3172,c_54])).

tff(c_3193,plain,(
    ~ v1_funct_1(k2_partfun1('#skF_4','#skF_2','#skF_4','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_3192])).

tff(c_3227,plain,(
    ~ v1_funct_1(k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3182,c_3193])).

tff(c_4071,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4067,c_3227])).

tff(c_4072,plain,
    ( ~ v1_funct_2(k2_partfun1('#skF_4','#skF_2','#skF_4','#skF_4'),'#skF_4','#skF_2')
    | ~ m1_subset_1(k2_partfun1('#skF_4','#skF_2','#skF_4','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_3192])).

tff(c_4185,plain,
    ( ~ v1_funct_2(k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_4'),'#skF_4','#skF_4')
    | ~ m1_subset_1(k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_4'),k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3180,c_3182,c_3182,c_3182,c_3182,c_4072])).

tff(c_4186,plain,(
    ~ m1_subset_1(k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_4'),k1_zfmisc_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_4185])).

tff(c_5747,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_4'))
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_5726,c_4186])).

tff(c_5766,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_3177,c_5747])).

tff(c_5768,plain,(
    m1_subset_1(k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_4'),k1_zfmisc_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_4185])).

tff(c_10,plain,(
    ! [A_4,B_5] :
      ( r1_tarski(A_4,B_5)
      | ~ m1_subset_1(A_4,k1_zfmisc_1(B_5)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_5887,plain,(
    r1_tarski(k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_4'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_5768,c_10])).

tff(c_3176,plain,(
    ! [A_1] :
      ( A_1 = '#skF_4'
      | ~ r1_tarski(A_1,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3172,c_3172,c_3135])).

tff(c_5909,plain,(
    k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_4') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_5887,c_3176])).

tff(c_5767,plain,(
    ~ v1_funct_2(k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_4'),'#skF_4','#skF_4') ),
    inference(splitRight,[status(thm)],[c_4185])).

tff(c_5923,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3178,c_5909,c_5767])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:13:45 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.92/2.16  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.92/2.18  
% 5.92/2.18  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.92/2.18  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_partfun1 > k1_relset_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 5.92/2.18  
% 5.92/2.18  %Foreground sorts:
% 5.92/2.18  
% 5.92/2.18  
% 5.92/2.18  %Background operators:
% 5.92/2.18  
% 5.92/2.18  
% 5.92/2.18  %Foreground operators:
% 5.92/2.18  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 5.92/2.18  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.92/2.18  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 5.92/2.18  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.92/2.18  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.92/2.18  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 5.92/2.18  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 5.92/2.18  tff('#skF_2', type, '#skF_2': $i).
% 5.92/2.18  tff('#skF_3', type, '#skF_3': $i).
% 5.92/2.18  tff('#skF_1', type, '#skF_1': $i).
% 5.92/2.18  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 5.92/2.18  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 5.92/2.18  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.92/2.18  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.92/2.18  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.92/2.18  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 5.92/2.18  tff('#skF_4', type, '#skF_4': $i).
% 5.92/2.18  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.92/2.18  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 5.92/2.18  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 5.92/2.18  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 5.92/2.18  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.92/2.18  
% 6.41/2.20  tff(f_138, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r1_tarski(C, A) => (((B = k1_xboole_0) & ~(A = k1_xboole_0)) | ((v1_funct_1(k2_partfun1(A, B, D, C)) & v1_funct_2(k2_partfun1(A, B, D, C), C, B)) & m1_subset_1(k2_partfun1(A, B, D, C), k1_zfmisc_1(k2_zfmisc_1(C, B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_funct_2)).
% 6.41/2.20  tff(f_54, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 6.41/2.20  tff(f_46, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 6.41/2.20  tff(f_78, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 6.41/2.20  tff(f_104, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 6.41/2.20  tff(f_68, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(A, k1_relat_1(B)) => (k1_relat_1(k7_relat_1(B, A)) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_relat_1)).
% 6.41/2.20  tff(f_118, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (k2_partfun1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_partfun1)).
% 6.41/2.20  tff(f_58, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k7_relat_1(B, A)), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t87_relat_1)).
% 6.41/2.20  tff(f_112, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (v1_funct_1(k2_partfun1(A, B, C, D)) & m1_subset_1(k2_partfun1(A, B, C, D), k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_partfun1)).
% 6.41/2.20  tff(f_74, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 6.41/2.20  tff(f_62, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k7_relat_1(B, A), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t88_relat_1)).
% 6.41/2.20  tff(f_39, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 6.41/2.20  tff(f_86, axiom, (![A, B, C]: (v1_relat_1(C) => ((r1_tarski(k1_relat_1(C), A) & r1_tarski(k2_relat_1(C), B)) => m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_relset_1)).
% 6.41/2.20  tff(f_52, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 6.41/2.20  tff(f_35, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 6.41/2.20  tff(f_29, axiom, (![A]: (r1_tarski(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_1)).
% 6.41/2.20  tff(c_58, plain, (r1_tarski('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_138])).
% 6.41/2.20  tff(c_20, plain, (![A_11, B_12]: (v1_relat_1(k2_zfmisc_1(A_11, B_12)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 6.41/2.20  tff(c_60, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_138])).
% 6.41/2.20  tff(c_679, plain, (![B_126, A_127]: (v1_relat_1(B_126) | ~m1_subset_1(B_126, k1_zfmisc_1(A_127)) | ~v1_relat_1(A_127))), inference(cnfTransformation, [status(thm)], [f_46])).
% 6.41/2.20  tff(c_685, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_60, c_679])).
% 6.41/2.20  tff(c_689, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_20, c_685])).
% 6.41/2.20  tff(c_56, plain, (k1_xboole_0='#skF_1' | k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_138])).
% 6.41/2.20  tff(c_69, plain, (k1_xboole_0!='#skF_2'), inference(splitLeft, [status(thm)], [c_56])).
% 6.41/2.20  tff(c_62, plain, (v1_funct_2('#skF_4', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_138])).
% 6.41/2.20  tff(c_2408, plain, (![A_324, B_325, C_326]: (k1_relset_1(A_324, B_325, C_326)=k1_relat_1(C_326) | ~m1_subset_1(C_326, k1_zfmisc_1(k2_zfmisc_1(A_324, B_325))))), inference(cnfTransformation, [status(thm)], [f_78])).
% 6.41/2.20  tff(c_2427, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_60, c_2408])).
% 6.41/2.20  tff(c_2977, plain, (![B_389, A_390, C_391]: (k1_xboole_0=B_389 | k1_relset_1(A_390, B_389, C_391)=A_390 | ~v1_funct_2(C_391, A_390, B_389) | ~m1_subset_1(C_391, k1_zfmisc_1(k2_zfmisc_1(A_390, B_389))))), inference(cnfTransformation, [status(thm)], [f_104])).
% 6.41/2.20  tff(c_2990, plain, (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', '#skF_4')='#skF_1' | ~v1_funct_2('#skF_4', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_60, c_2977])).
% 6.41/2.20  tff(c_3003, plain, (k1_xboole_0='#skF_2' | k1_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_62, c_2427, c_2990])).
% 6.41/2.20  tff(c_3004, plain, (k1_relat_1('#skF_4')='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_69, c_3003])).
% 6.41/2.20  tff(c_26, plain, (![B_18, A_17]: (k1_relat_1(k7_relat_1(B_18, A_17))=A_17 | ~r1_tarski(A_17, k1_relat_1(B_18)) | ~v1_relat_1(B_18))), inference(cnfTransformation, [status(thm)], [f_68])).
% 6.41/2.20  tff(c_3010, plain, (![A_17]: (k1_relat_1(k7_relat_1('#skF_4', A_17))=A_17 | ~r1_tarski(A_17, '#skF_1') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_3004, c_26])).
% 6.41/2.20  tff(c_3014, plain, (![A_17]: (k1_relat_1(k7_relat_1('#skF_4', A_17))=A_17 | ~r1_tarski(A_17, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_689, c_3010])).
% 6.41/2.20  tff(c_64, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_138])).
% 6.41/2.20  tff(c_2799, plain, (![A_375, B_376, C_377, D_378]: (k2_partfun1(A_375, B_376, C_377, D_378)=k7_relat_1(C_377, D_378) | ~m1_subset_1(C_377, k1_zfmisc_1(k2_zfmisc_1(A_375, B_376))) | ~v1_funct_1(C_377))), inference(cnfTransformation, [status(thm)], [f_118])).
% 6.41/2.20  tff(c_2808, plain, (![D_378]: (k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_378)=k7_relat_1('#skF_4', D_378) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_60, c_2799])).
% 6.41/2.20  tff(c_2820, plain, (![D_378]: (k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_378)=k7_relat_1('#skF_4', D_378))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_2808])).
% 6.41/2.20  tff(c_22, plain, (![B_14, A_13]: (r1_tarski(k1_relat_1(k7_relat_1(B_14, A_13)), A_13) | ~v1_relat_1(B_14))), inference(cnfTransformation, [status(thm)], [f_58])).
% 6.41/2.20  tff(c_1169, plain, (![A_199, B_200, C_201, D_202]: (k2_partfun1(A_199, B_200, C_201, D_202)=k7_relat_1(C_201, D_202) | ~m1_subset_1(C_201, k1_zfmisc_1(k2_zfmisc_1(A_199, B_200))) | ~v1_funct_1(C_201))), inference(cnfTransformation, [status(thm)], [f_118])).
% 6.41/2.20  tff(c_1174, plain, (![D_202]: (k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_202)=k7_relat_1('#skF_4', D_202) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_60, c_1169])).
% 6.41/2.20  tff(c_1182, plain, (![D_202]: (k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_202)=k7_relat_1('#skF_4', D_202))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_1174])).
% 6.41/2.20  tff(c_1827, plain, (![A_261, B_262, C_263, D_264]: (m1_subset_1(k2_partfun1(A_261, B_262, C_263, D_264), k1_zfmisc_1(k2_zfmisc_1(A_261, B_262))) | ~m1_subset_1(C_263, k1_zfmisc_1(k2_zfmisc_1(A_261, B_262))) | ~v1_funct_1(C_263))), inference(cnfTransformation, [status(thm)], [f_112])).
% 6.41/2.20  tff(c_1855, plain, (![D_202]: (m1_subset_1(k7_relat_1('#skF_4', D_202), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_1182, c_1827])).
% 6.41/2.20  tff(c_1877, plain, (![D_265]: (m1_subset_1(k7_relat_1('#skF_4', D_265), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_60, c_1855])).
% 6.41/2.20  tff(c_28, plain, (![C_21, B_20, A_19]: (v5_relat_1(C_21, B_20) | ~m1_subset_1(C_21, k1_zfmisc_1(k2_zfmisc_1(A_19, B_20))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 6.41/2.20  tff(c_1916, plain, (![D_265]: (v5_relat_1(k7_relat_1('#skF_4', D_265), '#skF_2'))), inference(resolution, [status(thm)], [c_1877, c_28])).
% 6.41/2.20  tff(c_24, plain, (![B_16, A_15]: (r1_tarski(k7_relat_1(B_16, A_15), B_16) | ~v1_relat_1(B_16))), inference(cnfTransformation, [status(thm)], [f_62])).
% 6.41/2.20  tff(c_12, plain, (![A_4, B_5]: (m1_subset_1(A_4, k1_zfmisc_1(B_5)) | ~r1_tarski(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_39])).
% 6.41/2.20  tff(c_690, plain, (![A_128, B_129]: (v1_relat_1(A_128) | ~v1_relat_1(B_129) | ~r1_tarski(A_128, B_129))), inference(resolution, [status(thm)], [c_12, c_679])).
% 6.41/2.20  tff(c_712, plain, (![B_16, A_15]: (v1_relat_1(k7_relat_1(B_16, A_15)) | ~v1_relat_1(B_16))), inference(resolution, [status(thm)], [c_24, c_690])).
% 6.41/2.20  tff(c_1265, plain, (![C_216, A_217, B_218]: (m1_subset_1(C_216, k1_zfmisc_1(k2_zfmisc_1(A_217, B_218))) | ~r1_tarski(k2_relat_1(C_216), B_218) | ~r1_tarski(k1_relat_1(C_216), A_217) | ~v1_relat_1(C_216))), inference(cnfTransformation, [status(thm)], [f_86])).
% 6.41/2.20  tff(c_628, plain, (![A_120, B_121, C_122, D_123]: (v1_funct_1(k2_partfun1(A_120, B_121, C_122, D_123)) | ~m1_subset_1(C_122, k1_zfmisc_1(k2_zfmisc_1(A_120, B_121))) | ~v1_funct_1(C_122))), inference(cnfTransformation, [status(thm)], [f_112])).
% 6.41/2.20  tff(c_633, plain, (![D_123]: (v1_funct_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_123)) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_60, c_628])).
% 6.41/2.20  tff(c_641, plain, (![D_123]: (v1_funct_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_123)))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_633])).
% 6.41/2.20  tff(c_54, plain, (~m1_subset_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2'))) | ~v1_funct_2(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), '#skF_3', '#skF_2') | ~v1_funct_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_138])).
% 6.41/2.20  tff(c_151, plain, (~v1_funct_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'))), inference(splitLeft, [status(thm)], [c_54])).
% 6.41/2.20  tff(c_644, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_641, c_151])).
% 6.41/2.20  tff(c_645, plain, (~v1_funct_2(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), '#skF_3', '#skF_2') | ~m1_subset_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(splitRight, [status(thm)], [c_54])).
% 6.41/2.20  tff(c_715, plain, (~m1_subset_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(splitLeft, [status(thm)], [c_645])).
% 6.41/2.20  tff(c_1185, plain, (~m1_subset_1(k7_relat_1('#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_1182, c_715])).
% 6.41/2.20  tff(c_1294, plain, (~r1_tarski(k2_relat_1(k7_relat_1('#skF_4', '#skF_3')), '#skF_2') | ~r1_tarski(k1_relat_1(k7_relat_1('#skF_4', '#skF_3')), '#skF_3') | ~v1_relat_1(k7_relat_1('#skF_4', '#skF_3'))), inference(resolution, [status(thm)], [c_1265, c_1185])).
% 6.41/2.20  tff(c_1407, plain, (~v1_relat_1(k7_relat_1('#skF_4', '#skF_3'))), inference(splitLeft, [status(thm)], [c_1294])).
% 6.41/2.20  tff(c_1410, plain, (~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_712, c_1407])).
% 6.41/2.20  tff(c_1414, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_689, c_1410])).
% 6.41/2.20  tff(c_1416, plain, (v1_relat_1(k7_relat_1('#skF_4', '#skF_3'))), inference(splitRight, [status(thm)], [c_1294])).
% 6.41/2.20  tff(c_18, plain, (![B_10, A_9]: (r1_tarski(k2_relat_1(B_10), A_9) | ~v5_relat_1(B_10, A_9) | ~v1_relat_1(B_10))), inference(cnfTransformation, [status(thm)], [f_52])).
% 6.41/2.20  tff(c_1415, plain, (~r1_tarski(k1_relat_1(k7_relat_1('#skF_4', '#skF_3')), '#skF_3') | ~r1_tarski(k2_relat_1(k7_relat_1('#skF_4', '#skF_3')), '#skF_2')), inference(splitRight, [status(thm)], [c_1294])).
% 6.41/2.20  tff(c_1561, plain, (~r1_tarski(k2_relat_1(k7_relat_1('#skF_4', '#skF_3')), '#skF_2')), inference(splitLeft, [status(thm)], [c_1415])).
% 6.41/2.20  tff(c_1564, plain, (~v5_relat_1(k7_relat_1('#skF_4', '#skF_3'), '#skF_2') | ~v1_relat_1(k7_relat_1('#skF_4', '#skF_3'))), inference(resolution, [status(thm)], [c_18, c_1561])).
% 6.41/2.20  tff(c_1567, plain, (~v5_relat_1(k7_relat_1('#skF_4', '#skF_3'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1416, c_1564])).
% 6.41/2.20  tff(c_1928, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1916, c_1567])).
% 6.41/2.20  tff(c_1929, plain, (~r1_tarski(k1_relat_1(k7_relat_1('#skF_4', '#skF_3')), '#skF_3')), inference(splitRight, [status(thm)], [c_1415])).
% 6.41/2.20  tff(c_2003, plain, (~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_22, c_1929])).
% 6.41/2.20  tff(c_2009, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_689, c_2003])).
% 6.41/2.20  tff(c_2011, plain, (m1_subset_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(splitRight, [status(thm)], [c_645])).
% 6.41/2.20  tff(c_2425, plain, (k1_relset_1('#skF_3', '#skF_2', k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'))=k1_relat_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'))), inference(resolution, [status(thm)], [c_2011, c_2408])).
% 6.41/2.20  tff(c_2823, plain, (k1_relset_1('#skF_3', '#skF_2', k7_relat_1('#skF_4', '#skF_3'))=k1_relat_1(k7_relat_1('#skF_4', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_2820, c_2820, c_2425])).
% 6.41/2.20  tff(c_2010, plain, (~v1_funct_2(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), '#skF_3', '#skF_2')), inference(splitRight, [status(thm)], [c_645])).
% 6.41/2.20  tff(c_2829, plain, (~v1_funct_2(k7_relat_1('#skF_4', '#skF_3'), '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2820, c_2010])).
% 6.41/2.20  tff(c_2828, plain, (m1_subset_1(k7_relat_1('#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_2820, c_2011])).
% 6.41/2.20  tff(c_42, plain, (![B_29, C_30, A_28]: (k1_xboole_0=B_29 | v1_funct_2(C_30, A_28, B_29) | k1_relset_1(A_28, B_29, C_30)!=A_28 | ~m1_subset_1(C_30, k1_zfmisc_1(k2_zfmisc_1(A_28, B_29))))), inference(cnfTransformation, [status(thm)], [f_104])).
% 6.41/2.20  tff(c_2890, plain, (k1_xboole_0='#skF_2' | v1_funct_2(k7_relat_1('#skF_4', '#skF_3'), '#skF_3', '#skF_2') | k1_relset_1('#skF_3', '#skF_2', k7_relat_1('#skF_4', '#skF_3'))!='#skF_3'), inference(resolution, [status(thm)], [c_2828, c_42])).
% 6.41/2.20  tff(c_2912, plain, (k1_relset_1('#skF_3', '#skF_2', k7_relat_1('#skF_4', '#skF_3'))!='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_2829, c_69, c_2890])).
% 6.41/2.20  tff(c_3080, plain, (k1_relat_1(k7_relat_1('#skF_4', '#skF_3'))!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_2823, c_2912])).
% 6.41/2.20  tff(c_3087, plain, (~r1_tarski('#skF_3', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_3014, c_3080])).
% 6.41/2.20  tff(c_3091, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_58, c_3087])).
% 6.41/2.20  tff(c_3092, plain, (k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_56])).
% 6.41/2.20  tff(c_6, plain, (![A_2]: (k2_zfmisc_1(A_2, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_35])).
% 6.41/2.20  tff(c_3105, plain, (![A_2]: (k2_zfmisc_1(A_2, '#skF_1')='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_3092, c_3092, c_6])).
% 6.41/2.20  tff(c_3093, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_56])).
% 6.41/2.20  tff(c_3098, plain, ('#skF_2'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_3092, c_3093])).
% 6.41/2.20  tff(c_3134, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_3105, c_3098, c_60])).
% 6.41/2.20  tff(c_3160, plain, (![A_402, B_403]: (r1_tarski(A_402, B_403) | ~m1_subset_1(A_402, k1_zfmisc_1(B_403)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 6.41/2.20  tff(c_3168, plain, (r1_tarski('#skF_4', '#skF_1')), inference(resolution, [status(thm)], [c_3134, c_3160])).
% 6.41/2.20  tff(c_2, plain, (![A_1]: (k1_xboole_0=A_1 | ~r1_tarski(A_1, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_29])).
% 6.41/2.20  tff(c_3135, plain, (![A_1]: (A_1='#skF_1' | ~r1_tarski(A_1, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_3092, c_3092, c_2])).
% 6.41/2.20  tff(c_3172, plain, ('#skF_1'='#skF_4'), inference(resolution, [status(thm)], [c_3168, c_3135])).
% 6.41/2.20  tff(c_3099, plain, (v1_funct_2('#skF_4', '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_3098, c_62])).
% 6.41/2.20  tff(c_3178, plain, (v1_funct_2('#skF_4', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_3172, c_3172, c_3099])).
% 6.41/2.20  tff(c_3177, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_3172, c_3134])).
% 6.41/2.20  tff(c_8, plain, (![B_3]: (k2_zfmisc_1(k1_xboole_0, B_3)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_35])).
% 6.41/2.20  tff(c_3115, plain, (![B_3]: (k2_zfmisc_1('#skF_1', B_3)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_3092, c_3092, c_8])).
% 6.41/2.20  tff(c_3180, plain, (![B_3]: (k2_zfmisc_1('#skF_4', B_3)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_3172, c_3172, c_3115])).
% 6.41/2.20  tff(c_5275, plain, (![A_694, B_695, C_696, D_697]: (m1_subset_1(k2_partfun1(A_694, B_695, C_696, D_697), k1_zfmisc_1(k2_zfmisc_1(A_694, B_695))) | ~m1_subset_1(C_696, k1_zfmisc_1(k2_zfmisc_1(A_694, B_695))) | ~v1_funct_1(C_696))), inference(cnfTransformation, [status(thm)], [f_112])).
% 6.41/2.20  tff(c_5306, plain, (![B_3, C_696, D_697]: (m1_subset_1(k2_partfun1('#skF_4', B_3, C_696, D_697), k1_zfmisc_1('#skF_4')) | ~m1_subset_1(C_696, k1_zfmisc_1(k2_zfmisc_1('#skF_4', B_3))) | ~v1_funct_1(C_696))), inference(superposition, [status(thm), theory('equality')], [c_3180, c_5275])).
% 6.41/2.20  tff(c_5726, plain, (![B_751, C_752, D_753]: (m1_subset_1(k2_partfun1('#skF_4', B_751, C_752, D_753), k1_zfmisc_1('#skF_4')) | ~m1_subset_1(C_752, k1_zfmisc_1('#skF_4')) | ~v1_funct_1(C_752))), inference(demodulation, [status(thm), theory('equality')], [c_3180, c_5306])).
% 6.41/2.20  tff(c_3182, plain, ('#skF_2'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_3172, c_3098])).
% 6.41/2.20  tff(c_3919, plain, (![A_502, B_503, C_504, D_505]: (v1_funct_1(k2_partfun1(A_502, B_503, C_504, D_505)) | ~m1_subset_1(C_504, k1_zfmisc_1(k2_zfmisc_1(A_502, B_503))) | ~v1_funct_1(C_504))), inference(cnfTransformation, [status(thm)], [f_112])).
% 6.41/2.20  tff(c_4059, plain, (![B_526, C_527, D_528]: (v1_funct_1(k2_partfun1('#skF_4', B_526, C_527, D_528)) | ~m1_subset_1(C_527, k1_zfmisc_1('#skF_4')) | ~v1_funct_1(C_527))), inference(superposition, [status(thm), theory('equality')], [c_3180, c_3919])).
% 6.41/2.20  tff(c_4061, plain, (![B_526, D_528]: (v1_funct_1(k2_partfun1('#skF_4', B_526, '#skF_4', D_528)) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_3177, c_4059])).
% 6.41/2.20  tff(c_4067, plain, (![B_526, D_528]: (v1_funct_1(k2_partfun1('#skF_4', B_526, '#skF_4', D_528)))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_4061])).
% 6.41/2.20  tff(c_3136, plain, (![A_397]: (A_397='#skF_1' | ~r1_tarski(A_397, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_3092, c_3092, c_2])).
% 6.41/2.20  tff(c_3140, plain, ('#skF_3'='#skF_1'), inference(resolution, [status(thm)], [c_58, c_3136])).
% 6.41/2.20  tff(c_3175, plain, ('#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_3172, c_3140])).
% 6.41/2.20  tff(c_3192, plain, (~m1_subset_1(k2_partfun1('#skF_4', '#skF_2', '#skF_4', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_2'))) | ~v1_funct_2(k2_partfun1('#skF_4', '#skF_2', '#skF_4', '#skF_4'), '#skF_4', '#skF_2') | ~v1_funct_1(k2_partfun1('#skF_4', '#skF_2', '#skF_4', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_3175, c_3172, c_3175, c_3175, c_3172, c_3175, c_3175, c_3172, c_54])).
% 6.41/2.20  tff(c_3193, plain, (~v1_funct_1(k2_partfun1('#skF_4', '#skF_2', '#skF_4', '#skF_4'))), inference(splitLeft, [status(thm)], [c_3192])).
% 6.41/2.20  tff(c_3227, plain, (~v1_funct_1(k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_3182, c_3193])).
% 6.41/2.20  tff(c_4071, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4067, c_3227])).
% 6.41/2.20  tff(c_4072, plain, (~v1_funct_2(k2_partfun1('#skF_4', '#skF_2', '#skF_4', '#skF_4'), '#skF_4', '#skF_2') | ~m1_subset_1(k2_partfun1('#skF_4', '#skF_2', '#skF_4', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_2')))), inference(splitRight, [status(thm)], [c_3192])).
% 6.41/2.20  tff(c_4185, plain, (~v1_funct_2(k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_4'), '#skF_4', '#skF_4') | ~m1_subset_1(k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_4'), k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_3180, c_3182, c_3182, c_3182, c_3182, c_4072])).
% 6.41/2.20  tff(c_4186, plain, (~m1_subset_1(k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_4'), k1_zfmisc_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_4185])).
% 6.41/2.20  tff(c_5747, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_4')) | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_5726, c_4186])).
% 6.41/2.20  tff(c_5766, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_64, c_3177, c_5747])).
% 6.41/2.20  tff(c_5768, plain, (m1_subset_1(k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_4'), k1_zfmisc_1('#skF_4'))), inference(splitRight, [status(thm)], [c_4185])).
% 6.41/2.20  tff(c_10, plain, (![A_4, B_5]: (r1_tarski(A_4, B_5) | ~m1_subset_1(A_4, k1_zfmisc_1(B_5)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 6.41/2.20  tff(c_5887, plain, (r1_tarski(k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_4'), '#skF_4')), inference(resolution, [status(thm)], [c_5768, c_10])).
% 6.41/2.20  tff(c_3176, plain, (![A_1]: (A_1='#skF_4' | ~r1_tarski(A_1, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_3172, c_3172, c_3135])).
% 6.41/2.20  tff(c_5909, plain, (k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_4')='#skF_4'), inference(resolution, [status(thm)], [c_5887, c_3176])).
% 6.41/2.20  tff(c_5767, plain, (~v1_funct_2(k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_4'), '#skF_4', '#skF_4')), inference(splitRight, [status(thm)], [c_4185])).
% 6.41/2.20  tff(c_5923, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3178, c_5909, c_5767])).
% 6.41/2.20  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.41/2.20  
% 6.41/2.20  Inference rules
% 6.41/2.20  ----------------------
% 6.41/2.20  #Ref     : 0
% 6.41/2.20  #Sup     : 1232
% 6.41/2.20  #Fact    : 0
% 6.41/2.20  #Define  : 0
% 6.41/2.20  #Split   : 18
% 6.41/2.20  #Chain   : 0
% 6.41/2.20  #Close   : 0
% 6.41/2.20  
% 6.41/2.20  Ordering : KBO
% 6.41/2.20  
% 6.41/2.20  Simplification rules
% 6.41/2.20  ----------------------
% 6.41/2.20  #Subsume      : 183
% 6.41/2.20  #Demod        : 1094
% 6.41/2.20  #Tautology    : 567
% 6.41/2.20  #SimpNegUnit  : 39
% 6.41/2.20  #BackRed      : 51
% 6.41/2.20  
% 6.41/2.20  #Partial instantiations: 0
% 6.41/2.20  #Strategies tried      : 1
% 6.41/2.20  
% 6.41/2.20  Timing (in seconds)
% 6.41/2.20  ----------------------
% 6.41/2.21  Preprocessing        : 0.34
% 6.41/2.21  Parsing              : 0.18
% 6.41/2.21  CNF conversion       : 0.02
% 6.41/2.21  Main loop            : 1.09
% 6.41/2.21  Inferencing          : 0.39
% 6.41/2.21  Reduction            : 0.38
% 6.41/2.21  Demodulation         : 0.27
% 6.41/2.21  BG Simplification    : 0.04
% 6.41/2.21  Subsumption          : 0.19
% 6.41/2.21  Abstraction          : 0.04
% 6.41/2.21  MUC search           : 0.00
% 6.41/2.21  Cooper               : 0.00
% 6.41/2.21  Total                : 1.48
% 6.41/2.21  Index Insertion      : 0.00
% 6.41/2.21  Index Deletion       : 0.00
% 6.41/2.21  Index Matching       : 0.00
% 6.41/2.21  BG Taut test         : 0.00
%------------------------------------------------------------------------------
