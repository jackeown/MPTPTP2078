%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:16:39 EST 2020

% Result     : Theorem 7.73s
% Output     : CNFRefutation 7.73s
% Verified   : 
% Statistics : Number of formulae       :  130 ( 339 expanded)
%              Number of leaves         :   45 ( 124 expanded)
%              Depth                    :   12
%              Number of atoms          :  215 ( 800 expanded)
%              Number of equality atoms :   21 ( 107 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_zfmisc_1 > k1_funct_2 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_6 > #skF_1 > #skF_4 > #skF_10 > #skF_5 > #skF_7 > #skF_9 > #skF_8 > #skF_3 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff(v1_partfun1,type,(
    v1_partfun1: ( $i * $i ) > $o )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_2,type,(
    k1_funct_2: ( $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_182,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r2_hidden(C,k1_funct_2(A,B))
       => ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t121_funct_2)).

tff(f_163,axiom,(
    ! [A,B,C] :
      ( C = k1_funct_2(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ? [E] :
              ( v1_relat_1(E)
              & v1_funct_1(E)
              & D = E
              & k1_relat_1(E) = A
              & r1_tarski(k2_relat_1(E),B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_funct_2)).

tff(f_173,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_funct_1(A)
        & v1_funct_2(A,k1_relat_1(A),k2_relat_1(A))
        & m1_subset_1(A,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A)))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_funct_2)).

tff(f_116,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(C,A)))
     => ( r1_tarski(k2_relat_1(D),B)
       => m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(C,B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_relset_1)).

tff(f_133,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => v1_partfun1(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_partfun1)).

tff(f_97,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_69,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_103,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_82,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_110,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(B,A)))
         => v1_xboole_0(C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc4_relset_1)).

tff(f_126,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( ( v1_funct_1(C)
          & v1_partfun1(C,A) )
       => ( v1_funct_1(C)
          & v1_funct_2(C,A,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_funct_2)).

tff(f_147,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => ( ( v1_funct_1(C)
              & v1_funct_2(C,A,B) )
           => ( v1_funct_1(C)
              & v1_partfun1(C,A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc5_funct_2)).

tff(f_49,axiom,(
    ! [A] :
      ( r1_tarski(A,k1_xboole_0)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).

tff(f_39,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(c_110,plain,(
    r2_hidden('#skF_10',k1_funct_2('#skF_8','#skF_9')) ),
    inference(cnfTransformation,[status(thm)],[f_182])).

tff(c_3625,plain,(
    ! [A_379,B_380,D_381] :
      ( '#skF_7'(A_379,B_380,k1_funct_2(A_379,B_380),D_381) = D_381
      | ~ r2_hidden(D_381,k1_funct_2(A_379,B_380)) ) ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_3640,plain,(
    '#skF_7'('#skF_8','#skF_9',k1_funct_2('#skF_8','#skF_9'),'#skF_10') = '#skF_10' ),
    inference(resolution,[status(thm)],[c_110,c_3625])).

tff(c_4318,plain,(
    ! [A_413,B_414,D_415] :
      ( r1_tarski(k2_relat_1('#skF_7'(A_413,B_414,k1_funct_2(A_413,B_414),D_415)),B_414)
      | ~ r2_hidden(D_415,k1_funct_2(A_413,B_414)) ) ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_4355,plain,
    ( r1_tarski(k2_relat_1('#skF_10'),'#skF_9')
    | ~ r2_hidden('#skF_10',k1_funct_2('#skF_8','#skF_9')) ),
    inference(superposition,[status(thm),theory(equality)],[c_3640,c_4318])).

tff(c_4367,plain,(
    r1_tarski(k2_relat_1('#skF_10'),'#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_110,c_4355])).

tff(c_76,plain,(
    ! [A_52,B_53,D_68] :
      ( v1_relat_1('#skF_7'(A_52,B_53,k1_funct_2(A_52,B_53),D_68))
      | ~ r2_hidden(D_68,k1_funct_2(A_52,B_53)) ) ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_3841,plain,
    ( v1_relat_1('#skF_10')
    | ~ r2_hidden('#skF_10',k1_funct_2('#skF_8','#skF_9')) ),
    inference(superposition,[status(thm),theory(equality)],[c_3640,c_76])).

tff(c_3847,plain,(
    v1_relat_1('#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_110,c_3841])).

tff(c_108,plain,
    ( ~ m1_subset_1('#skF_10',k1_zfmisc_1(k2_zfmisc_1('#skF_8','#skF_9')))
    | ~ v1_funct_2('#skF_10','#skF_8','#skF_9')
    | ~ v1_funct_1('#skF_10') ),
    inference(cnfTransformation,[status(thm)],[f_182])).

tff(c_132,plain,(
    ~ v1_funct_1('#skF_10') ),
    inference(splitLeft,[status(thm)],[c_108])).

tff(c_1737,plain,(
    ! [A_225,B_226,D_227] :
      ( '#skF_7'(A_225,B_226,k1_funct_2(A_225,B_226),D_227) = D_227
      | ~ r2_hidden(D_227,k1_funct_2(A_225,B_226)) ) ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_1752,plain,(
    '#skF_7'('#skF_8','#skF_9',k1_funct_2('#skF_8','#skF_9'),'#skF_10') = '#skF_10' ),
    inference(resolution,[status(thm)],[c_110,c_1737])).

tff(c_74,plain,(
    ! [A_52,B_53,D_68] :
      ( v1_funct_1('#skF_7'(A_52,B_53,k1_funct_2(A_52,B_53),D_68))
      | ~ r2_hidden(D_68,k1_funct_2(A_52,B_53)) ) ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_1912,plain,
    ( v1_funct_1('#skF_10')
    | ~ r2_hidden('#skF_10',k1_funct_2('#skF_8','#skF_9')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1752,c_74])).

tff(c_1921,plain,(
    v1_funct_1('#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_110,c_1912])).

tff(c_1923,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_132,c_1921])).

tff(c_1925,plain,(
    v1_funct_1('#skF_10') ),
    inference(splitRight,[status(thm)],[c_108])).

tff(c_3889,plain,(
    ! [A_395,B_396,D_397] :
      ( k1_relat_1('#skF_7'(A_395,B_396,k1_funct_2(A_395,B_396),D_397)) = A_395
      | ~ r2_hidden(D_397,k1_funct_2(A_395,B_396)) ) ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_3921,plain,
    ( k1_relat_1('#skF_10') = '#skF_8'
    | ~ r2_hidden('#skF_10',k1_funct_2('#skF_8','#skF_9')) ),
    inference(superposition,[status(thm),theory(equality)],[c_3640,c_3889])).

tff(c_3925,plain,(
    k1_relat_1('#skF_10') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_110,c_3921])).

tff(c_102,plain,(
    ! [A_72] :
      ( m1_subset_1(A_72,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_72),k2_relat_1(A_72))))
      | ~ v1_funct_1(A_72)
      | ~ v1_relat_1(A_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_173])).

tff(c_3937,plain,
    ( m1_subset_1('#skF_10',k1_zfmisc_1(k2_zfmisc_1('#skF_8',k2_relat_1('#skF_10'))))
    | ~ v1_funct_1('#skF_10')
    | ~ v1_relat_1('#skF_10') ),
    inference(superposition,[status(thm),theory(equality)],[c_3925,c_102])).

tff(c_3959,plain,(
    m1_subset_1('#skF_10',k1_zfmisc_1(k2_zfmisc_1('#skF_8',k2_relat_1('#skF_10')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3847,c_1925,c_3937])).

tff(c_5436,plain,(
    ! [D_457,C_458,B_459,A_460] :
      ( m1_subset_1(D_457,k1_zfmisc_1(k2_zfmisc_1(C_458,B_459)))
      | ~ r1_tarski(k2_relat_1(D_457),B_459)
      | ~ m1_subset_1(D_457,k1_zfmisc_1(k2_zfmisc_1(C_458,A_460))) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_5618,plain,(
    ! [B_463] :
      ( m1_subset_1('#skF_10',k1_zfmisc_1(k2_zfmisc_1('#skF_8',B_463)))
      | ~ r1_tarski(k2_relat_1('#skF_10'),B_463) ) ),
    inference(resolution,[status(thm)],[c_3959,c_5436])).

tff(c_1924,plain,
    ( ~ v1_funct_2('#skF_10','#skF_8','#skF_9')
    | ~ m1_subset_1('#skF_10',k1_zfmisc_1(k2_zfmisc_1('#skF_8','#skF_9'))) ),
    inference(splitRight,[status(thm)],[c_108])).

tff(c_1992,plain,(
    ~ m1_subset_1('#skF_10',k1_zfmisc_1(k2_zfmisc_1('#skF_8','#skF_9'))) ),
    inference(splitLeft,[status(thm)],[c_1924])).

tff(c_5643,plain,(
    ~ r1_tarski(k2_relat_1('#skF_10'),'#skF_9') ),
    inference(resolution,[status(thm)],[c_5618,c_1992])).

tff(c_5667,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4367,c_5643])).

tff(c_5668,plain,(
    ~ v1_funct_2('#skF_10','#skF_8','#skF_9') ),
    inference(splitRight,[status(thm)],[c_1924])).

tff(c_5669,plain,(
    m1_subset_1('#skF_10',k1_zfmisc_1(k2_zfmisc_1('#skF_8','#skF_9'))) ),
    inference(splitRight,[status(thm)],[c_1924])).

tff(c_6745,plain,(
    ! [C_560,A_561,B_562] :
      ( v1_partfun1(C_560,A_561)
      | ~ m1_subset_1(C_560,k1_zfmisc_1(k2_zfmisc_1(A_561,B_562)))
      | ~ v1_xboole_0(A_561) ) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_6781,plain,
    ( v1_partfun1('#skF_10','#skF_8')
    | ~ v1_xboole_0('#skF_8') ),
    inference(resolution,[status(thm)],[c_5669,c_6745])).

tff(c_6785,plain,(
    ~ v1_xboole_0('#skF_8') ),
    inference(splitLeft,[status(thm)],[c_6781])).

tff(c_5918,plain,(
    ! [C_487,A_488,B_489] :
      ( v1_relat_1(C_487)
      | ~ m1_subset_1(C_487,k1_zfmisc_1(k2_zfmisc_1(A_488,B_489))) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_5944,plain,(
    v1_relat_1('#skF_10') ),
    inference(resolution,[status(thm)],[c_5669,c_5918])).

tff(c_7063,plain,(
    ! [A_592,B_593,D_594] :
      ( '#skF_7'(A_592,B_593,k1_funct_2(A_592,B_593),D_594) = D_594
      | ~ r2_hidden(D_594,k1_funct_2(A_592,B_593)) ) ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_7078,plain,(
    '#skF_7'('#skF_8','#skF_9',k1_funct_2('#skF_8','#skF_9'),'#skF_10') = '#skF_10' ),
    inference(resolution,[status(thm)],[c_110,c_7063])).

tff(c_7595,plain,(
    ! [A_614,B_615,D_616] :
      ( k1_relat_1('#skF_7'(A_614,B_615,k1_funct_2(A_614,B_615),D_616)) = A_614
      | ~ r2_hidden(D_616,k1_funct_2(A_614,B_615)) ) ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_7628,plain,
    ( k1_relat_1('#skF_10') = '#skF_8'
    | ~ r2_hidden('#skF_10',k1_funct_2('#skF_8','#skF_9')) ),
    inference(superposition,[status(thm),theory(equality)],[c_7078,c_7595])).

tff(c_7632,plain,(
    k1_relat_1('#skF_10') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_110,c_7628])).

tff(c_1987,plain,(
    ! [A_242,B_243] :
      ( r2_hidden('#skF_2'(A_242,B_243),A_242)
      | r1_tarski(A_242,B_243) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_1991,plain,(
    ! [A_242,B_243] :
      ( ~ v1_xboole_0(A_242)
      | r1_tarski(A_242,B_243) ) ),
    inference(resolution,[status(thm)],[c_1987,c_2])).

tff(c_34,plain,(
    ! [A_17,B_18] :
      ( m1_subset_1(A_17,k1_zfmisc_1(B_18))
      | ~ r1_tarski(A_17,B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_6407,plain,(
    ! [C_528,A_529,B_530] :
      ( v4_relat_1(C_528,A_529)
      | ~ m1_subset_1(C_528,k1_zfmisc_1(k2_zfmisc_1(A_529,B_530))) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_6467,plain,(
    ! [A_536,A_537,B_538] :
      ( v4_relat_1(A_536,A_537)
      | ~ r1_tarski(A_536,k2_zfmisc_1(A_537,B_538)) ) ),
    inference(resolution,[status(thm)],[c_34,c_6407])).

tff(c_6495,plain,(
    ! [A_242,A_537] :
      ( v4_relat_1(A_242,A_537)
      | ~ v1_xboole_0(A_242) ) ),
    inference(resolution,[status(thm)],[c_1991,c_6467])).

tff(c_40,plain,(
    ! [B_23,A_22] :
      ( r1_tarski(k1_relat_1(B_23),A_22)
      | ~ v4_relat_1(B_23,A_22)
      | ~ v1_relat_1(B_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_7651,plain,(
    ! [A_22] :
      ( r1_tarski('#skF_8',A_22)
      | ~ v4_relat_1('#skF_10',A_22)
      | ~ v1_relat_1('#skF_10') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_7632,c_40])).

tff(c_7713,plain,(
    ! [A_618] :
      ( r1_tarski('#skF_8',A_618)
      | ~ v4_relat_1('#skF_10',A_618) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5944,c_7651])).

tff(c_7725,plain,(
    ! [A_537] :
      ( r1_tarski('#skF_8',A_537)
      | ~ v1_xboole_0('#skF_10') ) ),
    inference(resolution,[status(thm)],[c_6495,c_7713])).

tff(c_7731,plain,(
    ~ v1_xboole_0('#skF_10') ),
    inference(splitLeft,[status(thm)],[c_7725])).

tff(c_7639,plain,
    ( m1_subset_1('#skF_10',k1_zfmisc_1(k2_zfmisc_1('#skF_8',k2_relat_1('#skF_10'))))
    | ~ v1_funct_1('#skF_10')
    | ~ v1_relat_1('#skF_10') ),
    inference(superposition,[status(thm),theory(equality)],[c_7632,c_102])).

tff(c_7663,plain,(
    m1_subset_1('#skF_10',k1_zfmisc_1(k2_zfmisc_1('#skF_8',k2_relat_1('#skF_10')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5944,c_1925,c_7639])).

tff(c_52,plain,(
    ! [C_36,B_34,A_33] :
      ( v1_xboole_0(C_36)
      | ~ m1_subset_1(C_36,k1_zfmisc_1(k2_zfmisc_1(B_34,A_33)))
      | ~ v1_xboole_0(A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_7821,plain,
    ( v1_xboole_0('#skF_10')
    | ~ v1_xboole_0(k2_relat_1('#skF_10')) ),
    inference(resolution,[status(thm)],[c_7663,c_52])).

tff(c_7846,plain,(
    ~ v1_xboole_0(k2_relat_1('#skF_10')) ),
    inference(negUnitSimplification,[status(thm)],[c_7731,c_7821])).

tff(c_7754,plain,(
    ! [C_620,A_621,B_622] :
      ( v1_funct_2(C_620,A_621,B_622)
      | ~ v1_partfun1(C_620,A_621)
      | ~ v1_funct_1(C_620)
      | ~ m1_subset_1(C_620,k1_zfmisc_1(k2_zfmisc_1(A_621,B_622))) ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_7776,plain,
    ( v1_funct_2('#skF_10','#skF_8','#skF_9')
    | ~ v1_partfun1('#skF_10','#skF_8')
    | ~ v1_funct_1('#skF_10') ),
    inference(resolution,[status(thm)],[c_5669,c_7754])).

tff(c_7796,plain,
    ( v1_funct_2('#skF_10','#skF_8','#skF_9')
    | ~ v1_partfun1('#skF_10','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1925,c_7776])).

tff(c_7797,plain,(
    ~ v1_partfun1('#skF_10','#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_5668,c_7796])).

tff(c_104,plain,(
    ! [A_72] :
      ( v1_funct_2(A_72,k1_relat_1(A_72),k2_relat_1(A_72))
      | ~ v1_funct_1(A_72)
      | ~ v1_relat_1(A_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_173])).

tff(c_7648,plain,
    ( v1_funct_2('#skF_10','#skF_8',k2_relat_1('#skF_10'))
    | ~ v1_funct_1('#skF_10')
    | ~ v1_relat_1('#skF_10') ),
    inference(superposition,[status(thm),theory(equality)],[c_7632,c_104])).

tff(c_7669,plain,(
    v1_funct_2('#skF_10','#skF_8',k2_relat_1('#skF_10')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5944,c_1925,c_7648])).

tff(c_9461,plain,(
    ! [C_694,A_695,B_696] :
      ( v1_partfun1(C_694,A_695)
      | ~ v1_funct_2(C_694,A_695,B_696)
      | ~ v1_funct_1(C_694)
      | ~ m1_subset_1(C_694,k1_zfmisc_1(k2_zfmisc_1(A_695,B_696)))
      | v1_xboole_0(B_696) ) ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_9474,plain,
    ( v1_partfun1('#skF_10','#skF_8')
    | ~ v1_funct_2('#skF_10','#skF_8',k2_relat_1('#skF_10'))
    | ~ v1_funct_1('#skF_10')
    | v1_xboole_0(k2_relat_1('#skF_10')) ),
    inference(resolution,[status(thm)],[c_7663,c_9461])).

tff(c_9517,plain,
    ( v1_partfun1('#skF_10','#skF_8')
    | v1_xboole_0(k2_relat_1('#skF_10')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1925,c_7669,c_9474])).

tff(c_9519,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_7846,c_7797,c_9517])).

tff(c_9521,plain,(
    v1_xboole_0('#skF_10') ),
    inference(splitRight,[status(thm)],[c_7725])).

tff(c_6503,plain,(
    ! [B_544,A_545] :
      ( r1_tarski(k1_relat_1(B_544),A_545)
      | ~ v4_relat_1(B_544,A_545)
      | ~ v1_relat_1(B_544) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_20,plain,(
    ! [A_12] :
      ( k1_xboole_0 = A_12
      | ~ r1_tarski(A_12,k1_xboole_0) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_6543,plain,(
    ! [B_548] :
      ( k1_relat_1(B_548) = k1_xboole_0
      | ~ v4_relat_1(B_548,k1_xboole_0)
      | ~ v1_relat_1(B_548) ) ),
    inference(resolution,[status(thm)],[c_6503,c_20])).

tff(c_6568,plain,(
    ! [A_242] :
      ( k1_relat_1(A_242) = k1_xboole_0
      | ~ v1_relat_1(A_242)
      | ~ v1_xboole_0(A_242) ) ),
    inference(resolution,[status(thm)],[c_6495,c_6543])).

tff(c_9524,plain,
    ( k1_relat_1('#skF_10') = k1_xboole_0
    | ~ v1_relat_1('#skF_10') ),
    inference(resolution,[status(thm)],[c_9521,c_6568])).

tff(c_9540,plain,(
    k1_xboole_0 = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5944,c_7632,c_9524])).

tff(c_12,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_9582,plain,(
    v1_xboole_0('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_9540,c_12])).

tff(c_9584,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_6785,c_9582])).

tff(c_9585,plain,(
    v1_partfun1('#skF_10','#skF_8') ),
    inference(splitRight,[status(thm)],[c_6781])).

tff(c_10670,plain,(
    ! [C_749,A_750,B_751] :
      ( v1_funct_2(C_749,A_750,B_751)
      | ~ v1_partfun1(C_749,A_750)
      | ~ v1_funct_1(C_749)
      | ~ m1_subset_1(C_749,k1_zfmisc_1(k2_zfmisc_1(A_750,B_751))) ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_10695,plain,
    ( v1_funct_2('#skF_10','#skF_8','#skF_9')
    | ~ v1_partfun1('#skF_10','#skF_8')
    | ~ v1_funct_1('#skF_10') ),
    inference(resolution,[status(thm)],[c_5669,c_10670])).

tff(c_10718,plain,(
    v1_funct_2('#skF_10','#skF_8','#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1925,c_9585,c_10695])).

tff(c_10720,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_5668,c_10718])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:30:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.73/2.65  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.73/2.66  
% 7.73/2.66  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.73/2.66  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_zfmisc_1 > k1_funct_2 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_6 > #skF_1 > #skF_4 > #skF_10 > #skF_5 > #skF_7 > #skF_9 > #skF_8 > #skF_3 > #skF_2
% 7.73/2.66  
% 7.73/2.66  %Foreground sorts:
% 7.73/2.66  
% 7.73/2.66  
% 7.73/2.66  %Background operators:
% 7.73/2.66  
% 7.73/2.66  
% 7.73/2.66  %Foreground operators:
% 7.73/2.66  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 7.73/2.66  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.73/2.66  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 7.73/2.66  tff('#skF_6', type, '#skF_6': ($i * $i * $i) > $i).
% 7.73/2.66  tff('#skF_1', type, '#skF_1': $i > $i).
% 7.73/2.66  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 7.73/2.66  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 7.73/2.66  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.73/2.66  tff('#skF_10', type, '#skF_10': $i).
% 7.73/2.66  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 7.73/2.66  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 7.73/2.66  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 7.73/2.66  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 7.73/2.66  tff('#skF_7', type, '#skF_7': ($i * $i * $i * $i) > $i).
% 7.73/2.66  tff('#skF_9', type, '#skF_9': $i).
% 7.73/2.66  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 7.73/2.66  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 7.73/2.66  tff(k1_funct_2, type, k1_funct_2: ($i * $i) > $i).
% 7.73/2.66  tff('#skF_8', type, '#skF_8': $i).
% 7.73/2.66  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.73/2.66  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 7.73/2.66  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 7.73/2.66  tff('#skF_3', type, '#skF_3': $i > $i).
% 7.73/2.66  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.73/2.66  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 7.73/2.66  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 7.73/2.66  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 7.73/2.66  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 7.73/2.66  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 7.73/2.66  
% 7.73/2.68  tff(f_182, negated_conjecture, ~(![A, B, C]: (r2_hidden(C, k1_funct_2(A, B)) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t121_funct_2)).
% 7.73/2.68  tff(f_163, axiom, (![A, B, C]: ((C = k1_funct_2(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (?[E]: ((((v1_relat_1(E) & v1_funct_1(E)) & (D = E)) & (k1_relat_1(E) = A)) & r1_tarski(k2_relat_1(E), B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_funct_2)).
% 7.73/2.68  tff(f_173, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => ((v1_funct_1(A) & v1_funct_2(A, k1_relat_1(A), k2_relat_1(A))) & m1_subset_1(A, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_funct_2)).
% 7.73/2.68  tff(f_116, axiom, (![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(C, A))) => (r1_tarski(k2_relat_1(D), B) => m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(C, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t14_relset_1)).
% 7.73/2.68  tff(f_133, axiom, (![A, B]: (v1_xboole_0(A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_partfun1(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_partfun1)).
% 7.73/2.68  tff(f_97, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 7.73/2.68  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 7.73/2.68  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 7.73/2.68  tff(f_69, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 7.73/2.68  tff(f_103, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 7.73/2.68  tff(f_82, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d18_relat_1)).
% 7.73/2.68  tff(f_110, axiom, (![A, B]: (v1_xboole_0(A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => v1_xboole_0(C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc4_relset_1)).
% 7.73/2.68  tff(f_126, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v1_partfun1(C, A)) => (v1_funct_1(C) & v1_funct_2(C, A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_funct_2)).
% 7.73/2.68  tff(f_147, axiom, (![A, B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) => (v1_funct_1(C) & v1_partfun1(C, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc5_funct_2)).
% 7.73/2.68  tff(f_49, axiom, (![A]: (r1_tarski(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_1)).
% 7.73/2.68  tff(f_39, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 7.73/2.68  tff(c_110, plain, (r2_hidden('#skF_10', k1_funct_2('#skF_8', '#skF_9'))), inference(cnfTransformation, [status(thm)], [f_182])).
% 7.73/2.68  tff(c_3625, plain, (![A_379, B_380, D_381]: ('#skF_7'(A_379, B_380, k1_funct_2(A_379, B_380), D_381)=D_381 | ~r2_hidden(D_381, k1_funct_2(A_379, B_380)))), inference(cnfTransformation, [status(thm)], [f_163])).
% 7.73/2.68  tff(c_3640, plain, ('#skF_7'('#skF_8', '#skF_9', k1_funct_2('#skF_8', '#skF_9'), '#skF_10')='#skF_10'), inference(resolution, [status(thm)], [c_110, c_3625])).
% 7.73/2.68  tff(c_4318, plain, (![A_413, B_414, D_415]: (r1_tarski(k2_relat_1('#skF_7'(A_413, B_414, k1_funct_2(A_413, B_414), D_415)), B_414) | ~r2_hidden(D_415, k1_funct_2(A_413, B_414)))), inference(cnfTransformation, [status(thm)], [f_163])).
% 7.73/2.68  tff(c_4355, plain, (r1_tarski(k2_relat_1('#skF_10'), '#skF_9') | ~r2_hidden('#skF_10', k1_funct_2('#skF_8', '#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_3640, c_4318])).
% 7.73/2.68  tff(c_4367, plain, (r1_tarski(k2_relat_1('#skF_10'), '#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_110, c_4355])).
% 7.73/2.68  tff(c_76, plain, (![A_52, B_53, D_68]: (v1_relat_1('#skF_7'(A_52, B_53, k1_funct_2(A_52, B_53), D_68)) | ~r2_hidden(D_68, k1_funct_2(A_52, B_53)))), inference(cnfTransformation, [status(thm)], [f_163])).
% 7.73/2.68  tff(c_3841, plain, (v1_relat_1('#skF_10') | ~r2_hidden('#skF_10', k1_funct_2('#skF_8', '#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_3640, c_76])).
% 7.73/2.68  tff(c_3847, plain, (v1_relat_1('#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_110, c_3841])).
% 7.73/2.68  tff(c_108, plain, (~m1_subset_1('#skF_10', k1_zfmisc_1(k2_zfmisc_1('#skF_8', '#skF_9'))) | ~v1_funct_2('#skF_10', '#skF_8', '#skF_9') | ~v1_funct_1('#skF_10')), inference(cnfTransformation, [status(thm)], [f_182])).
% 7.73/2.68  tff(c_132, plain, (~v1_funct_1('#skF_10')), inference(splitLeft, [status(thm)], [c_108])).
% 7.73/2.68  tff(c_1737, plain, (![A_225, B_226, D_227]: ('#skF_7'(A_225, B_226, k1_funct_2(A_225, B_226), D_227)=D_227 | ~r2_hidden(D_227, k1_funct_2(A_225, B_226)))), inference(cnfTransformation, [status(thm)], [f_163])).
% 7.73/2.68  tff(c_1752, plain, ('#skF_7'('#skF_8', '#skF_9', k1_funct_2('#skF_8', '#skF_9'), '#skF_10')='#skF_10'), inference(resolution, [status(thm)], [c_110, c_1737])).
% 7.73/2.68  tff(c_74, plain, (![A_52, B_53, D_68]: (v1_funct_1('#skF_7'(A_52, B_53, k1_funct_2(A_52, B_53), D_68)) | ~r2_hidden(D_68, k1_funct_2(A_52, B_53)))), inference(cnfTransformation, [status(thm)], [f_163])).
% 7.73/2.68  tff(c_1912, plain, (v1_funct_1('#skF_10') | ~r2_hidden('#skF_10', k1_funct_2('#skF_8', '#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_1752, c_74])).
% 7.73/2.68  tff(c_1921, plain, (v1_funct_1('#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_110, c_1912])).
% 7.73/2.68  tff(c_1923, plain, $false, inference(negUnitSimplification, [status(thm)], [c_132, c_1921])).
% 7.73/2.68  tff(c_1925, plain, (v1_funct_1('#skF_10')), inference(splitRight, [status(thm)], [c_108])).
% 7.73/2.68  tff(c_3889, plain, (![A_395, B_396, D_397]: (k1_relat_1('#skF_7'(A_395, B_396, k1_funct_2(A_395, B_396), D_397))=A_395 | ~r2_hidden(D_397, k1_funct_2(A_395, B_396)))), inference(cnfTransformation, [status(thm)], [f_163])).
% 7.73/2.68  tff(c_3921, plain, (k1_relat_1('#skF_10')='#skF_8' | ~r2_hidden('#skF_10', k1_funct_2('#skF_8', '#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_3640, c_3889])).
% 7.73/2.68  tff(c_3925, plain, (k1_relat_1('#skF_10')='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_110, c_3921])).
% 7.73/2.68  tff(c_102, plain, (![A_72]: (m1_subset_1(A_72, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_72), k2_relat_1(A_72)))) | ~v1_funct_1(A_72) | ~v1_relat_1(A_72))), inference(cnfTransformation, [status(thm)], [f_173])).
% 7.73/2.68  tff(c_3937, plain, (m1_subset_1('#skF_10', k1_zfmisc_1(k2_zfmisc_1('#skF_8', k2_relat_1('#skF_10')))) | ~v1_funct_1('#skF_10') | ~v1_relat_1('#skF_10')), inference(superposition, [status(thm), theory('equality')], [c_3925, c_102])).
% 7.73/2.68  tff(c_3959, plain, (m1_subset_1('#skF_10', k1_zfmisc_1(k2_zfmisc_1('#skF_8', k2_relat_1('#skF_10'))))), inference(demodulation, [status(thm), theory('equality')], [c_3847, c_1925, c_3937])).
% 7.73/2.68  tff(c_5436, plain, (![D_457, C_458, B_459, A_460]: (m1_subset_1(D_457, k1_zfmisc_1(k2_zfmisc_1(C_458, B_459))) | ~r1_tarski(k2_relat_1(D_457), B_459) | ~m1_subset_1(D_457, k1_zfmisc_1(k2_zfmisc_1(C_458, A_460))))), inference(cnfTransformation, [status(thm)], [f_116])).
% 7.73/2.68  tff(c_5618, plain, (![B_463]: (m1_subset_1('#skF_10', k1_zfmisc_1(k2_zfmisc_1('#skF_8', B_463))) | ~r1_tarski(k2_relat_1('#skF_10'), B_463))), inference(resolution, [status(thm)], [c_3959, c_5436])).
% 7.73/2.68  tff(c_1924, plain, (~v1_funct_2('#skF_10', '#skF_8', '#skF_9') | ~m1_subset_1('#skF_10', k1_zfmisc_1(k2_zfmisc_1('#skF_8', '#skF_9')))), inference(splitRight, [status(thm)], [c_108])).
% 7.73/2.68  tff(c_1992, plain, (~m1_subset_1('#skF_10', k1_zfmisc_1(k2_zfmisc_1('#skF_8', '#skF_9')))), inference(splitLeft, [status(thm)], [c_1924])).
% 7.73/2.68  tff(c_5643, plain, (~r1_tarski(k2_relat_1('#skF_10'), '#skF_9')), inference(resolution, [status(thm)], [c_5618, c_1992])).
% 7.73/2.68  tff(c_5667, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4367, c_5643])).
% 7.73/2.68  tff(c_5668, plain, (~v1_funct_2('#skF_10', '#skF_8', '#skF_9')), inference(splitRight, [status(thm)], [c_1924])).
% 7.73/2.68  tff(c_5669, plain, (m1_subset_1('#skF_10', k1_zfmisc_1(k2_zfmisc_1('#skF_8', '#skF_9')))), inference(splitRight, [status(thm)], [c_1924])).
% 7.73/2.68  tff(c_6745, plain, (![C_560, A_561, B_562]: (v1_partfun1(C_560, A_561) | ~m1_subset_1(C_560, k1_zfmisc_1(k2_zfmisc_1(A_561, B_562))) | ~v1_xboole_0(A_561))), inference(cnfTransformation, [status(thm)], [f_133])).
% 7.73/2.68  tff(c_6781, plain, (v1_partfun1('#skF_10', '#skF_8') | ~v1_xboole_0('#skF_8')), inference(resolution, [status(thm)], [c_5669, c_6745])).
% 7.73/2.68  tff(c_6785, plain, (~v1_xboole_0('#skF_8')), inference(splitLeft, [status(thm)], [c_6781])).
% 7.73/2.68  tff(c_5918, plain, (![C_487, A_488, B_489]: (v1_relat_1(C_487) | ~m1_subset_1(C_487, k1_zfmisc_1(k2_zfmisc_1(A_488, B_489))))), inference(cnfTransformation, [status(thm)], [f_97])).
% 7.73/2.68  tff(c_5944, plain, (v1_relat_1('#skF_10')), inference(resolution, [status(thm)], [c_5669, c_5918])).
% 7.73/2.68  tff(c_7063, plain, (![A_592, B_593, D_594]: ('#skF_7'(A_592, B_593, k1_funct_2(A_592, B_593), D_594)=D_594 | ~r2_hidden(D_594, k1_funct_2(A_592, B_593)))), inference(cnfTransformation, [status(thm)], [f_163])).
% 7.73/2.68  tff(c_7078, plain, ('#skF_7'('#skF_8', '#skF_9', k1_funct_2('#skF_8', '#skF_9'), '#skF_10')='#skF_10'), inference(resolution, [status(thm)], [c_110, c_7063])).
% 7.73/2.68  tff(c_7595, plain, (![A_614, B_615, D_616]: (k1_relat_1('#skF_7'(A_614, B_615, k1_funct_2(A_614, B_615), D_616))=A_614 | ~r2_hidden(D_616, k1_funct_2(A_614, B_615)))), inference(cnfTransformation, [status(thm)], [f_163])).
% 7.73/2.68  tff(c_7628, plain, (k1_relat_1('#skF_10')='#skF_8' | ~r2_hidden('#skF_10', k1_funct_2('#skF_8', '#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_7078, c_7595])).
% 7.73/2.68  tff(c_7632, plain, (k1_relat_1('#skF_10')='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_110, c_7628])).
% 7.73/2.68  tff(c_1987, plain, (![A_242, B_243]: (r2_hidden('#skF_2'(A_242, B_243), A_242) | r1_tarski(A_242, B_243))), inference(cnfTransformation, [status(thm)], [f_38])).
% 7.73/2.68  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 7.73/2.68  tff(c_1991, plain, (![A_242, B_243]: (~v1_xboole_0(A_242) | r1_tarski(A_242, B_243))), inference(resolution, [status(thm)], [c_1987, c_2])).
% 7.73/2.68  tff(c_34, plain, (![A_17, B_18]: (m1_subset_1(A_17, k1_zfmisc_1(B_18)) | ~r1_tarski(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_69])).
% 7.73/2.68  tff(c_6407, plain, (![C_528, A_529, B_530]: (v4_relat_1(C_528, A_529) | ~m1_subset_1(C_528, k1_zfmisc_1(k2_zfmisc_1(A_529, B_530))))), inference(cnfTransformation, [status(thm)], [f_103])).
% 7.73/2.68  tff(c_6467, plain, (![A_536, A_537, B_538]: (v4_relat_1(A_536, A_537) | ~r1_tarski(A_536, k2_zfmisc_1(A_537, B_538)))), inference(resolution, [status(thm)], [c_34, c_6407])).
% 7.73/2.68  tff(c_6495, plain, (![A_242, A_537]: (v4_relat_1(A_242, A_537) | ~v1_xboole_0(A_242))), inference(resolution, [status(thm)], [c_1991, c_6467])).
% 7.73/2.68  tff(c_40, plain, (![B_23, A_22]: (r1_tarski(k1_relat_1(B_23), A_22) | ~v4_relat_1(B_23, A_22) | ~v1_relat_1(B_23))), inference(cnfTransformation, [status(thm)], [f_82])).
% 7.73/2.68  tff(c_7651, plain, (![A_22]: (r1_tarski('#skF_8', A_22) | ~v4_relat_1('#skF_10', A_22) | ~v1_relat_1('#skF_10'))), inference(superposition, [status(thm), theory('equality')], [c_7632, c_40])).
% 7.73/2.68  tff(c_7713, plain, (![A_618]: (r1_tarski('#skF_8', A_618) | ~v4_relat_1('#skF_10', A_618))), inference(demodulation, [status(thm), theory('equality')], [c_5944, c_7651])).
% 7.73/2.68  tff(c_7725, plain, (![A_537]: (r1_tarski('#skF_8', A_537) | ~v1_xboole_0('#skF_10'))), inference(resolution, [status(thm)], [c_6495, c_7713])).
% 7.73/2.68  tff(c_7731, plain, (~v1_xboole_0('#skF_10')), inference(splitLeft, [status(thm)], [c_7725])).
% 7.73/2.68  tff(c_7639, plain, (m1_subset_1('#skF_10', k1_zfmisc_1(k2_zfmisc_1('#skF_8', k2_relat_1('#skF_10')))) | ~v1_funct_1('#skF_10') | ~v1_relat_1('#skF_10')), inference(superposition, [status(thm), theory('equality')], [c_7632, c_102])).
% 7.73/2.68  tff(c_7663, plain, (m1_subset_1('#skF_10', k1_zfmisc_1(k2_zfmisc_1('#skF_8', k2_relat_1('#skF_10'))))), inference(demodulation, [status(thm), theory('equality')], [c_5944, c_1925, c_7639])).
% 7.73/2.68  tff(c_52, plain, (![C_36, B_34, A_33]: (v1_xboole_0(C_36) | ~m1_subset_1(C_36, k1_zfmisc_1(k2_zfmisc_1(B_34, A_33))) | ~v1_xboole_0(A_33))), inference(cnfTransformation, [status(thm)], [f_110])).
% 7.73/2.68  tff(c_7821, plain, (v1_xboole_0('#skF_10') | ~v1_xboole_0(k2_relat_1('#skF_10'))), inference(resolution, [status(thm)], [c_7663, c_52])).
% 7.73/2.68  tff(c_7846, plain, (~v1_xboole_0(k2_relat_1('#skF_10'))), inference(negUnitSimplification, [status(thm)], [c_7731, c_7821])).
% 7.73/2.68  tff(c_7754, plain, (![C_620, A_621, B_622]: (v1_funct_2(C_620, A_621, B_622) | ~v1_partfun1(C_620, A_621) | ~v1_funct_1(C_620) | ~m1_subset_1(C_620, k1_zfmisc_1(k2_zfmisc_1(A_621, B_622))))), inference(cnfTransformation, [status(thm)], [f_126])).
% 7.73/2.68  tff(c_7776, plain, (v1_funct_2('#skF_10', '#skF_8', '#skF_9') | ~v1_partfun1('#skF_10', '#skF_8') | ~v1_funct_1('#skF_10')), inference(resolution, [status(thm)], [c_5669, c_7754])).
% 7.73/2.68  tff(c_7796, plain, (v1_funct_2('#skF_10', '#skF_8', '#skF_9') | ~v1_partfun1('#skF_10', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_1925, c_7776])).
% 7.73/2.68  tff(c_7797, plain, (~v1_partfun1('#skF_10', '#skF_8')), inference(negUnitSimplification, [status(thm)], [c_5668, c_7796])).
% 7.73/2.68  tff(c_104, plain, (![A_72]: (v1_funct_2(A_72, k1_relat_1(A_72), k2_relat_1(A_72)) | ~v1_funct_1(A_72) | ~v1_relat_1(A_72))), inference(cnfTransformation, [status(thm)], [f_173])).
% 7.73/2.68  tff(c_7648, plain, (v1_funct_2('#skF_10', '#skF_8', k2_relat_1('#skF_10')) | ~v1_funct_1('#skF_10') | ~v1_relat_1('#skF_10')), inference(superposition, [status(thm), theory('equality')], [c_7632, c_104])).
% 7.73/2.68  tff(c_7669, plain, (v1_funct_2('#skF_10', '#skF_8', k2_relat_1('#skF_10'))), inference(demodulation, [status(thm), theory('equality')], [c_5944, c_1925, c_7648])).
% 7.73/2.68  tff(c_9461, plain, (![C_694, A_695, B_696]: (v1_partfun1(C_694, A_695) | ~v1_funct_2(C_694, A_695, B_696) | ~v1_funct_1(C_694) | ~m1_subset_1(C_694, k1_zfmisc_1(k2_zfmisc_1(A_695, B_696))) | v1_xboole_0(B_696))), inference(cnfTransformation, [status(thm)], [f_147])).
% 7.73/2.68  tff(c_9474, plain, (v1_partfun1('#skF_10', '#skF_8') | ~v1_funct_2('#skF_10', '#skF_8', k2_relat_1('#skF_10')) | ~v1_funct_1('#skF_10') | v1_xboole_0(k2_relat_1('#skF_10'))), inference(resolution, [status(thm)], [c_7663, c_9461])).
% 7.73/2.68  tff(c_9517, plain, (v1_partfun1('#skF_10', '#skF_8') | v1_xboole_0(k2_relat_1('#skF_10'))), inference(demodulation, [status(thm), theory('equality')], [c_1925, c_7669, c_9474])).
% 7.73/2.68  tff(c_9519, plain, $false, inference(negUnitSimplification, [status(thm)], [c_7846, c_7797, c_9517])).
% 7.73/2.68  tff(c_9521, plain, (v1_xboole_0('#skF_10')), inference(splitRight, [status(thm)], [c_7725])).
% 7.73/2.68  tff(c_6503, plain, (![B_544, A_545]: (r1_tarski(k1_relat_1(B_544), A_545) | ~v4_relat_1(B_544, A_545) | ~v1_relat_1(B_544))), inference(cnfTransformation, [status(thm)], [f_82])).
% 7.73/2.68  tff(c_20, plain, (![A_12]: (k1_xboole_0=A_12 | ~r1_tarski(A_12, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_49])).
% 7.73/2.68  tff(c_6543, plain, (![B_548]: (k1_relat_1(B_548)=k1_xboole_0 | ~v4_relat_1(B_548, k1_xboole_0) | ~v1_relat_1(B_548))), inference(resolution, [status(thm)], [c_6503, c_20])).
% 7.73/2.68  tff(c_6568, plain, (![A_242]: (k1_relat_1(A_242)=k1_xboole_0 | ~v1_relat_1(A_242) | ~v1_xboole_0(A_242))), inference(resolution, [status(thm)], [c_6495, c_6543])).
% 7.73/2.68  tff(c_9524, plain, (k1_relat_1('#skF_10')=k1_xboole_0 | ~v1_relat_1('#skF_10')), inference(resolution, [status(thm)], [c_9521, c_6568])).
% 7.73/2.68  tff(c_9540, plain, (k1_xboole_0='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_5944, c_7632, c_9524])).
% 7.73/2.68  tff(c_12, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 7.73/2.68  tff(c_9582, plain, (v1_xboole_0('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_9540, c_12])).
% 7.73/2.68  tff(c_9584, plain, $false, inference(negUnitSimplification, [status(thm)], [c_6785, c_9582])).
% 7.73/2.68  tff(c_9585, plain, (v1_partfun1('#skF_10', '#skF_8')), inference(splitRight, [status(thm)], [c_6781])).
% 7.73/2.68  tff(c_10670, plain, (![C_749, A_750, B_751]: (v1_funct_2(C_749, A_750, B_751) | ~v1_partfun1(C_749, A_750) | ~v1_funct_1(C_749) | ~m1_subset_1(C_749, k1_zfmisc_1(k2_zfmisc_1(A_750, B_751))))), inference(cnfTransformation, [status(thm)], [f_126])).
% 7.73/2.68  tff(c_10695, plain, (v1_funct_2('#skF_10', '#skF_8', '#skF_9') | ~v1_partfun1('#skF_10', '#skF_8') | ~v1_funct_1('#skF_10')), inference(resolution, [status(thm)], [c_5669, c_10670])).
% 7.73/2.68  tff(c_10718, plain, (v1_funct_2('#skF_10', '#skF_8', '#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_1925, c_9585, c_10695])).
% 7.73/2.68  tff(c_10720, plain, $false, inference(negUnitSimplification, [status(thm)], [c_5668, c_10718])).
% 7.73/2.68  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.73/2.68  
% 7.73/2.68  Inference rules
% 7.73/2.68  ----------------------
% 7.73/2.68  #Ref     : 0
% 7.73/2.68  #Sup     : 2292
% 7.73/2.68  #Fact    : 0
% 7.73/2.68  #Define  : 0
% 7.73/2.68  #Split   : 27
% 7.73/2.68  #Chain   : 0
% 7.73/2.68  #Close   : 0
% 7.73/2.68  
% 7.73/2.68  Ordering : KBO
% 7.73/2.68  
% 7.73/2.68  Simplification rules
% 7.73/2.68  ----------------------
% 7.73/2.68  #Subsume      : 595
% 7.73/2.68  #Demod        : 1369
% 7.73/2.68  #Tautology    : 860
% 7.73/2.68  #SimpNegUnit  : 63
% 7.73/2.68  #BackRed      : 92
% 7.73/2.68  
% 7.73/2.68  #Partial instantiations: 0
% 7.73/2.68  #Strategies tried      : 1
% 7.73/2.68  
% 7.73/2.68  Timing (in seconds)
% 7.73/2.68  ----------------------
% 7.73/2.69  Preprocessing        : 0.37
% 7.73/2.69  Parsing              : 0.18
% 7.73/2.69  CNF conversion       : 0.03
% 7.73/2.69  Main loop            : 1.54
% 7.73/2.69  Inferencing          : 0.53
% 7.73/2.69  Reduction            : 0.50
% 7.73/2.69  Demodulation         : 0.35
% 7.73/2.69  BG Simplification    : 0.06
% 7.73/2.69  Subsumption          : 0.33
% 7.73/2.69  Abstraction          : 0.06
% 7.73/2.69  MUC search           : 0.00
% 7.73/2.69  Cooper               : 0.00
% 7.73/2.69  Total                : 1.96
% 7.73/2.69  Index Insertion      : 0.00
% 7.73/2.69  Index Deletion       : 0.00
% 7.73/2.69  Index Matching       : 0.00
% 7.73/2.69  BG Taut test         : 0.00
%------------------------------------------------------------------------------
