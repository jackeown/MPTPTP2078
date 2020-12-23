%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:16:39 EST 2020

% Result     : Theorem 5.09s
% Output     : CNFRefutation 5.42s
% Verified   : 
% Statistics : Number of formulae       :  116 ( 279 expanded)
%              Number of leaves         :   47 ( 114 expanded)
%              Depth                    :    9
%              Number of atoms          :  179 ( 680 expanded)
%              Number of equality atoms :   18 ( 116 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v1_partfun1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k4_tarski > k2_zfmisc_1 > k1_funct_2 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_13 > #skF_6 > #skF_18 > #skF_17 > #skF_1 > #skF_19 > #skF_3 > #skF_10 > #skF_5 > #skF_16 > #skF_8 > #skF_9 > #skF_15 > #skF_14 > #skF_11 > #skF_2 > #skF_12 > #skF_7 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_13',type,(
    '#skF_13': ( $i * $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#skF_18',type,(
    '#skF_18': $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff('#skF_17',type,(
    '#skF_17': $i )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff('#skF_19',type,(
    '#skF_19': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_10',type,(
    '#skF_10': $i > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff('#skF_16',type,(
    '#skF_16': ( $i * $i * $i * $i ) > $i )).

tff(v1_partfun1,type,(
    v1_partfun1: ( $i * $i ) > $o )).

tff('#skF_8',type,(
    '#skF_8': ( $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': ( $i * $i * $i ) > $i )).

tff(k1_funct_2,type,(
    k1_funct_2: ( $i * $i ) > $i )).

tff('#skF_15',type,(
    '#skF_15': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_14',type,(
    '#skF_14': ( $i * $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_11',type,(
    '#skF_11': $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_12',type,(
    '#skF_12': $i > $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_143,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r2_hidden(C,k1_funct_2(A,B))
       => ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t121_funct_2)).

tff(f_124,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_funct_2)).

tff(f_37,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_77,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( ( r1_tarski(k1_relat_1(C),A)
          & r1_tarski(k2_relat_1(C),B) )
       => m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_relset_1)).

tff(f_94,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => v1_partfun1(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_partfun1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_60,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( B = k2_relat_1(A)
        <=> ! [C] :
              ( r2_hidden(C,B)
            <=> ? [D] :
                  ( r2_hidden(D,k1_relat_1(A))
                  & C = k1_funct_1(A,D) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_funct_1)).

tff(f_87,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( ( v1_funct_1(C)
          & v1_partfun1(C,A) )
       => ( v1_funct_1(C)
          & v1_funct_2(C,A,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_funct_2)).

tff(f_134,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_funct_1(A)
        & v1_funct_2(A,k1_relat_1(A),k2_relat_1(A))
        & m1_subset_1(A,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A)))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_funct_2)).

tff(f_108,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => ( ( v1_funct_1(C)
              & v1_funct_2(C,A,B) )
           => ( v1_funct_1(C)
              & v1_partfun1(C,A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc5_funct_2)).

tff(c_106,plain,(
    r2_hidden('#skF_19',k1_funct_2('#skF_17','#skF_18')) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_323,plain,(
    ! [A_169,B_170,D_171] :
      ( '#skF_16'(A_169,B_170,k1_funct_2(A_169,B_170),D_171) = D_171
      | ~ r2_hidden(D_171,k1_funct_2(A_169,B_170)) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_342,plain,(
    '#skF_16'('#skF_17','#skF_18',k1_funct_2('#skF_17','#skF_18'),'#skF_19') = '#skF_19' ),
    inference(resolution,[status(thm)],[c_106,c_323])).

tff(c_434,plain,(
    ! [A_180,B_181,D_182] :
      ( v1_relat_1('#skF_16'(A_180,B_181,k1_funct_2(A_180,B_181),D_182))
      | ~ r2_hidden(D_182,k1_funct_2(A_180,B_181)) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_437,plain,
    ( v1_relat_1('#skF_19')
    | ~ r2_hidden('#skF_19',k1_funct_2('#skF_17','#skF_18')) ),
    inference(superposition,[status(thm),theory(equality)],[c_342,c_434])).

tff(c_439,plain,(
    v1_relat_1('#skF_19') ),
    inference(demodulation,[status(thm),theory(equality)],[c_106,c_437])).

tff(c_10,plain,(
    ! [B_6] : r1_tarski(B_6,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_658,plain,(
    ! [A_210,B_211,D_212] :
      ( k1_relat_1('#skF_16'(A_210,B_211,k1_funct_2(A_210,B_211),D_212)) = A_210
      | ~ r2_hidden(D_212,k1_funct_2(A_210,B_211)) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_691,plain,
    ( k1_relat_1('#skF_19') = '#skF_17'
    | ~ r2_hidden('#skF_19',k1_funct_2('#skF_17','#skF_18')) ),
    inference(superposition,[status(thm),theory(equality)],[c_342,c_658])).

tff(c_695,plain,(
    k1_relat_1('#skF_19') = '#skF_17' ),
    inference(demodulation,[status(thm),theory(equality)],[c_106,c_691])).

tff(c_741,plain,(
    ! [A_213,B_214,D_215] :
      ( r1_tarski(k2_relat_1('#skF_16'(A_213,B_214,k1_funct_2(A_213,B_214),D_215)),B_214)
      | ~ r2_hidden(D_215,k1_funct_2(A_213,B_214)) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_746,plain,
    ( r1_tarski(k2_relat_1('#skF_19'),'#skF_18')
    | ~ r2_hidden('#skF_19',k1_funct_2('#skF_17','#skF_18')) ),
    inference(superposition,[status(thm),theory(equality)],[c_342,c_741])).

tff(c_749,plain,(
    r1_tarski(k2_relat_1('#skF_19'),'#skF_18') ),
    inference(demodulation,[status(thm),theory(equality)],[c_106,c_746])).

tff(c_1488,plain,(
    ! [C_276,A_277,B_278] :
      ( m1_subset_1(C_276,k1_zfmisc_1(k2_zfmisc_1(A_277,B_278)))
      | ~ r1_tarski(k2_relat_1(C_276),B_278)
      | ~ r1_tarski(k1_relat_1(C_276),A_277)
      | ~ v1_relat_1(C_276) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_104,plain,
    ( ~ m1_subset_1('#skF_19',k1_zfmisc_1(k2_zfmisc_1('#skF_17','#skF_18')))
    | ~ v1_funct_2('#skF_19','#skF_17','#skF_18')
    | ~ v1_funct_1('#skF_19') ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_133,plain,(
    ~ v1_funct_1('#skF_19') ),
    inference(splitLeft,[status(thm)],[c_104])).

tff(c_183,plain,(
    ! [A_143,B_144,D_145] :
      ( '#skF_16'(A_143,B_144,k1_funct_2(A_143,B_144),D_145) = D_145
      | ~ r2_hidden(D_145,k1_funct_2(A_143,B_144)) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_202,plain,(
    '#skF_16'('#skF_17','#skF_18',k1_funct_2('#skF_17','#skF_18'),'#skF_19') = '#skF_19' ),
    inference(resolution,[status(thm)],[c_106,c_183])).

tff(c_70,plain,(
    ! [A_90,B_91,D_106] :
      ( v1_funct_1('#skF_16'(A_90,B_91,k1_funct_2(A_90,B_91),D_106))
      | ~ r2_hidden(D_106,k1_funct_2(A_90,B_91)) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_239,plain,
    ( v1_funct_1('#skF_19')
    | ~ r2_hidden('#skF_19',k1_funct_2('#skF_17','#skF_18')) ),
    inference(superposition,[status(thm),theory(equality)],[c_202,c_70])).

tff(c_245,plain,(
    v1_funct_1('#skF_19') ),
    inference(demodulation,[status(thm),theory(equality)],[c_106,c_239])).

tff(c_247,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_133,c_245])).

tff(c_248,plain,
    ( ~ v1_funct_2('#skF_19','#skF_17','#skF_18')
    | ~ m1_subset_1('#skF_19',k1_zfmisc_1(k2_zfmisc_1('#skF_17','#skF_18'))) ),
    inference(splitRight,[status(thm)],[c_104])).

tff(c_276,plain,(
    ~ m1_subset_1('#skF_19',k1_zfmisc_1(k2_zfmisc_1('#skF_17','#skF_18'))) ),
    inference(splitLeft,[status(thm)],[c_248])).

tff(c_1497,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_19'),'#skF_18')
    | ~ r1_tarski(k1_relat_1('#skF_19'),'#skF_17')
    | ~ v1_relat_1('#skF_19') ),
    inference(resolution,[status(thm)],[c_1488,c_276])).

tff(c_1503,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_439,c_10,c_695,c_749,c_1497])).

tff(c_1504,plain,(
    ~ v1_funct_2('#skF_19','#skF_17','#skF_18') ),
    inference(splitRight,[status(thm)],[c_248])).

tff(c_249,plain,(
    v1_funct_1('#skF_19') ),
    inference(splitRight,[status(thm)],[c_104])).

tff(c_1505,plain,(
    m1_subset_1('#skF_19',k1_zfmisc_1(k2_zfmisc_1('#skF_17','#skF_18'))) ),
    inference(splitRight,[status(thm)],[c_248])).

tff(c_1506,plain,(
    ! [C_279,A_280,B_281] :
      ( v1_partfun1(C_279,A_280)
      | ~ m1_subset_1(C_279,k1_zfmisc_1(k2_zfmisc_1(A_280,B_281)))
      | ~ v1_xboole_0(A_280) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_1510,plain,
    ( v1_partfun1('#skF_19','#skF_17')
    | ~ v1_xboole_0('#skF_17') ),
    inference(resolution,[status(thm)],[c_1505,c_1506])).

tff(c_1511,plain,(
    ~ v1_xboole_0('#skF_17') ),
    inference(splitLeft,[status(thm)],[c_1510])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_1518,plain,(
    ! [A_284,B_285,D_286] :
      ( '#skF_16'(A_284,B_285,k1_funct_2(A_284,B_285),D_286) = D_286
      | ~ r2_hidden(D_286,k1_funct_2(A_284,B_285)) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_1533,plain,(
    '#skF_16'('#skF_17','#skF_18',k1_funct_2('#skF_17','#skF_18'),'#skF_19') = '#skF_19' ),
    inference(resolution,[status(thm)],[c_106,c_1518])).

tff(c_1587,plain,(
    ! [A_296,B_297,D_298] :
      ( v1_relat_1('#skF_16'(A_296,B_297,k1_funct_2(A_296,B_297),D_298))
      | ~ r2_hidden(D_298,k1_funct_2(A_296,B_297)) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_1590,plain,
    ( v1_relat_1('#skF_19')
    | ~ r2_hidden('#skF_19',k1_funct_2('#skF_17','#skF_18')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1533,c_1587])).

tff(c_1592,plain,(
    v1_relat_1('#skF_19') ),
    inference(demodulation,[status(thm),theory(equality)],[c_106,c_1590])).

tff(c_1634,plain,(
    ! [A_303,B_304,D_305] :
      ( k1_relat_1('#skF_16'(A_303,B_304,k1_funct_2(A_303,B_304),D_305)) = A_303
      | ~ r2_hidden(D_305,k1_funct_2(A_303,B_304)) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_1652,plain,
    ( k1_relat_1('#skF_19') = '#skF_17'
    | ~ r2_hidden('#skF_19',k1_funct_2('#skF_17','#skF_18')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1533,c_1634])).

tff(c_1656,plain,(
    k1_relat_1('#skF_19') = '#skF_17' ),
    inference(demodulation,[status(thm),theory(equality)],[c_106,c_1652])).

tff(c_1773,plain,(
    ! [A_319,D_320] :
      ( r2_hidden(k1_funct_1(A_319,D_320),k2_relat_1(A_319))
      | ~ r2_hidden(D_320,k1_relat_1(A_319))
      | ~ v1_funct_1(A_319)
      | ~ v1_relat_1(A_319) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_1962,plain,(
    ! [A_337,D_338] :
      ( ~ v1_xboole_0(k2_relat_1(A_337))
      | ~ r2_hidden(D_338,k1_relat_1(A_337))
      | ~ v1_funct_1(A_337)
      | ~ v1_relat_1(A_337) ) ),
    inference(resolution,[status(thm)],[c_1773,c_2])).

tff(c_1965,plain,(
    ! [D_338] :
      ( ~ v1_xboole_0(k2_relat_1('#skF_19'))
      | ~ r2_hidden(D_338,'#skF_17')
      | ~ v1_funct_1('#skF_19')
      | ~ v1_relat_1('#skF_19') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1656,c_1962])).

tff(c_1986,plain,(
    ! [D_338] :
      ( ~ v1_xboole_0(k2_relat_1('#skF_19'))
      | ~ r2_hidden(D_338,'#skF_17') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1592,c_249,c_1965])).

tff(c_1991,plain,(
    ~ v1_xboole_0(k2_relat_1('#skF_19')) ),
    inference(splitLeft,[status(thm)],[c_1986])).

tff(c_1935,plain,(
    ! [C_333,A_334,B_335] :
      ( v1_funct_2(C_333,A_334,B_335)
      | ~ v1_partfun1(C_333,A_334)
      | ~ v1_funct_1(C_333)
      | ~ m1_subset_1(C_333,k1_zfmisc_1(k2_zfmisc_1(A_334,B_335))) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_1944,plain,
    ( v1_funct_2('#skF_19','#skF_17','#skF_18')
    | ~ v1_partfun1('#skF_19','#skF_17')
    | ~ v1_funct_1('#skF_19') ),
    inference(resolution,[status(thm)],[c_1505,c_1935])).

tff(c_1951,plain,
    ( v1_funct_2('#skF_19','#skF_17','#skF_18')
    | ~ v1_partfun1('#skF_19','#skF_17') ),
    inference(demodulation,[status(thm),theory(equality)],[c_249,c_1944])).

tff(c_1952,plain,(
    ~ v1_partfun1('#skF_19','#skF_17') ),
    inference(negUnitSimplification,[status(thm)],[c_1504,c_1951])).

tff(c_100,plain,(
    ! [A_110] :
      ( v1_funct_2(A_110,k1_relat_1(A_110),k2_relat_1(A_110))
      | ~ v1_funct_1(A_110)
      | ~ v1_relat_1(A_110) ) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_1666,plain,
    ( v1_funct_2('#skF_19','#skF_17',k2_relat_1('#skF_19'))
    | ~ v1_funct_1('#skF_19')
    | ~ v1_relat_1('#skF_19') ),
    inference(superposition,[status(thm),theory(equality)],[c_1656,c_100])).

tff(c_1674,plain,(
    v1_funct_2('#skF_19','#skF_17',k2_relat_1('#skF_19')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1592,c_249,c_1666])).

tff(c_98,plain,(
    ! [A_110] :
      ( m1_subset_1(A_110,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_110),k2_relat_1(A_110))))
      | ~ v1_funct_1(A_110)
      | ~ v1_relat_1(A_110) ) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_1663,plain,
    ( m1_subset_1('#skF_19',k1_zfmisc_1(k2_zfmisc_1('#skF_17',k2_relat_1('#skF_19'))))
    | ~ v1_funct_1('#skF_19')
    | ~ v1_relat_1('#skF_19') ),
    inference(superposition,[status(thm),theory(equality)],[c_1656,c_98])).

tff(c_1672,plain,(
    m1_subset_1('#skF_19',k1_zfmisc_1(k2_zfmisc_1('#skF_17',k2_relat_1('#skF_19')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1592,c_249,c_1663])).

tff(c_2927,plain,(
    ! [C_412,A_413,B_414] :
      ( v1_partfun1(C_412,A_413)
      | ~ v1_funct_2(C_412,A_413,B_414)
      | ~ v1_funct_1(C_412)
      | ~ m1_subset_1(C_412,k1_zfmisc_1(k2_zfmisc_1(A_413,B_414)))
      | v1_xboole_0(B_414) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_2933,plain,
    ( v1_partfun1('#skF_19','#skF_17')
    | ~ v1_funct_2('#skF_19','#skF_17',k2_relat_1('#skF_19'))
    | ~ v1_funct_1('#skF_19')
    | v1_xboole_0(k2_relat_1('#skF_19')) ),
    inference(resolution,[status(thm)],[c_1672,c_2927])).

tff(c_2943,plain,
    ( v1_partfun1('#skF_19','#skF_17')
    | v1_xboole_0(k2_relat_1('#skF_19')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_249,c_1674,c_2933])).

tff(c_2945,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1991,c_1952,c_2943])).

tff(c_2948,plain,(
    ! [D_415] : ~ r2_hidden(D_415,'#skF_17') ),
    inference(splitRight,[status(thm)],[c_1986])).

tff(c_2964,plain,(
    v1_xboole_0('#skF_17') ),
    inference(resolution,[status(thm)],[c_4,c_2948])).

tff(c_2971,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1511,c_2964])).

tff(c_2972,plain,(
    v1_partfun1('#skF_19','#skF_17') ),
    inference(splitRight,[status(thm)],[c_1510])).

tff(c_3636,plain,(
    ! [C_483,A_484,B_485] :
      ( v1_funct_2(C_483,A_484,B_485)
      | ~ v1_partfun1(C_483,A_484)
      | ~ v1_funct_1(C_483)
      | ~ m1_subset_1(C_483,k1_zfmisc_1(k2_zfmisc_1(A_484,B_485))) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_3645,plain,
    ( v1_funct_2('#skF_19','#skF_17','#skF_18')
    | ~ v1_partfun1('#skF_19','#skF_17')
    | ~ v1_funct_1('#skF_19') ),
    inference(resolution,[status(thm)],[c_1505,c_3636])).

tff(c_3652,plain,(
    v1_funct_2('#skF_19','#skF_17','#skF_18') ),
    inference(demodulation,[status(thm),theory(equality)],[c_249,c_2972,c_3645])).

tff(c_3654,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1504,c_3652])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n007.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:10:06 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.09/1.97  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.09/1.98  
% 5.09/1.98  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.09/1.98  %$ v1_funct_2 > v1_partfun1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k4_tarski > k2_zfmisc_1 > k1_funct_2 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_13 > #skF_6 > #skF_18 > #skF_17 > #skF_1 > #skF_19 > #skF_3 > #skF_10 > #skF_5 > #skF_16 > #skF_8 > #skF_9 > #skF_15 > #skF_14 > #skF_11 > #skF_2 > #skF_12 > #skF_7 > #skF_4
% 5.09/1.98  
% 5.09/1.98  %Foreground sorts:
% 5.09/1.98  
% 5.09/1.98  
% 5.09/1.98  %Background operators:
% 5.09/1.98  
% 5.09/1.98  
% 5.09/1.98  %Foreground operators:
% 5.09/1.98  tff('#skF_13', type, '#skF_13': ($i * $i * $i) > $i).
% 5.09/1.98  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 5.09/1.98  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 5.09/1.98  tff('#skF_18', type, '#skF_18': $i).
% 5.09/1.98  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.09/1.98  tff('#skF_17', type, '#skF_17': $i).
% 5.09/1.98  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.09/1.98  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 5.09/1.98  tff('#skF_1', type, '#skF_1': $i > $i).
% 5.09/1.98  tff('#skF_19', type, '#skF_19': $i).
% 5.09/1.98  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 5.09/1.98  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.09/1.98  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 5.09/1.98  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 5.09/1.98  tff('#skF_10', type, '#skF_10': $i > $i).
% 5.09/1.98  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 5.09/1.98  tff('#skF_16', type, '#skF_16': ($i * $i * $i * $i) > $i).
% 5.09/1.98  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 5.09/1.98  tff('#skF_8', type, '#skF_8': ($i * $i) > $i).
% 5.09/1.98  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.09/1.98  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 5.09/1.98  tff('#skF_9', type, '#skF_9': ($i * $i * $i) > $i).
% 5.09/1.98  tff(k1_funct_2, type, k1_funct_2: ($i * $i) > $i).
% 5.09/1.98  tff('#skF_15', type, '#skF_15': ($i * $i * $i) > $i).
% 5.09/1.98  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.09/1.98  tff('#skF_14', type, '#skF_14': ($i * $i * $i) > $i).
% 5.09/1.98  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.09/1.98  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 5.09/1.98  tff('#skF_11', type, '#skF_11': $i > $i).
% 5.09/1.98  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.09/1.98  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 5.09/1.98  tff('#skF_12', type, '#skF_12': $i > $i).
% 5.09/1.98  tff('#skF_7', type, '#skF_7': ($i * $i) > $i).
% 5.09/1.98  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 5.09/1.98  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 5.09/1.98  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 5.09/1.98  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.09/1.98  
% 5.42/2.00  tff(f_143, negated_conjecture, ~(![A, B, C]: (r2_hidden(C, k1_funct_2(A, B)) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t121_funct_2)).
% 5.42/2.00  tff(f_124, axiom, (![A, B, C]: ((C = k1_funct_2(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (?[E]: ((((v1_relat_1(E) & v1_funct_1(E)) & (D = E)) & (k1_relat_1(E) = A)) & r1_tarski(k2_relat_1(E), B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_funct_2)).
% 5.42/2.00  tff(f_37, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 5.42/2.00  tff(f_77, axiom, (![A, B, C]: (v1_relat_1(C) => ((r1_tarski(k1_relat_1(C), A) & r1_tarski(k2_relat_1(C), B)) => m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_relset_1)).
% 5.42/2.00  tff(f_94, axiom, (![A, B]: (v1_xboole_0(A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_partfun1(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_partfun1)).
% 5.42/2.00  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 5.42/2.00  tff(f_60, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((B = k2_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: (r2_hidden(D, k1_relat_1(A)) & (C = k1_funct_1(A, D)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_funct_1)).
% 5.42/2.00  tff(f_87, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v1_partfun1(C, A)) => (v1_funct_1(C) & v1_funct_2(C, A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_funct_2)).
% 5.42/2.00  tff(f_134, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => ((v1_funct_1(A) & v1_funct_2(A, k1_relat_1(A), k2_relat_1(A))) & m1_subset_1(A, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_funct_2)).
% 5.42/2.00  tff(f_108, axiom, (![A, B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) => (v1_funct_1(C) & v1_partfun1(C, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc5_funct_2)).
% 5.42/2.00  tff(c_106, plain, (r2_hidden('#skF_19', k1_funct_2('#skF_17', '#skF_18'))), inference(cnfTransformation, [status(thm)], [f_143])).
% 5.42/2.00  tff(c_323, plain, (![A_169, B_170, D_171]: ('#skF_16'(A_169, B_170, k1_funct_2(A_169, B_170), D_171)=D_171 | ~r2_hidden(D_171, k1_funct_2(A_169, B_170)))), inference(cnfTransformation, [status(thm)], [f_124])).
% 5.42/2.00  tff(c_342, plain, ('#skF_16'('#skF_17', '#skF_18', k1_funct_2('#skF_17', '#skF_18'), '#skF_19')='#skF_19'), inference(resolution, [status(thm)], [c_106, c_323])).
% 5.42/2.00  tff(c_434, plain, (![A_180, B_181, D_182]: (v1_relat_1('#skF_16'(A_180, B_181, k1_funct_2(A_180, B_181), D_182)) | ~r2_hidden(D_182, k1_funct_2(A_180, B_181)))), inference(cnfTransformation, [status(thm)], [f_124])).
% 5.42/2.00  tff(c_437, plain, (v1_relat_1('#skF_19') | ~r2_hidden('#skF_19', k1_funct_2('#skF_17', '#skF_18'))), inference(superposition, [status(thm), theory('equality')], [c_342, c_434])).
% 5.42/2.00  tff(c_439, plain, (v1_relat_1('#skF_19')), inference(demodulation, [status(thm), theory('equality')], [c_106, c_437])).
% 5.42/2.00  tff(c_10, plain, (![B_6]: (r1_tarski(B_6, B_6))), inference(cnfTransformation, [status(thm)], [f_37])).
% 5.42/2.00  tff(c_658, plain, (![A_210, B_211, D_212]: (k1_relat_1('#skF_16'(A_210, B_211, k1_funct_2(A_210, B_211), D_212))=A_210 | ~r2_hidden(D_212, k1_funct_2(A_210, B_211)))), inference(cnfTransformation, [status(thm)], [f_124])).
% 5.42/2.00  tff(c_691, plain, (k1_relat_1('#skF_19')='#skF_17' | ~r2_hidden('#skF_19', k1_funct_2('#skF_17', '#skF_18'))), inference(superposition, [status(thm), theory('equality')], [c_342, c_658])).
% 5.42/2.00  tff(c_695, plain, (k1_relat_1('#skF_19')='#skF_17'), inference(demodulation, [status(thm), theory('equality')], [c_106, c_691])).
% 5.42/2.00  tff(c_741, plain, (![A_213, B_214, D_215]: (r1_tarski(k2_relat_1('#skF_16'(A_213, B_214, k1_funct_2(A_213, B_214), D_215)), B_214) | ~r2_hidden(D_215, k1_funct_2(A_213, B_214)))), inference(cnfTransformation, [status(thm)], [f_124])).
% 5.42/2.00  tff(c_746, plain, (r1_tarski(k2_relat_1('#skF_19'), '#skF_18') | ~r2_hidden('#skF_19', k1_funct_2('#skF_17', '#skF_18'))), inference(superposition, [status(thm), theory('equality')], [c_342, c_741])).
% 5.42/2.00  tff(c_749, plain, (r1_tarski(k2_relat_1('#skF_19'), '#skF_18')), inference(demodulation, [status(thm), theory('equality')], [c_106, c_746])).
% 5.42/2.00  tff(c_1488, plain, (![C_276, A_277, B_278]: (m1_subset_1(C_276, k1_zfmisc_1(k2_zfmisc_1(A_277, B_278))) | ~r1_tarski(k2_relat_1(C_276), B_278) | ~r1_tarski(k1_relat_1(C_276), A_277) | ~v1_relat_1(C_276))), inference(cnfTransformation, [status(thm)], [f_77])).
% 5.42/2.00  tff(c_104, plain, (~m1_subset_1('#skF_19', k1_zfmisc_1(k2_zfmisc_1('#skF_17', '#skF_18'))) | ~v1_funct_2('#skF_19', '#skF_17', '#skF_18') | ~v1_funct_1('#skF_19')), inference(cnfTransformation, [status(thm)], [f_143])).
% 5.42/2.00  tff(c_133, plain, (~v1_funct_1('#skF_19')), inference(splitLeft, [status(thm)], [c_104])).
% 5.42/2.00  tff(c_183, plain, (![A_143, B_144, D_145]: ('#skF_16'(A_143, B_144, k1_funct_2(A_143, B_144), D_145)=D_145 | ~r2_hidden(D_145, k1_funct_2(A_143, B_144)))), inference(cnfTransformation, [status(thm)], [f_124])).
% 5.42/2.00  tff(c_202, plain, ('#skF_16'('#skF_17', '#skF_18', k1_funct_2('#skF_17', '#skF_18'), '#skF_19')='#skF_19'), inference(resolution, [status(thm)], [c_106, c_183])).
% 5.42/2.00  tff(c_70, plain, (![A_90, B_91, D_106]: (v1_funct_1('#skF_16'(A_90, B_91, k1_funct_2(A_90, B_91), D_106)) | ~r2_hidden(D_106, k1_funct_2(A_90, B_91)))), inference(cnfTransformation, [status(thm)], [f_124])).
% 5.42/2.00  tff(c_239, plain, (v1_funct_1('#skF_19') | ~r2_hidden('#skF_19', k1_funct_2('#skF_17', '#skF_18'))), inference(superposition, [status(thm), theory('equality')], [c_202, c_70])).
% 5.42/2.00  tff(c_245, plain, (v1_funct_1('#skF_19')), inference(demodulation, [status(thm), theory('equality')], [c_106, c_239])).
% 5.42/2.00  tff(c_247, plain, $false, inference(negUnitSimplification, [status(thm)], [c_133, c_245])).
% 5.42/2.00  tff(c_248, plain, (~v1_funct_2('#skF_19', '#skF_17', '#skF_18') | ~m1_subset_1('#skF_19', k1_zfmisc_1(k2_zfmisc_1('#skF_17', '#skF_18')))), inference(splitRight, [status(thm)], [c_104])).
% 5.42/2.00  tff(c_276, plain, (~m1_subset_1('#skF_19', k1_zfmisc_1(k2_zfmisc_1('#skF_17', '#skF_18')))), inference(splitLeft, [status(thm)], [c_248])).
% 5.42/2.00  tff(c_1497, plain, (~r1_tarski(k2_relat_1('#skF_19'), '#skF_18') | ~r1_tarski(k1_relat_1('#skF_19'), '#skF_17') | ~v1_relat_1('#skF_19')), inference(resolution, [status(thm)], [c_1488, c_276])).
% 5.42/2.00  tff(c_1503, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_439, c_10, c_695, c_749, c_1497])).
% 5.42/2.00  tff(c_1504, plain, (~v1_funct_2('#skF_19', '#skF_17', '#skF_18')), inference(splitRight, [status(thm)], [c_248])).
% 5.42/2.00  tff(c_249, plain, (v1_funct_1('#skF_19')), inference(splitRight, [status(thm)], [c_104])).
% 5.42/2.00  tff(c_1505, plain, (m1_subset_1('#skF_19', k1_zfmisc_1(k2_zfmisc_1('#skF_17', '#skF_18')))), inference(splitRight, [status(thm)], [c_248])).
% 5.42/2.00  tff(c_1506, plain, (![C_279, A_280, B_281]: (v1_partfun1(C_279, A_280) | ~m1_subset_1(C_279, k1_zfmisc_1(k2_zfmisc_1(A_280, B_281))) | ~v1_xboole_0(A_280))), inference(cnfTransformation, [status(thm)], [f_94])).
% 5.42/2.00  tff(c_1510, plain, (v1_partfun1('#skF_19', '#skF_17') | ~v1_xboole_0('#skF_17')), inference(resolution, [status(thm)], [c_1505, c_1506])).
% 5.42/2.00  tff(c_1511, plain, (~v1_xboole_0('#skF_17')), inference(splitLeft, [status(thm)], [c_1510])).
% 5.42/2.00  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.42/2.00  tff(c_1518, plain, (![A_284, B_285, D_286]: ('#skF_16'(A_284, B_285, k1_funct_2(A_284, B_285), D_286)=D_286 | ~r2_hidden(D_286, k1_funct_2(A_284, B_285)))), inference(cnfTransformation, [status(thm)], [f_124])).
% 5.42/2.00  tff(c_1533, plain, ('#skF_16'('#skF_17', '#skF_18', k1_funct_2('#skF_17', '#skF_18'), '#skF_19')='#skF_19'), inference(resolution, [status(thm)], [c_106, c_1518])).
% 5.42/2.00  tff(c_1587, plain, (![A_296, B_297, D_298]: (v1_relat_1('#skF_16'(A_296, B_297, k1_funct_2(A_296, B_297), D_298)) | ~r2_hidden(D_298, k1_funct_2(A_296, B_297)))), inference(cnfTransformation, [status(thm)], [f_124])).
% 5.42/2.00  tff(c_1590, plain, (v1_relat_1('#skF_19') | ~r2_hidden('#skF_19', k1_funct_2('#skF_17', '#skF_18'))), inference(superposition, [status(thm), theory('equality')], [c_1533, c_1587])).
% 5.42/2.00  tff(c_1592, plain, (v1_relat_1('#skF_19')), inference(demodulation, [status(thm), theory('equality')], [c_106, c_1590])).
% 5.42/2.00  tff(c_1634, plain, (![A_303, B_304, D_305]: (k1_relat_1('#skF_16'(A_303, B_304, k1_funct_2(A_303, B_304), D_305))=A_303 | ~r2_hidden(D_305, k1_funct_2(A_303, B_304)))), inference(cnfTransformation, [status(thm)], [f_124])).
% 5.42/2.00  tff(c_1652, plain, (k1_relat_1('#skF_19')='#skF_17' | ~r2_hidden('#skF_19', k1_funct_2('#skF_17', '#skF_18'))), inference(superposition, [status(thm), theory('equality')], [c_1533, c_1634])).
% 5.42/2.00  tff(c_1656, plain, (k1_relat_1('#skF_19')='#skF_17'), inference(demodulation, [status(thm), theory('equality')], [c_106, c_1652])).
% 5.42/2.00  tff(c_1773, plain, (![A_319, D_320]: (r2_hidden(k1_funct_1(A_319, D_320), k2_relat_1(A_319)) | ~r2_hidden(D_320, k1_relat_1(A_319)) | ~v1_funct_1(A_319) | ~v1_relat_1(A_319))), inference(cnfTransformation, [status(thm)], [f_60])).
% 5.42/2.00  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.42/2.00  tff(c_1962, plain, (![A_337, D_338]: (~v1_xboole_0(k2_relat_1(A_337)) | ~r2_hidden(D_338, k1_relat_1(A_337)) | ~v1_funct_1(A_337) | ~v1_relat_1(A_337))), inference(resolution, [status(thm)], [c_1773, c_2])).
% 5.42/2.00  tff(c_1965, plain, (![D_338]: (~v1_xboole_0(k2_relat_1('#skF_19')) | ~r2_hidden(D_338, '#skF_17') | ~v1_funct_1('#skF_19') | ~v1_relat_1('#skF_19'))), inference(superposition, [status(thm), theory('equality')], [c_1656, c_1962])).
% 5.42/2.00  tff(c_1986, plain, (![D_338]: (~v1_xboole_0(k2_relat_1('#skF_19')) | ~r2_hidden(D_338, '#skF_17'))), inference(demodulation, [status(thm), theory('equality')], [c_1592, c_249, c_1965])).
% 5.42/2.00  tff(c_1991, plain, (~v1_xboole_0(k2_relat_1('#skF_19'))), inference(splitLeft, [status(thm)], [c_1986])).
% 5.42/2.00  tff(c_1935, plain, (![C_333, A_334, B_335]: (v1_funct_2(C_333, A_334, B_335) | ~v1_partfun1(C_333, A_334) | ~v1_funct_1(C_333) | ~m1_subset_1(C_333, k1_zfmisc_1(k2_zfmisc_1(A_334, B_335))))), inference(cnfTransformation, [status(thm)], [f_87])).
% 5.42/2.00  tff(c_1944, plain, (v1_funct_2('#skF_19', '#skF_17', '#skF_18') | ~v1_partfun1('#skF_19', '#skF_17') | ~v1_funct_1('#skF_19')), inference(resolution, [status(thm)], [c_1505, c_1935])).
% 5.42/2.00  tff(c_1951, plain, (v1_funct_2('#skF_19', '#skF_17', '#skF_18') | ~v1_partfun1('#skF_19', '#skF_17')), inference(demodulation, [status(thm), theory('equality')], [c_249, c_1944])).
% 5.42/2.00  tff(c_1952, plain, (~v1_partfun1('#skF_19', '#skF_17')), inference(negUnitSimplification, [status(thm)], [c_1504, c_1951])).
% 5.42/2.00  tff(c_100, plain, (![A_110]: (v1_funct_2(A_110, k1_relat_1(A_110), k2_relat_1(A_110)) | ~v1_funct_1(A_110) | ~v1_relat_1(A_110))), inference(cnfTransformation, [status(thm)], [f_134])).
% 5.42/2.00  tff(c_1666, plain, (v1_funct_2('#skF_19', '#skF_17', k2_relat_1('#skF_19')) | ~v1_funct_1('#skF_19') | ~v1_relat_1('#skF_19')), inference(superposition, [status(thm), theory('equality')], [c_1656, c_100])).
% 5.42/2.00  tff(c_1674, plain, (v1_funct_2('#skF_19', '#skF_17', k2_relat_1('#skF_19'))), inference(demodulation, [status(thm), theory('equality')], [c_1592, c_249, c_1666])).
% 5.42/2.00  tff(c_98, plain, (![A_110]: (m1_subset_1(A_110, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_110), k2_relat_1(A_110)))) | ~v1_funct_1(A_110) | ~v1_relat_1(A_110))), inference(cnfTransformation, [status(thm)], [f_134])).
% 5.42/2.00  tff(c_1663, plain, (m1_subset_1('#skF_19', k1_zfmisc_1(k2_zfmisc_1('#skF_17', k2_relat_1('#skF_19')))) | ~v1_funct_1('#skF_19') | ~v1_relat_1('#skF_19')), inference(superposition, [status(thm), theory('equality')], [c_1656, c_98])).
% 5.42/2.00  tff(c_1672, plain, (m1_subset_1('#skF_19', k1_zfmisc_1(k2_zfmisc_1('#skF_17', k2_relat_1('#skF_19'))))), inference(demodulation, [status(thm), theory('equality')], [c_1592, c_249, c_1663])).
% 5.42/2.00  tff(c_2927, plain, (![C_412, A_413, B_414]: (v1_partfun1(C_412, A_413) | ~v1_funct_2(C_412, A_413, B_414) | ~v1_funct_1(C_412) | ~m1_subset_1(C_412, k1_zfmisc_1(k2_zfmisc_1(A_413, B_414))) | v1_xboole_0(B_414))), inference(cnfTransformation, [status(thm)], [f_108])).
% 5.42/2.00  tff(c_2933, plain, (v1_partfun1('#skF_19', '#skF_17') | ~v1_funct_2('#skF_19', '#skF_17', k2_relat_1('#skF_19')) | ~v1_funct_1('#skF_19') | v1_xboole_0(k2_relat_1('#skF_19'))), inference(resolution, [status(thm)], [c_1672, c_2927])).
% 5.42/2.00  tff(c_2943, plain, (v1_partfun1('#skF_19', '#skF_17') | v1_xboole_0(k2_relat_1('#skF_19'))), inference(demodulation, [status(thm), theory('equality')], [c_249, c_1674, c_2933])).
% 5.42/2.00  tff(c_2945, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1991, c_1952, c_2943])).
% 5.42/2.00  tff(c_2948, plain, (![D_415]: (~r2_hidden(D_415, '#skF_17'))), inference(splitRight, [status(thm)], [c_1986])).
% 5.42/2.00  tff(c_2964, plain, (v1_xboole_0('#skF_17')), inference(resolution, [status(thm)], [c_4, c_2948])).
% 5.42/2.00  tff(c_2971, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1511, c_2964])).
% 5.42/2.00  tff(c_2972, plain, (v1_partfun1('#skF_19', '#skF_17')), inference(splitRight, [status(thm)], [c_1510])).
% 5.42/2.00  tff(c_3636, plain, (![C_483, A_484, B_485]: (v1_funct_2(C_483, A_484, B_485) | ~v1_partfun1(C_483, A_484) | ~v1_funct_1(C_483) | ~m1_subset_1(C_483, k1_zfmisc_1(k2_zfmisc_1(A_484, B_485))))), inference(cnfTransformation, [status(thm)], [f_87])).
% 5.42/2.00  tff(c_3645, plain, (v1_funct_2('#skF_19', '#skF_17', '#skF_18') | ~v1_partfun1('#skF_19', '#skF_17') | ~v1_funct_1('#skF_19')), inference(resolution, [status(thm)], [c_1505, c_3636])).
% 5.42/2.00  tff(c_3652, plain, (v1_funct_2('#skF_19', '#skF_17', '#skF_18')), inference(demodulation, [status(thm), theory('equality')], [c_249, c_2972, c_3645])).
% 5.42/2.00  tff(c_3654, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1504, c_3652])).
% 5.42/2.00  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.42/2.00  
% 5.42/2.00  Inference rules
% 5.42/2.00  ----------------------
% 5.42/2.00  #Ref     : 0
% 5.42/2.00  #Sup     : 766
% 5.42/2.00  #Fact    : 0
% 5.42/2.00  #Define  : 0
% 5.42/2.00  #Split   : 12
% 5.42/2.00  #Chain   : 0
% 5.42/2.00  #Close   : 0
% 5.42/2.00  
% 5.42/2.00  Ordering : KBO
% 5.42/2.00  
% 5.42/2.00  Simplification rules
% 5.42/2.00  ----------------------
% 5.42/2.00  #Subsume      : 209
% 5.42/2.00  #Demod        : 157
% 5.42/2.00  #Tautology    : 77
% 5.42/2.00  #SimpNegUnit  : 6
% 5.42/2.00  #BackRed      : 0
% 5.42/2.00  
% 5.42/2.00  #Partial instantiations: 0
% 5.42/2.00  #Strategies tried      : 1
% 5.42/2.00  
% 5.42/2.00  Timing (in seconds)
% 5.42/2.00  ----------------------
% 5.42/2.00  Preprocessing        : 0.37
% 5.42/2.00  Parsing              : 0.18
% 5.42/2.00  CNF conversion       : 0.04
% 5.42/2.00  Main loop            : 0.83
% 5.42/2.00  Inferencing          : 0.31
% 5.42/2.00  Reduction            : 0.20
% 5.42/2.00  Demodulation         : 0.13
% 5.42/2.00  BG Simplification    : 0.04
% 5.42/2.00  Subsumption          : 0.22
% 5.42/2.00  Abstraction          : 0.04
% 5.42/2.00  MUC search           : 0.00
% 5.42/2.00  Cooper               : 0.00
% 5.42/2.00  Total                : 1.24
% 5.42/2.00  Index Insertion      : 0.00
% 5.42/2.00  Index Deletion       : 0.00
% 5.42/2.00  Index Matching       : 0.00
% 5.42/2.00  BG Taut test         : 0.00
%------------------------------------------------------------------------------
