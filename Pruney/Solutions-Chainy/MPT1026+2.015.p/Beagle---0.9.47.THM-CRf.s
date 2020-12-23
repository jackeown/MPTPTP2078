%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:16:41 EST 2020

% Result     : Theorem 17.05s
% Output     : CNFRefutation 17.34s
% Verified   : 
% Statistics : Number of formulae       :  259 (4393 expanded)
%              Number of leaves         :   53 (1220 expanded)
%              Depth                    :   20
%              Number of atoms          :  422 (10252 expanded)
%              Number of equality atoms :  103 (3854 expanded)
%              Maximal formula depth    :   12 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v1_partfun1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_zfmisc_1 > k1_funct_2 > k1_funct_1 > #nlpp > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_6 > #skF_4 > #skF_15 > #skF_1 > #skF_12 > #skF_14 > #skF_13 > #skF_11 > #skF_9 > #skF_3 > #skF_2 > #skF_8 > #skF_7 > #skF_5 > #skF_10

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_15',type,(
    '#skF_15': $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_12',type,(
    '#skF_12': ( $i * $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_14',type,(
    '#skF_14': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_13',type,(
    '#skF_13': $i )).

tff(v1_partfun1,type,(
    v1_partfun1: ( $i * $i ) > $o )).

tff('#skF_11',type,(
    '#skF_11': ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': ( $i * $i * $i ) > $i )).

tff(k6_partfun1,type,(
    k6_partfun1: $i > $i )).

tff(k1_funct_2,type,(
    k1_funct_2: ( $i * $i ) > $i )).

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

tff('#skF_8',type,(
    '#skF_8': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_10',type,(
    '#skF_10': ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_185,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r2_hidden(C,k1_funct_2(A,B))
       => ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t121_funct_2)).

tff(f_162,axiom,(
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

tff(f_39,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_86,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => r1_tarski(A,k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_relat_1)).

tff(f_75,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_114,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(B,A)))
         => v1_xboole_0(C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc4_relset_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_122,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( ( r1_tarski(k1_relat_1(C),A)
          & r1_tarski(k2_relat_1(C),B) )
       => m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_relset_1)).

tff(f_132,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( ( v1_funct_1(C)
          & v1_partfun1(C,A) )
       => ( v1_funct_1(C)
          & v1_funct_2(C,A,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_funct_2)).

tff(f_176,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_funct_1(A)
        & v1_funct_2(A,k1_relat_1(A),k2_relat_1(A))
        & m1_subset_1(A,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A)))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_funct_2)).

tff(f_146,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => ( ( v1_funct_1(C)
              & v1_funct_2(C,A,B) )
           => ( v1_funct_1(C)
              & v1_partfun1(C,A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc5_funct_2)).

tff(f_47,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_92,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( k1_relat_1(A) = k1_xboole_0
      <=> k2_relat_1(A) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_relat_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_82,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

tff(f_62,axiom,(
    ! [A,B] : ~ r2_hidden(A,k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_zfmisc_1)).

tff(f_166,axiom,(
    ! [A] :
      ( v1_partfun1(k6_partfun1(A),A)
      & m1_subset_1(k6_partfun1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).

tff(c_124,plain,(
    r2_hidden('#skF_15',k1_funct_2('#skF_13','#skF_14')) ),
    inference(cnfTransformation,[status(thm)],[f_185])).

tff(c_7791,plain,(
    ! [A_554,B_555,D_556] :
      ( '#skF_12'(A_554,B_555,k1_funct_2(A_554,B_555),D_556) = D_556
      | ~ r2_hidden(D_556,k1_funct_2(A_554,B_555)) ) ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_7814,plain,(
    '#skF_12'('#skF_13','#skF_14',k1_funct_2('#skF_13','#skF_14'),'#skF_15') = '#skF_15' ),
    inference(resolution,[status(thm)],[c_124,c_7791])).

tff(c_86,plain,(
    ! [A_83,B_84,D_99] :
      ( v1_relat_1('#skF_12'(A_83,B_84,k1_funct_2(A_83,B_84),D_99))
      | ~ r2_hidden(D_99,k1_funct_2(A_83,B_84)) ) ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_7927,plain,
    ( v1_relat_1('#skF_15')
    | ~ r2_hidden('#skF_15',k1_funct_2('#skF_13','#skF_14')) ),
    inference(superposition,[status(thm),theory(equality)],[c_7814,c_86])).

tff(c_7933,plain,(
    v1_relat_1('#skF_15') ),
    inference(demodulation,[status(thm),theory(equality)],[c_124,c_7927])).

tff(c_122,plain,
    ( ~ m1_subset_1('#skF_15',k1_zfmisc_1(k2_zfmisc_1('#skF_13','#skF_14')))
    | ~ v1_funct_2('#skF_15','#skF_13','#skF_14')
    | ~ v1_funct_1('#skF_15') ),
    inference(cnfTransformation,[status(thm)],[f_185])).

tff(c_156,plain,(
    ~ v1_funct_1('#skF_15') ),
    inference(splitLeft,[status(thm)],[c_122])).

tff(c_1166,plain,(
    ! [A_209,B_210,D_211] :
      ( '#skF_12'(A_209,B_210,k1_funct_2(A_209,B_210),D_211) = D_211
      | ~ r2_hidden(D_211,k1_funct_2(A_209,B_210)) ) ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_1185,plain,(
    '#skF_12'('#skF_13','#skF_14',k1_funct_2('#skF_13','#skF_14'),'#skF_15') = '#skF_15' ),
    inference(resolution,[status(thm)],[c_124,c_1166])).

tff(c_84,plain,(
    ! [A_83,B_84,D_99] :
      ( v1_funct_1('#skF_12'(A_83,B_84,k1_funct_2(A_83,B_84),D_99))
      | ~ r2_hidden(D_99,k1_funct_2(A_83,B_84)) ) ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_1192,plain,
    ( v1_funct_1('#skF_15')
    | ~ r2_hidden('#skF_15',k1_funct_2('#skF_13','#skF_14')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1185,c_84])).

tff(c_1198,plain,(
    v1_funct_1('#skF_15') ),
    inference(demodulation,[status(thm),theory(equality)],[c_124,c_1192])).

tff(c_1200,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_156,c_1198])).

tff(c_1202,plain,(
    v1_funct_1('#skF_15') ),
    inference(splitRight,[status(thm)],[c_122])).

tff(c_12,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_8341,plain,(
    ! [A_580,B_581,D_582] :
      ( k1_relat_1('#skF_12'(A_580,B_581,k1_funct_2(A_580,B_581),D_582)) = A_580
      | ~ r2_hidden(D_582,k1_funct_2(A_580,B_581)) ) ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_8362,plain,
    ( k1_relat_1('#skF_15') = '#skF_13'
    | ~ r2_hidden('#skF_15',k1_funct_2('#skF_13','#skF_14')) ),
    inference(superposition,[status(thm),theory(equality)],[c_7814,c_8341])).

tff(c_8366,plain,(
    k1_relat_1('#skF_15') = '#skF_13' ),
    inference(demodulation,[status(thm),theory(equality)],[c_124,c_8362])).

tff(c_40,plain,(
    ! [A_27] :
      ( r1_tarski(A_27,k2_zfmisc_1(k1_relat_1(A_27),k2_relat_1(A_27)))
      | ~ v1_relat_1(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_8380,plain,
    ( r1_tarski('#skF_15',k2_zfmisc_1('#skF_13',k2_relat_1('#skF_15')))
    | ~ v1_relat_1('#skF_15') ),
    inference(superposition,[status(thm),theory(equality)],[c_8366,c_40])).

tff(c_8390,plain,(
    r1_tarski('#skF_15',k2_zfmisc_1('#skF_13',k2_relat_1('#skF_15'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7933,c_8380])).

tff(c_36,plain,(
    ! [A_22,B_23] :
      ( m1_subset_1(A_22,k1_zfmisc_1(B_23))
      | ~ r1_tarski(A_22,B_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_7236,plain,(
    ! [C_512,B_513,A_514] :
      ( v1_xboole_0(C_512)
      | ~ m1_subset_1(C_512,k1_zfmisc_1(k2_zfmisc_1(B_513,A_514)))
      | ~ v1_xboole_0(A_514) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_7270,plain,(
    ! [A_22,A_514,B_513] :
      ( v1_xboole_0(A_22)
      | ~ v1_xboole_0(A_514)
      | ~ r1_tarski(A_22,k2_zfmisc_1(B_513,A_514)) ) ),
    inference(resolution,[status(thm)],[c_36,c_7236])).

tff(c_8408,plain,
    ( v1_xboole_0('#skF_15')
    | ~ v1_xboole_0(k2_relat_1('#skF_15')) ),
    inference(resolution,[status(thm)],[c_8390,c_7270])).

tff(c_8414,plain,(
    ~ v1_xboole_0(k2_relat_1('#skF_15')) ),
    inference(splitLeft,[status(thm)],[c_8408])).

tff(c_2197,plain,(
    ! [A_304,B_305,D_306] :
      ( '#skF_12'(A_304,B_305,k1_funct_2(A_304,B_305),D_306) = D_306
      | ~ r2_hidden(D_306,k1_funct_2(A_304,B_305)) ) ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_2216,plain,(
    '#skF_12'('#skF_13','#skF_14',k1_funct_2('#skF_13','#skF_14'),'#skF_15') = '#skF_15' ),
    inference(resolution,[status(thm)],[c_124,c_2197])).

tff(c_2294,plain,(
    ! [A_314,B_315,D_316] :
      ( v1_relat_1('#skF_12'(A_314,B_315,k1_funct_2(A_314,B_315),D_316))
      | ~ r2_hidden(D_316,k1_funct_2(A_314,B_315)) ) ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_2303,plain,
    ( v1_relat_1('#skF_15')
    | ~ r2_hidden('#skF_15',k1_funct_2('#skF_13','#skF_14')) ),
    inference(superposition,[status(thm),theory(equality)],[c_2216,c_2294])).

tff(c_2307,plain,(
    v1_relat_1('#skF_15') ),
    inference(demodulation,[status(thm),theory(equality)],[c_124,c_2303])).

tff(c_20,plain,(
    ! [B_13] : r1_tarski(B_13,B_13) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_2462,plain,(
    ! [A_325,B_326,D_327] :
      ( k1_relat_1('#skF_12'(A_325,B_326,k1_funct_2(A_325,B_326),D_327)) = A_325
      | ~ r2_hidden(D_327,k1_funct_2(A_325,B_326)) ) ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_2480,plain,
    ( k1_relat_1('#skF_15') = '#skF_13'
    | ~ r2_hidden('#skF_15',k1_funct_2('#skF_13','#skF_14')) ),
    inference(superposition,[status(thm),theory(equality)],[c_2216,c_2462])).

tff(c_2484,plain,(
    k1_relat_1('#skF_15') = '#skF_13' ),
    inference(demodulation,[status(thm),theory(equality)],[c_124,c_2480])).

tff(c_3395,plain,(
    ! [A_356,B_357,D_358] :
      ( r1_tarski(k2_relat_1('#skF_12'(A_356,B_357,k1_funct_2(A_356,B_357),D_358)),B_357)
      | ~ r2_hidden(D_358,k1_funct_2(A_356,B_357)) ) ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_3423,plain,
    ( r1_tarski(k2_relat_1('#skF_15'),'#skF_14')
    | ~ r2_hidden('#skF_15',k1_funct_2('#skF_13','#skF_14')) ),
    inference(superposition,[status(thm),theory(equality)],[c_2216,c_3395])).

tff(c_3433,plain,(
    r1_tarski(k2_relat_1('#skF_15'),'#skF_14') ),
    inference(demodulation,[status(thm),theory(equality)],[c_124,c_3423])).

tff(c_6557,plain,(
    ! [C_446,A_447,B_448] :
      ( m1_subset_1(C_446,k1_zfmisc_1(k2_zfmisc_1(A_447,B_448)))
      | ~ r1_tarski(k2_relat_1(C_446),B_448)
      | ~ r1_tarski(k1_relat_1(C_446),A_447)
      | ~ v1_relat_1(C_446) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_1201,plain,
    ( ~ v1_funct_2('#skF_15','#skF_13','#skF_14')
    | ~ m1_subset_1('#skF_15',k1_zfmisc_1(k2_zfmisc_1('#skF_13','#skF_14'))) ),
    inference(splitRight,[status(thm)],[c_122])).

tff(c_1240,plain,(
    ~ m1_subset_1('#skF_15',k1_zfmisc_1(k2_zfmisc_1('#skF_13','#skF_14'))) ),
    inference(splitLeft,[status(thm)],[c_1201])).

tff(c_6571,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_15'),'#skF_14')
    | ~ r1_tarski(k1_relat_1('#skF_15'),'#skF_13')
    | ~ v1_relat_1('#skF_15') ),
    inference(resolution,[status(thm)],[c_6557,c_1240])).

tff(c_6597,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2307,c_20,c_2484,c_3433,c_6571])).

tff(c_6598,plain,(
    ~ v1_funct_2('#skF_15','#skF_13','#skF_14') ),
    inference(splitRight,[status(thm)],[c_1201])).

tff(c_6599,plain,(
    m1_subset_1('#skF_15',k1_zfmisc_1(k2_zfmisc_1('#skF_13','#skF_14'))) ),
    inference(splitRight,[status(thm)],[c_1201])).

tff(c_8694,plain,(
    ! [C_594,A_595,B_596] :
      ( v1_funct_2(C_594,A_595,B_596)
      | ~ v1_partfun1(C_594,A_595)
      | ~ v1_funct_1(C_594)
      | ~ m1_subset_1(C_594,k1_zfmisc_1(k2_zfmisc_1(A_595,B_596))) ) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_8720,plain,
    ( v1_funct_2('#skF_15','#skF_13','#skF_14')
    | ~ v1_partfun1('#skF_15','#skF_13')
    | ~ v1_funct_1('#skF_15') ),
    inference(resolution,[status(thm)],[c_6599,c_8694])).

tff(c_8747,plain,
    ( v1_funct_2('#skF_15','#skF_13','#skF_14')
    | ~ v1_partfun1('#skF_15','#skF_13') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1202,c_8720])).

tff(c_8748,plain,(
    ~ v1_partfun1('#skF_15','#skF_13') ),
    inference(negUnitSimplification,[status(thm)],[c_6598,c_8747])).

tff(c_118,plain,(
    ! [A_104] :
      ( v1_funct_2(A_104,k1_relat_1(A_104),k2_relat_1(A_104))
      | ~ v1_funct_1(A_104)
      | ~ v1_relat_1(A_104) ) ),
    inference(cnfTransformation,[status(thm)],[f_176])).

tff(c_8377,plain,
    ( v1_funct_2('#skF_15','#skF_13',k2_relat_1('#skF_15'))
    | ~ v1_funct_1('#skF_15')
    | ~ v1_relat_1('#skF_15') ),
    inference(superposition,[status(thm),theory(equality)],[c_8366,c_118])).

tff(c_8388,plain,(
    v1_funct_2('#skF_15','#skF_13',k2_relat_1('#skF_15')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7933,c_1202,c_8377])).

tff(c_116,plain,(
    ! [A_104] :
      ( m1_subset_1(A_104,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_104),k2_relat_1(A_104))))
      | ~ v1_funct_1(A_104)
      | ~ v1_relat_1(A_104) ) ),
    inference(cnfTransformation,[status(thm)],[f_176])).

tff(c_8374,plain,
    ( m1_subset_1('#skF_15',k1_zfmisc_1(k2_zfmisc_1('#skF_13',k2_relat_1('#skF_15'))))
    | ~ v1_funct_1('#skF_15')
    | ~ v1_relat_1('#skF_15') ),
    inference(superposition,[status(thm),theory(equality)],[c_8366,c_116])).

tff(c_8386,plain,(
    m1_subset_1('#skF_15',k1_zfmisc_1(k2_zfmisc_1('#skF_13',k2_relat_1('#skF_15')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7933,c_1202,c_8374])).

tff(c_12364,plain,(
    ! [C_691,A_692,B_693] :
      ( v1_partfun1(C_691,A_692)
      | ~ v1_funct_2(C_691,A_692,B_693)
      | ~ v1_funct_1(C_691)
      | ~ m1_subset_1(C_691,k1_zfmisc_1(k2_zfmisc_1(A_692,B_693)))
      | v1_xboole_0(B_693) ) ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_12379,plain,
    ( v1_partfun1('#skF_15','#skF_13')
    | ~ v1_funct_2('#skF_15','#skF_13',k2_relat_1('#skF_15'))
    | ~ v1_funct_1('#skF_15')
    | v1_xboole_0(k2_relat_1('#skF_15')) ),
    inference(resolution,[status(thm)],[c_8386,c_12364])).

tff(c_12420,plain,
    ( v1_partfun1('#skF_15','#skF_13')
    | v1_xboole_0(k2_relat_1('#skF_15')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1202,c_8388,c_12379])).

tff(c_12422,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_8414,c_8748,c_12420])).

tff(c_12423,plain,(
    v1_xboole_0('#skF_15') ),
    inference(splitRight,[status(thm)],[c_8408])).

tff(c_1222,plain,(
    ! [A_216] :
      ( r2_hidden('#skF_3'(A_216),A_216)
      | k1_xboole_0 = A_216 ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_1232,plain,(
    ! [A_216] :
      ( ~ v1_xboole_0(A_216)
      | k1_xboole_0 = A_216 ) ),
    inference(resolution,[status(thm)],[c_1222,c_2])).

tff(c_12447,plain,(
    k1_xboole_0 = '#skF_15' ),
    inference(resolution,[status(thm)],[c_12423,c_1232])).

tff(c_44,plain,(
    ! [A_28] :
      ( k2_relat_1(A_28) = k1_xboole_0
      | k1_relat_1(A_28) != k1_xboole_0
      | ~ v1_relat_1(A_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_7941,plain,
    ( k2_relat_1('#skF_15') = k1_xboole_0
    | k1_relat_1('#skF_15') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_7933,c_44])).

tff(c_7943,plain,(
    k1_relat_1('#skF_15') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_7941])).

tff(c_42,plain,(
    ! [A_28] :
      ( k1_relat_1(A_28) = k1_xboole_0
      | k2_relat_1(A_28) != k1_xboole_0
      | ~ v1_relat_1(A_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_7942,plain,
    ( k1_relat_1('#skF_15') = k1_xboole_0
    | k2_relat_1('#skF_15') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_7933,c_42])).

tff(c_7944,plain,(
    k2_relat_1('#skF_15') != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_7943,c_7942])).

tff(c_12452,plain,(
    k2_relat_1('#skF_15') != '#skF_15' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12447,c_7944])).

tff(c_12424,plain,(
    v1_xboole_0(k2_relat_1('#skF_15')) ),
    inference(splitRight,[status(thm)],[c_8408])).

tff(c_12706,plain,(
    ! [A_703] :
      ( ~ v1_xboole_0(A_703)
      | A_703 = '#skF_15' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12447,c_1232])).

tff(c_12709,plain,(
    k2_relat_1('#skF_15') = '#skF_15' ),
    inference(resolution,[status(thm)],[c_12424,c_12706])).

tff(c_12731,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_12452,c_12709])).

tff(c_12732,plain,(
    k2_relat_1('#skF_15') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_7941])).

tff(c_7478,plain,(
    ! [A_526] :
      ( m1_subset_1(A_526,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_526),k2_relat_1(A_526))))
      | ~ v1_funct_1(A_526)
      | ~ v1_relat_1(A_526) ) ),
    inference(cnfTransformation,[status(thm)],[f_176])).

tff(c_64,plain,(
    ! [C_72,B_70,A_69] :
      ( v1_xboole_0(C_72)
      | ~ m1_subset_1(C_72,k1_zfmisc_1(k2_zfmisc_1(B_70,A_69)))
      | ~ v1_xboole_0(A_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_7487,plain,(
    ! [A_526] :
      ( v1_xboole_0(A_526)
      | ~ v1_xboole_0(k2_relat_1(A_526))
      | ~ v1_funct_1(A_526)
      | ~ v1_relat_1(A_526) ) ),
    inference(resolution,[status(thm)],[c_7478,c_64])).

tff(c_12737,plain,
    ( v1_xboole_0('#skF_15')
    | ~ v1_xboole_0(k1_xboole_0)
    | ~ v1_funct_1('#skF_15')
    | ~ v1_relat_1('#skF_15') ),
    inference(superposition,[status(thm),theory(equality)],[c_12732,c_7487])).

tff(c_12750,plain,(
    v1_xboole_0('#skF_15') ),
    inference(demodulation,[status(thm),theory(equality)],[c_7933,c_1202,c_12,c_12737])).

tff(c_12780,plain,(
    k1_xboole_0 = '#skF_15' ),
    inference(resolution,[status(thm)],[c_12750,c_1232])).

tff(c_12733,plain,(
    k1_relat_1('#skF_15') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_7941])).

tff(c_12839,plain,(
    k1_relat_1('#skF_15') = '#skF_15' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12780,c_12733])).

tff(c_12988,plain,(
    ! [A_708,B_709,D_710] :
      ( k1_relat_1('#skF_12'(A_708,B_709,k1_funct_2(A_708,B_709),D_710)) = A_708
      | ~ r2_hidden(D_710,k1_funct_2(A_708,B_709)) ) ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_13006,plain,
    ( k1_relat_1('#skF_15') = '#skF_13'
    | ~ r2_hidden('#skF_15',k1_funct_2('#skF_13','#skF_14')) ),
    inference(superposition,[status(thm),theory(equality)],[c_7814,c_12988])).

tff(c_13010,plain,(
    '#skF_15' = '#skF_13' ),
    inference(demodulation,[status(thm),theory(equality)],[c_124,c_12839,c_13006])).

tff(c_13018,plain,(
    v1_xboole_0('#skF_13') ),
    inference(demodulation,[status(thm),theory(equality)],[c_13010,c_12750])).

tff(c_26,plain,(
    ! [B_15] : k2_zfmisc_1(k1_xboole_0,B_15) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_12832,plain,(
    ! [B_15] : k2_zfmisc_1('#skF_15',B_15) = '#skF_15' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12780,c_12780,c_26])).

tff(c_13288,plain,(
    ! [B_15] : k2_zfmisc_1('#skF_13',B_15) = '#skF_13' ),
    inference(demodulation,[status(thm),theory(equality)],[c_13010,c_13010,c_12832])).

tff(c_6757,plain,(
    ! [A_468,B_469] :
      ( r2_hidden('#skF_2'(A_468,B_469),A_468)
      | r1_tarski(A_468,B_469) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_6796,plain,(
    ! [A_474,B_475] :
      ( ~ v1_xboole_0(A_474)
      | r1_tarski(A_474,B_475) ) ),
    inference(resolution,[status(thm)],[c_6757,c_2])).

tff(c_6600,plain,(
    ! [A_449,B_450] :
      ( r1_tarski(A_449,B_450)
      | ~ m1_subset_1(A_449,k1_zfmisc_1(B_450)) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_6611,plain,(
    r1_tarski('#skF_15',k2_zfmisc_1('#skF_13','#skF_14')) ),
    inference(resolution,[status(thm)],[c_6599,c_6600])).

tff(c_6647,plain,(
    ! [B_458,A_459] :
      ( B_458 = A_459
      | ~ r1_tarski(B_458,A_459)
      | ~ r1_tarski(A_459,B_458) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_6661,plain,
    ( k2_zfmisc_1('#skF_13','#skF_14') = '#skF_15'
    | ~ r1_tarski(k2_zfmisc_1('#skF_13','#skF_14'),'#skF_15') ),
    inference(resolution,[status(thm)],[c_6611,c_6647])).

tff(c_6729,plain,(
    ~ r1_tarski(k2_zfmisc_1('#skF_13','#skF_14'),'#skF_15') ),
    inference(splitLeft,[status(thm)],[c_6661])).

tff(c_6802,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_13','#skF_14')) ),
    inference(resolution,[status(thm)],[c_6796,c_6729])).

tff(c_13289,plain,(
    ~ v1_xboole_0('#skF_13') ),
    inference(demodulation,[status(thm),theory(equality)],[c_13288,c_6802])).

tff(c_13292,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_13018,c_13289])).

tff(c_13293,plain,(
    k2_zfmisc_1('#skF_13','#skF_14') = '#skF_15' ),
    inference(splitRight,[status(thm)],[c_6661])).

tff(c_22,plain,(
    ! [B_15,A_14] :
      ( k1_xboole_0 = B_15
      | k1_xboole_0 = A_14
      | k2_zfmisc_1(A_14,B_15) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_13301,plain,
    ( k1_xboole_0 = '#skF_14'
    | k1_xboole_0 = '#skF_13'
    | k1_xboole_0 != '#skF_15' ),
    inference(superposition,[status(thm),theory(equality)],[c_13293,c_22])).

tff(c_13320,plain,(
    k1_xboole_0 != '#skF_15' ),
    inference(splitLeft,[status(thm)],[c_13301])).

tff(c_14329,plain,(
    ! [A_808,B_809,D_810] :
      ( '#skF_12'(A_808,B_809,k1_funct_2(A_808,B_809),D_810) = D_810
      | ~ r2_hidden(D_810,k1_funct_2(A_808,B_809)) ) ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_14356,plain,(
    '#skF_12'('#skF_13','#skF_14',k1_funct_2('#skF_13','#skF_14'),'#skF_15') = '#skF_15' ),
    inference(resolution,[status(thm)],[c_124,c_14329])).

tff(c_14363,plain,
    ( v1_relat_1('#skF_15')
    | ~ r2_hidden('#skF_15',k1_funct_2('#skF_13','#skF_14')) ),
    inference(superposition,[status(thm),theory(equality)],[c_14356,c_86])).

tff(c_14369,plain,(
    v1_relat_1('#skF_15') ),
    inference(demodulation,[status(thm),theory(equality)],[c_124,c_14363])).

tff(c_14381,plain,(
    ! [A_811,B_812,D_813] :
      ( k1_relat_1('#skF_12'(A_811,B_812,k1_funct_2(A_811,B_812),D_813)) = A_811
      | ~ r2_hidden(D_813,k1_funct_2(A_811,B_812)) ) ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_14399,plain,
    ( k1_relat_1('#skF_15') = '#skF_13'
    | ~ r2_hidden('#skF_15',k1_funct_2('#skF_13','#skF_14')) ),
    inference(superposition,[status(thm),theory(equality)],[c_14356,c_14381])).

tff(c_14403,plain,(
    k1_relat_1('#skF_15') = '#skF_13' ),
    inference(demodulation,[status(thm),theory(equality)],[c_124,c_14399])).

tff(c_14408,plain,
    ( m1_subset_1('#skF_15',k1_zfmisc_1(k2_zfmisc_1('#skF_13',k2_relat_1('#skF_15'))))
    | ~ v1_funct_1('#skF_15')
    | ~ v1_relat_1('#skF_15') ),
    inference(superposition,[status(thm),theory(equality)],[c_14403,c_116])).

tff(c_14418,plain,(
    m1_subset_1('#skF_15',k1_zfmisc_1(k2_zfmisc_1('#skF_13',k2_relat_1('#skF_15')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14369,c_1202,c_14408])).

tff(c_14452,plain,
    ( v1_xboole_0('#skF_15')
    | ~ v1_xboole_0(k2_relat_1('#skF_15')) ),
    inference(resolution,[status(thm)],[c_14418,c_64])).

tff(c_14456,plain,(
    ~ v1_xboole_0(k2_relat_1('#skF_15')) ),
    inference(splitLeft,[status(thm)],[c_14452])).

tff(c_13296,plain,(
    m1_subset_1('#skF_15',k1_zfmisc_1('#skF_15')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_13293,c_6599])).

tff(c_15401,plain,(
    ! [C_851,A_852,B_853] :
      ( v1_funct_2(C_851,A_852,B_853)
      | ~ v1_partfun1(C_851,A_852)
      | ~ v1_funct_1(C_851)
      | ~ m1_subset_1(C_851,k1_zfmisc_1(k2_zfmisc_1(A_852,B_853))) ) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_18633,plain,(
    ! [C_934] :
      ( v1_funct_2(C_934,'#skF_13','#skF_14')
      | ~ v1_partfun1(C_934,'#skF_13')
      | ~ v1_funct_1(C_934)
      | ~ m1_subset_1(C_934,k1_zfmisc_1('#skF_15')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_13293,c_15401])).

tff(c_18644,plain,
    ( v1_funct_2('#skF_15','#skF_13','#skF_14')
    | ~ v1_partfun1('#skF_15','#skF_13')
    | ~ v1_funct_1('#skF_15') ),
    inference(resolution,[status(thm)],[c_13296,c_18633])).

tff(c_18660,plain,
    ( v1_funct_2('#skF_15','#skF_13','#skF_14')
    | ~ v1_partfun1('#skF_15','#skF_13') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1202,c_18644])).

tff(c_18661,plain,(
    ~ v1_partfun1('#skF_15','#skF_13') ),
    inference(negUnitSimplification,[status(thm)],[c_6598,c_18660])).

tff(c_14411,plain,
    ( v1_funct_2('#skF_15','#skF_13',k2_relat_1('#skF_15'))
    | ~ v1_funct_1('#skF_15')
    | ~ v1_relat_1('#skF_15') ),
    inference(superposition,[status(thm),theory(equality)],[c_14403,c_118])).

tff(c_14420,plain,(
    v1_funct_2('#skF_15','#skF_13',k2_relat_1('#skF_15')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14369,c_1202,c_14411])).

tff(c_19381,plain,(
    ! [C_956,A_957,B_958] :
      ( v1_partfun1(C_956,A_957)
      | ~ v1_funct_2(C_956,A_957,B_958)
      | ~ v1_funct_1(C_956)
      | ~ m1_subset_1(C_956,k1_zfmisc_1(k2_zfmisc_1(A_957,B_958)))
      | v1_xboole_0(B_958) ) ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_19399,plain,
    ( v1_partfun1('#skF_15','#skF_13')
    | ~ v1_funct_2('#skF_15','#skF_13',k2_relat_1('#skF_15'))
    | ~ v1_funct_1('#skF_15')
    | v1_xboole_0(k2_relat_1('#skF_15')) ),
    inference(resolution,[status(thm)],[c_14418,c_19381])).

tff(c_19437,plain,
    ( v1_partfun1('#skF_15','#skF_13')
    | v1_xboole_0(k2_relat_1('#skF_15')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1202,c_14420,c_19399])).

tff(c_19439,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_14456,c_18661,c_19437])).

tff(c_19440,plain,(
    v1_xboole_0('#skF_15') ),
    inference(splitRight,[status(thm)],[c_14452])).

tff(c_19455,plain,(
    k1_xboole_0 = '#skF_15' ),
    inference(resolution,[status(thm)],[c_19440,c_1232])).

tff(c_19464,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_13320,c_19455])).

tff(c_19466,plain,(
    k1_xboole_0 = '#skF_15' ),
    inference(splitRight,[status(thm)],[c_13301])).

tff(c_19465,plain,
    ( k1_xboole_0 = '#skF_13'
    | k1_xboole_0 = '#skF_14' ),
    inference(splitRight,[status(thm)],[c_13301])).

tff(c_19484,plain,
    ( '#skF_15' = '#skF_13'
    | '#skF_15' = '#skF_14' ),
    inference(demodulation,[status(thm),theory(equality)],[c_19466,c_19466,c_19465])).

tff(c_19485,plain,(
    '#skF_15' = '#skF_14' ),
    inference(splitLeft,[status(thm)],[c_19484])).

tff(c_19493,plain,(
    r2_hidden('#skF_14',k1_funct_2('#skF_13','#skF_14')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_19485,c_124])).

tff(c_20336,plain,(
    ! [A_1026,B_1027,D_1028] :
      ( '#skF_12'(A_1026,B_1027,k1_funct_2(A_1026,B_1027),D_1028) = D_1028
      | ~ r2_hidden(D_1028,k1_funct_2(A_1026,B_1027)) ) ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_20353,plain,(
    '#skF_12'('#skF_13','#skF_14',k1_funct_2('#skF_13','#skF_14'),'#skF_14') = '#skF_14' ),
    inference(resolution,[status(thm)],[c_19493,c_20336])).

tff(c_20490,plain,(
    ! [A_1042,B_1043,D_1044] :
      ( v1_relat_1('#skF_12'(A_1042,B_1043,k1_funct_2(A_1042,B_1043),D_1044))
      | ~ r2_hidden(D_1044,k1_funct_2(A_1042,B_1043)) ) ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_20499,plain,
    ( v1_relat_1('#skF_14')
    | ~ r2_hidden('#skF_14',k1_funct_2('#skF_13','#skF_14')) ),
    inference(superposition,[status(thm),theory(equality)],[c_20353,c_20490])).

tff(c_20503,plain,(
    v1_relat_1('#skF_14') ),
    inference(demodulation,[status(thm),theory(equality)],[c_19493,c_20499])).

tff(c_19471,plain,(
    ! [A_28] :
      ( k2_relat_1(A_28) = '#skF_15'
      | k1_relat_1(A_28) != '#skF_15'
      | ~ v1_relat_1(A_28) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_19466,c_19466,c_44])).

tff(c_20414,plain,(
    ! [A_28] :
      ( k2_relat_1(A_28) = '#skF_14'
      | k1_relat_1(A_28) != '#skF_14'
      | ~ v1_relat_1(A_28) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_19485,c_19485,c_19471])).

tff(c_20510,plain,
    ( k2_relat_1('#skF_14') = '#skF_14'
    | k1_relat_1('#skF_14') != '#skF_14' ),
    inference(resolution,[status(thm)],[c_20503,c_20414])).

tff(c_20512,plain,(
    k1_relat_1('#skF_14') != '#skF_14' ),
    inference(splitLeft,[status(thm)],[c_20510])).

tff(c_19472,plain,(
    ! [A_28] :
      ( k1_relat_1(A_28) = '#skF_15'
      | k2_relat_1(A_28) != '#skF_15'
      | ~ v1_relat_1(A_28) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_19466,c_19466,c_42])).

tff(c_20412,plain,(
    ! [A_28] :
      ( k1_relat_1(A_28) = '#skF_14'
      | k2_relat_1(A_28) != '#skF_14'
      | ~ v1_relat_1(A_28) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_19485,c_19485,c_19472])).

tff(c_20511,plain,
    ( k1_relat_1('#skF_14') = '#skF_14'
    | k2_relat_1('#skF_14') != '#skF_14' ),
    inference(resolution,[status(thm)],[c_20503,c_20412])).

tff(c_20513,plain,(
    k2_relat_1('#skF_14') != '#skF_14' ),
    inference(negUnitSimplification,[status(thm)],[c_20512,c_20511])).

tff(c_19478,plain,(
    v1_xboole_0('#skF_15') ),
    inference(demodulation,[status(thm),theory(equality)],[c_19466,c_12])).

tff(c_19486,plain,(
    v1_xboole_0('#skF_14') ),
    inference(demodulation,[status(thm),theory(equality)],[c_19485,c_19478])).

tff(c_21962,plain,(
    ! [A_1110,B_1111,D_1112] :
      ( r1_tarski(k2_relat_1('#skF_12'(A_1110,B_1111,k1_funct_2(A_1110,B_1111),D_1112)),B_1111)
      | ~ r2_hidden(D_1112,k1_funct_2(A_1110,B_1111)) ) ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_21994,plain,
    ( r1_tarski(k2_relat_1('#skF_14'),'#skF_14')
    | ~ r2_hidden('#skF_14',k1_funct_2('#skF_13','#skF_14')) ),
    inference(superposition,[status(thm),theory(equality)],[c_20353,c_21962])).

tff(c_22005,plain,(
    r1_tarski(k2_relat_1('#skF_14'),'#skF_14') ),
    inference(demodulation,[status(thm),theory(equality)],[c_19493,c_21994])).

tff(c_14,plain,(
    ! [A_10] :
      ( r2_hidden('#skF_3'(A_10),A_10)
      | k1_xboole_0 = A_10 ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_19474,plain,(
    ! [A_10] :
      ( r2_hidden('#skF_3'(A_10),A_10)
      | A_10 = '#skF_15' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_19466,c_14])).

tff(c_19705,plain,(
    ! [A_10] :
      ( r2_hidden('#skF_3'(A_10),A_10)
      | A_10 = '#skF_14' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_19485,c_19474])).

tff(c_19634,plain,(
    ! [C_968,B_969,A_970] :
      ( ~ v1_xboole_0(C_968)
      | ~ m1_subset_1(B_969,k1_zfmisc_1(C_968))
      | ~ r2_hidden(A_970,B_969) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_19939,plain,(
    ! [B_995,A_996,A_997] :
      ( ~ v1_xboole_0(B_995)
      | ~ r2_hidden(A_996,A_997)
      | ~ r1_tarski(A_997,B_995) ) ),
    inference(resolution,[status(thm)],[c_36,c_19634])).

tff(c_19950,plain,(
    ! [B_995,A_10] :
      ( ~ v1_xboole_0(B_995)
      | ~ r1_tarski(A_10,B_995)
      | A_10 = '#skF_14' ) ),
    inference(resolution,[status(thm)],[c_19705,c_19939])).

tff(c_22013,plain,
    ( ~ v1_xboole_0('#skF_14')
    | k2_relat_1('#skF_14') = '#skF_14' ),
    inference(resolution,[status(thm)],[c_22005,c_19950])).

tff(c_22034,plain,(
    k2_relat_1('#skF_14') = '#skF_14' ),
    inference(demodulation,[status(thm),theory(equality)],[c_19486,c_22013])).

tff(c_22036,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_20513,c_22034])).

tff(c_22038,plain,(
    k1_relat_1('#skF_14') = '#skF_14' ),
    inference(splitRight,[status(thm)],[c_20510])).

tff(c_22333,plain,(
    ! [A_1135,B_1136,D_1137] :
      ( k1_relat_1('#skF_12'(A_1135,B_1136,k1_funct_2(A_1135,B_1136),D_1137)) = A_1135
      | ~ r2_hidden(D_1137,k1_funct_2(A_1135,B_1136)) ) ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_22357,plain,
    ( k1_relat_1('#skF_14') = '#skF_13'
    | ~ r2_hidden('#skF_14',k1_funct_2('#skF_13','#skF_14')) ),
    inference(superposition,[status(thm),theory(equality)],[c_20353,c_22333])).

tff(c_22363,plain,(
    '#skF_14' = '#skF_13' ),
    inference(demodulation,[status(thm),theory(equality)],[c_19493,c_22038,c_22357])).

tff(c_19491,plain,(
    ~ v1_funct_2('#skF_14','#skF_13','#skF_14') ),
    inference(demodulation,[status(thm),theory(equality)],[c_19485,c_6598])).

tff(c_22397,plain,(
    ~ v1_funct_2('#skF_13','#skF_13','#skF_13') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22363,c_22363,c_19491])).

tff(c_19492,plain,(
    v1_funct_1('#skF_14') ),
    inference(demodulation,[status(thm),theory(equality)],[c_19485,c_1202])).

tff(c_22037,plain,(
    k2_relat_1('#skF_14') = '#skF_14' ),
    inference(splitRight,[status(thm)],[c_20510])).

tff(c_22064,plain,
    ( v1_funct_2('#skF_14','#skF_14',k2_relat_1('#skF_14'))
    | ~ v1_funct_1('#skF_14')
    | ~ v1_relat_1('#skF_14') ),
    inference(superposition,[status(thm),theory(equality)],[c_22038,c_118])).

tff(c_22073,plain,(
    v1_funct_2('#skF_14','#skF_14','#skF_14') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20503,c_19492,c_22037,c_22064])).

tff(c_22370,plain,(
    v1_funct_2('#skF_13','#skF_13','#skF_13') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22363,c_22363,c_22363,c_22073])).

tff(c_22815,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_22397,c_22370])).

tff(c_22816,plain,(
    '#skF_15' = '#skF_13' ),
    inference(splitRight,[status(thm)],[c_19484])).

tff(c_6678,plain,(
    ! [A_462,B_463] :
      ( r2_hidden('#skF_2'(A_462,B_463),A_462)
      | r1_tarski(A_462,B_463) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_24,plain,(
    ! [A_14] : k2_zfmisc_1(A_14,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_1203,plain,(
    ! [A_212,B_213] : ~ r2_hidden(A_212,k2_zfmisc_1(A_212,B_213)) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_1206,plain,(
    ! [A_14] : ~ r2_hidden(A_14,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_1203])).

tff(c_6692,plain,(
    ! [B_463] : r1_tarski(k1_xboole_0,B_463) ),
    inference(resolution,[status(thm)],[c_6678,c_1206])).

tff(c_6615,plain,(
    ! [A_452] : m1_subset_1(k6_partfun1(A_452),k1_zfmisc_1(k2_zfmisc_1(A_452,A_452))) ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_6622,plain,(
    m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_6615])).

tff(c_34,plain,(
    ! [A_22,B_23] :
      ( r1_tarski(A_22,B_23)
      | ~ m1_subset_1(A_22,k1_zfmisc_1(B_23)) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_6631,plain,(
    r1_tarski(k6_partfun1(k1_xboole_0),k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_6622,c_34])).

tff(c_6659,plain,
    ( k6_partfun1(k1_xboole_0) = k1_xboole_0
    | ~ r1_tarski(k1_xboole_0,k6_partfun1(k1_xboole_0)) ),
    inference(resolution,[status(thm)],[c_6631,c_6647])).

tff(c_6666,plain,(
    ~ r1_tarski(k1_xboole_0,k6_partfun1(k1_xboole_0)) ),
    inference(splitLeft,[status(thm)],[c_6659])).

tff(c_6696,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6692,c_6666])).

tff(c_6697,plain,(
    k6_partfun1(k1_xboole_0) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_6659])).

tff(c_19469,plain,(
    k6_partfun1('#skF_15') = '#skF_15' ),
    inference(demodulation,[status(thm),theory(equality)],[c_19466,c_19466,c_6697])).

tff(c_22850,plain,(
    k6_partfun1('#skF_13') = '#skF_13' ),
    inference(demodulation,[status(thm),theory(equality)],[c_22816,c_22816,c_19469])).

tff(c_112,plain,(
    ! [A_103] : v1_partfun1(k6_partfun1(A_103),A_103) ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_22860,plain,(
    v1_partfun1('#skF_13','#skF_13') ),
    inference(superposition,[status(thm),theory(equality)],[c_22850,c_112])).

tff(c_22824,plain,(
    v1_funct_1('#skF_13') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22816,c_1202])).

tff(c_22895,plain,(
    ! [A_1153,B_1154] :
      ( r2_hidden('#skF_2'(A_1153,B_1154),A_1153)
      | r1_tarski(A_1153,B_1154) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_19475,plain,(
    ! [A_14] : ~ r2_hidden(A_14,'#skF_15') ),
    inference(demodulation,[status(thm),theory(equality)],[c_19466,c_1206])).

tff(c_22873,plain,(
    ! [A_14] : ~ r2_hidden(A_14,'#skF_13') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22816,c_19475])).

tff(c_22907,plain,(
    ! [B_1154] : r1_tarski('#skF_13',B_1154) ),
    inference(resolution,[status(thm)],[c_22895,c_22873])).

tff(c_26263,plain,(
    ! [C_1337,A_1338,B_1339] :
      ( v1_funct_2(C_1337,A_1338,B_1339)
      | ~ v1_partfun1(C_1337,A_1338)
      | ~ v1_funct_1(C_1337)
      | ~ m1_subset_1(C_1337,k1_zfmisc_1(k2_zfmisc_1(A_1338,B_1339))) ) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_65229,plain,(
    ! [A_1839,A_1840,B_1841] :
      ( v1_funct_2(A_1839,A_1840,B_1841)
      | ~ v1_partfun1(A_1839,A_1840)
      | ~ v1_funct_1(A_1839)
      | ~ r1_tarski(A_1839,k2_zfmisc_1(A_1840,B_1841)) ) ),
    inference(resolution,[status(thm)],[c_36,c_26263])).

tff(c_65398,plain,(
    ! [A_1840,B_1841] :
      ( v1_funct_2('#skF_13',A_1840,B_1841)
      | ~ v1_partfun1('#skF_13',A_1840)
      | ~ v1_funct_1('#skF_13') ) ),
    inference(resolution,[status(thm)],[c_22907,c_65229])).

tff(c_65446,plain,(
    ! [A_1842,B_1843] :
      ( v1_funct_2('#skF_13',A_1842,B_1843)
      | ~ v1_partfun1('#skF_13',A_1842) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22824,c_65398])).

tff(c_22823,plain,(
    ~ v1_funct_2('#skF_13','#skF_13','#skF_14') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22816,c_6598])).

tff(c_65449,plain,(
    ~ v1_partfun1('#skF_13','#skF_13') ),
    inference(resolution,[status(thm)],[c_65446,c_22823])).

tff(c_65453,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_22860,c_65449])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n021.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 09:54:19 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 17.05/7.68  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 17.05/7.71  
% 17.05/7.71  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 17.05/7.72  %$ v1_funct_2 > v1_partfun1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_zfmisc_1 > k1_funct_2 > k1_funct_1 > #nlpp > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_6 > #skF_4 > #skF_15 > #skF_1 > #skF_12 > #skF_14 > #skF_13 > #skF_11 > #skF_9 > #skF_3 > #skF_2 > #skF_8 > #skF_7 > #skF_5 > #skF_10
% 17.05/7.72  
% 17.05/7.72  %Foreground sorts:
% 17.05/7.72  
% 17.05/7.72  
% 17.05/7.72  %Background operators:
% 17.05/7.72  
% 17.05/7.72  
% 17.05/7.72  %Foreground operators:
% 17.05/7.72  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 17.05/7.72  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 17.05/7.72  tff('#skF_4', type, '#skF_4': $i > $i).
% 17.05/7.72  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 17.05/7.72  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 17.05/7.72  tff('#skF_15', type, '#skF_15': $i).
% 17.05/7.72  tff('#skF_1', type, '#skF_1': $i > $i).
% 17.05/7.72  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 17.05/7.72  tff('#skF_12', type, '#skF_12': ($i * $i * $i * $i) > $i).
% 17.05/7.72  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 17.05/7.72  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 17.05/7.72  tff('#skF_14', type, '#skF_14': $i).
% 17.05/7.72  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 17.05/7.72  tff('#skF_13', type, '#skF_13': $i).
% 17.05/7.72  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 17.05/7.72  tff('#skF_11', type, '#skF_11': ($i * $i * $i) > $i).
% 17.05/7.72  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 17.05/7.72  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 17.05/7.72  tff('#skF_9', type, '#skF_9': ($i * $i * $i) > $i).
% 17.05/7.72  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 17.05/7.72  tff(k1_funct_2, type, k1_funct_2: ($i * $i) > $i).
% 17.05/7.72  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 17.05/7.72  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 17.05/7.72  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 17.05/7.72  tff('#skF_3', type, '#skF_3': $i > $i).
% 17.05/7.72  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 17.05/7.72  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 17.05/7.72  tff('#skF_8', type, '#skF_8': ($i * $i * $i) > $i).
% 17.05/7.72  tff('#skF_7', type, '#skF_7': ($i * $i) > $i).
% 17.05/7.72  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 17.05/7.72  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 17.05/7.72  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 17.05/7.72  tff('#skF_10', type, '#skF_10': ($i * $i * $i) > $i).
% 17.05/7.72  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 17.05/7.72  
% 17.05/7.75  tff(f_185, negated_conjecture, ~(![A, B, C]: (r2_hidden(C, k1_funct_2(A, B)) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t121_funct_2)).
% 17.05/7.75  tff(f_162, axiom, (![A, B, C]: ((C = k1_funct_2(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (?[E]: ((((v1_relat_1(E) & v1_funct_1(E)) & (D = E)) & (k1_relat_1(E) = A)) & r1_tarski(k2_relat_1(E), B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_funct_2)).
% 17.05/7.75  tff(f_39, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 17.05/7.75  tff(f_86, axiom, (![A]: (v1_relat_1(A) => r1_tarski(A, k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t21_relat_1)).
% 17.05/7.75  tff(f_75, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 17.05/7.75  tff(f_114, axiom, (![A, B]: (v1_xboole_0(A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => v1_xboole_0(C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc4_relset_1)).
% 17.05/7.75  tff(f_53, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 17.05/7.75  tff(f_122, axiom, (![A, B, C]: (v1_relat_1(C) => ((r1_tarski(k1_relat_1(C), A) & r1_tarski(k2_relat_1(C), B)) => m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_relset_1)).
% 17.05/7.75  tff(f_132, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v1_partfun1(C, A)) => (v1_funct_1(C) & v1_funct_2(C, A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_funct_2)).
% 17.05/7.75  tff(f_176, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => ((v1_funct_1(A) & v1_funct_2(A, k1_relat_1(A), k2_relat_1(A))) & m1_subset_1(A, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_funct_2)).
% 17.05/7.75  tff(f_146, axiom, (![A, B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) => (v1_funct_1(C) & v1_partfun1(C, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc5_funct_2)).
% 17.05/7.75  tff(f_47, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 17.05/7.75  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 17.05/7.75  tff(f_92, axiom, (![A]: (v1_relat_1(A) => ((k1_relat_1(A) = k1_xboole_0) <=> (k2_relat_1(A) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_relat_1)).
% 17.05/7.75  tff(f_59, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 17.05/7.75  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 17.05/7.75  tff(f_82, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_subset)).
% 17.05/7.75  tff(f_62, axiom, (![A, B]: ~r2_hidden(A, k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t152_zfmisc_1)).
% 17.05/7.75  tff(f_166, axiom, (![A]: (v1_partfun1(k6_partfun1(A), A) & m1_subset_1(k6_partfun1(A), k1_zfmisc_1(k2_zfmisc_1(A, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_partfun1)).
% 17.05/7.75  tff(c_124, plain, (r2_hidden('#skF_15', k1_funct_2('#skF_13', '#skF_14'))), inference(cnfTransformation, [status(thm)], [f_185])).
% 17.05/7.75  tff(c_7791, plain, (![A_554, B_555, D_556]: ('#skF_12'(A_554, B_555, k1_funct_2(A_554, B_555), D_556)=D_556 | ~r2_hidden(D_556, k1_funct_2(A_554, B_555)))), inference(cnfTransformation, [status(thm)], [f_162])).
% 17.05/7.75  tff(c_7814, plain, ('#skF_12'('#skF_13', '#skF_14', k1_funct_2('#skF_13', '#skF_14'), '#skF_15')='#skF_15'), inference(resolution, [status(thm)], [c_124, c_7791])).
% 17.05/7.75  tff(c_86, plain, (![A_83, B_84, D_99]: (v1_relat_1('#skF_12'(A_83, B_84, k1_funct_2(A_83, B_84), D_99)) | ~r2_hidden(D_99, k1_funct_2(A_83, B_84)))), inference(cnfTransformation, [status(thm)], [f_162])).
% 17.05/7.75  tff(c_7927, plain, (v1_relat_1('#skF_15') | ~r2_hidden('#skF_15', k1_funct_2('#skF_13', '#skF_14'))), inference(superposition, [status(thm), theory('equality')], [c_7814, c_86])).
% 17.05/7.75  tff(c_7933, plain, (v1_relat_1('#skF_15')), inference(demodulation, [status(thm), theory('equality')], [c_124, c_7927])).
% 17.05/7.75  tff(c_122, plain, (~m1_subset_1('#skF_15', k1_zfmisc_1(k2_zfmisc_1('#skF_13', '#skF_14'))) | ~v1_funct_2('#skF_15', '#skF_13', '#skF_14') | ~v1_funct_1('#skF_15')), inference(cnfTransformation, [status(thm)], [f_185])).
% 17.05/7.75  tff(c_156, plain, (~v1_funct_1('#skF_15')), inference(splitLeft, [status(thm)], [c_122])).
% 17.05/7.75  tff(c_1166, plain, (![A_209, B_210, D_211]: ('#skF_12'(A_209, B_210, k1_funct_2(A_209, B_210), D_211)=D_211 | ~r2_hidden(D_211, k1_funct_2(A_209, B_210)))), inference(cnfTransformation, [status(thm)], [f_162])).
% 17.05/7.75  tff(c_1185, plain, ('#skF_12'('#skF_13', '#skF_14', k1_funct_2('#skF_13', '#skF_14'), '#skF_15')='#skF_15'), inference(resolution, [status(thm)], [c_124, c_1166])).
% 17.05/7.75  tff(c_84, plain, (![A_83, B_84, D_99]: (v1_funct_1('#skF_12'(A_83, B_84, k1_funct_2(A_83, B_84), D_99)) | ~r2_hidden(D_99, k1_funct_2(A_83, B_84)))), inference(cnfTransformation, [status(thm)], [f_162])).
% 17.05/7.75  tff(c_1192, plain, (v1_funct_1('#skF_15') | ~r2_hidden('#skF_15', k1_funct_2('#skF_13', '#skF_14'))), inference(superposition, [status(thm), theory('equality')], [c_1185, c_84])).
% 17.05/7.75  tff(c_1198, plain, (v1_funct_1('#skF_15')), inference(demodulation, [status(thm), theory('equality')], [c_124, c_1192])).
% 17.05/7.75  tff(c_1200, plain, $false, inference(negUnitSimplification, [status(thm)], [c_156, c_1198])).
% 17.05/7.75  tff(c_1202, plain, (v1_funct_1('#skF_15')), inference(splitRight, [status(thm)], [c_122])).
% 17.05/7.75  tff(c_12, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 17.34/7.75  tff(c_8341, plain, (![A_580, B_581, D_582]: (k1_relat_1('#skF_12'(A_580, B_581, k1_funct_2(A_580, B_581), D_582))=A_580 | ~r2_hidden(D_582, k1_funct_2(A_580, B_581)))), inference(cnfTransformation, [status(thm)], [f_162])).
% 17.34/7.75  tff(c_8362, plain, (k1_relat_1('#skF_15')='#skF_13' | ~r2_hidden('#skF_15', k1_funct_2('#skF_13', '#skF_14'))), inference(superposition, [status(thm), theory('equality')], [c_7814, c_8341])).
% 17.34/7.75  tff(c_8366, plain, (k1_relat_1('#skF_15')='#skF_13'), inference(demodulation, [status(thm), theory('equality')], [c_124, c_8362])).
% 17.34/7.75  tff(c_40, plain, (![A_27]: (r1_tarski(A_27, k2_zfmisc_1(k1_relat_1(A_27), k2_relat_1(A_27))) | ~v1_relat_1(A_27))), inference(cnfTransformation, [status(thm)], [f_86])).
% 17.34/7.75  tff(c_8380, plain, (r1_tarski('#skF_15', k2_zfmisc_1('#skF_13', k2_relat_1('#skF_15'))) | ~v1_relat_1('#skF_15')), inference(superposition, [status(thm), theory('equality')], [c_8366, c_40])).
% 17.34/7.75  tff(c_8390, plain, (r1_tarski('#skF_15', k2_zfmisc_1('#skF_13', k2_relat_1('#skF_15')))), inference(demodulation, [status(thm), theory('equality')], [c_7933, c_8380])).
% 17.34/7.75  tff(c_36, plain, (![A_22, B_23]: (m1_subset_1(A_22, k1_zfmisc_1(B_23)) | ~r1_tarski(A_22, B_23))), inference(cnfTransformation, [status(thm)], [f_75])).
% 17.34/7.75  tff(c_7236, plain, (![C_512, B_513, A_514]: (v1_xboole_0(C_512) | ~m1_subset_1(C_512, k1_zfmisc_1(k2_zfmisc_1(B_513, A_514))) | ~v1_xboole_0(A_514))), inference(cnfTransformation, [status(thm)], [f_114])).
% 17.34/7.75  tff(c_7270, plain, (![A_22, A_514, B_513]: (v1_xboole_0(A_22) | ~v1_xboole_0(A_514) | ~r1_tarski(A_22, k2_zfmisc_1(B_513, A_514)))), inference(resolution, [status(thm)], [c_36, c_7236])).
% 17.34/7.75  tff(c_8408, plain, (v1_xboole_0('#skF_15') | ~v1_xboole_0(k2_relat_1('#skF_15'))), inference(resolution, [status(thm)], [c_8390, c_7270])).
% 17.34/7.75  tff(c_8414, plain, (~v1_xboole_0(k2_relat_1('#skF_15'))), inference(splitLeft, [status(thm)], [c_8408])).
% 17.34/7.75  tff(c_2197, plain, (![A_304, B_305, D_306]: ('#skF_12'(A_304, B_305, k1_funct_2(A_304, B_305), D_306)=D_306 | ~r2_hidden(D_306, k1_funct_2(A_304, B_305)))), inference(cnfTransformation, [status(thm)], [f_162])).
% 17.34/7.75  tff(c_2216, plain, ('#skF_12'('#skF_13', '#skF_14', k1_funct_2('#skF_13', '#skF_14'), '#skF_15')='#skF_15'), inference(resolution, [status(thm)], [c_124, c_2197])).
% 17.34/7.75  tff(c_2294, plain, (![A_314, B_315, D_316]: (v1_relat_1('#skF_12'(A_314, B_315, k1_funct_2(A_314, B_315), D_316)) | ~r2_hidden(D_316, k1_funct_2(A_314, B_315)))), inference(cnfTransformation, [status(thm)], [f_162])).
% 17.34/7.75  tff(c_2303, plain, (v1_relat_1('#skF_15') | ~r2_hidden('#skF_15', k1_funct_2('#skF_13', '#skF_14'))), inference(superposition, [status(thm), theory('equality')], [c_2216, c_2294])).
% 17.34/7.75  tff(c_2307, plain, (v1_relat_1('#skF_15')), inference(demodulation, [status(thm), theory('equality')], [c_124, c_2303])).
% 17.34/7.75  tff(c_20, plain, (![B_13]: (r1_tarski(B_13, B_13))), inference(cnfTransformation, [status(thm)], [f_53])).
% 17.34/7.75  tff(c_2462, plain, (![A_325, B_326, D_327]: (k1_relat_1('#skF_12'(A_325, B_326, k1_funct_2(A_325, B_326), D_327))=A_325 | ~r2_hidden(D_327, k1_funct_2(A_325, B_326)))), inference(cnfTransformation, [status(thm)], [f_162])).
% 17.34/7.75  tff(c_2480, plain, (k1_relat_1('#skF_15')='#skF_13' | ~r2_hidden('#skF_15', k1_funct_2('#skF_13', '#skF_14'))), inference(superposition, [status(thm), theory('equality')], [c_2216, c_2462])).
% 17.34/7.75  tff(c_2484, plain, (k1_relat_1('#skF_15')='#skF_13'), inference(demodulation, [status(thm), theory('equality')], [c_124, c_2480])).
% 17.34/7.75  tff(c_3395, plain, (![A_356, B_357, D_358]: (r1_tarski(k2_relat_1('#skF_12'(A_356, B_357, k1_funct_2(A_356, B_357), D_358)), B_357) | ~r2_hidden(D_358, k1_funct_2(A_356, B_357)))), inference(cnfTransformation, [status(thm)], [f_162])).
% 17.34/7.75  tff(c_3423, plain, (r1_tarski(k2_relat_1('#skF_15'), '#skF_14') | ~r2_hidden('#skF_15', k1_funct_2('#skF_13', '#skF_14'))), inference(superposition, [status(thm), theory('equality')], [c_2216, c_3395])).
% 17.34/7.75  tff(c_3433, plain, (r1_tarski(k2_relat_1('#skF_15'), '#skF_14')), inference(demodulation, [status(thm), theory('equality')], [c_124, c_3423])).
% 17.34/7.75  tff(c_6557, plain, (![C_446, A_447, B_448]: (m1_subset_1(C_446, k1_zfmisc_1(k2_zfmisc_1(A_447, B_448))) | ~r1_tarski(k2_relat_1(C_446), B_448) | ~r1_tarski(k1_relat_1(C_446), A_447) | ~v1_relat_1(C_446))), inference(cnfTransformation, [status(thm)], [f_122])).
% 17.34/7.75  tff(c_1201, plain, (~v1_funct_2('#skF_15', '#skF_13', '#skF_14') | ~m1_subset_1('#skF_15', k1_zfmisc_1(k2_zfmisc_1('#skF_13', '#skF_14')))), inference(splitRight, [status(thm)], [c_122])).
% 17.34/7.75  tff(c_1240, plain, (~m1_subset_1('#skF_15', k1_zfmisc_1(k2_zfmisc_1('#skF_13', '#skF_14')))), inference(splitLeft, [status(thm)], [c_1201])).
% 17.34/7.75  tff(c_6571, plain, (~r1_tarski(k2_relat_1('#skF_15'), '#skF_14') | ~r1_tarski(k1_relat_1('#skF_15'), '#skF_13') | ~v1_relat_1('#skF_15')), inference(resolution, [status(thm)], [c_6557, c_1240])).
% 17.34/7.75  tff(c_6597, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2307, c_20, c_2484, c_3433, c_6571])).
% 17.34/7.75  tff(c_6598, plain, (~v1_funct_2('#skF_15', '#skF_13', '#skF_14')), inference(splitRight, [status(thm)], [c_1201])).
% 17.34/7.75  tff(c_6599, plain, (m1_subset_1('#skF_15', k1_zfmisc_1(k2_zfmisc_1('#skF_13', '#skF_14')))), inference(splitRight, [status(thm)], [c_1201])).
% 17.34/7.75  tff(c_8694, plain, (![C_594, A_595, B_596]: (v1_funct_2(C_594, A_595, B_596) | ~v1_partfun1(C_594, A_595) | ~v1_funct_1(C_594) | ~m1_subset_1(C_594, k1_zfmisc_1(k2_zfmisc_1(A_595, B_596))))), inference(cnfTransformation, [status(thm)], [f_132])).
% 17.34/7.75  tff(c_8720, plain, (v1_funct_2('#skF_15', '#skF_13', '#skF_14') | ~v1_partfun1('#skF_15', '#skF_13') | ~v1_funct_1('#skF_15')), inference(resolution, [status(thm)], [c_6599, c_8694])).
% 17.34/7.75  tff(c_8747, plain, (v1_funct_2('#skF_15', '#skF_13', '#skF_14') | ~v1_partfun1('#skF_15', '#skF_13')), inference(demodulation, [status(thm), theory('equality')], [c_1202, c_8720])).
% 17.34/7.75  tff(c_8748, plain, (~v1_partfun1('#skF_15', '#skF_13')), inference(negUnitSimplification, [status(thm)], [c_6598, c_8747])).
% 17.34/7.75  tff(c_118, plain, (![A_104]: (v1_funct_2(A_104, k1_relat_1(A_104), k2_relat_1(A_104)) | ~v1_funct_1(A_104) | ~v1_relat_1(A_104))), inference(cnfTransformation, [status(thm)], [f_176])).
% 17.34/7.75  tff(c_8377, plain, (v1_funct_2('#skF_15', '#skF_13', k2_relat_1('#skF_15')) | ~v1_funct_1('#skF_15') | ~v1_relat_1('#skF_15')), inference(superposition, [status(thm), theory('equality')], [c_8366, c_118])).
% 17.34/7.75  tff(c_8388, plain, (v1_funct_2('#skF_15', '#skF_13', k2_relat_1('#skF_15'))), inference(demodulation, [status(thm), theory('equality')], [c_7933, c_1202, c_8377])).
% 17.34/7.75  tff(c_116, plain, (![A_104]: (m1_subset_1(A_104, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_104), k2_relat_1(A_104)))) | ~v1_funct_1(A_104) | ~v1_relat_1(A_104))), inference(cnfTransformation, [status(thm)], [f_176])).
% 17.34/7.75  tff(c_8374, plain, (m1_subset_1('#skF_15', k1_zfmisc_1(k2_zfmisc_1('#skF_13', k2_relat_1('#skF_15')))) | ~v1_funct_1('#skF_15') | ~v1_relat_1('#skF_15')), inference(superposition, [status(thm), theory('equality')], [c_8366, c_116])).
% 17.34/7.75  tff(c_8386, plain, (m1_subset_1('#skF_15', k1_zfmisc_1(k2_zfmisc_1('#skF_13', k2_relat_1('#skF_15'))))), inference(demodulation, [status(thm), theory('equality')], [c_7933, c_1202, c_8374])).
% 17.34/7.75  tff(c_12364, plain, (![C_691, A_692, B_693]: (v1_partfun1(C_691, A_692) | ~v1_funct_2(C_691, A_692, B_693) | ~v1_funct_1(C_691) | ~m1_subset_1(C_691, k1_zfmisc_1(k2_zfmisc_1(A_692, B_693))) | v1_xboole_0(B_693))), inference(cnfTransformation, [status(thm)], [f_146])).
% 17.34/7.75  tff(c_12379, plain, (v1_partfun1('#skF_15', '#skF_13') | ~v1_funct_2('#skF_15', '#skF_13', k2_relat_1('#skF_15')) | ~v1_funct_1('#skF_15') | v1_xboole_0(k2_relat_1('#skF_15'))), inference(resolution, [status(thm)], [c_8386, c_12364])).
% 17.34/7.75  tff(c_12420, plain, (v1_partfun1('#skF_15', '#skF_13') | v1_xboole_0(k2_relat_1('#skF_15'))), inference(demodulation, [status(thm), theory('equality')], [c_1202, c_8388, c_12379])).
% 17.34/7.75  tff(c_12422, plain, $false, inference(negUnitSimplification, [status(thm)], [c_8414, c_8748, c_12420])).
% 17.34/7.75  tff(c_12423, plain, (v1_xboole_0('#skF_15')), inference(splitRight, [status(thm)], [c_8408])).
% 17.34/7.75  tff(c_1222, plain, (![A_216]: (r2_hidden('#skF_3'(A_216), A_216) | k1_xboole_0=A_216)), inference(cnfTransformation, [status(thm)], [f_47])).
% 17.34/7.75  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 17.34/7.75  tff(c_1232, plain, (![A_216]: (~v1_xboole_0(A_216) | k1_xboole_0=A_216)), inference(resolution, [status(thm)], [c_1222, c_2])).
% 17.34/7.75  tff(c_12447, plain, (k1_xboole_0='#skF_15'), inference(resolution, [status(thm)], [c_12423, c_1232])).
% 17.34/7.75  tff(c_44, plain, (![A_28]: (k2_relat_1(A_28)=k1_xboole_0 | k1_relat_1(A_28)!=k1_xboole_0 | ~v1_relat_1(A_28))), inference(cnfTransformation, [status(thm)], [f_92])).
% 17.34/7.75  tff(c_7941, plain, (k2_relat_1('#skF_15')=k1_xboole_0 | k1_relat_1('#skF_15')!=k1_xboole_0), inference(resolution, [status(thm)], [c_7933, c_44])).
% 17.34/7.75  tff(c_7943, plain, (k1_relat_1('#skF_15')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_7941])).
% 17.34/7.75  tff(c_42, plain, (![A_28]: (k1_relat_1(A_28)=k1_xboole_0 | k2_relat_1(A_28)!=k1_xboole_0 | ~v1_relat_1(A_28))), inference(cnfTransformation, [status(thm)], [f_92])).
% 17.34/7.75  tff(c_7942, plain, (k1_relat_1('#skF_15')=k1_xboole_0 | k2_relat_1('#skF_15')!=k1_xboole_0), inference(resolution, [status(thm)], [c_7933, c_42])).
% 17.34/7.75  tff(c_7944, plain, (k2_relat_1('#skF_15')!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_7943, c_7942])).
% 17.34/7.75  tff(c_12452, plain, (k2_relat_1('#skF_15')!='#skF_15'), inference(demodulation, [status(thm), theory('equality')], [c_12447, c_7944])).
% 17.34/7.75  tff(c_12424, plain, (v1_xboole_0(k2_relat_1('#skF_15'))), inference(splitRight, [status(thm)], [c_8408])).
% 17.34/7.75  tff(c_12706, plain, (![A_703]: (~v1_xboole_0(A_703) | A_703='#skF_15')), inference(demodulation, [status(thm), theory('equality')], [c_12447, c_1232])).
% 17.34/7.75  tff(c_12709, plain, (k2_relat_1('#skF_15')='#skF_15'), inference(resolution, [status(thm)], [c_12424, c_12706])).
% 17.34/7.75  tff(c_12731, plain, $false, inference(negUnitSimplification, [status(thm)], [c_12452, c_12709])).
% 17.34/7.75  tff(c_12732, plain, (k2_relat_1('#skF_15')=k1_xboole_0), inference(splitRight, [status(thm)], [c_7941])).
% 17.34/7.75  tff(c_7478, plain, (![A_526]: (m1_subset_1(A_526, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_526), k2_relat_1(A_526)))) | ~v1_funct_1(A_526) | ~v1_relat_1(A_526))), inference(cnfTransformation, [status(thm)], [f_176])).
% 17.34/7.75  tff(c_64, plain, (![C_72, B_70, A_69]: (v1_xboole_0(C_72) | ~m1_subset_1(C_72, k1_zfmisc_1(k2_zfmisc_1(B_70, A_69))) | ~v1_xboole_0(A_69))), inference(cnfTransformation, [status(thm)], [f_114])).
% 17.34/7.75  tff(c_7487, plain, (![A_526]: (v1_xboole_0(A_526) | ~v1_xboole_0(k2_relat_1(A_526)) | ~v1_funct_1(A_526) | ~v1_relat_1(A_526))), inference(resolution, [status(thm)], [c_7478, c_64])).
% 17.34/7.75  tff(c_12737, plain, (v1_xboole_0('#skF_15') | ~v1_xboole_0(k1_xboole_0) | ~v1_funct_1('#skF_15') | ~v1_relat_1('#skF_15')), inference(superposition, [status(thm), theory('equality')], [c_12732, c_7487])).
% 17.34/7.75  tff(c_12750, plain, (v1_xboole_0('#skF_15')), inference(demodulation, [status(thm), theory('equality')], [c_7933, c_1202, c_12, c_12737])).
% 17.34/7.75  tff(c_12780, plain, (k1_xboole_0='#skF_15'), inference(resolution, [status(thm)], [c_12750, c_1232])).
% 17.34/7.75  tff(c_12733, plain, (k1_relat_1('#skF_15')=k1_xboole_0), inference(splitRight, [status(thm)], [c_7941])).
% 17.34/7.75  tff(c_12839, plain, (k1_relat_1('#skF_15')='#skF_15'), inference(demodulation, [status(thm), theory('equality')], [c_12780, c_12733])).
% 17.34/7.75  tff(c_12988, plain, (![A_708, B_709, D_710]: (k1_relat_1('#skF_12'(A_708, B_709, k1_funct_2(A_708, B_709), D_710))=A_708 | ~r2_hidden(D_710, k1_funct_2(A_708, B_709)))), inference(cnfTransformation, [status(thm)], [f_162])).
% 17.34/7.75  tff(c_13006, plain, (k1_relat_1('#skF_15')='#skF_13' | ~r2_hidden('#skF_15', k1_funct_2('#skF_13', '#skF_14'))), inference(superposition, [status(thm), theory('equality')], [c_7814, c_12988])).
% 17.34/7.75  tff(c_13010, plain, ('#skF_15'='#skF_13'), inference(demodulation, [status(thm), theory('equality')], [c_124, c_12839, c_13006])).
% 17.34/7.75  tff(c_13018, plain, (v1_xboole_0('#skF_13')), inference(demodulation, [status(thm), theory('equality')], [c_13010, c_12750])).
% 17.34/7.75  tff(c_26, plain, (![B_15]: (k2_zfmisc_1(k1_xboole_0, B_15)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_59])).
% 17.34/7.75  tff(c_12832, plain, (![B_15]: (k2_zfmisc_1('#skF_15', B_15)='#skF_15')), inference(demodulation, [status(thm), theory('equality')], [c_12780, c_12780, c_26])).
% 17.34/7.75  tff(c_13288, plain, (![B_15]: (k2_zfmisc_1('#skF_13', B_15)='#skF_13')), inference(demodulation, [status(thm), theory('equality')], [c_13010, c_13010, c_12832])).
% 17.34/7.75  tff(c_6757, plain, (![A_468, B_469]: (r2_hidden('#skF_2'(A_468, B_469), A_468) | r1_tarski(A_468, B_469))), inference(cnfTransformation, [status(thm)], [f_38])).
% 17.34/7.75  tff(c_6796, plain, (![A_474, B_475]: (~v1_xboole_0(A_474) | r1_tarski(A_474, B_475))), inference(resolution, [status(thm)], [c_6757, c_2])).
% 17.34/7.75  tff(c_6600, plain, (![A_449, B_450]: (r1_tarski(A_449, B_450) | ~m1_subset_1(A_449, k1_zfmisc_1(B_450)))), inference(cnfTransformation, [status(thm)], [f_75])).
% 17.34/7.75  tff(c_6611, plain, (r1_tarski('#skF_15', k2_zfmisc_1('#skF_13', '#skF_14'))), inference(resolution, [status(thm)], [c_6599, c_6600])).
% 17.34/7.75  tff(c_6647, plain, (![B_458, A_459]: (B_458=A_459 | ~r1_tarski(B_458, A_459) | ~r1_tarski(A_459, B_458))), inference(cnfTransformation, [status(thm)], [f_53])).
% 17.34/7.75  tff(c_6661, plain, (k2_zfmisc_1('#skF_13', '#skF_14')='#skF_15' | ~r1_tarski(k2_zfmisc_1('#skF_13', '#skF_14'), '#skF_15')), inference(resolution, [status(thm)], [c_6611, c_6647])).
% 17.34/7.75  tff(c_6729, plain, (~r1_tarski(k2_zfmisc_1('#skF_13', '#skF_14'), '#skF_15')), inference(splitLeft, [status(thm)], [c_6661])).
% 17.34/7.75  tff(c_6802, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_13', '#skF_14'))), inference(resolution, [status(thm)], [c_6796, c_6729])).
% 17.34/7.75  tff(c_13289, plain, (~v1_xboole_0('#skF_13')), inference(demodulation, [status(thm), theory('equality')], [c_13288, c_6802])).
% 17.34/7.75  tff(c_13292, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_13018, c_13289])).
% 17.34/7.75  tff(c_13293, plain, (k2_zfmisc_1('#skF_13', '#skF_14')='#skF_15'), inference(splitRight, [status(thm)], [c_6661])).
% 17.34/7.75  tff(c_22, plain, (![B_15, A_14]: (k1_xboole_0=B_15 | k1_xboole_0=A_14 | k2_zfmisc_1(A_14, B_15)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_59])).
% 17.34/7.75  tff(c_13301, plain, (k1_xboole_0='#skF_14' | k1_xboole_0='#skF_13' | k1_xboole_0!='#skF_15'), inference(superposition, [status(thm), theory('equality')], [c_13293, c_22])).
% 17.34/7.75  tff(c_13320, plain, (k1_xboole_0!='#skF_15'), inference(splitLeft, [status(thm)], [c_13301])).
% 17.34/7.75  tff(c_14329, plain, (![A_808, B_809, D_810]: ('#skF_12'(A_808, B_809, k1_funct_2(A_808, B_809), D_810)=D_810 | ~r2_hidden(D_810, k1_funct_2(A_808, B_809)))), inference(cnfTransformation, [status(thm)], [f_162])).
% 17.34/7.75  tff(c_14356, plain, ('#skF_12'('#skF_13', '#skF_14', k1_funct_2('#skF_13', '#skF_14'), '#skF_15')='#skF_15'), inference(resolution, [status(thm)], [c_124, c_14329])).
% 17.34/7.75  tff(c_14363, plain, (v1_relat_1('#skF_15') | ~r2_hidden('#skF_15', k1_funct_2('#skF_13', '#skF_14'))), inference(superposition, [status(thm), theory('equality')], [c_14356, c_86])).
% 17.34/7.75  tff(c_14369, plain, (v1_relat_1('#skF_15')), inference(demodulation, [status(thm), theory('equality')], [c_124, c_14363])).
% 17.34/7.75  tff(c_14381, plain, (![A_811, B_812, D_813]: (k1_relat_1('#skF_12'(A_811, B_812, k1_funct_2(A_811, B_812), D_813))=A_811 | ~r2_hidden(D_813, k1_funct_2(A_811, B_812)))), inference(cnfTransformation, [status(thm)], [f_162])).
% 17.34/7.75  tff(c_14399, plain, (k1_relat_1('#skF_15')='#skF_13' | ~r2_hidden('#skF_15', k1_funct_2('#skF_13', '#skF_14'))), inference(superposition, [status(thm), theory('equality')], [c_14356, c_14381])).
% 17.34/7.75  tff(c_14403, plain, (k1_relat_1('#skF_15')='#skF_13'), inference(demodulation, [status(thm), theory('equality')], [c_124, c_14399])).
% 17.34/7.75  tff(c_14408, plain, (m1_subset_1('#skF_15', k1_zfmisc_1(k2_zfmisc_1('#skF_13', k2_relat_1('#skF_15')))) | ~v1_funct_1('#skF_15') | ~v1_relat_1('#skF_15')), inference(superposition, [status(thm), theory('equality')], [c_14403, c_116])).
% 17.34/7.75  tff(c_14418, plain, (m1_subset_1('#skF_15', k1_zfmisc_1(k2_zfmisc_1('#skF_13', k2_relat_1('#skF_15'))))), inference(demodulation, [status(thm), theory('equality')], [c_14369, c_1202, c_14408])).
% 17.34/7.75  tff(c_14452, plain, (v1_xboole_0('#skF_15') | ~v1_xboole_0(k2_relat_1('#skF_15'))), inference(resolution, [status(thm)], [c_14418, c_64])).
% 17.34/7.75  tff(c_14456, plain, (~v1_xboole_0(k2_relat_1('#skF_15'))), inference(splitLeft, [status(thm)], [c_14452])).
% 17.34/7.75  tff(c_13296, plain, (m1_subset_1('#skF_15', k1_zfmisc_1('#skF_15'))), inference(demodulation, [status(thm), theory('equality')], [c_13293, c_6599])).
% 17.34/7.75  tff(c_15401, plain, (![C_851, A_852, B_853]: (v1_funct_2(C_851, A_852, B_853) | ~v1_partfun1(C_851, A_852) | ~v1_funct_1(C_851) | ~m1_subset_1(C_851, k1_zfmisc_1(k2_zfmisc_1(A_852, B_853))))), inference(cnfTransformation, [status(thm)], [f_132])).
% 17.34/7.75  tff(c_18633, plain, (![C_934]: (v1_funct_2(C_934, '#skF_13', '#skF_14') | ~v1_partfun1(C_934, '#skF_13') | ~v1_funct_1(C_934) | ~m1_subset_1(C_934, k1_zfmisc_1('#skF_15')))), inference(superposition, [status(thm), theory('equality')], [c_13293, c_15401])).
% 17.34/7.75  tff(c_18644, plain, (v1_funct_2('#skF_15', '#skF_13', '#skF_14') | ~v1_partfun1('#skF_15', '#skF_13') | ~v1_funct_1('#skF_15')), inference(resolution, [status(thm)], [c_13296, c_18633])).
% 17.34/7.75  tff(c_18660, plain, (v1_funct_2('#skF_15', '#skF_13', '#skF_14') | ~v1_partfun1('#skF_15', '#skF_13')), inference(demodulation, [status(thm), theory('equality')], [c_1202, c_18644])).
% 17.34/7.75  tff(c_18661, plain, (~v1_partfun1('#skF_15', '#skF_13')), inference(negUnitSimplification, [status(thm)], [c_6598, c_18660])).
% 17.34/7.75  tff(c_14411, plain, (v1_funct_2('#skF_15', '#skF_13', k2_relat_1('#skF_15')) | ~v1_funct_1('#skF_15') | ~v1_relat_1('#skF_15')), inference(superposition, [status(thm), theory('equality')], [c_14403, c_118])).
% 17.34/7.75  tff(c_14420, plain, (v1_funct_2('#skF_15', '#skF_13', k2_relat_1('#skF_15'))), inference(demodulation, [status(thm), theory('equality')], [c_14369, c_1202, c_14411])).
% 17.34/7.75  tff(c_19381, plain, (![C_956, A_957, B_958]: (v1_partfun1(C_956, A_957) | ~v1_funct_2(C_956, A_957, B_958) | ~v1_funct_1(C_956) | ~m1_subset_1(C_956, k1_zfmisc_1(k2_zfmisc_1(A_957, B_958))) | v1_xboole_0(B_958))), inference(cnfTransformation, [status(thm)], [f_146])).
% 17.34/7.75  tff(c_19399, plain, (v1_partfun1('#skF_15', '#skF_13') | ~v1_funct_2('#skF_15', '#skF_13', k2_relat_1('#skF_15')) | ~v1_funct_1('#skF_15') | v1_xboole_0(k2_relat_1('#skF_15'))), inference(resolution, [status(thm)], [c_14418, c_19381])).
% 17.34/7.75  tff(c_19437, plain, (v1_partfun1('#skF_15', '#skF_13') | v1_xboole_0(k2_relat_1('#skF_15'))), inference(demodulation, [status(thm), theory('equality')], [c_1202, c_14420, c_19399])).
% 17.34/7.75  tff(c_19439, plain, $false, inference(negUnitSimplification, [status(thm)], [c_14456, c_18661, c_19437])).
% 17.34/7.75  tff(c_19440, plain, (v1_xboole_0('#skF_15')), inference(splitRight, [status(thm)], [c_14452])).
% 17.34/7.75  tff(c_19455, plain, (k1_xboole_0='#skF_15'), inference(resolution, [status(thm)], [c_19440, c_1232])).
% 17.34/7.75  tff(c_19464, plain, $false, inference(negUnitSimplification, [status(thm)], [c_13320, c_19455])).
% 17.34/7.75  tff(c_19466, plain, (k1_xboole_0='#skF_15'), inference(splitRight, [status(thm)], [c_13301])).
% 17.34/7.75  tff(c_19465, plain, (k1_xboole_0='#skF_13' | k1_xboole_0='#skF_14'), inference(splitRight, [status(thm)], [c_13301])).
% 17.34/7.75  tff(c_19484, plain, ('#skF_15'='#skF_13' | '#skF_15'='#skF_14'), inference(demodulation, [status(thm), theory('equality')], [c_19466, c_19466, c_19465])).
% 17.34/7.75  tff(c_19485, plain, ('#skF_15'='#skF_14'), inference(splitLeft, [status(thm)], [c_19484])).
% 17.34/7.75  tff(c_19493, plain, (r2_hidden('#skF_14', k1_funct_2('#skF_13', '#skF_14'))), inference(demodulation, [status(thm), theory('equality')], [c_19485, c_124])).
% 17.34/7.75  tff(c_20336, plain, (![A_1026, B_1027, D_1028]: ('#skF_12'(A_1026, B_1027, k1_funct_2(A_1026, B_1027), D_1028)=D_1028 | ~r2_hidden(D_1028, k1_funct_2(A_1026, B_1027)))), inference(cnfTransformation, [status(thm)], [f_162])).
% 17.34/7.75  tff(c_20353, plain, ('#skF_12'('#skF_13', '#skF_14', k1_funct_2('#skF_13', '#skF_14'), '#skF_14')='#skF_14'), inference(resolution, [status(thm)], [c_19493, c_20336])).
% 17.34/7.75  tff(c_20490, plain, (![A_1042, B_1043, D_1044]: (v1_relat_1('#skF_12'(A_1042, B_1043, k1_funct_2(A_1042, B_1043), D_1044)) | ~r2_hidden(D_1044, k1_funct_2(A_1042, B_1043)))), inference(cnfTransformation, [status(thm)], [f_162])).
% 17.34/7.75  tff(c_20499, plain, (v1_relat_1('#skF_14') | ~r2_hidden('#skF_14', k1_funct_2('#skF_13', '#skF_14'))), inference(superposition, [status(thm), theory('equality')], [c_20353, c_20490])).
% 17.34/7.75  tff(c_20503, plain, (v1_relat_1('#skF_14')), inference(demodulation, [status(thm), theory('equality')], [c_19493, c_20499])).
% 17.34/7.75  tff(c_19471, plain, (![A_28]: (k2_relat_1(A_28)='#skF_15' | k1_relat_1(A_28)!='#skF_15' | ~v1_relat_1(A_28))), inference(demodulation, [status(thm), theory('equality')], [c_19466, c_19466, c_44])).
% 17.34/7.75  tff(c_20414, plain, (![A_28]: (k2_relat_1(A_28)='#skF_14' | k1_relat_1(A_28)!='#skF_14' | ~v1_relat_1(A_28))), inference(demodulation, [status(thm), theory('equality')], [c_19485, c_19485, c_19471])).
% 17.34/7.75  tff(c_20510, plain, (k2_relat_1('#skF_14')='#skF_14' | k1_relat_1('#skF_14')!='#skF_14'), inference(resolution, [status(thm)], [c_20503, c_20414])).
% 17.34/7.75  tff(c_20512, plain, (k1_relat_1('#skF_14')!='#skF_14'), inference(splitLeft, [status(thm)], [c_20510])).
% 17.34/7.75  tff(c_19472, plain, (![A_28]: (k1_relat_1(A_28)='#skF_15' | k2_relat_1(A_28)!='#skF_15' | ~v1_relat_1(A_28))), inference(demodulation, [status(thm), theory('equality')], [c_19466, c_19466, c_42])).
% 17.34/7.75  tff(c_20412, plain, (![A_28]: (k1_relat_1(A_28)='#skF_14' | k2_relat_1(A_28)!='#skF_14' | ~v1_relat_1(A_28))), inference(demodulation, [status(thm), theory('equality')], [c_19485, c_19485, c_19472])).
% 17.34/7.75  tff(c_20511, plain, (k1_relat_1('#skF_14')='#skF_14' | k2_relat_1('#skF_14')!='#skF_14'), inference(resolution, [status(thm)], [c_20503, c_20412])).
% 17.34/7.75  tff(c_20513, plain, (k2_relat_1('#skF_14')!='#skF_14'), inference(negUnitSimplification, [status(thm)], [c_20512, c_20511])).
% 17.34/7.75  tff(c_19478, plain, (v1_xboole_0('#skF_15')), inference(demodulation, [status(thm), theory('equality')], [c_19466, c_12])).
% 17.34/7.75  tff(c_19486, plain, (v1_xboole_0('#skF_14')), inference(demodulation, [status(thm), theory('equality')], [c_19485, c_19478])).
% 17.34/7.75  tff(c_21962, plain, (![A_1110, B_1111, D_1112]: (r1_tarski(k2_relat_1('#skF_12'(A_1110, B_1111, k1_funct_2(A_1110, B_1111), D_1112)), B_1111) | ~r2_hidden(D_1112, k1_funct_2(A_1110, B_1111)))), inference(cnfTransformation, [status(thm)], [f_162])).
% 17.34/7.75  tff(c_21994, plain, (r1_tarski(k2_relat_1('#skF_14'), '#skF_14') | ~r2_hidden('#skF_14', k1_funct_2('#skF_13', '#skF_14'))), inference(superposition, [status(thm), theory('equality')], [c_20353, c_21962])).
% 17.34/7.75  tff(c_22005, plain, (r1_tarski(k2_relat_1('#skF_14'), '#skF_14')), inference(demodulation, [status(thm), theory('equality')], [c_19493, c_21994])).
% 17.34/7.75  tff(c_14, plain, (![A_10]: (r2_hidden('#skF_3'(A_10), A_10) | k1_xboole_0=A_10)), inference(cnfTransformation, [status(thm)], [f_47])).
% 17.34/7.75  tff(c_19474, plain, (![A_10]: (r2_hidden('#skF_3'(A_10), A_10) | A_10='#skF_15')), inference(demodulation, [status(thm), theory('equality')], [c_19466, c_14])).
% 17.34/7.75  tff(c_19705, plain, (![A_10]: (r2_hidden('#skF_3'(A_10), A_10) | A_10='#skF_14')), inference(demodulation, [status(thm), theory('equality')], [c_19485, c_19474])).
% 17.34/7.75  tff(c_19634, plain, (![C_968, B_969, A_970]: (~v1_xboole_0(C_968) | ~m1_subset_1(B_969, k1_zfmisc_1(C_968)) | ~r2_hidden(A_970, B_969))), inference(cnfTransformation, [status(thm)], [f_82])).
% 17.34/7.75  tff(c_19939, plain, (![B_995, A_996, A_997]: (~v1_xboole_0(B_995) | ~r2_hidden(A_996, A_997) | ~r1_tarski(A_997, B_995))), inference(resolution, [status(thm)], [c_36, c_19634])).
% 17.34/7.75  tff(c_19950, plain, (![B_995, A_10]: (~v1_xboole_0(B_995) | ~r1_tarski(A_10, B_995) | A_10='#skF_14')), inference(resolution, [status(thm)], [c_19705, c_19939])).
% 17.34/7.75  tff(c_22013, plain, (~v1_xboole_0('#skF_14') | k2_relat_1('#skF_14')='#skF_14'), inference(resolution, [status(thm)], [c_22005, c_19950])).
% 17.34/7.75  tff(c_22034, plain, (k2_relat_1('#skF_14')='#skF_14'), inference(demodulation, [status(thm), theory('equality')], [c_19486, c_22013])).
% 17.34/7.75  tff(c_22036, plain, $false, inference(negUnitSimplification, [status(thm)], [c_20513, c_22034])).
% 17.34/7.75  tff(c_22038, plain, (k1_relat_1('#skF_14')='#skF_14'), inference(splitRight, [status(thm)], [c_20510])).
% 17.34/7.75  tff(c_22333, plain, (![A_1135, B_1136, D_1137]: (k1_relat_1('#skF_12'(A_1135, B_1136, k1_funct_2(A_1135, B_1136), D_1137))=A_1135 | ~r2_hidden(D_1137, k1_funct_2(A_1135, B_1136)))), inference(cnfTransformation, [status(thm)], [f_162])).
% 17.34/7.75  tff(c_22357, plain, (k1_relat_1('#skF_14')='#skF_13' | ~r2_hidden('#skF_14', k1_funct_2('#skF_13', '#skF_14'))), inference(superposition, [status(thm), theory('equality')], [c_20353, c_22333])).
% 17.34/7.75  tff(c_22363, plain, ('#skF_14'='#skF_13'), inference(demodulation, [status(thm), theory('equality')], [c_19493, c_22038, c_22357])).
% 17.34/7.75  tff(c_19491, plain, (~v1_funct_2('#skF_14', '#skF_13', '#skF_14')), inference(demodulation, [status(thm), theory('equality')], [c_19485, c_6598])).
% 17.34/7.75  tff(c_22397, plain, (~v1_funct_2('#skF_13', '#skF_13', '#skF_13')), inference(demodulation, [status(thm), theory('equality')], [c_22363, c_22363, c_19491])).
% 17.34/7.75  tff(c_19492, plain, (v1_funct_1('#skF_14')), inference(demodulation, [status(thm), theory('equality')], [c_19485, c_1202])).
% 17.34/7.75  tff(c_22037, plain, (k2_relat_1('#skF_14')='#skF_14'), inference(splitRight, [status(thm)], [c_20510])).
% 17.34/7.75  tff(c_22064, plain, (v1_funct_2('#skF_14', '#skF_14', k2_relat_1('#skF_14')) | ~v1_funct_1('#skF_14') | ~v1_relat_1('#skF_14')), inference(superposition, [status(thm), theory('equality')], [c_22038, c_118])).
% 17.34/7.75  tff(c_22073, plain, (v1_funct_2('#skF_14', '#skF_14', '#skF_14')), inference(demodulation, [status(thm), theory('equality')], [c_20503, c_19492, c_22037, c_22064])).
% 17.34/7.75  tff(c_22370, plain, (v1_funct_2('#skF_13', '#skF_13', '#skF_13')), inference(demodulation, [status(thm), theory('equality')], [c_22363, c_22363, c_22363, c_22073])).
% 17.34/7.75  tff(c_22815, plain, $false, inference(negUnitSimplification, [status(thm)], [c_22397, c_22370])).
% 17.34/7.75  tff(c_22816, plain, ('#skF_15'='#skF_13'), inference(splitRight, [status(thm)], [c_19484])).
% 17.34/7.75  tff(c_6678, plain, (![A_462, B_463]: (r2_hidden('#skF_2'(A_462, B_463), A_462) | r1_tarski(A_462, B_463))), inference(cnfTransformation, [status(thm)], [f_38])).
% 17.34/7.75  tff(c_24, plain, (![A_14]: (k2_zfmisc_1(A_14, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_59])).
% 17.34/7.75  tff(c_1203, plain, (![A_212, B_213]: (~r2_hidden(A_212, k2_zfmisc_1(A_212, B_213)))), inference(cnfTransformation, [status(thm)], [f_62])).
% 17.34/7.75  tff(c_1206, plain, (![A_14]: (~r2_hidden(A_14, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_24, c_1203])).
% 17.34/7.75  tff(c_6692, plain, (![B_463]: (r1_tarski(k1_xboole_0, B_463))), inference(resolution, [status(thm)], [c_6678, c_1206])).
% 17.34/7.75  tff(c_6615, plain, (![A_452]: (m1_subset_1(k6_partfun1(A_452), k1_zfmisc_1(k2_zfmisc_1(A_452, A_452))))), inference(cnfTransformation, [status(thm)], [f_166])).
% 17.34/7.75  tff(c_6622, plain, (m1_subset_1(k6_partfun1(k1_xboole_0), k1_zfmisc_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_24, c_6615])).
% 17.34/7.75  tff(c_34, plain, (![A_22, B_23]: (r1_tarski(A_22, B_23) | ~m1_subset_1(A_22, k1_zfmisc_1(B_23)))), inference(cnfTransformation, [status(thm)], [f_75])).
% 17.34/7.75  tff(c_6631, plain, (r1_tarski(k6_partfun1(k1_xboole_0), k1_xboole_0)), inference(resolution, [status(thm)], [c_6622, c_34])).
% 17.34/7.75  tff(c_6659, plain, (k6_partfun1(k1_xboole_0)=k1_xboole_0 | ~r1_tarski(k1_xboole_0, k6_partfun1(k1_xboole_0))), inference(resolution, [status(thm)], [c_6631, c_6647])).
% 17.34/7.75  tff(c_6666, plain, (~r1_tarski(k1_xboole_0, k6_partfun1(k1_xboole_0))), inference(splitLeft, [status(thm)], [c_6659])).
% 17.34/7.75  tff(c_6696, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6692, c_6666])).
% 17.34/7.75  tff(c_6697, plain, (k6_partfun1(k1_xboole_0)=k1_xboole_0), inference(splitRight, [status(thm)], [c_6659])).
% 17.34/7.75  tff(c_19469, plain, (k6_partfun1('#skF_15')='#skF_15'), inference(demodulation, [status(thm), theory('equality')], [c_19466, c_19466, c_6697])).
% 17.34/7.75  tff(c_22850, plain, (k6_partfun1('#skF_13')='#skF_13'), inference(demodulation, [status(thm), theory('equality')], [c_22816, c_22816, c_19469])).
% 17.34/7.75  tff(c_112, plain, (![A_103]: (v1_partfun1(k6_partfun1(A_103), A_103))), inference(cnfTransformation, [status(thm)], [f_166])).
% 17.34/7.75  tff(c_22860, plain, (v1_partfun1('#skF_13', '#skF_13')), inference(superposition, [status(thm), theory('equality')], [c_22850, c_112])).
% 17.34/7.75  tff(c_22824, plain, (v1_funct_1('#skF_13')), inference(demodulation, [status(thm), theory('equality')], [c_22816, c_1202])).
% 17.34/7.75  tff(c_22895, plain, (![A_1153, B_1154]: (r2_hidden('#skF_2'(A_1153, B_1154), A_1153) | r1_tarski(A_1153, B_1154))), inference(cnfTransformation, [status(thm)], [f_38])).
% 17.34/7.75  tff(c_19475, plain, (![A_14]: (~r2_hidden(A_14, '#skF_15'))), inference(demodulation, [status(thm), theory('equality')], [c_19466, c_1206])).
% 17.34/7.75  tff(c_22873, plain, (![A_14]: (~r2_hidden(A_14, '#skF_13'))), inference(demodulation, [status(thm), theory('equality')], [c_22816, c_19475])).
% 17.34/7.75  tff(c_22907, plain, (![B_1154]: (r1_tarski('#skF_13', B_1154))), inference(resolution, [status(thm)], [c_22895, c_22873])).
% 17.34/7.75  tff(c_26263, plain, (![C_1337, A_1338, B_1339]: (v1_funct_2(C_1337, A_1338, B_1339) | ~v1_partfun1(C_1337, A_1338) | ~v1_funct_1(C_1337) | ~m1_subset_1(C_1337, k1_zfmisc_1(k2_zfmisc_1(A_1338, B_1339))))), inference(cnfTransformation, [status(thm)], [f_132])).
% 17.34/7.75  tff(c_65229, plain, (![A_1839, A_1840, B_1841]: (v1_funct_2(A_1839, A_1840, B_1841) | ~v1_partfun1(A_1839, A_1840) | ~v1_funct_1(A_1839) | ~r1_tarski(A_1839, k2_zfmisc_1(A_1840, B_1841)))), inference(resolution, [status(thm)], [c_36, c_26263])).
% 17.34/7.75  tff(c_65398, plain, (![A_1840, B_1841]: (v1_funct_2('#skF_13', A_1840, B_1841) | ~v1_partfun1('#skF_13', A_1840) | ~v1_funct_1('#skF_13'))), inference(resolution, [status(thm)], [c_22907, c_65229])).
% 17.34/7.75  tff(c_65446, plain, (![A_1842, B_1843]: (v1_funct_2('#skF_13', A_1842, B_1843) | ~v1_partfun1('#skF_13', A_1842))), inference(demodulation, [status(thm), theory('equality')], [c_22824, c_65398])).
% 17.34/7.75  tff(c_22823, plain, (~v1_funct_2('#skF_13', '#skF_13', '#skF_14')), inference(demodulation, [status(thm), theory('equality')], [c_22816, c_6598])).
% 17.34/7.75  tff(c_65449, plain, (~v1_partfun1('#skF_13', '#skF_13')), inference(resolution, [status(thm)], [c_65446, c_22823])).
% 17.34/7.75  tff(c_65453, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_22860, c_65449])).
% 17.34/7.75  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 17.34/7.75  
% 17.34/7.75  Inference rules
% 17.34/7.75  ----------------------
% 17.34/7.75  #Ref     : 0
% 17.34/7.75  #Sup     : 16507
% 17.34/7.75  #Fact    : 0
% 17.34/7.75  #Define  : 0
% 17.34/7.75  #Split   : 41
% 17.34/7.75  #Chain   : 0
% 17.34/7.75  #Close   : 0
% 17.34/7.75  
% 17.34/7.75  Ordering : KBO
% 17.34/7.75  
% 17.34/7.75  Simplification rules
% 17.34/7.75  ----------------------
% 17.34/7.75  #Subsume      : 5476
% 17.34/7.75  #Demod        : 15332
% 17.34/7.75  #Tautology    : 6906
% 17.34/7.75  #SimpNegUnit  : 44
% 17.34/7.75  #BackRed      : 174
% 17.34/7.75  
% 17.34/7.75  #Partial instantiations: 0
% 17.34/7.75  #Strategies tried      : 1
% 17.34/7.75  
% 17.34/7.75  Timing (in seconds)
% 17.34/7.75  ----------------------
% 17.34/7.75  Preprocessing        : 0.40
% 17.34/7.75  Parsing              : 0.20
% 17.34/7.75  CNF conversion       : 0.04
% 17.34/7.75  Main loop            : 6.56
% 17.34/7.75  Inferencing          : 1.54
% 17.34/7.75  Reduction            : 1.92
% 17.34/7.75  Demodulation         : 1.34
% 17.34/7.75  BG Simplification    : 0.16
% 17.34/7.75  Subsumption          : 2.53
% 17.34/7.75  Abstraction          : 0.25
% 17.34/7.75  MUC search           : 0.00
% 17.34/7.75  Cooper               : 0.00
% 17.34/7.75  Total                : 7.03
% 17.34/7.75  Index Insertion      : 0.00
% 17.34/7.75  Index Deletion       : 0.00
% 17.34/7.75  Index Matching       : 0.00
% 17.34/7.75  BG Taut test         : 0.00
%------------------------------------------------------------------------------
