%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:16:41 EST 2020

% Result     : Theorem 10.83s
% Output     : CNFRefutation 10.95s
% Verified   : 
% Statistics : Number of formulae       :  137 ( 701 expanded)
%              Number of leaves         :   48 ( 252 expanded)
%              Depth                    :   15
%              Number of atoms          :  211 (1635 expanded)
%              Number of equality atoms :   30 ( 381 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v1_partfun1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k4_tarski > k2_zfmisc_1 > k1_funct_2 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_13 > #skF_2 > #skF_6 > #skF_15 > #skF_1 > #skF_12 > #skF_3 > #skF_8 > #skF_16 > #skF_14 > #skF_7 > #skF_11 > #skF_9 > #skF_5 > #skF_4 > #skF_10

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_13',type,(
    '#skF_13': ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i ) > $i )).

tff('#skF_15',type,(
    '#skF_15': $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_12',type,(
    '#skF_12': ( $i * $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_8',type,(
    '#skF_8': ( $i * $i * $i * $i ) > $i )).

tff('#skF_16',type,(
    '#skF_16': $i )).

tff('#skF_14',type,(
    '#skF_14': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff(v1_partfun1,type,(
    v1_partfun1: ( $i * $i ) > $o )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i * $i * $i ) > $i )).

tff('#skF_11',type,(
    '#skF_11': ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': ( $i * $i * $i ) > $i )).

tff(k1_funct_2,type,(
    k1_funct_2: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff('#skF_10',type,(
    '#skF_10': ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_155,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r2_hidden(C,k1_funct_2(A,B))
       => ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t121_funct_2)).

tff(f_119,axiom,(
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

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_58,axiom,(
    ! [A,B] :
      ( B = k1_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(C,D),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_1)).

tff(f_32,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_40,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_46,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_66,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( ( r1_tarski(k1_relat_1(C),A)
          & r1_tarski(k2_relat_1(C),B) )
       => m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_relset_1)).

tff(f_89,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( ( v1_funct_1(C)
          & v1_partfun1(C,A) )
       => ( v1_funct_1(C)
          & v1_funct_2(C,A,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_funct_2)).

tff(f_129,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_funct_1(A)
        & v1_funct_2(A,k1_relat_1(A),k2_relat_1(A))
        & m1_subset_1(A,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A)))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_funct_2)).

tff(f_103,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => ( ( v1_funct_1(C)
              & v1_funct_2(C,A,B) )
           => ( v1_funct_1(C)
              & v1_partfun1(C,A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc5_funct_2)).

tff(f_79,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,C)))
     => ~ ( r2_hidden(A,D)
          & ! [E,F] :
              ~ ( A = k4_tarski(E,F)
                & r2_hidden(E,B)
                & r2_hidden(F,C) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_relset_1)).

tff(f_146,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( ( k1_relat_1(C) = A
          & ! [D] :
              ( r2_hidden(D,A)
             => r2_hidden(k1_funct_1(C,D),B) ) )
       => ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_funct_2)).

tff(c_104,plain,(
    r2_hidden('#skF_16',k1_funct_2('#skF_14','#skF_15')) ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_7435,plain,(
    ! [A_263,B_264,D_265] :
      ( '#skF_12'(A_263,B_264,k1_funct_2(A_263,B_264),D_265) = D_265
      | ~ r2_hidden(D_265,k1_funct_2(A_263,B_264)) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_7450,plain,(
    '#skF_12'('#skF_14','#skF_15',k1_funct_2('#skF_14','#skF_15'),'#skF_16') = '#skF_16' ),
    inference(resolution,[status(thm)],[c_104,c_7435])).

tff(c_7906,plain,(
    ! [A_277,B_278,D_279] :
      ( k1_relat_1('#skF_12'(A_277,B_278,k1_funct_2(A_277,B_278),D_279)) = A_277
      | ~ r2_hidden(D_279,k1_funct_2(A_277,B_278)) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_7960,plain,
    ( k1_relat_1('#skF_16') = '#skF_14'
    | ~ r2_hidden('#skF_16',k1_funct_2('#skF_14','#skF_15')) ),
    inference(superposition,[status(thm),theory(equality)],[c_7450,c_7906])).

tff(c_7964,plain,(
    k1_relat_1('#skF_16') = '#skF_14' ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_7960])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_7257,plain,(
    ! [C_247,A_248] :
      ( r2_hidden(k4_tarski(C_247,'#skF_6'(A_248,k1_relat_1(A_248),C_247)),A_248)
      | ~ r2_hidden(C_247,k1_relat_1(A_248)) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_7267,plain,(
    ! [A_252,C_253] :
      ( ~ v1_xboole_0(A_252)
      | ~ r2_hidden(C_253,k1_relat_1(A_252)) ) ),
    inference(resolution,[status(thm)],[c_7257,c_2])).

tff(c_7282,plain,(
    ! [A_252] :
      ( ~ v1_xboole_0(A_252)
      | v1_xboole_0(k1_relat_1(A_252)) ) ),
    inference(resolution,[status(thm)],[c_4,c_7267])).

tff(c_7995,plain,
    ( ~ v1_xboole_0('#skF_16')
    | v1_xboole_0('#skF_14') ),
    inference(superposition,[status(thm),theory(equality)],[c_7964,c_7282])).

tff(c_8021,plain,(
    ~ v1_xboole_0('#skF_16') ),
    inference(splitLeft,[status(thm)],[c_7995])).

tff(c_6,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_8,plain,(
    ! [A_5] :
      ( r2_hidden('#skF_2'(A_5),A_5)
      | k1_xboole_0 = A_5 ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_7283,plain,(
    ! [A_254] :
      ( ~ v1_xboole_0(A_254)
      | k1_relat_1(A_254) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_8,c_7267])).

tff(c_7287,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_6,c_7283])).

tff(c_7265,plain,(
    ! [A_248,C_247] :
      ( ~ v1_xboole_0(A_248)
      | ~ r2_hidden(C_247,k1_relat_1(A_248)) ) ),
    inference(resolution,[status(thm)],[c_7257,c_2])).

tff(c_7291,plain,(
    ! [C_247] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | ~ r2_hidden(C_247,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_7287,c_7265])).

tff(c_7307,plain,(
    ! [C_247] : ~ r2_hidden(C_247,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_7291])).

tff(c_480,plain,(
    ! [A_130,B_131,D_132] :
      ( '#skF_12'(A_130,B_131,k1_funct_2(A_130,B_131),D_132) = D_132
      | ~ r2_hidden(D_132,k1_funct_2(A_130,B_131)) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_491,plain,(
    '#skF_12'('#skF_14','#skF_15',k1_funct_2('#skF_14','#skF_15'),'#skF_16') = '#skF_16' ),
    inference(resolution,[status(thm)],[c_104,c_480])).

tff(c_58,plain,(
    ! [A_46,B_47,D_62] :
      ( v1_relat_1('#skF_12'(A_46,B_47,k1_funct_2(A_46,B_47),D_62))
      | ~ r2_hidden(D_62,k1_funct_2(A_46,B_47)) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_498,plain,
    ( v1_relat_1('#skF_16')
    | ~ r2_hidden('#skF_16',k1_funct_2('#skF_14','#skF_15')) ),
    inference(superposition,[status(thm),theory(equality)],[c_491,c_58])).

tff(c_504,plain,(
    v1_relat_1('#skF_16') ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_498])).

tff(c_14,plain,(
    ! [B_8] : r1_tarski(B_8,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_519,plain,(
    ! [A_135,B_136,D_137] :
      ( k1_relat_1('#skF_12'(A_135,B_136,k1_funct_2(A_135,B_136),D_137)) = A_135
      | ~ r2_hidden(D_137,k1_funct_2(A_135,B_136)) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_540,plain,
    ( k1_relat_1('#skF_16') = '#skF_14'
    | ~ r2_hidden('#skF_16',k1_funct_2('#skF_14','#skF_15')) ),
    inference(superposition,[status(thm),theory(equality)],[c_491,c_519])).

tff(c_544,plain,(
    k1_relat_1('#skF_16') = '#skF_14' ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_540])).

tff(c_2445,plain,(
    ! [A_182,B_183,D_184] :
      ( r1_tarski(k2_relat_1('#skF_12'(A_182,B_183,k1_funct_2(A_182,B_183),D_184)),B_183)
      | ~ r2_hidden(D_184,k1_funct_2(A_182,B_183)) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_2450,plain,
    ( r1_tarski(k2_relat_1('#skF_16'),'#skF_15')
    | ~ r2_hidden('#skF_16',k1_funct_2('#skF_14','#skF_15')) ),
    inference(superposition,[status(thm),theory(equality)],[c_491,c_2445])).

tff(c_2453,plain,(
    r1_tarski(k2_relat_1('#skF_16'),'#skF_15') ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_2450])).

tff(c_7213,plain,(
    ! [C_241,A_242,B_243] :
      ( m1_subset_1(C_241,k1_zfmisc_1(k2_zfmisc_1(A_242,B_243)))
      | ~ r1_tarski(k2_relat_1(C_241),B_243)
      | ~ r1_tarski(k1_relat_1(C_241),A_242)
      | ~ v1_relat_1(C_241) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_102,plain,
    ( ~ m1_subset_1('#skF_16',k1_zfmisc_1(k2_zfmisc_1('#skF_14','#skF_15')))
    | ~ v1_funct_2('#skF_16','#skF_14','#skF_15')
    | ~ v1_funct_1('#skF_16') ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_129,plain,(
    ~ v1_funct_1('#skF_16') ),
    inference(splitLeft,[status(thm)],[c_102])).

tff(c_332,plain,(
    ! [A_108,B_109,D_110] :
      ( '#skF_12'(A_108,B_109,k1_funct_2(A_108,B_109),D_110) = D_110
      | ~ r2_hidden(D_110,k1_funct_2(A_108,B_109)) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_347,plain,(
    '#skF_12'('#skF_14','#skF_15',k1_funct_2('#skF_14','#skF_15'),'#skF_16') = '#skF_16' ),
    inference(resolution,[status(thm)],[c_104,c_332])).

tff(c_56,plain,(
    ! [A_46,B_47,D_62] :
      ( v1_funct_1('#skF_12'(A_46,B_47,k1_funct_2(A_46,B_47),D_62))
      | ~ r2_hidden(D_62,k1_funct_2(A_46,B_47)) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_438,plain,
    ( v1_funct_1('#skF_16')
    | ~ r2_hidden('#skF_16',k1_funct_2('#skF_14','#skF_15')) ),
    inference(superposition,[status(thm),theory(equality)],[c_347,c_56])).

tff(c_444,plain,(
    v1_funct_1('#skF_16') ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_438])).

tff(c_446,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_129,c_444])).

tff(c_447,plain,
    ( ~ v1_funct_2('#skF_16','#skF_14','#skF_15')
    | ~ m1_subset_1('#skF_16',k1_zfmisc_1(k2_zfmisc_1('#skF_14','#skF_15'))) ),
    inference(splitRight,[status(thm)],[c_102])).

tff(c_462,plain,(
    ~ m1_subset_1('#skF_16',k1_zfmisc_1(k2_zfmisc_1('#skF_14','#skF_15'))) ),
    inference(splitLeft,[status(thm)],[c_447])).

tff(c_7223,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_16'),'#skF_15')
    | ~ r1_tarski(k1_relat_1('#skF_16'),'#skF_14')
    | ~ v1_relat_1('#skF_16') ),
    inference(resolution,[status(thm)],[c_7213,c_462])).

tff(c_7236,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_504,c_14,c_544,c_2453,c_7223])).

tff(c_7237,plain,(
    ~ v1_funct_2('#skF_16','#skF_14','#skF_15') ),
    inference(splitRight,[status(thm)],[c_447])).

tff(c_448,plain,(
    v1_funct_1('#skF_16') ),
    inference(splitRight,[status(thm)],[c_102])).

tff(c_7238,plain,(
    m1_subset_1('#skF_16',k1_zfmisc_1(k2_zfmisc_1('#skF_14','#skF_15'))) ),
    inference(splitRight,[status(thm)],[c_447])).

tff(c_11364,plain,(
    ! [C_332,A_333,B_334] :
      ( v1_funct_2(C_332,A_333,B_334)
      | ~ v1_partfun1(C_332,A_333)
      | ~ v1_funct_1(C_332)
      | ~ m1_subset_1(C_332,k1_zfmisc_1(k2_zfmisc_1(A_333,B_334))) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_11373,plain,
    ( v1_funct_2('#skF_16','#skF_14','#skF_15')
    | ~ v1_partfun1('#skF_16','#skF_14')
    | ~ v1_funct_1('#skF_16') ),
    inference(resolution,[status(thm)],[c_7238,c_11364])).

tff(c_11384,plain,
    ( v1_funct_2('#skF_16','#skF_14','#skF_15')
    | ~ v1_partfun1('#skF_16','#skF_14') ),
    inference(demodulation,[status(thm),theory(equality)],[c_448,c_11373])).

tff(c_11385,plain,(
    ~ v1_partfun1('#skF_16','#skF_14') ),
    inference(negUnitSimplification,[status(thm)],[c_7237,c_11384])).

tff(c_7587,plain,(
    ! [A_269,B_270,D_271] :
      ( v1_relat_1('#skF_12'(A_269,B_270,k1_funct_2(A_269,B_270),D_271))
      | ~ r2_hidden(D_271,k1_funct_2(A_269,B_270)) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_7590,plain,
    ( v1_relat_1('#skF_16')
    | ~ r2_hidden('#skF_16',k1_funct_2('#skF_14','#skF_15')) ),
    inference(superposition,[status(thm),theory(equality)],[c_7450,c_7587])).

tff(c_7592,plain,(
    v1_relat_1('#skF_16') ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_7590])).

tff(c_86,plain,(
    ! [A_66] :
      ( v1_funct_2(A_66,k1_relat_1(A_66),k2_relat_1(A_66))
      | ~ v1_funct_1(A_66)
      | ~ v1_relat_1(A_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_8010,plain,
    ( v1_funct_2('#skF_16','#skF_14',k2_relat_1('#skF_16'))
    | ~ v1_funct_1('#skF_16')
    | ~ v1_relat_1('#skF_16') ),
    inference(superposition,[status(thm),theory(equality)],[c_7964,c_86])).

tff(c_8019,plain,(
    v1_funct_2('#skF_16','#skF_14',k2_relat_1('#skF_16')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7592,c_448,c_8010])).

tff(c_84,plain,(
    ! [A_66] :
      ( m1_subset_1(A_66,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_66),k2_relat_1(A_66))))
      | ~ v1_funct_1(A_66)
      | ~ v1_relat_1(A_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_8007,plain,
    ( m1_subset_1('#skF_16',k1_zfmisc_1(k2_zfmisc_1('#skF_14',k2_relat_1('#skF_16'))))
    | ~ v1_funct_1('#skF_16')
    | ~ v1_relat_1('#skF_16') ),
    inference(superposition,[status(thm),theory(equality)],[c_7964,c_84])).

tff(c_8017,plain,(
    m1_subset_1('#skF_16',k1_zfmisc_1(k2_zfmisc_1('#skF_14',k2_relat_1('#skF_16')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7592,c_448,c_8007])).

tff(c_19788,plain,(
    ! [C_459,A_460,B_461] :
      ( v1_partfun1(C_459,A_460)
      | ~ v1_funct_2(C_459,A_460,B_461)
      | ~ v1_funct_1(C_459)
      | ~ m1_subset_1(C_459,k1_zfmisc_1(k2_zfmisc_1(A_460,B_461)))
      | v1_xboole_0(B_461) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_19797,plain,
    ( v1_partfun1('#skF_16','#skF_14')
    | ~ v1_funct_2('#skF_16','#skF_14',k2_relat_1('#skF_16'))
    | ~ v1_funct_1('#skF_16')
    | v1_xboole_0(k2_relat_1('#skF_16')) ),
    inference(resolution,[status(thm)],[c_8017,c_19788])).

tff(c_19811,plain,
    ( v1_partfun1('#skF_16','#skF_14')
    | v1_xboole_0(k2_relat_1('#skF_16')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_448,c_8019,c_19797])).

tff(c_19812,plain,(
    v1_xboole_0(k2_relat_1('#skF_16')) ),
    inference(negUnitSimplification,[status(thm)],[c_11385,c_19811])).

tff(c_117,plain,(
    ! [A_75] :
      ( r2_hidden('#skF_2'(A_75),A_75)
      | k1_xboole_0 = A_75 ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_121,plain,(
    ! [A_75] :
      ( ~ v1_xboole_0(A_75)
      | k1_xboole_0 = A_75 ) ),
    inference(resolution,[status(thm)],[c_117,c_2])).

tff(c_19826,plain,(
    k2_relat_1('#skF_16') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_19812,c_121])).

tff(c_19843,plain,(
    m1_subset_1('#skF_16',k1_zfmisc_1(k2_zfmisc_1('#skF_14',k1_xboole_0))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_19826,c_8017])).

tff(c_34,plain,(
    ! [A_33,B_34,C_35,D_36] :
      ( r2_hidden('#skF_8'(A_33,B_34,C_35,D_36),C_35)
      | ~ r2_hidden(A_33,D_36)
      | ~ m1_subset_1(D_36,k1_zfmisc_1(k2_zfmisc_1(B_34,C_35))) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_19951,plain,(
    ! [A_33] :
      ( r2_hidden('#skF_8'(A_33,'#skF_14',k1_xboole_0,'#skF_16'),k1_xboole_0)
      | ~ r2_hidden(A_33,'#skF_16') ) ),
    inference(resolution,[status(thm)],[c_19843,c_34])).

tff(c_19974,plain,(
    ! [A_464] : ~ r2_hidden(A_464,'#skF_16') ),
    inference(negUnitSimplification,[status(thm)],[c_7307,c_19951])).

tff(c_20016,plain,(
    v1_xboole_0('#skF_16') ),
    inference(resolution,[status(thm)],[c_4,c_19974])).

tff(c_20031,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_8021,c_20016])).

tff(c_20032,plain,(
    v1_xboole_0('#skF_14') ),
    inference(splitRight,[status(thm)],[c_7995])).

tff(c_20041,plain,(
    k1_xboole_0 = '#skF_14' ),
    inference(resolution,[status(thm)],[c_20032,c_121])).

tff(c_20087,plain,(
    ! [C_247] : ~ r2_hidden(C_247,'#skF_14') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20041,c_7307])).

tff(c_20033,plain,(
    v1_xboole_0('#skF_16') ),
    inference(splitRight,[status(thm)],[c_7995])).

tff(c_20050,plain,(
    k1_xboole_0 = '#skF_16' ),
    inference(resolution,[status(thm)],[c_20033,c_121])).

tff(c_20098,plain,(
    '#skF_16' = '#skF_14' ),
    inference(demodulation,[status(thm),theory(equality)],[c_20041,c_20050])).

tff(c_20101,plain,(
    v1_relat_1('#skF_14') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20098,c_7592])).

tff(c_20107,plain,(
    v1_funct_1('#skF_14') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20098,c_448])).

tff(c_20100,plain,(
    k1_relat_1('#skF_14') = '#skF_14' ),
    inference(demodulation,[status(thm),theory(equality)],[c_20098,c_7964])).

tff(c_23931,plain,(
    ! [C_557,B_558] :
      ( r2_hidden('#skF_13'(k1_relat_1(C_557),B_558,C_557),k1_relat_1(C_557))
      | v1_funct_2(C_557,k1_relat_1(C_557),B_558)
      | ~ v1_funct_1(C_557)
      | ~ v1_relat_1(C_557) ) ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_24018,plain,(
    ! [B_558] :
      ( r2_hidden('#skF_13'('#skF_14',B_558,'#skF_14'),k1_relat_1('#skF_14'))
      | v1_funct_2('#skF_14',k1_relat_1('#skF_14'),B_558)
      | ~ v1_funct_1('#skF_14')
      | ~ v1_relat_1('#skF_14') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20100,c_23931])).

tff(c_24044,plain,(
    ! [B_558] :
      ( r2_hidden('#skF_13'('#skF_14',B_558,'#skF_14'),'#skF_14')
      | v1_funct_2('#skF_14','#skF_14',B_558) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20101,c_20107,c_20100,c_20100,c_24018])).

tff(c_24045,plain,(
    ! [B_558] : v1_funct_2('#skF_14','#skF_14',B_558) ),
    inference(negUnitSimplification,[status(thm)],[c_20087,c_24044])).

tff(c_20106,plain,(
    ~ v1_funct_2('#skF_14','#skF_14','#skF_15') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20098,c_7237])).

tff(c_24052,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_24045,c_20106])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n011.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 10:01:42 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 10.83/3.65  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.83/3.66  
% 10.83/3.66  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.83/3.66  %$ v1_funct_2 > v1_partfun1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k4_tarski > k2_zfmisc_1 > k1_funct_2 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_13 > #skF_2 > #skF_6 > #skF_15 > #skF_1 > #skF_12 > #skF_3 > #skF_8 > #skF_16 > #skF_14 > #skF_7 > #skF_11 > #skF_9 > #skF_5 > #skF_4 > #skF_10
% 10.83/3.66  
% 10.83/3.66  %Foreground sorts:
% 10.83/3.66  
% 10.83/3.66  
% 10.83/3.66  %Background operators:
% 10.83/3.66  
% 10.83/3.66  
% 10.83/3.66  %Foreground operators:
% 10.83/3.66  tff('#skF_13', type, '#skF_13': ($i * $i * $i) > $i).
% 10.83/3.66  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 10.83/3.66  tff('#skF_2', type, '#skF_2': $i > $i).
% 10.83/3.66  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 10.83/3.66  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 10.83/3.66  tff('#skF_6', type, '#skF_6': ($i * $i * $i) > $i).
% 10.83/3.66  tff('#skF_15', type, '#skF_15': $i).
% 10.83/3.66  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 10.83/3.66  tff('#skF_1', type, '#skF_1': $i > $i).
% 10.83/3.66  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 10.83/3.66  tff('#skF_12', type, '#skF_12': ($i * $i * $i * $i) > $i).
% 10.83/3.66  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 10.83/3.66  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 10.83/3.66  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 10.83/3.66  tff('#skF_8', type, '#skF_8': ($i * $i * $i * $i) > $i).
% 10.83/3.66  tff('#skF_16', type, '#skF_16': $i).
% 10.83/3.66  tff('#skF_14', type, '#skF_14': $i).
% 10.83/3.66  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 10.83/3.66  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 10.83/3.66  tff('#skF_7', type, '#skF_7': ($i * $i * $i * $i) > $i).
% 10.83/3.66  tff('#skF_11', type, '#skF_11': ($i * $i * $i) > $i).
% 10.83/3.66  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 10.83/3.66  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 10.83/3.66  tff('#skF_9', type, '#skF_9': ($i * $i * $i) > $i).
% 10.83/3.66  tff(k1_funct_2, type, k1_funct_2: ($i * $i) > $i).
% 10.83/3.66  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 10.83/3.66  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 10.83/3.66  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 10.83/3.66  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 10.83/3.66  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 10.83/3.66  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 10.83/3.66  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 10.83/3.66  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 10.83/3.66  tff('#skF_10', type, '#skF_10': ($i * $i * $i) > $i).
% 10.83/3.66  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 10.83/3.66  
% 10.95/3.68  tff(f_155, negated_conjecture, ~(![A, B, C]: (r2_hidden(C, k1_funct_2(A, B)) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t121_funct_2)).
% 10.95/3.68  tff(f_119, axiom, (![A, B, C]: ((C = k1_funct_2(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (?[E]: ((((v1_relat_1(E) & v1_funct_1(E)) & (D = E)) & (k1_relat_1(E) = A)) & r1_tarski(k2_relat_1(E), B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_funct_2)).
% 10.95/3.68  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 10.95/3.68  tff(f_58, axiom, (![A, B]: ((B = k1_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(C, D), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_relat_1)).
% 10.95/3.68  tff(f_32, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 10.95/3.68  tff(f_40, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 10.95/3.68  tff(f_46, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 10.95/3.68  tff(f_66, axiom, (![A, B, C]: (v1_relat_1(C) => ((r1_tarski(k1_relat_1(C), A) & r1_tarski(k2_relat_1(C), B)) => m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_relset_1)).
% 10.95/3.68  tff(f_89, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v1_partfun1(C, A)) => (v1_funct_1(C) & v1_funct_2(C, A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_funct_2)).
% 10.95/3.68  tff(f_129, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => ((v1_funct_1(A) & v1_funct_2(A, k1_relat_1(A), k2_relat_1(A))) & m1_subset_1(A, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_funct_2)).
% 10.95/3.68  tff(f_103, axiom, (![A, B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) => (v1_funct_1(C) & v1_partfun1(C, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc5_funct_2)).
% 10.95/3.68  tff(f_79, axiom, (![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C))) => ~(r2_hidden(A, D) & (![E, F]: ~(((A = k4_tarski(E, F)) & r2_hidden(E, B)) & r2_hidden(F, C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_relset_1)).
% 10.95/3.68  tff(f_146, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (((k1_relat_1(C) = A) & (![D]: (r2_hidden(D, A) => r2_hidden(k1_funct_1(C, D), B)))) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_funct_2)).
% 10.95/3.68  tff(c_104, plain, (r2_hidden('#skF_16', k1_funct_2('#skF_14', '#skF_15'))), inference(cnfTransformation, [status(thm)], [f_155])).
% 10.95/3.68  tff(c_7435, plain, (![A_263, B_264, D_265]: ('#skF_12'(A_263, B_264, k1_funct_2(A_263, B_264), D_265)=D_265 | ~r2_hidden(D_265, k1_funct_2(A_263, B_264)))), inference(cnfTransformation, [status(thm)], [f_119])).
% 10.95/3.68  tff(c_7450, plain, ('#skF_12'('#skF_14', '#skF_15', k1_funct_2('#skF_14', '#skF_15'), '#skF_16')='#skF_16'), inference(resolution, [status(thm)], [c_104, c_7435])).
% 10.95/3.68  tff(c_7906, plain, (![A_277, B_278, D_279]: (k1_relat_1('#skF_12'(A_277, B_278, k1_funct_2(A_277, B_278), D_279))=A_277 | ~r2_hidden(D_279, k1_funct_2(A_277, B_278)))), inference(cnfTransformation, [status(thm)], [f_119])).
% 10.95/3.68  tff(c_7960, plain, (k1_relat_1('#skF_16')='#skF_14' | ~r2_hidden('#skF_16', k1_funct_2('#skF_14', '#skF_15'))), inference(superposition, [status(thm), theory('equality')], [c_7450, c_7906])).
% 10.95/3.68  tff(c_7964, plain, (k1_relat_1('#skF_16')='#skF_14'), inference(demodulation, [status(thm), theory('equality')], [c_104, c_7960])).
% 10.95/3.68  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 10.95/3.68  tff(c_7257, plain, (![C_247, A_248]: (r2_hidden(k4_tarski(C_247, '#skF_6'(A_248, k1_relat_1(A_248), C_247)), A_248) | ~r2_hidden(C_247, k1_relat_1(A_248)))), inference(cnfTransformation, [status(thm)], [f_58])).
% 10.95/3.68  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 10.95/3.68  tff(c_7267, plain, (![A_252, C_253]: (~v1_xboole_0(A_252) | ~r2_hidden(C_253, k1_relat_1(A_252)))), inference(resolution, [status(thm)], [c_7257, c_2])).
% 10.95/3.68  tff(c_7282, plain, (![A_252]: (~v1_xboole_0(A_252) | v1_xboole_0(k1_relat_1(A_252)))), inference(resolution, [status(thm)], [c_4, c_7267])).
% 10.95/3.68  tff(c_7995, plain, (~v1_xboole_0('#skF_16') | v1_xboole_0('#skF_14')), inference(superposition, [status(thm), theory('equality')], [c_7964, c_7282])).
% 10.95/3.68  tff(c_8021, plain, (~v1_xboole_0('#skF_16')), inference(splitLeft, [status(thm)], [c_7995])).
% 10.95/3.68  tff(c_6, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_32])).
% 10.95/3.68  tff(c_8, plain, (![A_5]: (r2_hidden('#skF_2'(A_5), A_5) | k1_xboole_0=A_5)), inference(cnfTransformation, [status(thm)], [f_40])).
% 10.95/3.68  tff(c_7283, plain, (![A_254]: (~v1_xboole_0(A_254) | k1_relat_1(A_254)=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_7267])).
% 10.95/3.68  tff(c_7287, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_6, c_7283])).
% 10.95/3.68  tff(c_7265, plain, (![A_248, C_247]: (~v1_xboole_0(A_248) | ~r2_hidden(C_247, k1_relat_1(A_248)))), inference(resolution, [status(thm)], [c_7257, c_2])).
% 10.95/3.68  tff(c_7291, plain, (![C_247]: (~v1_xboole_0(k1_xboole_0) | ~r2_hidden(C_247, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_7287, c_7265])).
% 10.95/3.68  tff(c_7307, plain, (![C_247]: (~r2_hidden(C_247, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_7291])).
% 10.95/3.68  tff(c_480, plain, (![A_130, B_131, D_132]: ('#skF_12'(A_130, B_131, k1_funct_2(A_130, B_131), D_132)=D_132 | ~r2_hidden(D_132, k1_funct_2(A_130, B_131)))), inference(cnfTransformation, [status(thm)], [f_119])).
% 10.95/3.68  tff(c_491, plain, ('#skF_12'('#skF_14', '#skF_15', k1_funct_2('#skF_14', '#skF_15'), '#skF_16')='#skF_16'), inference(resolution, [status(thm)], [c_104, c_480])).
% 10.95/3.68  tff(c_58, plain, (![A_46, B_47, D_62]: (v1_relat_1('#skF_12'(A_46, B_47, k1_funct_2(A_46, B_47), D_62)) | ~r2_hidden(D_62, k1_funct_2(A_46, B_47)))), inference(cnfTransformation, [status(thm)], [f_119])).
% 10.95/3.68  tff(c_498, plain, (v1_relat_1('#skF_16') | ~r2_hidden('#skF_16', k1_funct_2('#skF_14', '#skF_15'))), inference(superposition, [status(thm), theory('equality')], [c_491, c_58])).
% 10.95/3.68  tff(c_504, plain, (v1_relat_1('#skF_16')), inference(demodulation, [status(thm), theory('equality')], [c_104, c_498])).
% 10.95/3.68  tff(c_14, plain, (![B_8]: (r1_tarski(B_8, B_8))), inference(cnfTransformation, [status(thm)], [f_46])).
% 10.95/3.68  tff(c_519, plain, (![A_135, B_136, D_137]: (k1_relat_1('#skF_12'(A_135, B_136, k1_funct_2(A_135, B_136), D_137))=A_135 | ~r2_hidden(D_137, k1_funct_2(A_135, B_136)))), inference(cnfTransformation, [status(thm)], [f_119])).
% 10.95/3.68  tff(c_540, plain, (k1_relat_1('#skF_16')='#skF_14' | ~r2_hidden('#skF_16', k1_funct_2('#skF_14', '#skF_15'))), inference(superposition, [status(thm), theory('equality')], [c_491, c_519])).
% 10.95/3.68  tff(c_544, plain, (k1_relat_1('#skF_16')='#skF_14'), inference(demodulation, [status(thm), theory('equality')], [c_104, c_540])).
% 10.95/3.68  tff(c_2445, plain, (![A_182, B_183, D_184]: (r1_tarski(k2_relat_1('#skF_12'(A_182, B_183, k1_funct_2(A_182, B_183), D_184)), B_183) | ~r2_hidden(D_184, k1_funct_2(A_182, B_183)))), inference(cnfTransformation, [status(thm)], [f_119])).
% 10.95/3.68  tff(c_2450, plain, (r1_tarski(k2_relat_1('#skF_16'), '#skF_15') | ~r2_hidden('#skF_16', k1_funct_2('#skF_14', '#skF_15'))), inference(superposition, [status(thm), theory('equality')], [c_491, c_2445])).
% 10.95/3.68  tff(c_2453, plain, (r1_tarski(k2_relat_1('#skF_16'), '#skF_15')), inference(demodulation, [status(thm), theory('equality')], [c_104, c_2450])).
% 10.95/3.68  tff(c_7213, plain, (![C_241, A_242, B_243]: (m1_subset_1(C_241, k1_zfmisc_1(k2_zfmisc_1(A_242, B_243))) | ~r1_tarski(k2_relat_1(C_241), B_243) | ~r1_tarski(k1_relat_1(C_241), A_242) | ~v1_relat_1(C_241))), inference(cnfTransformation, [status(thm)], [f_66])).
% 10.95/3.68  tff(c_102, plain, (~m1_subset_1('#skF_16', k1_zfmisc_1(k2_zfmisc_1('#skF_14', '#skF_15'))) | ~v1_funct_2('#skF_16', '#skF_14', '#skF_15') | ~v1_funct_1('#skF_16')), inference(cnfTransformation, [status(thm)], [f_155])).
% 10.95/3.68  tff(c_129, plain, (~v1_funct_1('#skF_16')), inference(splitLeft, [status(thm)], [c_102])).
% 10.95/3.68  tff(c_332, plain, (![A_108, B_109, D_110]: ('#skF_12'(A_108, B_109, k1_funct_2(A_108, B_109), D_110)=D_110 | ~r2_hidden(D_110, k1_funct_2(A_108, B_109)))), inference(cnfTransformation, [status(thm)], [f_119])).
% 10.95/3.68  tff(c_347, plain, ('#skF_12'('#skF_14', '#skF_15', k1_funct_2('#skF_14', '#skF_15'), '#skF_16')='#skF_16'), inference(resolution, [status(thm)], [c_104, c_332])).
% 10.95/3.68  tff(c_56, plain, (![A_46, B_47, D_62]: (v1_funct_1('#skF_12'(A_46, B_47, k1_funct_2(A_46, B_47), D_62)) | ~r2_hidden(D_62, k1_funct_2(A_46, B_47)))), inference(cnfTransformation, [status(thm)], [f_119])).
% 10.95/3.68  tff(c_438, plain, (v1_funct_1('#skF_16') | ~r2_hidden('#skF_16', k1_funct_2('#skF_14', '#skF_15'))), inference(superposition, [status(thm), theory('equality')], [c_347, c_56])).
% 10.95/3.68  tff(c_444, plain, (v1_funct_1('#skF_16')), inference(demodulation, [status(thm), theory('equality')], [c_104, c_438])).
% 10.95/3.68  tff(c_446, plain, $false, inference(negUnitSimplification, [status(thm)], [c_129, c_444])).
% 10.95/3.68  tff(c_447, plain, (~v1_funct_2('#skF_16', '#skF_14', '#skF_15') | ~m1_subset_1('#skF_16', k1_zfmisc_1(k2_zfmisc_1('#skF_14', '#skF_15')))), inference(splitRight, [status(thm)], [c_102])).
% 10.95/3.68  tff(c_462, plain, (~m1_subset_1('#skF_16', k1_zfmisc_1(k2_zfmisc_1('#skF_14', '#skF_15')))), inference(splitLeft, [status(thm)], [c_447])).
% 10.95/3.68  tff(c_7223, plain, (~r1_tarski(k2_relat_1('#skF_16'), '#skF_15') | ~r1_tarski(k1_relat_1('#skF_16'), '#skF_14') | ~v1_relat_1('#skF_16')), inference(resolution, [status(thm)], [c_7213, c_462])).
% 10.95/3.68  tff(c_7236, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_504, c_14, c_544, c_2453, c_7223])).
% 10.95/3.68  tff(c_7237, plain, (~v1_funct_2('#skF_16', '#skF_14', '#skF_15')), inference(splitRight, [status(thm)], [c_447])).
% 10.95/3.68  tff(c_448, plain, (v1_funct_1('#skF_16')), inference(splitRight, [status(thm)], [c_102])).
% 10.95/3.68  tff(c_7238, plain, (m1_subset_1('#skF_16', k1_zfmisc_1(k2_zfmisc_1('#skF_14', '#skF_15')))), inference(splitRight, [status(thm)], [c_447])).
% 10.95/3.68  tff(c_11364, plain, (![C_332, A_333, B_334]: (v1_funct_2(C_332, A_333, B_334) | ~v1_partfun1(C_332, A_333) | ~v1_funct_1(C_332) | ~m1_subset_1(C_332, k1_zfmisc_1(k2_zfmisc_1(A_333, B_334))))), inference(cnfTransformation, [status(thm)], [f_89])).
% 10.95/3.68  tff(c_11373, plain, (v1_funct_2('#skF_16', '#skF_14', '#skF_15') | ~v1_partfun1('#skF_16', '#skF_14') | ~v1_funct_1('#skF_16')), inference(resolution, [status(thm)], [c_7238, c_11364])).
% 10.95/3.68  tff(c_11384, plain, (v1_funct_2('#skF_16', '#skF_14', '#skF_15') | ~v1_partfun1('#skF_16', '#skF_14')), inference(demodulation, [status(thm), theory('equality')], [c_448, c_11373])).
% 10.95/3.68  tff(c_11385, plain, (~v1_partfun1('#skF_16', '#skF_14')), inference(negUnitSimplification, [status(thm)], [c_7237, c_11384])).
% 10.95/3.68  tff(c_7587, plain, (![A_269, B_270, D_271]: (v1_relat_1('#skF_12'(A_269, B_270, k1_funct_2(A_269, B_270), D_271)) | ~r2_hidden(D_271, k1_funct_2(A_269, B_270)))), inference(cnfTransformation, [status(thm)], [f_119])).
% 10.95/3.68  tff(c_7590, plain, (v1_relat_1('#skF_16') | ~r2_hidden('#skF_16', k1_funct_2('#skF_14', '#skF_15'))), inference(superposition, [status(thm), theory('equality')], [c_7450, c_7587])).
% 10.95/3.68  tff(c_7592, plain, (v1_relat_1('#skF_16')), inference(demodulation, [status(thm), theory('equality')], [c_104, c_7590])).
% 10.95/3.68  tff(c_86, plain, (![A_66]: (v1_funct_2(A_66, k1_relat_1(A_66), k2_relat_1(A_66)) | ~v1_funct_1(A_66) | ~v1_relat_1(A_66))), inference(cnfTransformation, [status(thm)], [f_129])).
% 10.95/3.68  tff(c_8010, plain, (v1_funct_2('#skF_16', '#skF_14', k2_relat_1('#skF_16')) | ~v1_funct_1('#skF_16') | ~v1_relat_1('#skF_16')), inference(superposition, [status(thm), theory('equality')], [c_7964, c_86])).
% 10.95/3.68  tff(c_8019, plain, (v1_funct_2('#skF_16', '#skF_14', k2_relat_1('#skF_16'))), inference(demodulation, [status(thm), theory('equality')], [c_7592, c_448, c_8010])).
% 10.95/3.68  tff(c_84, plain, (![A_66]: (m1_subset_1(A_66, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_66), k2_relat_1(A_66)))) | ~v1_funct_1(A_66) | ~v1_relat_1(A_66))), inference(cnfTransformation, [status(thm)], [f_129])).
% 10.95/3.68  tff(c_8007, plain, (m1_subset_1('#skF_16', k1_zfmisc_1(k2_zfmisc_1('#skF_14', k2_relat_1('#skF_16')))) | ~v1_funct_1('#skF_16') | ~v1_relat_1('#skF_16')), inference(superposition, [status(thm), theory('equality')], [c_7964, c_84])).
% 10.95/3.68  tff(c_8017, plain, (m1_subset_1('#skF_16', k1_zfmisc_1(k2_zfmisc_1('#skF_14', k2_relat_1('#skF_16'))))), inference(demodulation, [status(thm), theory('equality')], [c_7592, c_448, c_8007])).
% 10.95/3.68  tff(c_19788, plain, (![C_459, A_460, B_461]: (v1_partfun1(C_459, A_460) | ~v1_funct_2(C_459, A_460, B_461) | ~v1_funct_1(C_459) | ~m1_subset_1(C_459, k1_zfmisc_1(k2_zfmisc_1(A_460, B_461))) | v1_xboole_0(B_461))), inference(cnfTransformation, [status(thm)], [f_103])).
% 10.95/3.68  tff(c_19797, plain, (v1_partfun1('#skF_16', '#skF_14') | ~v1_funct_2('#skF_16', '#skF_14', k2_relat_1('#skF_16')) | ~v1_funct_1('#skF_16') | v1_xboole_0(k2_relat_1('#skF_16'))), inference(resolution, [status(thm)], [c_8017, c_19788])).
% 10.95/3.68  tff(c_19811, plain, (v1_partfun1('#skF_16', '#skF_14') | v1_xboole_0(k2_relat_1('#skF_16'))), inference(demodulation, [status(thm), theory('equality')], [c_448, c_8019, c_19797])).
% 10.95/3.68  tff(c_19812, plain, (v1_xboole_0(k2_relat_1('#skF_16'))), inference(negUnitSimplification, [status(thm)], [c_11385, c_19811])).
% 10.95/3.68  tff(c_117, plain, (![A_75]: (r2_hidden('#skF_2'(A_75), A_75) | k1_xboole_0=A_75)), inference(cnfTransformation, [status(thm)], [f_40])).
% 10.95/3.68  tff(c_121, plain, (![A_75]: (~v1_xboole_0(A_75) | k1_xboole_0=A_75)), inference(resolution, [status(thm)], [c_117, c_2])).
% 10.95/3.68  tff(c_19826, plain, (k2_relat_1('#skF_16')=k1_xboole_0), inference(resolution, [status(thm)], [c_19812, c_121])).
% 10.95/3.68  tff(c_19843, plain, (m1_subset_1('#skF_16', k1_zfmisc_1(k2_zfmisc_1('#skF_14', k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_19826, c_8017])).
% 10.95/3.68  tff(c_34, plain, (![A_33, B_34, C_35, D_36]: (r2_hidden('#skF_8'(A_33, B_34, C_35, D_36), C_35) | ~r2_hidden(A_33, D_36) | ~m1_subset_1(D_36, k1_zfmisc_1(k2_zfmisc_1(B_34, C_35))))), inference(cnfTransformation, [status(thm)], [f_79])).
% 10.95/3.68  tff(c_19951, plain, (![A_33]: (r2_hidden('#skF_8'(A_33, '#skF_14', k1_xboole_0, '#skF_16'), k1_xboole_0) | ~r2_hidden(A_33, '#skF_16'))), inference(resolution, [status(thm)], [c_19843, c_34])).
% 10.95/3.68  tff(c_19974, plain, (![A_464]: (~r2_hidden(A_464, '#skF_16'))), inference(negUnitSimplification, [status(thm)], [c_7307, c_19951])).
% 10.95/3.68  tff(c_20016, plain, (v1_xboole_0('#skF_16')), inference(resolution, [status(thm)], [c_4, c_19974])).
% 10.95/3.68  tff(c_20031, plain, $false, inference(negUnitSimplification, [status(thm)], [c_8021, c_20016])).
% 10.95/3.68  tff(c_20032, plain, (v1_xboole_0('#skF_14')), inference(splitRight, [status(thm)], [c_7995])).
% 10.95/3.68  tff(c_20041, plain, (k1_xboole_0='#skF_14'), inference(resolution, [status(thm)], [c_20032, c_121])).
% 10.95/3.68  tff(c_20087, plain, (![C_247]: (~r2_hidden(C_247, '#skF_14'))), inference(demodulation, [status(thm), theory('equality')], [c_20041, c_7307])).
% 10.95/3.68  tff(c_20033, plain, (v1_xboole_0('#skF_16')), inference(splitRight, [status(thm)], [c_7995])).
% 10.95/3.68  tff(c_20050, plain, (k1_xboole_0='#skF_16'), inference(resolution, [status(thm)], [c_20033, c_121])).
% 10.95/3.68  tff(c_20098, plain, ('#skF_16'='#skF_14'), inference(demodulation, [status(thm), theory('equality')], [c_20041, c_20050])).
% 10.95/3.68  tff(c_20101, plain, (v1_relat_1('#skF_14')), inference(demodulation, [status(thm), theory('equality')], [c_20098, c_7592])).
% 10.95/3.68  tff(c_20107, plain, (v1_funct_1('#skF_14')), inference(demodulation, [status(thm), theory('equality')], [c_20098, c_448])).
% 10.95/3.68  tff(c_20100, plain, (k1_relat_1('#skF_14')='#skF_14'), inference(demodulation, [status(thm), theory('equality')], [c_20098, c_7964])).
% 10.95/3.68  tff(c_23931, plain, (![C_557, B_558]: (r2_hidden('#skF_13'(k1_relat_1(C_557), B_558, C_557), k1_relat_1(C_557)) | v1_funct_2(C_557, k1_relat_1(C_557), B_558) | ~v1_funct_1(C_557) | ~v1_relat_1(C_557))), inference(cnfTransformation, [status(thm)], [f_146])).
% 10.95/3.68  tff(c_24018, plain, (![B_558]: (r2_hidden('#skF_13'('#skF_14', B_558, '#skF_14'), k1_relat_1('#skF_14')) | v1_funct_2('#skF_14', k1_relat_1('#skF_14'), B_558) | ~v1_funct_1('#skF_14') | ~v1_relat_1('#skF_14'))), inference(superposition, [status(thm), theory('equality')], [c_20100, c_23931])).
% 10.95/3.68  tff(c_24044, plain, (![B_558]: (r2_hidden('#skF_13'('#skF_14', B_558, '#skF_14'), '#skF_14') | v1_funct_2('#skF_14', '#skF_14', B_558))), inference(demodulation, [status(thm), theory('equality')], [c_20101, c_20107, c_20100, c_20100, c_24018])).
% 10.95/3.68  tff(c_24045, plain, (![B_558]: (v1_funct_2('#skF_14', '#skF_14', B_558))), inference(negUnitSimplification, [status(thm)], [c_20087, c_24044])).
% 10.95/3.68  tff(c_20106, plain, (~v1_funct_2('#skF_14', '#skF_14', '#skF_15')), inference(demodulation, [status(thm), theory('equality')], [c_20098, c_7237])).
% 10.95/3.68  tff(c_24052, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_24045, c_20106])).
% 10.95/3.68  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.95/3.68  
% 10.95/3.68  Inference rules
% 10.95/3.68  ----------------------
% 10.95/3.68  #Ref     : 0
% 10.95/3.68  #Sup     : 6082
% 10.95/3.68  #Fact    : 0
% 10.95/3.68  #Define  : 0
% 10.95/3.68  #Split   : 33
% 10.95/3.68  #Chain   : 0
% 10.95/3.68  #Close   : 0
% 10.95/3.68  
% 10.95/3.68  Ordering : KBO
% 10.95/3.68  
% 10.95/3.68  Simplification rules
% 10.95/3.68  ----------------------
% 10.95/3.68  #Subsume      : 1631
% 10.95/3.68  #Demod        : 12190
% 10.95/3.68  #Tautology    : 2914
% 10.95/3.68  #SimpNegUnit  : 63
% 10.95/3.68  #BackRed      : 44
% 10.95/3.68  
% 10.95/3.68  #Partial instantiations: 0
% 10.95/3.68  #Strategies tried      : 1
% 10.95/3.68  
% 10.95/3.68  Timing (in seconds)
% 10.95/3.68  ----------------------
% 10.95/3.68  Preprocessing        : 0.37
% 10.95/3.68  Parsing              : 0.17
% 10.95/3.68  CNF conversion       : 0.03
% 10.95/3.68  Main loop            : 2.47
% 10.95/3.68  Inferencing          : 0.64
% 10.95/3.68  Reduction            : 0.90
% 10.95/3.68  Demodulation         : 0.68
% 10.95/3.68  BG Simplification    : 0.09
% 10.95/3.69  Subsumption          : 0.70
% 10.95/3.69  Abstraction          : 0.12
% 10.95/3.69  MUC search           : 0.00
% 10.95/3.69  Cooper               : 0.00
% 10.95/3.69  Total                : 2.89
% 10.95/3.69  Index Insertion      : 0.00
% 10.95/3.69  Index Deletion       : 0.00
% 10.95/3.69  Index Matching       : 0.00
% 10.95/3.69  BG Taut test         : 0.00
%------------------------------------------------------------------------------
