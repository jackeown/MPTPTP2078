%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:17:46 EST 2020

% Result     : Theorem 5.42s
% Output     : CNFRefutation 5.78s
% Verified   : 
% Statistics : Number of formulae       :  174 (1005 expanded)
%              Number of leaves         :   47 ( 365 expanded)
%              Depth                    :   22
%              Number of atoms          :  402 (3624 expanded)
%              Number of equality atoms :   68 ( 734 expanded)
%              Maximal formula depth    :   17 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k8_funct_2 > k7_partfun1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_3 > #skF_8 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k7_partfun1,type,(
    k7_partfun1: ( $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff(k8_funct_2,type,(
    k8_funct_2: ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

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

tff(f_198,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ~ v1_xboole_0(C)
       => ! [D] :
            ( ( v1_funct_1(D)
              & v1_funct_2(D,B,C)
              & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,C))) )
           => ! [E] :
                ( ( v1_funct_1(E)
                  & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(C,A))) )
               => ! [F] :
                    ( m1_subset_1(F,B)
                   => ( r1_tarski(k2_relset_1(B,C,D),k1_relset_1(C,A,E))
                     => ( B = k1_xboole_0
                        | k1_funct_1(k8_funct_2(B,C,A,D,E),F) = k7_partfun1(A,E,k1_funct_1(D,F)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t186_funct_2)).

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

tff(f_87,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_52,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_60,axiom,(
    ! [A] :
      ( ( ~ v1_xboole_0(A)
        & v1_relat_1(A) )
     => ~ v1_xboole_0(k2_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_relat_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_46,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_107,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & ~ v1_xboole_0(B) )
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => ( ( v1_funct_1(C)
              & v1_funct_2(C,A,B) )
           => ( v1_funct_1(C)
              & ~ v1_xboole_0(C)
              & v1_funct_2(C,A,B) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc6_funct_2)).

tff(f_69,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

tff(f_142,axiom,(
    ! [A,B,C] :
      ( ~ v1_xboole_0(C)
     => ! [D] :
          ( ( v1_funct_1(D)
            & v1_funct_2(D,B,C)
            & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,C))) )
         => ! [E] :
              ( ( v1_funct_1(E)
                & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(C,A))) )
             => ! [F] :
                  ( m1_subset_1(F,B)
                 => ( r1_tarski(k2_relset_1(B,C,D),k1_relset_1(C,A,E))
                   => ( B = k1_xboole_0
                      | k1_funct_1(k8_funct_2(B,C,A,D,E),F) = k1_funct_1(E,k1_funct_1(D,F)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t185_funct_2)).

tff(f_79,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_173,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r1_tarski(k2_relset_1(A,B,D),C)
       => ( ( B = k1_xboole_0
            & A != k1_xboole_0 )
          | ( v1_funct_1(D)
            & v1_funct_2(D,A,C)
            & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,C))) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_funct_2)).

tff(f_154,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_hidden(C,A)
       => ( B = k1_xboole_0
          | r2_hidden(k1_funct_1(D,C),B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_funct_2)).

tff(f_118,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A)
        & v1_funct_1(B) )
     => ! [C] :
          ( r2_hidden(C,k1_relat_1(B))
         => k7_partfun1(A,B,C) = k1_funct_1(B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_partfun1)).

tff(c_74,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_198])).

tff(c_107,plain,(
    ! [C_85,A_86,B_87] :
      ( v1_relat_1(C_85)
      | ~ m1_subset_1(C_85,k1_zfmisc_1(k2_zfmisc_1(A_86,B_87))) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_114,plain,(
    v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_74,c_107])).

tff(c_70,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_198])).

tff(c_370,plain,(
    ! [A_130,B_131,C_132] :
      ( k1_relset_1(A_130,B_131,C_132) = k1_relat_1(C_132)
      | ~ m1_subset_1(C_132,k1_zfmisc_1(k2_zfmisc_1(A_130,B_131))) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_378,plain,(
    k1_relset_1('#skF_5','#skF_3','#skF_7') = k1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_70,c_370])).

tff(c_286,plain,(
    ! [A_120,B_121,C_122] :
      ( k2_relset_1(A_120,B_121,C_122) = k2_relat_1(C_122)
      | ~ m1_subset_1(C_122,k1_zfmisc_1(k2_zfmisc_1(A_120,B_121))) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_293,plain,(
    k2_relset_1('#skF_4','#skF_5','#skF_6') = k2_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_74,c_286])).

tff(c_66,plain,(
    r1_tarski(k2_relset_1('#skF_4','#skF_5','#skF_6'),k1_relset_1('#skF_5','#skF_3','#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_198])).

tff(c_295,plain,(
    r1_tarski(k2_relat_1('#skF_6'),k1_relset_1('#skF_5','#skF_3','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_293,c_66])).

tff(c_384,plain,(
    r1_tarski(k2_relat_1('#skF_6'),k1_relat_1('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_378,c_295])).

tff(c_20,plain,(
    ! [A_13,B_14] :
      ( r2_hidden(A_13,B_14)
      | v1_xboole_0(B_14)
      | ~ m1_subset_1(A_13,B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_245,plain,(
    ! [C_109,B_110,A_111] :
      ( r2_hidden(C_109,B_110)
      | ~ r2_hidden(C_109,A_111)
      | ~ r1_tarski(A_111,B_110) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_429,plain,(
    ! [A_136,B_137,B_138] :
      ( r2_hidden(A_136,B_137)
      | ~ r1_tarski(B_138,B_137)
      | v1_xboole_0(B_138)
      | ~ m1_subset_1(A_136,B_138) ) ),
    inference(resolution,[status(thm)],[c_20,c_245])).

tff(c_438,plain,(
    ! [A_136] :
      ( r2_hidden(A_136,k1_relat_1('#skF_7'))
      | v1_xboole_0(k2_relat_1('#skF_6'))
      | ~ m1_subset_1(A_136,k2_relat_1('#skF_6')) ) ),
    inference(resolution,[status(thm)],[c_384,c_429])).

tff(c_479,plain,(
    v1_xboole_0(k2_relat_1('#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_438])).

tff(c_22,plain,(
    ! [A_15] :
      ( ~ v1_xboole_0(k2_relat_1(A_15))
      | ~ v1_relat_1(A_15)
      | v1_xboole_0(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_487,plain,
    ( ~ v1_relat_1('#skF_6')
    | v1_xboole_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_479,c_22])).

tff(c_495,plain,(
    v1_xboole_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_114,c_487])).

tff(c_142,plain,(
    ! [A_91,B_92] :
      ( r2_hidden('#skF_2'(A_91,B_92),A_91)
      | r1_tarski(A_91,B_92) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_158,plain,(
    ! [A_95,B_96] :
      ( ~ v1_xboole_0(A_95)
      | r1_tarski(A_95,B_96) ) ),
    inference(resolution,[status(thm)],[c_142,c_2])).

tff(c_18,plain,(
    ! [A_12] : r1_tarski(k1_xboole_0,A_12) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_116,plain,(
    ! [B_88,A_89] :
      ( B_88 = A_89
      | ~ r1_tarski(B_88,A_89)
      | ~ r1_tarski(A_89,B_88) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_128,plain,(
    ! [A_12] :
      ( k1_xboole_0 = A_12
      | ~ r1_tarski(A_12,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_18,c_116])).

tff(c_169,plain,(
    ! [A_95] :
      ( k1_xboole_0 = A_95
      | ~ v1_xboole_0(A_95) ) ),
    inference(resolution,[status(thm)],[c_158,c_128])).

tff(c_506,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(resolution,[status(thm)],[c_495,c_169])).

tff(c_64,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_198])).

tff(c_515,plain,(
    '#skF_6' != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_506,c_64])).

tff(c_80,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_198])).

tff(c_78,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_198])).

tff(c_76,plain,(
    v1_funct_2('#skF_6','#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_198])).

tff(c_522,plain,(
    ! [C_145,A_146,B_147] :
      ( ~ v1_xboole_0(C_145)
      | ~ v1_funct_2(C_145,A_146,B_147)
      | ~ v1_funct_1(C_145)
      | ~ m1_subset_1(C_145,k1_zfmisc_1(k2_zfmisc_1(A_146,B_147)))
      | v1_xboole_0(B_147)
      | v1_xboole_0(A_146) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_525,plain,
    ( ~ v1_xboole_0('#skF_6')
    | ~ v1_funct_2('#skF_6','#skF_4','#skF_5')
    | ~ v1_funct_1('#skF_6')
    | v1_xboole_0('#skF_5')
    | v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_74,c_522])).

tff(c_531,plain,
    ( v1_xboole_0('#skF_5')
    | v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_495,c_525])).

tff(c_532,plain,(
    v1_xboole_0('#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_531])).

tff(c_606,plain,(
    ! [A_149] :
      ( A_149 = '#skF_6'
      | ~ v1_xboole_0(A_149) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_506,c_169])).

tff(c_609,plain,(
    '#skF_6' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_532,c_606])).

tff(c_616,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_515,c_609])).

tff(c_618,plain,(
    ~ v1_xboole_0(k2_relat_1('#skF_6')) ),
    inference(splitRight,[status(thm)],[c_438])).

tff(c_16,plain,(
    ! [B_11] : r1_tarski(B_11,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_87,plain,(
    ! [A_82] :
      ( v1_xboole_0(A_82)
      | r2_hidden('#skF_1'(A_82),A_82) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_26,plain,(
    ! [B_18,A_17] :
      ( ~ r1_tarski(B_18,A_17)
      | ~ r2_hidden(A_17,B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_96,plain,(
    ! [A_83] :
      ( ~ r1_tarski(A_83,'#skF_1'(A_83))
      | v1_xboole_0(A_83) ) ),
    inference(resolution,[status(thm)],[c_87,c_26])).

tff(c_101,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_18,c_96])).

tff(c_68,plain,(
    m1_subset_1('#skF_8','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_198])).

tff(c_72,plain,(
    v1_funct_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_198])).

tff(c_1190,plain,(
    ! [A_241,F_246,C_245,D_244,E_243,B_242] :
      ( k1_funct_1(k8_funct_2(B_242,C_245,A_241,D_244,E_243),F_246) = k1_funct_1(E_243,k1_funct_1(D_244,F_246))
      | k1_xboole_0 = B_242
      | ~ r1_tarski(k2_relset_1(B_242,C_245,D_244),k1_relset_1(C_245,A_241,E_243))
      | ~ m1_subset_1(F_246,B_242)
      | ~ m1_subset_1(E_243,k1_zfmisc_1(k2_zfmisc_1(C_245,A_241)))
      | ~ v1_funct_1(E_243)
      | ~ m1_subset_1(D_244,k1_zfmisc_1(k2_zfmisc_1(B_242,C_245)))
      | ~ v1_funct_2(D_244,B_242,C_245)
      | ~ v1_funct_1(D_244)
      | v1_xboole_0(C_245) ) ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_1202,plain,(
    ! [A_241,E_243,F_246] :
      ( k1_funct_1(k8_funct_2('#skF_4','#skF_5',A_241,'#skF_6',E_243),F_246) = k1_funct_1(E_243,k1_funct_1('#skF_6',F_246))
      | k1_xboole_0 = '#skF_4'
      | ~ r1_tarski(k2_relat_1('#skF_6'),k1_relset_1('#skF_5',A_241,E_243))
      | ~ m1_subset_1(F_246,'#skF_4')
      | ~ m1_subset_1(E_243,k1_zfmisc_1(k2_zfmisc_1('#skF_5',A_241)))
      | ~ v1_funct_1(E_243)
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_5')))
      | ~ v1_funct_2('#skF_6','#skF_4','#skF_5')
      | ~ v1_funct_1('#skF_6')
      | v1_xboole_0('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_293,c_1190])).

tff(c_1219,plain,(
    ! [A_241,E_243,F_246] :
      ( k1_funct_1(k8_funct_2('#skF_4','#skF_5',A_241,'#skF_6',E_243),F_246) = k1_funct_1(E_243,k1_funct_1('#skF_6',F_246))
      | k1_xboole_0 = '#skF_4'
      | ~ r1_tarski(k2_relat_1('#skF_6'),k1_relset_1('#skF_5',A_241,E_243))
      | ~ m1_subset_1(F_246,'#skF_4')
      | ~ m1_subset_1(E_243,k1_zfmisc_1(k2_zfmisc_1('#skF_5',A_241)))
      | ~ v1_funct_1(E_243)
      | v1_xboole_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_74,c_1202])).

tff(c_1278,plain,(
    ! [A_250,E_251,F_252] :
      ( k1_funct_1(k8_funct_2('#skF_4','#skF_5',A_250,'#skF_6',E_251),F_252) = k1_funct_1(E_251,k1_funct_1('#skF_6',F_252))
      | ~ r1_tarski(k2_relat_1('#skF_6'),k1_relset_1('#skF_5',A_250,E_251))
      | ~ m1_subset_1(F_252,'#skF_4')
      | ~ m1_subset_1(E_251,k1_zfmisc_1(k2_zfmisc_1('#skF_5',A_250)))
      | ~ v1_funct_1(E_251) ) ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_64,c_1219])).

tff(c_1280,plain,(
    ! [F_252] :
      ( k1_funct_1(k8_funct_2('#skF_4','#skF_5','#skF_3','#skF_6','#skF_7'),F_252) = k1_funct_1('#skF_7',k1_funct_1('#skF_6',F_252))
      | ~ r1_tarski(k2_relat_1('#skF_6'),k1_relat_1('#skF_7'))
      | ~ m1_subset_1(F_252,'#skF_4')
      | ~ m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_3')))
      | ~ v1_funct_1('#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_378,c_1278])).

tff(c_1285,plain,(
    ! [F_252] :
      ( k1_funct_1(k8_funct_2('#skF_4','#skF_5','#skF_3','#skF_6','#skF_7'),F_252) = k1_funct_1('#skF_7',k1_funct_1('#skF_6',F_252))
      | ~ m1_subset_1(F_252,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_384,c_1280])).

tff(c_265,plain,(
    ! [C_115,B_116,A_117] :
      ( v5_relat_1(C_115,B_116)
      | ~ m1_subset_1(C_115,k1_zfmisc_1(k2_zfmisc_1(A_117,B_116))) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_273,plain,(
    v5_relat_1('#skF_7','#skF_3') ),
    inference(resolution,[status(thm)],[c_70,c_265])).

tff(c_115,plain,(
    v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_70,c_107])).

tff(c_919,plain,(
    ! [B_197,D_198,A_199,C_200] :
      ( k1_xboole_0 = B_197
      | v1_funct_2(D_198,A_199,C_200)
      | ~ r1_tarski(k2_relset_1(A_199,B_197,D_198),C_200)
      | ~ m1_subset_1(D_198,k1_zfmisc_1(k2_zfmisc_1(A_199,B_197)))
      | ~ v1_funct_2(D_198,A_199,B_197)
      | ~ v1_funct_1(D_198) ) ),
    inference(cnfTransformation,[status(thm)],[f_173])).

tff(c_923,plain,(
    ! [C_200] :
      ( k1_xboole_0 = '#skF_5'
      | v1_funct_2('#skF_6','#skF_4',C_200)
      | ~ r1_tarski(k2_relat_1('#skF_6'),C_200)
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_5')))
      | ~ v1_funct_2('#skF_6','#skF_4','#skF_5')
      | ~ v1_funct_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_293,c_919])).

tff(c_933,plain,(
    ! [C_200] :
      ( k1_xboole_0 = '#skF_5'
      | v1_funct_2('#skF_6','#skF_4',C_200)
      | ~ r1_tarski(k2_relat_1('#skF_6'),C_200) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_74,c_923])).

tff(c_936,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_933])).

tff(c_945,plain,(
    v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_936,c_101])).

tff(c_949,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_945])).

tff(c_951,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(splitRight,[status(thm)],[c_933])).

tff(c_812,plain,(
    ! [D_180,C_181,B_182,A_183] :
      ( r2_hidden(k1_funct_1(D_180,C_181),B_182)
      | k1_xboole_0 = B_182
      | ~ r2_hidden(C_181,A_183)
      | ~ m1_subset_1(D_180,k1_zfmisc_1(k2_zfmisc_1(A_183,B_182)))
      | ~ v1_funct_2(D_180,A_183,B_182)
      | ~ v1_funct_1(D_180) ) ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_1998,plain,(
    ! [D_319,A_320,B_321,B_322] :
      ( r2_hidden(k1_funct_1(D_319,A_320),B_321)
      | k1_xboole_0 = B_321
      | ~ m1_subset_1(D_319,k1_zfmisc_1(k2_zfmisc_1(B_322,B_321)))
      | ~ v1_funct_2(D_319,B_322,B_321)
      | ~ v1_funct_1(D_319)
      | v1_xboole_0(B_322)
      | ~ m1_subset_1(A_320,B_322) ) ),
    inference(resolution,[status(thm)],[c_20,c_812])).

tff(c_2010,plain,(
    ! [A_320] :
      ( r2_hidden(k1_funct_1('#skF_6',A_320),'#skF_5')
      | k1_xboole_0 = '#skF_5'
      | ~ v1_funct_2('#skF_6','#skF_4','#skF_5')
      | ~ v1_funct_1('#skF_6')
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(A_320,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_74,c_1998])).

tff(c_2027,plain,(
    ! [A_320] :
      ( r2_hidden(k1_funct_1('#skF_6',A_320),'#skF_5')
      | k1_xboole_0 = '#skF_5'
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(A_320,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_2010])).

tff(c_2028,plain,(
    ! [A_320] :
      ( r2_hidden(k1_funct_1('#skF_6',A_320),'#skF_5')
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(A_320,'#skF_4') ) ),
    inference(negUnitSimplification,[status(thm)],[c_951,c_2027])).

tff(c_2033,plain,(
    v1_xboole_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_2028])).

tff(c_2038,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_2033,c_169])).

tff(c_2046,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_2038])).

tff(c_2048,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_2028])).

tff(c_952,plain,(
    ! [C_201] :
      ( v1_funct_2('#skF_6','#skF_4',C_201)
      | ~ r1_tarski(k2_relat_1('#skF_6'),C_201) ) ),
    inference(splitRight,[status(thm)],[c_933])).

tff(c_964,plain,(
    v1_funct_2('#skF_6','#skF_4',k1_relat_1('#skF_7')) ),
    inference(resolution,[status(thm)],[c_384,c_952])).

tff(c_1089,plain,(
    ! [B_229,D_230,A_231,C_232] :
      ( k1_xboole_0 = B_229
      | m1_subset_1(D_230,k1_zfmisc_1(k2_zfmisc_1(A_231,C_232)))
      | ~ r1_tarski(k2_relset_1(A_231,B_229,D_230),C_232)
      | ~ m1_subset_1(D_230,k1_zfmisc_1(k2_zfmisc_1(A_231,B_229)))
      | ~ v1_funct_2(D_230,A_231,B_229)
      | ~ v1_funct_1(D_230) ) ),
    inference(cnfTransformation,[status(thm)],[f_173])).

tff(c_1093,plain,(
    ! [C_232] :
      ( k1_xboole_0 = '#skF_5'
      | m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4',C_232)))
      | ~ r1_tarski(k2_relat_1('#skF_6'),C_232)
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_5')))
      | ~ v1_funct_2('#skF_6','#skF_4','#skF_5')
      | ~ v1_funct_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_293,c_1089])).

tff(c_1103,plain,(
    ! [C_232] :
      ( k1_xboole_0 = '#skF_5'
      | m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4',C_232)))
      | ~ r1_tarski(k2_relat_1('#skF_6'),C_232) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_74,c_1093])).

tff(c_1104,plain,(
    ! [C_232] :
      ( m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4',C_232)))
      | ~ r1_tarski(k2_relat_1('#skF_6'),C_232) ) ),
    inference(negUnitSimplification,[status(thm)],[c_951,c_1103])).

tff(c_12,plain,(
    ! [B_11,A_10] :
      ( B_11 = A_10
      | ~ r1_tarski(B_11,A_10)
      | ~ r1_tarski(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_178,plain,(
    ! [B_98,A_99] :
      ( B_98 = A_99
      | ~ r1_tarski(B_98,A_99)
      | ~ v1_xboole_0(A_99) ) ),
    inference(resolution,[status(thm)],[c_158,c_12])).

tff(c_192,plain,
    ( k2_relset_1('#skF_4','#skF_5','#skF_6') = k1_relset_1('#skF_5','#skF_3','#skF_7')
    | ~ v1_xboole_0(k1_relset_1('#skF_5','#skF_3','#skF_7')) ),
    inference(resolution,[status(thm)],[c_66,c_178])).

tff(c_264,plain,(
    ~ v1_xboole_0(k1_relset_1('#skF_5','#skF_3','#skF_7')) ),
    inference(splitLeft,[status(thm)],[c_192])).

tff(c_385,plain,(
    ~ v1_xboole_0(k1_relat_1('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_378,c_264])).

tff(c_1107,plain,(
    ! [C_233] :
      ( m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4',C_233)))
      | ~ r1_tarski(k2_relat_1('#skF_6'),C_233) ) ),
    inference(negUnitSimplification,[status(thm)],[c_951,c_1103])).

tff(c_36,plain,(
    ! [A_28,B_29,C_30] :
      ( k2_relset_1(A_28,B_29,C_30) = k2_relat_1(C_30)
      | ~ m1_subset_1(C_30,k1_zfmisc_1(k2_zfmisc_1(A_28,B_29))) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_1175,plain,(
    ! [C_240] :
      ( k2_relset_1('#skF_4',C_240,'#skF_6') = k2_relat_1('#skF_6')
      | ~ r1_tarski(k2_relat_1('#skF_6'),C_240) ) ),
    inference(resolution,[status(thm)],[c_1107,c_36])).

tff(c_1187,plain,(
    k2_relset_1('#skF_4',k1_relat_1('#skF_7'),'#skF_6') = k2_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_384,c_1175])).

tff(c_46,plain,(
    ! [D_49,F_55,A_39,C_41,B_40,E_53] :
      ( k1_funct_1(k8_funct_2(B_40,C_41,A_39,D_49,E_53),F_55) = k1_funct_1(E_53,k1_funct_1(D_49,F_55))
      | k1_xboole_0 = B_40
      | ~ r1_tarski(k2_relset_1(B_40,C_41,D_49),k1_relset_1(C_41,A_39,E_53))
      | ~ m1_subset_1(F_55,B_40)
      | ~ m1_subset_1(E_53,k1_zfmisc_1(k2_zfmisc_1(C_41,A_39)))
      | ~ v1_funct_1(E_53)
      | ~ m1_subset_1(D_49,k1_zfmisc_1(k2_zfmisc_1(B_40,C_41)))
      | ~ v1_funct_2(D_49,B_40,C_41)
      | ~ v1_funct_1(D_49)
      | v1_xboole_0(C_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_1224,plain,(
    ! [A_39,E_53,F_55] :
      ( k1_funct_1(k8_funct_2('#skF_4',k1_relat_1('#skF_7'),A_39,'#skF_6',E_53),F_55) = k1_funct_1(E_53,k1_funct_1('#skF_6',F_55))
      | k1_xboole_0 = '#skF_4'
      | ~ r1_tarski(k2_relat_1('#skF_6'),k1_relset_1(k1_relat_1('#skF_7'),A_39,E_53))
      | ~ m1_subset_1(F_55,'#skF_4')
      | ~ m1_subset_1(E_53,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_7'),A_39)))
      | ~ v1_funct_1(E_53)
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4',k1_relat_1('#skF_7'))))
      | ~ v1_funct_2('#skF_6','#skF_4',k1_relat_1('#skF_7'))
      | ~ v1_funct_1('#skF_6')
      | v1_xboole_0(k1_relat_1('#skF_7')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1187,c_46])).

tff(c_1232,plain,(
    ! [A_39,E_53,F_55] :
      ( k1_funct_1(k8_funct_2('#skF_4',k1_relat_1('#skF_7'),A_39,'#skF_6',E_53),F_55) = k1_funct_1(E_53,k1_funct_1('#skF_6',F_55))
      | k1_xboole_0 = '#skF_4'
      | ~ r1_tarski(k2_relat_1('#skF_6'),k1_relset_1(k1_relat_1('#skF_7'),A_39,E_53))
      | ~ m1_subset_1(F_55,'#skF_4')
      | ~ m1_subset_1(E_53,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_7'),A_39)))
      | ~ v1_funct_1(E_53)
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4',k1_relat_1('#skF_7'))))
      | v1_xboole_0(k1_relat_1('#skF_7')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_964,c_1224])).

tff(c_1233,plain,(
    ! [A_39,E_53,F_55] :
      ( k1_funct_1(k8_funct_2('#skF_4',k1_relat_1('#skF_7'),A_39,'#skF_6',E_53),F_55) = k1_funct_1(E_53,k1_funct_1('#skF_6',F_55))
      | ~ r1_tarski(k2_relat_1('#skF_6'),k1_relset_1(k1_relat_1('#skF_7'),A_39,E_53))
      | ~ m1_subset_1(F_55,'#skF_4')
      | ~ m1_subset_1(E_53,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_7'),A_39)))
      | ~ v1_funct_1(E_53)
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4',k1_relat_1('#skF_7')))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_385,c_64,c_1232])).

tff(c_1680,plain,(
    ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4',k1_relat_1('#skF_7')))) ),
    inference(splitLeft,[status(thm)],[c_1233])).

tff(c_1683,plain,(
    ~ r1_tarski(k2_relat_1('#skF_6'),k1_relat_1('#skF_7')) ),
    inference(resolution,[status(thm)],[c_1104,c_1680])).

tff(c_1687,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_384,c_1683])).

tff(c_1689,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4',k1_relat_1('#skF_7')))) ),
    inference(splitRight,[status(thm)],[c_1233])).

tff(c_2000,plain,(
    ! [A_320] :
      ( r2_hidden(k1_funct_1('#skF_6',A_320),k1_relat_1('#skF_7'))
      | k1_relat_1('#skF_7') = k1_xboole_0
      | ~ v1_funct_2('#skF_6','#skF_4',k1_relat_1('#skF_7'))
      | ~ v1_funct_1('#skF_6')
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(A_320,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_1689,c_1998])).

tff(c_2015,plain,(
    ! [A_320] :
      ( r2_hidden(k1_funct_1('#skF_6',A_320),k1_relat_1('#skF_7'))
      | k1_relat_1('#skF_7') = k1_xboole_0
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(A_320,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_964,c_2000])).

tff(c_2521,plain,(
    ! [A_320] :
      ( r2_hidden(k1_funct_1('#skF_6',A_320),k1_relat_1('#skF_7'))
      | k1_relat_1('#skF_7') = k1_xboole_0
      | ~ m1_subset_1(A_320,'#skF_4') ) ),
    inference(negUnitSimplification,[status(thm)],[c_2048,c_2015])).

tff(c_2522,plain,(
    k1_relat_1('#skF_7') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_2521])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_274,plain,(
    ! [A_118,B_119] :
      ( r2_hidden('#skF_1'(A_118),B_119)
      | ~ r1_tarski(A_118,B_119)
      | v1_xboole_0(A_118) ) ),
    inference(resolution,[status(thm)],[c_4,c_245])).

tff(c_6,plain,(
    ! [C_9,B_6,A_5] :
      ( r2_hidden(C_9,B_6)
      | ~ r2_hidden(C_9,A_5)
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_719,plain,(
    ! [A_166,B_167,B_168] :
      ( r2_hidden('#skF_1'(A_166),B_167)
      | ~ r1_tarski(B_168,B_167)
      | ~ r1_tarski(A_166,B_168)
      | v1_xboole_0(A_166) ) ),
    inference(resolution,[status(thm)],[c_274,c_6])).

tff(c_732,plain,(
    ! [A_169] :
      ( r2_hidden('#skF_1'(A_169),k1_relat_1('#skF_7'))
      | ~ r1_tarski(A_169,k2_relat_1('#skF_6'))
      | v1_xboole_0(A_169) ) ),
    inference(resolution,[status(thm)],[c_384,c_719])).

tff(c_842,plain,(
    ! [A_187,B_188] :
      ( r2_hidden('#skF_1'(A_187),B_188)
      | ~ r1_tarski(k1_relat_1('#skF_7'),B_188)
      | ~ r1_tarski(A_187,k2_relat_1('#skF_6'))
      | v1_xboole_0(A_187) ) ),
    inference(resolution,[status(thm)],[c_732,c_6])).

tff(c_906,plain,(
    ! [B_195,A_196] :
      ( ~ r1_tarski(B_195,'#skF_1'(A_196))
      | ~ r1_tarski(k1_relat_1('#skF_7'),B_195)
      | ~ r1_tarski(A_196,k2_relat_1('#skF_6'))
      | v1_xboole_0(A_196) ) ),
    inference(resolution,[status(thm)],[c_842,c_26])).

tff(c_918,plain,(
    ! [A_196] :
      ( ~ r1_tarski(k1_relat_1('#skF_7'),k1_xboole_0)
      | ~ r1_tarski(A_196,k2_relat_1('#skF_6'))
      | v1_xboole_0(A_196) ) ),
    inference(resolution,[status(thm)],[c_18,c_906])).

tff(c_967,plain,(
    ~ r1_tarski(k1_relat_1('#skF_7'),k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_918])).

tff(c_2535,plain,(
    ~ r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2522,c_967])).

tff(c_2564,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_2535])).

tff(c_2567,plain,(
    ! [A_373] :
      ( r2_hidden(k1_funct_1('#skF_6',A_373),k1_relat_1('#skF_7'))
      | ~ m1_subset_1(A_373,'#skF_4') ) ),
    inference(splitRight,[status(thm)],[c_2521])).

tff(c_44,plain,(
    ! [A_35,B_36,C_38] :
      ( k7_partfun1(A_35,B_36,C_38) = k1_funct_1(B_36,C_38)
      | ~ r2_hidden(C_38,k1_relat_1(B_36))
      | ~ v1_funct_1(B_36)
      | ~ v5_relat_1(B_36,A_35)
      | ~ v1_relat_1(B_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_2571,plain,(
    ! [A_35,A_373] :
      ( k7_partfun1(A_35,'#skF_7',k1_funct_1('#skF_6',A_373)) = k1_funct_1('#skF_7',k1_funct_1('#skF_6',A_373))
      | ~ v1_funct_1('#skF_7')
      | ~ v5_relat_1('#skF_7',A_35)
      | ~ v1_relat_1('#skF_7')
      | ~ m1_subset_1(A_373,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_2567,c_44])).

tff(c_2852,plain,(
    ! [A_409,A_410] :
      ( k7_partfun1(A_409,'#skF_7',k1_funct_1('#skF_6',A_410)) = k1_funct_1('#skF_7',k1_funct_1('#skF_6',A_410))
      | ~ v5_relat_1('#skF_7',A_409)
      | ~ m1_subset_1(A_410,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_115,c_72,c_2571])).

tff(c_62,plain,(
    k7_partfun1('#skF_3','#skF_7',k1_funct_1('#skF_6','#skF_8')) != k1_funct_1(k8_funct_2('#skF_4','#skF_5','#skF_3','#skF_6','#skF_7'),'#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_198])).

tff(c_2858,plain,
    ( k1_funct_1(k8_funct_2('#skF_4','#skF_5','#skF_3','#skF_6','#skF_7'),'#skF_8') != k1_funct_1('#skF_7',k1_funct_1('#skF_6','#skF_8'))
    | ~ v5_relat_1('#skF_7','#skF_3')
    | ~ m1_subset_1('#skF_8','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_2852,c_62])).

tff(c_2864,plain,(
    k1_funct_1(k8_funct_2('#skF_4','#skF_5','#skF_3','#skF_6','#skF_7'),'#skF_8') != k1_funct_1('#skF_7',k1_funct_1('#skF_6','#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_273,c_2858])).

tff(c_2868,plain,(
    ~ m1_subset_1('#skF_8','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1285,c_2864])).

tff(c_2872,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_2868])).

tff(c_2874,plain,(
    r1_tarski(k1_relat_1('#skF_7'),k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_918])).

tff(c_860,plain,(
    ! [B_188,A_187] :
      ( ~ v1_xboole_0(B_188)
      | ~ r1_tarski(k1_relat_1('#skF_7'),B_188)
      | ~ r1_tarski(A_187,k2_relat_1('#skF_6'))
      | v1_xboole_0(A_187) ) ),
    inference(resolution,[status(thm)],[c_842,c_2])).

tff(c_894,plain,(
    ! [B_188] :
      ( ~ v1_xboole_0(B_188)
      | ~ r1_tarski(k1_relat_1('#skF_7'),B_188) ) ),
    inference(splitLeft,[status(thm)],[c_860])).

tff(c_2877,plain,(
    ~ v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_2874,c_894])).

tff(c_2915,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_101,c_2877])).

tff(c_2917,plain,(
    ! [A_411] :
      ( ~ r1_tarski(A_411,k2_relat_1('#skF_6'))
      | v1_xboole_0(A_411) ) ),
    inference(splitRight,[status(thm)],[c_860])).

tff(c_2925,plain,(
    v1_xboole_0(k2_relat_1('#skF_6')) ),
    inference(resolution,[status(thm)],[c_16,c_2917])).

tff(c_2934,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_618,c_2925])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:14:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.42/2.03  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.42/2.04  
% 5.42/2.04  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.42/2.05  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k8_funct_2 > k7_partfun1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_3 > #skF_8 > #skF_4 > #skF_2
% 5.42/2.05  
% 5.42/2.05  %Foreground sorts:
% 5.42/2.05  
% 5.42/2.05  
% 5.42/2.05  %Background operators:
% 5.42/2.05  
% 5.42/2.05  
% 5.42/2.05  %Foreground operators:
% 5.42/2.05  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 5.42/2.05  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 5.42/2.05  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.42/2.05  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.42/2.05  tff('#skF_1', type, '#skF_1': $i > $i).
% 5.42/2.05  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.42/2.05  tff('#skF_7', type, '#skF_7': $i).
% 5.42/2.05  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.42/2.05  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 5.42/2.05  tff(k7_partfun1, type, k7_partfun1: ($i * $i * $i) > $i).
% 5.42/2.05  tff('#skF_5', type, '#skF_5': $i).
% 5.42/2.05  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 5.42/2.05  tff(k8_funct_2, type, k8_funct_2: ($i * $i * $i * $i * $i) > $i).
% 5.42/2.05  tff('#skF_6', type, '#skF_6': $i).
% 5.42/2.05  tff('#skF_3', type, '#skF_3': $i).
% 5.42/2.05  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 5.42/2.05  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 5.42/2.05  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.42/2.05  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 5.42/2.05  tff('#skF_8', type, '#skF_8': $i).
% 5.42/2.05  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.42/2.05  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.42/2.05  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 5.42/2.05  tff('#skF_4', type, '#skF_4': $i).
% 5.42/2.05  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.42/2.05  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 5.42/2.05  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 5.42/2.05  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 5.42/2.05  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 5.42/2.05  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.42/2.05  
% 5.78/2.07  tff(f_198, negated_conjecture, ~(![A, B, C]: (~v1_xboole_0(C) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, C)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (![E]: ((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(C, A)))) => (![F]: (m1_subset_1(F, B) => (r1_tarski(k2_relset_1(B, C, D), k1_relset_1(C, A, E)) => ((B = k1_xboole_0) | (k1_funct_1(k8_funct_2(B, C, A, D, E), F) = k7_partfun1(A, E, k1_funct_1(D, F))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t186_funct_2)).
% 5.78/2.07  tff(f_73, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 5.78/2.07  tff(f_83, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 5.78/2.07  tff(f_87, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 5.78/2.07  tff(f_52, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 5.78/2.07  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 5.78/2.07  tff(f_60, axiom, (![A]: ((~v1_xboole_0(A) & v1_relat_1(A)) => ~v1_xboole_0(k2_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc9_relat_1)).
% 5.78/2.07  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 5.78/2.07  tff(f_46, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 5.78/2.07  tff(f_44, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 5.78/2.07  tff(f_107, axiom, (![A, B]: ((~v1_xboole_0(A) & ~v1_xboole_0(B)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) => ((v1_funct_1(C) & ~v1_xboole_0(C)) & v1_funct_2(C, A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc6_funct_2)).
% 5.78/2.07  tff(f_69, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 5.78/2.07  tff(f_142, axiom, (![A, B, C]: (~v1_xboole_0(C) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, C)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (![E]: ((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(C, A)))) => (![F]: (m1_subset_1(F, B) => (r1_tarski(k2_relset_1(B, C, D), k1_relset_1(C, A, E)) => ((B = k1_xboole_0) | (k1_funct_1(k8_funct_2(B, C, A, D, E), F) = k1_funct_1(E, k1_funct_1(D, F))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t185_funct_2)).
% 5.78/2.07  tff(f_79, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 5.78/2.07  tff(f_173, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r1_tarski(k2_relset_1(A, B, D), C) => (((B = k1_xboole_0) & ~(A = k1_xboole_0)) | ((v1_funct_1(D) & v1_funct_2(D, A, C)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_funct_2)).
% 5.78/2.07  tff(f_154, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_hidden(C, A) => ((B = k1_xboole_0) | r2_hidden(k1_funct_1(D, C), B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_funct_2)).
% 5.78/2.07  tff(f_118, axiom, (![A, B]: (((v1_relat_1(B) & v5_relat_1(B, A)) & v1_funct_1(B)) => (![C]: (r2_hidden(C, k1_relat_1(B)) => (k7_partfun1(A, B, C) = k1_funct_1(B, C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_partfun1)).
% 5.78/2.07  tff(c_74, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_5')))), inference(cnfTransformation, [status(thm)], [f_198])).
% 5.78/2.07  tff(c_107, plain, (![C_85, A_86, B_87]: (v1_relat_1(C_85) | ~m1_subset_1(C_85, k1_zfmisc_1(k2_zfmisc_1(A_86, B_87))))), inference(cnfTransformation, [status(thm)], [f_73])).
% 5.78/2.07  tff(c_114, plain, (v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_74, c_107])).
% 5.78/2.07  tff(c_70, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_198])).
% 5.78/2.07  tff(c_370, plain, (![A_130, B_131, C_132]: (k1_relset_1(A_130, B_131, C_132)=k1_relat_1(C_132) | ~m1_subset_1(C_132, k1_zfmisc_1(k2_zfmisc_1(A_130, B_131))))), inference(cnfTransformation, [status(thm)], [f_83])).
% 5.78/2.07  tff(c_378, plain, (k1_relset_1('#skF_5', '#skF_3', '#skF_7')=k1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_70, c_370])).
% 5.78/2.07  tff(c_286, plain, (![A_120, B_121, C_122]: (k2_relset_1(A_120, B_121, C_122)=k2_relat_1(C_122) | ~m1_subset_1(C_122, k1_zfmisc_1(k2_zfmisc_1(A_120, B_121))))), inference(cnfTransformation, [status(thm)], [f_87])).
% 5.78/2.07  tff(c_293, plain, (k2_relset_1('#skF_4', '#skF_5', '#skF_6')=k2_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_74, c_286])).
% 5.78/2.07  tff(c_66, plain, (r1_tarski(k2_relset_1('#skF_4', '#skF_5', '#skF_6'), k1_relset_1('#skF_5', '#skF_3', '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_198])).
% 5.78/2.07  tff(c_295, plain, (r1_tarski(k2_relat_1('#skF_6'), k1_relset_1('#skF_5', '#skF_3', '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_293, c_66])).
% 5.78/2.07  tff(c_384, plain, (r1_tarski(k2_relat_1('#skF_6'), k1_relat_1('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_378, c_295])).
% 5.78/2.07  tff(c_20, plain, (![A_13, B_14]: (r2_hidden(A_13, B_14) | v1_xboole_0(B_14) | ~m1_subset_1(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_52])).
% 5.78/2.07  tff(c_245, plain, (![C_109, B_110, A_111]: (r2_hidden(C_109, B_110) | ~r2_hidden(C_109, A_111) | ~r1_tarski(A_111, B_110))), inference(cnfTransformation, [status(thm)], [f_38])).
% 5.78/2.07  tff(c_429, plain, (![A_136, B_137, B_138]: (r2_hidden(A_136, B_137) | ~r1_tarski(B_138, B_137) | v1_xboole_0(B_138) | ~m1_subset_1(A_136, B_138))), inference(resolution, [status(thm)], [c_20, c_245])).
% 5.78/2.07  tff(c_438, plain, (![A_136]: (r2_hidden(A_136, k1_relat_1('#skF_7')) | v1_xboole_0(k2_relat_1('#skF_6')) | ~m1_subset_1(A_136, k2_relat_1('#skF_6')))), inference(resolution, [status(thm)], [c_384, c_429])).
% 5.78/2.07  tff(c_479, plain, (v1_xboole_0(k2_relat_1('#skF_6'))), inference(splitLeft, [status(thm)], [c_438])).
% 5.78/2.07  tff(c_22, plain, (![A_15]: (~v1_xboole_0(k2_relat_1(A_15)) | ~v1_relat_1(A_15) | v1_xboole_0(A_15))), inference(cnfTransformation, [status(thm)], [f_60])).
% 5.78/2.07  tff(c_487, plain, (~v1_relat_1('#skF_6') | v1_xboole_0('#skF_6')), inference(resolution, [status(thm)], [c_479, c_22])).
% 5.78/2.07  tff(c_495, plain, (v1_xboole_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_114, c_487])).
% 5.78/2.07  tff(c_142, plain, (![A_91, B_92]: (r2_hidden('#skF_2'(A_91, B_92), A_91) | r1_tarski(A_91, B_92))), inference(cnfTransformation, [status(thm)], [f_38])).
% 5.78/2.07  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.78/2.07  tff(c_158, plain, (![A_95, B_96]: (~v1_xboole_0(A_95) | r1_tarski(A_95, B_96))), inference(resolution, [status(thm)], [c_142, c_2])).
% 5.78/2.07  tff(c_18, plain, (![A_12]: (r1_tarski(k1_xboole_0, A_12))), inference(cnfTransformation, [status(thm)], [f_46])).
% 5.78/2.07  tff(c_116, plain, (![B_88, A_89]: (B_88=A_89 | ~r1_tarski(B_88, A_89) | ~r1_tarski(A_89, B_88))), inference(cnfTransformation, [status(thm)], [f_44])).
% 5.78/2.07  tff(c_128, plain, (![A_12]: (k1_xboole_0=A_12 | ~r1_tarski(A_12, k1_xboole_0))), inference(resolution, [status(thm)], [c_18, c_116])).
% 5.78/2.07  tff(c_169, plain, (![A_95]: (k1_xboole_0=A_95 | ~v1_xboole_0(A_95))), inference(resolution, [status(thm)], [c_158, c_128])).
% 5.78/2.07  tff(c_506, plain, (k1_xboole_0='#skF_6'), inference(resolution, [status(thm)], [c_495, c_169])).
% 5.78/2.07  tff(c_64, plain, (k1_xboole_0!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_198])).
% 5.78/2.07  tff(c_515, plain, ('#skF_6'!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_506, c_64])).
% 5.78/2.07  tff(c_80, plain, (~v1_xboole_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_198])).
% 5.78/2.07  tff(c_78, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_198])).
% 5.78/2.07  tff(c_76, plain, (v1_funct_2('#skF_6', '#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_198])).
% 5.78/2.07  tff(c_522, plain, (![C_145, A_146, B_147]: (~v1_xboole_0(C_145) | ~v1_funct_2(C_145, A_146, B_147) | ~v1_funct_1(C_145) | ~m1_subset_1(C_145, k1_zfmisc_1(k2_zfmisc_1(A_146, B_147))) | v1_xboole_0(B_147) | v1_xboole_0(A_146))), inference(cnfTransformation, [status(thm)], [f_107])).
% 5.78/2.07  tff(c_525, plain, (~v1_xboole_0('#skF_6') | ~v1_funct_2('#skF_6', '#skF_4', '#skF_5') | ~v1_funct_1('#skF_6') | v1_xboole_0('#skF_5') | v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_74, c_522])).
% 5.78/2.07  tff(c_531, plain, (v1_xboole_0('#skF_5') | v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_495, c_525])).
% 5.78/2.07  tff(c_532, plain, (v1_xboole_0('#skF_4')), inference(negUnitSimplification, [status(thm)], [c_80, c_531])).
% 5.78/2.07  tff(c_606, plain, (![A_149]: (A_149='#skF_6' | ~v1_xboole_0(A_149))), inference(demodulation, [status(thm), theory('equality')], [c_506, c_169])).
% 5.78/2.07  tff(c_609, plain, ('#skF_6'='#skF_4'), inference(resolution, [status(thm)], [c_532, c_606])).
% 5.78/2.07  tff(c_616, plain, $false, inference(negUnitSimplification, [status(thm)], [c_515, c_609])).
% 5.78/2.07  tff(c_618, plain, (~v1_xboole_0(k2_relat_1('#skF_6'))), inference(splitRight, [status(thm)], [c_438])).
% 5.78/2.07  tff(c_16, plain, (![B_11]: (r1_tarski(B_11, B_11))), inference(cnfTransformation, [status(thm)], [f_44])).
% 5.78/2.07  tff(c_87, plain, (![A_82]: (v1_xboole_0(A_82) | r2_hidden('#skF_1'(A_82), A_82))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.78/2.07  tff(c_26, plain, (![B_18, A_17]: (~r1_tarski(B_18, A_17) | ~r2_hidden(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_69])).
% 5.78/2.07  tff(c_96, plain, (![A_83]: (~r1_tarski(A_83, '#skF_1'(A_83)) | v1_xboole_0(A_83))), inference(resolution, [status(thm)], [c_87, c_26])).
% 5.78/2.07  tff(c_101, plain, (v1_xboole_0(k1_xboole_0)), inference(resolution, [status(thm)], [c_18, c_96])).
% 5.78/2.07  tff(c_68, plain, (m1_subset_1('#skF_8', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_198])).
% 5.78/2.07  tff(c_72, plain, (v1_funct_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_198])).
% 5.78/2.07  tff(c_1190, plain, (![A_241, F_246, C_245, D_244, E_243, B_242]: (k1_funct_1(k8_funct_2(B_242, C_245, A_241, D_244, E_243), F_246)=k1_funct_1(E_243, k1_funct_1(D_244, F_246)) | k1_xboole_0=B_242 | ~r1_tarski(k2_relset_1(B_242, C_245, D_244), k1_relset_1(C_245, A_241, E_243)) | ~m1_subset_1(F_246, B_242) | ~m1_subset_1(E_243, k1_zfmisc_1(k2_zfmisc_1(C_245, A_241))) | ~v1_funct_1(E_243) | ~m1_subset_1(D_244, k1_zfmisc_1(k2_zfmisc_1(B_242, C_245))) | ~v1_funct_2(D_244, B_242, C_245) | ~v1_funct_1(D_244) | v1_xboole_0(C_245))), inference(cnfTransformation, [status(thm)], [f_142])).
% 5.78/2.07  tff(c_1202, plain, (![A_241, E_243, F_246]: (k1_funct_1(k8_funct_2('#skF_4', '#skF_5', A_241, '#skF_6', E_243), F_246)=k1_funct_1(E_243, k1_funct_1('#skF_6', F_246)) | k1_xboole_0='#skF_4' | ~r1_tarski(k2_relat_1('#skF_6'), k1_relset_1('#skF_5', A_241, E_243)) | ~m1_subset_1(F_246, '#skF_4') | ~m1_subset_1(E_243, k1_zfmisc_1(k2_zfmisc_1('#skF_5', A_241))) | ~v1_funct_1(E_243) | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_5'))) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_5') | ~v1_funct_1('#skF_6') | v1_xboole_0('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_293, c_1190])).
% 5.78/2.07  tff(c_1219, plain, (![A_241, E_243, F_246]: (k1_funct_1(k8_funct_2('#skF_4', '#skF_5', A_241, '#skF_6', E_243), F_246)=k1_funct_1(E_243, k1_funct_1('#skF_6', F_246)) | k1_xboole_0='#skF_4' | ~r1_tarski(k2_relat_1('#skF_6'), k1_relset_1('#skF_5', A_241, E_243)) | ~m1_subset_1(F_246, '#skF_4') | ~m1_subset_1(E_243, k1_zfmisc_1(k2_zfmisc_1('#skF_5', A_241))) | ~v1_funct_1(E_243) | v1_xboole_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_74, c_1202])).
% 5.78/2.07  tff(c_1278, plain, (![A_250, E_251, F_252]: (k1_funct_1(k8_funct_2('#skF_4', '#skF_5', A_250, '#skF_6', E_251), F_252)=k1_funct_1(E_251, k1_funct_1('#skF_6', F_252)) | ~r1_tarski(k2_relat_1('#skF_6'), k1_relset_1('#skF_5', A_250, E_251)) | ~m1_subset_1(F_252, '#skF_4') | ~m1_subset_1(E_251, k1_zfmisc_1(k2_zfmisc_1('#skF_5', A_250))) | ~v1_funct_1(E_251))), inference(negUnitSimplification, [status(thm)], [c_80, c_64, c_1219])).
% 5.78/2.07  tff(c_1280, plain, (![F_252]: (k1_funct_1(k8_funct_2('#skF_4', '#skF_5', '#skF_3', '#skF_6', '#skF_7'), F_252)=k1_funct_1('#skF_7', k1_funct_1('#skF_6', F_252)) | ~r1_tarski(k2_relat_1('#skF_6'), k1_relat_1('#skF_7')) | ~m1_subset_1(F_252, '#skF_4') | ~m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_3'))) | ~v1_funct_1('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_378, c_1278])).
% 5.78/2.07  tff(c_1285, plain, (![F_252]: (k1_funct_1(k8_funct_2('#skF_4', '#skF_5', '#skF_3', '#skF_6', '#skF_7'), F_252)=k1_funct_1('#skF_7', k1_funct_1('#skF_6', F_252)) | ~m1_subset_1(F_252, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_384, c_1280])).
% 5.78/2.07  tff(c_265, plain, (![C_115, B_116, A_117]: (v5_relat_1(C_115, B_116) | ~m1_subset_1(C_115, k1_zfmisc_1(k2_zfmisc_1(A_117, B_116))))), inference(cnfTransformation, [status(thm)], [f_79])).
% 5.78/2.07  tff(c_273, plain, (v5_relat_1('#skF_7', '#skF_3')), inference(resolution, [status(thm)], [c_70, c_265])).
% 5.78/2.07  tff(c_115, plain, (v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_70, c_107])).
% 5.78/2.07  tff(c_919, plain, (![B_197, D_198, A_199, C_200]: (k1_xboole_0=B_197 | v1_funct_2(D_198, A_199, C_200) | ~r1_tarski(k2_relset_1(A_199, B_197, D_198), C_200) | ~m1_subset_1(D_198, k1_zfmisc_1(k2_zfmisc_1(A_199, B_197))) | ~v1_funct_2(D_198, A_199, B_197) | ~v1_funct_1(D_198))), inference(cnfTransformation, [status(thm)], [f_173])).
% 5.78/2.07  tff(c_923, plain, (![C_200]: (k1_xboole_0='#skF_5' | v1_funct_2('#skF_6', '#skF_4', C_200) | ~r1_tarski(k2_relat_1('#skF_6'), C_200) | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_5'))) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_5') | ~v1_funct_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_293, c_919])).
% 5.78/2.07  tff(c_933, plain, (![C_200]: (k1_xboole_0='#skF_5' | v1_funct_2('#skF_6', '#skF_4', C_200) | ~r1_tarski(k2_relat_1('#skF_6'), C_200))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_74, c_923])).
% 5.78/2.07  tff(c_936, plain, (k1_xboole_0='#skF_5'), inference(splitLeft, [status(thm)], [c_933])).
% 5.78/2.07  tff(c_945, plain, (v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_936, c_101])).
% 5.78/2.07  tff(c_949, plain, $false, inference(negUnitSimplification, [status(thm)], [c_80, c_945])).
% 5.78/2.07  tff(c_951, plain, (k1_xboole_0!='#skF_5'), inference(splitRight, [status(thm)], [c_933])).
% 5.78/2.07  tff(c_812, plain, (![D_180, C_181, B_182, A_183]: (r2_hidden(k1_funct_1(D_180, C_181), B_182) | k1_xboole_0=B_182 | ~r2_hidden(C_181, A_183) | ~m1_subset_1(D_180, k1_zfmisc_1(k2_zfmisc_1(A_183, B_182))) | ~v1_funct_2(D_180, A_183, B_182) | ~v1_funct_1(D_180))), inference(cnfTransformation, [status(thm)], [f_154])).
% 5.78/2.07  tff(c_1998, plain, (![D_319, A_320, B_321, B_322]: (r2_hidden(k1_funct_1(D_319, A_320), B_321) | k1_xboole_0=B_321 | ~m1_subset_1(D_319, k1_zfmisc_1(k2_zfmisc_1(B_322, B_321))) | ~v1_funct_2(D_319, B_322, B_321) | ~v1_funct_1(D_319) | v1_xboole_0(B_322) | ~m1_subset_1(A_320, B_322))), inference(resolution, [status(thm)], [c_20, c_812])).
% 5.78/2.07  tff(c_2010, plain, (![A_320]: (r2_hidden(k1_funct_1('#skF_6', A_320), '#skF_5') | k1_xboole_0='#skF_5' | ~v1_funct_2('#skF_6', '#skF_4', '#skF_5') | ~v1_funct_1('#skF_6') | v1_xboole_0('#skF_4') | ~m1_subset_1(A_320, '#skF_4'))), inference(resolution, [status(thm)], [c_74, c_1998])).
% 5.78/2.07  tff(c_2027, plain, (![A_320]: (r2_hidden(k1_funct_1('#skF_6', A_320), '#skF_5') | k1_xboole_0='#skF_5' | v1_xboole_0('#skF_4') | ~m1_subset_1(A_320, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_2010])).
% 5.78/2.07  tff(c_2028, plain, (![A_320]: (r2_hidden(k1_funct_1('#skF_6', A_320), '#skF_5') | v1_xboole_0('#skF_4') | ~m1_subset_1(A_320, '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_951, c_2027])).
% 5.78/2.07  tff(c_2033, plain, (v1_xboole_0('#skF_4')), inference(splitLeft, [status(thm)], [c_2028])).
% 5.78/2.07  tff(c_2038, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_2033, c_169])).
% 5.78/2.07  tff(c_2046, plain, $false, inference(negUnitSimplification, [status(thm)], [c_64, c_2038])).
% 5.78/2.07  tff(c_2048, plain, (~v1_xboole_0('#skF_4')), inference(splitRight, [status(thm)], [c_2028])).
% 5.78/2.07  tff(c_952, plain, (![C_201]: (v1_funct_2('#skF_6', '#skF_4', C_201) | ~r1_tarski(k2_relat_1('#skF_6'), C_201))), inference(splitRight, [status(thm)], [c_933])).
% 5.78/2.07  tff(c_964, plain, (v1_funct_2('#skF_6', '#skF_4', k1_relat_1('#skF_7'))), inference(resolution, [status(thm)], [c_384, c_952])).
% 5.78/2.07  tff(c_1089, plain, (![B_229, D_230, A_231, C_232]: (k1_xboole_0=B_229 | m1_subset_1(D_230, k1_zfmisc_1(k2_zfmisc_1(A_231, C_232))) | ~r1_tarski(k2_relset_1(A_231, B_229, D_230), C_232) | ~m1_subset_1(D_230, k1_zfmisc_1(k2_zfmisc_1(A_231, B_229))) | ~v1_funct_2(D_230, A_231, B_229) | ~v1_funct_1(D_230))), inference(cnfTransformation, [status(thm)], [f_173])).
% 5.78/2.07  tff(c_1093, plain, (![C_232]: (k1_xboole_0='#skF_5' | m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', C_232))) | ~r1_tarski(k2_relat_1('#skF_6'), C_232) | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_5'))) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_5') | ~v1_funct_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_293, c_1089])).
% 5.78/2.07  tff(c_1103, plain, (![C_232]: (k1_xboole_0='#skF_5' | m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', C_232))) | ~r1_tarski(k2_relat_1('#skF_6'), C_232))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_74, c_1093])).
% 5.78/2.07  tff(c_1104, plain, (![C_232]: (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', C_232))) | ~r1_tarski(k2_relat_1('#skF_6'), C_232))), inference(negUnitSimplification, [status(thm)], [c_951, c_1103])).
% 5.78/2.07  tff(c_12, plain, (![B_11, A_10]: (B_11=A_10 | ~r1_tarski(B_11, A_10) | ~r1_tarski(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_44])).
% 5.78/2.07  tff(c_178, plain, (![B_98, A_99]: (B_98=A_99 | ~r1_tarski(B_98, A_99) | ~v1_xboole_0(A_99))), inference(resolution, [status(thm)], [c_158, c_12])).
% 5.78/2.07  tff(c_192, plain, (k2_relset_1('#skF_4', '#skF_5', '#skF_6')=k1_relset_1('#skF_5', '#skF_3', '#skF_7') | ~v1_xboole_0(k1_relset_1('#skF_5', '#skF_3', '#skF_7'))), inference(resolution, [status(thm)], [c_66, c_178])).
% 5.78/2.07  tff(c_264, plain, (~v1_xboole_0(k1_relset_1('#skF_5', '#skF_3', '#skF_7'))), inference(splitLeft, [status(thm)], [c_192])).
% 5.78/2.07  tff(c_385, plain, (~v1_xboole_0(k1_relat_1('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_378, c_264])).
% 5.78/2.07  tff(c_1107, plain, (![C_233]: (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', C_233))) | ~r1_tarski(k2_relat_1('#skF_6'), C_233))), inference(negUnitSimplification, [status(thm)], [c_951, c_1103])).
% 5.78/2.07  tff(c_36, plain, (![A_28, B_29, C_30]: (k2_relset_1(A_28, B_29, C_30)=k2_relat_1(C_30) | ~m1_subset_1(C_30, k1_zfmisc_1(k2_zfmisc_1(A_28, B_29))))), inference(cnfTransformation, [status(thm)], [f_87])).
% 5.78/2.07  tff(c_1175, plain, (![C_240]: (k2_relset_1('#skF_4', C_240, '#skF_6')=k2_relat_1('#skF_6') | ~r1_tarski(k2_relat_1('#skF_6'), C_240))), inference(resolution, [status(thm)], [c_1107, c_36])).
% 5.78/2.07  tff(c_1187, plain, (k2_relset_1('#skF_4', k1_relat_1('#skF_7'), '#skF_6')=k2_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_384, c_1175])).
% 5.78/2.07  tff(c_46, plain, (![D_49, F_55, A_39, C_41, B_40, E_53]: (k1_funct_1(k8_funct_2(B_40, C_41, A_39, D_49, E_53), F_55)=k1_funct_1(E_53, k1_funct_1(D_49, F_55)) | k1_xboole_0=B_40 | ~r1_tarski(k2_relset_1(B_40, C_41, D_49), k1_relset_1(C_41, A_39, E_53)) | ~m1_subset_1(F_55, B_40) | ~m1_subset_1(E_53, k1_zfmisc_1(k2_zfmisc_1(C_41, A_39))) | ~v1_funct_1(E_53) | ~m1_subset_1(D_49, k1_zfmisc_1(k2_zfmisc_1(B_40, C_41))) | ~v1_funct_2(D_49, B_40, C_41) | ~v1_funct_1(D_49) | v1_xboole_0(C_41))), inference(cnfTransformation, [status(thm)], [f_142])).
% 5.78/2.07  tff(c_1224, plain, (![A_39, E_53, F_55]: (k1_funct_1(k8_funct_2('#skF_4', k1_relat_1('#skF_7'), A_39, '#skF_6', E_53), F_55)=k1_funct_1(E_53, k1_funct_1('#skF_6', F_55)) | k1_xboole_0='#skF_4' | ~r1_tarski(k2_relat_1('#skF_6'), k1_relset_1(k1_relat_1('#skF_7'), A_39, E_53)) | ~m1_subset_1(F_55, '#skF_4') | ~m1_subset_1(E_53, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_7'), A_39))) | ~v1_funct_1(E_53) | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', k1_relat_1('#skF_7')))) | ~v1_funct_2('#skF_6', '#skF_4', k1_relat_1('#skF_7')) | ~v1_funct_1('#skF_6') | v1_xboole_0(k1_relat_1('#skF_7')))), inference(superposition, [status(thm), theory('equality')], [c_1187, c_46])).
% 5.78/2.07  tff(c_1232, plain, (![A_39, E_53, F_55]: (k1_funct_1(k8_funct_2('#skF_4', k1_relat_1('#skF_7'), A_39, '#skF_6', E_53), F_55)=k1_funct_1(E_53, k1_funct_1('#skF_6', F_55)) | k1_xboole_0='#skF_4' | ~r1_tarski(k2_relat_1('#skF_6'), k1_relset_1(k1_relat_1('#skF_7'), A_39, E_53)) | ~m1_subset_1(F_55, '#skF_4') | ~m1_subset_1(E_53, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_7'), A_39))) | ~v1_funct_1(E_53) | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', k1_relat_1('#skF_7')))) | v1_xboole_0(k1_relat_1('#skF_7')))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_964, c_1224])).
% 5.78/2.07  tff(c_1233, plain, (![A_39, E_53, F_55]: (k1_funct_1(k8_funct_2('#skF_4', k1_relat_1('#skF_7'), A_39, '#skF_6', E_53), F_55)=k1_funct_1(E_53, k1_funct_1('#skF_6', F_55)) | ~r1_tarski(k2_relat_1('#skF_6'), k1_relset_1(k1_relat_1('#skF_7'), A_39, E_53)) | ~m1_subset_1(F_55, '#skF_4') | ~m1_subset_1(E_53, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_7'), A_39))) | ~v1_funct_1(E_53) | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', k1_relat_1('#skF_7')))))), inference(negUnitSimplification, [status(thm)], [c_385, c_64, c_1232])).
% 5.78/2.07  tff(c_1680, plain, (~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', k1_relat_1('#skF_7'))))), inference(splitLeft, [status(thm)], [c_1233])).
% 5.78/2.07  tff(c_1683, plain, (~r1_tarski(k2_relat_1('#skF_6'), k1_relat_1('#skF_7'))), inference(resolution, [status(thm)], [c_1104, c_1680])).
% 5.78/2.07  tff(c_1687, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_384, c_1683])).
% 5.78/2.07  tff(c_1689, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', k1_relat_1('#skF_7'))))), inference(splitRight, [status(thm)], [c_1233])).
% 5.78/2.07  tff(c_2000, plain, (![A_320]: (r2_hidden(k1_funct_1('#skF_6', A_320), k1_relat_1('#skF_7')) | k1_relat_1('#skF_7')=k1_xboole_0 | ~v1_funct_2('#skF_6', '#skF_4', k1_relat_1('#skF_7')) | ~v1_funct_1('#skF_6') | v1_xboole_0('#skF_4') | ~m1_subset_1(A_320, '#skF_4'))), inference(resolution, [status(thm)], [c_1689, c_1998])).
% 5.78/2.07  tff(c_2015, plain, (![A_320]: (r2_hidden(k1_funct_1('#skF_6', A_320), k1_relat_1('#skF_7')) | k1_relat_1('#skF_7')=k1_xboole_0 | v1_xboole_0('#skF_4') | ~m1_subset_1(A_320, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_964, c_2000])).
% 5.78/2.07  tff(c_2521, plain, (![A_320]: (r2_hidden(k1_funct_1('#skF_6', A_320), k1_relat_1('#skF_7')) | k1_relat_1('#skF_7')=k1_xboole_0 | ~m1_subset_1(A_320, '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_2048, c_2015])).
% 5.78/2.07  tff(c_2522, plain, (k1_relat_1('#skF_7')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_2521])).
% 5.78/2.07  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.78/2.07  tff(c_274, plain, (![A_118, B_119]: (r2_hidden('#skF_1'(A_118), B_119) | ~r1_tarski(A_118, B_119) | v1_xboole_0(A_118))), inference(resolution, [status(thm)], [c_4, c_245])).
% 5.78/2.07  tff(c_6, plain, (![C_9, B_6, A_5]: (r2_hidden(C_9, B_6) | ~r2_hidden(C_9, A_5) | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_38])).
% 5.78/2.07  tff(c_719, plain, (![A_166, B_167, B_168]: (r2_hidden('#skF_1'(A_166), B_167) | ~r1_tarski(B_168, B_167) | ~r1_tarski(A_166, B_168) | v1_xboole_0(A_166))), inference(resolution, [status(thm)], [c_274, c_6])).
% 5.78/2.07  tff(c_732, plain, (![A_169]: (r2_hidden('#skF_1'(A_169), k1_relat_1('#skF_7')) | ~r1_tarski(A_169, k2_relat_1('#skF_6')) | v1_xboole_0(A_169))), inference(resolution, [status(thm)], [c_384, c_719])).
% 5.78/2.07  tff(c_842, plain, (![A_187, B_188]: (r2_hidden('#skF_1'(A_187), B_188) | ~r1_tarski(k1_relat_1('#skF_7'), B_188) | ~r1_tarski(A_187, k2_relat_1('#skF_6')) | v1_xboole_0(A_187))), inference(resolution, [status(thm)], [c_732, c_6])).
% 5.78/2.07  tff(c_906, plain, (![B_195, A_196]: (~r1_tarski(B_195, '#skF_1'(A_196)) | ~r1_tarski(k1_relat_1('#skF_7'), B_195) | ~r1_tarski(A_196, k2_relat_1('#skF_6')) | v1_xboole_0(A_196))), inference(resolution, [status(thm)], [c_842, c_26])).
% 5.78/2.07  tff(c_918, plain, (![A_196]: (~r1_tarski(k1_relat_1('#skF_7'), k1_xboole_0) | ~r1_tarski(A_196, k2_relat_1('#skF_6')) | v1_xboole_0(A_196))), inference(resolution, [status(thm)], [c_18, c_906])).
% 5.78/2.07  tff(c_967, plain, (~r1_tarski(k1_relat_1('#skF_7'), k1_xboole_0)), inference(splitLeft, [status(thm)], [c_918])).
% 5.78/2.07  tff(c_2535, plain, (~r1_tarski(k1_xboole_0, k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_2522, c_967])).
% 5.78/2.07  tff(c_2564, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_16, c_2535])).
% 5.78/2.07  tff(c_2567, plain, (![A_373]: (r2_hidden(k1_funct_1('#skF_6', A_373), k1_relat_1('#skF_7')) | ~m1_subset_1(A_373, '#skF_4'))), inference(splitRight, [status(thm)], [c_2521])).
% 5.78/2.07  tff(c_44, plain, (![A_35, B_36, C_38]: (k7_partfun1(A_35, B_36, C_38)=k1_funct_1(B_36, C_38) | ~r2_hidden(C_38, k1_relat_1(B_36)) | ~v1_funct_1(B_36) | ~v5_relat_1(B_36, A_35) | ~v1_relat_1(B_36))), inference(cnfTransformation, [status(thm)], [f_118])).
% 5.78/2.07  tff(c_2571, plain, (![A_35, A_373]: (k7_partfun1(A_35, '#skF_7', k1_funct_1('#skF_6', A_373))=k1_funct_1('#skF_7', k1_funct_1('#skF_6', A_373)) | ~v1_funct_1('#skF_7') | ~v5_relat_1('#skF_7', A_35) | ~v1_relat_1('#skF_7') | ~m1_subset_1(A_373, '#skF_4'))), inference(resolution, [status(thm)], [c_2567, c_44])).
% 5.78/2.07  tff(c_2852, plain, (![A_409, A_410]: (k7_partfun1(A_409, '#skF_7', k1_funct_1('#skF_6', A_410))=k1_funct_1('#skF_7', k1_funct_1('#skF_6', A_410)) | ~v5_relat_1('#skF_7', A_409) | ~m1_subset_1(A_410, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_115, c_72, c_2571])).
% 5.78/2.07  tff(c_62, plain, (k7_partfun1('#skF_3', '#skF_7', k1_funct_1('#skF_6', '#skF_8'))!=k1_funct_1(k8_funct_2('#skF_4', '#skF_5', '#skF_3', '#skF_6', '#skF_7'), '#skF_8')), inference(cnfTransformation, [status(thm)], [f_198])).
% 5.78/2.07  tff(c_2858, plain, (k1_funct_1(k8_funct_2('#skF_4', '#skF_5', '#skF_3', '#skF_6', '#skF_7'), '#skF_8')!=k1_funct_1('#skF_7', k1_funct_1('#skF_6', '#skF_8')) | ~v5_relat_1('#skF_7', '#skF_3') | ~m1_subset_1('#skF_8', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_2852, c_62])).
% 5.78/2.07  tff(c_2864, plain, (k1_funct_1(k8_funct_2('#skF_4', '#skF_5', '#skF_3', '#skF_6', '#skF_7'), '#skF_8')!=k1_funct_1('#skF_7', k1_funct_1('#skF_6', '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_273, c_2858])).
% 5.78/2.07  tff(c_2868, plain, (~m1_subset_1('#skF_8', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1285, c_2864])).
% 5.78/2.07  tff(c_2872, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_68, c_2868])).
% 5.78/2.07  tff(c_2874, plain, (r1_tarski(k1_relat_1('#skF_7'), k1_xboole_0)), inference(splitRight, [status(thm)], [c_918])).
% 5.78/2.07  tff(c_860, plain, (![B_188, A_187]: (~v1_xboole_0(B_188) | ~r1_tarski(k1_relat_1('#skF_7'), B_188) | ~r1_tarski(A_187, k2_relat_1('#skF_6')) | v1_xboole_0(A_187))), inference(resolution, [status(thm)], [c_842, c_2])).
% 5.78/2.07  tff(c_894, plain, (![B_188]: (~v1_xboole_0(B_188) | ~r1_tarski(k1_relat_1('#skF_7'), B_188))), inference(splitLeft, [status(thm)], [c_860])).
% 5.78/2.07  tff(c_2877, plain, (~v1_xboole_0(k1_xboole_0)), inference(resolution, [status(thm)], [c_2874, c_894])).
% 5.78/2.07  tff(c_2915, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_101, c_2877])).
% 5.78/2.07  tff(c_2917, plain, (![A_411]: (~r1_tarski(A_411, k2_relat_1('#skF_6')) | v1_xboole_0(A_411))), inference(splitRight, [status(thm)], [c_860])).
% 5.78/2.07  tff(c_2925, plain, (v1_xboole_0(k2_relat_1('#skF_6'))), inference(resolution, [status(thm)], [c_16, c_2917])).
% 5.78/2.07  tff(c_2934, plain, $false, inference(negUnitSimplification, [status(thm)], [c_618, c_2925])).
% 5.78/2.07  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.78/2.07  
% 5.78/2.07  Inference rules
% 5.78/2.07  ----------------------
% 5.78/2.07  #Ref     : 0
% 5.78/2.07  #Sup     : 600
% 5.78/2.07  #Fact    : 0
% 5.78/2.07  #Define  : 0
% 5.78/2.07  #Split   : 23
% 5.78/2.07  #Chain   : 0
% 5.78/2.07  #Close   : 0
% 5.78/2.07  
% 5.78/2.07  Ordering : KBO
% 5.78/2.07  
% 5.78/2.07  Simplification rules
% 5.78/2.07  ----------------------
% 5.78/2.07  #Subsume      : 223
% 5.78/2.07  #Demod        : 490
% 5.78/2.07  #Tautology    : 149
% 5.78/2.07  #SimpNegUnit  : 45
% 5.78/2.07  #BackRed      : 117
% 5.78/2.07  
% 5.78/2.07  #Partial instantiations: 0
% 5.78/2.07  #Strategies tried      : 1
% 5.78/2.07  
% 5.78/2.07  Timing (in seconds)
% 5.78/2.07  ----------------------
% 5.78/2.08  Preprocessing        : 0.36
% 5.78/2.08  Parsing              : 0.19
% 5.78/2.08  CNF conversion       : 0.03
% 5.78/2.08  Main loop            : 0.91
% 5.78/2.08  Inferencing          : 0.28
% 5.78/2.08  Reduction            : 0.30
% 5.78/2.08  Demodulation         : 0.20
% 5.78/2.08  BG Simplification    : 0.04
% 5.78/2.08  Subsumption          : 0.23
% 5.78/2.08  Abstraction          : 0.04
% 5.78/2.08  MUC search           : 0.00
% 5.78/2.08  Cooper               : 0.00
% 5.78/2.08  Total                : 1.32
% 5.78/2.08  Index Insertion      : 0.00
% 5.78/2.08  Index Deletion       : 0.00
% 5.78/2.08  Index Matching       : 0.00
% 5.78/2.08  BG Taut test         : 0.00
%------------------------------------------------------------------------------
