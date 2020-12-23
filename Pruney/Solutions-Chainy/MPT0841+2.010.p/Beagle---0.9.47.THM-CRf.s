%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:08:33 EST 2020

% Result     : Theorem 5.51s
% Output     : CNFRefutation 5.51s
% Verified   : 
% Statistics : Number of formulae       :  142 ( 340 expanded)
%              Number of leaves         :   38 ( 129 expanded)
%              Depth                    :   10
%              Number of atoms          :  274 ( 957 expanded)
%              Number of equality atoms :   10 (  25 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k7_relset_1 > k9_relat_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > #skF_1 > #skF_11 > #skF_7 > #skF_10 > #skF_6 > #skF_5 > #skF_2 > #skF_9 > #skF_4 > #skF_8 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_11',type,(
    '#skF_11': $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff(k7_relset_1,type,(
    k7_relset_1: ( $i * $i * $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_116,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B] :
            ( ~ v1_xboole_0(B)
           => ! [C] :
                ( ~ v1_xboole_0(C)
               => ! [D] :
                    ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(C,A)))
                   => ! [E] :
                        ( m1_subset_1(E,A)
                       => ( r2_hidden(E,k7_relset_1(C,A,D,B))
                        <=> ? [F] :
                              ( m1_subset_1(F,C)
                              & r2_hidden(k4_tarski(F,E),D)
                              & r2_hidden(F,B) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_relset_1)).

tff(f_85,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_68,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_47,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_66,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_89,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_60,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B,C] :
          ( C = k9_relat_1(A,B)
        <=> ! [D] :
              ( r2_hidden(D,C)
            <=> ? [E] :
                  ( r2_hidden(k4_tarski(E,D),A)
                  & r2_hidden(E,B) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d13_relat_1)).

tff(f_40,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_79,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k9_relat_1(C,B))
      <=> ? [D] :
            ( r2_hidden(D,k1_relat_1(C))
            & r2_hidden(k4_tarski(D,A),C)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t143_relat_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

tff(f_36,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

tff(c_52,plain,(
    m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1('#skF_8','#skF_6'))) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_2214,plain,(
    ! [C_556,A_557,B_558] :
      ( v4_relat_1(C_556,A_557)
      | ~ m1_subset_1(C_556,k1_zfmisc_1(k2_zfmisc_1(A_557,B_558))) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_2223,plain,(
    v4_relat_1('#skF_9','#skF_8') ),
    inference(resolution,[status(thm)],[c_52,c_2214])).

tff(c_34,plain,(
    ! [A_56,B_57] : v1_relat_1(k2_zfmisc_1(A_56,B_57)) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_2165,plain,(
    ! [B_542,A_543] :
      ( v1_relat_1(B_542)
      | ~ m1_subset_1(B_542,k1_zfmisc_1(A_543))
      | ~ v1_relat_1(A_543) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_2171,plain,
    ( v1_relat_1('#skF_9')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_8','#skF_6')) ),
    inference(resolution,[status(thm)],[c_52,c_2165])).

tff(c_2175,plain,(
    v1_relat_1('#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_2171])).

tff(c_32,plain,(
    ! [B_55,A_54] :
      ( r1_tarski(k1_relat_1(B_55),A_54)
      | ~ v4_relat_1(B_55,A_54)
      | ~ v1_relat_1(B_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_2903,plain,(
    ! [A_691,B_692,C_693,D_694] :
      ( k7_relset_1(A_691,B_692,C_693,D_694) = k9_relat_1(C_693,D_694)
      | ~ m1_subset_1(C_693,k1_zfmisc_1(k2_zfmisc_1(A_691,B_692))) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_2910,plain,(
    ! [D_694] : k7_relset_1('#skF_8','#skF_6','#skF_9',D_694) = k9_relat_1('#skF_9',D_694) ),
    inference(resolution,[status(thm)],[c_52,c_2903])).

tff(c_1305,plain,(
    ! [C_393,A_394,B_395] :
      ( v4_relat_1(C_393,A_394)
      | ~ m1_subset_1(C_393,k1_zfmisc_1(k2_zfmisc_1(A_394,B_395))) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_1314,plain,(
    v4_relat_1('#skF_9','#skF_8') ),
    inference(resolution,[status(thm)],[c_52,c_1305])).

tff(c_92,plain,(
    ! [B_168,A_169] :
      ( v1_relat_1(B_168)
      | ~ m1_subset_1(B_168,k1_zfmisc_1(A_169))
      | ~ v1_relat_1(A_169) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_98,plain,
    ( v1_relat_1('#skF_9')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_8','#skF_6')) ),
    inference(resolution,[status(thm)],[c_52,c_92])).

tff(c_102,plain,(
    v1_relat_1('#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_98])).

tff(c_1375,plain,(
    ! [A_413,B_414,C_415,D_416] :
      ( k7_relset_1(A_413,B_414,C_415,D_416) = k9_relat_1(C_415,D_416)
      | ~ m1_subset_1(C_415,k1_zfmisc_1(k2_zfmisc_1(A_413,B_414))) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_1382,plain,(
    ! [D_416] : k7_relset_1('#skF_8','#skF_6','#skF_9',D_416) = k9_relat_1('#skF_9',D_416) ),
    inference(resolution,[status(thm)],[c_52,c_1375])).

tff(c_127,plain,(
    ! [C_178,A_179,B_180] :
      ( v4_relat_1(C_178,A_179)
      | ~ m1_subset_1(C_178,k1_zfmisc_1(k2_zfmisc_1(A_179,B_180))) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_136,plain,(
    v4_relat_1('#skF_9','#skF_8') ),
    inference(resolution,[status(thm)],[c_52,c_127])).

tff(c_505,plain,(
    ! [A_264,B_265,C_266,D_267] :
      ( k7_relset_1(A_264,B_265,C_266,D_267) = k9_relat_1(C_266,D_267)
      | ~ m1_subset_1(C_266,k1_zfmisc_1(k2_zfmisc_1(A_264,B_265))) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_512,plain,(
    ! [D_267] : k7_relset_1('#skF_8','#skF_6','#skF_9',D_267) = k9_relat_1('#skF_9',D_267) ),
    inference(resolution,[status(thm)],[c_52,c_505])).

tff(c_74,plain,
    ( r2_hidden('#skF_10',k7_relset_1('#skF_8','#skF_6','#skF_9','#skF_7'))
    | m1_subset_1('#skF_11','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_126,plain,(
    m1_subset_1('#skF_11','#skF_8') ),
    inference(splitLeft,[status(thm)],[c_74])).

tff(c_66,plain,
    ( r2_hidden('#skF_10',k7_relset_1('#skF_8','#skF_6','#skF_9','#skF_7'))
    | r2_hidden('#skF_11','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_82,plain,(
    r2_hidden('#skF_11','#skF_7') ),
    inference(splitLeft,[status(thm)],[c_66])).

tff(c_70,plain,
    ( r2_hidden('#skF_10',k7_relset_1('#skF_8','#skF_6','#skF_9','#skF_7'))
    | r2_hidden(k4_tarski('#skF_11','#skF_10'),'#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_181,plain,(
    r2_hidden(k4_tarski('#skF_11','#skF_10'),'#skF_9') ),
    inference(splitLeft,[status(thm)],[c_70])).

tff(c_291,plain,(
    ! [A_220,B_221,C_222,D_223] :
      ( k7_relset_1(A_220,B_221,C_222,D_223) = k9_relat_1(C_222,D_223)
      | ~ m1_subset_1(C_222,k1_zfmisc_1(k2_zfmisc_1(A_220,B_221))) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_302,plain,(
    ! [D_223] : k7_relset_1('#skF_8','#skF_6','#skF_9',D_223) = k9_relat_1('#skF_9',D_223) ),
    inference(resolution,[status(thm)],[c_52,c_291])).

tff(c_60,plain,(
    ! [F_159] :
      ( ~ r2_hidden(F_159,'#skF_7')
      | ~ r2_hidden(k4_tarski(F_159,'#skF_10'),'#skF_9')
      | ~ m1_subset_1(F_159,'#skF_8')
      | ~ r2_hidden('#skF_10',k7_relset_1('#skF_8','#skF_6','#skF_9','#skF_7')) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_396,plain,(
    ! [F_159] :
      ( ~ r2_hidden(F_159,'#skF_7')
      | ~ r2_hidden(k4_tarski(F_159,'#skF_10'),'#skF_9')
      | ~ m1_subset_1(F_159,'#skF_8')
      | ~ r2_hidden('#skF_10',k9_relat_1('#skF_9','#skF_7')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_302,c_60])).

tff(c_397,plain,(
    ~ r2_hidden('#skF_10',k9_relat_1('#skF_9','#skF_7')) ),
    inference(splitLeft,[status(thm)],[c_396])).

tff(c_362,plain,(
    ! [D_240,A_241,B_242,E_243] :
      ( r2_hidden(D_240,k9_relat_1(A_241,B_242))
      | ~ r2_hidden(E_243,B_242)
      | ~ r2_hidden(k4_tarski(E_243,D_240),A_241)
      | ~ v1_relat_1(A_241) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_385,plain,(
    ! [D_244,A_245] :
      ( r2_hidden(D_244,k9_relat_1(A_245,'#skF_7'))
      | ~ r2_hidden(k4_tarski('#skF_11',D_244),A_245)
      | ~ v1_relat_1(A_245) ) ),
    inference(resolution,[status(thm)],[c_82,c_362])).

tff(c_391,plain,
    ( r2_hidden('#skF_10',k9_relat_1('#skF_9','#skF_7'))
    | ~ v1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_181,c_385])).

tff(c_395,plain,(
    r2_hidden('#skF_10',k9_relat_1('#skF_9','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_391])).

tff(c_398,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_397,c_395])).

tff(c_439,plain,(
    ! [F_251] :
      ( ~ r2_hidden(F_251,'#skF_7')
      | ~ r2_hidden(k4_tarski(F_251,'#skF_10'),'#skF_9')
      | ~ m1_subset_1(F_251,'#skF_8') ) ),
    inference(splitRight,[status(thm)],[c_396])).

tff(c_450,plain,
    ( ~ r2_hidden('#skF_11','#skF_7')
    | ~ m1_subset_1('#skF_11','#skF_8') ),
    inference(resolution,[status(thm)],[c_181,c_439])).

tff(c_460,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_126,c_82,c_450])).

tff(c_461,plain,(
    r2_hidden('#skF_10',k7_relset_1('#skF_8','#skF_6','#skF_9','#skF_7')) ),
    inference(splitRight,[status(thm)],[c_70])).

tff(c_516,plain,(
    r2_hidden('#skF_10',k9_relat_1('#skF_9','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_512,c_461])).

tff(c_8,plain,(
    ! [A_7,B_8] :
      ( m1_subset_1(A_7,k1_zfmisc_1(B_8))
      | ~ r1_tarski(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_544,plain,(
    ! [A_277,B_278,C_279] :
      ( r2_hidden('#skF_5'(A_277,B_278,C_279),k1_relat_1(C_279))
      | ~ r2_hidden(A_277,k9_relat_1(C_279,B_278))
      | ~ v1_relat_1(C_279) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_2,plain,(
    ! [C_4,A_1,B_2] :
      ( r2_hidden(C_4,A_1)
      | ~ r2_hidden(C_4,B_2)
      | ~ m1_subset_1(B_2,k1_zfmisc_1(A_1)) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_1094,plain,(
    ! [A_370,B_371,C_372,A_373] :
      ( r2_hidden('#skF_5'(A_370,B_371,C_372),A_373)
      | ~ m1_subset_1(k1_relat_1(C_372),k1_zfmisc_1(A_373))
      | ~ r2_hidden(A_370,k9_relat_1(C_372,B_371))
      | ~ v1_relat_1(C_372) ) ),
    inference(resolution,[status(thm)],[c_544,c_2])).

tff(c_1118,plain,(
    ! [A_377,B_378,C_379,B_380] :
      ( r2_hidden('#skF_5'(A_377,B_378,C_379),B_380)
      | ~ r2_hidden(A_377,k9_relat_1(C_379,B_378))
      | ~ v1_relat_1(C_379)
      | ~ r1_tarski(k1_relat_1(C_379),B_380) ) ),
    inference(resolution,[status(thm)],[c_8,c_1094])).

tff(c_4,plain,(
    ! [A_5,B_6] :
      ( m1_subset_1(A_5,B_6)
      | ~ r2_hidden(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_1182,plain,(
    ! [A_383,B_384,C_385,B_386] :
      ( m1_subset_1('#skF_5'(A_383,B_384,C_385),B_386)
      | ~ r2_hidden(A_383,k9_relat_1(C_385,B_384))
      | ~ v1_relat_1(C_385)
      | ~ r1_tarski(k1_relat_1(C_385),B_386) ) ),
    inference(resolution,[status(thm)],[c_1118,c_4])).

tff(c_1219,plain,(
    ! [B_386] :
      ( m1_subset_1('#skF_5'('#skF_10','#skF_7','#skF_9'),B_386)
      | ~ v1_relat_1('#skF_9')
      | ~ r1_tarski(k1_relat_1('#skF_9'),B_386) ) ),
    inference(resolution,[status(thm)],[c_516,c_1182])).

tff(c_1244,plain,(
    ! [B_387] :
      ( m1_subset_1('#skF_5'('#skF_10','#skF_7','#skF_9'),B_387)
      | ~ r1_tarski(k1_relat_1('#skF_9'),B_387) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_1219])).

tff(c_1248,plain,(
    ! [A_54] :
      ( m1_subset_1('#skF_5'('#skF_10','#skF_7','#skF_9'),A_54)
      | ~ v4_relat_1('#skF_9',A_54)
      | ~ v1_relat_1('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_32,c_1244])).

tff(c_1252,plain,(
    ! [A_388] :
      ( m1_subset_1('#skF_5'('#skF_10','#skF_7','#skF_9'),A_388)
      | ~ v4_relat_1('#skF_9',A_388) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_1248])).

tff(c_38,plain,(
    ! [A_58,B_59,C_60] :
      ( r2_hidden('#skF_5'(A_58,B_59,C_60),B_59)
      | ~ r2_hidden(A_58,k9_relat_1(C_60,B_59))
      | ~ v1_relat_1(C_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_579,plain,(
    ! [A_293,B_294,C_295] :
      ( r2_hidden(k4_tarski('#skF_5'(A_293,B_294,C_295),A_293),C_295)
      | ~ r2_hidden(A_293,k9_relat_1(C_295,B_294))
      | ~ v1_relat_1(C_295) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_462,plain,(
    ~ r2_hidden(k4_tarski('#skF_11','#skF_10'),'#skF_9') ),
    inference(splitRight,[status(thm)],[c_70])).

tff(c_68,plain,(
    ! [F_159] :
      ( ~ r2_hidden(F_159,'#skF_7')
      | ~ r2_hidden(k4_tarski(F_159,'#skF_10'),'#skF_9')
      | ~ m1_subset_1(F_159,'#skF_8')
      | r2_hidden(k4_tarski('#skF_11','#skF_10'),'#skF_9') ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_575,plain,(
    ! [F_159] :
      ( ~ r2_hidden(F_159,'#skF_7')
      | ~ r2_hidden(k4_tarski(F_159,'#skF_10'),'#skF_9')
      | ~ m1_subset_1(F_159,'#skF_8') ) ),
    inference(negUnitSimplification,[status(thm)],[c_462,c_68])).

tff(c_583,plain,(
    ! [B_294] :
      ( ~ r2_hidden('#skF_5'('#skF_10',B_294,'#skF_9'),'#skF_7')
      | ~ m1_subset_1('#skF_5'('#skF_10',B_294,'#skF_9'),'#skF_8')
      | ~ r2_hidden('#skF_10',k9_relat_1('#skF_9',B_294))
      | ~ v1_relat_1('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_579,c_575])).

tff(c_735,plain,(
    ! [B_322] :
      ( ~ r2_hidden('#skF_5'('#skF_10',B_322,'#skF_9'),'#skF_7')
      | ~ m1_subset_1('#skF_5'('#skF_10',B_322,'#skF_9'),'#skF_8')
      | ~ r2_hidden('#skF_10',k9_relat_1('#skF_9',B_322)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_583])).

tff(c_743,plain,
    ( ~ m1_subset_1('#skF_5'('#skF_10','#skF_7','#skF_9'),'#skF_8')
    | ~ r2_hidden('#skF_10',k9_relat_1('#skF_9','#skF_7'))
    | ~ v1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_38,c_735])).

tff(c_749,plain,(
    ~ m1_subset_1('#skF_5'('#skF_10','#skF_7','#skF_9'),'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_516,c_743])).

tff(c_1255,plain,(
    ~ v4_relat_1('#skF_9','#skF_8') ),
    inference(resolution,[status(thm)],[c_1252,c_749])).

tff(c_1282,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_136,c_1255])).

tff(c_1283,plain,(
    r2_hidden('#skF_10',k7_relset_1('#skF_8','#skF_6','#skF_9','#skF_7')) ),
    inference(splitRight,[status(thm)],[c_74])).

tff(c_1384,plain,(
    r2_hidden('#skF_10',k9_relat_1('#skF_9','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1382,c_1283])).

tff(c_1413,plain,(
    ! [A_425,B_426,C_427] :
      ( r2_hidden('#skF_5'(A_425,B_426,C_427),k1_relat_1(C_427))
      | ~ r2_hidden(A_425,k9_relat_1(C_427,B_426))
      | ~ v1_relat_1(C_427) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_1983,plain,(
    ! [A_524,B_525,C_526,A_527] :
      ( r2_hidden('#skF_5'(A_524,B_525,C_526),A_527)
      | ~ m1_subset_1(k1_relat_1(C_526),k1_zfmisc_1(A_527))
      | ~ r2_hidden(A_524,k9_relat_1(C_526,B_525))
      | ~ v1_relat_1(C_526) ) ),
    inference(resolution,[status(thm)],[c_1413,c_2])).

tff(c_1988,plain,(
    ! [A_528,B_529,C_530,B_531] :
      ( r2_hidden('#skF_5'(A_528,B_529,C_530),B_531)
      | ~ r2_hidden(A_528,k9_relat_1(C_530,B_529))
      | ~ v1_relat_1(C_530)
      | ~ r1_tarski(k1_relat_1(C_530),B_531) ) ),
    inference(resolution,[status(thm)],[c_8,c_1983])).

tff(c_2056,plain,(
    ! [A_534,B_535,C_536,B_537] :
      ( m1_subset_1('#skF_5'(A_534,B_535,C_536),B_537)
      | ~ r2_hidden(A_534,k9_relat_1(C_536,B_535))
      | ~ v1_relat_1(C_536)
      | ~ r1_tarski(k1_relat_1(C_536),B_537) ) ),
    inference(resolution,[status(thm)],[c_1988,c_4])).

tff(c_2090,plain,(
    ! [B_537] :
      ( m1_subset_1('#skF_5'('#skF_10','#skF_7','#skF_9'),B_537)
      | ~ v1_relat_1('#skF_9')
      | ~ r1_tarski(k1_relat_1('#skF_9'),B_537) ) ),
    inference(resolution,[status(thm)],[c_1384,c_2056])).

tff(c_2114,plain,(
    ! [B_538] :
      ( m1_subset_1('#skF_5'('#skF_10','#skF_7','#skF_9'),B_538)
      | ~ r1_tarski(k1_relat_1('#skF_9'),B_538) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_2090])).

tff(c_2118,plain,(
    ! [A_54] :
      ( m1_subset_1('#skF_5'('#skF_10','#skF_7','#skF_9'),A_54)
      | ~ v4_relat_1('#skF_9',A_54)
      | ~ v1_relat_1('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_32,c_2114])).

tff(c_2122,plain,(
    ! [A_539] :
      ( m1_subset_1('#skF_5'('#skF_10','#skF_7','#skF_9'),A_539)
      | ~ v4_relat_1('#skF_9',A_539) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_2118])).

tff(c_1447,plain,(
    ! [A_443,B_444,C_445] :
      ( r2_hidden(k4_tarski('#skF_5'(A_443,B_444,C_445),A_443),C_445)
      | ~ r2_hidden(A_443,k9_relat_1(C_445,B_444))
      | ~ v1_relat_1(C_445) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_1284,plain,(
    ~ m1_subset_1('#skF_11','#skF_8') ),
    inference(splitRight,[status(thm)],[c_74])).

tff(c_72,plain,(
    ! [F_159] :
      ( ~ r2_hidden(F_159,'#skF_7')
      | ~ r2_hidden(k4_tarski(F_159,'#skF_10'),'#skF_9')
      | ~ m1_subset_1(F_159,'#skF_8')
      | m1_subset_1('#skF_11','#skF_8') ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_1362,plain,(
    ! [F_159] :
      ( ~ r2_hidden(F_159,'#skF_7')
      | ~ r2_hidden(k4_tarski(F_159,'#skF_10'),'#skF_9')
      | ~ m1_subset_1(F_159,'#skF_8') ) ),
    inference(negUnitSimplification,[status(thm)],[c_1284,c_72])).

tff(c_1454,plain,(
    ! [B_444] :
      ( ~ r2_hidden('#skF_5'('#skF_10',B_444,'#skF_9'),'#skF_7')
      | ~ m1_subset_1('#skF_5'('#skF_10',B_444,'#skF_9'),'#skF_8')
      | ~ r2_hidden('#skF_10',k9_relat_1('#skF_9',B_444))
      | ~ v1_relat_1('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_1447,c_1362])).

tff(c_1603,plain,(
    ! [B_472] :
      ( ~ r2_hidden('#skF_5'('#skF_10',B_472,'#skF_9'),'#skF_7')
      | ~ m1_subset_1('#skF_5'('#skF_10',B_472,'#skF_9'),'#skF_8')
      | ~ r2_hidden('#skF_10',k9_relat_1('#skF_9',B_472)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_1454])).

tff(c_1611,plain,
    ( ~ m1_subset_1('#skF_5'('#skF_10','#skF_7','#skF_9'),'#skF_8')
    | ~ r2_hidden('#skF_10',k9_relat_1('#skF_9','#skF_7'))
    | ~ v1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_38,c_1603])).

tff(c_1617,plain,(
    ~ m1_subset_1('#skF_5'('#skF_10','#skF_7','#skF_9'),'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_1384,c_1611])).

tff(c_2125,plain,(
    ~ v4_relat_1('#skF_9','#skF_8') ),
    inference(resolution,[status(thm)],[c_2122,c_1617])).

tff(c_2152,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1314,c_2125])).

tff(c_2153,plain,(
    r2_hidden('#skF_10',k7_relset_1('#skF_8','#skF_6','#skF_9','#skF_7')) ),
    inference(splitRight,[status(thm)],[c_66])).

tff(c_2914,plain,(
    r2_hidden('#skF_10',k9_relat_1('#skF_9','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2910,c_2153])).

tff(c_2943,plain,(
    ! [A_705,B_706,C_707] :
      ( r2_hidden('#skF_5'(A_705,B_706,C_707),k1_relat_1(C_707))
      | ~ r2_hidden(A_705,k9_relat_1(C_707,B_706))
      | ~ v1_relat_1(C_707) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_3426,plain,(
    ! [A_795,B_796,C_797,A_798] :
      ( r2_hidden('#skF_5'(A_795,B_796,C_797),A_798)
      | ~ m1_subset_1(k1_relat_1(C_797),k1_zfmisc_1(A_798))
      | ~ r2_hidden(A_795,k9_relat_1(C_797,B_796))
      | ~ v1_relat_1(C_797) ) ),
    inference(resolution,[status(thm)],[c_2943,c_2])).

tff(c_3439,plain,(
    ! [A_800,B_801,C_802,B_803] :
      ( r2_hidden('#skF_5'(A_800,B_801,C_802),B_803)
      | ~ r2_hidden(A_800,k9_relat_1(C_802,B_801))
      | ~ v1_relat_1(C_802)
      | ~ r1_tarski(k1_relat_1(C_802),B_803) ) ),
    inference(resolution,[status(thm)],[c_8,c_3426])).

tff(c_3485,plain,(
    ! [A_808,B_809,C_810,B_811] :
      ( m1_subset_1('#skF_5'(A_808,B_809,C_810),B_811)
      | ~ r2_hidden(A_808,k9_relat_1(C_810,B_809))
      | ~ v1_relat_1(C_810)
      | ~ r1_tarski(k1_relat_1(C_810),B_811) ) ),
    inference(resolution,[status(thm)],[c_3439,c_4])).

tff(c_3516,plain,(
    ! [B_811] :
      ( m1_subset_1('#skF_5'('#skF_10','#skF_7','#skF_9'),B_811)
      | ~ v1_relat_1('#skF_9')
      | ~ r1_tarski(k1_relat_1('#skF_9'),B_811) ) ),
    inference(resolution,[status(thm)],[c_2914,c_3485])).

tff(c_3534,plain,(
    ! [B_812] :
      ( m1_subset_1('#skF_5'('#skF_10','#skF_7','#skF_9'),B_812)
      | ~ r1_tarski(k1_relat_1('#skF_9'),B_812) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2175,c_3516])).

tff(c_3538,plain,(
    ! [A_54] :
      ( m1_subset_1('#skF_5'('#skF_10','#skF_7','#skF_9'),A_54)
      | ~ v4_relat_1('#skF_9',A_54)
      | ~ v1_relat_1('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_32,c_3534])).

tff(c_3542,plain,(
    ! [A_813] :
      ( m1_subset_1('#skF_5'('#skF_10','#skF_7','#skF_9'),A_813)
      | ~ v4_relat_1('#skF_9',A_813) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2175,c_3538])).

tff(c_2971,plain,(
    ! [A_718,B_719,C_720] :
      ( r2_hidden(k4_tarski('#skF_5'(A_718,B_719,C_720),A_718),C_720)
      | ~ r2_hidden(A_718,k9_relat_1(C_720,B_719))
      | ~ v1_relat_1(C_720) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_2154,plain,(
    ~ r2_hidden('#skF_11','#skF_7') ),
    inference(splitRight,[status(thm)],[c_66])).

tff(c_64,plain,(
    ! [F_159] :
      ( ~ r2_hidden(F_159,'#skF_7')
      | ~ r2_hidden(k4_tarski(F_159,'#skF_10'),'#skF_9')
      | ~ m1_subset_1(F_159,'#skF_8')
      | r2_hidden('#skF_11','#skF_7') ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_2932,plain,(
    ! [F_159] :
      ( ~ r2_hidden(F_159,'#skF_7')
      | ~ r2_hidden(k4_tarski(F_159,'#skF_10'),'#skF_9')
      | ~ m1_subset_1(F_159,'#skF_8') ) ),
    inference(negUnitSimplification,[status(thm)],[c_2154,c_64])).

tff(c_2978,plain,(
    ! [B_719] :
      ( ~ r2_hidden('#skF_5'('#skF_10',B_719,'#skF_9'),'#skF_7')
      | ~ m1_subset_1('#skF_5'('#skF_10',B_719,'#skF_9'),'#skF_8')
      | ~ r2_hidden('#skF_10',k9_relat_1('#skF_9',B_719))
      | ~ v1_relat_1('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_2971,c_2932])).

tff(c_3100,plain,(
    ! [B_742] :
      ( ~ r2_hidden('#skF_5'('#skF_10',B_742,'#skF_9'),'#skF_7')
      | ~ m1_subset_1('#skF_5'('#skF_10',B_742,'#skF_9'),'#skF_8')
      | ~ r2_hidden('#skF_10',k9_relat_1('#skF_9',B_742)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2175,c_2978])).

tff(c_3108,plain,
    ( ~ m1_subset_1('#skF_5'('#skF_10','#skF_7','#skF_9'),'#skF_8')
    | ~ r2_hidden('#skF_10',k9_relat_1('#skF_9','#skF_7'))
    | ~ v1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_38,c_3100])).

tff(c_3114,plain,(
    ~ m1_subset_1('#skF_5'('#skF_10','#skF_7','#skF_9'),'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2175,c_2914,c_3108])).

tff(c_3545,plain,(
    ~ v4_relat_1('#skF_9','#skF_8') ),
    inference(resolution,[status(thm)],[c_3542,c_3114])).

tff(c_3568,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2223,c_3545])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:33:36 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.51/2.07  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.51/2.08  
% 5.51/2.08  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.51/2.09  %$ v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k7_relset_1 > k9_relat_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > #skF_1 > #skF_11 > #skF_7 > #skF_10 > #skF_6 > #skF_5 > #skF_2 > #skF_9 > #skF_4 > #skF_8 > #skF_3
% 5.51/2.09  
% 5.51/2.09  %Foreground sorts:
% 5.51/2.09  
% 5.51/2.09  
% 5.51/2.09  %Background operators:
% 5.51/2.09  
% 5.51/2.09  
% 5.51/2.09  %Foreground operators:
% 5.51/2.09  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 5.51/2.09  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.51/2.09  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.51/2.09  tff('#skF_11', type, '#skF_11': $i).
% 5.51/2.09  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 5.51/2.09  tff('#skF_7', type, '#skF_7': $i).
% 5.51/2.09  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.51/2.09  tff('#skF_10', type, '#skF_10': $i).
% 5.51/2.09  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 5.51/2.09  tff('#skF_6', type, '#skF_6': $i).
% 5.51/2.09  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 5.51/2.09  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 5.51/2.09  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 5.51/2.09  tff('#skF_9', type, '#skF_9': $i).
% 5.51/2.09  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 5.51/2.09  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.51/2.09  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i) > $i).
% 5.51/2.09  tff('#skF_8', type, '#skF_8': $i).
% 5.51/2.09  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.51/2.09  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.51/2.09  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 5.51/2.09  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 5.51/2.09  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.51/2.09  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 5.51/2.09  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 5.51/2.09  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 5.51/2.09  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.51/2.09  
% 5.51/2.11  tff(f_116, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: (~v1_xboole_0(C) => (![D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(C, A))) => (![E]: (m1_subset_1(E, A) => (r2_hidden(E, k7_relset_1(C, A, D, B)) <=> (?[F]: ((m1_subset_1(F, C) & r2_hidden(k4_tarski(F, E), D)) & r2_hidden(F, B)))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_relset_1)).
% 5.51/2.11  tff(f_85, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 5.51/2.11  tff(f_68, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 5.51/2.11  tff(f_47, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 5.51/2.11  tff(f_66, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d18_relat_1)).
% 5.51/2.11  tff(f_89, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 5.51/2.11  tff(f_60, axiom, (![A]: (v1_relat_1(A) => (![B, C]: ((C = k9_relat_1(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (?[E]: (r2_hidden(k4_tarski(E, D), A) & r2_hidden(E, B))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d13_relat_1)).
% 5.51/2.11  tff(f_40, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 5.51/2.11  tff(f_79, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k9_relat_1(C, B)) <=> (?[D]: ((r2_hidden(D, k1_relat_1(C)) & r2_hidden(k4_tarski(D, A), C)) & r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t143_relat_1)).
% 5.51/2.11  tff(f_32, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_subset_1)).
% 5.51/2.11  tff(f_36, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_subset)).
% 5.51/2.11  tff(c_52, plain, (m1_subset_1('#skF_9', k1_zfmisc_1(k2_zfmisc_1('#skF_8', '#skF_6')))), inference(cnfTransformation, [status(thm)], [f_116])).
% 5.51/2.11  tff(c_2214, plain, (![C_556, A_557, B_558]: (v4_relat_1(C_556, A_557) | ~m1_subset_1(C_556, k1_zfmisc_1(k2_zfmisc_1(A_557, B_558))))), inference(cnfTransformation, [status(thm)], [f_85])).
% 5.51/2.11  tff(c_2223, plain, (v4_relat_1('#skF_9', '#skF_8')), inference(resolution, [status(thm)], [c_52, c_2214])).
% 5.51/2.11  tff(c_34, plain, (![A_56, B_57]: (v1_relat_1(k2_zfmisc_1(A_56, B_57)))), inference(cnfTransformation, [status(thm)], [f_68])).
% 5.51/2.11  tff(c_2165, plain, (![B_542, A_543]: (v1_relat_1(B_542) | ~m1_subset_1(B_542, k1_zfmisc_1(A_543)) | ~v1_relat_1(A_543))), inference(cnfTransformation, [status(thm)], [f_47])).
% 5.51/2.11  tff(c_2171, plain, (v1_relat_1('#skF_9') | ~v1_relat_1(k2_zfmisc_1('#skF_8', '#skF_6'))), inference(resolution, [status(thm)], [c_52, c_2165])).
% 5.51/2.11  tff(c_2175, plain, (v1_relat_1('#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_2171])).
% 5.51/2.11  tff(c_32, plain, (![B_55, A_54]: (r1_tarski(k1_relat_1(B_55), A_54) | ~v4_relat_1(B_55, A_54) | ~v1_relat_1(B_55))), inference(cnfTransformation, [status(thm)], [f_66])).
% 5.51/2.11  tff(c_2903, plain, (![A_691, B_692, C_693, D_694]: (k7_relset_1(A_691, B_692, C_693, D_694)=k9_relat_1(C_693, D_694) | ~m1_subset_1(C_693, k1_zfmisc_1(k2_zfmisc_1(A_691, B_692))))), inference(cnfTransformation, [status(thm)], [f_89])).
% 5.51/2.11  tff(c_2910, plain, (![D_694]: (k7_relset_1('#skF_8', '#skF_6', '#skF_9', D_694)=k9_relat_1('#skF_9', D_694))), inference(resolution, [status(thm)], [c_52, c_2903])).
% 5.51/2.11  tff(c_1305, plain, (![C_393, A_394, B_395]: (v4_relat_1(C_393, A_394) | ~m1_subset_1(C_393, k1_zfmisc_1(k2_zfmisc_1(A_394, B_395))))), inference(cnfTransformation, [status(thm)], [f_85])).
% 5.51/2.11  tff(c_1314, plain, (v4_relat_1('#skF_9', '#skF_8')), inference(resolution, [status(thm)], [c_52, c_1305])).
% 5.51/2.11  tff(c_92, plain, (![B_168, A_169]: (v1_relat_1(B_168) | ~m1_subset_1(B_168, k1_zfmisc_1(A_169)) | ~v1_relat_1(A_169))), inference(cnfTransformation, [status(thm)], [f_47])).
% 5.51/2.11  tff(c_98, plain, (v1_relat_1('#skF_9') | ~v1_relat_1(k2_zfmisc_1('#skF_8', '#skF_6'))), inference(resolution, [status(thm)], [c_52, c_92])).
% 5.51/2.11  tff(c_102, plain, (v1_relat_1('#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_98])).
% 5.51/2.11  tff(c_1375, plain, (![A_413, B_414, C_415, D_416]: (k7_relset_1(A_413, B_414, C_415, D_416)=k9_relat_1(C_415, D_416) | ~m1_subset_1(C_415, k1_zfmisc_1(k2_zfmisc_1(A_413, B_414))))), inference(cnfTransformation, [status(thm)], [f_89])).
% 5.51/2.11  tff(c_1382, plain, (![D_416]: (k7_relset_1('#skF_8', '#skF_6', '#skF_9', D_416)=k9_relat_1('#skF_9', D_416))), inference(resolution, [status(thm)], [c_52, c_1375])).
% 5.51/2.11  tff(c_127, plain, (![C_178, A_179, B_180]: (v4_relat_1(C_178, A_179) | ~m1_subset_1(C_178, k1_zfmisc_1(k2_zfmisc_1(A_179, B_180))))), inference(cnfTransformation, [status(thm)], [f_85])).
% 5.51/2.11  tff(c_136, plain, (v4_relat_1('#skF_9', '#skF_8')), inference(resolution, [status(thm)], [c_52, c_127])).
% 5.51/2.11  tff(c_505, plain, (![A_264, B_265, C_266, D_267]: (k7_relset_1(A_264, B_265, C_266, D_267)=k9_relat_1(C_266, D_267) | ~m1_subset_1(C_266, k1_zfmisc_1(k2_zfmisc_1(A_264, B_265))))), inference(cnfTransformation, [status(thm)], [f_89])).
% 5.51/2.11  tff(c_512, plain, (![D_267]: (k7_relset_1('#skF_8', '#skF_6', '#skF_9', D_267)=k9_relat_1('#skF_9', D_267))), inference(resolution, [status(thm)], [c_52, c_505])).
% 5.51/2.11  tff(c_74, plain, (r2_hidden('#skF_10', k7_relset_1('#skF_8', '#skF_6', '#skF_9', '#skF_7')) | m1_subset_1('#skF_11', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_116])).
% 5.51/2.11  tff(c_126, plain, (m1_subset_1('#skF_11', '#skF_8')), inference(splitLeft, [status(thm)], [c_74])).
% 5.51/2.11  tff(c_66, plain, (r2_hidden('#skF_10', k7_relset_1('#skF_8', '#skF_6', '#skF_9', '#skF_7')) | r2_hidden('#skF_11', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_116])).
% 5.51/2.11  tff(c_82, plain, (r2_hidden('#skF_11', '#skF_7')), inference(splitLeft, [status(thm)], [c_66])).
% 5.51/2.11  tff(c_70, plain, (r2_hidden('#skF_10', k7_relset_1('#skF_8', '#skF_6', '#skF_9', '#skF_7')) | r2_hidden(k4_tarski('#skF_11', '#skF_10'), '#skF_9')), inference(cnfTransformation, [status(thm)], [f_116])).
% 5.51/2.11  tff(c_181, plain, (r2_hidden(k4_tarski('#skF_11', '#skF_10'), '#skF_9')), inference(splitLeft, [status(thm)], [c_70])).
% 5.51/2.11  tff(c_291, plain, (![A_220, B_221, C_222, D_223]: (k7_relset_1(A_220, B_221, C_222, D_223)=k9_relat_1(C_222, D_223) | ~m1_subset_1(C_222, k1_zfmisc_1(k2_zfmisc_1(A_220, B_221))))), inference(cnfTransformation, [status(thm)], [f_89])).
% 5.51/2.11  tff(c_302, plain, (![D_223]: (k7_relset_1('#skF_8', '#skF_6', '#skF_9', D_223)=k9_relat_1('#skF_9', D_223))), inference(resolution, [status(thm)], [c_52, c_291])).
% 5.51/2.11  tff(c_60, plain, (![F_159]: (~r2_hidden(F_159, '#skF_7') | ~r2_hidden(k4_tarski(F_159, '#skF_10'), '#skF_9') | ~m1_subset_1(F_159, '#skF_8') | ~r2_hidden('#skF_10', k7_relset_1('#skF_8', '#skF_6', '#skF_9', '#skF_7')))), inference(cnfTransformation, [status(thm)], [f_116])).
% 5.51/2.11  tff(c_396, plain, (![F_159]: (~r2_hidden(F_159, '#skF_7') | ~r2_hidden(k4_tarski(F_159, '#skF_10'), '#skF_9') | ~m1_subset_1(F_159, '#skF_8') | ~r2_hidden('#skF_10', k9_relat_1('#skF_9', '#skF_7')))), inference(demodulation, [status(thm), theory('equality')], [c_302, c_60])).
% 5.51/2.11  tff(c_397, plain, (~r2_hidden('#skF_10', k9_relat_1('#skF_9', '#skF_7'))), inference(splitLeft, [status(thm)], [c_396])).
% 5.51/2.11  tff(c_362, plain, (![D_240, A_241, B_242, E_243]: (r2_hidden(D_240, k9_relat_1(A_241, B_242)) | ~r2_hidden(E_243, B_242) | ~r2_hidden(k4_tarski(E_243, D_240), A_241) | ~v1_relat_1(A_241))), inference(cnfTransformation, [status(thm)], [f_60])).
% 5.51/2.11  tff(c_385, plain, (![D_244, A_245]: (r2_hidden(D_244, k9_relat_1(A_245, '#skF_7')) | ~r2_hidden(k4_tarski('#skF_11', D_244), A_245) | ~v1_relat_1(A_245))), inference(resolution, [status(thm)], [c_82, c_362])).
% 5.51/2.11  tff(c_391, plain, (r2_hidden('#skF_10', k9_relat_1('#skF_9', '#skF_7')) | ~v1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_181, c_385])).
% 5.51/2.11  tff(c_395, plain, (r2_hidden('#skF_10', k9_relat_1('#skF_9', '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_102, c_391])).
% 5.51/2.11  tff(c_398, plain, $false, inference(negUnitSimplification, [status(thm)], [c_397, c_395])).
% 5.51/2.11  tff(c_439, plain, (![F_251]: (~r2_hidden(F_251, '#skF_7') | ~r2_hidden(k4_tarski(F_251, '#skF_10'), '#skF_9') | ~m1_subset_1(F_251, '#skF_8'))), inference(splitRight, [status(thm)], [c_396])).
% 5.51/2.11  tff(c_450, plain, (~r2_hidden('#skF_11', '#skF_7') | ~m1_subset_1('#skF_11', '#skF_8')), inference(resolution, [status(thm)], [c_181, c_439])).
% 5.51/2.11  tff(c_460, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_126, c_82, c_450])).
% 5.51/2.11  tff(c_461, plain, (r2_hidden('#skF_10', k7_relset_1('#skF_8', '#skF_6', '#skF_9', '#skF_7'))), inference(splitRight, [status(thm)], [c_70])).
% 5.51/2.11  tff(c_516, plain, (r2_hidden('#skF_10', k9_relat_1('#skF_9', '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_512, c_461])).
% 5.51/2.11  tff(c_8, plain, (![A_7, B_8]: (m1_subset_1(A_7, k1_zfmisc_1(B_8)) | ~r1_tarski(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_40])).
% 5.51/2.11  tff(c_544, plain, (![A_277, B_278, C_279]: (r2_hidden('#skF_5'(A_277, B_278, C_279), k1_relat_1(C_279)) | ~r2_hidden(A_277, k9_relat_1(C_279, B_278)) | ~v1_relat_1(C_279))), inference(cnfTransformation, [status(thm)], [f_79])).
% 5.51/2.11  tff(c_2, plain, (![C_4, A_1, B_2]: (r2_hidden(C_4, A_1) | ~r2_hidden(C_4, B_2) | ~m1_subset_1(B_2, k1_zfmisc_1(A_1)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.51/2.11  tff(c_1094, plain, (![A_370, B_371, C_372, A_373]: (r2_hidden('#skF_5'(A_370, B_371, C_372), A_373) | ~m1_subset_1(k1_relat_1(C_372), k1_zfmisc_1(A_373)) | ~r2_hidden(A_370, k9_relat_1(C_372, B_371)) | ~v1_relat_1(C_372))), inference(resolution, [status(thm)], [c_544, c_2])).
% 5.51/2.11  tff(c_1118, plain, (![A_377, B_378, C_379, B_380]: (r2_hidden('#skF_5'(A_377, B_378, C_379), B_380) | ~r2_hidden(A_377, k9_relat_1(C_379, B_378)) | ~v1_relat_1(C_379) | ~r1_tarski(k1_relat_1(C_379), B_380))), inference(resolution, [status(thm)], [c_8, c_1094])).
% 5.51/2.11  tff(c_4, plain, (![A_5, B_6]: (m1_subset_1(A_5, B_6) | ~r2_hidden(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_36])).
% 5.51/2.11  tff(c_1182, plain, (![A_383, B_384, C_385, B_386]: (m1_subset_1('#skF_5'(A_383, B_384, C_385), B_386) | ~r2_hidden(A_383, k9_relat_1(C_385, B_384)) | ~v1_relat_1(C_385) | ~r1_tarski(k1_relat_1(C_385), B_386))), inference(resolution, [status(thm)], [c_1118, c_4])).
% 5.51/2.11  tff(c_1219, plain, (![B_386]: (m1_subset_1('#skF_5'('#skF_10', '#skF_7', '#skF_9'), B_386) | ~v1_relat_1('#skF_9') | ~r1_tarski(k1_relat_1('#skF_9'), B_386))), inference(resolution, [status(thm)], [c_516, c_1182])).
% 5.51/2.11  tff(c_1244, plain, (![B_387]: (m1_subset_1('#skF_5'('#skF_10', '#skF_7', '#skF_9'), B_387) | ~r1_tarski(k1_relat_1('#skF_9'), B_387))), inference(demodulation, [status(thm), theory('equality')], [c_102, c_1219])).
% 5.51/2.11  tff(c_1248, plain, (![A_54]: (m1_subset_1('#skF_5'('#skF_10', '#skF_7', '#skF_9'), A_54) | ~v4_relat_1('#skF_9', A_54) | ~v1_relat_1('#skF_9'))), inference(resolution, [status(thm)], [c_32, c_1244])).
% 5.51/2.11  tff(c_1252, plain, (![A_388]: (m1_subset_1('#skF_5'('#skF_10', '#skF_7', '#skF_9'), A_388) | ~v4_relat_1('#skF_9', A_388))), inference(demodulation, [status(thm), theory('equality')], [c_102, c_1248])).
% 5.51/2.11  tff(c_38, plain, (![A_58, B_59, C_60]: (r2_hidden('#skF_5'(A_58, B_59, C_60), B_59) | ~r2_hidden(A_58, k9_relat_1(C_60, B_59)) | ~v1_relat_1(C_60))), inference(cnfTransformation, [status(thm)], [f_79])).
% 5.51/2.11  tff(c_579, plain, (![A_293, B_294, C_295]: (r2_hidden(k4_tarski('#skF_5'(A_293, B_294, C_295), A_293), C_295) | ~r2_hidden(A_293, k9_relat_1(C_295, B_294)) | ~v1_relat_1(C_295))), inference(cnfTransformation, [status(thm)], [f_79])).
% 5.51/2.11  tff(c_462, plain, (~r2_hidden(k4_tarski('#skF_11', '#skF_10'), '#skF_9')), inference(splitRight, [status(thm)], [c_70])).
% 5.51/2.11  tff(c_68, plain, (![F_159]: (~r2_hidden(F_159, '#skF_7') | ~r2_hidden(k4_tarski(F_159, '#skF_10'), '#skF_9') | ~m1_subset_1(F_159, '#skF_8') | r2_hidden(k4_tarski('#skF_11', '#skF_10'), '#skF_9'))), inference(cnfTransformation, [status(thm)], [f_116])).
% 5.51/2.11  tff(c_575, plain, (![F_159]: (~r2_hidden(F_159, '#skF_7') | ~r2_hidden(k4_tarski(F_159, '#skF_10'), '#skF_9') | ~m1_subset_1(F_159, '#skF_8'))), inference(negUnitSimplification, [status(thm)], [c_462, c_68])).
% 5.51/2.11  tff(c_583, plain, (![B_294]: (~r2_hidden('#skF_5'('#skF_10', B_294, '#skF_9'), '#skF_7') | ~m1_subset_1('#skF_5'('#skF_10', B_294, '#skF_9'), '#skF_8') | ~r2_hidden('#skF_10', k9_relat_1('#skF_9', B_294)) | ~v1_relat_1('#skF_9'))), inference(resolution, [status(thm)], [c_579, c_575])).
% 5.51/2.11  tff(c_735, plain, (![B_322]: (~r2_hidden('#skF_5'('#skF_10', B_322, '#skF_9'), '#skF_7') | ~m1_subset_1('#skF_5'('#skF_10', B_322, '#skF_9'), '#skF_8') | ~r2_hidden('#skF_10', k9_relat_1('#skF_9', B_322)))), inference(demodulation, [status(thm), theory('equality')], [c_102, c_583])).
% 5.51/2.11  tff(c_743, plain, (~m1_subset_1('#skF_5'('#skF_10', '#skF_7', '#skF_9'), '#skF_8') | ~r2_hidden('#skF_10', k9_relat_1('#skF_9', '#skF_7')) | ~v1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_38, c_735])).
% 5.51/2.11  tff(c_749, plain, (~m1_subset_1('#skF_5'('#skF_10', '#skF_7', '#skF_9'), '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_102, c_516, c_743])).
% 5.51/2.11  tff(c_1255, plain, (~v4_relat_1('#skF_9', '#skF_8')), inference(resolution, [status(thm)], [c_1252, c_749])).
% 5.51/2.11  tff(c_1282, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_136, c_1255])).
% 5.51/2.11  tff(c_1283, plain, (r2_hidden('#skF_10', k7_relset_1('#skF_8', '#skF_6', '#skF_9', '#skF_7'))), inference(splitRight, [status(thm)], [c_74])).
% 5.51/2.11  tff(c_1384, plain, (r2_hidden('#skF_10', k9_relat_1('#skF_9', '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_1382, c_1283])).
% 5.51/2.11  tff(c_1413, plain, (![A_425, B_426, C_427]: (r2_hidden('#skF_5'(A_425, B_426, C_427), k1_relat_1(C_427)) | ~r2_hidden(A_425, k9_relat_1(C_427, B_426)) | ~v1_relat_1(C_427))), inference(cnfTransformation, [status(thm)], [f_79])).
% 5.51/2.11  tff(c_1983, plain, (![A_524, B_525, C_526, A_527]: (r2_hidden('#skF_5'(A_524, B_525, C_526), A_527) | ~m1_subset_1(k1_relat_1(C_526), k1_zfmisc_1(A_527)) | ~r2_hidden(A_524, k9_relat_1(C_526, B_525)) | ~v1_relat_1(C_526))), inference(resolution, [status(thm)], [c_1413, c_2])).
% 5.51/2.11  tff(c_1988, plain, (![A_528, B_529, C_530, B_531]: (r2_hidden('#skF_5'(A_528, B_529, C_530), B_531) | ~r2_hidden(A_528, k9_relat_1(C_530, B_529)) | ~v1_relat_1(C_530) | ~r1_tarski(k1_relat_1(C_530), B_531))), inference(resolution, [status(thm)], [c_8, c_1983])).
% 5.51/2.11  tff(c_2056, plain, (![A_534, B_535, C_536, B_537]: (m1_subset_1('#skF_5'(A_534, B_535, C_536), B_537) | ~r2_hidden(A_534, k9_relat_1(C_536, B_535)) | ~v1_relat_1(C_536) | ~r1_tarski(k1_relat_1(C_536), B_537))), inference(resolution, [status(thm)], [c_1988, c_4])).
% 5.51/2.11  tff(c_2090, plain, (![B_537]: (m1_subset_1('#skF_5'('#skF_10', '#skF_7', '#skF_9'), B_537) | ~v1_relat_1('#skF_9') | ~r1_tarski(k1_relat_1('#skF_9'), B_537))), inference(resolution, [status(thm)], [c_1384, c_2056])).
% 5.51/2.11  tff(c_2114, plain, (![B_538]: (m1_subset_1('#skF_5'('#skF_10', '#skF_7', '#skF_9'), B_538) | ~r1_tarski(k1_relat_1('#skF_9'), B_538))), inference(demodulation, [status(thm), theory('equality')], [c_102, c_2090])).
% 5.51/2.11  tff(c_2118, plain, (![A_54]: (m1_subset_1('#skF_5'('#skF_10', '#skF_7', '#skF_9'), A_54) | ~v4_relat_1('#skF_9', A_54) | ~v1_relat_1('#skF_9'))), inference(resolution, [status(thm)], [c_32, c_2114])).
% 5.51/2.11  tff(c_2122, plain, (![A_539]: (m1_subset_1('#skF_5'('#skF_10', '#skF_7', '#skF_9'), A_539) | ~v4_relat_1('#skF_9', A_539))), inference(demodulation, [status(thm), theory('equality')], [c_102, c_2118])).
% 5.51/2.11  tff(c_1447, plain, (![A_443, B_444, C_445]: (r2_hidden(k4_tarski('#skF_5'(A_443, B_444, C_445), A_443), C_445) | ~r2_hidden(A_443, k9_relat_1(C_445, B_444)) | ~v1_relat_1(C_445))), inference(cnfTransformation, [status(thm)], [f_79])).
% 5.51/2.11  tff(c_1284, plain, (~m1_subset_1('#skF_11', '#skF_8')), inference(splitRight, [status(thm)], [c_74])).
% 5.51/2.11  tff(c_72, plain, (![F_159]: (~r2_hidden(F_159, '#skF_7') | ~r2_hidden(k4_tarski(F_159, '#skF_10'), '#skF_9') | ~m1_subset_1(F_159, '#skF_8') | m1_subset_1('#skF_11', '#skF_8'))), inference(cnfTransformation, [status(thm)], [f_116])).
% 5.51/2.11  tff(c_1362, plain, (![F_159]: (~r2_hidden(F_159, '#skF_7') | ~r2_hidden(k4_tarski(F_159, '#skF_10'), '#skF_9') | ~m1_subset_1(F_159, '#skF_8'))), inference(negUnitSimplification, [status(thm)], [c_1284, c_72])).
% 5.51/2.11  tff(c_1454, plain, (![B_444]: (~r2_hidden('#skF_5'('#skF_10', B_444, '#skF_9'), '#skF_7') | ~m1_subset_1('#skF_5'('#skF_10', B_444, '#skF_9'), '#skF_8') | ~r2_hidden('#skF_10', k9_relat_1('#skF_9', B_444)) | ~v1_relat_1('#skF_9'))), inference(resolution, [status(thm)], [c_1447, c_1362])).
% 5.51/2.11  tff(c_1603, plain, (![B_472]: (~r2_hidden('#skF_5'('#skF_10', B_472, '#skF_9'), '#skF_7') | ~m1_subset_1('#skF_5'('#skF_10', B_472, '#skF_9'), '#skF_8') | ~r2_hidden('#skF_10', k9_relat_1('#skF_9', B_472)))), inference(demodulation, [status(thm), theory('equality')], [c_102, c_1454])).
% 5.51/2.11  tff(c_1611, plain, (~m1_subset_1('#skF_5'('#skF_10', '#skF_7', '#skF_9'), '#skF_8') | ~r2_hidden('#skF_10', k9_relat_1('#skF_9', '#skF_7')) | ~v1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_38, c_1603])).
% 5.51/2.11  tff(c_1617, plain, (~m1_subset_1('#skF_5'('#skF_10', '#skF_7', '#skF_9'), '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_102, c_1384, c_1611])).
% 5.51/2.11  tff(c_2125, plain, (~v4_relat_1('#skF_9', '#skF_8')), inference(resolution, [status(thm)], [c_2122, c_1617])).
% 5.51/2.11  tff(c_2152, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1314, c_2125])).
% 5.51/2.11  tff(c_2153, plain, (r2_hidden('#skF_10', k7_relset_1('#skF_8', '#skF_6', '#skF_9', '#skF_7'))), inference(splitRight, [status(thm)], [c_66])).
% 5.51/2.11  tff(c_2914, plain, (r2_hidden('#skF_10', k9_relat_1('#skF_9', '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_2910, c_2153])).
% 5.51/2.11  tff(c_2943, plain, (![A_705, B_706, C_707]: (r2_hidden('#skF_5'(A_705, B_706, C_707), k1_relat_1(C_707)) | ~r2_hidden(A_705, k9_relat_1(C_707, B_706)) | ~v1_relat_1(C_707))), inference(cnfTransformation, [status(thm)], [f_79])).
% 5.51/2.11  tff(c_3426, plain, (![A_795, B_796, C_797, A_798]: (r2_hidden('#skF_5'(A_795, B_796, C_797), A_798) | ~m1_subset_1(k1_relat_1(C_797), k1_zfmisc_1(A_798)) | ~r2_hidden(A_795, k9_relat_1(C_797, B_796)) | ~v1_relat_1(C_797))), inference(resolution, [status(thm)], [c_2943, c_2])).
% 5.51/2.11  tff(c_3439, plain, (![A_800, B_801, C_802, B_803]: (r2_hidden('#skF_5'(A_800, B_801, C_802), B_803) | ~r2_hidden(A_800, k9_relat_1(C_802, B_801)) | ~v1_relat_1(C_802) | ~r1_tarski(k1_relat_1(C_802), B_803))), inference(resolution, [status(thm)], [c_8, c_3426])).
% 5.51/2.11  tff(c_3485, plain, (![A_808, B_809, C_810, B_811]: (m1_subset_1('#skF_5'(A_808, B_809, C_810), B_811) | ~r2_hidden(A_808, k9_relat_1(C_810, B_809)) | ~v1_relat_1(C_810) | ~r1_tarski(k1_relat_1(C_810), B_811))), inference(resolution, [status(thm)], [c_3439, c_4])).
% 5.51/2.11  tff(c_3516, plain, (![B_811]: (m1_subset_1('#skF_5'('#skF_10', '#skF_7', '#skF_9'), B_811) | ~v1_relat_1('#skF_9') | ~r1_tarski(k1_relat_1('#skF_9'), B_811))), inference(resolution, [status(thm)], [c_2914, c_3485])).
% 5.51/2.11  tff(c_3534, plain, (![B_812]: (m1_subset_1('#skF_5'('#skF_10', '#skF_7', '#skF_9'), B_812) | ~r1_tarski(k1_relat_1('#skF_9'), B_812))), inference(demodulation, [status(thm), theory('equality')], [c_2175, c_3516])).
% 5.51/2.11  tff(c_3538, plain, (![A_54]: (m1_subset_1('#skF_5'('#skF_10', '#skF_7', '#skF_9'), A_54) | ~v4_relat_1('#skF_9', A_54) | ~v1_relat_1('#skF_9'))), inference(resolution, [status(thm)], [c_32, c_3534])).
% 5.51/2.11  tff(c_3542, plain, (![A_813]: (m1_subset_1('#skF_5'('#skF_10', '#skF_7', '#skF_9'), A_813) | ~v4_relat_1('#skF_9', A_813))), inference(demodulation, [status(thm), theory('equality')], [c_2175, c_3538])).
% 5.51/2.11  tff(c_2971, plain, (![A_718, B_719, C_720]: (r2_hidden(k4_tarski('#skF_5'(A_718, B_719, C_720), A_718), C_720) | ~r2_hidden(A_718, k9_relat_1(C_720, B_719)) | ~v1_relat_1(C_720))), inference(cnfTransformation, [status(thm)], [f_79])).
% 5.51/2.11  tff(c_2154, plain, (~r2_hidden('#skF_11', '#skF_7')), inference(splitRight, [status(thm)], [c_66])).
% 5.51/2.11  tff(c_64, plain, (![F_159]: (~r2_hidden(F_159, '#skF_7') | ~r2_hidden(k4_tarski(F_159, '#skF_10'), '#skF_9') | ~m1_subset_1(F_159, '#skF_8') | r2_hidden('#skF_11', '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_116])).
% 5.51/2.11  tff(c_2932, plain, (![F_159]: (~r2_hidden(F_159, '#skF_7') | ~r2_hidden(k4_tarski(F_159, '#skF_10'), '#skF_9') | ~m1_subset_1(F_159, '#skF_8'))), inference(negUnitSimplification, [status(thm)], [c_2154, c_64])).
% 5.51/2.11  tff(c_2978, plain, (![B_719]: (~r2_hidden('#skF_5'('#skF_10', B_719, '#skF_9'), '#skF_7') | ~m1_subset_1('#skF_5'('#skF_10', B_719, '#skF_9'), '#skF_8') | ~r2_hidden('#skF_10', k9_relat_1('#skF_9', B_719)) | ~v1_relat_1('#skF_9'))), inference(resolution, [status(thm)], [c_2971, c_2932])).
% 5.51/2.11  tff(c_3100, plain, (![B_742]: (~r2_hidden('#skF_5'('#skF_10', B_742, '#skF_9'), '#skF_7') | ~m1_subset_1('#skF_5'('#skF_10', B_742, '#skF_9'), '#skF_8') | ~r2_hidden('#skF_10', k9_relat_1('#skF_9', B_742)))), inference(demodulation, [status(thm), theory('equality')], [c_2175, c_2978])).
% 5.51/2.11  tff(c_3108, plain, (~m1_subset_1('#skF_5'('#skF_10', '#skF_7', '#skF_9'), '#skF_8') | ~r2_hidden('#skF_10', k9_relat_1('#skF_9', '#skF_7')) | ~v1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_38, c_3100])).
% 5.51/2.11  tff(c_3114, plain, (~m1_subset_1('#skF_5'('#skF_10', '#skF_7', '#skF_9'), '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_2175, c_2914, c_3108])).
% 5.51/2.11  tff(c_3545, plain, (~v4_relat_1('#skF_9', '#skF_8')), inference(resolution, [status(thm)], [c_3542, c_3114])).
% 5.51/2.11  tff(c_3568, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2223, c_3545])).
% 5.51/2.11  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.51/2.11  
% 5.51/2.11  Inference rules
% 5.51/2.11  ----------------------
% 5.51/2.11  #Ref     : 0
% 5.51/2.11  #Sup     : 751
% 5.51/2.11  #Fact    : 0
% 5.51/2.11  #Define  : 0
% 5.51/2.11  #Split   : 29
% 5.51/2.11  #Chain   : 0
% 5.51/2.11  #Close   : 0
% 5.51/2.11  
% 5.51/2.11  Ordering : KBO
% 5.51/2.11  
% 5.51/2.11  Simplification rules
% 5.51/2.11  ----------------------
% 5.51/2.11  #Subsume      : 37
% 5.51/2.11  #Demod        : 125
% 5.51/2.11  #Tautology    : 41
% 5.51/2.11  #SimpNegUnit  : 5
% 5.51/2.11  #BackRed      : 14
% 5.51/2.11  
% 5.51/2.11  #Partial instantiations: 0
% 5.51/2.11  #Strategies tried      : 1
% 5.51/2.11  
% 5.51/2.11  Timing (in seconds)
% 5.51/2.11  ----------------------
% 5.51/2.11  Preprocessing        : 0.36
% 5.51/2.11  Parsing              : 0.19
% 5.51/2.11  CNF conversion       : 0.04
% 5.51/2.11  Main loop            : 0.90
% 5.51/2.11  Inferencing          : 0.34
% 5.51/2.11  Reduction            : 0.24
% 5.51/2.11  Demodulation         : 0.16
% 5.51/2.11  BG Simplification    : 0.04
% 5.51/2.11  Subsumption          : 0.19
% 5.51/2.11  Abstraction          : 0.05
% 5.51/2.11  MUC search           : 0.00
% 5.51/2.11  Cooper               : 0.00
% 5.51/2.11  Total                : 1.31
% 5.51/2.11  Index Insertion      : 0.00
% 5.51/2.11  Index Deletion       : 0.00
% 5.51/2.11  Index Matching       : 0.00
% 5.51/2.11  BG Taut test         : 0.00
%------------------------------------------------------------------------------
