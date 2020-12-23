%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:14:42 EST 2020

% Result     : Theorem 8.37s
% Output     : CNFRefutation 8.54s
% Verified   : 
% Statistics : Number of formulae       :  138 ( 445 expanded)
%              Number of leaves         :   51 ( 171 expanded)
%              Depth                    :   13
%              Number of atoms          :  213 ( 877 expanded)
%              Number of equality atoms :   49 ( 203 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_7 > #skF_3 > #skF_6 > #skF_5 > #skF_9 > #skF_8 > #skF_2 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k7_relset_1,type,(
    k7_relset_1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

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

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_173,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,k1_tarski(A),B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A),B))) )
       => ( B != k1_xboole_0
         => r1_tarski(k7_relset_1(k1_tarski(A),B,D,C),k1_tarski(k1_funct_1(D,A))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_funct_2)).

tff(f_145,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_95,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k9_relat_1(B,A),k2_relat_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t144_relat_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_40,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_58,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_91,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_60,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_113,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_funct_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc3_funct_1)).

tff(f_151,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_83,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_89,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_128,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_funct_1)).

tff(f_141,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

tff(f_136,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( k1_relat_1(B) = k1_tarski(A)
       => k2_relat_1(B) = k1_tarski(k1_funct_1(B,A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_funct_1)).

tff(f_52,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k1_tarski(B))
    <=> ( A = k1_xboole_0
        | A = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).

tff(f_161,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(C,A)))
     => ( r1_tarski(k2_relat_1(D),B)
       => m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(C,B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_relset_1)).

tff(f_64,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_155,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(c_96,plain,(
    m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_6'),'#skF_7'))) ),
    inference(cnfTransformation,[status(thm)],[f_173])).

tff(c_180,plain,(
    ! [C_119,A_120,B_121] :
      ( v1_relat_1(C_119)
      | ~ m1_subset_1(C_119,k1_zfmisc_1(k2_zfmisc_1(A_120,B_121))) ) ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_196,plain,(
    v1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_96,c_180])).

tff(c_54,plain,(
    ! [B_35,A_34] :
      ( r1_tarski(k9_relat_1(B_35,A_34),k2_relat_1(B_35))
      | ~ v1_relat_1(B_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_12,plain,(
    ! [B_7] : r1_tarski(B_7,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_14,plain,(
    ! [A_8] : r1_tarski(k1_xboole_0,A_8) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_32,plain,(
    ! [B_18] : k2_zfmisc_1(k1_xboole_0,B_18) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_114,plain,(
    ! [A_105,B_106] : v1_relat_1(k2_zfmisc_1(A_105,B_106)) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_116,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_114])).

tff(c_100,plain,(
    v1_funct_1('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_173])).

tff(c_34,plain,(
    ! [A_19] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_19)) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_755,plain,(
    ! [B_197,A_198] :
      ( v1_funct_1(B_197)
      | ~ m1_subset_1(B_197,k1_zfmisc_1(A_198))
      | ~ v1_funct_1(A_198)
      | ~ v1_relat_1(A_198) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_769,plain,(
    ! [A_19] :
      ( v1_funct_1(k1_xboole_0)
      | ~ v1_funct_1(A_19)
      | ~ v1_relat_1(A_19) ) ),
    inference(resolution,[status(thm)],[c_34,c_755])).

tff(c_771,plain,(
    ! [A_199] :
      ( ~ v1_funct_1(A_199)
      | ~ v1_relat_1(A_199) ) ),
    inference(splitLeft,[status(thm)],[c_769])).

tff(c_780,plain,(
    ~ v1_funct_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_196,c_771])).

tff(c_792,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_780])).

tff(c_793,plain,(
    v1_funct_1(k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_769])).

tff(c_649,plain,(
    ! [C_179,A_180,B_181] :
      ( v4_relat_1(C_179,A_180)
      | ~ m1_subset_1(C_179,k1_zfmisc_1(k2_zfmisc_1(A_180,B_181))) ) ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_674,plain,(
    ! [A_185] : v4_relat_1(k1_xboole_0,A_185) ),
    inference(resolution,[status(thm)],[c_34,c_649])).

tff(c_529,plain,(
    ! [B_166,A_167] :
      ( r1_tarski(k1_relat_1(B_166),A_167)
      | ~ v4_relat_1(B_166,A_167)
      | ~ v1_relat_1(B_166) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_296,plain,(
    ! [B_137,A_138] :
      ( B_137 = A_138
      | ~ r1_tarski(B_137,A_138)
      | ~ r1_tarski(A_138,B_137) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_311,plain,(
    ! [A_8] :
      ( k1_xboole_0 = A_8
      | ~ r1_tarski(A_8,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_14,c_296])).

tff(c_557,plain,(
    ! [B_166] :
      ( k1_relat_1(B_166) = k1_xboole_0
      | ~ v4_relat_1(B_166,k1_xboole_0)
      | ~ v1_relat_1(B_166) ) ),
    inference(resolution,[status(thm)],[c_529,c_311])).

tff(c_678,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_674,c_557])).

tff(c_681,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_116,c_678])).

tff(c_380,plain,(
    ! [C_148,B_149,A_150] :
      ( v5_relat_1(C_148,B_149)
      | ~ m1_subset_1(C_148,k1_zfmisc_1(k2_zfmisc_1(A_150,B_149))) ) ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_402,plain,(
    ! [B_151] : v5_relat_1(k1_xboole_0,B_151) ),
    inference(resolution,[status(thm)],[c_34,c_380])).

tff(c_332,plain,(
    ! [B_142,A_143] :
      ( r1_tarski(k2_relat_1(B_142),A_143)
      | ~ v5_relat_1(B_142,A_143)
      | ~ v1_relat_1(B_142) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_355,plain,(
    ! [B_142] :
      ( k2_relat_1(B_142) = k1_xboole_0
      | ~ v5_relat_1(B_142,k1_xboole_0)
      | ~ v1_relat_1(B_142) ) ),
    inference(resolution,[status(thm)],[c_332,c_311])).

tff(c_406,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_402,c_355])).

tff(c_409,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_116,c_406])).

tff(c_953,plain,(
    ! [A_220,D_221] :
      ( r2_hidden(k1_funct_1(A_220,D_221),k2_relat_1(A_220))
      | ~ r2_hidden(D_221,k1_relat_1(A_220))
      | ~ v1_funct_1(A_220)
      | ~ v1_relat_1(A_220) ) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_963,plain,(
    ! [D_221] :
      ( r2_hidden(k1_funct_1(k1_xboole_0,D_221),k1_xboole_0)
      | ~ r2_hidden(D_221,k1_relat_1(k1_xboole_0))
      | ~ v1_funct_1(k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_409,c_953])).

tff(c_986,plain,(
    ! [D_226] :
      ( r2_hidden(k1_funct_1(k1_xboole_0,D_226),k1_xboole_0)
      | ~ r2_hidden(D_226,k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_116,c_793,c_681,c_963])).

tff(c_80,plain,(
    ! [B_86,A_85] :
      ( ~ r1_tarski(B_86,A_85)
      | ~ r2_hidden(A_85,B_86) ) ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_995,plain,(
    ! [D_226] :
      ( ~ r1_tarski(k1_xboole_0,k1_funct_1(k1_xboole_0,D_226))
      | ~ r2_hidden(D_226,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_986,c_80])).

tff(c_1005,plain,(
    ! [D_226] : ~ r2_hidden(D_226,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_995])).

tff(c_2040,plain,(
    ! [A_324,B_325] :
      ( r2_hidden('#skF_3'(A_324,B_325),k1_relat_1(A_324))
      | r2_hidden('#skF_4'(A_324,B_325),B_325)
      | k2_relat_1(A_324) = B_325
      | ~ v1_funct_1(A_324)
      | ~ v1_relat_1(A_324) ) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_2059,plain,(
    ! [B_325] :
      ( r2_hidden('#skF_3'(k1_xboole_0,B_325),k1_xboole_0)
      | r2_hidden('#skF_4'(k1_xboole_0,B_325),B_325)
      | k2_relat_1(k1_xboole_0) = B_325
      | ~ v1_funct_1(k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_681,c_2040])).

tff(c_2067,plain,(
    ! [B_325] :
      ( r2_hidden('#skF_3'(k1_xboole_0,B_325),k1_xboole_0)
      | r2_hidden('#skF_4'(k1_xboole_0,B_325),B_325)
      | k1_xboole_0 = B_325 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_116,c_793,c_409,c_2059])).

tff(c_2068,plain,(
    ! [B_325] :
      ( r2_hidden('#skF_4'(k1_xboole_0,B_325),B_325)
      | k1_xboole_0 = B_325 ) ),
    inference(negUnitSimplification,[status(thm)],[c_1005,c_2067])).

tff(c_1014,plain,(
    ! [B_228,A_229] :
      ( k1_tarski(k1_funct_1(B_228,A_229)) = k2_relat_1(B_228)
      | k1_tarski(A_229) != k1_relat_1(B_228)
      | ~ v1_funct_1(B_228)
      | ~ v1_relat_1(B_228) ) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_92,plain,(
    ~ r1_tarski(k7_relset_1(k1_tarski('#skF_6'),'#skF_7','#skF_9','#skF_8'),k1_tarski(k1_funct_1('#skF_9','#skF_6'))) ),
    inference(cnfTransformation,[status(thm)],[f_173])).

tff(c_1023,plain,
    ( ~ r1_tarski(k7_relset_1(k1_tarski('#skF_6'),'#skF_7','#skF_9','#skF_8'),k2_relat_1('#skF_9'))
    | k1_tarski('#skF_6') != k1_relat_1('#skF_9')
    | ~ v1_funct_1('#skF_9')
    | ~ v1_relat_1('#skF_9') ),
    inference(superposition,[status(thm),theory(equality)],[c_1014,c_92])).

tff(c_1029,plain,
    ( ~ r1_tarski(k7_relset_1(k1_tarski('#skF_6'),'#skF_7','#skF_9','#skF_8'),k2_relat_1('#skF_9'))
    | k1_tarski('#skF_6') != k1_relat_1('#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_196,c_100,c_1023])).

tff(c_1053,plain,(
    k1_tarski('#skF_6') != k1_relat_1('#skF_9') ),
    inference(splitLeft,[status(thm)],[c_1029])).

tff(c_667,plain,(
    v4_relat_1('#skF_9',k1_tarski('#skF_6')) ),
    inference(resolution,[status(thm)],[c_96,c_649])).

tff(c_22,plain,(
    ! [B_16,A_15] :
      ( k1_tarski(B_16) = A_15
      | k1_xboole_0 = A_15
      | ~ r1_tarski(A_15,k1_tarski(B_16)) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_8672,plain,(
    ! [B_687,B_688] :
      ( k1_tarski(B_687) = k1_relat_1(B_688)
      | k1_relat_1(B_688) = k1_xboole_0
      | ~ v4_relat_1(B_688,k1_tarski(B_687))
      | ~ v1_relat_1(B_688) ) ),
    inference(resolution,[status(thm)],[c_529,c_22])).

tff(c_8734,plain,
    ( k1_tarski('#skF_6') = k1_relat_1('#skF_9')
    | k1_relat_1('#skF_9') = k1_xboole_0
    | ~ v1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_667,c_8672])).

tff(c_8769,plain,
    ( k1_tarski('#skF_6') = k1_relat_1('#skF_9')
    | k1_relat_1('#skF_9') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_196,c_8734])).

tff(c_8770,plain,(
    k1_relat_1('#skF_9') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_1053,c_8769])).

tff(c_64,plain,(
    ! [A_43,C_79] :
      ( r2_hidden('#skF_5'(A_43,k2_relat_1(A_43),C_79),k1_relat_1(A_43))
      | ~ r2_hidden(C_79,k2_relat_1(A_43))
      | ~ v1_funct_1(A_43)
      | ~ v1_relat_1(A_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_8811,plain,(
    ! [C_79] :
      ( r2_hidden('#skF_5'('#skF_9',k2_relat_1('#skF_9'),C_79),k1_xboole_0)
      | ~ r2_hidden(C_79,k2_relat_1('#skF_9'))
      | ~ v1_funct_1('#skF_9')
      | ~ v1_relat_1('#skF_9') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8770,c_64])).

tff(c_8856,plain,(
    ! [C_79] :
      ( r2_hidden('#skF_5'('#skF_9',k2_relat_1('#skF_9'),C_79),k1_xboole_0)
      | ~ r2_hidden(C_79,k2_relat_1('#skF_9')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_196,c_100,c_8811])).

tff(c_8959,plain,(
    ! [C_690] : ~ r2_hidden(C_690,k2_relat_1('#skF_9')) ),
    inference(negUnitSimplification,[status(thm)],[c_1005,c_8856])).

tff(c_8988,plain,(
    k2_relat_1('#skF_9') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2068,c_8959])).

tff(c_30,plain,(
    ! [A_17] : k2_zfmisc_1(A_17,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_1178,plain,(
    ! [D_253,C_254,B_255,A_256] :
      ( m1_subset_1(D_253,k1_zfmisc_1(k2_zfmisc_1(C_254,B_255)))
      | ~ r1_tarski(k2_relat_1(D_253),B_255)
      | ~ m1_subset_1(D_253,k1_zfmisc_1(k2_zfmisc_1(C_254,A_256))) ) ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_1242,plain,(
    ! [B_261] :
      ( m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_6'),B_261)))
      | ~ r1_tarski(k2_relat_1('#skF_9'),B_261) ) ),
    inference(resolution,[status(thm)],[c_96,c_1178])).

tff(c_1270,plain,
    ( m1_subset_1('#skF_9',k1_zfmisc_1(k1_xboole_0))
    | ~ r1_tarski(k2_relat_1('#skF_9'),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_1242])).

tff(c_1304,plain,(
    ~ r1_tarski(k2_relat_1('#skF_9'),k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_1270])).

tff(c_9000,plain,(
    ~ r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8988,c_1304])).

tff(c_9014,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_9000])).

tff(c_9015,plain,(
    m1_subset_1('#skF_9',k1_zfmisc_1(k1_xboole_0)) ),
    inference(splitRight,[status(thm)],[c_1270])).

tff(c_36,plain,(
    ! [A_20,B_21] :
      ( r1_tarski(A_20,B_21)
      | ~ m1_subset_1(A_20,k1_zfmisc_1(B_21)) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_9046,plain,(
    r1_tarski('#skF_9',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_9015,c_36])).

tff(c_9140,plain,(
    k1_xboole_0 = '#skF_9' ),
    inference(resolution,[status(thm)],[c_9046,c_311])).

tff(c_9182,plain,(
    ! [A_8] : r1_tarski('#skF_9',A_8) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9140,c_14])).

tff(c_419,plain,(
    ! [A_34] :
      ( r1_tarski(k9_relat_1(k1_xboole_0,A_34),k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_409,c_54])).

tff(c_429,plain,(
    ! [A_152] : r1_tarski(k9_relat_1(k1_xboole_0,A_152),k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_116,c_419])).

tff(c_441,plain,(
    ! [A_152] : k9_relat_1(k1_xboole_0,A_152) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_429,c_311])).

tff(c_9168,plain,(
    ! [A_152] : k9_relat_1('#skF_9',A_152) = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9140,c_9140,c_441])).

tff(c_1087,plain,(
    ! [A_236,B_237,C_238,D_239] :
      ( k7_relset_1(A_236,B_237,C_238,D_239) = k9_relat_1(C_238,D_239)
      | ~ m1_subset_1(C_238,k1_zfmisc_1(k2_zfmisc_1(A_236,B_237))) ) ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_1100,plain,(
    ! [D_239] : k7_relset_1(k1_tarski('#skF_6'),'#skF_7','#skF_9',D_239) = k9_relat_1('#skF_9',D_239) ),
    inference(resolution,[status(thm)],[c_96,c_1087])).

tff(c_1112,plain,(
    ~ r1_tarski(k9_relat_1('#skF_9','#skF_8'),k1_tarski(k1_funct_1('#skF_9','#skF_6'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1100,c_92])).

tff(c_9613,plain,(
    ~ r1_tarski('#skF_9',k1_tarski(k1_funct_1('#skF_9','#skF_6'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9168,c_1112])).

tff(c_9617,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_9182,c_9613])).

tff(c_9619,plain,(
    k1_tarski('#skF_6') = k1_relat_1('#skF_9') ),
    inference(splitRight,[status(thm)],[c_1029])).

tff(c_9625,plain,(
    m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_9'),'#skF_7'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9619,c_96])).

tff(c_88,plain,(
    ! [A_93,B_94,C_95,D_96] :
      ( k7_relset_1(A_93,B_94,C_95,D_96) = k9_relat_1(C_95,D_96)
      | ~ m1_subset_1(C_95,k1_zfmisc_1(k2_zfmisc_1(A_93,B_94))) ) ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_9706,plain,(
    ! [D_96] : k7_relset_1(k1_relat_1('#skF_9'),'#skF_7','#skF_9',D_96) = k9_relat_1('#skF_9',D_96) ),
    inference(resolution,[status(thm)],[c_9625,c_88])).

tff(c_9618,plain,(
    ~ r1_tarski(k7_relset_1(k1_tarski('#skF_6'),'#skF_7','#skF_9','#skF_8'),k2_relat_1('#skF_9')) ),
    inference(splitRight,[status(thm)],[c_1029])).

tff(c_9740,plain,(
    ~ r1_tarski(k7_relset_1(k1_relat_1('#skF_9'),'#skF_7','#skF_9','#skF_8'),k2_relat_1('#skF_9')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9619,c_9618])).

tff(c_9765,plain,(
    ~ r1_tarski(k9_relat_1('#skF_9','#skF_8'),k2_relat_1('#skF_9')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9706,c_9740])).

tff(c_9783,plain,(
    ~ v1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_54,c_9765])).

tff(c_9787,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_196,c_9783])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:30:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.37/2.90  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.44/2.91  
% 8.44/2.91  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.44/2.91  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_7 > #skF_3 > #skF_6 > #skF_5 > #skF_9 > #skF_8 > #skF_2 > #skF_1 > #skF_4
% 8.44/2.91  
% 8.44/2.91  %Foreground sorts:
% 8.44/2.91  
% 8.44/2.91  
% 8.44/2.91  %Background operators:
% 8.44/2.91  
% 8.44/2.91  
% 8.44/2.91  %Foreground operators:
% 8.44/2.91  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 8.44/2.91  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.44/2.91  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 8.44/2.91  tff(k1_tarski, type, k1_tarski: $i > $i).
% 8.44/2.91  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 8.44/2.91  tff('#skF_7', type, '#skF_7': $i).
% 8.44/2.91  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 8.44/2.91  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 8.44/2.91  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 8.44/2.91  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 8.44/2.91  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 8.44/2.91  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 8.44/2.91  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 8.44/2.91  tff('#skF_6', type, '#skF_6': $i).
% 8.44/2.91  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 8.44/2.91  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 8.44/2.91  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 8.44/2.91  tff('#skF_9', type, '#skF_9': $i).
% 8.44/2.91  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 8.44/2.91  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 8.44/2.91  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 8.44/2.91  tff('#skF_8', type, '#skF_8': $i).
% 8.44/2.91  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.44/2.91  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 8.44/2.91  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 8.44/2.91  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.44/2.91  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 8.44/2.91  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 8.44/2.91  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 8.44/2.91  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 8.44/2.91  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 8.44/2.91  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 8.44/2.91  
% 8.54/2.93  tff(f_173, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, k1_tarski(A), B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A), B)))) => (~(B = k1_xboole_0) => r1_tarski(k7_relset_1(k1_tarski(A), B, D, C), k1_tarski(k1_funct_1(D, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_funct_2)).
% 8.54/2.93  tff(f_145, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 8.54/2.93  tff(f_95, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k9_relat_1(B, A), k2_relat_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t144_relat_1)).
% 8.54/2.93  tff(f_38, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 8.54/2.93  tff(f_40, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 8.54/2.93  tff(f_58, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 8.54/2.93  tff(f_91, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 8.54/2.93  tff(f_60, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 8.54/2.93  tff(f_113, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_funct_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc3_funct_1)).
% 8.54/2.93  tff(f_151, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 8.54/2.93  tff(f_83, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d18_relat_1)).
% 8.54/2.93  tff(f_89, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 8.54/2.93  tff(f_128, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((B = k2_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: (r2_hidden(D, k1_relat_1(A)) & (C = k1_funct_1(A, D)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_funct_1)).
% 8.54/2.93  tff(f_141, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 8.54/2.93  tff(f_136, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((k1_relat_1(B) = k1_tarski(A)) => (k2_relat_1(B) = k1_tarski(k1_funct_1(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t14_funct_1)).
% 8.54/2.93  tff(f_52, axiom, (![A, B]: (r1_tarski(A, k1_tarski(B)) <=> ((A = k1_xboole_0) | (A = k1_tarski(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_zfmisc_1)).
% 8.54/2.93  tff(f_161, axiom, (![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(C, A))) => (r1_tarski(k2_relat_1(D), B) => m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(C, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t14_relset_1)).
% 8.54/2.93  tff(f_64, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 8.54/2.93  tff(f_155, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 8.54/2.93  tff(c_96, plain, (m1_subset_1('#skF_9', k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_6'), '#skF_7')))), inference(cnfTransformation, [status(thm)], [f_173])).
% 8.54/2.93  tff(c_180, plain, (![C_119, A_120, B_121]: (v1_relat_1(C_119) | ~m1_subset_1(C_119, k1_zfmisc_1(k2_zfmisc_1(A_120, B_121))))), inference(cnfTransformation, [status(thm)], [f_145])).
% 8.54/2.93  tff(c_196, plain, (v1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_96, c_180])).
% 8.54/2.93  tff(c_54, plain, (![B_35, A_34]: (r1_tarski(k9_relat_1(B_35, A_34), k2_relat_1(B_35)) | ~v1_relat_1(B_35))), inference(cnfTransformation, [status(thm)], [f_95])).
% 8.54/2.93  tff(c_12, plain, (![B_7]: (r1_tarski(B_7, B_7))), inference(cnfTransformation, [status(thm)], [f_38])).
% 8.54/2.93  tff(c_14, plain, (![A_8]: (r1_tarski(k1_xboole_0, A_8))), inference(cnfTransformation, [status(thm)], [f_40])).
% 8.54/2.93  tff(c_32, plain, (![B_18]: (k2_zfmisc_1(k1_xboole_0, B_18)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_58])).
% 8.54/2.93  tff(c_114, plain, (![A_105, B_106]: (v1_relat_1(k2_zfmisc_1(A_105, B_106)))), inference(cnfTransformation, [status(thm)], [f_91])).
% 8.54/2.93  tff(c_116, plain, (v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_32, c_114])).
% 8.54/2.93  tff(c_100, plain, (v1_funct_1('#skF_9')), inference(cnfTransformation, [status(thm)], [f_173])).
% 8.54/2.93  tff(c_34, plain, (![A_19]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_19)))), inference(cnfTransformation, [status(thm)], [f_60])).
% 8.54/2.93  tff(c_755, plain, (![B_197, A_198]: (v1_funct_1(B_197) | ~m1_subset_1(B_197, k1_zfmisc_1(A_198)) | ~v1_funct_1(A_198) | ~v1_relat_1(A_198))), inference(cnfTransformation, [status(thm)], [f_113])).
% 8.54/2.93  tff(c_769, plain, (![A_19]: (v1_funct_1(k1_xboole_0) | ~v1_funct_1(A_19) | ~v1_relat_1(A_19))), inference(resolution, [status(thm)], [c_34, c_755])).
% 8.54/2.93  tff(c_771, plain, (![A_199]: (~v1_funct_1(A_199) | ~v1_relat_1(A_199))), inference(splitLeft, [status(thm)], [c_769])).
% 8.54/2.93  tff(c_780, plain, (~v1_funct_1('#skF_9')), inference(resolution, [status(thm)], [c_196, c_771])).
% 8.54/2.93  tff(c_792, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_100, c_780])).
% 8.54/2.93  tff(c_793, plain, (v1_funct_1(k1_xboole_0)), inference(splitRight, [status(thm)], [c_769])).
% 8.54/2.93  tff(c_649, plain, (![C_179, A_180, B_181]: (v4_relat_1(C_179, A_180) | ~m1_subset_1(C_179, k1_zfmisc_1(k2_zfmisc_1(A_180, B_181))))), inference(cnfTransformation, [status(thm)], [f_151])).
% 8.54/2.93  tff(c_674, plain, (![A_185]: (v4_relat_1(k1_xboole_0, A_185))), inference(resolution, [status(thm)], [c_34, c_649])).
% 8.54/2.93  tff(c_529, plain, (![B_166, A_167]: (r1_tarski(k1_relat_1(B_166), A_167) | ~v4_relat_1(B_166, A_167) | ~v1_relat_1(B_166))), inference(cnfTransformation, [status(thm)], [f_83])).
% 8.54/2.93  tff(c_296, plain, (![B_137, A_138]: (B_137=A_138 | ~r1_tarski(B_137, A_138) | ~r1_tarski(A_138, B_137))), inference(cnfTransformation, [status(thm)], [f_38])).
% 8.54/2.93  tff(c_311, plain, (![A_8]: (k1_xboole_0=A_8 | ~r1_tarski(A_8, k1_xboole_0))), inference(resolution, [status(thm)], [c_14, c_296])).
% 8.54/2.93  tff(c_557, plain, (![B_166]: (k1_relat_1(B_166)=k1_xboole_0 | ~v4_relat_1(B_166, k1_xboole_0) | ~v1_relat_1(B_166))), inference(resolution, [status(thm)], [c_529, c_311])).
% 8.54/2.93  tff(c_678, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_674, c_557])).
% 8.54/2.93  tff(c_681, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_116, c_678])).
% 8.54/2.93  tff(c_380, plain, (![C_148, B_149, A_150]: (v5_relat_1(C_148, B_149) | ~m1_subset_1(C_148, k1_zfmisc_1(k2_zfmisc_1(A_150, B_149))))), inference(cnfTransformation, [status(thm)], [f_151])).
% 8.54/2.93  tff(c_402, plain, (![B_151]: (v5_relat_1(k1_xboole_0, B_151))), inference(resolution, [status(thm)], [c_34, c_380])).
% 8.54/2.93  tff(c_332, plain, (![B_142, A_143]: (r1_tarski(k2_relat_1(B_142), A_143) | ~v5_relat_1(B_142, A_143) | ~v1_relat_1(B_142))), inference(cnfTransformation, [status(thm)], [f_89])).
% 8.54/2.93  tff(c_355, plain, (![B_142]: (k2_relat_1(B_142)=k1_xboole_0 | ~v5_relat_1(B_142, k1_xboole_0) | ~v1_relat_1(B_142))), inference(resolution, [status(thm)], [c_332, c_311])).
% 8.54/2.93  tff(c_406, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_402, c_355])).
% 8.54/2.93  tff(c_409, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_116, c_406])).
% 8.54/2.93  tff(c_953, plain, (![A_220, D_221]: (r2_hidden(k1_funct_1(A_220, D_221), k2_relat_1(A_220)) | ~r2_hidden(D_221, k1_relat_1(A_220)) | ~v1_funct_1(A_220) | ~v1_relat_1(A_220))), inference(cnfTransformation, [status(thm)], [f_128])).
% 8.54/2.93  tff(c_963, plain, (![D_221]: (r2_hidden(k1_funct_1(k1_xboole_0, D_221), k1_xboole_0) | ~r2_hidden(D_221, k1_relat_1(k1_xboole_0)) | ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_409, c_953])).
% 8.54/2.93  tff(c_986, plain, (![D_226]: (r2_hidden(k1_funct_1(k1_xboole_0, D_226), k1_xboole_0) | ~r2_hidden(D_226, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_116, c_793, c_681, c_963])).
% 8.54/2.93  tff(c_80, plain, (![B_86, A_85]: (~r1_tarski(B_86, A_85) | ~r2_hidden(A_85, B_86))), inference(cnfTransformation, [status(thm)], [f_141])).
% 8.54/2.93  tff(c_995, plain, (![D_226]: (~r1_tarski(k1_xboole_0, k1_funct_1(k1_xboole_0, D_226)) | ~r2_hidden(D_226, k1_xboole_0))), inference(resolution, [status(thm)], [c_986, c_80])).
% 8.54/2.93  tff(c_1005, plain, (![D_226]: (~r2_hidden(D_226, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_995])).
% 8.54/2.93  tff(c_2040, plain, (![A_324, B_325]: (r2_hidden('#skF_3'(A_324, B_325), k1_relat_1(A_324)) | r2_hidden('#skF_4'(A_324, B_325), B_325) | k2_relat_1(A_324)=B_325 | ~v1_funct_1(A_324) | ~v1_relat_1(A_324))), inference(cnfTransformation, [status(thm)], [f_128])).
% 8.54/2.93  tff(c_2059, plain, (![B_325]: (r2_hidden('#skF_3'(k1_xboole_0, B_325), k1_xboole_0) | r2_hidden('#skF_4'(k1_xboole_0, B_325), B_325) | k2_relat_1(k1_xboole_0)=B_325 | ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_681, c_2040])).
% 8.54/2.93  tff(c_2067, plain, (![B_325]: (r2_hidden('#skF_3'(k1_xboole_0, B_325), k1_xboole_0) | r2_hidden('#skF_4'(k1_xboole_0, B_325), B_325) | k1_xboole_0=B_325)), inference(demodulation, [status(thm), theory('equality')], [c_116, c_793, c_409, c_2059])).
% 8.54/2.93  tff(c_2068, plain, (![B_325]: (r2_hidden('#skF_4'(k1_xboole_0, B_325), B_325) | k1_xboole_0=B_325)), inference(negUnitSimplification, [status(thm)], [c_1005, c_2067])).
% 8.54/2.93  tff(c_1014, plain, (![B_228, A_229]: (k1_tarski(k1_funct_1(B_228, A_229))=k2_relat_1(B_228) | k1_tarski(A_229)!=k1_relat_1(B_228) | ~v1_funct_1(B_228) | ~v1_relat_1(B_228))), inference(cnfTransformation, [status(thm)], [f_136])).
% 8.54/2.93  tff(c_92, plain, (~r1_tarski(k7_relset_1(k1_tarski('#skF_6'), '#skF_7', '#skF_9', '#skF_8'), k1_tarski(k1_funct_1('#skF_9', '#skF_6')))), inference(cnfTransformation, [status(thm)], [f_173])).
% 8.54/2.93  tff(c_1023, plain, (~r1_tarski(k7_relset_1(k1_tarski('#skF_6'), '#skF_7', '#skF_9', '#skF_8'), k2_relat_1('#skF_9')) | k1_tarski('#skF_6')!=k1_relat_1('#skF_9') | ~v1_funct_1('#skF_9') | ~v1_relat_1('#skF_9')), inference(superposition, [status(thm), theory('equality')], [c_1014, c_92])).
% 8.54/2.93  tff(c_1029, plain, (~r1_tarski(k7_relset_1(k1_tarski('#skF_6'), '#skF_7', '#skF_9', '#skF_8'), k2_relat_1('#skF_9')) | k1_tarski('#skF_6')!=k1_relat_1('#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_196, c_100, c_1023])).
% 8.54/2.93  tff(c_1053, plain, (k1_tarski('#skF_6')!=k1_relat_1('#skF_9')), inference(splitLeft, [status(thm)], [c_1029])).
% 8.54/2.93  tff(c_667, plain, (v4_relat_1('#skF_9', k1_tarski('#skF_6'))), inference(resolution, [status(thm)], [c_96, c_649])).
% 8.54/2.93  tff(c_22, plain, (![B_16, A_15]: (k1_tarski(B_16)=A_15 | k1_xboole_0=A_15 | ~r1_tarski(A_15, k1_tarski(B_16)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 8.54/2.93  tff(c_8672, plain, (![B_687, B_688]: (k1_tarski(B_687)=k1_relat_1(B_688) | k1_relat_1(B_688)=k1_xboole_0 | ~v4_relat_1(B_688, k1_tarski(B_687)) | ~v1_relat_1(B_688))), inference(resolution, [status(thm)], [c_529, c_22])).
% 8.54/2.93  tff(c_8734, plain, (k1_tarski('#skF_6')=k1_relat_1('#skF_9') | k1_relat_1('#skF_9')=k1_xboole_0 | ~v1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_667, c_8672])).
% 8.54/2.93  tff(c_8769, plain, (k1_tarski('#skF_6')=k1_relat_1('#skF_9') | k1_relat_1('#skF_9')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_196, c_8734])).
% 8.54/2.93  tff(c_8770, plain, (k1_relat_1('#skF_9')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_1053, c_8769])).
% 8.54/2.93  tff(c_64, plain, (![A_43, C_79]: (r2_hidden('#skF_5'(A_43, k2_relat_1(A_43), C_79), k1_relat_1(A_43)) | ~r2_hidden(C_79, k2_relat_1(A_43)) | ~v1_funct_1(A_43) | ~v1_relat_1(A_43))), inference(cnfTransformation, [status(thm)], [f_128])).
% 8.54/2.93  tff(c_8811, plain, (![C_79]: (r2_hidden('#skF_5'('#skF_9', k2_relat_1('#skF_9'), C_79), k1_xboole_0) | ~r2_hidden(C_79, k2_relat_1('#skF_9')) | ~v1_funct_1('#skF_9') | ~v1_relat_1('#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_8770, c_64])).
% 8.54/2.93  tff(c_8856, plain, (![C_79]: (r2_hidden('#skF_5'('#skF_9', k2_relat_1('#skF_9'), C_79), k1_xboole_0) | ~r2_hidden(C_79, k2_relat_1('#skF_9')))), inference(demodulation, [status(thm), theory('equality')], [c_196, c_100, c_8811])).
% 8.54/2.93  tff(c_8959, plain, (![C_690]: (~r2_hidden(C_690, k2_relat_1('#skF_9')))), inference(negUnitSimplification, [status(thm)], [c_1005, c_8856])).
% 8.54/2.93  tff(c_8988, plain, (k2_relat_1('#skF_9')=k1_xboole_0), inference(resolution, [status(thm)], [c_2068, c_8959])).
% 8.54/2.93  tff(c_30, plain, (![A_17]: (k2_zfmisc_1(A_17, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_58])).
% 8.54/2.93  tff(c_1178, plain, (![D_253, C_254, B_255, A_256]: (m1_subset_1(D_253, k1_zfmisc_1(k2_zfmisc_1(C_254, B_255))) | ~r1_tarski(k2_relat_1(D_253), B_255) | ~m1_subset_1(D_253, k1_zfmisc_1(k2_zfmisc_1(C_254, A_256))))), inference(cnfTransformation, [status(thm)], [f_161])).
% 8.54/2.93  tff(c_1242, plain, (![B_261]: (m1_subset_1('#skF_9', k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_6'), B_261))) | ~r1_tarski(k2_relat_1('#skF_9'), B_261))), inference(resolution, [status(thm)], [c_96, c_1178])).
% 8.54/2.93  tff(c_1270, plain, (m1_subset_1('#skF_9', k1_zfmisc_1(k1_xboole_0)) | ~r1_tarski(k2_relat_1('#skF_9'), k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_30, c_1242])).
% 8.54/2.93  tff(c_1304, plain, (~r1_tarski(k2_relat_1('#skF_9'), k1_xboole_0)), inference(splitLeft, [status(thm)], [c_1270])).
% 8.54/2.93  tff(c_9000, plain, (~r1_tarski(k1_xboole_0, k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_8988, c_1304])).
% 8.54/2.93  tff(c_9014, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12, c_9000])).
% 8.54/2.93  tff(c_9015, plain, (m1_subset_1('#skF_9', k1_zfmisc_1(k1_xboole_0))), inference(splitRight, [status(thm)], [c_1270])).
% 8.54/2.93  tff(c_36, plain, (![A_20, B_21]: (r1_tarski(A_20, B_21) | ~m1_subset_1(A_20, k1_zfmisc_1(B_21)))), inference(cnfTransformation, [status(thm)], [f_64])).
% 8.54/2.93  tff(c_9046, plain, (r1_tarski('#skF_9', k1_xboole_0)), inference(resolution, [status(thm)], [c_9015, c_36])).
% 8.54/2.93  tff(c_9140, plain, (k1_xboole_0='#skF_9'), inference(resolution, [status(thm)], [c_9046, c_311])).
% 8.54/2.93  tff(c_9182, plain, (![A_8]: (r1_tarski('#skF_9', A_8))), inference(demodulation, [status(thm), theory('equality')], [c_9140, c_14])).
% 8.54/2.93  tff(c_419, plain, (![A_34]: (r1_tarski(k9_relat_1(k1_xboole_0, A_34), k1_xboole_0) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_409, c_54])).
% 8.54/2.93  tff(c_429, plain, (![A_152]: (r1_tarski(k9_relat_1(k1_xboole_0, A_152), k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_116, c_419])).
% 8.54/2.93  tff(c_441, plain, (![A_152]: (k9_relat_1(k1_xboole_0, A_152)=k1_xboole_0)), inference(resolution, [status(thm)], [c_429, c_311])).
% 8.54/2.93  tff(c_9168, plain, (![A_152]: (k9_relat_1('#skF_9', A_152)='#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_9140, c_9140, c_441])).
% 8.54/2.93  tff(c_1087, plain, (![A_236, B_237, C_238, D_239]: (k7_relset_1(A_236, B_237, C_238, D_239)=k9_relat_1(C_238, D_239) | ~m1_subset_1(C_238, k1_zfmisc_1(k2_zfmisc_1(A_236, B_237))))), inference(cnfTransformation, [status(thm)], [f_155])).
% 8.54/2.93  tff(c_1100, plain, (![D_239]: (k7_relset_1(k1_tarski('#skF_6'), '#skF_7', '#skF_9', D_239)=k9_relat_1('#skF_9', D_239))), inference(resolution, [status(thm)], [c_96, c_1087])).
% 8.54/2.93  tff(c_1112, plain, (~r1_tarski(k9_relat_1('#skF_9', '#skF_8'), k1_tarski(k1_funct_1('#skF_9', '#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_1100, c_92])).
% 8.54/2.93  tff(c_9613, plain, (~r1_tarski('#skF_9', k1_tarski(k1_funct_1('#skF_9', '#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_9168, c_1112])).
% 8.54/2.93  tff(c_9617, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_9182, c_9613])).
% 8.54/2.93  tff(c_9619, plain, (k1_tarski('#skF_6')=k1_relat_1('#skF_9')), inference(splitRight, [status(thm)], [c_1029])).
% 8.54/2.93  tff(c_9625, plain, (m1_subset_1('#skF_9', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_9'), '#skF_7')))), inference(demodulation, [status(thm), theory('equality')], [c_9619, c_96])).
% 8.54/2.93  tff(c_88, plain, (![A_93, B_94, C_95, D_96]: (k7_relset_1(A_93, B_94, C_95, D_96)=k9_relat_1(C_95, D_96) | ~m1_subset_1(C_95, k1_zfmisc_1(k2_zfmisc_1(A_93, B_94))))), inference(cnfTransformation, [status(thm)], [f_155])).
% 8.54/2.93  tff(c_9706, plain, (![D_96]: (k7_relset_1(k1_relat_1('#skF_9'), '#skF_7', '#skF_9', D_96)=k9_relat_1('#skF_9', D_96))), inference(resolution, [status(thm)], [c_9625, c_88])).
% 8.54/2.93  tff(c_9618, plain, (~r1_tarski(k7_relset_1(k1_tarski('#skF_6'), '#skF_7', '#skF_9', '#skF_8'), k2_relat_1('#skF_9'))), inference(splitRight, [status(thm)], [c_1029])).
% 8.54/2.93  tff(c_9740, plain, (~r1_tarski(k7_relset_1(k1_relat_1('#skF_9'), '#skF_7', '#skF_9', '#skF_8'), k2_relat_1('#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_9619, c_9618])).
% 8.54/2.93  tff(c_9765, plain, (~r1_tarski(k9_relat_1('#skF_9', '#skF_8'), k2_relat_1('#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_9706, c_9740])).
% 8.54/2.93  tff(c_9783, plain, (~v1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_54, c_9765])).
% 8.54/2.93  tff(c_9787, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_196, c_9783])).
% 8.54/2.93  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.54/2.93  
% 8.54/2.93  Inference rules
% 8.54/2.93  ----------------------
% 8.54/2.93  #Ref     : 0
% 8.54/2.93  #Sup     : 1998
% 8.54/2.93  #Fact    : 0
% 8.54/2.93  #Define  : 0
% 8.54/2.93  #Split   : 9
% 8.54/2.93  #Chain   : 0
% 8.54/2.93  #Close   : 0
% 8.54/2.93  
% 8.54/2.93  Ordering : KBO
% 8.54/2.93  
% 8.54/2.93  Simplification rules
% 8.54/2.93  ----------------------
% 8.54/2.93  #Subsume      : 393
% 8.54/2.94  #Demod        : 2281
% 8.54/2.94  #Tautology    : 675
% 8.54/2.94  #SimpNegUnit  : 55
% 8.54/2.94  #BackRed      : 80
% 8.54/2.94  
% 8.54/2.94  #Partial instantiations: 0
% 8.54/2.94  #Strategies tried      : 1
% 8.54/2.94  
% 8.54/2.94  Timing (in seconds)
% 8.54/2.94  ----------------------
% 8.54/2.94  Preprocessing        : 0.47
% 8.54/2.94  Parsing              : 0.24
% 8.54/2.94  CNF conversion       : 0.04
% 8.54/2.94  Main loop            : 1.57
% 8.54/2.94  Inferencing          : 0.50
% 8.54/2.94  Reduction            : 0.55
% 8.54/2.94  Demodulation         : 0.39
% 8.54/2.94  BG Simplification    : 0.06
% 8.54/2.94  Subsumption          : 0.35
% 8.54/2.94  Abstraction          : 0.06
% 8.54/2.94  MUC search           : 0.00
% 8.54/2.94  Cooper               : 0.00
% 8.54/2.94  Total                : 2.08
% 8.54/2.94  Index Insertion      : 0.00
% 8.54/2.94  Index Deletion       : 0.00
% 8.54/2.94  Index Matching       : 0.00
% 8.54/2.94  BG Taut test         : 0.00
%------------------------------------------------------------------------------
