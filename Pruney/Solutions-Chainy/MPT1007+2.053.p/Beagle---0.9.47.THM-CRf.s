%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:14:18 EST 2020

% Result     : Theorem 7.96s
% Output     : CNFRefutation 7.96s
% Verified   : 
% Statistics : Number of formulae       :   98 ( 173 expanded)
%              Number of leaves         :   48 (  79 expanded)
%              Depth                    :   13
%              Number of atoms          :  158 ( 369 expanded)
%              Number of equality atoms :   42 (  93 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_enumset1 > k1_relset_1 > k1_enumset1 > k4_tarski > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1 > #skF_4 > #skF_7 > #skF_6 > #skF_8 > #skF_5 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

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

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i > $i )).

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

tff(f_45,axiom,(
    ! [A] :
    ? [B] : m1_subset_1(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',existence_m1_subset_1)).

tff(f_29,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_36,axiom,(
    ! [A,B] : ~ v1_xboole_0(k2_tarski(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_xboole_0)).

tff(f_152,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,k1_tarski(A),B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A),B))) )
       => ( B != k1_xboole_0
         => r2_hidden(k1_funct_1(C,A),B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_2)).

tff(f_140,axiom,(
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

tff(f_60,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_104,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_74,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ! [B,C] : ~ r2_hidden(k4_tarski(B,C),A)
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_relat_1)).

tff(f_52,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

tff(f_42,axiom,(
    ! [A,B,C,D] :
      ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(k1_tarski(C),D))
    <=> ( A = C
        & r2_hidden(B,D) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t128_zfmisc_1)).

tff(f_54,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_27,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_122,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(B,A)))
     => ( ! [D] :
            ~ ( r2_hidden(D,B)
              & ! [E] : ~ r2_hidden(k4_tarski(D,E),C) )
      <=> k1_relset_1(B,A,C) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_relset_1)).

tff(f_100,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

tff(f_110,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_85,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A)
        & v1_funct_1(B) )
     => ! [C] :
          ( r2_hidden(C,k1_relat_1(B))
         => r2_hidden(k1_funct_1(B,C),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t172_funct_1)).

tff(f_95,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( r2_hidden(k4_tarski(A,B),C)
      <=> ( r2_hidden(A,k1_relat_1(C))
          & B = k1_funct_1(C,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_funct_1)).

tff(c_18,plain,(
    ! [A_14] : m1_subset_1('#skF_1'(A_14),A_14) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_79,plain,(
    ! [A_65] : k2_tarski(A_65,A_65) = k1_tarski(A_65) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_10,plain,(
    ! [A_8,B_9] : ~ v1_xboole_0(k2_tarski(A_8,B_9)) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_84,plain,(
    ! [A_65] : ~ v1_xboole_0(k1_tarski(A_65)) ),
    inference(superposition,[status(thm),theory(equality)],[c_79,c_10])).

tff(c_66,plain,(
    k1_xboole_0 != '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_70,plain,(
    v1_funct_2('#skF_8',k1_tarski('#skF_6'),'#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_68,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_6'),'#skF_7'))) ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_1245,plain,(
    ! [B_224,A_225,C_226] :
      ( k1_xboole_0 = B_224
      | k1_relset_1(A_225,B_224,C_226) = A_225
      | ~ v1_funct_2(C_226,A_225,B_224)
      | ~ m1_subset_1(C_226,k1_zfmisc_1(k2_zfmisc_1(A_225,B_224))) ) ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_1264,plain,
    ( k1_xboole_0 = '#skF_7'
    | k1_relset_1(k1_tarski('#skF_6'),'#skF_7','#skF_8') = k1_tarski('#skF_6')
    | ~ v1_funct_2('#skF_8',k1_tarski('#skF_6'),'#skF_7') ),
    inference(resolution,[status(thm)],[c_68,c_1245])).

tff(c_1279,plain,
    ( k1_xboole_0 = '#skF_7'
    | k1_relset_1(k1_tarski('#skF_6'),'#skF_7','#skF_8') = k1_tarski('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_1264])).

tff(c_1280,plain,(
    k1_relset_1(k1_tarski('#skF_6'),'#skF_7','#skF_8') = k1_tarski('#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_1279])).

tff(c_24,plain,(
    ! [A_21,B_22] :
      ( r2_hidden(A_21,B_22)
      | v1_xboole_0(B_22)
      | ~ m1_subset_1(A_21,B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_102,plain,(
    ! [C_72,A_73,B_74] :
      ( v1_relat_1(C_72)
      | ~ m1_subset_1(C_72,k1_zfmisc_1(k2_zfmisc_1(A_73,B_74))) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_114,plain,(
    v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_68,c_102])).

tff(c_217,plain,(
    ! [A_112] :
      ( k1_xboole_0 = A_112
      | r2_hidden(k4_tarski('#skF_2'(A_112),'#skF_3'(A_112)),A_112)
      | ~ v1_relat_1(A_112) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_20,plain,(
    ! [C_19,A_16,B_17] :
      ( r2_hidden(C_19,A_16)
      | ~ r2_hidden(C_19,B_17)
      | ~ m1_subset_1(B_17,k1_zfmisc_1(A_16)) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_1705,plain,(
    ! [A_275,A_276] :
      ( r2_hidden(k4_tarski('#skF_2'(A_275),'#skF_3'(A_275)),A_276)
      | ~ m1_subset_1(A_275,k1_zfmisc_1(A_276))
      | k1_xboole_0 = A_275
      | ~ v1_relat_1(A_275) ) ),
    inference(resolution,[status(thm)],[c_217,c_20])).

tff(c_16,plain,(
    ! [C_12,A_10,B_11,D_13] :
      ( C_12 = A_10
      | ~ r2_hidden(k4_tarski(A_10,B_11),k2_zfmisc_1(k1_tarski(C_12),D_13)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_1856,plain,(
    ! [C_286,A_287,D_288] :
      ( C_286 = '#skF_2'(A_287)
      | ~ m1_subset_1(A_287,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(C_286),D_288)))
      | k1_xboole_0 = A_287
      | ~ v1_relat_1(A_287) ) ),
    inference(resolution,[status(thm)],[c_1705,c_16])).

tff(c_1867,plain,
    ( '#skF_2'('#skF_8') = '#skF_6'
    | k1_xboole_0 = '#skF_8'
    | ~ v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_68,c_1856])).

tff(c_1880,plain,
    ( '#skF_2'('#skF_8') = '#skF_6'
    | k1_xboole_0 = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_114,c_1867])).

tff(c_1888,plain,(
    k1_xboole_0 = '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_1880])).

tff(c_22,plain,(
    ! [A_20] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_20)) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_1928,plain,(
    ! [A_20] : m1_subset_1('#skF_8',k1_zfmisc_1(A_20)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1888,c_22])).

tff(c_2,plain,(
    ! [A_1] : r1_tarski(k1_xboole_0,A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_1929,plain,(
    ! [A_1] : r1_tarski('#skF_8',A_1) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1888,c_2])).

tff(c_1486,plain,(
    ! [D_251,A_252,B_253,C_254] :
      ( r2_hidden(k4_tarski(D_251,'#skF_5'(A_252,B_253,C_254,D_251)),C_254)
      | ~ r2_hidden(D_251,B_253)
      | k1_relset_1(B_253,A_252,C_254) != B_253
      | ~ m1_subset_1(C_254,k1_zfmisc_1(k2_zfmisc_1(B_253,A_252))) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_38,plain,(
    ! [B_37,A_36] :
      ( ~ r1_tarski(B_37,A_36)
      | ~ r2_hidden(A_36,B_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_7394,plain,(
    ! [C_6537,D_6538,A_6539,B_6540] :
      ( ~ r1_tarski(C_6537,k4_tarski(D_6538,'#skF_5'(A_6539,B_6540,C_6537,D_6538)))
      | ~ r2_hidden(D_6538,B_6540)
      | k1_relset_1(B_6540,A_6539,C_6537) != B_6540
      | ~ m1_subset_1(C_6537,k1_zfmisc_1(k2_zfmisc_1(B_6540,A_6539))) ) ),
    inference(resolution,[status(thm)],[c_1486,c_38])).

tff(c_7407,plain,(
    ! [D_6538,B_6540,A_6539] :
      ( ~ r2_hidden(D_6538,B_6540)
      | k1_relset_1(B_6540,A_6539,'#skF_8') != B_6540
      | ~ m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1(B_6540,A_6539))) ) ),
    inference(resolution,[status(thm)],[c_1929,c_7394])).

tff(c_7413,plain,(
    ! [D_6572,B_6573,A_6574] :
      ( ~ r2_hidden(D_6572,B_6573)
      | k1_relset_1(B_6573,A_6574,'#skF_8') != B_6573 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1928,c_7407])).

tff(c_7511,plain,(
    ! [B_6579,A_6580,A_6581] :
      ( k1_relset_1(B_6579,A_6580,'#skF_8') != B_6579
      | v1_xboole_0(B_6579)
      | ~ m1_subset_1(A_6581,B_6579) ) ),
    inference(resolution,[status(thm)],[c_24,c_7413])).

tff(c_7523,plain,(
    ! [A_6581] :
      ( v1_xboole_0(k1_tarski('#skF_6'))
      | ~ m1_subset_1(A_6581,k1_tarski('#skF_6')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1280,c_7511])).

tff(c_7536,plain,(
    ! [A_6582] : ~ m1_subset_1(A_6582,k1_tarski('#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_84,c_7523])).

tff(c_7568,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_18,c_7536])).

tff(c_7570,plain,(
    k1_xboole_0 != '#skF_8' ),
    inference(splitRight,[status(thm)],[c_1880])).

tff(c_150,plain,(
    ! [C_85,B_86,A_87] :
      ( v5_relat_1(C_85,B_86)
      | ~ m1_subset_1(C_85,k1_zfmisc_1(k2_zfmisc_1(A_87,B_86))) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_162,plain,(
    v5_relat_1('#skF_8','#skF_7') ),
    inference(resolution,[status(thm)],[c_68,c_150])).

tff(c_72,plain,(
    v1_funct_1('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_1091,plain,(
    ! [B_209,C_210,A_211] :
      ( r2_hidden(k1_funct_1(B_209,C_210),A_211)
      | ~ r2_hidden(C_210,k1_relat_1(B_209))
      | ~ v1_funct_1(B_209)
      | ~ v5_relat_1(B_209,A_211)
      | ~ v1_relat_1(B_209) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_64,plain,(
    ~ r2_hidden(k1_funct_1('#skF_8','#skF_6'),'#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_1106,plain,
    ( ~ r2_hidden('#skF_6',k1_relat_1('#skF_8'))
    | ~ v1_funct_1('#skF_8')
    | ~ v5_relat_1('#skF_8','#skF_7')
    | ~ v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_1091,c_64])).

tff(c_1116,plain,(
    ~ r2_hidden('#skF_6',k1_relat_1('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_114,c_162,c_72,c_1106])).

tff(c_7569,plain,(
    '#skF_2'('#skF_8') = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_1880])).

tff(c_28,plain,(
    ! [A_26] :
      ( k1_xboole_0 = A_26
      | r2_hidden(k4_tarski('#skF_2'(A_26),'#skF_3'(A_26)),A_26)
      | ~ v1_relat_1(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_306,plain,(
    ! [A_130,C_131,B_132] :
      ( r2_hidden(A_130,k1_relat_1(C_131))
      | ~ r2_hidden(k4_tarski(A_130,B_132),C_131)
      | ~ v1_funct_1(C_131)
      | ~ v1_relat_1(C_131) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_318,plain,(
    ! [A_26] :
      ( r2_hidden('#skF_2'(A_26),k1_relat_1(A_26))
      | ~ v1_funct_1(A_26)
      | k1_xboole_0 = A_26
      | ~ v1_relat_1(A_26) ) ),
    inference(resolution,[status(thm)],[c_28,c_306])).

tff(c_7590,plain,
    ( r2_hidden('#skF_6',k1_relat_1('#skF_8'))
    | ~ v1_funct_1('#skF_8')
    | k1_xboole_0 = '#skF_8'
    | ~ v1_relat_1('#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_7569,c_318])).

tff(c_7609,plain,
    ( r2_hidden('#skF_6',k1_relat_1('#skF_8'))
    | k1_xboole_0 = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_114,c_72,c_7590])).

tff(c_7611,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_7570,c_1116,c_7609])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n025.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 20:16:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.96/2.71  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.96/2.71  
% 7.96/2.71  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.96/2.71  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_enumset1 > k1_relset_1 > k1_enumset1 > k4_tarski > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1 > #skF_4 > #skF_7 > #skF_6 > #skF_8 > #skF_5 > #skF_3
% 7.96/2.71  
% 7.96/2.71  %Foreground sorts:
% 7.96/2.71  
% 7.96/2.71  
% 7.96/2.71  %Background operators:
% 7.96/2.71  
% 7.96/2.71  
% 7.96/2.71  %Foreground operators:
% 7.96/2.71  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 7.96/2.71  tff('#skF_2', type, '#skF_2': $i > $i).
% 7.96/2.71  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.96/2.71  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 7.96/2.71  tff(k1_tarski, type, k1_tarski: $i > $i).
% 7.96/2.71  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 7.96/2.71  tff('#skF_1', type, '#skF_1': $i > $i).
% 7.96/2.71  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 7.96/2.71  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 7.96/2.71  tff('#skF_7', type, '#skF_7': $i).
% 7.96/2.71  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.96/2.71  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 7.96/2.71  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 7.96/2.71  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 7.96/2.71  tff('#skF_6', type, '#skF_6': $i).
% 7.96/2.71  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 7.96/2.71  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 7.96/2.71  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 7.96/2.71  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 7.96/2.71  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 7.96/2.71  tff('#skF_8', type, '#skF_8': $i).
% 7.96/2.71  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.96/2.71  tff('#skF_5', type, '#skF_5': ($i * $i * $i * $i) > $i).
% 7.96/2.71  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 7.96/2.71  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 7.96/2.71  tff('#skF_3', type, '#skF_3': $i > $i).
% 7.96/2.71  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.96/2.71  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 7.96/2.71  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 7.96/2.71  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 7.96/2.71  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 7.96/2.71  
% 7.96/2.73  tff(f_45, axiom, (![A]: (?[B]: m1_subset_1(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', existence_m1_subset_1)).
% 7.96/2.73  tff(f_29, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 7.96/2.73  tff(f_36, axiom, (![A, B]: ~v1_xboole_0(k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc3_xboole_0)).
% 7.96/2.73  tff(f_152, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, k1_tarski(A), B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A), B)))) => (~(B = k1_xboole_0) => r2_hidden(k1_funct_1(C, A), B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t61_funct_2)).
% 7.96/2.73  tff(f_140, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 7.96/2.73  tff(f_60, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 7.96/2.73  tff(f_104, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 7.96/2.73  tff(f_74, axiom, (![A]: (v1_relat_1(A) => ((![B, C]: ~r2_hidden(k4_tarski(B, C), A)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t56_relat_1)).
% 7.96/2.73  tff(f_52, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_subset_1)).
% 7.96/2.73  tff(f_42, axiom, (![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(k1_tarski(C), D)) <=> ((A = C) & r2_hidden(B, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t128_zfmisc_1)).
% 7.96/2.73  tff(f_54, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 7.96/2.73  tff(f_27, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 7.96/2.73  tff(f_122, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => ((![D]: ~(r2_hidden(D, B) & (![E]: ~r2_hidden(k4_tarski(D, E), C)))) <=> (k1_relset_1(B, A, C) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t22_relset_1)).
% 7.96/2.73  tff(f_100, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 7.96/2.73  tff(f_110, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 7.96/2.73  tff(f_85, axiom, (![A, B]: (((v1_relat_1(B) & v5_relat_1(B, A)) & v1_funct_1(B)) => (![C]: (r2_hidden(C, k1_relat_1(B)) => r2_hidden(k1_funct_1(B, C), A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t172_funct_1)).
% 7.96/2.73  tff(f_95, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(k4_tarski(A, B), C) <=> (r2_hidden(A, k1_relat_1(C)) & (B = k1_funct_1(C, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_funct_1)).
% 7.96/2.73  tff(c_18, plain, (![A_14]: (m1_subset_1('#skF_1'(A_14), A_14))), inference(cnfTransformation, [status(thm)], [f_45])).
% 7.96/2.73  tff(c_79, plain, (![A_65]: (k2_tarski(A_65, A_65)=k1_tarski(A_65))), inference(cnfTransformation, [status(thm)], [f_29])).
% 7.96/2.73  tff(c_10, plain, (![A_8, B_9]: (~v1_xboole_0(k2_tarski(A_8, B_9)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 7.96/2.73  tff(c_84, plain, (![A_65]: (~v1_xboole_0(k1_tarski(A_65)))), inference(superposition, [status(thm), theory('equality')], [c_79, c_10])).
% 7.96/2.73  tff(c_66, plain, (k1_xboole_0!='#skF_7'), inference(cnfTransformation, [status(thm)], [f_152])).
% 7.96/2.73  tff(c_70, plain, (v1_funct_2('#skF_8', k1_tarski('#skF_6'), '#skF_7')), inference(cnfTransformation, [status(thm)], [f_152])).
% 7.96/2.73  tff(c_68, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_6'), '#skF_7')))), inference(cnfTransformation, [status(thm)], [f_152])).
% 7.96/2.73  tff(c_1245, plain, (![B_224, A_225, C_226]: (k1_xboole_0=B_224 | k1_relset_1(A_225, B_224, C_226)=A_225 | ~v1_funct_2(C_226, A_225, B_224) | ~m1_subset_1(C_226, k1_zfmisc_1(k2_zfmisc_1(A_225, B_224))))), inference(cnfTransformation, [status(thm)], [f_140])).
% 7.96/2.73  tff(c_1264, plain, (k1_xboole_0='#skF_7' | k1_relset_1(k1_tarski('#skF_6'), '#skF_7', '#skF_8')=k1_tarski('#skF_6') | ~v1_funct_2('#skF_8', k1_tarski('#skF_6'), '#skF_7')), inference(resolution, [status(thm)], [c_68, c_1245])).
% 7.96/2.73  tff(c_1279, plain, (k1_xboole_0='#skF_7' | k1_relset_1(k1_tarski('#skF_6'), '#skF_7', '#skF_8')=k1_tarski('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_1264])).
% 7.96/2.73  tff(c_1280, plain, (k1_relset_1(k1_tarski('#skF_6'), '#skF_7', '#skF_8')=k1_tarski('#skF_6')), inference(negUnitSimplification, [status(thm)], [c_66, c_1279])).
% 7.96/2.73  tff(c_24, plain, (![A_21, B_22]: (r2_hidden(A_21, B_22) | v1_xboole_0(B_22) | ~m1_subset_1(A_21, B_22))), inference(cnfTransformation, [status(thm)], [f_60])).
% 7.96/2.73  tff(c_102, plain, (![C_72, A_73, B_74]: (v1_relat_1(C_72) | ~m1_subset_1(C_72, k1_zfmisc_1(k2_zfmisc_1(A_73, B_74))))), inference(cnfTransformation, [status(thm)], [f_104])).
% 7.96/2.73  tff(c_114, plain, (v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_68, c_102])).
% 7.96/2.73  tff(c_217, plain, (![A_112]: (k1_xboole_0=A_112 | r2_hidden(k4_tarski('#skF_2'(A_112), '#skF_3'(A_112)), A_112) | ~v1_relat_1(A_112))), inference(cnfTransformation, [status(thm)], [f_74])).
% 7.96/2.73  tff(c_20, plain, (![C_19, A_16, B_17]: (r2_hidden(C_19, A_16) | ~r2_hidden(C_19, B_17) | ~m1_subset_1(B_17, k1_zfmisc_1(A_16)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 7.96/2.73  tff(c_1705, plain, (![A_275, A_276]: (r2_hidden(k4_tarski('#skF_2'(A_275), '#skF_3'(A_275)), A_276) | ~m1_subset_1(A_275, k1_zfmisc_1(A_276)) | k1_xboole_0=A_275 | ~v1_relat_1(A_275))), inference(resolution, [status(thm)], [c_217, c_20])).
% 7.96/2.73  tff(c_16, plain, (![C_12, A_10, B_11, D_13]: (C_12=A_10 | ~r2_hidden(k4_tarski(A_10, B_11), k2_zfmisc_1(k1_tarski(C_12), D_13)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 7.96/2.73  tff(c_1856, plain, (![C_286, A_287, D_288]: (C_286='#skF_2'(A_287) | ~m1_subset_1(A_287, k1_zfmisc_1(k2_zfmisc_1(k1_tarski(C_286), D_288))) | k1_xboole_0=A_287 | ~v1_relat_1(A_287))), inference(resolution, [status(thm)], [c_1705, c_16])).
% 7.96/2.73  tff(c_1867, plain, ('#skF_2'('#skF_8')='#skF_6' | k1_xboole_0='#skF_8' | ~v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_68, c_1856])).
% 7.96/2.73  tff(c_1880, plain, ('#skF_2'('#skF_8')='#skF_6' | k1_xboole_0='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_114, c_1867])).
% 7.96/2.73  tff(c_1888, plain, (k1_xboole_0='#skF_8'), inference(splitLeft, [status(thm)], [c_1880])).
% 7.96/2.73  tff(c_22, plain, (![A_20]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_20)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 7.96/2.73  tff(c_1928, plain, (![A_20]: (m1_subset_1('#skF_8', k1_zfmisc_1(A_20)))), inference(demodulation, [status(thm), theory('equality')], [c_1888, c_22])).
% 7.96/2.73  tff(c_2, plain, (![A_1]: (r1_tarski(k1_xboole_0, A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 7.96/2.73  tff(c_1929, plain, (![A_1]: (r1_tarski('#skF_8', A_1))), inference(demodulation, [status(thm), theory('equality')], [c_1888, c_2])).
% 7.96/2.73  tff(c_1486, plain, (![D_251, A_252, B_253, C_254]: (r2_hidden(k4_tarski(D_251, '#skF_5'(A_252, B_253, C_254, D_251)), C_254) | ~r2_hidden(D_251, B_253) | k1_relset_1(B_253, A_252, C_254)!=B_253 | ~m1_subset_1(C_254, k1_zfmisc_1(k2_zfmisc_1(B_253, A_252))))), inference(cnfTransformation, [status(thm)], [f_122])).
% 7.96/2.73  tff(c_38, plain, (![B_37, A_36]: (~r1_tarski(B_37, A_36) | ~r2_hidden(A_36, B_37))), inference(cnfTransformation, [status(thm)], [f_100])).
% 7.96/2.73  tff(c_7394, plain, (![C_6537, D_6538, A_6539, B_6540]: (~r1_tarski(C_6537, k4_tarski(D_6538, '#skF_5'(A_6539, B_6540, C_6537, D_6538))) | ~r2_hidden(D_6538, B_6540) | k1_relset_1(B_6540, A_6539, C_6537)!=B_6540 | ~m1_subset_1(C_6537, k1_zfmisc_1(k2_zfmisc_1(B_6540, A_6539))))), inference(resolution, [status(thm)], [c_1486, c_38])).
% 7.96/2.73  tff(c_7407, plain, (![D_6538, B_6540, A_6539]: (~r2_hidden(D_6538, B_6540) | k1_relset_1(B_6540, A_6539, '#skF_8')!=B_6540 | ~m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1(B_6540, A_6539))))), inference(resolution, [status(thm)], [c_1929, c_7394])).
% 7.96/2.73  tff(c_7413, plain, (![D_6572, B_6573, A_6574]: (~r2_hidden(D_6572, B_6573) | k1_relset_1(B_6573, A_6574, '#skF_8')!=B_6573)), inference(demodulation, [status(thm), theory('equality')], [c_1928, c_7407])).
% 7.96/2.73  tff(c_7511, plain, (![B_6579, A_6580, A_6581]: (k1_relset_1(B_6579, A_6580, '#skF_8')!=B_6579 | v1_xboole_0(B_6579) | ~m1_subset_1(A_6581, B_6579))), inference(resolution, [status(thm)], [c_24, c_7413])).
% 7.96/2.73  tff(c_7523, plain, (![A_6581]: (v1_xboole_0(k1_tarski('#skF_6')) | ~m1_subset_1(A_6581, k1_tarski('#skF_6')))), inference(superposition, [status(thm), theory('equality')], [c_1280, c_7511])).
% 7.96/2.73  tff(c_7536, plain, (![A_6582]: (~m1_subset_1(A_6582, k1_tarski('#skF_6')))), inference(negUnitSimplification, [status(thm)], [c_84, c_7523])).
% 7.96/2.73  tff(c_7568, plain, $false, inference(resolution, [status(thm)], [c_18, c_7536])).
% 7.96/2.73  tff(c_7570, plain, (k1_xboole_0!='#skF_8'), inference(splitRight, [status(thm)], [c_1880])).
% 7.96/2.73  tff(c_150, plain, (![C_85, B_86, A_87]: (v5_relat_1(C_85, B_86) | ~m1_subset_1(C_85, k1_zfmisc_1(k2_zfmisc_1(A_87, B_86))))), inference(cnfTransformation, [status(thm)], [f_110])).
% 7.96/2.73  tff(c_162, plain, (v5_relat_1('#skF_8', '#skF_7')), inference(resolution, [status(thm)], [c_68, c_150])).
% 7.96/2.73  tff(c_72, plain, (v1_funct_1('#skF_8')), inference(cnfTransformation, [status(thm)], [f_152])).
% 7.96/2.73  tff(c_1091, plain, (![B_209, C_210, A_211]: (r2_hidden(k1_funct_1(B_209, C_210), A_211) | ~r2_hidden(C_210, k1_relat_1(B_209)) | ~v1_funct_1(B_209) | ~v5_relat_1(B_209, A_211) | ~v1_relat_1(B_209))), inference(cnfTransformation, [status(thm)], [f_85])).
% 7.96/2.73  tff(c_64, plain, (~r2_hidden(k1_funct_1('#skF_8', '#skF_6'), '#skF_7')), inference(cnfTransformation, [status(thm)], [f_152])).
% 7.96/2.73  tff(c_1106, plain, (~r2_hidden('#skF_6', k1_relat_1('#skF_8')) | ~v1_funct_1('#skF_8') | ~v5_relat_1('#skF_8', '#skF_7') | ~v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_1091, c_64])).
% 7.96/2.73  tff(c_1116, plain, (~r2_hidden('#skF_6', k1_relat_1('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_114, c_162, c_72, c_1106])).
% 7.96/2.73  tff(c_7569, plain, ('#skF_2'('#skF_8')='#skF_6'), inference(splitRight, [status(thm)], [c_1880])).
% 7.96/2.73  tff(c_28, plain, (![A_26]: (k1_xboole_0=A_26 | r2_hidden(k4_tarski('#skF_2'(A_26), '#skF_3'(A_26)), A_26) | ~v1_relat_1(A_26))), inference(cnfTransformation, [status(thm)], [f_74])).
% 7.96/2.73  tff(c_306, plain, (![A_130, C_131, B_132]: (r2_hidden(A_130, k1_relat_1(C_131)) | ~r2_hidden(k4_tarski(A_130, B_132), C_131) | ~v1_funct_1(C_131) | ~v1_relat_1(C_131))), inference(cnfTransformation, [status(thm)], [f_95])).
% 7.96/2.73  tff(c_318, plain, (![A_26]: (r2_hidden('#skF_2'(A_26), k1_relat_1(A_26)) | ~v1_funct_1(A_26) | k1_xboole_0=A_26 | ~v1_relat_1(A_26))), inference(resolution, [status(thm)], [c_28, c_306])).
% 7.96/2.73  tff(c_7590, plain, (r2_hidden('#skF_6', k1_relat_1('#skF_8')) | ~v1_funct_1('#skF_8') | k1_xboole_0='#skF_8' | ~v1_relat_1('#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_7569, c_318])).
% 7.96/2.73  tff(c_7609, plain, (r2_hidden('#skF_6', k1_relat_1('#skF_8')) | k1_xboole_0='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_114, c_72, c_7590])).
% 7.96/2.73  tff(c_7611, plain, $false, inference(negUnitSimplification, [status(thm)], [c_7570, c_1116, c_7609])).
% 7.96/2.73  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.96/2.73  
% 7.96/2.73  Inference rules
% 7.96/2.73  ----------------------
% 7.96/2.73  #Ref     : 0
% 7.96/2.73  #Sup     : 1678
% 7.96/2.73  #Fact    : 0
% 7.96/2.73  #Define  : 0
% 7.96/2.73  #Split   : 24
% 7.96/2.73  #Chain   : 0
% 7.96/2.73  #Close   : 0
% 7.96/2.73  
% 7.96/2.73  Ordering : KBO
% 7.96/2.73  
% 7.96/2.73  Simplification rules
% 7.96/2.73  ----------------------
% 7.96/2.73  #Subsume      : 196
% 7.96/2.73  #Demod        : 574
% 7.96/2.73  #Tautology    : 259
% 7.96/2.73  #SimpNegUnit  : 17
% 7.96/2.73  #BackRed      : 74
% 7.96/2.73  
% 7.96/2.73  #Partial instantiations: 3648
% 7.96/2.73  #Strategies tried      : 1
% 7.96/2.73  
% 7.96/2.73  Timing (in seconds)
% 7.96/2.73  ----------------------
% 7.96/2.73  Preprocessing        : 0.35
% 7.96/2.73  Parsing              : 0.18
% 7.96/2.73  CNF conversion       : 0.02
% 7.96/2.73  Main loop            : 1.62
% 7.96/2.73  Inferencing          : 0.51
% 7.96/2.73  Reduction            : 0.51
% 7.96/2.73  Demodulation         : 0.33
% 7.96/2.73  BG Simplification    : 0.07
% 7.96/2.73  Subsumption          : 0.39
% 7.96/2.73  Abstraction          : 0.08
% 7.96/2.73  MUC search           : 0.00
% 7.96/2.73  Cooper               : 0.00
% 7.96/2.73  Total                : 2.00
% 7.96/2.73  Index Insertion      : 0.00
% 7.96/2.73  Index Deletion       : 0.00
% 7.96/2.73  Index Matching       : 0.00
% 7.96/2.74  BG Taut test         : 0.00
%------------------------------------------------------------------------------
