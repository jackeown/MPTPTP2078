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
% DateTime   : Thu Dec  3 10:14:18 EST 2020

% Result     : Theorem 3.87s
% Output     : CNFRefutation 3.87s
% Verified   : 
% Statistics : Number of formulae       :  149 ( 719 expanded)
%              Number of leaves         :   49 ( 256 expanded)
%              Depth                    :   18
%              Number of atoms          :  267 (1741 expanded)
%              Number of equality atoms :   75 ( 295 expanded)
%              Maximal formula depth    :   17 (   4 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_enumset1 > k1_relset_1 > k1_enumset1 > k4_tarski > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_1 > #skF_7 > #skF_6 > #skF_4 > #skF_8 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_5',type,(
    '#skF_5': $i > $i )).

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

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_29,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_166,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,k1_tarski(A),B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A),B))) )
       => ( B != k1_xboole_0
         => r2_hidden(k1_funct_1(C,A),B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_2)).

tff(f_97,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_67,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ! [B,C] : ~ r2_hidden(k4_tarski(B,C),A)
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_relat_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

tff(f_41,axiom,(
    ! [A,B,C,D] :
      ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(k1_tarski(C),D))
    <=> ( A = C
        & r2_hidden(B,D) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t128_zfmisc_1)).

tff(f_27,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

tff(f_44,axiom,(
    ! [A,B] : k2_xboole_0(k1_tarski(A),B) != k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_zfmisc_1)).

tff(f_154,axiom,(
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

tff(f_136,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] :
            ~ ( r2_hidden(B,A)
              & ! [C,D,E,F,G] :
                  ( ( r2_hidden(C,D)
                    & r2_hidden(D,E)
                    & r2_hidden(E,F)
                    & r2_hidden(F,G)
                    & r2_hidden(G,B) )
                 => r1_xboole_0(C,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_mcart_1)).

tff(f_53,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_115,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(B,A)))
     => ( ! [D] :
            ~ ( r2_hidden(D,B)
              & ! [E] : ~ r2_hidden(k4_tarski(D,E),C) )
      <=> k1_relset_1(B,A,C) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_relset_1)).

tff(f_88,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( r2_hidden(k4_tarski(A,B),C)
      <=> ( r2_hidden(A,k1_relat_1(C))
          & B = k1_funct_1(C,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_funct_1)).

tff(f_59,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

tff(f_103,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_78,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A)
        & v1_funct_1(B) )
     => ! [C] :
          ( r2_hidden(C,k1_relat_1(B))
         => r2_hidden(k1_funct_1(B,C),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t172_funct_1)).

tff(f_93,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

tff(c_4,plain,(
    ! [A_2] : r1_tarski(k1_xboole_0,A_2) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_70,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_6'),'#skF_7'))) ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_126,plain,(
    ! [C_93,A_94,B_95] :
      ( v1_relat_1(C_93)
      | ~ m1_subset_1(C_93,k1_zfmisc_1(k2_zfmisc_1(A_94,B_95))) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_134,plain,(
    v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_70,c_126])).

tff(c_261,plain,(
    ! [A_135] :
      ( k1_xboole_0 = A_135
      | r2_hidden(k4_tarski('#skF_1'(A_135),'#skF_2'(A_135)),A_135)
      | ~ v1_relat_1(A_135) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_20,plain,(
    ! [C_18,A_15,B_16] :
      ( r2_hidden(C_18,A_15)
      | ~ r2_hidden(C_18,B_16)
      | ~ m1_subset_1(B_16,k1_zfmisc_1(A_15)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_1139,plain,(
    ! [A_266,A_267] :
      ( r2_hidden(k4_tarski('#skF_1'(A_266),'#skF_2'(A_266)),A_267)
      | ~ m1_subset_1(A_266,k1_zfmisc_1(A_267))
      | k1_xboole_0 = A_266
      | ~ v1_relat_1(A_266) ) ),
    inference(resolution,[status(thm)],[c_261,c_20])).

tff(c_16,plain,(
    ! [C_11,A_9,B_10,D_12] :
      ( C_11 = A_9
      | ~ r2_hidden(k4_tarski(A_9,B_10),k2_zfmisc_1(k1_tarski(C_11),D_12)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_1182,plain,(
    ! [C_268,A_269,D_270] :
      ( C_268 = '#skF_1'(A_269)
      | ~ m1_subset_1(A_269,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(C_268),D_270)))
      | k1_xboole_0 = A_269
      | ~ v1_relat_1(A_269) ) ),
    inference(resolution,[status(thm)],[c_1139,c_16])).

tff(c_1185,plain,
    ( '#skF_1'('#skF_8') = '#skF_6'
    | k1_xboole_0 = '#skF_8'
    | ~ v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_70,c_1182])).

tff(c_1192,plain,
    ( '#skF_1'('#skF_8') = '#skF_6'
    | k1_xboole_0 = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_134,c_1185])).

tff(c_1197,plain,(
    k1_xboole_0 = '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_1192])).

tff(c_2,plain,(
    ! [A_1] : k2_xboole_0(A_1,k1_xboole_0) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_97,plain,(
    ! [A_83,B_84] : k2_xboole_0(k1_tarski(A_83),B_84) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_101,plain,(
    ! [A_83] : k1_tarski(A_83) != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_97])).

tff(c_1246,plain,(
    ! [A_83] : k1_tarski(A_83) != '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1197,c_101])).

tff(c_68,plain,(
    k1_xboole_0 != '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_72,plain,(
    v1_funct_2('#skF_8',k1_tarski('#skF_6'),'#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_796,plain,(
    ! [B_198,A_199,C_200] :
      ( k1_xboole_0 = B_198
      | k1_relset_1(A_199,B_198,C_200) = A_199
      | ~ v1_funct_2(C_200,A_199,B_198)
      | ~ m1_subset_1(C_200,k1_zfmisc_1(k2_zfmisc_1(A_199,B_198))) ) ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_799,plain,
    ( k1_xboole_0 = '#skF_7'
    | k1_relset_1(k1_tarski('#skF_6'),'#skF_7','#skF_8') = k1_tarski('#skF_6')
    | ~ v1_funct_2('#skF_8',k1_tarski('#skF_6'),'#skF_7') ),
    inference(resolution,[status(thm)],[c_70,c_796])).

tff(c_806,plain,
    ( k1_xboole_0 = '#skF_7'
    | k1_relset_1(k1_tarski('#skF_6'),'#skF_7','#skF_8') = k1_tarski('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_799])).

tff(c_807,plain,(
    k1_relset_1(k1_tarski('#skF_6'),'#skF_7','#skF_8') = k1_tarski('#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_806])).

tff(c_52,plain,(
    ! [A_54] :
      ( r2_hidden('#skF_5'(A_54),A_54)
      | k1_xboole_0 = A_54 ) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_22,plain,(
    ! [A_19] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_19)) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_989,plain,(
    ! [D_233,A_234,B_235,C_236] :
      ( r2_hidden(k4_tarski(D_233,'#skF_4'(A_234,B_235,C_236,D_233)),C_236)
      | ~ r2_hidden(D_233,B_235)
      | k1_relset_1(B_235,A_234,C_236) != B_235
      | ~ m1_subset_1(C_236,k1_zfmisc_1(k2_zfmisc_1(B_235,A_234))) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_135,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_22,c_126])).

tff(c_74,plain,(
    v1_funct_1('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_429,plain,(
    ! [A_172,A_173] :
      ( r2_hidden(k4_tarski('#skF_1'(A_172),'#skF_2'(A_172)),A_173)
      | ~ m1_subset_1(A_172,k1_zfmisc_1(A_173))
      | k1_xboole_0 = A_172
      | ~ v1_relat_1(A_172) ) ),
    inference(resolution,[status(thm)],[c_261,c_20])).

tff(c_480,plain,(
    ! [C_177,A_178,D_179] :
      ( C_177 = '#skF_1'(A_178)
      | ~ m1_subset_1(A_178,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(C_177),D_179)))
      | k1_xboole_0 = A_178
      | ~ v1_relat_1(A_178) ) ),
    inference(resolution,[status(thm)],[c_429,c_16])).

tff(c_483,plain,
    ( '#skF_1'('#skF_8') = '#skF_6'
    | k1_xboole_0 = '#skF_8'
    | ~ v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_70,c_480])).

tff(c_490,plain,
    ( '#skF_1'('#skF_8') = '#skF_6'
    | k1_xboole_0 = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_134,c_483])).

tff(c_495,plain,(
    k1_xboole_0 = '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_490])).

tff(c_361,plain,(
    ! [A_158,C_159] :
      ( r2_hidden(k4_tarski(A_158,k1_funct_1(C_159,A_158)),C_159)
      | ~ r2_hidden(A_158,k1_relat_1(C_159))
      | ~ v1_funct_1(C_159)
      | ~ v1_relat_1(C_159) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_172,plain,(
    ! [A_114,C_115,B_116] :
      ( m1_subset_1(A_114,C_115)
      | ~ m1_subset_1(B_116,k1_zfmisc_1(C_115))
      | ~ r2_hidden(A_114,B_116) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_178,plain,(
    ! [A_114,A_19] :
      ( m1_subset_1(A_114,A_19)
      | ~ r2_hidden(A_114,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_22,c_172])).

tff(c_374,plain,(
    ! [A_158,A_19] :
      ( m1_subset_1(k4_tarski(A_158,k1_funct_1(k1_xboole_0,A_158)),A_19)
      | ~ r2_hidden(A_158,k1_relat_1(k1_xboole_0))
      | ~ v1_funct_1(k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_361,c_178])).

tff(c_393,plain,(
    ! [A_158,A_19] :
      ( m1_subset_1(k4_tarski(A_158,k1_funct_1(k1_xboole_0,A_158)),A_19)
      | ~ r2_hidden(A_158,k1_relat_1(k1_xboole_0))
      | ~ v1_funct_1(k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_135,c_374])).

tff(c_404,plain,(
    ~ v1_funct_1(k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_393])).

tff(c_501,plain,(
    ~ v1_funct_1('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_495,c_404])).

tff(c_531,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_501])).

tff(c_533,plain,(
    k1_xboole_0 != '#skF_8' ),
    inference(splitRight,[status(thm)],[c_490])).

tff(c_156,plain,(
    ! [C_103,B_104,A_105] :
      ( v5_relat_1(C_103,B_104)
      | ~ m1_subset_1(C_103,k1_zfmisc_1(k2_zfmisc_1(A_105,B_104))) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_164,plain,(
    v5_relat_1('#skF_8','#skF_7') ),
    inference(resolution,[status(thm)],[c_70,c_156])).

tff(c_459,plain,(
    ! [B_174,C_175,A_176] :
      ( r2_hidden(k1_funct_1(B_174,C_175),A_176)
      | ~ r2_hidden(C_175,k1_relat_1(B_174))
      | ~ v1_funct_1(B_174)
      | ~ v5_relat_1(B_174,A_176)
      | ~ v1_relat_1(B_174) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_66,plain,(
    ~ r2_hidden(k1_funct_1('#skF_8','#skF_6'),'#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_470,plain,
    ( ~ r2_hidden('#skF_6',k1_relat_1('#skF_8'))
    | ~ v1_funct_1('#skF_8')
    | ~ v5_relat_1('#skF_8','#skF_7')
    | ~ v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_459,c_66])).

tff(c_479,plain,(
    ~ r2_hidden('#skF_6',k1_relat_1('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_134,c_164,c_74,c_470])).

tff(c_532,plain,(
    '#skF_1'('#skF_8') = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_490])).

tff(c_26,plain,(
    ! [A_23] :
      ( k1_xboole_0 = A_23
      | r2_hidden(k4_tarski('#skF_1'(A_23),'#skF_2'(A_23)),A_23)
      | ~ v1_relat_1(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_296,plain,(
    ! [A_140,C_141,B_142] :
      ( r2_hidden(A_140,k1_relat_1(C_141))
      | ~ r2_hidden(k4_tarski(A_140,B_142),C_141)
      | ~ v1_funct_1(C_141)
      | ~ v1_relat_1(C_141) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_303,plain,(
    ! [A_23] :
      ( r2_hidden('#skF_1'(A_23),k1_relat_1(A_23))
      | ~ v1_funct_1(A_23)
      | k1_xboole_0 = A_23
      | ~ v1_relat_1(A_23) ) ),
    inference(resolution,[status(thm)],[c_26,c_296])).

tff(c_546,plain,
    ( r2_hidden('#skF_6',k1_relat_1('#skF_8'))
    | ~ v1_funct_1('#skF_8')
    | k1_xboole_0 = '#skF_8'
    | ~ v1_relat_1('#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_532,c_303])).

tff(c_565,plain,
    ( r2_hidden('#skF_6',k1_relat_1('#skF_8'))
    | k1_xboole_0 = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_134,c_74,c_546])).

tff(c_567,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_533,c_479,c_565])).

tff(c_569,plain,(
    v1_funct_1(k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_393])).

tff(c_570,plain,(
    ! [A_180,A_181] :
      ( m1_subset_1(k4_tarski(A_180,k1_funct_1(k1_xboole_0,A_180)),A_181)
      | ~ r2_hidden(A_180,k1_relat_1(k1_xboole_0)) ) ),
    inference(splitRight,[status(thm)],[c_393])).

tff(c_168,plain,(
    ! [C_111,A_112,B_113] :
      ( r2_hidden(C_111,A_112)
      | ~ r2_hidden(C_111,B_113)
      | ~ m1_subset_1(B_113,k1_zfmisc_1(A_112)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_186,plain,(
    ! [A_120,A_121] :
      ( r2_hidden('#skF_5'(A_120),A_121)
      | ~ m1_subset_1(A_120,k1_zfmisc_1(A_121))
      | k1_xboole_0 = A_120 ) ),
    inference(resolution,[status(thm)],[c_52,c_168])).

tff(c_36,plain,(
    ! [B_34,A_33] :
      ( ~ r1_tarski(B_34,A_33)
      | ~ r2_hidden(A_33,B_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_230,plain,(
    ! [A_125,A_126] :
      ( ~ r1_tarski(A_125,'#skF_5'(A_126))
      | ~ m1_subset_1(A_126,k1_zfmisc_1(A_125))
      | k1_xboole_0 = A_126 ) ),
    inference(resolution,[status(thm)],[c_186,c_36])).

tff(c_235,plain,(
    ! [A_126] :
      ( ~ m1_subset_1(A_126,k1_zfmisc_1(k1_xboole_0))
      | k1_xboole_0 = A_126 ) ),
    inference(resolution,[status(thm)],[c_4,c_230])).

tff(c_640,plain,(
    ! [A_186] :
      ( k4_tarski(A_186,k1_funct_1(k1_xboole_0,A_186)) = k1_xboole_0
      | ~ r2_hidden(A_186,k1_relat_1(k1_xboole_0)) ) ),
    inference(resolution,[status(thm)],[c_570,c_235])).

tff(c_663,plain,
    ( k4_tarski('#skF_5'(k1_relat_1(k1_xboole_0)),k1_funct_1(k1_xboole_0,'#skF_5'(k1_relat_1(k1_xboole_0)))) = k1_xboole_0
    | k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_52,c_640])).

tff(c_681,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_663])).

tff(c_608,plain,(
    ! [A_180] :
      ( k4_tarski(A_180,k1_funct_1(k1_xboole_0,A_180)) = k1_xboole_0
      | ~ r2_hidden(A_180,k1_relat_1(k1_xboole_0)) ) ),
    inference(resolution,[status(thm)],[c_570,c_235])).

tff(c_703,plain,(
    ! [A_193] :
      ( k4_tarski(A_193,k1_funct_1(k1_xboole_0,A_193)) = k1_xboole_0
      | ~ r2_hidden(A_193,k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_681,c_608])).

tff(c_30,plain,(
    ! [A_30,C_32] :
      ( r2_hidden(k4_tarski(A_30,k1_funct_1(C_32,A_30)),C_32)
      | ~ r2_hidden(A_30,k1_relat_1(C_32))
      | ~ v1_funct_1(C_32)
      | ~ v1_relat_1(C_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_709,plain,(
    ! [A_193] :
      ( r2_hidden(k1_xboole_0,k1_xboole_0)
      | ~ r2_hidden(A_193,k1_relat_1(k1_xboole_0))
      | ~ v1_funct_1(k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0)
      | ~ r2_hidden(A_193,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_703,c_30])).

tff(c_737,plain,(
    ! [A_193] :
      ( r2_hidden(k1_xboole_0,k1_xboole_0)
      | ~ r2_hidden(A_193,k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_135,c_569,c_681,c_709])).

tff(c_742,plain,(
    ! [A_193] : ~ r2_hidden(A_193,k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_737])).

tff(c_1004,plain,(
    ! [D_233,B_235,A_234] :
      ( ~ r2_hidden(D_233,B_235)
      | k1_relset_1(B_235,A_234,k1_xboole_0) != B_235
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(B_235,A_234))) ) ),
    inference(resolution,[status(thm)],[c_989,c_742])).

tff(c_1036,plain,(
    ! [D_237,B_238,A_239] :
      ( ~ r2_hidden(D_237,B_238)
      | k1_relset_1(B_238,A_239,k1_xboole_0) != B_238 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_1004])).

tff(c_1066,plain,(
    ! [A_54,A_239] :
      ( k1_relset_1(A_54,A_239,k1_xboole_0) != A_54
      | k1_xboole_0 = A_54 ) ),
    inference(resolution,[status(thm)],[c_52,c_1036])).

tff(c_1403,plain,(
    ! [A_295,A_296] :
      ( k1_relset_1(A_295,A_296,'#skF_8') != A_295
      | A_295 = '#skF_8' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1197,c_1197,c_1066])).

tff(c_1409,plain,(
    k1_tarski('#skF_6') = '#skF_8' ),
    inference(superposition,[status(thm),theory(equality)],[c_807,c_1403])).

tff(c_1415,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1246,c_1409])).

tff(c_1417,plain,(
    k1_xboole_0 != '#skF_8' ),
    inference(splitRight,[status(thm)],[c_1192])).

tff(c_743,plain,(
    ! [B_194,C_195,A_196] :
      ( r2_hidden(k1_funct_1(B_194,C_195),A_196)
      | ~ r2_hidden(C_195,k1_relat_1(B_194))
      | ~ v1_funct_1(B_194)
      | ~ v5_relat_1(B_194,A_196)
      | ~ v1_relat_1(B_194) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_754,plain,
    ( ~ r2_hidden('#skF_6',k1_relat_1('#skF_8'))
    | ~ v1_funct_1('#skF_8')
    | ~ v5_relat_1('#skF_8','#skF_7')
    | ~ v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_743,c_66])).

tff(c_763,plain,(
    ~ r2_hidden('#skF_6',k1_relat_1('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_134,c_164,c_74,c_754])).

tff(c_1416,plain,(
    '#skF_1'('#skF_8') = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_1192])).

tff(c_1430,plain,
    ( r2_hidden('#skF_6',k1_relat_1('#skF_8'))
    | ~ v1_funct_1('#skF_8')
    | k1_xboole_0 = '#skF_8'
    | ~ v1_relat_1('#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_1416,c_303])).

tff(c_1449,plain,
    ( r2_hidden('#skF_6',k1_relat_1('#skF_8'))
    | k1_xboole_0 = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_134,c_74,c_1430])).

tff(c_1451,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1417,c_763,c_1449])).

tff(c_1452,plain,(
    r2_hidden(k1_xboole_0,k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_737])).

tff(c_1459,plain,(
    ~ r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_1452,c_36])).

tff(c_1467,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_1459])).

tff(c_1469,plain,(
    k1_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_663])).

tff(c_1468,plain,(
    k4_tarski('#skF_5'(k1_relat_1(k1_xboole_0)),k1_funct_1(k1_xboole_0,'#skF_5'(k1_relat_1(k1_xboole_0)))) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_663])).

tff(c_568,plain,(
    ! [A_158,A_19] :
      ( m1_subset_1(k4_tarski(A_158,k1_funct_1(k1_xboole_0,A_158)),A_19)
      | ~ r2_hidden(A_158,k1_relat_1(k1_xboole_0)) ) ),
    inference(splitRight,[status(thm)],[c_393])).

tff(c_1482,plain,(
    ! [A_19] :
      ( m1_subset_1(k1_xboole_0,A_19)
      | ~ r2_hidden('#skF_5'(k1_relat_1(k1_xboole_0)),k1_relat_1(k1_xboole_0)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1468,c_568])).

tff(c_1512,plain,(
    ~ r2_hidden('#skF_5'(k1_relat_1(k1_xboole_0)),k1_relat_1(k1_xboole_0)) ),
    inference(splitLeft,[status(thm)],[c_1482])).

tff(c_1543,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_52,c_1512])).

tff(c_1550,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1469,c_1543])).

tff(c_1552,plain,(
    r2_hidden('#skF_5'(k1_relat_1(k1_xboole_0)),k1_relat_1(k1_xboole_0)) ),
    inference(splitRight,[status(thm)],[c_1482])).

tff(c_1485,plain,
    ( r2_hidden(k1_xboole_0,k1_xboole_0)
    | ~ r2_hidden('#skF_5'(k1_relat_1(k1_xboole_0)),k1_relat_1(k1_xboole_0))
    | ~ v1_funct_1(k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_1468,c_30])).

tff(c_1510,plain,
    ( r2_hidden(k1_xboole_0,k1_xboole_0)
    | ~ r2_hidden('#skF_5'(k1_relat_1(k1_xboole_0)),k1_relat_1(k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_135,c_569,c_1485])).

tff(c_1640,plain,(
    r2_hidden(k1_xboole_0,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1552,c_1510])).

tff(c_1647,plain,(
    ~ r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_1640,c_36])).

tff(c_1656,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_1647])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:09:12 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.87/1.64  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.87/1.65  
% 3.87/1.65  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.87/1.65  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_enumset1 > k1_relset_1 > k1_enumset1 > k4_tarski > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_1 > #skF_7 > #skF_6 > #skF_4 > #skF_8 > #skF_3
% 3.87/1.65  
% 3.87/1.65  %Foreground sorts:
% 3.87/1.65  
% 3.87/1.65  
% 3.87/1.65  %Background operators:
% 3.87/1.65  
% 3.87/1.65  
% 3.87/1.65  %Foreground operators:
% 3.87/1.65  tff('#skF_5', type, '#skF_5': $i > $i).
% 3.87/1.65  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.87/1.65  tff('#skF_2', type, '#skF_2': $i > $i).
% 3.87/1.65  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.87/1.65  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.87/1.65  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.87/1.65  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 3.87/1.65  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.87/1.65  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.87/1.65  tff('#skF_7', type, '#skF_7': $i).
% 3.87/1.65  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.87/1.65  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.87/1.65  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.87/1.65  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.87/1.65  tff('#skF_6', type, '#skF_6': $i).
% 3.87/1.65  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.87/1.65  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.87/1.65  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.87/1.65  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.87/1.65  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.87/1.65  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.87/1.65  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i) > $i).
% 3.87/1.65  tff('#skF_8', type, '#skF_8': $i).
% 3.87/1.65  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.87/1.65  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.87/1.65  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.87/1.65  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 3.87/1.65  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.87/1.65  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.87/1.65  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.87/1.65  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.87/1.65  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.87/1.65  
% 3.87/1.67  tff(f_29, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 3.87/1.67  tff(f_166, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, k1_tarski(A), B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A), B)))) => (~(B = k1_xboole_0) => r2_hidden(k1_funct_1(C, A), B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t61_funct_2)).
% 3.87/1.67  tff(f_97, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.87/1.67  tff(f_67, axiom, (![A]: (v1_relat_1(A) => ((![B, C]: ~r2_hidden(k4_tarski(B, C), A)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t56_relat_1)).
% 3.87/1.67  tff(f_51, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_subset_1)).
% 3.87/1.67  tff(f_41, axiom, (![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(k1_tarski(C), D)) <=> ((A = C) & r2_hidden(B, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t128_zfmisc_1)).
% 3.87/1.67  tff(f_27, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 3.87/1.67  tff(f_44, axiom, (![A, B]: ~(k2_xboole_0(k1_tarski(A), B) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_zfmisc_1)).
% 3.87/1.67  tff(f_154, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 3.87/1.67  tff(f_136, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~(r2_hidden(B, A) & (![C, D, E, F, G]: (((((r2_hidden(C, D) & r2_hidden(D, E)) & r2_hidden(E, F)) & r2_hidden(F, G)) & r2_hidden(G, B)) => r1_xboole_0(C, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_mcart_1)).
% 3.87/1.67  tff(f_53, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 3.87/1.67  tff(f_115, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => ((![D]: ~(r2_hidden(D, B) & (![E]: ~r2_hidden(k4_tarski(D, E), C)))) <=> (k1_relset_1(B, A, C) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t22_relset_1)).
% 3.87/1.67  tff(f_88, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(k4_tarski(A, B), C) <=> (r2_hidden(A, k1_relat_1(C)) & (B = k1_funct_1(C, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_funct_1)).
% 3.87/1.67  tff(f_59, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset)).
% 3.87/1.67  tff(f_103, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.87/1.67  tff(f_78, axiom, (![A, B]: (((v1_relat_1(B) & v5_relat_1(B, A)) & v1_funct_1(B)) => (![C]: (r2_hidden(C, k1_relat_1(B)) => r2_hidden(k1_funct_1(B, C), A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t172_funct_1)).
% 3.87/1.67  tff(f_93, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 3.87/1.67  tff(c_4, plain, (![A_2]: (r1_tarski(k1_xboole_0, A_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.87/1.67  tff(c_70, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_6'), '#skF_7')))), inference(cnfTransformation, [status(thm)], [f_166])).
% 3.87/1.67  tff(c_126, plain, (![C_93, A_94, B_95]: (v1_relat_1(C_93) | ~m1_subset_1(C_93, k1_zfmisc_1(k2_zfmisc_1(A_94, B_95))))), inference(cnfTransformation, [status(thm)], [f_97])).
% 3.87/1.67  tff(c_134, plain, (v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_70, c_126])).
% 3.87/1.67  tff(c_261, plain, (![A_135]: (k1_xboole_0=A_135 | r2_hidden(k4_tarski('#skF_1'(A_135), '#skF_2'(A_135)), A_135) | ~v1_relat_1(A_135))), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.87/1.67  tff(c_20, plain, (![C_18, A_15, B_16]: (r2_hidden(C_18, A_15) | ~r2_hidden(C_18, B_16) | ~m1_subset_1(B_16, k1_zfmisc_1(A_15)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.87/1.67  tff(c_1139, plain, (![A_266, A_267]: (r2_hidden(k4_tarski('#skF_1'(A_266), '#skF_2'(A_266)), A_267) | ~m1_subset_1(A_266, k1_zfmisc_1(A_267)) | k1_xboole_0=A_266 | ~v1_relat_1(A_266))), inference(resolution, [status(thm)], [c_261, c_20])).
% 3.87/1.67  tff(c_16, plain, (![C_11, A_9, B_10, D_12]: (C_11=A_9 | ~r2_hidden(k4_tarski(A_9, B_10), k2_zfmisc_1(k1_tarski(C_11), D_12)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.87/1.67  tff(c_1182, plain, (![C_268, A_269, D_270]: (C_268='#skF_1'(A_269) | ~m1_subset_1(A_269, k1_zfmisc_1(k2_zfmisc_1(k1_tarski(C_268), D_270))) | k1_xboole_0=A_269 | ~v1_relat_1(A_269))), inference(resolution, [status(thm)], [c_1139, c_16])).
% 3.87/1.67  tff(c_1185, plain, ('#skF_1'('#skF_8')='#skF_6' | k1_xboole_0='#skF_8' | ~v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_70, c_1182])).
% 3.87/1.67  tff(c_1192, plain, ('#skF_1'('#skF_8')='#skF_6' | k1_xboole_0='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_134, c_1185])).
% 3.87/1.67  tff(c_1197, plain, (k1_xboole_0='#skF_8'), inference(splitLeft, [status(thm)], [c_1192])).
% 3.87/1.67  tff(c_2, plain, (![A_1]: (k2_xboole_0(A_1, k1_xboole_0)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.87/1.67  tff(c_97, plain, (![A_83, B_84]: (k2_xboole_0(k1_tarski(A_83), B_84)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.87/1.67  tff(c_101, plain, (![A_83]: (k1_tarski(A_83)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2, c_97])).
% 3.87/1.67  tff(c_1246, plain, (![A_83]: (k1_tarski(A_83)!='#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_1197, c_101])).
% 3.87/1.67  tff(c_68, plain, (k1_xboole_0!='#skF_7'), inference(cnfTransformation, [status(thm)], [f_166])).
% 3.87/1.67  tff(c_72, plain, (v1_funct_2('#skF_8', k1_tarski('#skF_6'), '#skF_7')), inference(cnfTransformation, [status(thm)], [f_166])).
% 3.87/1.67  tff(c_796, plain, (![B_198, A_199, C_200]: (k1_xboole_0=B_198 | k1_relset_1(A_199, B_198, C_200)=A_199 | ~v1_funct_2(C_200, A_199, B_198) | ~m1_subset_1(C_200, k1_zfmisc_1(k2_zfmisc_1(A_199, B_198))))), inference(cnfTransformation, [status(thm)], [f_154])).
% 3.87/1.67  tff(c_799, plain, (k1_xboole_0='#skF_7' | k1_relset_1(k1_tarski('#skF_6'), '#skF_7', '#skF_8')=k1_tarski('#skF_6') | ~v1_funct_2('#skF_8', k1_tarski('#skF_6'), '#skF_7')), inference(resolution, [status(thm)], [c_70, c_796])).
% 3.87/1.67  tff(c_806, plain, (k1_xboole_0='#skF_7' | k1_relset_1(k1_tarski('#skF_6'), '#skF_7', '#skF_8')=k1_tarski('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_799])).
% 3.87/1.67  tff(c_807, plain, (k1_relset_1(k1_tarski('#skF_6'), '#skF_7', '#skF_8')=k1_tarski('#skF_6')), inference(negUnitSimplification, [status(thm)], [c_68, c_806])).
% 3.87/1.67  tff(c_52, plain, (![A_54]: (r2_hidden('#skF_5'(A_54), A_54) | k1_xboole_0=A_54)), inference(cnfTransformation, [status(thm)], [f_136])).
% 3.87/1.67  tff(c_22, plain, (![A_19]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_19)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.87/1.67  tff(c_989, plain, (![D_233, A_234, B_235, C_236]: (r2_hidden(k4_tarski(D_233, '#skF_4'(A_234, B_235, C_236, D_233)), C_236) | ~r2_hidden(D_233, B_235) | k1_relset_1(B_235, A_234, C_236)!=B_235 | ~m1_subset_1(C_236, k1_zfmisc_1(k2_zfmisc_1(B_235, A_234))))), inference(cnfTransformation, [status(thm)], [f_115])).
% 3.87/1.67  tff(c_135, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_22, c_126])).
% 3.87/1.67  tff(c_74, plain, (v1_funct_1('#skF_8')), inference(cnfTransformation, [status(thm)], [f_166])).
% 3.87/1.67  tff(c_429, plain, (![A_172, A_173]: (r2_hidden(k4_tarski('#skF_1'(A_172), '#skF_2'(A_172)), A_173) | ~m1_subset_1(A_172, k1_zfmisc_1(A_173)) | k1_xboole_0=A_172 | ~v1_relat_1(A_172))), inference(resolution, [status(thm)], [c_261, c_20])).
% 3.87/1.67  tff(c_480, plain, (![C_177, A_178, D_179]: (C_177='#skF_1'(A_178) | ~m1_subset_1(A_178, k1_zfmisc_1(k2_zfmisc_1(k1_tarski(C_177), D_179))) | k1_xboole_0=A_178 | ~v1_relat_1(A_178))), inference(resolution, [status(thm)], [c_429, c_16])).
% 3.87/1.67  tff(c_483, plain, ('#skF_1'('#skF_8')='#skF_6' | k1_xboole_0='#skF_8' | ~v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_70, c_480])).
% 3.87/1.67  tff(c_490, plain, ('#skF_1'('#skF_8')='#skF_6' | k1_xboole_0='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_134, c_483])).
% 3.87/1.67  tff(c_495, plain, (k1_xboole_0='#skF_8'), inference(splitLeft, [status(thm)], [c_490])).
% 3.87/1.67  tff(c_361, plain, (![A_158, C_159]: (r2_hidden(k4_tarski(A_158, k1_funct_1(C_159, A_158)), C_159) | ~r2_hidden(A_158, k1_relat_1(C_159)) | ~v1_funct_1(C_159) | ~v1_relat_1(C_159))), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.87/1.67  tff(c_172, plain, (![A_114, C_115, B_116]: (m1_subset_1(A_114, C_115) | ~m1_subset_1(B_116, k1_zfmisc_1(C_115)) | ~r2_hidden(A_114, B_116))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.87/1.67  tff(c_178, plain, (![A_114, A_19]: (m1_subset_1(A_114, A_19) | ~r2_hidden(A_114, k1_xboole_0))), inference(resolution, [status(thm)], [c_22, c_172])).
% 3.87/1.67  tff(c_374, plain, (![A_158, A_19]: (m1_subset_1(k4_tarski(A_158, k1_funct_1(k1_xboole_0, A_158)), A_19) | ~r2_hidden(A_158, k1_relat_1(k1_xboole_0)) | ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_361, c_178])).
% 3.87/1.67  tff(c_393, plain, (![A_158, A_19]: (m1_subset_1(k4_tarski(A_158, k1_funct_1(k1_xboole_0, A_158)), A_19) | ~r2_hidden(A_158, k1_relat_1(k1_xboole_0)) | ~v1_funct_1(k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_135, c_374])).
% 3.87/1.67  tff(c_404, plain, (~v1_funct_1(k1_xboole_0)), inference(splitLeft, [status(thm)], [c_393])).
% 3.87/1.67  tff(c_501, plain, (~v1_funct_1('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_495, c_404])).
% 3.87/1.67  tff(c_531, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_74, c_501])).
% 3.87/1.67  tff(c_533, plain, (k1_xboole_0!='#skF_8'), inference(splitRight, [status(thm)], [c_490])).
% 3.87/1.67  tff(c_156, plain, (![C_103, B_104, A_105]: (v5_relat_1(C_103, B_104) | ~m1_subset_1(C_103, k1_zfmisc_1(k2_zfmisc_1(A_105, B_104))))), inference(cnfTransformation, [status(thm)], [f_103])).
% 3.87/1.67  tff(c_164, plain, (v5_relat_1('#skF_8', '#skF_7')), inference(resolution, [status(thm)], [c_70, c_156])).
% 3.87/1.67  tff(c_459, plain, (![B_174, C_175, A_176]: (r2_hidden(k1_funct_1(B_174, C_175), A_176) | ~r2_hidden(C_175, k1_relat_1(B_174)) | ~v1_funct_1(B_174) | ~v5_relat_1(B_174, A_176) | ~v1_relat_1(B_174))), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.87/1.67  tff(c_66, plain, (~r2_hidden(k1_funct_1('#skF_8', '#skF_6'), '#skF_7')), inference(cnfTransformation, [status(thm)], [f_166])).
% 3.87/1.67  tff(c_470, plain, (~r2_hidden('#skF_6', k1_relat_1('#skF_8')) | ~v1_funct_1('#skF_8') | ~v5_relat_1('#skF_8', '#skF_7') | ~v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_459, c_66])).
% 3.87/1.67  tff(c_479, plain, (~r2_hidden('#skF_6', k1_relat_1('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_134, c_164, c_74, c_470])).
% 3.87/1.67  tff(c_532, plain, ('#skF_1'('#skF_8')='#skF_6'), inference(splitRight, [status(thm)], [c_490])).
% 3.87/1.67  tff(c_26, plain, (![A_23]: (k1_xboole_0=A_23 | r2_hidden(k4_tarski('#skF_1'(A_23), '#skF_2'(A_23)), A_23) | ~v1_relat_1(A_23))), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.87/1.67  tff(c_296, plain, (![A_140, C_141, B_142]: (r2_hidden(A_140, k1_relat_1(C_141)) | ~r2_hidden(k4_tarski(A_140, B_142), C_141) | ~v1_funct_1(C_141) | ~v1_relat_1(C_141))), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.87/1.67  tff(c_303, plain, (![A_23]: (r2_hidden('#skF_1'(A_23), k1_relat_1(A_23)) | ~v1_funct_1(A_23) | k1_xboole_0=A_23 | ~v1_relat_1(A_23))), inference(resolution, [status(thm)], [c_26, c_296])).
% 3.87/1.67  tff(c_546, plain, (r2_hidden('#skF_6', k1_relat_1('#skF_8')) | ~v1_funct_1('#skF_8') | k1_xboole_0='#skF_8' | ~v1_relat_1('#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_532, c_303])).
% 3.87/1.67  tff(c_565, plain, (r2_hidden('#skF_6', k1_relat_1('#skF_8')) | k1_xboole_0='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_134, c_74, c_546])).
% 3.87/1.67  tff(c_567, plain, $false, inference(negUnitSimplification, [status(thm)], [c_533, c_479, c_565])).
% 3.87/1.67  tff(c_569, plain, (v1_funct_1(k1_xboole_0)), inference(splitRight, [status(thm)], [c_393])).
% 3.87/1.67  tff(c_570, plain, (![A_180, A_181]: (m1_subset_1(k4_tarski(A_180, k1_funct_1(k1_xboole_0, A_180)), A_181) | ~r2_hidden(A_180, k1_relat_1(k1_xboole_0)))), inference(splitRight, [status(thm)], [c_393])).
% 3.87/1.67  tff(c_168, plain, (![C_111, A_112, B_113]: (r2_hidden(C_111, A_112) | ~r2_hidden(C_111, B_113) | ~m1_subset_1(B_113, k1_zfmisc_1(A_112)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.87/1.67  tff(c_186, plain, (![A_120, A_121]: (r2_hidden('#skF_5'(A_120), A_121) | ~m1_subset_1(A_120, k1_zfmisc_1(A_121)) | k1_xboole_0=A_120)), inference(resolution, [status(thm)], [c_52, c_168])).
% 3.87/1.67  tff(c_36, plain, (![B_34, A_33]: (~r1_tarski(B_34, A_33) | ~r2_hidden(A_33, B_34))), inference(cnfTransformation, [status(thm)], [f_93])).
% 3.87/1.67  tff(c_230, plain, (![A_125, A_126]: (~r1_tarski(A_125, '#skF_5'(A_126)) | ~m1_subset_1(A_126, k1_zfmisc_1(A_125)) | k1_xboole_0=A_126)), inference(resolution, [status(thm)], [c_186, c_36])).
% 3.87/1.67  tff(c_235, plain, (![A_126]: (~m1_subset_1(A_126, k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0=A_126)), inference(resolution, [status(thm)], [c_4, c_230])).
% 3.87/1.67  tff(c_640, plain, (![A_186]: (k4_tarski(A_186, k1_funct_1(k1_xboole_0, A_186))=k1_xboole_0 | ~r2_hidden(A_186, k1_relat_1(k1_xboole_0)))), inference(resolution, [status(thm)], [c_570, c_235])).
% 3.87/1.67  tff(c_663, plain, (k4_tarski('#skF_5'(k1_relat_1(k1_xboole_0)), k1_funct_1(k1_xboole_0, '#skF_5'(k1_relat_1(k1_xboole_0))))=k1_xboole_0 | k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_52, c_640])).
% 3.87/1.67  tff(c_681, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(splitLeft, [status(thm)], [c_663])).
% 3.87/1.67  tff(c_608, plain, (![A_180]: (k4_tarski(A_180, k1_funct_1(k1_xboole_0, A_180))=k1_xboole_0 | ~r2_hidden(A_180, k1_relat_1(k1_xboole_0)))), inference(resolution, [status(thm)], [c_570, c_235])).
% 3.87/1.67  tff(c_703, plain, (![A_193]: (k4_tarski(A_193, k1_funct_1(k1_xboole_0, A_193))=k1_xboole_0 | ~r2_hidden(A_193, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_681, c_608])).
% 3.87/1.67  tff(c_30, plain, (![A_30, C_32]: (r2_hidden(k4_tarski(A_30, k1_funct_1(C_32, A_30)), C_32) | ~r2_hidden(A_30, k1_relat_1(C_32)) | ~v1_funct_1(C_32) | ~v1_relat_1(C_32))), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.87/1.67  tff(c_709, plain, (![A_193]: (r2_hidden(k1_xboole_0, k1_xboole_0) | ~r2_hidden(A_193, k1_relat_1(k1_xboole_0)) | ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0) | ~r2_hidden(A_193, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_703, c_30])).
% 3.87/1.67  tff(c_737, plain, (![A_193]: (r2_hidden(k1_xboole_0, k1_xboole_0) | ~r2_hidden(A_193, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_135, c_569, c_681, c_709])).
% 3.87/1.67  tff(c_742, plain, (![A_193]: (~r2_hidden(A_193, k1_xboole_0))), inference(splitLeft, [status(thm)], [c_737])).
% 3.87/1.67  tff(c_1004, plain, (![D_233, B_235, A_234]: (~r2_hidden(D_233, B_235) | k1_relset_1(B_235, A_234, k1_xboole_0)!=B_235 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k2_zfmisc_1(B_235, A_234))))), inference(resolution, [status(thm)], [c_989, c_742])).
% 3.87/1.67  tff(c_1036, plain, (![D_237, B_238, A_239]: (~r2_hidden(D_237, B_238) | k1_relset_1(B_238, A_239, k1_xboole_0)!=B_238)), inference(demodulation, [status(thm), theory('equality')], [c_22, c_1004])).
% 3.87/1.67  tff(c_1066, plain, (![A_54, A_239]: (k1_relset_1(A_54, A_239, k1_xboole_0)!=A_54 | k1_xboole_0=A_54)), inference(resolution, [status(thm)], [c_52, c_1036])).
% 3.87/1.67  tff(c_1403, plain, (![A_295, A_296]: (k1_relset_1(A_295, A_296, '#skF_8')!=A_295 | A_295='#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_1197, c_1197, c_1066])).
% 3.87/1.67  tff(c_1409, plain, (k1_tarski('#skF_6')='#skF_8'), inference(superposition, [status(thm), theory('equality')], [c_807, c_1403])).
% 3.87/1.67  tff(c_1415, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1246, c_1409])).
% 3.87/1.67  tff(c_1417, plain, (k1_xboole_0!='#skF_8'), inference(splitRight, [status(thm)], [c_1192])).
% 3.87/1.67  tff(c_743, plain, (![B_194, C_195, A_196]: (r2_hidden(k1_funct_1(B_194, C_195), A_196) | ~r2_hidden(C_195, k1_relat_1(B_194)) | ~v1_funct_1(B_194) | ~v5_relat_1(B_194, A_196) | ~v1_relat_1(B_194))), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.87/1.67  tff(c_754, plain, (~r2_hidden('#skF_6', k1_relat_1('#skF_8')) | ~v1_funct_1('#skF_8') | ~v5_relat_1('#skF_8', '#skF_7') | ~v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_743, c_66])).
% 3.87/1.67  tff(c_763, plain, (~r2_hidden('#skF_6', k1_relat_1('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_134, c_164, c_74, c_754])).
% 3.87/1.67  tff(c_1416, plain, ('#skF_1'('#skF_8')='#skF_6'), inference(splitRight, [status(thm)], [c_1192])).
% 3.87/1.67  tff(c_1430, plain, (r2_hidden('#skF_6', k1_relat_1('#skF_8')) | ~v1_funct_1('#skF_8') | k1_xboole_0='#skF_8' | ~v1_relat_1('#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_1416, c_303])).
% 3.87/1.67  tff(c_1449, plain, (r2_hidden('#skF_6', k1_relat_1('#skF_8')) | k1_xboole_0='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_134, c_74, c_1430])).
% 3.87/1.67  tff(c_1451, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1417, c_763, c_1449])).
% 3.87/1.67  tff(c_1452, plain, (r2_hidden(k1_xboole_0, k1_xboole_0)), inference(splitRight, [status(thm)], [c_737])).
% 3.87/1.67  tff(c_1459, plain, (~r1_tarski(k1_xboole_0, k1_xboole_0)), inference(resolution, [status(thm)], [c_1452, c_36])).
% 3.87/1.67  tff(c_1467, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4, c_1459])).
% 3.87/1.67  tff(c_1469, plain, (k1_relat_1(k1_xboole_0)!=k1_xboole_0), inference(splitRight, [status(thm)], [c_663])).
% 3.87/1.67  tff(c_1468, plain, (k4_tarski('#skF_5'(k1_relat_1(k1_xboole_0)), k1_funct_1(k1_xboole_0, '#skF_5'(k1_relat_1(k1_xboole_0))))=k1_xboole_0), inference(splitRight, [status(thm)], [c_663])).
% 3.87/1.67  tff(c_568, plain, (![A_158, A_19]: (m1_subset_1(k4_tarski(A_158, k1_funct_1(k1_xboole_0, A_158)), A_19) | ~r2_hidden(A_158, k1_relat_1(k1_xboole_0)))), inference(splitRight, [status(thm)], [c_393])).
% 3.87/1.67  tff(c_1482, plain, (![A_19]: (m1_subset_1(k1_xboole_0, A_19) | ~r2_hidden('#skF_5'(k1_relat_1(k1_xboole_0)), k1_relat_1(k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_1468, c_568])).
% 3.87/1.67  tff(c_1512, plain, (~r2_hidden('#skF_5'(k1_relat_1(k1_xboole_0)), k1_relat_1(k1_xboole_0))), inference(splitLeft, [status(thm)], [c_1482])).
% 3.87/1.67  tff(c_1543, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_52, c_1512])).
% 3.87/1.67  tff(c_1550, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1469, c_1543])).
% 3.87/1.67  tff(c_1552, plain, (r2_hidden('#skF_5'(k1_relat_1(k1_xboole_0)), k1_relat_1(k1_xboole_0))), inference(splitRight, [status(thm)], [c_1482])).
% 3.87/1.67  tff(c_1485, plain, (r2_hidden(k1_xboole_0, k1_xboole_0) | ~r2_hidden('#skF_5'(k1_relat_1(k1_xboole_0)), k1_relat_1(k1_xboole_0)) | ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_1468, c_30])).
% 3.87/1.67  tff(c_1510, plain, (r2_hidden(k1_xboole_0, k1_xboole_0) | ~r2_hidden('#skF_5'(k1_relat_1(k1_xboole_0)), k1_relat_1(k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_135, c_569, c_1485])).
% 3.87/1.67  tff(c_1640, plain, (r2_hidden(k1_xboole_0, k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_1552, c_1510])).
% 3.87/1.67  tff(c_1647, plain, (~r1_tarski(k1_xboole_0, k1_xboole_0)), inference(resolution, [status(thm)], [c_1640, c_36])).
% 3.87/1.67  tff(c_1656, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4, c_1647])).
% 3.87/1.67  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.87/1.67  
% 3.87/1.67  Inference rules
% 3.87/1.67  ----------------------
% 3.87/1.67  #Ref     : 0
% 3.87/1.67  #Sup     : 303
% 3.87/1.67  #Fact    : 0
% 3.87/1.67  #Define  : 0
% 3.87/1.67  #Split   : 7
% 3.87/1.67  #Chain   : 0
% 3.87/1.67  #Close   : 0
% 3.87/1.67  
% 3.87/1.67  Ordering : KBO
% 3.87/1.67  
% 3.87/1.67  Simplification rules
% 3.87/1.67  ----------------------
% 3.87/1.67  #Subsume      : 53
% 3.87/1.67  #Demod        : 272
% 3.87/1.67  #Tautology    : 96
% 3.87/1.67  #SimpNegUnit  : 13
% 3.87/1.67  #BackRed      : 94
% 3.87/1.67  
% 3.87/1.67  #Partial instantiations: 0
% 3.87/1.67  #Strategies tried      : 1
% 3.87/1.67  
% 3.87/1.67  Timing (in seconds)
% 3.87/1.67  ----------------------
% 3.87/1.68  Preprocessing        : 0.36
% 3.87/1.68  Parsing              : 0.20
% 3.87/1.68  CNF conversion       : 0.03
% 3.87/1.68  Main loop            : 0.52
% 3.87/1.68  Inferencing          : 0.18
% 3.87/1.68  Reduction            : 0.16
% 3.87/1.68  Demodulation         : 0.10
% 3.87/1.68  BG Simplification    : 0.03
% 3.87/1.68  Subsumption          : 0.11
% 3.87/1.68  Abstraction          : 0.03
% 3.87/1.68  MUC search           : 0.00
% 3.87/1.68  Cooper               : 0.00
% 3.87/1.68  Total                : 0.93
% 3.87/1.68  Index Insertion      : 0.00
% 3.87/1.68  Index Deletion       : 0.00
% 3.87/1.68  Index Matching       : 0.00
% 3.87/1.68  BG Taut test         : 0.00
%------------------------------------------------------------------------------
