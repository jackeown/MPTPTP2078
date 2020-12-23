%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:14:18 EST 2020

% Result     : Theorem 3.70s
% Output     : CNFRefutation 4.04s
% Verified   : 
% Statistics : Number of formulae       :  106 ( 238 expanded)
%              Number of leaves         :   49 ( 101 expanded)
%              Depth                    :   12
%              Number of atoms          :  167 ( 517 expanded)
%              Number of equality atoms :   55 ( 150 expanded)
%              Maximal formula depth    :   17 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_enumset1 > k1_relset_1 > k1_enumset1 > k4_xboole_0 > k4_tarski > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_1 > #skF_7 > #skF_6 > #skF_4 > #skF_8 > #skF_3

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

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

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

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_165,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,k1_tarski(A),B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A),B))) )
       => ( B != k1_xboole_0
         => r2_hidden(k1_funct_1(C,A),B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_2)).

tff(f_96,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_76,axiom,(
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

tff(f_45,axiom,(
    ! [A,B,C,D] :
      ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(k1_tarski(C),D))
    <=> ( A = C
        & r2_hidden(B,D) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t128_zfmisc_1)).

tff(f_27,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_29,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_39,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),B) = k1_xboole_0
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l35_zfmisc_1)).

tff(f_92,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

tff(f_114,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(B,A)))
     => ( ! [D] :
            ~ ( r2_hidden(D,B)
              & ! [E] : ~ r2_hidden(k4_tarski(D,E),C) )
      <=> k1_relset_1(B,A,C) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_relset_1)).

tff(f_135,axiom,(
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

tff(f_54,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_102,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_87,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A)
        & v1_funct_1(B) )
     => ! [C] :
          ( r2_hidden(C,k1_relat_1(B))
         => r2_hidden(k1_funct_1(B,C),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t172_funct_1)).

tff(f_68,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(k4_tarski(A,B),C)
       => ( r2_hidden(A,k1_relat_1(C))
          & r2_hidden(B,k2_relat_1(C)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_relat_1)).

tff(f_153,axiom,(
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

tff(c_70,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_6'),'#skF_7'))) ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_164,plain,(
    ! [C_96,A_97,B_98] :
      ( v1_relat_1(C_96)
      | ~ m1_subset_1(C_96,k1_zfmisc_1(k2_zfmisc_1(A_97,B_98))) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_172,plain,(
    v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_70,c_164])).

tff(c_271,plain,(
    ! [A_134] :
      ( k1_xboole_0 = A_134
      | r2_hidden(k4_tarski('#skF_1'(A_134),'#skF_2'(A_134)),A_134)
      | ~ v1_relat_1(A_134) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_22,plain,(
    ! [C_18,A_15,B_16] :
      ( r2_hidden(C_18,A_15)
      | ~ r2_hidden(C_18,B_16)
      | ~ m1_subset_1(B_16,k1_zfmisc_1(A_15)) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_863,plain,(
    ! [A_227,A_228] :
      ( r2_hidden(k4_tarski('#skF_1'(A_227),'#skF_2'(A_227)),A_228)
      | ~ m1_subset_1(A_227,k1_zfmisc_1(A_228))
      | k1_xboole_0 = A_227
      | ~ v1_relat_1(A_227) ) ),
    inference(resolution,[status(thm)],[c_271,c_22])).

tff(c_20,plain,(
    ! [C_13,A_11,B_12,D_14] :
      ( C_13 = A_11
      | ~ r2_hidden(k4_tarski(A_11,B_12),k2_zfmisc_1(k1_tarski(C_13),D_14)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_916,plain,(
    ! [C_234,A_235,D_236] :
      ( C_234 = '#skF_1'(A_235)
      | ~ m1_subset_1(A_235,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(C_234),D_236)))
      | k1_xboole_0 = A_235
      | ~ v1_relat_1(A_235) ) ),
    inference(resolution,[status(thm)],[c_863,c_20])).

tff(c_919,plain,
    ( '#skF_1'('#skF_8') = '#skF_6'
    | k1_xboole_0 = '#skF_8'
    | ~ v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_70,c_916])).

tff(c_926,plain,
    ( '#skF_1'('#skF_8') = '#skF_6'
    | k1_xboole_0 = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_172,c_919])).

tff(c_931,plain,(
    k1_xboole_0 = '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_926])).

tff(c_2,plain,(
    ! [A_1] : r1_tarski(k1_xboole_0,A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_4,plain,(
    ! [A_2] : k4_xboole_0(A_2,k1_xboole_0) = A_2 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_137,plain,(
    ! [A_92,B_93] :
      ( r2_hidden(A_92,B_93)
      | k4_xboole_0(k1_tarski(A_92),B_93) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_153,plain,(
    ! [A_95] :
      ( r2_hidden(A_95,k1_xboole_0)
      | k1_tarski(A_95) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_137])).

tff(c_36,plain,(
    ! [B_34,A_33] :
      ( ~ r1_tarski(B_34,A_33)
      | ~ r2_hidden(A_33,B_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_159,plain,(
    ! [A_95] :
      ( ~ r1_tarski(k1_xboole_0,A_95)
      | k1_tarski(A_95) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_153,c_36])).

tff(c_163,plain,(
    ! [A_95] : k1_tarski(A_95) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_159])).

tff(c_968,plain,(
    ! [A_95] : k1_tarski(A_95) != '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_931,c_163])).

tff(c_785,plain,(
    ! [A_214,B_215,C_216] :
      ( r2_hidden('#skF_3'(A_214,B_215,C_216),B_215)
      | k1_relset_1(B_215,A_214,C_216) = B_215
      | ~ m1_subset_1(C_216,k1_zfmisc_1(k2_zfmisc_1(B_215,A_214))) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_791,plain,
    ( r2_hidden('#skF_3'('#skF_7',k1_tarski('#skF_6'),'#skF_8'),k1_tarski('#skF_6'))
    | k1_relset_1(k1_tarski('#skF_6'),'#skF_7','#skF_8') = k1_tarski('#skF_6') ),
    inference(resolution,[status(thm)],[c_70,c_785])).

tff(c_825,plain,(
    k1_relset_1(k1_tarski('#skF_6'),'#skF_7','#skF_8') = k1_tarski('#skF_6') ),
    inference(splitLeft,[status(thm)],[c_791])).

tff(c_52,plain,(
    ! [A_54] :
      ( r2_hidden('#skF_5'(A_54),A_54)
      | k1_xboole_0 = A_54 ) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_974,plain,(
    ! [A_54] :
      ( r2_hidden('#skF_5'(A_54),A_54)
      | A_54 = '#skF_8' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_931,c_52])).

tff(c_24,plain,(
    ! [A_19] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_19)) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_975,plain,(
    ! [A_19] : m1_subset_1('#skF_8',k1_zfmisc_1(A_19)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_931,c_24])).

tff(c_1171,plain,(
    ! [D_270,A_271,B_272,C_273] :
      ( r2_hidden(k4_tarski(D_270,'#skF_4'(A_271,B_272,C_273,D_270)),C_273)
      | ~ r2_hidden(D_270,B_272)
      | k1_relset_1(B_272,A_271,C_273) != B_272
      | ~ m1_subset_1(C_273,k1_zfmisc_1(k2_zfmisc_1(B_272,A_271))) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_120,plain,(
    ! [A_90,B_91] :
      ( k4_xboole_0(k1_tarski(A_90),B_91) = k1_xboole_0
      | ~ r2_hidden(A_90,B_91) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_127,plain,(
    ! [A_90] :
      ( k1_tarski(A_90) = k1_xboole_0
      | ~ r2_hidden(A_90,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_120,c_4])).

tff(c_174,plain,(
    ! [A_90] : ~ r2_hidden(A_90,k1_xboole_0) ),
    inference(negUnitSimplification,[status(thm)],[c_163,c_127])).

tff(c_967,plain,(
    ! [A_90] : ~ r2_hidden(A_90,'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_931,c_174])).

tff(c_1182,plain,(
    ! [D_270,B_272,A_271] :
      ( ~ r2_hidden(D_270,B_272)
      | k1_relset_1(B_272,A_271,'#skF_8') != B_272
      | ~ m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1(B_272,A_271))) ) ),
    inference(resolution,[status(thm)],[c_1171,c_967])).

tff(c_1216,plain,(
    ! [D_274,B_275,A_276] :
      ( ~ r2_hidden(D_274,B_275)
      | k1_relset_1(B_275,A_276,'#skF_8') != B_275 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_975,c_1182])).

tff(c_1235,plain,(
    ! [A_277,A_278] :
      ( k1_relset_1(A_277,A_278,'#skF_8') != A_277
      | A_277 = '#skF_8' ) ),
    inference(resolution,[status(thm)],[c_974,c_1216])).

tff(c_1241,plain,(
    k1_tarski('#skF_6') = '#skF_8' ),
    inference(superposition,[status(thm),theory(equality)],[c_825,c_1235])).

tff(c_1247,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_968,c_1241])).

tff(c_1249,plain,(
    k1_xboole_0 != '#skF_8' ),
    inference(splitRight,[status(thm)],[c_926])).

tff(c_192,plain,(
    ! [C_104,B_105,A_106] :
      ( v5_relat_1(C_104,B_105)
      | ~ m1_subset_1(C_104,k1_zfmisc_1(k2_zfmisc_1(A_106,B_105))) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_200,plain,(
    v5_relat_1('#skF_8','#skF_7') ),
    inference(resolution,[status(thm)],[c_70,c_192])).

tff(c_74,plain,(
    v1_funct_1('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_459,plain,(
    ! [B_183,C_184,A_185] :
      ( r2_hidden(k1_funct_1(B_183,C_184),A_185)
      | ~ r2_hidden(C_184,k1_relat_1(B_183))
      | ~ v1_funct_1(B_183)
      | ~ v5_relat_1(B_183,A_185)
      | ~ v1_relat_1(B_183) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_66,plain,(
    ~ r2_hidden(k1_funct_1('#skF_8','#skF_6'),'#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_473,plain,
    ( ~ r2_hidden('#skF_6',k1_relat_1('#skF_8'))
    | ~ v1_funct_1('#skF_8')
    | ~ v5_relat_1('#skF_8','#skF_7')
    | ~ v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_459,c_66])).

tff(c_480,plain,(
    ~ r2_hidden('#skF_6',k1_relat_1('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_172,c_200,c_74,c_473])).

tff(c_1248,plain,(
    '#skF_1'('#skF_8') = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_926])).

tff(c_30,plain,(
    ! [A_23,C_25,B_24] :
      ( r2_hidden(A_23,k1_relat_1(C_25))
      | ~ r2_hidden(k4_tarski(A_23,B_24),C_25)
      | ~ v1_relat_1(C_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_288,plain,(
    ! [A_134] :
      ( r2_hidden('#skF_1'(A_134),k1_relat_1(A_134))
      | k1_xboole_0 = A_134
      | ~ v1_relat_1(A_134) ) ),
    inference(resolution,[status(thm)],[c_271,c_30])).

tff(c_1262,plain,
    ( r2_hidden('#skF_6',k1_relat_1('#skF_8'))
    | k1_xboole_0 = '#skF_8'
    | ~ v1_relat_1('#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_1248,c_288])).

tff(c_1278,plain,
    ( r2_hidden('#skF_6',k1_relat_1('#skF_8'))
    | k1_xboole_0 = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_172,c_1262])).

tff(c_1280,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1249,c_480,c_1278])).

tff(c_1282,plain,(
    k1_relset_1(k1_tarski('#skF_6'),'#skF_7','#skF_8') != k1_tarski('#skF_6') ),
    inference(splitRight,[status(thm)],[c_791])).

tff(c_68,plain,(
    k1_xboole_0 != '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_72,plain,(
    v1_funct_2('#skF_8',k1_tarski('#skF_6'),'#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_1437,plain,(
    ! [B_297,A_298,C_299] :
      ( k1_xboole_0 = B_297
      | k1_relset_1(A_298,B_297,C_299) = A_298
      | ~ v1_funct_2(C_299,A_298,B_297)
      | ~ m1_subset_1(C_299,k1_zfmisc_1(k2_zfmisc_1(A_298,B_297))) ) ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_1440,plain,
    ( k1_xboole_0 = '#skF_7'
    | k1_relset_1(k1_tarski('#skF_6'),'#skF_7','#skF_8') = k1_tarski('#skF_6')
    | ~ v1_funct_2('#skF_8',k1_tarski('#skF_6'),'#skF_7') ),
    inference(resolution,[status(thm)],[c_70,c_1437])).

tff(c_1447,plain,
    ( k1_xboole_0 = '#skF_7'
    | k1_relset_1(k1_tarski('#skF_6'),'#skF_7','#skF_8') = k1_tarski('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_1440])).

tff(c_1449,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1282,c_68,c_1447])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:11:22 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.70/1.64  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.97/1.65  
% 3.97/1.65  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.97/1.65  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_enumset1 > k1_relset_1 > k1_enumset1 > k4_xboole_0 > k4_tarski > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_1 > #skF_7 > #skF_6 > #skF_4 > #skF_8 > #skF_3
% 3.97/1.65  
% 3.97/1.65  %Foreground sorts:
% 3.97/1.65  
% 3.97/1.65  
% 3.97/1.65  %Background operators:
% 3.97/1.65  
% 3.97/1.65  
% 3.97/1.65  %Foreground operators:
% 3.97/1.65  tff('#skF_5', type, '#skF_5': $i > $i).
% 3.97/1.65  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.97/1.65  tff('#skF_2', type, '#skF_2': $i > $i).
% 3.97/1.65  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.97/1.65  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.97/1.65  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.97/1.65  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.97/1.65  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 3.97/1.65  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.97/1.65  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.97/1.65  tff('#skF_7', type, '#skF_7': $i).
% 3.97/1.65  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.97/1.65  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.97/1.65  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.97/1.65  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.97/1.65  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.97/1.65  tff('#skF_6', type, '#skF_6': $i).
% 3.97/1.65  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.97/1.65  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.97/1.65  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.97/1.65  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.97/1.65  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.97/1.65  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.97/1.65  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i) > $i).
% 3.97/1.65  tff('#skF_8', type, '#skF_8': $i).
% 3.97/1.65  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.97/1.65  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.97/1.65  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.97/1.65  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 3.97/1.65  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.97/1.65  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.97/1.65  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.97/1.65  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.97/1.65  
% 4.04/1.67  tff(f_165, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, k1_tarski(A), B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A), B)))) => (~(B = k1_xboole_0) => r2_hidden(k1_funct_1(C, A), B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t61_funct_2)).
% 4.04/1.67  tff(f_96, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 4.04/1.67  tff(f_76, axiom, (![A]: (v1_relat_1(A) => ((![B, C]: ~r2_hidden(k4_tarski(B, C), A)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t56_relat_1)).
% 4.04/1.67  tff(f_52, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_subset_1)).
% 4.04/1.67  tff(f_45, axiom, (![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(k1_tarski(C), D)) <=> ((A = C) & r2_hidden(B, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t128_zfmisc_1)).
% 4.04/1.67  tff(f_27, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 4.04/1.67  tff(f_29, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 4.04/1.67  tff(f_39, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), B) = k1_xboole_0) <=> r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l35_zfmisc_1)).
% 4.04/1.67  tff(f_92, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 4.04/1.67  tff(f_114, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => ((![D]: ~(r2_hidden(D, B) & (![E]: ~r2_hidden(k4_tarski(D, E), C)))) <=> (k1_relset_1(B, A, C) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t22_relset_1)).
% 4.04/1.67  tff(f_135, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~(r2_hidden(B, A) & (![C, D, E, F, G]: (((((r2_hidden(C, D) & r2_hidden(D, E)) & r2_hidden(E, F)) & r2_hidden(F, G)) & r2_hidden(G, B)) => r1_xboole_0(C, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_mcart_1)).
% 4.04/1.67  tff(f_54, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 4.04/1.67  tff(f_102, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 4.04/1.67  tff(f_87, axiom, (![A, B]: (((v1_relat_1(B) & v5_relat_1(B, A)) & v1_funct_1(B)) => (![C]: (r2_hidden(C, k1_relat_1(B)) => r2_hidden(k1_funct_1(B, C), A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t172_funct_1)).
% 4.04/1.67  tff(f_68, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(k4_tarski(A, B), C) => (r2_hidden(A, k1_relat_1(C)) & r2_hidden(B, k2_relat_1(C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_relat_1)).
% 4.04/1.67  tff(f_153, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 4.04/1.67  tff(c_70, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_6'), '#skF_7')))), inference(cnfTransformation, [status(thm)], [f_165])).
% 4.04/1.67  tff(c_164, plain, (![C_96, A_97, B_98]: (v1_relat_1(C_96) | ~m1_subset_1(C_96, k1_zfmisc_1(k2_zfmisc_1(A_97, B_98))))), inference(cnfTransformation, [status(thm)], [f_96])).
% 4.04/1.67  tff(c_172, plain, (v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_70, c_164])).
% 4.04/1.67  tff(c_271, plain, (![A_134]: (k1_xboole_0=A_134 | r2_hidden(k4_tarski('#skF_1'(A_134), '#skF_2'(A_134)), A_134) | ~v1_relat_1(A_134))), inference(cnfTransformation, [status(thm)], [f_76])).
% 4.04/1.67  tff(c_22, plain, (![C_18, A_15, B_16]: (r2_hidden(C_18, A_15) | ~r2_hidden(C_18, B_16) | ~m1_subset_1(B_16, k1_zfmisc_1(A_15)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 4.04/1.67  tff(c_863, plain, (![A_227, A_228]: (r2_hidden(k4_tarski('#skF_1'(A_227), '#skF_2'(A_227)), A_228) | ~m1_subset_1(A_227, k1_zfmisc_1(A_228)) | k1_xboole_0=A_227 | ~v1_relat_1(A_227))), inference(resolution, [status(thm)], [c_271, c_22])).
% 4.04/1.67  tff(c_20, plain, (![C_13, A_11, B_12, D_14]: (C_13=A_11 | ~r2_hidden(k4_tarski(A_11, B_12), k2_zfmisc_1(k1_tarski(C_13), D_14)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 4.04/1.67  tff(c_916, plain, (![C_234, A_235, D_236]: (C_234='#skF_1'(A_235) | ~m1_subset_1(A_235, k1_zfmisc_1(k2_zfmisc_1(k1_tarski(C_234), D_236))) | k1_xboole_0=A_235 | ~v1_relat_1(A_235))), inference(resolution, [status(thm)], [c_863, c_20])).
% 4.04/1.67  tff(c_919, plain, ('#skF_1'('#skF_8')='#skF_6' | k1_xboole_0='#skF_8' | ~v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_70, c_916])).
% 4.04/1.67  tff(c_926, plain, ('#skF_1'('#skF_8')='#skF_6' | k1_xboole_0='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_172, c_919])).
% 4.04/1.67  tff(c_931, plain, (k1_xboole_0='#skF_8'), inference(splitLeft, [status(thm)], [c_926])).
% 4.04/1.67  tff(c_2, plain, (![A_1]: (r1_tarski(k1_xboole_0, A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.04/1.67  tff(c_4, plain, (![A_2]: (k4_xboole_0(A_2, k1_xboole_0)=A_2)), inference(cnfTransformation, [status(thm)], [f_29])).
% 4.04/1.67  tff(c_137, plain, (![A_92, B_93]: (r2_hidden(A_92, B_93) | k4_xboole_0(k1_tarski(A_92), B_93)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.04/1.67  tff(c_153, plain, (![A_95]: (r2_hidden(A_95, k1_xboole_0) | k1_tarski(A_95)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_4, c_137])).
% 4.04/1.67  tff(c_36, plain, (![B_34, A_33]: (~r1_tarski(B_34, A_33) | ~r2_hidden(A_33, B_34))), inference(cnfTransformation, [status(thm)], [f_92])).
% 4.04/1.67  tff(c_159, plain, (![A_95]: (~r1_tarski(k1_xboole_0, A_95) | k1_tarski(A_95)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_153, c_36])).
% 4.04/1.67  tff(c_163, plain, (![A_95]: (k1_tarski(A_95)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_2, c_159])).
% 4.04/1.67  tff(c_968, plain, (![A_95]: (k1_tarski(A_95)!='#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_931, c_163])).
% 4.04/1.67  tff(c_785, plain, (![A_214, B_215, C_216]: (r2_hidden('#skF_3'(A_214, B_215, C_216), B_215) | k1_relset_1(B_215, A_214, C_216)=B_215 | ~m1_subset_1(C_216, k1_zfmisc_1(k2_zfmisc_1(B_215, A_214))))), inference(cnfTransformation, [status(thm)], [f_114])).
% 4.04/1.67  tff(c_791, plain, (r2_hidden('#skF_3'('#skF_7', k1_tarski('#skF_6'), '#skF_8'), k1_tarski('#skF_6')) | k1_relset_1(k1_tarski('#skF_6'), '#skF_7', '#skF_8')=k1_tarski('#skF_6')), inference(resolution, [status(thm)], [c_70, c_785])).
% 4.04/1.67  tff(c_825, plain, (k1_relset_1(k1_tarski('#skF_6'), '#skF_7', '#skF_8')=k1_tarski('#skF_6')), inference(splitLeft, [status(thm)], [c_791])).
% 4.04/1.67  tff(c_52, plain, (![A_54]: (r2_hidden('#skF_5'(A_54), A_54) | k1_xboole_0=A_54)), inference(cnfTransformation, [status(thm)], [f_135])).
% 4.04/1.67  tff(c_974, plain, (![A_54]: (r2_hidden('#skF_5'(A_54), A_54) | A_54='#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_931, c_52])).
% 4.04/1.67  tff(c_24, plain, (![A_19]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_19)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 4.04/1.67  tff(c_975, plain, (![A_19]: (m1_subset_1('#skF_8', k1_zfmisc_1(A_19)))), inference(demodulation, [status(thm), theory('equality')], [c_931, c_24])).
% 4.04/1.67  tff(c_1171, plain, (![D_270, A_271, B_272, C_273]: (r2_hidden(k4_tarski(D_270, '#skF_4'(A_271, B_272, C_273, D_270)), C_273) | ~r2_hidden(D_270, B_272) | k1_relset_1(B_272, A_271, C_273)!=B_272 | ~m1_subset_1(C_273, k1_zfmisc_1(k2_zfmisc_1(B_272, A_271))))), inference(cnfTransformation, [status(thm)], [f_114])).
% 4.04/1.67  tff(c_120, plain, (![A_90, B_91]: (k4_xboole_0(k1_tarski(A_90), B_91)=k1_xboole_0 | ~r2_hidden(A_90, B_91))), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.04/1.67  tff(c_127, plain, (![A_90]: (k1_tarski(A_90)=k1_xboole_0 | ~r2_hidden(A_90, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_120, c_4])).
% 4.04/1.67  tff(c_174, plain, (![A_90]: (~r2_hidden(A_90, k1_xboole_0))), inference(negUnitSimplification, [status(thm)], [c_163, c_127])).
% 4.04/1.67  tff(c_967, plain, (![A_90]: (~r2_hidden(A_90, '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_931, c_174])).
% 4.04/1.67  tff(c_1182, plain, (![D_270, B_272, A_271]: (~r2_hidden(D_270, B_272) | k1_relset_1(B_272, A_271, '#skF_8')!=B_272 | ~m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1(B_272, A_271))))), inference(resolution, [status(thm)], [c_1171, c_967])).
% 4.04/1.67  tff(c_1216, plain, (![D_274, B_275, A_276]: (~r2_hidden(D_274, B_275) | k1_relset_1(B_275, A_276, '#skF_8')!=B_275)), inference(demodulation, [status(thm), theory('equality')], [c_975, c_1182])).
% 4.04/1.67  tff(c_1235, plain, (![A_277, A_278]: (k1_relset_1(A_277, A_278, '#skF_8')!=A_277 | A_277='#skF_8')), inference(resolution, [status(thm)], [c_974, c_1216])).
% 4.04/1.67  tff(c_1241, plain, (k1_tarski('#skF_6')='#skF_8'), inference(superposition, [status(thm), theory('equality')], [c_825, c_1235])).
% 4.04/1.67  tff(c_1247, plain, $false, inference(negUnitSimplification, [status(thm)], [c_968, c_1241])).
% 4.04/1.67  tff(c_1249, plain, (k1_xboole_0!='#skF_8'), inference(splitRight, [status(thm)], [c_926])).
% 4.04/1.67  tff(c_192, plain, (![C_104, B_105, A_106]: (v5_relat_1(C_104, B_105) | ~m1_subset_1(C_104, k1_zfmisc_1(k2_zfmisc_1(A_106, B_105))))), inference(cnfTransformation, [status(thm)], [f_102])).
% 4.04/1.67  tff(c_200, plain, (v5_relat_1('#skF_8', '#skF_7')), inference(resolution, [status(thm)], [c_70, c_192])).
% 4.04/1.67  tff(c_74, plain, (v1_funct_1('#skF_8')), inference(cnfTransformation, [status(thm)], [f_165])).
% 4.04/1.67  tff(c_459, plain, (![B_183, C_184, A_185]: (r2_hidden(k1_funct_1(B_183, C_184), A_185) | ~r2_hidden(C_184, k1_relat_1(B_183)) | ~v1_funct_1(B_183) | ~v5_relat_1(B_183, A_185) | ~v1_relat_1(B_183))), inference(cnfTransformation, [status(thm)], [f_87])).
% 4.04/1.67  tff(c_66, plain, (~r2_hidden(k1_funct_1('#skF_8', '#skF_6'), '#skF_7')), inference(cnfTransformation, [status(thm)], [f_165])).
% 4.04/1.67  tff(c_473, plain, (~r2_hidden('#skF_6', k1_relat_1('#skF_8')) | ~v1_funct_1('#skF_8') | ~v5_relat_1('#skF_8', '#skF_7') | ~v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_459, c_66])).
% 4.04/1.67  tff(c_480, plain, (~r2_hidden('#skF_6', k1_relat_1('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_172, c_200, c_74, c_473])).
% 4.04/1.67  tff(c_1248, plain, ('#skF_1'('#skF_8')='#skF_6'), inference(splitRight, [status(thm)], [c_926])).
% 4.04/1.67  tff(c_30, plain, (![A_23, C_25, B_24]: (r2_hidden(A_23, k1_relat_1(C_25)) | ~r2_hidden(k4_tarski(A_23, B_24), C_25) | ~v1_relat_1(C_25))), inference(cnfTransformation, [status(thm)], [f_68])).
% 4.04/1.67  tff(c_288, plain, (![A_134]: (r2_hidden('#skF_1'(A_134), k1_relat_1(A_134)) | k1_xboole_0=A_134 | ~v1_relat_1(A_134))), inference(resolution, [status(thm)], [c_271, c_30])).
% 4.04/1.67  tff(c_1262, plain, (r2_hidden('#skF_6', k1_relat_1('#skF_8')) | k1_xboole_0='#skF_8' | ~v1_relat_1('#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_1248, c_288])).
% 4.04/1.67  tff(c_1278, plain, (r2_hidden('#skF_6', k1_relat_1('#skF_8')) | k1_xboole_0='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_172, c_1262])).
% 4.04/1.67  tff(c_1280, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1249, c_480, c_1278])).
% 4.04/1.67  tff(c_1282, plain, (k1_relset_1(k1_tarski('#skF_6'), '#skF_7', '#skF_8')!=k1_tarski('#skF_6')), inference(splitRight, [status(thm)], [c_791])).
% 4.04/1.67  tff(c_68, plain, (k1_xboole_0!='#skF_7'), inference(cnfTransformation, [status(thm)], [f_165])).
% 4.04/1.67  tff(c_72, plain, (v1_funct_2('#skF_8', k1_tarski('#skF_6'), '#skF_7')), inference(cnfTransformation, [status(thm)], [f_165])).
% 4.04/1.67  tff(c_1437, plain, (![B_297, A_298, C_299]: (k1_xboole_0=B_297 | k1_relset_1(A_298, B_297, C_299)=A_298 | ~v1_funct_2(C_299, A_298, B_297) | ~m1_subset_1(C_299, k1_zfmisc_1(k2_zfmisc_1(A_298, B_297))))), inference(cnfTransformation, [status(thm)], [f_153])).
% 4.04/1.67  tff(c_1440, plain, (k1_xboole_0='#skF_7' | k1_relset_1(k1_tarski('#skF_6'), '#skF_7', '#skF_8')=k1_tarski('#skF_6') | ~v1_funct_2('#skF_8', k1_tarski('#skF_6'), '#skF_7')), inference(resolution, [status(thm)], [c_70, c_1437])).
% 4.04/1.67  tff(c_1447, plain, (k1_xboole_0='#skF_7' | k1_relset_1(k1_tarski('#skF_6'), '#skF_7', '#skF_8')=k1_tarski('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_1440])).
% 4.04/1.67  tff(c_1449, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1282, c_68, c_1447])).
% 4.04/1.67  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.04/1.67  
% 4.04/1.67  Inference rules
% 4.04/1.67  ----------------------
% 4.04/1.67  #Ref     : 0
% 4.04/1.67  #Sup     : 260
% 4.04/1.67  #Fact    : 0
% 4.04/1.67  #Define  : 0
% 4.04/1.67  #Split   : 6
% 4.04/1.67  #Chain   : 0
% 4.04/1.67  #Close   : 0
% 4.04/1.67  
% 4.04/1.67  Ordering : KBO
% 4.04/1.67  
% 4.04/1.67  Simplification rules
% 4.04/1.67  ----------------------
% 4.04/1.67  #Subsume      : 31
% 4.04/1.67  #Demod        : 221
% 4.04/1.67  #Tautology    : 87
% 4.04/1.67  #SimpNegUnit  : 20
% 4.04/1.67  #BackRed      : 97
% 4.04/1.67  
% 4.04/1.67  #Partial instantiations: 0
% 4.04/1.67  #Strategies tried      : 1
% 4.04/1.67  
% 4.04/1.67  Timing (in seconds)
% 4.04/1.67  ----------------------
% 4.04/1.67  Preprocessing        : 0.37
% 4.04/1.67  Parsing              : 0.19
% 4.04/1.67  CNF conversion       : 0.03
% 4.04/1.67  Main loop            : 0.52
% 4.04/1.67  Inferencing          : 0.18
% 4.04/1.67  Reduction            : 0.16
% 4.04/1.67  Demodulation         : 0.11
% 4.04/1.67  BG Simplification    : 0.03
% 4.04/1.67  Subsumption          : 0.11
% 4.04/1.67  Abstraction          : 0.02
% 4.04/1.67  MUC search           : 0.00
% 4.04/1.67  Cooper               : 0.00
% 4.04/1.67  Total                : 0.93
% 4.04/1.67  Index Insertion      : 0.00
% 4.04/1.67  Index Deletion       : 0.00
% 4.04/1.67  Index Matching       : 0.00
% 4.04/1.67  BG Taut test         : 0.00
%------------------------------------------------------------------------------
