%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:55:20 EST 2020

% Result     : Theorem 4.70s
% Output     : CNFRefutation 4.70s
% Verified   : 
% Statistics : Number of formulae       :  109 ( 315 expanded)
%              Number of leaves         :   27 ( 109 expanded)
%              Depth                    :   14
%              Number of atoms          :  185 ( 783 expanded)
%              Number of equality atoms :   24 (  65 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_6 > #skF_1 > #skF_7 > #skF_3 > #skF_8 > #skF_2 > #skF_5 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

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

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_90,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => ~ ( B != k1_xboole_0
            & ! [C] :
                ( m1_subset_1(C,A)
               => ~ r2_hidden(C,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_subset_1)).

tff(f_74,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_45,axiom,(
    ! [A,B] :
      ( ! [C] :
          ( r2_hidden(C,A)
        <=> r2_hidden(C,B) )
     => A = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tarski)).

tff(f_58,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_61,axiom,(
    ! [A,B] : ~ r2_hidden(A,k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_zfmisc_1)).

tff(f_77,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_52,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(c_52,plain,(
    k1_xboole_0 != '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_44,plain,(
    ! [B_23,A_22] :
      ( m1_subset_1(B_23,A_22)
      | ~ v1_xboole_0(B_23)
      | ~ v1_xboole_0(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_127,plain,(
    ! [B_44,A_45] :
      ( m1_subset_1(B_44,A_45)
      | ~ v1_xboole_0(B_44)
      | ~ v1_xboole_0(A_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_88,plain,(
    ! [A_36] :
      ( v1_xboole_0(A_36)
      | r2_hidden('#skF_1'(A_36),A_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_50,plain,(
    ! [C_26] :
      ( ~ r2_hidden(C_26,'#skF_8')
      | ~ m1_subset_1(C_26,'#skF_7') ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_100,plain,
    ( ~ m1_subset_1('#skF_1'('#skF_8'),'#skF_7')
    | v1_xboole_0('#skF_8') ),
    inference(resolution,[status(thm)],[c_88,c_50])).

tff(c_103,plain,(
    ~ m1_subset_1('#skF_1'('#skF_8'),'#skF_7') ),
    inference(splitLeft,[status(thm)],[c_100])).

tff(c_135,plain,
    ( ~ v1_xboole_0('#skF_1'('#skF_8'))
    | ~ v1_xboole_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_127,c_103])).

tff(c_136,plain,(
    ~ v1_xboole_0('#skF_7') ),
    inference(splitLeft,[status(thm)],[c_135])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_159,plain,(
    ! [B_51,A_52] :
      ( m1_subset_1(B_51,A_52)
      | ~ r2_hidden(B_51,A_52)
      | v1_xboole_0(A_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_173,plain,(
    ! [A_1] :
      ( m1_subset_1('#skF_1'(A_1),A_1)
      | v1_xboole_0(A_1) ) ),
    inference(resolution,[status(thm)],[c_4,c_159])).

tff(c_174,plain,(
    ! [B_53,A_54] :
      ( r2_hidden(B_53,A_54)
      | ~ m1_subset_1(B_53,A_54)
      | v1_xboole_0(A_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_201,plain,(
    ! [B_53] :
      ( ~ m1_subset_1(B_53,'#skF_7')
      | ~ m1_subset_1(B_53,'#skF_8')
      | v1_xboole_0('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_174,c_50])).

tff(c_284,plain,(
    ! [B_69] :
      ( ~ m1_subset_1(B_69,'#skF_7')
      | ~ m1_subset_1(B_69,'#skF_8') ) ),
    inference(splitLeft,[status(thm)],[c_201])).

tff(c_288,plain,
    ( ~ m1_subset_1('#skF_1'('#skF_7'),'#skF_8')
    | v1_xboole_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_173,c_284])).

tff(c_295,plain,(
    ~ m1_subset_1('#skF_1'('#skF_7'),'#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_136,c_288])).

tff(c_300,plain,
    ( ~ v1_xboole_0('#skF_1'('#skF_7'))
    | ~ v1_xboole_0('#skF_8') ),
    inference(resolution,[status(thm)],[c_44,c_295])).

tff(c_301,plain,(
    ~ v1_xboole_0('#skF_8') ),
    inference(splitLeft,[status(thm)],[c_300])).

tff(c_698,plain,(
    ! [A_114,B_115] :
      ( r2_hidden('#skF_3'(A_114,B_115),B_115)
      | r2_hidden('#skF_4'(A_114,B_115),A_114)
      | B_115 = A_114 ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_34,plain,(
    ! [A_18] : k2_zfmisc_1(A_18,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_78,plain,(
    ! [A_30,B_31] : ~ r2_hidden(A_30,k2_zfmisc_1(A_30,B_31)) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_81,plain,(
    ! [A_18] : ~ r2_hidden(A_18,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_78])).

tff(c_758,plain,(
    ! [A_116] :
      ( r2_hidden('#skF_4'(A_116,k1_xboole_0),A_116)
      | k1_xboole_0 = A_116 ) ),
    inference(resolution,[status(thm)],[c_698,c_81])).

tff(c_40,plain,(
    ! [B_23,A_22] :
      ( m1_subset_1(B_23,A_22)
      | ~ r2_hidden(B_23,A_22)
      | v1_xboole_0(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_780,plain,(
    ! [A_116] :
      ( m1_subset_1('#skF_4'(A_116,k1_xboole_0),A_116)
      | v1_xboole_0(A_116)
      | k1_xboole_0 = A_116 ) ),
    inference(resolution,[status(thm)],[c_758,c_40])).

tff(c_54,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1('#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_48,plain,(
    ! [A_24] : ~ v1_xboole_0(k1_zfmisc_1(A_24)) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_20,plain,(
    ! [C_17,A_13] :
      ( r1_tarski(C_17,A_13)
      | ~ r2_hidden(C_17,k1_zfmisc_1(A_13)) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_181,plain,(
    ! [B_53,A_13] :
      ( r1_tarski(B_53,A_13)
      | ~ m1_subset_1(B_53,k1_zfmisc_1(A_13))
      | v1_xboole_0(k1_zfmisc_1(A_13)) ) ),
    inference(resolution,[status(thm)],[c_174,c_20])).

tff(c_216,plain,(
    ! [B_58,A_59] :
      ( r1_tarski(B_58,A_59)
      | ~ m1_subset_1(B_58,k1_zfmisc_1(A_59)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_181])).

tff(c_236,plain,(
    r1_tarski('#skF_8','#skF_7') ),
    inference(resolution,[status(thm)],[c_54,c_216])).

tff(c_42,plain,(
    ! [B_23,A_22] :
      ( r2_hidden(B_23,A_22)
      | ~ m1_subset_1(B_23,A_22)
      | v1_xboole_0(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_271,plain,(
    ! [C_66,B_67,A_68] :
      ( r2_hidden(C_66,B_67)
      | ~ r2_hidden(C_66,A_68)
      | ~ r1_tarski(A_68,B_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_1729,plain,(
    ! [B_159,B_160,A_161] :
      ( r2_hidden(B_159,B_160)
      | ~ r1_tarski(A_161,B_160)
      | ~ m1_subset_1(B_159,A_161)
      | v1_xboole_0(A_161) ) ),
    inference(resolution,[status(thm)],[c_42,c_271])).

tff(c_1751,plain,(
    ! [B_159] :
      ( r2_hidden(B_159,'#skF_7')
      | ~ m1_subset_1(B_159,'#skF_8')
      | v1_xboole_0('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_236,c_1729])).

tff(c_1779,plain,(
    ! [B_162] :
      ( r2_hidden(B_162,'#skF_7')
      | ~ m1_subset_1(B_162,'#skF_8') ) ),
    inference(negUnitSimplification,[status(thm)],[c_301,c_1751])).

tff(c_1798,plain,(
    ! [B_162] :
      ( m1_subset_1(B_162,'#skF_7')
      | v1_xboole_0('#skF_7')
      | ~ m1_subset_1(B_162,'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_1779,c_40])).

tff(c_1811,plain,(
    ! [B_163] :
      ( m1_subset_1(B_163,'#skF_7')
      | ~ m1_subset_1(B_163,'#skF_8') ) ),
    inference(negUnitSimplification,[status(thm)],[c_136,c_1798])).

tff(c_270,plain,(
    ! [B_53] :
      ( ~ m1_subset_1(B_53,'#skF_7')
      | ~ m1_subset_1(B_53,'#skF_8') ) ),
    inference(splitLeft,[status(thm)],[c_201])).

tff(c_1863,plain,(
    ! [B_164] : ~ m1_subset_1(B_164,'#skF_8') ),
    inference(resolution,[status(thm)],[c_1811,c_270])).

tff(c_1867,plain,
    ( v1_xboole_0('#skF_8')
    | k1_xboole_0 = '#skF_8' ),
    inference(resolution,[status(thm)],[c_780,c_1863])).

tff(c_1883,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_301,c_1867])).

tff(c_1885,plain,(
    v1_xboole_0('#skF_8') ),
    inference(splitRight,[status(thm)],[c_300])).

tff(c_2279,plain,(
    ! [A_209,B_210] :
      ( r2_hidden('#skF_3'(A_209,B_210),B_210)
      | r2_hidden('#skF_4'(A_209,B_210),A_209)
      | B_210 = A_209 ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_2339,plain,(
    ! [A_211] :
      ( r2_hidden('#skF_4'(A_211,k1_xboole_0),A_211)
      | k1_xboole_0 = A_211 ) ),
    inference(resolution,[status(thm)],[c_2279,c_81])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_2369,plain,(
    ! [A_212] :
      ( ~ v1_xboole_0(A_212)
      | k1_xboole_0 = A_212 ) ),
    inference(resolution,[status(thm)],[c_2339,c_2])).

tff(c_2381,plain,(
    k1_xboole_0 = '#skF_8' ),
    inference(resolution,[status(thm)],[c_1885,c_2369])).

tff(c_2391,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_2381])).

tff(c_2392,plain,(
    v1_xboole_0('#skF_8') ),
    inference(splitRight,[status(thm)],[c_201])).

tff(c_2685,plain,(
    ! [A_249,B_250] :
      ( r2_hidden('#skF_3'(A_249,B_250),B_250)
      | r2_hidden('#skF_4'(A_249,B_250),A_249)
      | B_250 = A_249 ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_2786,plain,(
    ! [A_254] :
      ( r2_hidden('#skF_4'(A_254,k1_xboole_0),A_254)
      | k1_xboole_0 = A_254 ) ),
    inference(resolution,[status(thm)],[c_2685,c_81])).

tff(c_2820,plain,(
    ! [A_255] :
      ( ~ v1_xboole_0(A_255)
      | k1_xboole_0 = A_255 ) ),
    inference(resolution,[status(thm)],[c_2786,c_2])).

tff(c_2832,plain,(
    k1_xboole_0 = '#skF_8' ),
    inference(resolution,[status(thm)],[c_2392,c_2820])).

tff(c_2842,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_2832])).

tff(c_2844,plain,(
    v1_xboole_0('#skF_7') ),
    inference(splitRight,[status(thm)],[c_135])).

tff(c_2923,plain,(
    ! [B_273,A_274] :
      ( r2_hidden(B_273,A_274)
      | ~ m1_subset_1(B_273,A_274)
      | v1_xboole_0(A_274) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_2955,plain,(
    ! [B_273] :
      ( ~ m1_subset_1(B_273,'#skF_7')
      | ~ m1_subset_1(B_273,'#skF_8')
      | v1_xboole_0('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_2923,c_50])).

tff(c_2995,plain,(
    ! [B_280] :
      ( ~ m1_subset_1(B_280,'#skF_7')
      | ~ m1_subset_1(B_280,'#skF_8') ) ),
    inference(splitLeft,[status(thm)],[c_2955])).

tff(c_3003,plain,(
    ! [B_23] :
      ( ~ m1_subset_1(B_23,'#skF_8')
      | ~ v1_xboole_0(B_23)
      | ~ v1_xboole_0('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_44,c_2995])).

tff(c_3009,plain,(
    ! [B_281] :
      ( ~ m1_subset_1(B_281,'#skF_8')
      | ~ v1_xboole_0(B_281) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2844,c_3003])).

tff(c_3019,plain,(
    ! [B_23] :
      ( ~ v1_xboole_0(B_23)
      | ~ v1_xboole_0('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_44,c_3009])).

tff(c_3020,plain,(
    ~ v1_xboole_0('#skF_8') ),
    inference(splitLeft,[status(thm)],[c_3019])).

tff(c_2934,plain,(
    ! [B_273,A_13] :
      ( r1_tarski(B_273,A_13)
      | ~ m1_subset_1(B_273,k1_zfmisc_1(A_13))
      | v1_xboole_0(k1_zfmisc_1(A_13)) ) ),
    inference(resolution,[status(thm)],[c_2923,c_20])).

tff(c_2973,plain,(
    ! [B_278,A_279] :
      ( r1_tarski(B_278,A_279)
      | ~ m1_subset_1(B_278,k1_zfmisc_1(A_279)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_2934])).

tff(c_2993,plain,(
    r1_tarski('#skF_8','#skF_7') ),
    inference(resolution,[status(thm)],[c_54,c_2973])).

tff(c_2960,plain,(
    ! [C_275,B_276,A_277] :
      ( r2_hidden(C_275,B_276)
      | ~ r2_hidden(C_275,A_277)
      | ~ r1_tarski(A_277,B_276) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_3035,plain,(
    ! [A_284,B_285] :
      ( r2_hidden('#skF_1'(A_284),B_285)
      | ~ r1_tarski(A_284,B_285)
      | v1_xboole_0(A_284) ) ),
    inference(resolution,[status(thm)],[c_4,c_2960])).

tff(c_3117,plain,(
    ! [B_289,A_290] :
      ( ~ v1_xboole_0(B_289)
      | ~ r1_tarski(A_290,B_289)
      | v1_xboole_0(A_290) ) ),
    inference(resolution,[status(thm)],[c_3035,c_2])).

tff(c_3120,plain,
    ( ~ v1_xboole_0('#skF_7')
    | v1_xboole_0('#skF_8') ),
    inference(resolution,[status(thm)],[c_2993,c_3117])).

tff(c_3135,plain,(
    v1_xboole_0('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2844,c_3120])).

tff(c_3137,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3020,c_3135])).

tff(c_3138,plain,(
    ! [B_23] : ~ v1_xboole_0(B_23) ),
    inference(splitRight,[status(thm)],[c_3019])).

tff(c_3139,plain,(
    v1_xboole_0('#skF_8') ),
    inference(splitRight,[status(thm)],[c_3019])).

tff(c_3148,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3138,c_3139])).

tff(c_3149,plain,(
    v1_xboole_0('#skF_8') ),
    inference(splitRight,[status(thm)],[c_2955])).

tff(c_3462,plain,(
    ! [A_327,B_328] :
      ( r2_hidden('#skF_3'(A_327,B_328),B_328)
      | r2_hidden('#skF_4'(A_327,B_328),A_327)
      | B_328 = A_327 ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_3566,plain,(
    ! [A_332] :
      ( r2_hidden('#skF_4'(A_332,k1_xboole_0),A_332)
      | k1_xboole_0 = A_332 ) ),
    inference(resolution,[status(thm)],[c_3462,c_81])).

tff(c_3602,plain,(
    ! [A_333] :
      ( ~ v1_xboole_0(A_333)
      | k1_xboole_0 = A_333 ) ),
    inference(resolution,[status(thm)],[c_3566,c_2])).

tff(c_3614,plain,(
    k1_xboole_0 = '#skF_8' ),
    inference(resolution,[status(thm)],[c_3149,c_3602])).

tff(c_3627,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_3614])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n022.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 10:56:11 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.70/2.01  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.70/2.02  
% 4.70/2.02  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.70/2.02  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_6 > #skF_1 > #skF_7 > #skF_3 > #skF_8 > #skF_2 > #skF_5 > #skF_4
% 4.70/2.02  
% 4.70/2.02  %Foreground sorts:
% 4.70/2.02  
% 4.70/2.02  
% 4.70/2.02  %Background operators:
% 4.70/2.02  
% 4.70/2.02  
% 4.70/2.02  %Foreground operators:
% 4.70/2.02  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 4.70/2.02  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.70/2.02  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.70/2.02  tff('#skF_1', type, '#skF_1': $i > $i).
% 4.70/2.02  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.70/2.02  tff('#skF_7', type, '#skF_7': $i).
% 4.70/2.02  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 4.70/2.02  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.70/2.02  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.70/2.02  tff('#skF_8', type, '#skF_8': $i).
% 4.70/2.02  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.70/2.02  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.70/2.02  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.70/2.02  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 4.70/2.02  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.70/2.02  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 4.70/2.02  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 4.70/2.02  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.70/2.02  
% 4.70/2.04  tff(f_90, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => ~(~(B = k1_xboole_0) & (![C]: (m1_subset_1(C, A) => ~r2_hidden(C, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_subset_1)).
% 4.70/2.04  tff(f_74, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 4.70/2.04  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 4.70/2.04  tff(f_45, axiom, (![A, B]: ((![C]: (r2_hidden(C, A) <=> r2_hidden(C, B))) => (A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_tarski)).
% 4.70/2.04  tff(f_58, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 4.70/2.04  tff(f_61, axiom, (![A, B]: ~r2_hidden(A, k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t152_zfmisc_1)).
% 4.70/2.04  tff(f_77, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_subset_1)).
% 4.70/2.04  tff(f_52, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 4.70/2.04  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 4.70/2.04  tff(c_52, plain, (k1_xboole_0!='#skF_8'), inference(cnfTransformation, [status(thm)], [f_90])).
% 4.70/2.04  tff(c_44, plain, (![B_23, A_22]: (m1_subset_1(B_23, A_22) | ~v1_xboole_0(B_23) | ~v1_xboole_0(A_22))), inference(cnfTransformation, [status(thm)], [f_74])).
% 4.70/2.04  tff(c_127, plain, (![B_44, A_45]: (m1_subset_1(B_44, A_45) | ~v1_xboole_0(B_44) | ~v1_xboole_0(A_45))), inference(cnfTransformation, [status(thm)], [f_74])).
% 4.70/2.04  tff(c_88, plain, (![A_36]: (v1_xboole_0(A_36) | r2_hidden('#skF_1'(A_36), A_36))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.70/2.04  tff(c_50, plain, (![C_26]: (~r2_hidden(C_26, '#skF_8') | ~m1_subset_1(C_26, '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_90])).
% 4.70/2.04  tff(c_100, plain, (~m1_subset_1('#skF_1'('#skF_8'), '#skF_7') | v1_xboole_0('#skF_8')), inference(resolution, [status(thm)], [c_88, c_50])).
% 4.70/2.04  tff(c_103, plain, (~m1_subset_1('#skF_1'('#skF_8'), '#skF_7')), inference(splitLeft, [status(thm)], [c_100])).
% 4.70/2.04  tff(c_135, plain, (~v1_xboole_0('#skF_1'('#skF_8')) | ~v1_xboole_0('#skF_7')), inference(resolution, [status(thm)], [c_127, c_103])).
% 4.70/2.04  tff(c_136, plain, (~v1_xboole_0('#skF_7')), inference(splitLeft, [status(thm)], [c_135])).
% 4.70/2.04  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.70/2.04  tff(c_159, plain, (![B_51, A_52]: (m1_subset_1(B_51, A_52) | ~r2_hidden(B_51, A_52) | v1_xboole_0(A_52))), inference(cnfTransformation, [status(thm)], [f_74])).
% 4.70/2.04  tff(c_173, plain, (![A_1]: (m1_subset_1('#skF_1'(A_1), A_1) | v1_xboole_0(A_1))), inference(resolution, [status(thm)], [c_4, c_159])).
% 4.70/2.04  tff(c_174, plain, (![B_53, A_54]: (r2_hidden(B_53, A_54) | ~m1_subset_1(B_53, A_54) | v1_xboole_0(A_54))), inference(cnfTransformation, [status(thm)], [f_74])).
% 4.70/2.04  tff(c_201, plain, (![B_53]: (~m1_subset_1(B_53, '#skF_7') | ~m1_subset_1(B_53, '#skF_8') | v1_xboole_0('#skF_8'))), inference(resolution, [status(thm)], [c_174, c_50])).
% 4.70/2.04  tff(c_284, plain, (![B_69]: (~m1_subset_1(B_69, '#skF_7') | ~m1_subset_1(B_69, '#skF_8'))), inference(splitLeft, [status(thm)], [c_201])).
% 4.70/2.04  tff(c_288, plain, (~m1_subset_1('#skF_1'('#skF_7'), '#skF_8') | v1_xboole_0('#skF_7')), inference(resolution, [status(thm)], [c_173, c_284])).
% 4.70/2.04  tff(c_295, plain, (~m1_subset_1('#skF_1'('#skF_7'), '#skF_8')), inference(negUnitSimplification, [status(thm)], [c_136, c_288])).
% 4.70/2.04  tff(c_300, plain, (~v1_xboole_0('#skF_1'('#skF_7')) | ~v1_xboole_0('#skF_8')), inference(resolution, [status(thm)], [c_44, c_295])).
% 4.70/2.04  tff(c_301, plain, (~v1_xboole_0('#skF_8')), inference(splitLeft, [status(thm)], [c_300])).
% 4.70/2.04  tff(c_698, plain, (![A_114, B_115]: (r2_hidden('#skF_3'(A_114, B_115), B_115) | r2_hidden('#skF_4'(A_114, B_115), A_114) | B_115=A_114)), inference(cnfTransformation, [status(thm)], [f_45])).
% 4.70/2.04  tff(c_34, plain, (![A_18]: (k2_zfmisc_1(A_18, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_58])).
% 4.70/2.04  tff(c_78, plain, (![A_30, B_31]: (~r2_hidden(A_30, k2_zfmisc_1(A_30, B_31)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 4.70/2.04  tff(c_81, plain, (![A_18]: (~r2_hidden(A_18, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_34, c_78])).
% 4.70/2.04  tff(c_758, plain, (![A_116]: (r2_hidden('#skF_4'(A_116, k1_xboole_0), A_116) | k1_xboole_0=A_116)), inference(resolution, [status(thm)], [c_698, c_81])).
% 4.70/2.04  tff(c_40, plain, (![B_23, A_22]: (m1_subset_1(B_23, A_22) | ~r2_hidden(B_23, A_22) | v1_xboole_0(A_22))), inference(cnfTransformation, [status(thm)], [f_74])).
% 4.70/2.04  tff(c_780, plain, (![A_116]: (m1_subset_1('#skF_4'(A_116, k1_xboole_0), A_116) | v1_xboole_0(A_116) | k1_xboole_0=A_116)), inference(resolution, [status(thm)], [c_758, c_40])).
% 4.70/2.04  tff(c_54, plain, (m1_subset_1('#skF_8', k1_zfmisc_1('#skF_7'))), inference(cnfTransformation, [status(thm)], [f_90])).
% 4.70/2.04  tff(c_48, plain, (![A_24]: (~v1_xboole_0(k1_zfmisc_1(A_24)))), inference(cnfTransformation, [status(thm)], [f_77])).
% 4.70/2.04  tff(c_20, plain, (![C_17, A_13]: (r1_tarski(C_17, A_13) | ~r2_hidden(C_17, k1_zfmisc_1(A_13)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 4.70/2.04  tff(c_181, plain, (![B_53, A_13]: (r1_tarski(B_53, A_13) | ~m1_subset_1(B_53, k1_zfmisc_1(A_13)) | v1_xboole_0(k1_zfmisc_1(A_13)))), inference(resolution, [status(thm)], [c_174, c_20])).
% 4.70/2.04  tff(c_216, plain, (![B_58, A_59]: (r1_tarski(B_58, A_59) | ~m1_subset_1(B_58, k1_zfmisc_1(A_59)))), inference(negUnitSimplification, [status(thm)], [c_48, c_181])).
% 4.70/2.04  tff(c_236, plain, (r1_tarski('#skF_8', '#skF_7')), inference(resolution, [status(thm)], [c_54, c_216])).
% 4.70/2.04  tff(c_42, plain, (![B_23, A_22]: (r2_hidden(B_23, A_22) | ~m1_subset_1(B_23, A_22) | v1_xboole_0(A_22))), inference(cnfTransformation, [status(thm)], [f_74])).
% 4.70/2.04  tff(c_271, plain, (![C_66, B_67, A_68]: (r2_hidden(C_66, B_67) | ~r2_hidden(C_66, A_68) | ~r1_tarski(A_68, B_67))), inference(cnfTransformation, [status(thm)], [f_38])).
% 4.70/2.04  tff(c_1729, plain, (![B_159, B_160, A_161]: (r2_hidden(B_159, B_160) | ~r1_tarski(A_161, B_160) | ~m1_subset_1(B_159, A_161) | v1_xboole_0(A_161))), inference(resolution, [status(thm)], [c_42, c_271])).
% 4.70/2.04  tff(c_1751, plain, (![B_159]: (r2_hidden(B_159, '#skF_7') | ~m1_subset_1(B_159, '#skF_8') | v1_xboole_0('#skF_8'))), inference(resolution, [status(thm)], [c_236, c_1729])).
% 4.70/2.04  tff(c_1779, plain, (![B_162]: (r2_hidden(B_162, '#skF_7') | ~m1_subset_1(B_162, '#skF_8'))), inference(negUnitSimplification, [status(thm)], [c_301, c_1751])).
% 4.70/2.04  tff(c_1798, plain, (![B_162]: (m1_subset_1(B_162, '#skF_7') | v1_xboole_0('#skF_7') | ~m1_subset_1(B_162, '#skF_8'))), inference(resolution, [status(thm)], [c_1779, c_40])).
% 4.70/2.04  tff(c_1811, plain, (![B_163]: (m1_subset_1(B_163, '#skF_7') | ~m1_subset_1(B_163, '#skF_8'))), inference(negUnitSimplification, [status(thm)], [c_136, c_1798])).
% 4.70/2.04  tff(c_270, plain, (![B_53]: (~m1_subset_1(B_53, '#skF_7') | ~m1_subset_1(B_53, '#skF_8'))), inference(splitLeft, [status(thm)], [c_201])).
% 4.70/2.04  tff(c_1863, plain, (![B_164]: (~m1_subset_1(B_164, '#skF_8'))), inference(resolution, [status(thm)], [c_1811, c_270])).
% 4.70/2.04  tff(c_1867, plain, (v1_xboole_0('#skF_8') | k1_xboole_0='#skF_8'), inference(resolution, [status(thm)], [c_780, c_1863])).
% 4.70/2.04  tff(c_1883, plain, $false, inference(negUnitSimplification, [status(thm)], [c_52, c_301, c_1867])).
% 4.70/2.04  tff(c_1885, plain, (v1_xboole_0('#skF_8')), inference(splitRight, [status(thm)], [c_300])).
% 4.70/2.04  tff(c_2279, plain, (![A_209, B_210]: (r2_hidden('#skF_3'(A_209, B_210), B_210) | r2_hidden('#skF_4'(A_209, B_210), A_209) | B_210=A_209)), inference(cnfTransformation, [status(thm)], [f_45])).
% 4.70/2.04  tff(c_2339, plain, (![A_211]: (r2_hidden('#skF_4'(A_211, k1_xboole_0), A_211) | k1_xboole_0=A_211)), inference(resolution, [status(thm)], [c_2279, c_81])).
% 4.70/2.04  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.70/2.04  tff(c_2369, plain, (![A_212]: (~v1_xboole_0(A_212) | k1_xboole_0=A_212)), inference(resolution, [status(thm)], [c_2339, c_2])).
% 4.70/2.04  tff(c_2381, plain, (k1_xboole_0='#skF_8'), inference(resolution, [status(thm)], [c_1885, c_2369])).
% 4.70/2.04  tff(c_2391, plain, $false, inference(negUnitSimplification, [status(thm)], [c_52, c_2381])).
% 4.70/2.04  tff(c_2392, plain, (v1_xboole_0('#skF_8')), inference(splitRight, [status(thm)], [c_201])).
% 4.70/2.04  tff(c_2685, plain, (![A_249, B_250]: (r2_hidden('#skF_3'(A_249, B_250), B_250) | r2_hidden('#skF_4'(A_249, B_250), A_249) | B_250=A_249)), inference(cnfTransformation, [status(thm)], [f_45])).
% 4.70/2.04  tff(c_2786, plain, (![A_254]: (r2_hidden('#skF_4'(A_254, k1_xboole_0), A_254) | k1_xboole_0=A_254)), inference(resolution, [status(thm)], [c_2685, c_81])).
% 4.70/2.04  tff(c_2820, plain, (![A_255]: (~v1_xboole_0(A_255) | k1_xboole_0=A_255)), inference(resolution, [status(thm)], [c_2786, c_2])).
% 4.70/2.04  tff(c_2832, plain, (k1_xboole_0='#skF_8'), inference(resolution, [status(thm)], [c_2392, c_2820])).
% 4.70/2.04  tff(c_2842, plain, $false, inference(negUnitSimplification, [status(thm)], [c_52, c_2832])).
% 4.70/2.04  tff(c_2844, plain, (v1_xboole_0('#skF_7')), inference(splitRight, [status(thm)], [c_135])).
% 4.70/2.04  tff(c_2923, plain, (![B_273, A_274]: (r2_hidden(B_273, A_274) | ~m1_subset_1(B_273, A_274) | v1_xboole_0(A_274))), inference(cnfTransformation, [status(thm)], [f_74])).
% 4.70/2.04  tff(c_2955, plain, (![B_273]: (~m1_subset_1(B_273, '#skF_7') | ~m1_subset_1(B_273, '#skF_8') | v1_xboole_0('#skF_8'))), inference(resolution, [status(thm)], [c_2923, c_50])).
% 4.70/2.04  tff(c_2995, plain, (![B_280]: (~m1_subset_1(B_280, '#skF_7') | ~m1_subset_1(B_280, '#skF_8'))), inference(splitLeft, [status(thm)], [c_2955])).
% 4.70/2.04  tff(c_3003, plain, (![B_23]: (~m1_subset_1(B_23, '#skF_8') | ~v1_xboole_0(B_23) | ~v1_xboole_0('#skF_7'))), inference(resolution, [status(thm)], [c_44, c_2995])).
% 4.70/2.04  tff(c_3009, plain, (![B_281]: (~m1_subset_1(B_281, '#skF_8') | ~v1_xboole_0(B_281))), inference(demodulation, [status(thm), theory('equality')], [c_2844, c_3003])).
% 4.70/2.04  tff(c_3019, plain, (![B_23]: (~v1_xboole_0(B_23) | ~v1_xboole_0('#skF_8'))), inference(resolution, [status(thm)], [c_44, c_3009])).
% 4.70/2.04  tff(c_3020, plain, (~v1_xboole_0('#skF_8')), inference(splitLeft, [status(thm)], [c_3019])).
% 4.70/2.04  tff(c_2934, plain, (![B_273, A_13]: (r1_tarski(B_273, A_13) | ~m1_subset_1(B_273, k1_zfmisc_1(A_13)) | v1_xboole_0(k1_zfmisc_1(A_13)))), inference(resolution, [status(thm)], [c_2923, c_20])).
% 4.70/2.04  tff(c_2973, plain, (![B_278, A_279]: (r1_tarski(B_278, A_279) | ~m1_subset_1(B_278, k1_zfmisc_1(A_279)))), inference(negUnitSimplification, [status(thm)], [c_48, c_2934])).
% 4.70/2.04  tff(c_2993, plain, (r1_tarski('#skF_8', '#skF_7')), inference(resolution, [status(thm)], [c_54, c_2973])).
% 4.70/2.04  tff(c_2960, plain, (![C_275, B_276, A_277]: (r2_hidden(C_275, B_276) | ~r2_hidden(C_275, A_277) | ~r1_tarski(A_277, B_276))), inference(cnfTransformation, [status(thm)], [f_38])).
% 4.70/2.04  tff(c_3035, plain, (![A_284, B_285]: (r2_hidden('#skF_1'(A_284), B_285) | ~r1_tarski(A_284, B_285) | v1_xboole_0(A_284))), inference(resolution, [status(thm)], [c_4, c_2960])).
% 4.70/2.04  tff(c_3117, plain, (![B_289, A_290]: (~v1_xboole_0(B_289) | ~r1_tarski(A_290, B_289) | v1_xboole_0(A_290))), inference(resolution, [status(thm)], [c_3035, c_2])).
% 4.70/2.04  tff(c_3120, plain, (~v1_xboole_0('#skF_7') | v1_xboole_0('#skF_8')), inference(resolution, [status(thm)], [c_2993, c_3117])).
% 4.70/2.04  tff(c_3135, plain, (v1_xboole_0('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_2844, c_3120])).
% 4.70/2.04  tff(c_3137, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3020, c_3135])).
% 4.70/2.04  tff(c_3138, plain, (![B_23]: (~v1_xboole_0(B_23))), inference(splitRight, [status(thm)], [c_3019])).
% 4.70/2.04  tff(c_3139, plain, (v1_xboole_0('#skF_8')), inference(splitRight, [status(thm)], [c_3019])).
% 4.70/2.04  tff(c_3148, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3138, c_3139])).
% 4.70/2.04  tff(c_3149, plain, (v1_xboole_0('#skF_8')), inference(splitRight, [status(thm)], [c_2955])).
% 4.70/2.04  tff(c_3462, plain, (![A_327, B_328]: (r2_hidden('#skF_3'(A_327, B_328), B_328) | r2_hidden('#skF_4'(A_327, B_328), A_327) | B_328=A_327)), inference(cnfTransformation, [status(thm)], [f_45])).
% 4.70/2.04  tff(c_3566, plain, (![A_332]: (r2_hidden('#skF_4'(A_332, k1_xboole_0), A_332) | k1_xboole_0=A_332)), inference(resolution, [status(thm)], [c_3462, c_81])).
% 4.70/2.04  tff(c_3602, plain, (![A_333]: (~v1_xboole_0(A_333) | k1_xboole_0=A_333)), inference(resolution, [status(thm)], [c_3566, c_2])).
% 4.70/2.04  tff(c_3614, plain, (k1_xboole_0='#skF_8'), inference(resolution, [status(thm)], [c_3149, c_3602])).
% 4.70/2.04  tff(c_3627, plain, $false, inference(negUnitSimplification, [status(thm)], [c_52, c_3614])).
% 4.70/2.04  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.70/2.04  
% 4.70/2.04  Inference rules
% 4.70/2.04  ----------------------
% 4.70/2.04  #Ref     : 0
% 4.70/2.04  #Sup     : 721
% 4.70/2.04  #Fact    : 0
% 4.70/2.04  #Define  : 0
% 4.70/2.04  #Split   : 10
% 4.70/2.04  #Chain   : 0
% 4.70/2.04  #Close   : 0
% 4.70/2.04  
% 4.70/2.04  Ordering : KBO
% 4.70/2.04  
% 4.70/2.04  Simplification rules
% 4.70/2.04  ----------------------
% 4.70/2.04  #Subsume      : 132
% 4.70/2.04  #Demod        : 182
% 4.70/2.04  #Tautology    : 214
% 4.70/2.04  #SimpNegUnit  : 108
% 4.70/2.04  #BackRed      : 16
% 4.70/2.04  
% 4.70/2.04  #Partial instantiations: 0
% 4.70/2.04  #Strategies tried      : 1
% 4.70/2.04  
% 4.70/2.04  Timing (in seconds)
% 4.70/2.04  ----------------------
% 4.70/2.04  Preprocessing        : 0.29
% 4.70/2.04  Parsing              : 0.14
% 4.70/2.04  CNF conversion       : 0.02
% 4.70/2.04  Main loop            : 0.89
% 4.70/2.04  Inferencing          : 0.34
% 4.70/2.04  Reduction            : 0.24
% 4.70/2.04  Demodulation         : 0.14
% 4.70/2.04  BG Simplification    : 0.03
% 4.70/2.04  Subsumption          : 0.17
% 4.70/2.04  Abstraction          : 0.03
% 4.70/2.04  MUC search           : 0.00
% 4.70/2.05  Cooper               : 0.00
% 4.70/2.05  Total                : 1.22
% 4.70/2.05  Index Insertion      : 0.00
% 4.70/2.05  Index Deletion       : 0.00
% 4.70/2.05  Index Matching       : 0.00
% 4.70/2.05  BG Taut test         : 0.00
%------------------------------------------------------------------------------
