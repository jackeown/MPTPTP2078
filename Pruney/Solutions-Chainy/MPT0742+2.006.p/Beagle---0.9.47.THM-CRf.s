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
% DateTime   : Thu Dec  3 10:06:07 EST 2020

% Result     : Theorem 6.33s
% Output     : CNFRefutation 6.59s
% Verified   : 
% Statistics : Number of formulae       :  107 ( 454 expanded)
%              Number of leaves         :   23 ( 160 expanded)
%              Depth                    :   15
%              Number of atoms          :  243 (1121 expanded)
%              Number of equality atoms :    9 (  31 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > r1_ordinal1 > v3_ordinal1 > #nlpp > k1_xboole_0 > #skF_5 > #skF_4 > #skF_3 > #skF_2 > #skF_1 > #skF_6

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(r1_ordinal1,type,(
    r1_ordinal1: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v3_ordinal1,type,(
    v3_ordinal1: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i > $i )).

tff(f_34,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & ! [C] :
            ~ ( r2_hidden(C,B)
              & ! [D] :
                  ~ ( r2_hidden(D,B)
                    & r2_hidden(D,C) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_tarski)).

tff(f_91,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

tff(f_113,negated_conjecture,(
    ~ ! [A,B] :
        ( v3_ordinal1(B)
       => ~ ( r1_tarski(A,B)
            & A != k1_xboole_0
            & ! [C] :
                ( v3_ordinal1(C)
               => ~ ( r2_hidden(C,A)
                    & ! [D] :
                        ( v3_ordinal1(D)
                       => ( r2_hidden(D,A)
                         => r1_ordinal1(C,D) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_ordinal1)).

tff(f_86,axiom,(
    ! [A] :
      ( ! [B] :
          ( r2_hidden(B,A)
         => ( v3_ordinal1(B)
            & r1_tarski(B,A) ) )
     => v3_ordinal1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_ordinal1)).

tff(f_77,axiom,(
    ! [A] :
      ( v3_ordinal1(A)
     => ! [B] :
          ( v3_ordinal1(B)
         => ( r1_ordinal1(A,B)
            | r2_hidden(B,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_ordinal1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_53,axiom,(
    ! [A,B] :
      ( v3_ordinal1(B)
     => ( r2_hidden(A,B)
       => v3_ordinal1(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_ordinal1)).

tff(f_68,axiom,(
    ! [A] :
      ( v3_ordinal1(A)
     => ! [B] :
          ( v3_ordinal1(B)
         => ~ ( ~ r2_hidden(A,B)
              & A != B
              & ~ r2_hidden(B,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_ordinal1)).

tff(c_8,plain,(
    ! [A_6] : r1_tarski(k1_xboole_0,A_6) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_56,plain,(
    ! [A_39,B_40] :
      ( r2_hidden('#skF_2'(A_39,B_40),B_40)
      | ~ r2_hidden(A_39,B_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_24,plain,(
    ! [B_25,A_24] :
      ( ~ r1_tarski(B_25,A_24)
      | ~ r2_hidden(A_24,B_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_81,plain,(
    ! [B_46,A_47] :
      ( ~ r1_tarski(B_46,'#skF_2'(A_47,B_46))
      | ~ r2_hidden(A_47,B_46) ) ),
    inference(resolution,[status(thm)],[c_56,c_24])).

tff(c_86,plain,(
    ! [A_47] : ~ r2_hidden(A_47,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_8,c_81])).

tff(c_26,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_22,plain,(
    ! [A_22] :
      ( r2_hidden('#skF_3'(A_22),A_22)
      | v3_ordinal1(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_39,plain,(
    ! [B_33,A_34] :
      ( ~ r1_tarski(B_33,A_34)
      | ~ r2_hidden(A_34,B_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_44,plain,(
    ! [A_35] :
      ( ~ r1_tarski(A_35,'#skF_3'(A_35))
      | v3_ordinal1(A_35) ) ),
    inference(resolution,[status(thm)],[c_22,c_39])).

tff(c_49,plain,(
    v3_ordinal1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_8,c_44])).

tff(c_18,plain,(
    ! [B_21,A_19] :
      ( r2_hidden(B_21,A_19)
      | r1_ordinal1(A_19,B_21)
      | ~ v3_ordinal1(B_21)
      | ~ v3_ordinal1(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_36,plain,(
    ! [C_29] :
      ( v3_ordinal1('#skF_6'(C_29))
      | ~ r2_hidden(C_29,'#skF_4')
      | ~ v3_ordinal1(C_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_168,plain,(
    ! [B_63,A_64] :
      ( r2_hidden(B_63,A_64)
      | r1_ordinal1(A_64,B_63)
      | ~ v3_ordinal1(B_63)
      | ~ v3_ordinal1(A_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_174,plain,(
    ! [B_63] :
      ( r1_ordinal1(k1_xboole_0,B_63)
      | ~ v3_ordinal1(B_63)
      | ~ v3_ordinal1(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_168,c_86])).

tff(c_192,plain,(
    ! [B_65] :
      ( r1_ordinal1(k1_xboole_0,B_65)
      | ~ v3_ordinal1(B_65) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_49,c_174])).

tff(c_32,plain,(
    ! [C_29] :
      ( ~ r1_ordinal1(C_29,'#skF_6'(C_29))
      | ~ r2_hidden(C_29,'#skF_4')
      | ~ v3_ordinal1(C_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_196,plain,
    ( ~ r2_hidden(k1_xboole_0,'#skF_4')
    | ~ v3_ordinal1(k1_xboole_0)
    | ~ v3_ordinal1('#skF_6'(k1_xboole_0)) ),
    inference(resolution,[status(thm)],[c_192,c_32])).

tff(c_199,plain,
    ( ~ r2_hidden(k1_xboole_0,'#skF_4')
    | ~ v3_ordinal1('#skF_6'(k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_49,c_196])).

tff(c_200,plain,(
    ~ v3_ordinal1('#skF_6'(k1_xboole_0)) ),
    inference(splitLeft,[status(thm)],[c_199])).

tff(c_203,plain,
    ( ~ r2_hidden(k1_xboole_0,'#skF_4')
    | ~ v3_ordinal1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_36,c_200])).

tff(c_206,plain,(
    ~ r2_hidden(k1_xboole_0,'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_49,c_203])).

tff(c_226,plain,
    ( r1_ordinal1('#skF_4',k1_xboole_0)
    | ~ v3_ordinal1(k1_xboole_0)
    | ~ v3_ordinal1('#skF_4') ),
    inference(resolution,[status(thm)],[c_18,c_206])).

tff(c_229,plain,
    ( r1_ordinal1('#skF_4',k1_xboole_0)
    | ~ v3_ordinal1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_49,c_226])).

tff(c_230,plain,(
    ~ v3_ordinal1('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_229])).

tff(c_66,plain,(
    ! [A_43,B_44] :
      ( r2_hidden('#skF_1'(A_43,B_44),A_43)
      | r1_tarski(A_43,B_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_77,plain,(
    ! [A_43] : r1_tarski(A_43,A_43) ),
    inference(resolution,[status(thm)],[c_66,c_4])).

tff(c_30,plain,(
    v3_ordinal1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_28,plain,(
    r1_tarski('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_12,plain,(
    ! [A_7,B_8] :
      ( r2_hidden('#skF_2'(A_7,B_8),B_8)
      | ~ r2_hidden(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_123,plain,(
    ! [C_54,B_55,A_56] :
      ( r2_hidden(C_54,B_55)
      | ~ r2_hidden(C_54,A_56)
      | ~ r1_tarski(A_56,B_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_318,plain,(
    ! [A_82,B_83,B_84] :
      ( r2_hidden('#skF_2'(A_82,B_83),B_84)
      | ~ r1_tarski(B_83,B_84)
      | ~ r2_hidden(A_82,B_83) ) ),
    inference(resolution,[status(thm)],[c_12,c_123])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_1308,plain,(
    ! [A_173,B_174,B_175,B_176] :
      ( r2_hidden('#skF_2'(A_173,B_174),B_175)
      | ~ r1_tarski(B_176,B_175)
      | ~ r1_tarski(B_174,B_176)
      | ~ r2_hidden(A_173,B_174) ) ),
    inference(resolution,[status(thm)],[c_318,c_2])).

tff(c_1318,plain,(
    ! [A_177,B_178] :
      ( r2_hidden('#skF_2'(A_177,B_178),'#skF_5')
      | ~ r1_tarski(B_178,'#skF_4')
      | ~ r2_hidden(A_177,B_178) ) ),
    inference(resolution,[status(thm)],[c_28,c_1308])).

tff(c_14,plain,(
    ! [A_14,B_15] :
      ( v3_ordinal1(A_14)
      | ~ r2_hidden(A_14,B_15)
      | ~ v3_ordinal1(B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_1326,plain,(
    ! [A_177,B_178] :
      ( v3_ordinal1('#skF_2'(A_177,B_178))
      | ~ v3_ordinal1('#skF_5')
      | ~ r1_tarski(B_178,'#skF_4')
      | ~ r2_hidden(A_177,B_178) ) ),
    inference(resolution,[status(thm)],[c_1318,c_14])).

tff(c_1334,plain,(
    ! [A_177,B_178] :
      ( v3_ordinal1('#skF_2'(A_177,B_178))
      | ~ r1_tarski(B_178,'#skF_4')
      | ~ r2_hidden(A_177,B_178) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_1326])).

tff(c_134,plain,(
    ! [A_7,B_8,B_55] :
      ( r2_hidden('#skF_2'(A_7,B_8),B_55)
      | ~ r1_tarski(B_8,B_55)
      | ~ r2_hidden(A_7,B_8) ) ),
    inference(resolution,[status(thm)],[c_12,c_123])).

tff(c_34,plain,(
    ! [C_29] :
      ( r2_hidden('#skF_6'(C_29),'#skF_4')
      | ~ r2_hidden(C_29,'#skF_4')
      | ~ v3_ordinal1(C_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_232,plain,(
    ! [D_68,A_69,B_70] :
      ( ~ r2_hidden(D_68,'#skF_2'(A_69,B_70))
      | ~ r2_hidden(D_68,B_70)
      | ~ r2_hidden(A_69,B_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_2203,plain,(
    ! [B_248,B_249,A_250] :
      ( ~ r2_hidden(B_248,B_249)
      | ~ r2_hidden(A_250,B_249)
      | r1_ordinal1('#skF_2'(A_250,B_249),B_248)
      | ~ v3_ordinal1(B_248)
      | ~ v3_ordinal1('#skF_2'(A_250,B_249)) ) ),
    inference(resolution,[status(thm)],[c_18,c_232])).

tff(c_2442,plain,(
    ! [A_253,B_254] :
      ( ~ r2_hidden('#skF_2'(A_253,B_254),'#skF_4')
      | ~ r2_hidden('#skF_6'('#skF_2'(A_253,B_254)),B_254)
      | ~ r2_hidden(A_253,B_254)
      | ~ v3_ordinal1('#skF_6'('#skF_2'(A_253,B_254)))
      | ~ v3_ordinal1('#skF_2'(A_253,B_254)) ) ),
    inference(resolution,[status(thm)],[c_2203,c_32])).

tff(c_2993,plain,(
    ! [A_263] :
      ( ~ r2_hidden(A_263,'#skF_4')
      | ~ v3_ordinal1('#skF_6'('#skF_2'(A_263,'#skF_4')))
      | ~ r2_hidden('#skF_2'(A_263,'#skF_4'),'#skF_4')
      | ~ v3_ordinal1('#skF_2'(A_263,'#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_34,c_2442])).

tff(c_3206,plain,(
    ! [A_265] :
      ( ~ r2_hidden(A_265,'#skF_4')
      | ~ r2_hidden('#skF_2'(A_265,'#skF_4'),'#skF_4')
      | ~ v3_ordinal1('#skF_2'(A_265,'#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_36,c_2993])).

tff(c_3226,plain,(
    ! [A_7] :
      ( ~ v3_ordinal1('#skF_2'(A_7,'#skF_4'))
      | ~ r1_tarski('#skF_4','#skF_4')
      | ~ r2_hidden(A_7,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_134,c_3206])).

tff(c_3246,plain,(
    ! [A_266] :
      ( ~ v3_ordinal1('#skF_2'(A_266,'#skF_4'))
      | ~ r2_hidden(A_266,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_77,c_3226])).

tff(c_3250,plain,(
    ! [A_177] :
      ( ~ r1_tarski('#skF_4','#skF_4')
      | ~ r2_hidden(A_177,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_1334,c_3246])).

tff(c_3264,plain,(
    ! [A_267] : ~ r2_hidden(A_267,'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_77,c_3250])).

tff(c_3328,plain,(
    v3_ordinal1('#skF_4') ),
    inference(resolution,[status(thm)],[c_22,c_3264])).

tff(c_3348,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_230,c_3328])).

tff(c_3350,plain,(
    v3_ordinal1('#skF_4') ),
    inference(splitRight,[status(thm)],[c_229])).

tff(c_3480,plain,(
    ! [B_285,A_286] :
      ( r2_hidden(B_285,A_286)
      | B_285 = A_286
      | r2_hidden(A_286,B_285)
      | ~ v3_ordinal1(B_285)
      | ~ v3_ordinal1(A_286) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_3487,plain,
    ( k1_xboole_0 = '#skF_4'
    | r2_hidden('#skF_4',k1_xboole_0)
    | ~ v3_ordinal1(k1_xboole_0)
    | ~ v3_ordinal1('#skF_4') ),
    inference(resolution,[status(thm)],[c_3480,c_206])).

tff(c_3530,plain,
    ( k1_xboole_0 = '#skF_4'
    | r2_hidden('#skF_4',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3350,c_49,c_3487])).

tff(c_3532,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_26,c_3530])).

tff(c_3533,plain,(
    ~ r2_hidden(k1_xboole_0,'#skF_4') ),
    inference(splitRight,[status(thm)],[c_199])).

tff(c_3537,plain,
    ( r1_ordinal1('#skF_4',k1_xboole_0)
    | ~ v3_ordinal1(k1_xboole_0)
    | ~ v3_ordinal1('#skF_4') ),
    inference(resolution,[status(thm)],[c_18,c_3533])).

tff(c_3540,plain,
    ( r1_ordinal1('#skF_4',k1_xboole_0)
    | ~ v3_ordinal1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_49,c_3537])).

tff(c_3541,plain,(
    ~ v3_ordinal1('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_3540])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_3954,plain,(
    ! [A_323,B_324,B_325] :
      ( r2_hidden('#skF_1'(A_323,B_324),B_325)
      | ~ r1_tarski(A_323,B_325)
      | r1_tarski(A_323,B_324) ) ),
    inference(resolution,[status(thm)],[c_6,c_123])).

tff(c_4491,plain,(
    ! [A_390,B_391,B_392,B_393] :
      ( r2_hidden('#skF_1'(A_390,B_391),B_392)
      | ~ r1_tarski(B_393,B_392)
      | ~ r1_tarski(A_390,B_393)
      | r1_tarski(A_390,B_391) ) ),
    inference(resolution,[status(thm)],[c_3954,c_2])).

tff(c_4501,plain,(
    ! [A_394,B_395] :
      ( r2_hidden('#skF_1'(A_394,B_395),'#skF_5')
      | ~ r1_tarski(A_394,'#skF_4')
      | r1_tarski(A_394,B_395) ) ),
    inference(resolution,[status(thm)],[c_28,c_4491])).

tff(c_4524,plain,(
    ! [A_396] :
      ( ~ r1_tarski(A_396,'#skF_4')
      | r1_tarski(A_396,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_4501,c_4])).

tff(c_3646,plain,(
    ! [A_303,B_304,B_305] :
      ( r2_hidden('#skF_2'(A_303,B_304),B_305)
      | ~ r1_tarski(B_304,B_305)
      | ~ r2_hidden(A_303,B_304) ) ),
    inference(resolution,[status(thm)],[c_12,c_123])).

tff(c_3666,plain,(
    ! [A_303,B_304,B_305] :
      ( v3_ordinal1('#skF_2'(A_303,B_304))
      | ~ v3_ordinal1(B_305)
      | ~ r1_tarski(B_304,B_305)
      | ~ r2_hidden(A_303,B_304) ) ),
    inference(resolution,[status(thm)],[c_3646,c_14])).

tff(c_4534,plain,(
    ! [A_303,A_396] :
      ( v3_ordinal1('#skF_2'(A_303,A_396))
      | ~ v3_ordinal1('#skF_5')
      | ~ r2_hidden(A_303,A_396)
      | ~ r1_tarski(A_396,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_4524,c_3666])).

tff(c_4559,plain,(
    ! [A_303,A_396] :
      ( v3_ordinal1('#skF_2'(A_303,A_396))
      | ~ r2_hidden(A_303,A_396)
      | ~ r1_tarski(A_396,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_4534])).

tff(c_3572,plain,(
    ! [D_293,A_294,B_295] :
      ( ~ r2_hidden(D_293,'#skF_2'(A_294,B_295))
      | ~ r2_hidden(D_293,B_295)
      | ~ r2_hidden(A_294,B_295) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_5880,plain,(
    ! [B_467,B_468,A_469] :
      ( ~ r2_hidden(B_467,B_468)
      | ~ r2_hidden(A_469,B_468)
      | r1_ordinal1('#skF_2'(A_469,B_468),B_467)
      | ~ v3_ordinal1(B_467)
      | ~ v3_ordinal1('#skF_2'(A_469,B_468)) ) ),
    inference(resolution,[status(thm)],[c_18,c_3572])).

tff(c_6016,plain,(
    ! [A_471,B_472] :
      ( ~ r2_hidden('#skF_2'(A_471,B_472),'#skF_4')
      | ~ r2_hidden('#skF_6'('#skF_2'(A_471,B_472)),B_472)
      | ~ r2_hidden(A_471,B_472)
      | ~ v3_ordinal1('#skF_6'('#skF_2'(A_471,B_472)))
      | ~ v3_ordinal1('#skF_2'(A_471,B_472)) ) ),
    inference(resolution,[status(thm)],[c_5880,c_32])).

tff(c_6680,plain,(
    ! [A_483] :
      ( ~ r2_hidden(A_483,'#skF_4')
      | ~ v3_ordinal1('#skF_6'('#skF_2'(A_483,'#skF_4')))
      | ~ r2_hidden('#skF_2'(A_483,'#skF_4'),'#skF_4')
      | ~ v3_ordinal1('#skF_2'(A_483,'#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_34,c_6016])).

tff(c_6763,plain,(
    ! [A_486] :
      ( ~ r2_hidden(A_486,'#skF_4')
      | ~ r2_hidden('#skF_2'(A_486,'#skF_4'),'#skF_4')
      | ~ v3_ordinal1('#skF_2'(A_486,'#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_36,c_6680])).

tff(c_6803,plain,(
    ! [A_487] :
      ( ~ v3_ordinal1('#skF_2'(A_487,'#skF_4'))
      | ~ r2_hidden(A_487,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_12,c_6763])).

tff(c_6807,plain,(
    ! [A_303] :
      ( ~ r2_hidden(A_303,'#skF_4')
      | ~ r1_tarski('#skF_4','#skF_4') ) ),
    inference(resolution,[status(thm)],[c_4559,c_6803])).

tff(c_6821,plain,(
    ! [A_488] : ~ r2_hidden(A_488,'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_77,c_6807])).

tff(c_6889,plain,(
    v3_ordinal1('#skF_4') ),
    inference(resolution,[status(thm)],[c_22,c_6821])).

tff(c_6910,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3541,c_6889])).

tff(c_6912,plain,(
    v3_ordinal1('#skF_4') ),
    inference(splitRight,[status(thm)],[c_3540])).

tff(c_7076,plain,(
    ! [B_508,A_509] :
      ( r2_hidden(B_508,A_509)
      | B_508 = A_509
      | r2_hidden(A_509,B_508)
      | ~ v3_ordinal1(B_508)
      | ~ v3_ordinal1(A_509) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_7086,plain,
    ( k1_xboole_0 = '#skF_4'
    | r2_hidden('#skF_4',k1_xboole_0)
    | ~ v3_ordinal1(k1_xboole_0)
    | ~ v3_ordinal1('#skF_4') ),
    inference(resolution,[status(thm)],[c_7076,c_3533])).

tff(c_7133,plain,
    ( k1_xboole_0 = '#skF_4'
    | r2_hidden('#skF_4',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6912,c_49,c_7086])).

tff(c_7135,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_26,c_7133])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:00:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.33/2.29  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.59/2.30  
% 6.59/2.30  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.59/2.30  %$ r2_hidden > r1_tarski > r1_ordinal1 > v3_ordinal1 > #nlpp > k1_xboole_0 > #skF_5 > #skF_4 > #skF_3 > #skF_2 > #skF_1 > #skF_6
% 6.59/2.30  
% 6.59/2.30  %Foreground sorts:
% 6.59/2.30  
% 6.59/2.30  
% 6.59/2.30  %Background operators:
% 6.59/2.30  
% 6.59/2.30  
% 6.59/2.30  %Foreground operators:
% 6.59/2.30  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.59/2.30  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 6.59/2.30  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 6.59/2.30  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.59/2.30  tff(r1_ordinal1, type, r1_ordinal1: ($i * $i) > $o).
% 6.59/2.30  tff('#skF_5', type, '#skF_5': $i).
% 6.59/2.30  tff(v3_ordinal1, type, v3_ordinal1: $i > $o).
% 6.59/2.30  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.59/2.30  tff('#skF_4', type, '#skF_4': $i).
% 6.59/2.30  tff('#skF_3', type, '#skF_3': $i > $i).
% 6.59/2.30  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.59/2.30  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 6.59/2.30  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 6.59/2.30  tff('#skF_6', type, '#skF_6': $i > $i).
% 6.59/2.30  
% 6.59/2.32  tff(f_34, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 6.59/2.32  tff(f_47, axiom, (![A, B]: ~(r2_hidden(A, B) & (![C]: ~(r2_hidden(C, B) & (![D]: ~(r2_hidden(D, B) & r2_hidden(D, C))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_tarski)).
% 6.59/2.32  tff(f_91, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 6.59/2.32  tff(f_113, negated_conjecture, ~(![A, B]: (v3_ordinal1(B) => ~((r1_tarski(A, B) & ~(A = k1_xboole_0)) & (![C]: (v3_ordinal1(C) => ~(r2_hidden(C, A) & (![D]: (v3_ordinal1(D) => (r2_hidden(D, A) => r1_ordinal1(C, D)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t32_ordinal1)).
% 6.59/2.32  tff(f_86, axiom, (![A]: ((![B]: (r2_hidden(B, A) => (v3_ordinal1(B) & r1_tarski(B, A)))) => v3_ordinal1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_ordinal1)).
% 6.59/2.32  tff(f_77, axiom, (![A]: (v3_ordinal1(A) => (![B]: (v3_ordinal1(B) => (r1_ordinal1(A, B) | r2_hidden(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t26_ordinal1)).
% 6.59/2.32  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 6.59/2.32  tff(f_53, axiom, (![A, B]: (v3_ordinal1(B) => (r2_hidden(A, B) => v3_ordinal1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t23_ordinal1)).
% 6.59/2.32  tff(f_68, axiom, (![A]: (v3_ordinal1(A) => (![B]: (v3_ordinal1(B) => ~((~r2_hidden(A, B) & ~(A = B)) & ~r2_hidden(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t24_ordinal1)).
% 6.59/2.32  tff(c_8, plain, (![A_6]: (r1_tarski(k1_xboole_0, A_6))), inference(cnfTransformation, [status(thm)], [f_34])).
% 6.59/2.32  tff(c_56, plain, (![A_39, B_40]: (r2_hidden('#skF_2'(A_39, B_40), B_40) | ~r2_hidden(A_39, B_40))), inference(cnfTransformation, [status(thm)], [f_47])).
% 6.59/2.32  tff(c_24, plain, (![B_25, A_24]: (~r1_tarski(B_25, A_24) | ~r2_hidden(A_24, B_25))), inference(cnfTransformation, [status(thm)], [f_91])).
% 6.59/2.32  tff(c_81, plain, (![B_46, A_47]: (~r1_tarski(B_46, '#skF_2'(A_47, B_46)) | ~r2_hidden(A_47, B_46))), inference(resolution, [status(thm)], [c_56, c_24])).
% 6.59/2.32  tff(c_86, plain, (![A_47]: (~r2_hidden(A_47, k1_xboole_0))), inference(resolution, [status(thm)], [c_8, c_81])).
% 6.59/2.32  tff(c_26, plain, (k1_xboole_0!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_113])).
% 6.59/2.32  tff(c_22, plain, (![A_22]: (r2_hidden('#skF_3'(A_22), A_22) | v3_ordinal1(A_22))), inference(cnfTransformation, [status(thm)], [f_86])).
% 6.59/2.32  tff(c_39, plain, (![B_33, A_34]: (~r1_tarski(B_33, A_34) | ~r2_hidden(A_34, B_33))), inference(cnfTransformation, [status(thm)], [f_91])).
% 6.59/2.32  tff(c_44, plain, (![A_35]: (~r1_tarski(A_35, '#skF_3'(A_35)) | v3_ordinal1(A_35))), inference(resolution, [status(thm)], [c_22, c_39])).
% 6.59/2.32  tff(c_49, plain, (v3_ordinal1(k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_44])).
% 6.59/2.32  tff(c_18, plain, (![B_21, A_19]: (r2_hidden(B_21, A_19) | r1_ordinal1(A_19, B_21) | ~v3_ordinal1(B_21) | ~v3_ordinal1(A_19))), inference(cnfTransformation, [status(thm)], [f_77])).
% 6.59/2.32  tff(c_36, plain, (![C_29]: (v3_ordinal1('#skF_6'(C_29)) | ~r2_hidden(C_29, '#skF_4') | ~v3_ordinal1(C_29))), inference(cnfTransformation, [status(thm)], [f_113])).
% 6.59/2.32  tff(c_168, plain, (![B_63, A_64]: (r2_hidden(B_63, A_64) | r1_ordinal1(A_64, B_63) | ~v3_ordinal1(B_63) | ~v3_ordinal1(A_64))), inference(cnfTransformation, [status(thm)], [f_77])).
% 6.59/2.32  tff(c_174, plain, (![B_63]: (r1_ordinal1(k1_xboole_0, B_63) | ~v3_ordinal1(B_63) | ~v3_ordinal1(k1_xboole_0))), inference(resolution, [status(thm)], [c_168, c_86])).
% 6.59/2.32  tff(c_192, plain, (![B_65]: (r1_ordinal1(k1_xboole_0, B_65) | ~v3_ordinal1(B_65))), inference(demodulation, [status(thm), theory('equality')], [c_49, c_174])).
% 6.59/2.32  tff(c_32, plain, (![C_29]: (~r1_ordinal1(C_29, '#skF_6'(C_29)) | ~r2_hidden(C_29, '#skF_4') | ~v3_ordinal1(C_29))), inference(cnfTransformation, [status(thm)], [f_113])).
% 6.59/2.32  tff(c_196, plain, (~r2_hidden(k1_xboole_0, '#skF_4') | ~v3_ordinal1(k1_xboole_0) | ~v3_ordinal1('#skF_6'(k1_xboole_0))), inference(resolution, [status(thm)], [c_192, c_32])).
% 6.59/2.32  tff(c_199, plain, (~r2_hidden(k1_xboole_0, '#skF_4') | ~v3_ordinal1('#skF_6'(k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_49, c_196])).
% 6.59/2.32  tff(c_200, plain, (~v3_ordinal1('#skF_6'(k1_xboole_0))), inference(splitLeft, [status(thm)], [c_199])).
% 6.59/2.32  tff(c_203, plain, (~r2_hidden(k1_xboole_0, '#skF_4') | ~v3_ordinal1(k1_xboole_0)), inference(resolution, [status(thm)], [c_36, c_200])).
% 6.59/2.32  tff(c_206, plain, (~r2_hidden(k1_xboole_0, '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_49, c_203])).
% 6.59/2.32  tff(c_226, plain, (r1_ordinal1('#skF_4', k1_xboole_0) | ~v3_ordinal1(k1_xboole_0) | ~v3_ordinal1('#skF_4')), inference(resolution, [status(thm)], [c_18, c_206])).
% 6.59/2.32  tff(c_229, plain, (r1_ordinal1('#skF_4', k1_xboole_0) | ~v3_ordinal1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_49, c_226])).
% 6.59/2.32  tff(c_230, plain, (~v3_ordinal1('#skF_4')), inference(splitLeft, [status(thm)], [c_229])).
% 6.59/2.32  tff(c_66, plain, (![A_43, B_44]: (r2_hidden('#skF_1'(A_43, B_44), A_43) | r1_tarski(A_43, B_44))), inference(cnfTransformation, [status(thm)], [f_32])).
% 6.59/2.32  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 6.59/2.32  tff(c_77, plain, (![A_43]: (r1_tarski(A_43, A_43))), inference(resolution, [status(thm)], [c_66, c_4])).
% 6.59/2.32  tff(c_30, plain, (v3_ordinal1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_113])).
% 6.59/2.32  tff(c_28, plain, (r1_tarski('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_113])).
% 6.59/2.32  tff(c_12, plain, (![A_7, B_8]: (r2_hidden('#skF_2'(A_7, B_8), B_8) | ~r2_hidden(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_47])).
% 6.59/2.32  tff(c_123, plain, (![C_54, B_55, A_56]: (r2_hidden(C_54, B_55) | ~r2_hidden(C_54, A_56) | ~r1_tarski(A_56, B_55))), inference(cnfTransformation, [status(thm)], [f_32])).
% 6.59/2.32  tff(c_318, plain, (![A_82, B_83, B_84]: (r2_hidden('#skF_2'(A_82, B_83), B_84) | ~r1_tarski(B_83, B_84) | ~r2_hidden(A_82, B_83))), inference(resolution, [status(thm)], [c_12, c_123])).
% 6.59/2.32  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 6.59/2.32  tff(c_1308, plain, (![A_173, B_174, B_175, B_176]: (r2_hidden('#skF_2'(A_173, B_174), B_175) | ~r1_tarski(B_176, B_175) | ~r1_tarski(B_174, B_176) | ~r2_hidden(A_173, B_174))), inference(resolution, [status(thm)], [c_318, c_2])).
% 6.59/2.32  tff(c_1318, plain, (![A_177, B_178]: (r2_hidden('#skF_2'(A_177, B_178), '#skF_5') | ~r1_tarski(B_178, '#skF_4') | ~r2_hidden(A_177, B_178))), inference(resolution, [status(thm)], [c_28, c_1308])).
% 6.59/2.32  tff(c_14, plain, (![A_14, B_15]: (v3_ordinal1(A_14) | ~r2_hidden(A_14, B_15) | ~v3_ordinal1(B_15))), inference(cnfTransformation, [status(thm)], [f_53])).
% 6.59/2.32  tff(c_1326, plain, (![A_177, B_178]: (v3_ordinal1('#skF_2'(A_177, B_178)) | ~v3_ordinal1('#skF_5') | ~r1_tarski(B_178, '#skF_4') | ~r2_hidden(A_177, B_178))), inference(resolution, [status(thm)], [c_1318, c_14])).
% 6.59/2.32  tff(c_1334, plain, (![A_177, B_178]: (v3_ordinal1('#skF_2'(A_177, B_178)) | ~r1_tarski(B_178, '#skF_4') | ~r2_hidden(A_177, B_178))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_1326])).
% 6.59/2.32  tff(c_134, plain, (![A_7, B_8, B_55]: (r2_hidden('#skF_2'(A_7, B_8), B_55) | ~r1_tarski(B_8, B_55) | ~r2_hidden(A_7, B_8))), inference(resolution, [status(thm)], [c_12, c_123])).
% 6.59/2.32  tff(c_34, plain, (![C_29]: (r2_hidden('#skF_6'(C_29), '#skF_4') | ~r2_hidden(C_29, '#skF_4') | ~v3_ordinal1(C_29))), inference(cnfTransformation, [status(thm)], [f_113])).
% 6.59/2.32  tff(c_232, plain, (![D_68, A_69, B_70]: (~r2_hidden(D_68, '#skF_2'(A_69, B_70)) | ~r2_hidden(D_68, B_70) | ~r2_hidden(A_69, B_70))), inference(cnfTransformation, [status(thm)], [f_47])).
% 6.59/2.32  tff(c_2203, plain, (![B_248, B_249, A_250]: (~r2_hidden(B_248, B_249) | ~r2_hidden(A_250, B_249) | r1_ordinal1('#skF_2'(A_250, B_249), B_248) | ~v3_ordinal1(B_248) | ~v3_ordinal1('#skF_2'(A_250, B_249)))), inference(resolution, [status(thm)], [c_18, c_232])).
% 6.59/2.32  tff(c_2442, plain, (![A_253, B_254]: (~r2_hidden('#skF_2'(A_253, B_254), '#skF_4') | ~r2_hidden('#skF_6'('#skF_2'(A_253, B_254)), B_254) | ~r2_hidden(A_253, B_254) | ~v3_ordinal1('#skF_6'('#skF_2'(A_253, B_254))) | ~v3_ordinal1('#skF_2'(A_253, B_254)))), inference(resolution, [status(thm)], [c_2203, c_32])).
% 6.59/2.32  tff(c_2993, plain, (![A_263]: (~r2_hidden(A_263, '#skF_4') | ~v3_ordinal1('#skF_6'('#skF_2'(A_263, '#skF_4'))) | ~r2_hidden('#skF_2'(A_263, '#skF_4'), '#skF_4') | ~v3_ordinal1('#skF_2'(A_263, '#skF_4')))), inference(resolution, [status(thm)], [c_34, c_2442])).
% 6.59/2.32  tff(c_3206, plain, (![A_265]: (~r2_hidden(A_265, '#skF_4') | ~r2_hidden('#skF_2'(A_265, '#skF_4'), '#skF_4') | ~v3_ordinal1('#skF_2'(A_265, '#skF_4')))), inference(resolution, [status(thm)], [c_36, c_2993])).
% 6.59/2.32  tff(c_3226, plain, (![A_7]: (~v3_ordinal1('#skF_2'(A_7, '#skF_4')) | ~r1_tarski('#skF_4', '#skF_4') | ~r2_hidden(A_7, '#skF_4'))), inference(resolution, [status(thm)], [c_134, c_3206])).
% 6.59/2.32  tff(c_3246, plain, (![A_266]: (~v3_ordinal1('#skF_2'(A_266, '#skF_4')) | ~r2_hidden(A_266, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_77, c_3226])).
% 6.59/2.32  tff(c_3250, plain, (![A_177]: (~r1_tarski('#skF_4', '#skF_4') | ~r2_hidden(A_177, '#skF_4'))), inference(resolution, [status(thm)], [c_1334, c_3246])).
% 6.59/2.32  tff(c_3264, plain, (![A_267]: (~r2_hidden(A_267, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_77, c_3250])).
% 6.59/2.32  tff(c_3328, plain, (v3_ordinal1('#skF_4')), inference(resolution, [status(thm)], [c_22, c_3264])).
% 6.59/2.32  tff(c_3348, plain, $false, inference(negUnitSimplification, [status(thm)], [c_230, c_3328])).
% 6.59/2.32  tff(c_3350, plain, (v3_ordinal1('#skF_4')), inference(splitRight, [status(thm)], [c_229])).
% 6.59/2.32  tff(c_3480, plain, (![B_285, A_286]: (r2_hidden(B_285, A_286) | B_285=A_286 | r2_hidden(A_286, B_285) | ~v3_ordinal1(B_285) | ~v3_ordinal1(A_286))), inference(cnfTransformation, [status(thm)], [f_68])).
% 6.59/2.32  tff(c_3487, plain, (k1_xboole_0='#skF_4' | r2_hidden('#skF_4', k1_xboole_0) | ~v3_ordinal1(k1_xboole_0) | ~v3_ordinal1('#skF_4')), inference(resolution, [status(thm)], [c_3480, c_206])).
% 6.59/2.32  tff(c_3530, plain, (k1_xboole_0='#skF_4' | r2_hidden('#skF_4', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_3350, c_49, c_3487])).
% 6.59/2.32  tff(c_3532, plain, $false, inference(negUnitSimplification, [status(thm)], [c_86, c_26, c_3530])).
% 6.59/2.32  tff(c_3533, plain, (~r2_hidden(k1_xboole_0, '#skF_4')), inference(splitRight, [status(thm)], [c_199])).
% 6.59/2.32  tff(c_3537, plain, (r1_ordinal1('#skF_4', k1_xboole_0) | ~v3_ordinal1(k1_xboole_0) | ~v3_ordinal1('#skF_4')), inference(resolution, [status(thm)], [c_18, c_3533])).
% 6.59/2.32  tff(c_3540, plain, (r1_ordinal1('#skF_4', k1_xboole_0) | ~v3_ordinal1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_49, c_3537])).
% 6.59/2.32  tff(c_3541, plain, (~v3_ordinal1('#skF_4')), inference(splitLeft, [status(thm)], [c_3540])).
% 6.59/2.32  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 6.59/2.32  tff(c_3954, plain, (![A_323, B_324, B_325]: (r2_hidden('#skF_1'(A_323, B_324), B_325) | ~r1_tarski(A_323, B_325) | r1_tarski(A_323, B_324))), inference(resolution, [status(thm)], [c_6, c_123])).
% 6.59/2.32  tff(c_4491, plain, (![A_390, B_391, B_392, B_393]: (r2_hidden('#skF_1'(A_390, B_391), B_392) | ~r1_tarski(B_393, B_392) | ~r1_tarski(A_390, B_393) | r1_tarski(A_390, B_391))), inference(resolution, [status(thm)], [c_3954, c_2])).
% 6.59/2.32  tff(c_4501, plain, (![A_394, B_395]: (r2_hidden('#skF_1'(A_394, B_395), '#skF_5') | ~r1_tarski(A_394, '#skF_4') | r1_tarski(A_394, B_395))), inference(resolution, [status(thm)], [c_28, c_4491])).
% 6.59/2.32  tff(c_4524, plain, (![A_396]: (~r1_tarski(A_396, '#skF_4') | r1_tarski(A_396, '#skF_5'))), inference(resolution, [status(thm)], [c_4501, c_4])).
% 6.59/2.32  tff(c_3646, plain, (![A_303, B_304, B_305]: (r2_hidden('#skF_2'(A_303, B_304), B_305) | ~r1_tarski(B_304, B_305) | ~r2_hidden(A_303, B_304))), inference(resolution, [status(thm)], [c_12, c_123])).
% 6.59/2.32  tff(c_3666, plain, (![A_303, B_304, B_305]: (v3_ordinal1('#skF_2'(A_303, B_304)) | ~v3_ordinal1(B_305) | ~r1_tarski(B_304, B_305) | ~r2_hidden(A_303, B_304))), inference(resolution, [status(thm)], [c_3646, c_14])).
% 6.59/2.32  tff(c_4534, plain, (![A_303, A_396]: (v3_ordinal1('#skF_2'(A_303, A_396)) | ~v3_ordinal1('#skF_5') | ~r2_hidden(A_303, A_396) | ~r1_tarski(A_396, '#skF_4'))), inference(resolution, [status(thm)], [c_4524, c_3666])).
% 6.59/2.32  tff(c_4559, plain, (![A_303, A_396]: (v3_ordinal1('#skF_2'(A_303, A_396)) | ~r2_hidden(A_303, A_396) | ~r1_tarski(A_396, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_4534])).
% 6.59/2.32  tff(c_3572, plain, (![D_293, A_294, B_295]: (~r2_hidden(D_293, '#skF_2'(A_294, B_295)) | ~r2_hidden(D_293, B_295) | ~r2_hidden(A_294, B_295))), inference(cnfTransformation, [status(thm)], [f_47])).
% 6.59/2.32  tff(c_5880, plain, (![B_467, B_468, A_469]: (~r2_hidden(B_467, B_468) | ~r2_hidden(A_469, B_468) | r1_ordinal1('#skF_2'(A_469, B_468), B_467) | ~v3_ordinal1(B_467) | ~v3_ordinal1('#skF_2'(A_469, B_468)))), inference(resolution, [status(thm)], [c_18, c_3572])).
% 6.59/2.32  tff(c_6016, plain, (![A_471, B_472]: (~r2_hidden('#skF_2'(A_471, B_472), '#skF_4') | ~r2_hidden('#skF_6'('#skF_2'(A_471, B_472)), B_472) | ~r2_hidden(A_471, B_472) | ~v3_ordinal1('#skF_6'('#skF_2'(A_471, B_472))) | ~v3_ordinal1('#skF_2'(A_471, B_472)))), inference(resolution, [status(thm)], [c_5880, c_32])).
% 6.59/2.32  tff(c_6680, plain, (![A_483]: (~r2_hidden(A_483, '#skF_4') | ~v3_ordinal1('#skF_6'('#skF_2'(A_483, '#skF_4'))) | ~r2_hidden('#skF_2'(A_483, '#skF_4'), '#skF_4') | ~v3_ordinal1('#skF_2'(A_483, '#skF_4')))), inference(resolution, [status(thm)], [c_34, c_6016])).
% 6.59/2.32  tff(c_6763, plain, (![A_486]: (~r2_hidden(A_486, '#skF_4') | ~r2_hidden('#skF_2'(A_486, '#skF_4'), '#skF_4') | ~v3_ordinal1('#skF_2'(A_486, '#skF_4')))), inference(resolution, [status(thm)], [c_36, c_6680])).
% 6.59/2.32  tff(c_6803, plain, (![A_487]: (~v3_ordinal1('#skF_2'(A_487, '#skF_4')) | ~r2_hidden(A_487, '#skF_4'))), inference(resolution, [status(thm)], [c_12, c_6763])).
% 6.59/2.32  tff(c_6807, plain, (![A_303]: (~r2_hidden(A_303, '#skF_4') | ~r1_tarski('#skF_4', '#skF_4'))), inference(resolution, [status(thm)], [c_4559, c_6803])).
% 6.59/2.32  tff(c_6821, plain, (![A_488]: (~r2_hidden(A_488, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_77, c_6807])).
% 6.59/2.32  tff(c_6889, plain, (v3_ordinal1('#skF_4')), inference(resolution, [status(thm)], [c_22, c_6821])).
% 6.59/2.32  tff(c_6910, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3541, c_6889])).
% 6.59/2.32  tff(c_6912, plain, (v3_ordinal1('#skF_4')), inference(splitRight, [status(thm)], [c_3540])).
% 6.59/2.32  tff(c_7076, plain, (![B_508, A_509]: (r2_hidden(B_508, A_509) | B_508=A_509 | r2_hidden(A_509, B_508) | ~v3_ordinal1(B_508) | ~v3_ordinal1(A_509))), inference(cnfTransformation, [status(thm)], [f_68])).
% 6.59/2.32  tff(c_7086, plain, (k1_xboole_0='#skF_4' | r2_hidden('#skF_4', k1_xboole_0) | ~v3_ordinal1(k1_xboole_0) | ~v3_ordinal1('#skF_4')), inference(resolution, [status(thm)], [c_7076, c_3533])).
% 6.59/2.32  tff(c_7133, plain, (k1_xboole_0='#skF_4' | r2_hidden('#skF_4', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_6912, c_49, c_7086])).
% 6.59/2.32  tff(c_7135, plain, $false, inference(negUnitSimplification, [status(thm)], [c_86, c_26, c_7133])).
% 6.59/2.32  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.59/2.32  
% 6.59/2.32  Inference rules
% 6.59/2.32  ----------------------
% 6.59/2.32  #Ref     : 0
% 6.59/2.32  #Sup     : 1515
% 6.59/2.32  #Fact    : 8
% 6.59/2.32  #Define  : 0
% 6.59/2.32  #Split   : 23
% 6.59/2.32  #Chain   : 0
% 6.59/2.32  #Close   : 0
% 6.59/2.32  
% 6.59/2.32  Ordering : KBO
% 6.59/2.32  
% 6.59/2.32  Simplification rules
% 6.59/2.32  ----------------------
% 6.59/2.32  #Subsume      : 748
% 6.59/2.32  #Demod        : 635
% 6.59/2.32  #Tautology    : 216
% 6.59/2.32  #SimpNegUnit  : 67
% 6.59/2.32  #BackRed      : 3
% 6.59/2.32  
% 6.59/2.32  #Partial instantiations: 0
% 6.59/2.32  #Strategies tried      : 1
% 6.59/2.32  
% 6.59/2.32  Timing (in seconds)
% 6.59/2.32  ----------------------
% 6.59/2.32  Preprocessing        : 0.29
% 6.59/2.32  Parsing              : 0.16
% 6.59/2.32  CNF conversion       : 0.02
% 6.59/2.32  Main loop            : 1.26
% 6.59/2.32  Inferencing          : 0.41
% 6.59/2.32  Reduction            : 0.34
% 6.59/2.32  Demodulation         : 0.22
% 6.59/2.32  BG Simplification    : 0.04
% 6.59/2.32  Subsumption          : 0.39
% 6.59/2.32  Abstraction          : 0.05
% 6.59/2.32  MUC search           : 0.00
% 6.59/2.32  Cooper               : 0.00
% 6.59/2.32  Total                : 1.59
% 6.59/2.32  Index Insertion      : 0.00
% 6.59/2.32  Index Deletion       : 0.00
% 6.59/2.32  Index Matching       : 0.00
% 6.59/2.32  BG Taut test         : 0.00
%------------------------------------------------------------------------------
