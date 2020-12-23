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
% DateTime   : Thu Dec  3 09:53:50 EST 2020

% Result     : Theorem 3.72s
% Output     : CNFRefutation 3.87s
% Verified   : 
% Statistics : Number of formulae       :  117 ( 378 expanded)
%              Number of leaves         :   27 ( 135 expanded)
%              Depth                    :   13
%              Number of atoms          :  164 ( 723 expanded)
%              Number of equality atoms :   33 ( 183 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_xboole_0 > r2_hidden > r1_xboole_0 > r1_tarski > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_3 > #skF_5 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff(r2_xboole_0,type,(
    r2_xboole_0: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_88,negated_conjecture,(
    ~ ! [A,B] :
        ( k2_zfmisc_1(A,B) = k2_zfmisc_1(B,A)
       => ( A = k1_xboole_0
          | B = k1_xboole_0
          | A = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t114_zfmisc_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_71,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_67,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_73,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_69,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( r2_xboole_0(A,B)
    <=> ( r1_tarski(A,B)
        & A != B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_xboole_0)).

tff(f_63,axiom,(
    ! [A,B] :
      ~ ( r2_xboole_0(A,B)
        & ! [C] :
            ~ ( r2_hidden(C,B)
              & ~ r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_xboole_0)).

tff(f_79,axiom,(
    ! [A,B,C,D] :
      ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(C,D))
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,D) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l54_zfmisc_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

tff(c_38,plain,(
    '#skF_5' != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_28,plain,(
    ! [A_20] : k4_xboole_0(A_20,k1_xboole_0) = A_20 ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_163,plain,(
    ! [A_49,B_50] :
      ( r2_hidden('#skF_1'(A_49,B_50),A_49)
      | r1_tarski(A_49,B_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_170,plain,(
    ! [A_51] : r1_tarski(A_51,A_51) ),
    inference(resolution,[status(thm)],[c_163,c_4])).

tff(c_24,plain,(
    ! [A_16,B_17] :
      ( k4_xboole_0(A_16,B_17) = k1_xboole_0
      | ~ r1_tarski(A_16,B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_176,plain,(
    ! [A_52] : k4_xboole_0(A_52,A_52) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_170,c_24])).

tff(c_30,plain,(
    ! [A_21,B_22] : k4_xboole_0(A_21,k4_xboole_0(A_21,B_22)) = k3_xboole_0(A_21,B_22) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_181,plain,(
    ! [A_52] : k4_xboole_0(A_52,k1_xboole_0) = k3_xboole_0(A_52,A_52) ),
    inference(superposition,[status(thm),theory(equality)],[c_176,c_30])).

tff(c_193,plain,(
    ! [A_52] : k3_xboole_0(A_52,A_52) = A_52 ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_181])).

tff(c_174,plain,(
    ! [A_51] : k4_xboole_0(A_51,A_51) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_170,c_24])).

tff(c_107,plain,(
    ! [A_42,B_43] : k4_xboole_0(A_42,k4_xboole_0(A_42,B_43)) = k3_xboole_0(A_42,B_43) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_125,plain,(
    ! [A_20] : k4_xboole_0(A_20,A_20) = k3_xboole_0(A_20,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_107])).

tff(c_197,plain,(
    ! [A_53] : k3_xboole_0(A_53,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_174,c_125])).

tff(c_26,plain,(
    ! [A_18,B_19] : r1_tarski(k3_xboole_0(A_18,B_19),A_18) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_208,plain,(
    ! [A_53] : r1_tarski(k1_xboole_0,A_53) ),
    inference(superposition,[status(thm),theory(equality)],[c_197,c_26])).

tff(c_8,plain,(
    ! [A_6,B_7] :
      ( r2_xboole_0(A_6,B_7)
      | B_7 = A_6
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_20,plain,(
    ! [A_13,B_14] :
      ( r2_hidden('#skF_3'(A_13,B_14),B_14)
      | ~ r2_xboole_0(A_13,B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_40,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_710,plain,(
    ! [A_110,B_111,C_112,D_113] :
      ( r2_hidden(k4_tarski(A_110,B_111),k2_zfmisc_1(C_112,D_113))
      | ~ r2_hidden(B_111,D_113)
      | ~ r2_hidden(A_110,C_112) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_44,plain,(
    k2_zfmisc_1('#skF_5','#skF_4') = k2_zfmisc_1('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_479,plain,(
    ! [A_90,C_91,B_92,D_93] :
      ( r2_hidden(A_90,C_91)
      | ~ r2_hidden(k4_tarski(A_90,B_92),k2_zfmisc_1(C_91,D_93)) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_482,plain,(
    ! [A_90,B_92] :
      ( r2_hidden(A_90,'#skF_5')
      | ~ r2_hidden(k4_tarski(A_90,B_92),k2_zfmisc_1('#skF_4','#skF_5')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_479])).

tff(c_730,plain,(
    ! [A_110,B_111] :
      ( r2_hidden(A_110,'#skF_5')
      | ~ r2_hidden(B_111,'#skF_5')
      | ~ r2_hidden(A_110,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_710,c_482])).

tff(c_832,plain,(
    ! [B_122] : ~ r2_hidden(B_122,'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_730])).

tff(c_848,plain,(
    ! [B_123] : r1_tarski('#skF_5',B_123) ),
    inference(resolution,[status(thm)],[c_6,c_832])).

tff(c_175,plain,(
    ! [A_20] : k3_xboole_0(A_20,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_174,c_125])).

tff(c_306,plain,(
    ! [A_59,B_60,C_61] :
      ( ~ r1_xboole_0(A_59,B_60)
      | ~ r2_hidden(C_61,k3_xboole_0(A_59,B_60)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_312,plain,(
    ! [A_20,C_61] :
      ( ~ r1_xboole_0(A_20,k1_xboole_0)
      | ~ r2_hidden(C_61,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_175,c_306])).

tff(c_334,plain,(
    ! [C_65] : ~ r2_hidden(C_65,k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_312])).

tff(c_346,plain,(
    ! [A_66] : ~ r2_xboole_0(A_66,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_20,c_334])).

tff(c_351,plain,(
    ! [A_6] :
      ( k1_xboole_0 = A_6
      | ~ r1_tarski(A_6,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_8,c_346])).

tff(c_852,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_848,c_351])).

tff(c_859,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_852])).

tff(c_861,plain,(
    ! [A_124] :
      ( r2_hidden(A_124,'#skF_5')
      | ~ r2_hidden(A_124,'#skF_4') ) ),
    inference(splitRight,[status(thm)],[c_730])).

tff(c_18,plain,(
    ! [A_13,B_14] :
      ( ~ r2_hidden('#skF_3'(A_13,B_14),A_13)
      | ~ r2_xboole_0(A_13,B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_875,plain,(
    ! [B_125] :
      ( ~ r2_xboole_0('#skF_5',B_125)
      | ~ r2_hidden('#skF_3'('#skF_5',B_125),'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_861,c_18])).

tff(c_880,plain,(
    ~ r2_xboole_0('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_20,c_875])).

tff(c_933,plain,
    ( '#skF_5' = '#skF_4'
    | ~ r1_tarski('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_8,c_880])).

tff(c_936,plain,(
    ~ r1_tarski('#skF_5','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_933])).

tff(c_42,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_377,plain,(
    ! [B_68,D_69,A_70,C_71] :
      ( r2_hidden(B_68,D_69)
      | ~ r2_hidden(k4_tarski(A_70,B_68),k2_zfmisc_1(C_71,D_69)) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_380,plain,(
    ! [B_68,A_70] :
      ( r2_hidden(B_68,'#skF_4')
      | ~ r2_hidden(k4_tarski(A_70,B_68),k2_zfmisc_1('#skF_4','#skF_5')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_377])).

tff(c_732,plain,(
    ! [B_111,A_110] :
      ( r2_hidden(B_111,'#skF_4')
      | ~ r2_hidden(B_111,'#skF_5')
      | ~ r2_hidden(A_110,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_710,c_380])).

tff(c_943,plain,(
    ! [A_128] : ~ r2_hidden(A_128,'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_732])).

tff(c_959,plain,(
    ! [B_129] : r1_tarski('#skF_4',B_129) ),
    inference(resolution,[status(thm)],[c_6,c_943])).

tff(c_963,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_959,c_351])).

tff(c_970,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_963])).

tff(c_972,plain,(
    ! [B_130] :
      ( r2_hidden(B_130,'#skF_4')
      | ~ r2_hidden(B_130,'#skF_5') ) ),
    inference(splitRight,[status(thm)],[c_732])).

tff(c_1762,plain,(
    ! [B_176] :
      ( r2_hidden('#skF_1'('#skF_5',B_176),'#skF_4')
      | r1_tarski('#skF_5',B_176) ) ),
    inference(resolution,[status(thm)],[c_6,c_972])).

tff(c_1775,plain,(
    r1_tarski('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_1762,c_4])).

tff(c_1783,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_936,c_936,c_1775])).

tff(c_1784,plain,(
    ! [A_20] : ~ r1_xboole_0(A_20,k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_312])).

tff(c_2350,plain,(
    ! [A_258,B_259] :
      ( r2_hidden('#skF_2'(A_258,B_259),k3_xboole_0(A_258,B_259))
      | r1_xboole_0(A_258,B_259) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_2367,plain,(
    ! [A_20] :
      ( r2_hidden('#skF_2'(A_20,k1_xboole_0),k1_xboole_0)
      | r1_xboole_0(A_20,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_175,c_2350])).

tff(c_2395,plain,(
    ! [A_264] : r2_hidden('#skF_2'(A_264,k1_xboole_0),k1_xboole_0) ),
    inference(negUnitSimplification,[status(thm)],[c_1784,c_2367])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_2397,plain,(
    ! [A_264,B_2] :
      ( r2_hidden('#skF_2'(A_264,k1_xboole_0),B_2)
      | ~ r1_tarski(k1_xboole_0,B_2) ) ),
    inference(resolution,[status(thm)],[c_2395,c_2])).

tff(c_2408,plain,(
    ! [A_266,B_267] : r2_hidden('#skF_2'(A_266,k1_xboole_0),B_267) ),
    inference(demodulation,[status(thm),theory(equality)],[c_208,c_2397])).

tff(c_16,plain,(
    ! [A_8,B_9,C_12] :
      ( ~ r1_xboole_0(A_8,B_9)
      | ~ r2_hidden(C_12,k3_xboole_0(A_8,B_9)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_2416,plain,(
    ! [A_8,B_9] : ~ r1_xboole_0(A_8,B_9) ),
    inference(resolution,[status(thm)],[c_2408,c_16])).

tff(c_14,plain,(
    ! [A_8,B_9] :
      ( r2_hidden('#skF_2'(A_8,B_9),k3_xboole_0(A_8,B_9))
      | r1_xboole_0(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_2431,plain,(
    ! [A_274,B_275] : r2_hidden('#skF_2'(A_274,B_275),k3_xboole_0(A_274,B_275)) ),
    inference(negUnitSimplification,[status(thm)],[c_2416,c_14])).

tff(c_2439,plain,(
    ! [A_52] : r2_hidden('#skF_2'(A_52,A_52),A_52) ),
    inference(superposition,[status(thm),theory(equality)],[c_193,c_2431])).

tff(c_2375,plain,(
    ! [A_260,B_261,C_262,D_263] :
      ( r2_hidden(k4_tarski(A_260,B_261),k2_zfmisc_1(C_262,D_263))
      | ~ r2_hidden(B_261,D_263)
      | ~ r2_hidden(A_260,C_262) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_2124,plain,(
    ! [B_227,D_228,A_229,C_230] :
      ( r2_hidden(B_227,D_228)
      | ~ r2_hidden(k4_tarski(A_229,B_227),k2_zfmisc_1(C_230,D_228)) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_2127,plain,(
    ! [B_227,A_229] :
      ( r2_hidden(B_227,'#skF_4')
      | ~ r2_hidden(k4_tarski(A_229,B_227),k2_zfmisc_1('#skF_4','#skF_5')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_2124])).

tff(c_2391,plain,(
    ! [B_261,A_260] :
      ( r2_hidden(B_261,'#skF_4')
      | ~ r2_hidden(B_261,'#skF_5')
      | ~ r2_hidden(A_260,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_2375,c_2127])).

tff(c_2499,plain,(
    ! [A_281] : ~ r2_hidden(A_281,'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_2391])).

tff(c_2523,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_2439,c_2499])).

tff(c_2545,plain,(
    ! [B_284] :
      ( r2_hidden(B_284,'#skF_4')
      | ~ r2_hidden(B_284,'#skF_5') ) ),
    inference(splitRight,[status(thm)],[c_2391])).

tff(c_2581,plain,(
    ! [B_285] :
      ( r2_hidden('#skF_1'('#skF_5',B_285),'#skF_4')
      | r1_tarski('#skF_5',B_285) ) ),
    inference(resolution,[status(thm)],[c_6,c_2545])).

tff(c_2589,plain,(
    r1_tarski('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_2581,c_4])).

tff(c_2525,plain,(
    ! [A_282,B_283] :
      ( r2_hidden(k4_tarski(A_282,B_283),k2_zfmisc_1('#skF_4','#skF_5'))
      | ~ r2_hidden(B_283,'#skF_4')
      | ~ r2_hidden(A_282,'#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_2375])).

tff(c_34,plain,(
    ! [B_24,D_26,A_23,C_25] :
      ( r2_hidden(B_24,D_26)
      | ~ r2_hidden(k4_tarski(A_23,B_24),k2_zfmisc_1(C_25,D_26)) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_2543,plain,(
    ! [B_283,A_282] :
      ( r2_hidden(B_283,'#skF_5')
      | ~ r2_hidden(B_283,'#skF_4')
      | ~ r2_hidden(A_282,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_2525,c_34])).

tff(c_2636,plain,(
    ! [A_282] : ~ r2_hidden(A_282,'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_2543])).

tff(c_2593,plain,(
    k4_xboole_0('#skF_5','#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2589,c_24])).

tff(c_2597,plain,(
    k4_xboole_0('#skF_5',k1_xboole_0) = k3_xboole_0('#skF_5','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_2593,c_30])).

tff(c_2600,plain,(
    k3_xboole_0('#skF_5','#skF_4') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_2597])).

tff(c_2423,plain,(
    ! [A_8,B_9] : r2_hidden('#skF_2'(A_8,B_9),k3_xboole_0(A_8,B_9)) ),
    inference(negUnitSimplification,[status(thm)],[c_2416,c_14])).

tff(c_2609,plain,(
    r2_hidden('#skF_2'('#skF_5','#skF_4'),'#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_2600,c_2423])).

tff(c_2639,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2636,c_2609])).

tff(c_2641,plain,(
    ! [B_286] :
      ( r2_hidden(B_286,'#skF_5')
      | ~ r2_hidden(B_286,'#skF_4') ) ),
    inference(splitRight,[status(thm)],[c_2543])).

tff(c_2687,plain,(
    ! [B_291] :
      ( ~ r2_xboole_0('#skF_5',B_291)
      | ~ r2_hidden('#skF_3'('#skF_5',B_291),'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_2641,c_18])).

tff(c_2697,plain,(
    ~ r2_xboole_0('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_20,c_2687])).

tff(c_2700,plain,
    ( '#skF_5' = '#skF_4'
    | ~ r1_tarski('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_8,c_2697])).

tff(c_2703,plain,(
    '#skF_5' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2589,c_2700])).

tff(c_2705,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_2703])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n025.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 17:20:20 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.72/1.61  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.72/1.62  
% 3.72/1.62  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.72/1.62  %$ r2_xboole_0 > r2_hidden > r1_xboole_0 > r1_tarski > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_3 > #skF_5 > #skF_4 > #skF_2 > #skF_1
% 3.72/1.62  
% 3.72/1.62  %Foreground sorts:
% 3.72/1.62  
% 3.72/1.62  
% 3.72/1.62  %Background operators:
% 3.72/1.62  
% 3.72/1.62  
% 3.72/1.62  %Foreground operators:
% 3.72/1.62  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.72/1.62  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.72/1.62  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.72/1.62  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 3.72/1.62  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.72/1.62  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 3.72/1.62  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.72/1.62  tff('#skF_5', type, '#skF_5': $i).
% 3.72/1.62  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.72/1.62  tff(r2_xboole_0, type, r2_xboole_0: ($i * $i) > $o).
% 3.72/1.62  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.72/1.62  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.72/1.62  tff('#skF_4', type, '#skF_4': $i).
% 3.72/1.62  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.72/1.62  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.72/1.62  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.72/1.62  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.72/1.62  
% 3.87/1.64  tff(f_88, negated_conjecture, ~(![A, B]: ((k2_zfmisc_1(A, B) = k2_zfmisc_1(B, A)) => (((A = k1_xboole_0) | (B = k1_xboole_0)) | (A = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t114_zfmisc_1)).
% 3.87/1.64  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 3.87/1.64  tff(f_71, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 3.87/1.64  tff(f_67, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 3.87/1.64  tff(f_73, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 3.87/1.64  tff(f_69, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 3.87/1.64  tff(f_39, axiom, (![A, B]: (r2_xboole_0(A, B) <=> (r1_tarski(A, B) & ~(A = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_xboole_0)).
% 3.87/1.64  tff(f_63, axiom, (![A, B]: ~(r2_xboole_0(A, B) & (![C]: ~(r2_hidden(C, B) & ~r2_hidden(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_xboole_0)).
% 3.87/1.64  tff(f_79, axiom, (![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(C, D)) <=> (r2_hidden(A, C) & r2_hidden(B, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l54_zfmisc_1)).
% 3.87/1.64  tff(f_53, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 3.87/1.64  tff(c_38, plain, ('#skF_5'!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.87/1.64  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.87/1.64  tff(c_28, plain, (![A_20]: (k4_xboole_0(A_20, k1_xboole_0)=A_20)), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.87/1.64  tff(c_163, plain, (![A_49, B_50]: (r2_hidden('#skF_1'(A_49, B_50), A_49) | r1_tarski(A_49, B_50))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.87/1.64  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.87/1.64  tff(c_170, plain, (![A_51]: (r1_tarski(A_51, A_51))), inference(resolution, [status(thm)], [c_163, c_4])).
% 3.87/1.64  tff(c_24, plain, (![A_16, B_17]: (k4_xboole_0(A_16, B_17)=k1_xboole_0 | ~r1_tarski(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.87/1.64  tff(c_176, plain, (![A_52]: (k4_xboole_0(A_52, A_52)=k1_xboole_0)), inference(resolution, [status(thm)], [c_170, c_24])).
% 3.87/1.64  tff(c_30, plain, (![A_21, B_22]: (k4_xboole_0(A_21, k4_xboole_0(A_21, B_22))=k3_xboole_0(A_21, B_22))), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.87/1.64  tff(c_181, plain, (![A_52]: (k4_xboole_0(A_52, k1_xboole_0)=k3_xboole_0(A_52, A_52))), inference(superposition, [status(thm), theory('equality')], [c_176, c_30])).
% 3.87/1.64  tff(c_193, plain, (![A_52]: (k3_xboole_0(A_52, A_52)=A_52)), inference(demodulation, [status(thm), theory('equality')], [c_28, c_181])).
% 3.87/1.64  tff(c_174, plain, (![A_51]: (k4_xboole_0(A_51, A_51)=k1_xboole_0)), inference(resolution, [status(thm)], [c_170, c_24])).
% 3.87/1.64  tff(c_107, plain, (![A_42, B_43]: (k4_xboole_0(A_42, k4_xboole_0(A_42, B_43))=k3_xboole_0(A_42, B_43))), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.87/1.64  tff(c_125, plain, (![A_20]: (k4_xboole_0(A_20, A_20)=k3_xboole_0(A_20, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_28, c_107])).
% 3.87/1.64  tff(c_197, plain, (![A_53]: (k3_xboole_0(A_53, k1_xboole_0)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_174, c_125])).
% 3.87/1.64  tff(c_26, plain, (![A_18, B_19]: (r1_tarski(k3_xboole_0(A_18, B_19), A_18))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.87/1.64  tff(c_208, plain, (![A_53]: (r1_tarski(k1_xboole_0, A_53))), inference(superposition, [status(thm), theory('equality')], [c_197, c_26])).
% 3.87/1.64  tff(c_8, plain, (![A_6, B_7]: (r2_xboole_0(A_6, B_7) | B_7=A_6 | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.87/1.64  tff(c_20, plain, (![A_13, B_14]: (r2_hidden('#skF_3'(A_13, B_14), B_14) | ~r2_xboole_0(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.87/1.64  tff(c_40, plain, (k1_xboole_0!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.87/1.64  tff(c_710, plain, (![A_110, B_111, C_112, D_113]: (r2_hidden(k4_tarski(A_110, B_111), k2_zfmisc_1(C_112, D_113)) | ~r2_hidden(B_111, D_113) | ~r2_hidden(A_110, C_112))), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.87/1.64  tff(c_44, plain, (k2_zfmisc_1('#skF_5', '#skF_4')=k2_zfmisc_1('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.87/1.64  tff(c_479, plain, (![A_90, C_91, B_92, D_93]: (r2_hidden(A_90, C_91) | ~r2_hidden(k4_tarski(A_90, B_92), k2_zfmisc_1(C_91, D_93)))), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.87/1.64  tff(c_482, plain, (![A_90, B_92]: (r2_hidden(A_90, '#skF_5') | ~r2_hidden(k4_tarski(A_90, B_92), k2_zfmisc_1('#skF_4', '#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_44, c_479])).
% 3.87/1.64  tff(c_730, plain, (![A_110, B_111]: (r2_hidden(A_110, '#skF_5') | ~r2_hidden(B_111, '#skF_5') | ~r2_hidden(A_110, '#skF_4'))), inference(resolution, [status(thm)], [c_710, c_482])).
% 3.87/1.64  tff(c_832, plain, (![B_122]: (~r2_hidden(B_122, '#skF_5'))), inference(splitLeft, [status(thm)], [c_730])).
% 3.87/1.64  tff(c_848, plain, (![B_123]: (r1_tarski('#skF_5', B_123))), inference(resolution, [status(thm)], [c_6, c_832])).
% 3.87/1.64  tff(c_175, plain, (![A_20]: (k3_xboole_0(A_20, k1_xboole_0)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_174, c_125])).
% 3.87/1.64  tff(c_306, plain, (![A_59, B_60, C_61]: (~r1_xboole_0(A_59, B_60) | ~r2_hidden(C_61, k3_xboole_0(A_59, B_60)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.87/1.64  tff(c_312, plain, (![A_20, C_61]: (~r1_xboole_0(A_20, k1_xboole_0) | ~r2_hidden(C_61, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_175, c_306])).
% 3.87/1.64  tff(c_334, plain, (![C_65]: (~r2_hidden(C_65, k1_xboole_0))), inference(splitLeft, [status(thm)], [c_312])).
% 3.87/1.64  tff(c_346, plain, (![A_66]: (~r2_xboole_0(A_66, k1_xboole_0))), inference(resolution, [status(thm)], [c_20, c_334])).
% 3.87/1.64  tff(c_351, plain, (![A_6]: (k1_xboole_0=A_6 | ~r1_tarski(A_6, k1_xboole_0))), inference(resolution, [status(thm)], [c_8, c_346])).
% 3.87/1.64  tff(c_852, plain, (k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_848, c_351])).
% 3.87/1.64  tff(c_859, plain, $false, inference(negUnitSimplification, [status(thm)], [c_40, c_852])).
% 3.87/1.64  tff(c_861, plain, (![A_124]: (r2_hidden(A_124, '#skF_5') | ~r2_hidden(A_124, '#skF_4'))), inference(splitRight, [status(thm)], [c_730])).
% 3.87/1.64  tff(c_18, plain, (![A_13, B_14]: (~r2_hidden('#skF_3'(A_13, B_14), A_13) | ~r2_xboole_0(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.87/1.64  tff(c_875, plain, (![B_125]: (~r2_xboole_0('#skF_5', B_125) | ~r2_hidden('#skF_3'('#skF_5', B_125), '#skF_4'))), inference(resolution, [status(thm)], [c_861, c_18])).
% 3.87/1.64  tff(c_880, plain, (~r2_xboole_0('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_20, c_875])).
% 3.87/1.64  tff(c_933, plain, ('#skF_5'='#skF_4' | ~r1_tarski('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_8, c_880])).
% 3.87/1.64  tff(c_936, plain, (~r1_tarski('#skF_5', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_38, c_933])).
% 3.87/1.64  tff(c_42, plain, (k1_xboole_0!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.87/1.64  tff(c_377, plain, (![B_68, D_69, A_70, C_71]: (r2_hidden(B_68, D_69) | ~r2_hidden(k4_tarski(A_70, B_68), k2_zfmisc_1(C_71, D_69)))), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.87/1.64  tff(c_380, plain, (![B_68, A_70]: (r2_hidden(B_68, '#skF_4') | ~r2_hidden(k4_tarski(A_70, B_68), k2_zfmisc_1('#skF_4', '#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_44, c_377])).
% 3.87/1.64  tff(c_732, plain, (![B_111, A_110]: (r2_hidden(B_111, '#skF_4') | ~r2_hidden(B_111, '#skF_5') | ~r2_hidden(A_110, '#skF_4'))), inference(resolution, [status(thm)], [c_710, c_380])).
% 3.87/1.64  tff(c_943, plain, (![A_128]: (~r2_hidden(A_128, '#skF_4'))), inference(splitLeft, [status(thm)], [c_732])).
% 3.87/1.64  tff(c_959, plain, (![B_129]: (r1_tarski('#skF_4', B_129))), inference(resolution, [status(thm)], [c_6, c_943])).
% 3.87/1.64  tff(c_963, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_959, c_351])).
% 3.87/1.64  tff(c_970, plain, $false, inference(negUnitSimplification, [status(thm)], [c_42, c_963])).
% 3.87/1.64  tff(c_972, plain, (![B_130]: (r2_hidden(B_130, '#skF_4') | ~r2_hidden(B_130, '#skF_5'))), inference(splitRight, [status(thm)], [c_732])).
% 3.87/1.64  tff(c_1762, plain, (![B_176]: (r2_hidden('#skF_1'('#skF_5', B_176), '#skF_4') | r1_tarski('#skF_5', B_176))), inference(resolution, [status(thm)], [c_6, c_972])).
% 3.87/1.64  tff(c_1775, plain, (r1_tarski('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_1762, c_4])).
% 3.87/1.64  tff(c_1783, plain, $false, inference(negUnitSimplification, [status(thm)], [c_936, c_936, c_1775])).
% 3.87/1.64  tff(c_1784, plain, (![A_20]: (~r1_xboole_0(A_20, k1_xboole_0))), inference(splitRight, [status(thm)], [c_312])).
% 3.87/1.64  tff(c_2350, plain, (![A_258, B_259]: (r2_hidden('#skF_2'(A_258, B_259), k3_xboole_0(A_258, B_259)) | r1_xboole_0(A_258, B_259))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.87/1.64  tff(c_2367, plain, (![A_20]: (r2_hidden('#skF_2'(A_20, k1_xboole_0), k1_xboole_0) | r1_xboole_0(A_20, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_175, c_2350])).
% 3.87/1.64  tff(c_2395, plain, (![A_264]: (r2_hidden('#skF_2'(A_264, k1_xboole_0), k1_xboole_0))), inference(negUnitSimplification, [status(thm)], [c_1784, c_2367])).
% 3.87/1.64  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.87/1.64  tff(c_2397, plain, (![A_264, B_2]: (r2_hidden('#skF_2'(A_264, k1_xboole_0), B_2) | ~r1_tarski(k1_xboole_0, B_2))), inference(resolution, [status(thm)], [c_2395, c_2])).
% 3.87/1.64  tff(c_2408, plain, (![A_266, B_267]: (r2_hidden('#skF_2'(A_266, k1_xboole_0), B_267))), inference(demodulation, [status(thm), theory('equality')], [c_208, c_2397])).
% 3.87/1.64  tff(c_16, plain, (![A_8, B_9, C_12]: (~r1_xboole_0(A_8, B_9) | ~r2_hidden(C_12, k3_xboole_0(A_8, B_9)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.87/1.64  tff(c_2416, plain, (![A_8, B_9]: (~r1_xboole_0(A_8, B_9))), inference(resolution, [status(thm)], [c_2408, c_16])).
% 3.87/1.64  tff(c_14, plain, (![A_8, B_9]: (r2_hidden('#skF_2'(A_8, B_9), k3_xboole_0(A_8, B_9)) | r1_xboole_0(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.87/1.64  tff(c_2431, plain, (![A_274, B_275]: (r2_hidden('#skF_2'(A_274, B_275), k3_xboole_0(A_274, B_275)))), inference(negUnitSimplification, [status(thm)], [c_2416, c_14])).
% 3.87/1.64  tff(c_2439, plain, (![A_52]: (r2_hidden('#skF_2'(A_52, A_52), A_52))), inference(superposition, [status(thm), theory('equality')], [c_193, c_2431])).
% 3.87/1.64  tff(c_2375, plain, (![A_260, B_261, C_262, D_263]: (r2_hidden(k4_tarski(A_260, B_261), k2_zfmisc_1(C_262, D_263)) | ~r2_hidden(B_261, D_263) | ~r2_hidden(A_260, C_262))), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.87/1.64  tff(c_2124, plain, (![B_227, D_228, A_229, C_230]: (r2_hidden(B_227, D_228) | ~r2_hidden(k4_tarski(A_229, B_227), k2_zfmisc_1(C_230, D_228)))), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.87/1.64  tff(c_2127, plain, (![B_227, A_229]: (r2_hidden(B_227, '#skF_4') | ~r2_hidden(k4_tarski(A_229, B_227), k2_zfmisc_1('#skF_4', '#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_44, c_2124])).
% 3.87/1.64  tff(c_2391, plain, (![B_261, A_260]: (r2_hidden(B_261, '#skF_4') | ~r2_hidden(B_261, '#skF_5') | ~r2_hidden(A_260, '#skF_4'))), inference(resolution, [status(thm)], [c_2375, c_2127])).
% 3.87/1.64  tff(c_2499, plain, (![A_281]: (~r2_hidden(A_281, '#skF_4'))), inference(splitLeft, [status(thm)], [c_2391])).
% 3.87/1.64  tff(c_2523, plain, $false, inference(resolution, [status(thm)], [c_2439, c_2499])).
% 3.87/1.64  tff(c_2545, plain, (![B_284]: (r2_hidden(B_284, '#skF_4') | ~r2_hidden(B_284, '#skF_5'))), inference(splitRight, [status(thm)], [c_2391])).
% 3.87/1.64  tff(c_2581, plain, (![B_285]: (r2_hidden('#skF_1'('#skF_5', B_285), '#skF_4') | r1_tarski('#skF_5', B_285))), inference(resolution, [status(thm)], [c_6, c_2545])).
% 3.87/1.64  tff(c_2589, plain, (r1_tarski('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_2581, c_4])).
% 3.87/1.64  tff(c_2525, plain, (![A_282, B_283]: (r2_hidden(k4_tarski(A_282, B_283), k2_zfmisc_1('#skF_4', '#skF_5')) | ~r2_hidden(B_283, '#skF_4') | ~r2_hidden(A_282, '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_44, c_2375])).
% 3.87/1.64  tff(c_34, plain, (![B_24, D_26, A_23, C_25]: (r2_hidden(B_24, D_26) | ~r2_hidden(k4_tarski(A_23, B_24), k2_zfmisc_1(C_25, D_26)))), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.87/1.64  tff(c_2543, plain, (![B_283, A_282]: (r2_hidden(B_283, '#skF_5') | ~r2_hidden(B_283, '#skF_4') | ~r2_hidden(A_282, '#skF_5'))), inference(resolution, [status(thm)], [c_2525, c_34])).
% 3.87/1.64  tff(c_2636, plain, (![A_282]: (~r2_hidden(A_282, '#skF_5'))), inference(splitLeft, [status(thm)], [c_2543])).
% 3.87/1.64  tff(c_2593, plain, (k4_xboole_0('#skF_5', '#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_2589, c_24])).
% 3.87/1.64  tff(c_2597, plain, (k4_xboole_0('#skF_5', k1_xboole_0)=k3_xboole_0('#skF_5', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_2593, c_30])).
% 3.87/1.64  tff(c_2600, plain, (k3_xboole_0('#skF_5', '#skF_4')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_28, c_2597])).
% 3.87/1.64  tff(c_2423, plain, (![A_8, B_9]: (r2_hidden('#skF_2'(A_8, B_9), k3_xboole_0(A_8, B_9)))), inference(negUnitSimplification, [status(thm)], [c_2416, c_14])).
% 3.87/1.64  tff(c_2609, plain, (r2_hidden('#skF_2'('#skF_5', '#skF_4'), '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_2600, c_2423])).
% 3.87/1.64  tff(c_2639, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2636, c_2609])).
% 3.87/1.64  tff(c_2641, plain, (![B_286]: (r2_hidden(B_286, '#skF_5') | ~r2_hidden(B_286, '#skF_4'))), inference(splitRight, [status(thm)], [c_2543])).
% 3.87/1.64  tff(c_2687, plain, (![B_291]: (~r2_xboole_0('#skF_5', B_291) | ~r2_hidden('#skF_3'('#skF_5', B_291), '#skF_4'))), inference(resolution, [status(thm)], [c_2641, c_18])).
% 3.87/1.64  tff(c_2697, plain, (~r2_xboole_0('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_20, c_2687])).
% 3.87/1.64  tff(c_2700, plain, ('#skF_5'='#skF_4' | ~r1_tarski('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_8, c_2697])).
% 3.87/1.64  tff(c_2703, plain, ('#skF_5'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_2589, c_2700])).
% 3.87/1.64  tff(c_2705, plain, $false, inference(negUnitSimplification, [status(thm)], [c_38, c_2703])).
% 3.87/1.64  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.87/1.64  
% 3.87/1.64  Inference rules
% 3.87/1.64  ----------------------
% 3.87/1.64  #Ref     : 1
% 3.87/1.64  #Sup     : 614
% 3.87/1.64  #Fact    : 0
% 3.87/1.64  #Define  : 0
% 3.87/1.64  #Split   : 8
% 3.87/1.64  #Chain   : 0
% 3.87/1.64  #Close   : 0
% 3.87/1.64  
% 3.87/1.64  Ordering : KBO
% 3.87/1.64  
% 3.87/1.64  Simplification rules
% 3.87/1.64  ----------------------
% 3.87/1.64  #Subsume      : 131
% 3.87/1.64  #Demod        : 234
% 3.87/1.64  #Tautology    : 284
% 3.87/1.64  #SimpNegUnit  : 25
% 3.87/1.64  #BackRed      : 7
% 3.87/1.64  
% 3.87/1.64  #Partial instantiations: 0
% 3.87/1.64  #Strategies tried      : 1
% 3.87/1.64  
% 3.87/1.64  Timing (in seconds)
% 3.87/1.64  ----------------------
% 3.87/1.65  Preprocessing        : 0.30
% 3.87/1.65  Parsing              : 0.16
% 3.87/1.65  CNF conversion       : 0.02
% 3.87/1.65  Main loop            : 0.56
% 3.87/1.65  Inferencing          : 0.22
% 3.87/1.65  Reduction            : 0.17
% 3.87/1.65  Demodulation         : 0.12
% 3.87/1.65  BG Simplification    : 0.02
% 3.87/1.65  Subsumption          : 0.11
% 3.87/1.65  Abstraction          : 0.02
% 3.87/1.65  MUC search           : 0.00
% 3.87/1.65  Cooper               : 0.00
% 3.87/1.65  Total                : 0.91
% 3.87/1.65  Index Insertion      : 0.00
% 3.87/1.65  Index Deletion       : 0.00
% 3.87/1.65  Index Matching       : 0.00
% 3.87/1.65  BG Taut test         : 0.00
%------------------------------------------------------------------------------
