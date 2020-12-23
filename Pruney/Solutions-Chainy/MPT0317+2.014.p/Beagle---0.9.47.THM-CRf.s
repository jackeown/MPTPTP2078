%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:54:01 EST 2020

% Result     : Theorem 1.94s
% Output     : CNFRefutation 2.06s
% Verified   : 
% Statistics : Number of formulae       :   89 ( 202 expanded)
%              Number of leaves         :   19 (  72 expanded)
%              Depth                    :    6
%              Number of atoms          :  115 ( 395 expanded)
%              Number of equality atoms :   18 (  92 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k1_enumset1 > k4_tarski > k2_zfmisc_1 > #nlpp > k1_tarski > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_8 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(f_46,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(C,k1_tarski(D)))
      <=> ( r2_hidden(A,C)
          & B = D ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t129_zfmisc_1)).

tff(f_33,axiom,(
    ! [A,B,C,D] :
      ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(C,D))
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,D) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l54_zfmisc_1)).

tff(f_39,axiom,(
    ! [A,B,C,D] :
      ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(k1_tarski(C),D))
    <=> ( A = C
        & r2_hidden(B,D) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t128_zfmisc_1)).

tff(c_18,plain,
    ( '#skF_2' = '#skF_4'
    | '#skF_6' != '#skF_8'
    | ~ r2_hidden('#skF_5','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_36,plain,(
    ~ r2_hidden('#skF_5','#skF_7') ),
    inference(splitLeft,[status(thm)],[c_18])).

tff(c_24,plain,
    ( '#skF_2' = '#skF_4'
    | r2_hidden(k4_tarski('#skF_5','#skF_6'),k2_zfmisc_1('#skF_7',k1_tarski('#skF_8'))) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_38,plain,(
    r2_hidden(k4_tarski('#skF_5','#skF_6'),k2_zfmisc_1('#skF_7',k1_tarski('#skF_8'))) ),
    inference(splitLeft,[status(thm)],[c_24])).

tff(c_45,plain,(
    ! [A_19,C_20,B_21,D_22] :
      ( r2_hidden(A_19,C_20)
      | ~ r2_hidden(k4_tarski(A_19,B_21),k2_zfmisc_1(C_20,D_22)) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_48,plain,(
    r2_hidden('#skF_5','#skF_7') ),
    inference(resolution,[status(thm)],[c_38,c_45])).

tff(c_52,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_48])).

tff(c_54,plain,(
    ~ r2_hidden(k4_tarski('#skF_5','#skF_6'),k2_zfmisc_1('#skF_7',k1_tarski('#skF_8'))) ),
    inference(splitRight,[status(thm)],[c_24])).

tff(c_26,plain,
    ( r2_hidden('#skF_1','#skF_3')
    | r2_hidden(k4_tarski('#skF_5','#skF_6'),k2_zfmisc_1('#skF_7',k1_tarski('#skF_8'))) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_82,plain,(
    r2_hidden('#skF_1','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_26])).

tff(c_61,plain,(
    ! [C_31,B_32,D_33] :
      ( r2_hidden(k4_tarski(C_31,B_32),k2_zfmisc_1(k1_tarski(C_31),D_33))
      | ~ r2_hidden(B_32,D_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_8,plain,(
    ! [A_2,C_4,B_3,D_5] :
      ( r2_hidden(A_2,C_4)
      | ~ r2_hidden(k4_tarski(A_2,B_3),k2_zfmisc_1(C_4,D_5)) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_71,plain,(
    ! [C_31,B_32,D_33] :
      ( r2_hidden(C_31,k1_tarski(C_31))
      | ~ r2_hidden(B_32,D_33) ) ),
    inference(resolution,[status(thm)],[c_61,c_8])).

tff(c_75,plain,(
    ! [B_32,D_33] : ~ r2_hidden(B_32,D_33) ),
    inference(splitLeft,[status(thm)],[c_71])).

tff(c_80,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_75,c_75,c_26])).

tff(c_81,plain,(
    ! [C_31] : r2_hidden(C_31,k1_tarski(C_31)) ),
    inference(splitRight,[status(thm)],[c_71])).

tff(c_4,plain,(
    ! [A_2,B_3,C_4,D_5] :
      ( r2_hidden(k4_tarski(A_2,B_3),k2_zfmisc_1(C_4,D_5))
      | ~ r2_hidden(B_3,D_5)
      | ~ r2_hidden(A_2,C_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_53,plain,(
    '#skF_2' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_24])).

tff(c_22,plain,
    ( ~ r2_hidden(k4_tarski('#skF_1','#skF_2'),k2_zfmisc_1('#skF_3',k1_tarski('#skF_4')))
    | r2_hidden(k4_tarski('#skF_5','#skF_6'),k2_zfmisc_1('#skF_7',k1_tarski('#skF_8'))) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_118,plain,
    ( ~ r2_hidden(k4_tarski('#skF_1','#skF_4'),k2_zfmisc_1('#skF_3',k1_tarski('#skF_4')))
    | r2_hidden(k4_tarski('#skF_5','#skF_6'),k2_zfmisc_1('#skF_7',k1_tarski('#skF_8'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_53,c_22])).

tff(c_119,plain,(
    ~ r2_hidden(k4_tarski('#skF_1','#skF_4'),k2_zfmisc_1('#skF_3',k1_tarski('#skF_4'))) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_118])).

tff(c_122,plain,
    ( ~ r2_hidden('#skF_4',k1_tarski('#skF_4'))
    | ~ r2_hidden('#skF_1','#skF_3') ),
    inference(resolution,[status(thm)],[c_4,c_119])).

tff(c_126,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_81,c_122])).

tff(c_128,plain,(
    r2_hidden('#skF_5','#skF_7') ),
    inference(splitRight,[status(thm)],[c_18])).

tff(c_214,plain,(
    r2_hidden(k4_tarski('#skF_5','#skF_6'),k2_zfmisc_1('#skF_7',k1_tarski('#skF_8'))) ),
    inference(splitLeft,[status(thm)],[c_26])).

tff(c_127,plain,
    ( '#skF_6' != '#skF_8'
    | '#skF_2' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_18])).

tff(c_129,plain,(
    '#skF_6' != '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_127])).

tff(c_136,plain,(
    r2_hidden(k4_tarski('#skF_5','#skF_6'),k2_zfmisc_1('#skF_7',k1_tarski('#skF_8'))) ),
    inference(splitLeft,[status(thm)],[c_24])).

tff(c_6,plain,(
    ! [B_3,D_5,A_2,C_4] :
      ( r2_hidden(B_3,D_5)
      | ~ r2_hidden(k4_tarski(A_2,B_3),k2_zfmisc_1(C_4,D_5)) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_143,plain,(
    r2_hidden('#skF_6',k1_tarski('#skF_8')) ),
    inference(resolution,[status(thm)],[c_136,c_6])).

tff(c_173,plain,(
    ! [A_59,B_60,C_61,D_62] :
      ( r2_hidden(k4_tarski(A_59,B_60),k2_zfmisc_1(C_61,D_62))
      | ~ r2_hidden(B_60,D_62)
      | ~ r2_hidden(A_59,C_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_14,plain,(
    ! [C_8,A_6,B_7,D_9] :
      ( C_8 = A_6
      | ~ r2_hidden(k4_tarski(A_6,B_7),k2_zfmisc_1(k1_tarski(C_8),D_9)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_184,plain,(
    ! [C_8,A_59,B_60,D_62] :
      ( C_8 = A_59
      | ~ r2_hidden(B_60,D_62)
      | ~ r2_hidden(A_59,k1_tarski(C_8)) ) ),
    inference(resolution,[status(thm)],[c_173,c_14])).

tff(c_188,plain,(
    ! [B_60,D_62] : ~ r2_hidden(B_60,D_62) ),
    inference(splitLeft,[status(thm)],[c_184])).

tff(c_149,plain,(
    ! [C_55,B_56,D_57] :
      ( r2_hidden(k4_tarski(C_55,B_56),k2_zfmisc_1(k1_tarski(C_55),D_57))
      | ~ r2_hidden(B_56,D_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_162,plain,(
    ! [C_55,B_56,D_57] :
      ( r2_hidden(C_55,k1_tarski(C_55))
      | ~ r2_hidden(B_56,D_57) ) ),
    inference(resolution,[status(thm)],[c_149,c_8])).

tff(c_163,plain,(
    ! [B_56,D_57] : ~ r2_hidden(B_56,D_57) ),
    inference(splitLeft,[status(thm)],[c_162])).

tff(c_170,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_163,c_143])).

tff(c_171,plain,(
    ! [C_55] : r2_hidden(C_55,k1_tarski(C_55)) ),
    inference(splitRight,[status(thm)],[c_162])).

tff(c_197,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_188,c_171])).

tff(c_199,plain,(
    ! [C_63,A_64] :
      ( C_63 = A_64
      | ~ r2_hidden(A_64,k1_tarski(C_63)) ) ),
    inference(splitRight,[status(thm)],[c_184])).

tff(c_205,plain,(
    '#skF_6' = '#skF_8' ),
    inference(resolution,[status(thm)],[c_143,c_199])).

tff(c_211,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_129,c_205])).

tff(c_213,plain,(
    ~ r2_hidden(k4_tarski('#skF_5','#skF_6'),k2_zfmisc_1('#skF_7',k1_tarski('#skF_8'))) ),
    inference(splitRight,[status(thm)],[c_24])).

tff(c_229,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_214,c_213])).

tff(c_230,plain,(
    r2_hidden('#skF_1','#skF_3') ),
    inference(splitRight,[status(thm)],[c_26])).

tff(c_236,plain,(
    ! [C_65,B_66,D_67] :
      ( r2_hidden(k4_tarski(C_65,B_66),k2_zfmisc_1(k1_tarski(C_65),D_67))
      | ~ r2_hidden(B_66,D_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_249,plain,(
    ! [C_65,B_66,D_67] :
      ( r2_hidden(C_65,k1_tarski(C_65))
      | ~ r2_hidden(B_66,D_67) ) ),
    inference(resolution,[status(thm)],[c_236,c_8])).

tff(c_252,plain,(
    ! [B_66,D_67] : ~ r2_hidden(B_66,D_67) ),
    inference(splitLeft,[status(thm)],[c_249])).

tff(c_258,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_252,c_230])).

tff(c_259,plain,(
    ! [C_65] : r2_hidden(C_65,k1_tarski(C_65)) ),
    inference(splitRight,[status(thm)],[c_249])).

tff(c_212,plain,(
    '#skF_2' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_24])).

tff(c_281,plain,
    ( ~ r2_hidden(k4_tarski('#skF_1','#skF_4'),k2_zfmisc_1('#skF_3',k1_tarski('#skF_4')))
    | r2_hidden(k4_tarski('#skF_5','#skF_6'),k2_zfmisc_1('#skF_7',k1_tarski('#skF_8'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_212,c_22])).

tff(c_282,plain,(
    ~ r2_hidden(k4_tarski('#skF_1','#skF_4'),k2_zfmisc_1('#skF_3',k1_tarski('#skF_4'))) ),
    inference(negUnitSimplification,[status(thm)],[c_213,c_281])).

tff(c_285,plain,
    ( ~ r2_hidden('#skF_4',k1_tarski('#skF_4'))
    | ~ r2_hidden('#skF_1','#skF_3') ),
    inference(resolution,[status(thm)],[c_4,c_282])).

tff(c_289,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_230,c_259,c_285])).

tff(c_291,plain,(
    '#skF_6' = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_127])).

tff(c_20,plain,
    ( r2_hidden('#skF_1','#skF_3')
    | '#skF_6' != '#skF_8'
    | ~ r2_hidden('#skF_5','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_301,plain,(
    r2_hidden('#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_128,c_291,c_20])).

tff(c_306,plain,(
    ! [C_85,B_86,D_87] :
      ( r2_hidden(k4_tarski(C_85,B_86),k2_zfmisc_1(k1_tarski(C_85),D_87))
      | ~ r2_hidden(B_86,D_87) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_317,plain,(
    ! [C_85,B_86,D_87] :
      ( r2_hidden(C_85,k1_tarski(C_85))
      | ~ r2_hidden(B_86,D_87) ) ),
    inference(resolution,[status(thm)],[c_306,c_8])).

tff(c_320,plain,(
    ! [B_86,D_87] : ~ r2_hidden(B_86,D_87) ),
    inference(splitLeft,[status(thm)],[c_317])).

tff(c_327,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_320,c_301])).

tff(c_328,plain,(
    ! [C_85] : r2_hidden(C_85,k1_tarski(C_85)) ),
    inference(splitRight,[status(thm)],[c_317])).

tff(c_333,plain,(
    ! [A_89,B_90,C_91,D_92] :
      ( r2_hidden(k4_tarski(A_89,B_90),k2_zfmisc_1(C_91,D_92))
      | ~ r2_hidden(B_90,D_92)
      | ~ r2_hidden(A_89,C_91) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_290,plain,(
    '#skF_2' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_127])).

tff(c_16,plain,
    ( ~ r2_hidden(k4_tarski('#skF_1','#skF_2'),k2_zfmisc_1('#skF_3',k1_tarski('#skF_4')))
    | '#skF_6' != '#skF_8'
    | ~ r2_hidden('#skF_5','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_332,plain,(
    ~ r2_hidden(k4_tarski('#skF_1','#skF_4'),k2_zfmisc_1('#skF_3',k1_tarski('#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_128,c_291,c_290,c_16])).

tff(c_336,plain,
    ( ~ r2_hidden('#skF_4',k1_tarski('#skF_4'))
    | ~ r2_hidden('#skF_1','#skF_3') ),
    inference(resolution,[status(thm)],[c_333,c_332])).

tff(c_350,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_301,c_328,c_336])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:29:21 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.94/1.22  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.94/1.23  
% 1.94/1.23  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.94/1.23  %$ r2_hidden > k1_enumset1 > k4_tarski > k2_zfmisc_1 > #nlpp > k1_tarski > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_8 > #skF_4
% 1.94/1.23  
% 1.94/1.23  %Foreground sorts:
% 1.94/1.23  
% 1.94/1.23  
% 1.94/1.23  %Background operators:
% 1.94/1.23  
% 1.94/1.23  
% 1.94/1.23  %Foreground operators:
% 1.94/1.23  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.94/1.23  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.94/1.23  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.94/1.23  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 1.94/1.23  tff('#skF_7', type, '#skF_7': $i).
% 1.94/1.23  tff('#skF_5', type, '#skF_5': $i).
% 1.94/1.23  tff('#skF_6', type, '#skF_6': $i).
% 1.94/1.23  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.94/1.23  tff('#skF_2', type, '#skF_2': $i).
% 1.94/1.23  tff('#skF_3', type, '#skF_3': $i).
% 1.94/1.23  tff('#skF_1', type, '#skF_1': $i).
% 1.94/1.23  tff('#skF_8', type, '#skF_8': $i).
% 1.94/1.23  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.94/1.23  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.94/1.23  tff('#skF_4', type, '#skF_4': $i).
% 1.94/1.23  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.94/1.23  
% 2.06/1.25  tff(f_46, negated_conjecture, ~(![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(C, k1_tarski(D))) <=> (r2_hidden(A, C) & (B = D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t129_zfmisc_1)).
% 2.06/1.25  tff(f_33, axiom, (![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(C, D)) <=> (r2_hidden(A, C) & r2_hidden(B, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l54_zfmisc_1)).
% 2.06/1.25  tff(f_39, axiom, (![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(k1_tarski(C), D)) <=> ((A = C) & r2_hidden(B, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t128_zfmisc_1)).
% 2.06/1.25  tff(c_18, plain, ('#skF_2'='#skF_4' | '#skF_6'!='#skF_8' | ~r2_hidden('#skF_5', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.06/1.25  tff(c_36, plain, (~r2_hidden('#skF_5', '#skF_7')), inference(splitLeft, [status(thm)], [c_18])).
% 2.06/1.25  tff(c_24, plain, ('#skF_2'='#skF_4' | r2_hidden(k4_tarski('#skF_5', '#skF_6'), k2_zfmisc_1('#skF_7', k1_tarski('#skF_8')))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.06/1.25  tff(c_38, plain, (r2_hidden(k4_tarski('#skF_5', '#skF_6'), k2_zfmisc_1('#skF_7', k1_tarski('#skF_8')))), inference(splitLeft, [status(thm)], [c_24])).
% 2.06/1.25  tff(c_45, plain, (![A_19, C_20, B_21, D_22]: (r2_hidden(A_19, C_20) | ~r2_hidden(k4_tarski(A_19, B_21), k2_zfmisc_1(C_20, D_22)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.06/1.25  tff(c_48, plain, (r2_hidden('#skF_5', '#skF_7')), inference(resolution, [status(thm)], [c_38, c_45])).
% 2.06/1.25  tff(c_52, plain, $false, inference(negUnitSimplification, [status(thm)], [c_36, c_48])).
% 2.06/1.25  tff(c_54, plain, (~r2_hidden(k4_tarski('#skF_5', '#skF_6'), k2_zfmisc_1('#skF_7', k1_tarski('#skF_8')))), inference(splitRight, [status(thm)], [c_24])).
% 2.06/1.25  tff(c_26, plain, (r2_hidden('#skF_1', '#skF_3') | r2_hidden(k4_tarski('#skF_5', '#skF_6'), k2_zfmisc_1('#skF_7', k1_tarski('#skF_8')))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.06/1.25  tff(c_82, plain, (r2_hidden('#skF_1', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_54, c_26])).
% 2.06/1.25  tff(c_61, plain, (![C_31, B_32, D_33]: (r2_hidden(k4_tarski(C_31, B_32), k2_zfmisc_1(k1_tarski(C_31), D_33)) | ~r2_hidden(B_32, D_33))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.06/1.25  tff(c_8, plain, (![A_2, C_4, B_3, D_5]: (r2_hidden(A_2, C_4) | ~r2_hidden(k4_tarski(A_2, B_3), k2_zfmisc_1(C_4, D_5)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.06/1.25  tff(c_71, plain, (![C_31, B_32, D_33]: (r2_hidden(C_31, k1_tarski(C_31)) | ~r2_hidden(B_32, D_33))), inference(resolution, [status(thm)], [c_61, c_8])).
% 2.06/1.25  tff(c_75, plain, (![B_32, D_33]: (~r2_hidden(B_32, D_33))), inference(splitLeft, [status(thm)], [c_71])).
% 2.06/1.25  tff(c_80, plain, $false, inference(negUnitSimplification, [status(thm)], [c_75, c_75, c_26])).
% 2.06/1.25  tff(c_81, plain, (![C_31]: (r2_hidden(C_31, k1_tarski(C_31)))), inference(splitRight, [status(thm)], [c_71])).
% 2.06/1.25  tff(c_4, plain, (![A_2, B_3, C_4, D_5]: (r2_hidden(k4_tarski(A_2, B_3), k2_zfmisc_1(C_4, D_5)) | ~r2_hidden(B_3, D_5) | ~r2_hidden(A_2, C_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.06/1.25  tff(c_53, plain, ('#skF_2'='#skF_4'), inference(splitRight, [status(thm)], [c_24])).
% 2.06/1.25  tff(c_22, plain, (~r2_hidden(k4_tarski('#skF_1', '#skF_2'), k2_zfmisc_1('#skF_3', k1_tarski('#skF_4'))) | r2_hidden(k4_tarski('#skF_5', '#skF_6'), k2_zfmisc_1('#skF_7', k1_tarski('#skF_8')))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.06/1.25  tff(c_118, plain, (~r2_hidden(k4_tarski('#skF_1', '#skF_4'), k2_zfmisc_1('#skF_3', k1_tarski('#skF_4'))) | r2_hidden(k4_tarski('#skF_5', '#skF_6'), k2_zfmisc_1('#skF_7', k1_tarski('#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_53, c_22])).
% 2.06/1.25  tff(c_119, plain, (~r2_hidden(k4_tarski('#skF_1', '#skF_4'), k2_zfmisc_1('#skF_3', k1_tarski('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_54, c_118])).
% 2.06/1.25  tff(c_122, plain, (~r2_hidden('#skF_4', k1_tarski('#skF_4')) | ~r2_hidden('#skF_1', '#skF_3')), inference(resolution, [status(thm)], [c_4, c_119])).
% 2.06/1.25  tff(c_126, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_82, c_81, c_122])).
% 2.06/1.25  tff(c_128, plain, (r2_hidden('#skF_5', '#skF_7')), inference(splitRight, [status(thm)], [c_18])).
% 2.06/1.25  tff(c_214, plain, (r2_hidden(k4_tarski('#skF_5', '#skF_6'), k2_zfmisc_1('#skF_7', k1_tarski('#skF_8')))), inference(splitLeft, [status(thm)], [c_26])).
% 2.06/1.25  tff(c_127, plain, ('#skF_6'!='#skF_8' | '#skF_2'='#skF_4'), inference(splitRight, [status(thm)], [c_18])).
% 2.06/1.25  tff(c_129, plain, ('#skF_6'!='#skF_8'), inference(splitLeft, [status(thm)], [c_127])).
% 2.06/1.25  tff(c_136, plain, (r2_hidden(k4_tarski('#skF_5', '#skF_6'), k2_zfmisc_1('#skF_7', k1_tarski('#skF_8')))), inference(splitLeft, [status(thm)], [c_24])).
% 2.06/1.25  tff(c_6, plain, (![B_3, D_5, A_2, C_4]: (r2_hidden(B_3, D_5) | ~r2_hidden(k4_tarski(A_2, B_3), k2_zfmisc_1(C_4, D_5)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.06/1.25  tff(c_143, plain, (r2_hidden('#skF_6', k1_tarski('#skF_8'))), inference(resolution, [status(thm)], [c_136, c_6])).
% 2.06/1.25  tff(c_173, plain, (![A_59, B_60, C_61, D_62]: (r2_hidden(k4_tarski(A_59, B_60), k2_zfmisc_1(C_61, D_62)) | ~r2_hidden(B_60, D_62) | ~r2_hidden(A_59, C_61))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.06/1.25  tff(c_14, plain, (![C_8, A_6, B_7, D_9]: (C_8=A_6 | ~r2_hidden(k4_tarski(A_6, B_7), k2_zfmisc_1(k1_tarski(C_8), D_9)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.06/1.25  tff(c_184, plain, (![C_8, A_59, B_60, D_62]: (C_8=A_59 | ~r2_hidden(B_60, D_62) | ~r2_hidden(A_59, k1_tarski(C_8)))), inference(resolution, [status(thm)], [c_173, c_14])).
% 2.06/1.25  tff(c_188, plain, (![B_60, D_62]: (~r2_hidden(B_60, D_62))), inference(splitLeft, [status(thm)], [c_184])).
% 2.06/1.25  tff(c_149, plain, (![C_55, B_56, D_57]: (r2_hidden(k4_tarski(C_55, B_56), k2_zfmisc_1(k1_tarski(C_55), D_57)) | ~r2_hidden(B_56, D_57))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.06/1.25  tff(c_162, plain, (![C_55, B_56, D_57]: (r2_hidden(C_55, k1_tarski(C_55)) | ~r2_hidden(B_56, D_57))), inference(resolution, [status(thm)], [c_149, c_8])).
% 2.06/1.25  tff(c_163, plain, (![B_56, D_57]: (~r2_hidden(B_56, D_57))), inference(splitLeft, [status(thm)], [c_162])).
% 2.06/1.25  tff(c_170, plain, $false, inference(negUnitSimplification, [status(thm)], [c_163, c_143])).
% 2.06/1.25  tff(c_171, plain, (![C_55]: (r2_hidden(C_55, k1_tarski(C_55)))), inference(splitRight, [status(thm)], [c_162])).
% 2.06/1.25  tff(c_197, plain, $false, inference(negUnitSimplification, [status(thm)], [c_188, c_171])).
% 2.06/1.25  tff(c_199, plain, (![C_63, A_64]: (C_63=A_64 | ~r2_hidden(A_64, k1_tarski(C_63)))), inference(splitRight, [status(thm)], [c_184])).
% 2.06/1.25  tff(c_205, plain, ('#skF_6'='#skF_8'), inference(resolution, [status(thm)], [c_143, c_199])).
% 2.06/1.25  tff(c_211, plain, $false, inference(negUnitSimplification, [status(thm)], [c_129, c_205])).
% 2.06/1.25  tff(c_213, plain, (~r2_hidden(k4_tarski('#skF_5', '#skF_6'), k2_zfmisc_1('#skF_7', k1_tarski('#skF_8')))), inference(splitRight, [status(thm)], [c_24])).
% 2.06/1.25  tff(c_229, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_214, c_213])).
% 2.06/1.25  tff(c_230, plain, (r2_hidden('#skF_1', '#skF_3')), inference(splitRight, [status(thm)], [c_26])).
% 2.06/1.25  tff(c_236, plain, (![C_65, B_66, D_67]: (r2_hidden(k4_tarski(C_65, B_66), k2_zfmisc_1(k1_tarski(C_65), D_67)) | ~r2_hidden(B_66, D_67))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.06/1.25  tff(c_249, plain, (![C_65, B_66, D_67]: (r2_hidden(C_65, k1_tarski(C_65)) | ~r2_hidden(B_66, D_67))), inference(resolution, [status(thm)], [c_236, c_8])).
% 2.06/1.25  tff(c_252, plain, (![B_66, D_67]: (~r2_hidden(B_66, D_67))), inference(splitLeft, [status(thm)], [c_249])).
% 2.06/1.25  tff(c_258, plain, $false, inference(negUnitSimplification, [status(thm)], [c_252, c_230])).
% 2.06/1.25  tff(c_259, plain, (![C_65]: (r2_hidden(C_65, k1_tarski(C_65)))), inference(splitRight, [status(thm)], [c_249])).
% 2.06/1.25  tff(c_212, plain, ('#skF_2'='#skF_4'), inference(splitRight, [status(thm)], [c_24])).
% 2.06/1.25  tff(c_281, plain, (~r2_hidden(k4_tarski('#skF_1', '#skF_4'), k2_zfmisc_1('#skF_3', k1_tarski('#skF_4'))) | r2_hidden(k4_tarski('#skF_5', '#skF_6'), k2_zfmisc_1('#skF_7', k1_tarski('#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_212, c_22])).
% 2.06/1.25  tff(c_282, plain, (~r2_hidden(k4_tarski('#skF_1', '#skF_4'), k2_zfmisc_1('#skF_3', k1_tarski('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_213, c_281])).
% 2.06/1.25  tff(c_285, plain, (~r2_hidden('#skF_4', k1_tarski('#skF_4')) | ~r2_hidden('#skF_1', '#skF_3')), inference(resolution, [status(thm)], [c_4, c_282])).
% 2.06/1.25  tff(c_289, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_230, c_259, c_285])).
% 2.06/1.25  tff(c_291, plain, ('#skF_6'='#skF_8'), inference(splitRight, [status(thm)], [c_127])).
% 2.06/1.25  tff(c_20, plain, (r2_hidden('#skF_1', '#skF_3') | '#skF_6'!='#skF_8' | ~r2_hidden('#skF_5', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.06/1.25  tff(c_301, plain, (r2_hidden('#skF_1', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_128, c_291, c_20])).
% 2.06/1.25  tff(c_306, plain, (![C_85, B_86, D_87]: (r2_hidden(k4_tarski(C_85, B_86), k2_zfmisc_1(k1_tarski(C_85), D_87)) | ~r2_hidden(B_86, D_87))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.06/1.25  tff(c_317, plain, (![C_85, B_86, D_87]: (r2_hidden(C_85, k1_tarski(C_85)) | ~r2_hidden(B_86, D_87))), inference(resolution, [status(thm)], [c_306, c_8])).
% 2.06/1.25  tff(c_320, plain, (![B_86, D_87]: (~r2_hidden(B_86, D_87))), inference(splitLeft, [status(thm)], [c_317])).
% 2.06/1.25  tff(c_327, plain, $false, inference(negUnitSimplification, [status(thm)], [c_320, c_301])).
% 2.06/1.25  tff(c_328, plain, (![C_85]: (r2_hidden(C_85, k1_tarski(C_85)))), inference(splitRight, [status(thm)], [c_317])).
% 2.06/1.25  tff(c_333, plain, (![A_89, B_90, C_91, D_92]: (r2_hidden(k4_tarski(A_89, B_90), k2_zfmisc_1(C_91, D_92)) | ~r2_hidden(B_90, D_92) | ~r2_hidden(A_89, C_91))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.06/1.25  tff(c_290, plain, ('#skF_2'='#skF_4'), inference(splitRight, [status(thm)], [c_127])).
% 2.06/1.25  tff(c_16, plain, (~r2_hidden(k4_tarski('#skF_1', '#skF_2'), k2_zfmisc_1('#skF_3', k1_tarski('#skF_4'))) | '#skF_6'!='#skF_8' | ~r2_hidden('#skF_5', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.06/1.25  tff(c_332, plain, (~r2_hidden(k4_tarski('#skF_1', '#skF_4'), k2_zfmisc_1('#skF_3', k1_tarski('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_128, c_291, c_290, c_16])).
% 2.06/1.25  tff(c_336, plain, (~r2_hidden('#skF_4', k1_tarski('#skF_4')) | ~r2_hidden('#skF_1', '#skF_3')), inference(resolution, [status(thm)], [c_333, c_332])).
% 2.06/1.25  tff(c_350, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_301, c_328, c_336])).
% 2.06/1.25  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.06/1.25  
% 2.06/1.25  Inference rules
% 2.06/1.25  ----------------------
% 2.06/1.25  #Ref     : 0
% 2.06/1.25  #Sup     : 50
% 2.06/1.25  #Fact    : 0
% 2.06/1.25  #Define  : 0
% 2.06/1.25  #Split   : 12
% 2.06/1.25  #Chain   : 0
% 2.06/1.25  #Close   : 0
% 2.06/1.25  
% 2.06/1.25  Ordering : KBO
% 2.06/1.25  
% 2.06/1.25  Simplification rules
% 2.06/1.25  ----------------------
% 2.06/1.25  #Subsume      : 39
% 2.06/1.25  #Demod        : 31
% 2.06/1.25  #Tautology    : 36
% 2.06/1.25  #SimpNegUnit  : 39
% 2.06/1.25  #BackRed      : 13
% 2.06/1.25  
% 2.06/1.25  #Partial instantiations: 0
% 2.06/1.25  #Strategies tried      : 1
% 2.06/1.25  
% 2.06/1.25  Timing (in seconds)
% 2.06/1.25  ----------------------
% 2.06/1.25  Preprocessing        : 0.28
% 2.06/1.25  Parsing              : 0.14
% 2.06/1.25  CNF conversion       : 0.02
% 2.06/1.25  Main loop            : 0.20
% 2.06/1.25  Inferencing          : 0.07
% 2.06/1.25  Reduction            : 0.06
% 2.06/1.25  Demodulation         : 0.04
% 2.06/1.25  BG Simplification    : 0.01
% 2.06/1.25  Subsumption          : 0.04
% 2.06/1.25  Abstraction          : 0.01
% 2.06/1.25  MUC search           : 0.00
% 2.06/1.25  Cooper               : 0.00
% 2.06/1.25  Total                : 0.51
% 2.06/1.25  Index Insertion      : 0.00
% 2.06/1.25  Index Deletion       : 0.00
% 2.06/1.25  Index Matching       : 0.00
% 2.06/1.25  BG Taut test         : 0.00
%------------------------------------------------------------------------------
