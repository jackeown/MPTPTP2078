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
% DateTime   : Thu Dec  3 09:54:01 EST 2020

% Result     : Theorem 2.27s
% Output     : CNFRefutation 2.27s
% Verified   : 
% Statistics : Number of formulae       :   90 ( 163 expanded)
%              Number of leaves         :   27 (  65 expanded)
%              Depth                    :    6
%              Number of atoms          :  101 ( 265 expanded)
%              Number of equality atoms :   38 ( 115 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_tarski > k2_zfmisc_1 > k2_tarski > #nlpp > k1_tarski > #skF_1 > #skF_7 > #skF_10 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_9 > #skF_8 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

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

tff(f_55,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(C,k1_tarski(D)))
      <=> ( r2_hidden(A,C)
          & B = D ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t129_zfmisc_1)).

tff(f_48,axiom,(
    ! [A,B,C,D] :
      ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(C,D))
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,D) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l54_zfmisc_1)).

tff(f_36,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_42,axiom,(
    ! [A,B] : k2_enumset1(A,A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_enumset1)).

tff(f_40,axiom,(
    ! [A] : k1_enumset1(A,A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t76_enumset1)).

tff(f_34,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

tff(c_44,plain,
    ( r2_hidden('#skF_3','#skF_5')
    | r2_hidden(k4_tarski('#skF_7','#skF_8'),k2_zfmisc_1('#skF_9',k1_tarski('#skF_10'))) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_148,plain,(
    r2_hidden(k4_tarski('#skF_7','#skF_8'),k2_zfmisc_1('#skF_9',k1_tarski('#skF_10'))) ),
    inference(splitLeft,[status(thm)],[c_44])).

tff(c_36,plain,
    ( '#skF_6' = '#skF_4'
    | '#skF_10' != '#skF_8'
    | ~ r2_hidden('#skF_7','#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_56,plain,(
    ~ r2_hidden('#skF_7','#skF_9') ),
    inference(splitLeft,[status(thm)],[c_36])).

tff(c_42,plain,
    ( '#skF_6' = '#skF_4'
    | r2_hidden(k4_tarski('#skF_7','#skF_8'),k2_zfmisc_1('#skF_9',k1_tarski('#skF_10'))) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_98,plain,(
    r2_hidden(k4_tarski('#skF_7','#skF_8'),k2_zfmisc_1('#skF_9',k1_tarski('#skF_10'))) ),
    inference(splitLeft,[status(thm)],[c_42])).

tff(c_138,plain,(
    ! [A_40,C_41,B_42,D_43] :
      ( r2_hidden(A_40,C_41)
      | ~ r2_hidden(k4_tarski(A_40,B_42),k2_zfmisc_1(C_41,D_43)) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_141,plain,(
    r2_hidden('#skF_7','#skF_9') ),
    inference(resolution,[status(thm)],[c_98,c_138])).

tff(c_145,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_141])).

tff(c_147,plain,(
    ~ r2_hidden(k4_tarski('#skF_7','#skF_8'),k2_zfmisc_1('#skF_9',k1_tarski('#skF_10'))) ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_173,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_148,c_147])).

tff(c_174,plain,(
    r2_hidden('#skF_3','#skF_5') ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_66,plain,(
    ! [A_28,B_29,C_30] : k2_enumset1(A_28,A_28,B_29,C_30) = k1_enumset1(A_28,B_29,C_30) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_26,plain,(
    ! [A_15,B_16] : k2_enumset1(A_15,A_15,A_15,B_16) = k2_tarski(A_15,B_16) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_82,plain,(
    ! [B_31,C_32] : k1_enumset1(B_31,B_31,C_32) = k2_tarski(B_31,C_32) ),
    inference(superposition,[status(thm),theory(equality)],[c_66,c_26])).

tff(c_24,plain,(
    ! [A_14] : k1_enumset1(A_14,A_14,A_14) = k1_tarski(A_14) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_181,plain,(
    ! [C_46] : k2_tarski(C_46,C_46) = k1_tarski(C_46) ),
    inference(superposition,[status(thm),theory(equality)],[c_82,c_24])).

tff(c_4,plain,(
    ! [D_6,A_1] : r2_hidden(D_6,k2_tarski(A_1,D_6)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_187,plain,(
    ! [C_46] : r2_hidden(C_46,k1_tarski(C_46)) ),
    inference(superposition,[status(thm),theory(equality)],[c_181,c_4])).

tff(c_233,plain,(
    ! [A_65,B_66,C_67,D_68] :
      ( r2_hidden(k4_tarski(A_65,B_66),k2_zfmisc_1(C_67,D_68))
      | ~ r2_hidden(B_66,D_68)
      | ~ r2_hidden(A_65,C_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_146,plain,(
    '#skF_6' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_40,plain,
    ( ~ r2_hidden(k4_tarski('#skF_3','#skF_4'),k2_zfmisc_1('#skF_5',k1_tarski('#skF_6')))
    | r2_hidden(k4_tarski('#skF_7','#skF_8'),k2_zfmisc_1('#skF_9',k1_tarski('#skF_10'))) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_214,plain,
    ( ~ r2_hidden(k4_tarski('#skF_3','#skF_4'),k2_zfmisc_1('#skF_5',k1_tarski('#skF_4')))
    | r2_hidden(k4_tarski('#skF_7','#skF_8'),k2_zfmisc_1('#skF_9',k1_tarski('#skF_10'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_146,c_40])).

tff(c_215,plain,(
    ~ r2_hidden(k4_tarski('#skF_3','#skF_4'),k2_zfmisc_1('#skF_5',k1_tarski('#skF_4'))) ),
    inference(negUnitSimplification,[status(thm)],[c_147,c_214])).

tff(c_242,plain,
    ( ~ r2_hidden('#skF_4',k1_tarski('#skF_4'))
    | ~ r2_hidden('#skF_3','#skF_5') ),
    inference(resolution,[status(thm)],[c_233,c_215])).

tff(c_251,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_174,c_187,c_242])).

tff(c_253,plain,(
    r2_hidden('#skF_7','#skF_9') ),
    inference(splitRight,[status(thm)],[c_36])).

tff(c_252,plain,
    ( '#skF_10' != '#skF_8'
    | '#skF_6' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_36])).

tff(c_254,plain,(
    '#skF_10' != '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_252])).

tff(c_257,plain,(
    r2_hidden(k4_tarski('#skF_7','#skF_8'),k2_zfmisc_1('#skF_9',k1_tarski('#skF_10'))) ),
    inference(splitLeft,[status(thm)],[c_42])).

tff(c_345,plain,(
    ! [B_87,D_88,A_89,C_90] :
      ( r2_hidden(B_87,D_88)
      | ~ r2_hidden(k4_tarski(A_89,B_87),k2_zfmisc_1(C_90,D_88)) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_349,plain,(
    r2_hidden('#skF_8',k1_tarski('#skF_10')) ),
    inference(resolution,[status(thm)],[c_257,c_345])).

tff(c_267,plain,(
    ! [A_71,B_72,C_73] : k2_enumset1(A_71,A_71,B_72,C_73) = k1_enumset1(A_71,B_72,C_73) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_283,plain,(
    ! [B_74,C_75] : k1_enumset1(B_74,B_74,C_75) = k2_tarski(B_74,C_75) ),
    inference(superposition,[status(thm),theory(equality)],[c_267,c_26])).

tff(c_290,plain,(
    ! [C_75] : k2_tarski(C_75,C_75) = k1_tarski(C_75) ),
    inference(superposition,[status(thm),theory(equality)],[c_283,c_24])).

tff(c_314,plain,(
    ! [D_77,B_78,A_79] :
      ( D_77 = B_78
      | D_77 = A_79
      | ~ r2_hidden(D_77,k2_tarski(A_79,B_78)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_317,plain,(
    ! [D_77,C_75] :
      ( D_77 = C_75
      | D_77 = C_75
      | ~ r2_hidden(D_77,k1_tarski(C_75)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_290,c_314])).

tff(c_352,plain,(
    '#skF_10' = '#skF_8' ),
    inference(resolution,[status(thm)],[c_349,c_317])).

tff(c_356,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_254,c_254,c_352])).

tff(c_358,plain,(
    ~ r2_hidden(k4_tarski('#skF_7','#skF_8'),k2_zfmisc_1('#skF_9',k1_tarski('#skF_10'))) ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_383,plain,(
    r2_hidden('#skF_3','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_358,c_44])).

tff(c_384,plain,(
    ! [A_96,B_97,C_98] : k2_enumset1(A_96,A_96,B_97,C_98) = k1_enumset1(A_96,B_97,C_98) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_400,plain,(
    ! [B_99,C_100] : k1_enumset1(B_99,B_99,C_100) = k2_tarski(B_99,C_100) ),
    inference(superposition,[status(thm),theory(equality)],[c_384,c_26])).

tff(c_416,plain,(
    ! [C_101] : k2_tarski(C_101,C_101) = k1_tarski(C_101) ),
    inference(superposition,[status(thm),theory(equality)],[c_400,c_24])).

tff(c_425,plain,(
    ! [C_101] : r2_hidden(C_101,k1_tarski(C_101)) ),
    inference(superposition,[status(thm),theory(equality)],[c_416,c_4])).

tff(c_28,plain,(
    ! [A_17,B_18,C_19,D_20] :
      ( r2_hidden(k4_tarski(A_17,B_18),k2_zfmisc_1(C_19,D_20))
      | ~ r2_hidden(B_18,D_20)
      | ~ r2_hidden(A_17,C_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_357,plain,(
    '#skF_6' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_474,plain,
    ( ~ r2_hidden(k4_tarski('#skF_3','#skF_4'),k2_zfmisc_1('#skF_5',k1_tarski('#skF_4')))
    | r2_hidden(k4_tarski('#skF_7','#skF_8'),k2_zfmisc_1('#skF_9',k1_tarski('#skF_10'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_357,c_40])).

tff(c_475,plain,(
    ~ r2_hidden(k4_tarski('#skF_3','#skF_4'),k2_zfmisc_1('#skF_5',k1_tarski('#skF_4'))) ),
    inference(negUnitSimplification,[status(thm)],[c_358,c_474])).

tff(c_478,plain,
    ( ~ r2_hidden('#skF_4',k1_tarski('#skF_4'))
    | ~ r2_hidden('#skF_3','#skF_5') ),
    inference(resolution,[status(thm)],[c_28,c_475])).

tff(c_482,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_383,c_425,c_478])).

tff(c_484,plain,(
    '#skF_10' = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_252])).

tff(c_38,plain,
    ( r2_hidden('#skF_3','#skF_5')
    | '#skF_10' != '#skF_8'
    | ~ r2_hidden('#skF_7','#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_494,plain,(
    r2_hidden('#skF_3','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_253,c_484,c_38])).

tff(c_504,plain,(
    ! [A_129,B_130,C_131] : k2_enumset1(A_129,A_129,B_130,C_131) = k1_enumset1(A_129,B_130,C_131) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_520,plain,(
    ! [B_132,C_133] : k1_enumset1(B_132,B_132,C_133) = k2_tarski(B_132,C_133) ),
    inference(superposition,[status(thm),theory(equality)],[c_504,c_26])).

tff(c_536,plain,(
    ! [C_134] : k2_tarski(C_134,C_134) = k1_tarski(C_134) ),
    inference(superposition,[status(thm),theory(equality)],[c_520,c_24])).

tff(c_542,plain,(
    ! [C_134] : r2_hidden(C_134,k1_tarski(C_134)) ),
    inference(superposition,[status(thm),theory(equality)],[c_536,c_4])).

tff(c_483,plain,(
    '#skF_6' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_252])).

tff(c_34,plain,
    ( ~ r2_hidden(k4_tarski('#skF_3','#skF_4'),k2_zfmisc_1('#skF_5',k1_tarski('#skF_6')))
    | '#skF_10' != '#skF_8'
    | ~ r2_hidden('#skF_7','#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_598,plain,(
    ~ r2_hidden(k4_tarski('#skF_3','#skF_4'),k2_zfmisc_1('#skF_5',k1_tarski('#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_253,c_484,c_483,c_34])).

tff(c_601,plain,
    ( ~ r2_hidden('#skF_4',k1_tarski('#skF_4'))
    | ~ r2_hidden('#skF_3','#skF_5') ),
    inference(resolution,[status(thm)],[c_28,c_598])).

tff(c_605,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_494,c_542,c_601])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n025.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 10:33:20 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.27/1.36  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.27/1.37  
% 2.27/1.37  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.27/1.37  %$ r2_hidden > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_tarski > k2_zfmisc_1 > k2_tarski > #nlpp > k1_tarski > #skF_1 > #skF_7 > #skF_10 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_9 > #skF_8 > #skF_4
% 2.27/1.37  
% 2.27/1.37  %Foreground sorts:
% 2.27/1.37  
% 2.27/1.37  
% 2.27/1.37  %Background operators:
% 2.27/1.37  
% 2.27/1.37  
% 2.27/1.37  %Foreground operators:
% 2.27/1.37  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.27/1.37  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.27/1.37  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.27/1.37  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.27/1.37  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.27/1.37  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.27/1.37  tff('#skF_7', type, '#skF_7': $i).
% 2.27/1.37  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.27/1.37  tff('#skF_10', type, '#skF_10': $i).
% 2.27/1.37  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.27/1.37  tff('#skF_5', type, '#skF_5': $i).
% 2.27/1.37  tff('#skF_6', type, '#skF_6': $i).
% 2.27/1.37  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.27/1.37  tff('#skF_3', type, '#skF_3': $i).
% 2.27/1.37  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.27/1.37  tff('#skF_9', type, '#skF_9': $i).
% 2.27/1.37  tff('#skF_8', type, '#skF_8': $i).
% 2.27/1.37  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.27/1.37  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.27/1.37  tff('#skF_4', type, '#skF_4': $i).
% 2.27/1.37  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.27/1.37  
% 2.27/1.39  tff(f_55, negated_conjecture, ~(![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(C, k1_tarski(D))) <=> (r2_hidden(A, C) & (B = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t129_zfmisc_1)).
% 2.27/1.39  tff(f_48, axiom, (![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(C, D)) <=> (r2_hidden(A, C) & r2_hidden(B, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l54_zfmisc_1)).
% 2.27/1.39  tff(f_36, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 2.27/1.39  tff(f_42, axiom, (![A, B]: (k2_enumset1(A, A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t77_enumset1)).
% 2.27/1.39  tff(f_40, axiom, (![A]: (k1_enumset1(A, A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t76_enumset1)).
% 2.27/1.39  tff(f_34, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_tarski)).
% 2.27/1.39  tff(c_44, plain, (r2_hidden('#skF_3', '#skF_5') | r2_hidden(k4_tarski('#skF_7', '#skF_8'), k2_zfmisc_1('#skF_9', k1_tarski('#skF_10')))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.27/1.39  tff(c_148, plain, (r2_hidden(k4_tarski('#skF_7', '#skF_8'), k2_zfmisc_1('#skF_9', k1_tarski('#skF_10')))), inference(splitLeft, [status(thm)], [c_44])).
% 2.27/1.39  tff(c_36, plain, ('#skF_6'='#skF_4' | '#skF_10'!='#skF_8' | ~r2_hidden('#skF_7', '#skF_9')), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.27/1.39  tff(c_56, plain, (~r2_hidden('#skF_7', '#skF_9')), inference(splitLeft, [status(thm)], [c_36])).
% 2.27/1.39  tff(c_42, plain, ('#skF_6'='#skF_4' | r2_hidden(k4_tarski('#skF_7', '#skF_8'), k2_zfmisc_1('#skF_9', k1_tarski('#skF_10')))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.27/1.39  tff(c_98, plain, (r2_hidden(k4_tarski('#skF_7', '#skF_8'), k2_zfmisc_1('#skF_9', k1_tarski('#skF_10')))), inference(splitLeft, [status(thm)], [c_42])).
% 2.27/1.39  tff(c_138, plain, (![A_40, C_41, B_42, D_43]: (r2_hidden(A_40, C_41) | ~r2_hidden(k4_tarski(A_40, B_42), k2_zfmisc_1(C_41, D_43)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.27/1.39  tff(c_141, plain, (r2_hidden('#skF_7', '#skF_9')), inference(resolution, [status(thm)], [c_98, c_138])).
% 2.27/1.39  tff(c_145, plain, $false, inference(negUnitSimplification, [status(thm)], [c_56, c_141])).
% 2.27/1.39  tff(c_147, plain, (~r2_hidden(k4_tarski('#skF_7', '#skF_8'), k2_zfmisc_1('#skF_9', k1_tarski('#skF_10')))), inference(splitRight, [status(thm)], [c_42])).
% 2.27/1.39  tff(c_173, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_148, c_147])).
% 2.27/1.39  tff(c_174, plain, (r2_hidden('#skF_3', '#skF_5')), inference(splitRight, [status(thm)], [c_44])).
% 2.27/1.39  tff(c_66, plain, (![A_28, B_29, C_30]: (k2_enumset1(A_28, A_28, B_29, C_30)=k1_enumset1(A_28, B_29, C_30))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.27/1.39  tff(c_26, plain, (![A_15, B_16]: (k2_enumset1(A_15, A_15, A_15, B_16)=k2_tarski(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.27/1.39  tff(c_82, plain, (![B_31, C_32]: (k1_enumset1(B_31, B_31, C_32)=k2_tarski(B_31, C_32))), inference(superposition, [status(thm), theory('equality')], [c_66, c_26])).
% 2.27/1.39  tff(c_24, plain, (![A_14]: (k1_enumset1(A_14, A_14, A_14)=k1_tarski(A_14))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.27/1.39  tff(c_181, plain, (![C_46]: (k2_tarski(C_46, C_46)=k1_tarski(C_46))), inference(superposition, [status(thm), theory('equality')], [c_82, c_24])).
% 2.27/1.39  tff(c_4, plain, (![D_6, A_1]: (r2_hidden(D_6, k2_tarski(A_1, D_6)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.27/1.39  tff(c_187, plain, (![C_46]: (r2_hidden(C_46, k1_tarski(C_46)))), inference(superposition, [status(thm), theory('equality')], [c_181, c_4])).
% 2.27/1.39  tff(c_233, plain, (![A_65, B_66, C_67, D_68]: (r2_hidden(k4_tarski(A_65, B_66), k2_zfmisc_1(C_67, D_68)) | ~r2_hidden(B_66, D_68) | ~r2_hidden(A_65, C_67))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.27/1.39  tff(c_146, plain, ('#skF_6'='#skF_4'), inference(splitRight, [status(thm)], [c_42])).
% 2.27/1.39  tff(c_40, plain, (~r2_hidden(k4_tarski('#skF_3', '#skF_4'), k2_zfmisc_1('#skF_5', k1_tarski('#skF_6'))) | r2_hidden(k4_tarski('#skF_7', '#skF_8'), k2_zfmisc_1('#skF_9', k1_tarski('#skF_10')))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.27/1.39  tff(c_214, plain, (~r2_hidden(k4_tarski('#skF_3', '#skF_4'), k2_zfmisc_1('#skF_5', k1_tarski('#skF_4'))) | r2_hidden(k4_tarski('#skF_7', '#skF_8'), k2_zfmisc_1('#skF_9', k1_tarski('#skF_10')))), inference(demodulation, [status(thm), theory('equality')], [c_146, c_40])).
% 2.27/1.39  tff(c_215, plain, (~r2_hidden(k4_tarski('#skF_3', '#skF_4'), k2_zfmisc_1('#skF_5', k1_tarski('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_147, c_214])).
% 2.27/1.39  tff(c_242, plain, (~r2_hidden('#skF_4', k1_tarski('#skF_4')) | ~r2_hidden('#skF_3', '#skF_5')), inference(resolution, [status(thm)], [c_233, c_215])).
% 2.27/1.39  tff(c_251, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_174, c_187, c_242])).
% 2.27/1.39  tff(c_253, plain, (r2_hidden('#skF_7', '#skF_9')), inference(splitRight, [status(thm)], [c_36])).
% 2.27/1.39  tff(c_252, plain, ('#skF_10'!='#skF_8' | '#skF_6'='#skF_4'), inference(splitRight, [status(thm)], [c_36])).
% 2.27/1.39  tff(c_254, plain, ('#skF_10'!='#skF_8'), inference(splitLeft, [status(thm)], [c_252])).
% 2.27/1.39  tff(c_257, plain, (r2_hidden(k4_tarski('#skF_7', '#skF_8'), k2_zfmisc_1('#skF_9', k1_tarski('#skF_10')))), inference(splitLeft, [status(thm)], [c_42])).
% 2.27/1.39  tff(c_345, plain, (![B_87, D_88, A_89, C_90]: (r2_hidden(B_87, D_88) | ~r2_hidden(k4_tarski(A_89, B_87), k2_zfmisc_1(C_90, D_88)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.27/1.39  tff(c_349, plain, (r2_hidden('#skF_8', k1_tarski('#skF_10'))), inference(resolution, [status(thm)], [c_257, c_345])).
% 2.27/1.39  tff(c_267, plain, (![A_71, B_72, C_73]: (k2_enumset1(A_71, A_71, B_72, C_73)=k1_enumset1(A_71, B_72, C_73))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.27/1.39  tff(c_283, plain, (![B_74, C_75]: (k1_enumset1(B_74, B_74, C_75)=k2_tarski(B_74, C_75))), inference(superposition, [status(thm), theory('equality')], [c_267, c_26])).
% 2.27/1.39  tff(c_290, plain, (![C_75]: (k2_tarski(C_75, C_75)=k1_tarski(C_75))), inference(superposition, [status(thm), theory('equality')], [c_283, c_24])).
% 2.27/1.39  tff(c_314, plain, (![D_77, B_78, A_79]: (D_77=B_78 | D_77=A_79 | ~r2_hidden(D_77, k2_tarski(A_79, B_78)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.27/1.39  tff(c_317, plain, (![D_77, C_75]: (D_77=C_75 | D_77=C_75 | ~r2_hidden(D_77, k1_tarski(C_75)))), inference(superposition, [status(thm), theory('equality')], [c_290, c_314])).
% 2.27/1.39  tff(c_352, plain, ('#skF_10'='#skF_8'), inference(resolution, [status(thm)], [c_349, c_317])).
% 2.27/1.39  tff(c_356, plain, $false, inference(negUnitSimplification, [status(thm)], [c_254, c_254, c_352])).
% 2.27/1.39  tff(c_358, plain, (~r2_hidden(k4_tarski('#skF_7', '#skF_8'), k2_zfmisc_1('#skF_9', k1_tarski('#skF_10')))), inference(splitRight, [status(thm)], [c_42])).
% 2.27/1.39  tff(c_383, plain, (r2_hidden('#skF_3', '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_358, c_44])).
% 2.27/1.39  tff(c_384, plain, (![A_96, B_97, C_98]: (k2_enumset1(A_96, A_96, B_97, C_98)=k1_enumset1(A_96, B_97, C_98))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.27/1.39  tff(c_400, plain, (![B_99, C_100]: (k1_enumset1(B_99, B_99, C_100)=k2_tarski(B_99, C_100))), inference(superposition, [status(thm), theory('equality')], [c_384, c_26])).
% 2.27/1.39  tff(c_416, plain, (![C_101]: (k2_tarski(C_101, C_101)=k1_tarski(C_101))), inference(superposition, [status(thm), theory('equality')], [c_400, c_24])).
% 2.27/1.39  tff(c_425, plain, (![C_101]: (r2_hidden(C_101, k1_tarski(C_101)))), inference(superposition, [status(thm), theory('equality')], [c_416, c_4])).
% 2.27/1.39  tff(c_28, plain, (![A_17, B_18, C_19, D_20]: (r2_hidden(k4_tarski(A_17, B_18), k2_zfmisc_1(C_19, D_20)) | ~r2_hidden(B_18, D_20) | ~r2_hidden(A_17, C_19))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.27/1.39  tff(c_357, plain, ('#skF_6'='#skF_4'), inference(splitRight, [status(thm)], [c_42])).
% 2.27/1.39  tff(c_474, plain, (~r2_hidden(k4_tarski('#skF_3', '#skF_4'), k2_zfmisc_1('#skF_5', k1_tarski('#skF_4'))) | r2_hidden(k4_tarski('#skF_7', '#skF_8'), k2_zfmisc_1('#skF_9', k1_tarski('#skF_10')))), inference(demodulation, [status(thm), theory('equality')], [c_357, c_40])).
% 2.27/1.39  tff(c_475, plain, (~r2_hidden(k4_tarski('#skF_3', '#skF_4'), k2_zfmisc_1('#skF_5', k1_tarski('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_358, c_474])).
% 2.27/1.39  tff(c_478, plain, (~r2_hidden('#skF_4', k1_tarski('#skF_4')) | ~r2_hidden('#skF_3', '#skF_5')), inference(resolution, [status(thm)], [c_28, c_475])).
% 2.27/1.39  tff(c_482, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_383, c_425, c_478])).
% 2.27/1.39  tff(c_484, plain, ('#skF_10'='#skF_8'), inference(splitRight, [status(thm)], [c_252])).
% 2.27/1.39  tff(c_38, plain, (r2_hidden('#skF_3', '#skF_5') | '#skF_10'!='#skF_8' | ~r2_hidden('#skF_7', '#skF_9')), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.27/1.39  tff(c_494, plain, (r2_hidden('#skF_3', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_253, c_484, c_38])).
% 2.27/1.39  tff(c_504, plain, (![A_129, B_130, C_131]: (k2_enumset1(A_129, A_129, B_130, C_131)=k1_enumset1(A_129, B_130, C_131))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.27/1.39  tff(c_520, plain, (![B_132, C_133]: (k1_enumset1(B_132, B_132, C_133)=k2_tarski(B_132, C_133))), inference(superposition, [status(thm), theory('equality')], [c_504, c_26])).
% 2.27/1.39  tff(c_536, plain, (![C_134]: (k2_tarski(C_134, C_134)=k1_tarski(C_134))), inference(superposition, [status(thm), theory('equality')], [c_520, c_24])).
% 2.27/1.39  tff(c_542, plain, (![C_134]: (r2_hidden(C_134, k1_tarski(C_134)))), inference(superposition, [status(thm), theory('equality')], [c_536, c_4])).
% 2.27/1.39  tff(c_483, plain, ('#skF_6'='#skF_4'), inference(splitRight, [status(thm)], [c_252])).
% 2.27/1.39  tff(c_34, plain, (~r2_hidden(k4_tarski('#skF_3', '#skF_4'), k2_zfmisc_1('#skF_5', k1_tarski('#skF_6'))) | '#skF_10'!='#skF_8' | ~r2_hidden('#skF_7', '#skF_9')), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.27/1.39  tff(c_598, plain, (~r2_hidden(k4_tarski('#skF_3', '#skF_4'), k2_zfmisc_1('#skF_5', k1_tarski('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_253, c_484, c_483, c_34])).
% 2.27/1.39  tff(c_601, plain, (~r2_hidden('#skF_4', k1_tarski('#skF_4')) | ~r2_hidden('#skF_3', '#skF_5')), inference(resolution, [status(thm)], [c_28, c_598])).
% 2.27/1.39  tff(c_605, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_494, c_542, c_601])).
% 2.27/1.39  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.27/1.39  
% 2.27/1.39  Inference rules
% 2.27/1.39  ----------------------
% 2.27/1.39  #Ref     : 0
% 2.27/1.39  #Sup     : 117
% 2.27/1.39  #Fact    : 0
% 2.27/1.39  #Define  : 0
% 2.27/1.39  #Split   : 5
% 2.27/1.39  #Chain   : 0
% 2.27/1.39  #Close   : 0
% 2.27/1.39  
% 2.27/1.39  Ordering : KBO
% 2.27/1.39  
% 2.27/1.39  Simplification rules
% 2.27/1.39  ----------------------
% 2.27/1.39  #Subsume      : 5
% 2.27/1.39  #Demod        : 43
% 2.27/1.39  #Tautology    : 97
% 2.27/1.39  #SimpNegUnit  : 5
% 2.27/1.39  #BackRed      : 0
% 2.27/1.39  
% 2.27/1.39  #Partial instantiations: 0
% 2.27/1.39  #Strategies tried      : 1
% 2.27/1.39  
% 2.27/1.39  Timing (in seconds)
% 2.27/1.39  ----------------------
% 2.27/1.39  Preprocessing        : 0.32
% 2.27/1.39  Parsing              : 0.16
% 2.27/1.39  CNF conversion       : 0.02
% 2.27/1.39  Main loop            : 0.27
% 2.27/1.39  Inferencing          : 0.11
% 2.27/1.39  Reduction            : 0.08
% 2.27/1.39  Demodulation         : 0.06
% 2.27/1.39  BG Simplification    : 0.02
% 2.27/1.39  Subsumption          : 0.04
% 2.27/1.39  Abstraction          : 0.01
% 2.27/1.39  MUC search           : 0.00
% 2.27/1.39  Cooper               : 0.00
% 2.27/1.39  Total                : 0.62
% 2.27/1.39  Index Insertion      : 0.00
% 2.27/1.39  Index Deletion       : 0.00
% 2.27/1.39  Index Matching       : 0.00
% 2.27/1.39  BG Taut test         : 0.00
%------------------------------------------------------------------------------
