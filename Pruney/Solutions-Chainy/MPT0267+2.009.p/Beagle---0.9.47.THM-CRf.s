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
% DateTime   : Thu Dec  3 09:52:33 EST 2020

% Result     : Theorem 2.03s
% Output     : CNFRefutation 2.03s
% Verified   : 
% Statistics : Number of formulae       :   86 ( 207 expanded)
%              Number of leaves         :   22 (  72 expanded)
%              Depth                    :   11
%              Number of atoms          :  118 ( 415 expanded)
%              Number of equality atoms :   44 ( 180 expanded)
%              Maximal formula depth    :   12 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k2_enumset1 > k1_enumset1 > k4_xboole_0 > #nlpp > k1_tarski > #skF_1 > #skF_7 > #skF_10 > #skF_5 > #skF_6 > #skF_2 > #skF_9 > #skF_4 > #skF_8 > #skF_3

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

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i ) > $i )).

tff(f_52,axiom,(
    ! [A] : k1_enumset1(A,A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t76_enumset1)).

tff(f_50,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

tff(f_62,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r2_hidden(A,k4_xboole_0(B,k1_tarski(C)))
      <=> ( r2_hidden(A,B)
          & A != C ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_zfmisc_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

tff(c_44,plain,(
    ! [A_14] : k1_enumset1(A_14,A_14,A_14) = k1_tarski(A_14) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_68,plain,(
    ! [E_17,B_18,C_19] : r2_hidden(E_17,k1_enumset1(E_17,B_18,C_19)) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_71,plain,(
    ! [A_14] : r2_hidden(A_14,k1_tarski(A_14)) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_68])).

tff(c_50,plain,
    ( '#skF_7' != '#skF_5'
    | '#skF_10' = '#skF_8'
    | ~ r2_hidden('#skF_8','#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_83,plain,(
    ~ r2_hidden('#skF_8','#skF_9') ),
    inference(splitLeft,[status(thm)],[c_50])).

tff(c_56,plain,
    ( '#skF_7' != '#skF_5'
    | r2_hidden('#skF_8',k4_xboole_0('#skF_9',k1_tarski('#skF_10'))) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_95,plain,(
    '#skF_7' != '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_56])).

tff(c_58,plain,
    ( r2_hidden('#skF_5','#skF_6')
    | r2_hidden('#skF_8',k4_xboole_0('#skF_9',k1_tarski('#skF_10'))) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_96,plain,(
    r2_hidden('#skF_8',k4_xboole_0('#skF_9',k1_tarski('#skF_10'))) ),
    inference(splitLeft,[status(thm)],[c_58])).

tff(c_6,plain,(
    ! [D_6,A_1,B_2] :
      ( r2_hidden(D_6,A_1)
      | ~ r2_hidden(D_6,k4_xboole_0(A_1,B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_102,plain,(
    r2_hidden('#skF_8','#skF_9') ),
    inference(resolution,[status(thm)],[c_96,c_6])).

tff(c_107,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_83,c_102])).

tff(c_108,plain,(
    r2_hidden('#skF_5','#skF_6') ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_2,plain,(
    ! [D_6,A_1,B_2] :
      ( r2_hidden(D_6,k4_xboole_0(A_1,B_2))
      | r2_hidden(D_6,B_2)
      | ~ r2_hidden(D_6,A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_109,plain,(
    ~ r2_hidden('#skF_8',k4_xboole_0('#skF_9',k1_tarski('#skF_10'))) ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_54,plain,
    ( ~ r2_hidden('#skF_5',k4_xboole_0('#skF_6',k1_tarski('#skF_7')))
    | r2_hidden('#skF_8',k4_xboole_0('#skF_9',k1_tarski('#skF_10'))) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_123,plain,(
    ~ r2_hidden('#skF_5',k4_xboole_0('#skF_6',k1_tarski('#skF_7'))) ),
    inference(negUnitSimplification,[status(thm)],[c_109,c_54])).

tff(c_126,plain,
    ( r2_hidden('#skF_5',k1_tarski('#skF_7'))
    | ~ r2_hidden('#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_2,c_123])).

tff(c_129,plain,(
    r2_hidden('#skF_5',k1_tarski('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_108,c_126])).

tff(c_130,plain,(
    ! [E_37,C_38,B_39,A_40] :
      ( E_37 = C_38
      | E_37 = B_39
      | E_37 = A_40
      | ~ r2_hidden(E_37,k1_enumset1(A_40,B_39,C_38)) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_149,plain,(
    ! [E_41,A_42] :
      ( E_41 = A_42
      | E_41 = A_42
      | E_41 = A_42
      | ~ r2_hidden(E_41,k1_tarski(A_42)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_130])).

tff(c_152,plain,(
    '#skF_7' = '#skF_5' ),
    inference(resolution,[status(thm)],[c_129,c_149])).

tff(c_159,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_95,c_95,c_95,c_152])).

tff(c_160,plain,(
    r2_hidden('#skF_8',k4_xboole_0('#skF_9',k1_tarski('#skF_10'))) ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_171,plain,(
    r2_hidden('#skF_8','#skF_9') ),
    inference(resolution,[status(thm)],[c_160,c_6])).

tff(c_176,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_83,c_171])).

tff(c_177,plain,
    ( '#skF_7' != '#skF_5'
    | '#skF_10' = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_179,plain,(
    '#skF_7' != '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_177])).

tff(c_178,plain,(
    r2_hidden('#skF_8','#skF_9') ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_52,plain,
    ( r2_hidden('#skF_5','#skF_6')
    | '#skF_10' = '#skF_8'
    | ~ r2_hidden('#skF_8','#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_192,plain,
    ( r2_hidden('#skF_5','#skF_6')
    | '#skF_10' = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_178,c_52])).

tff(c_193,plain,(
    '#skF_10' = '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_192])).

tff(c_198,plain,
    ( r2_hidden('#skF_5','#skF_6')
    | r2_hidden('#skF_8',k4_xboole_0('#skF_9',k1_tarski('#skF_8'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_193,c_58])).

tff(c_199,plain,(
    r2_hidden('#skF_8',k4_xboole_0('#skF_9',k1_tarski('#skF_8'))) ),
    inference(splitLeft,[status(thm)],[c_198])).

tff(c_4,plain,(
    ! [D_6,B_2,A_1] :
      ( ~ r2_hidden(D_6,B_2)
      | ~ r2_hidden(D_6,k4_xboole_0(A_1,B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_205,plain,(
    ~ r2_hidden('#skF_8',k1_tarski('#skF_8')) ),
    inference(resolution,[status(thm)],[c_199,c_4])).

tff(c_211,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_71,c_205])).

tff(c_212,plain,(
    r2_hidden('#skF_5','#skF_6') ),
    inference(splitRight,[status(thm)],[c_198])).

tff(c_213,plain,(
    ~ r2_hidden('#skF_8',k4_xboole_0('#skF_9',k1_tarski('#skF_8'))) ),
    inference(splitRight,[status(thm)],[c_198])).

tff(c_256,plain,
    ( ~ r2_hidden('#skF_5',k4_xboole_0('#skF_6',k1_tarski('#skF_7')))
    | r2_hidden('#skF_8',k4_xboole_0('#skF_9',k1_tarski('#skF_8'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_193,c_54])).

tff(c_257,plain,(
    ~ r2_hidden('#skF_5',k4_xboole_0('#skF_6',k1_tarski('#skF_7'))) ),
    inference(negUnitSimplification,[status(thm)],[c_213,c_256])).

tff(c_260,plain,
    ( r2_hidden('#skF_5',k1_tarski('#skF_7'))
    | ~ r2_hidden('#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_2,c_257])).

tff(c_263,plain,(
    r2_hidden('#skF_5',k1_tarski('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_212,c_260])).

tff(c_231,plain,(
    ! [E_53,C_54,B_55,A_56] :
      ( E_53 = C_54
      | E_53 = B_55
      | E_53 = A_56
      | ~ r2_hidden(E_53,k1_enumset1(A_56,B_55,C_54)) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_243,plain,(
    ! [E_53,A_14] :
      ( E_53 = A_14
      | E_53 = A_14
      | E_53 = A_14
      | ~ r2_hidden(E_53,k1_tarski(A_14)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_231])).

tff(c_266,plain,(
    '#skF_7' = '#skF_5' ),
    inference(resolution,[status(thm)],[c_263,c_243])).

tff(c_270,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_179,c_179,c_179,c_266])).

tff(c_271,plain,(
    r2_hidden('#skF_5','#skF_6') ),
    inference(splitRight,[status(thm)],[c_192])).

tff(c_277,plain,(
    ! [D_59,A_60,B_61] :
      ( r2_hidden(D_59,k4_xboole_0(A_60,B_61))
      | r2_hidden(D_59,B_61)
      | ~ r2_hidden(D_59,A_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_272,plain,(
    '#skF_10' != '#skF_8' ),
    inference(splitRight,[status(thm)],[c_192])).

tff(c_48,plain,
    ( ~ r2_hidden('#skF_5',k4_xboole_0('#skF_6',k1_tarski('#skF_7')))
    | '#skF_10' = '#skF_8'
    | ~ r2_hidden('#skF_8','#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_275,plain,
    ( ~ r2_hidden('#skF_5',k4_xboole_0('#skF_6',k1_tarski('#skF_7')))
    | '#skF_10' = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_178,c_48])).

tff(c_276,plain,(
    ~ r2_hidden('#skF_5',k4_xboole_0('#skF_6',k1_tarski('#skF_7'))) ),
    inference(negUnitSimplification,[status(thm)],[c_272,c_275])).

tff(c_280,plain,
    ( r2_hidden('#skF_5',k1_tarski('#skF_7'))
    | ~ r2_hidden('#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_277,c_276])).

tff(c_289,plain,(
    r2_hidden('#skF_5',k1_tarski('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_271,c_280])).

tff(c_292,plain,(
    ! [E_62,C_63,B_64,A_65] :
      ( E_62 = C_63
      | E_62 = B_64
      | E_62 = A_65
      | ~ r2_hidden(E_62,k1_enumset1(A_65,B_64,C_63)) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_311,plain,(
    ! [E_66,A_67] :
      ( E_66 = A_67
      | E_66 = A_67
      | E_66 = A_67
      | ~ r2_hidden(E_66,k1_tarski(A_67)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_292])).

tff(c_314,plain,(
    '#skF_7' = '#skF_5' ),
    inference(resolution,[status(thm)],[c_289,c_311])).

tff(c_321,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_179,c_179,c_179,c_314])).

tff(c_322,plain,(
    '#skF_10' = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_177])).

tff(c_323,plain,(
    '#skF_7' = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_177])).

tff(c_346,plain,(
    r2_hidden('#skF_8',k4_xboole_0('#skF_9',k1_tarski('#skF_8'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_322,c_323,c_56])).

tff(c_352,plain,(
    ~ r2_hidden('#skF_8',k1_tarski('#skF_8')) ),
    inference(resolution,[status(thm)],[c_346,c_4])).

tff(c_358,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_71,c_352])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n025.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 15:37:50 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.03/1.26  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.03/1.26  
% 2.03/1.26  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.03/1.27  %$ r2_hidden > k2_enumset1 > k1_enumset1 > k4_xboole_0 > #nlpp > k1_tarski > #skF_1 > #skF_7 > #skF_10 > #skF_5 > #skF_6 > #skF_2 > #skF_9 > #skF_4 > #skF_8 > #skF_3
% 2.03/1.27  
% 2.03/1.27  %Foreground sorts:
% 2.03/1.27  
% 2.03/1.27  
% 2.03/1.27  %Background operators:
% 2.03/1.27  
% 2.03/1.27  
% 2.03/1.27  %Foreground operators:
% 2.03/1.27  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.03/1.27  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.03/1.27  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.03/1.27  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.03/1.27  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.03/1.27  tff('#skF_7', type, '#skF_7': $i).
% 2.03/1.27  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.03/1.27  tff('#skF_10', type, '#skF_10': $i).
% 2.03/1.27  tff('#skF_5', type, '#skF_5': $i).
% 2.03/1.27  tff('#skF_6', type, '#skF_6': $i).
% 2.03/1.27  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.03/1.27  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.03/1.27  tff('#skF_9', type, '#skF_9': $i).
% 2.03/1.27  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i) > $i).
% 2.03/1.27  tff('#skF_8', type, '#skF_8': $i).
% 2.03/1.27  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.03/1.27  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.03/1.27  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 2.03/1.27  
% 2.03/1.28  tff(f_52, axiom, (![A]: (k1_enumset1(A, A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t76_enumset1)).
% 2.03/1.28  tff(f_50, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_enumset1)).
% 2.03/1.28  tff(f_62, negated_conjecture, ~(![A, B, C]: (r2_hidden(A, k4_xboole_0(B, k1_tarski(C))) <=> (r2_hidden(A, B) & ~(A = C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_zfmisc_1)).
% 2.03/1.28  tff(f_35, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_xboole_0)).
% 2.03/1.28  tff(c_44, plain, (![A_14]: (k1_enumset1(A_14, A_14, A_14)=k1_tarski(A_14))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.03/1.28  tff(c_68, plain, (![E_17, B_18, C_19]: (r2_hidden(E_17, k1_enumset1(E_17, B_18, C_19)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.03/1.28  tff(c_71, plain, (![A_14]: (r2_hidden(A_14, k1_tarski(A_14)))), inference(superposition, [status(thm), theory('equality')], [c_44, c_68])).
% 2.03/1.28  tff(c_50, plain, ('#skF_7'!='#skF_5' | '#skF_10'='#skF_8' | ~r2_hidden('#skF_8', '#skF_9')), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.03/1.28  tff(c_83, plain, (~r2_hidden('#skF_8', '#skF_9')), inference(splitLeft, [status(thm)], [c_50])).
% 2.03/1.28  tff(c_56, plain, ('#skF_7'!='#skF_5' | r2_hidden('#skF_8', k4_xboole_0('#skF_9', k1_tarski('#skF_10')))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.03/1.28  tff(c_95, plain, ('#skF_7'!='#skF_5'), inference(splitLeft, [status(thm)], [c_56])).
% 2.03/1.28  tff(c_58, plain, (r2_hidden('#skF_5', '#skF_6') | r2_hidden('#skF_8', k4_xboole_0('#skF_9', k1_tarski('#skF_10')))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.03/1.28  tff(c_96, plain, (r2_hidden('#skF_8', k4_xboole_0('#skF_9', k1_tarski('#skF_10')))), inference(splitLeft, [status(thm)], [c_58])).
% 2.03/1.28  tff(c_6, plain, (![D_6, A_1, B_2]: (r2_hidden(D_6, A_1) | ~r2_hidden(D_6, k4_xboole_0(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.03/1.28  tff(c_102, plain, (r2_hidden('#skF_8', '#skF_9')), inference(resolution, [status(thm)], [c_96, c_6])).
% 2.03/1.28  tff(c_107, plain, $false, inference(negUnitSimplification, [status(thm)], [c_83, c_102])).
% 2.03/1.28  tff(c_108, plain, (r2_hidden('#skF_5', '#skF_6')), inference(splitRight, [status(thm)], [c_58])).
% 2.03/1.28  tff(c_2, plain, (![D_6, A_1, B_2]: (r2_hidden(D_6, k4_xboole_0(A_1, B_2)) | r2_hidden(D_6, B_2) | ~r2_hidden(D_6, A_1))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.03/1.28  tff(c_109, plain, (~r2_hidden('#skF_8', k4_xboole_0('#skF_9', k1_tarski('#skF_10')))), inference(splitRight, [status(thm)], [c_58])).
% 2.03/1.28  tff(c_54, plain, (~r2_hidden('#skF_5', k4_xboole_0('#skF_6', k1_tarski('#skF_7'))) | r2_hidden('#skF_8', k4_xboole_0('#skF_9', k1_tarski('#skF_10')))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.03/1.28  tff(c_123, plain, (~r2_hidden('#skF_5', k4_xboole_0('#skF_6', k1_tarski('#skF_7')))), inference(negUnitSimplification, [status(thm)], [c_109, c_54])).
% 2.03/1.28  tff(c_126, plain, (r2_hidden('#skF_5', k1_tarski('#skF_7')) | ~r2_hidden('#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_2, c_123])).
% 2.03/1.28  tff(c_129, plain, (r2_hidden('#skF_5', k1_tarski('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_108, c_126])).
% 2.03/1.28  tff(c_130, plain, (![E_37, C_38, B_39, A_40]: (E_37=C_38 | E_37=B_39 | E_37=A_40 | ~r2_hidden(E_37, k1_enumset1(A_40, B_39, C_38)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.03/1.28  tff(c_149, plain, (![E_41, A_42]: (E_41=A_42 | E_41=A_42 | E_41=A_42 | ~r2_hidden(E_41, k1_tarski(A_42)))), inference(superposition, [status(thm), theory('equality')], [c_44, c_130])).
% 2.03/1.28  tff(c_152, plain, ('#skF_7'='#skF_5'), inference(resolution, [status(thm)], [c_129, c_149])).
% 2.03/1.28  tff(c_159, plain, $false, inference(negUnitSimplification, [status(thm)], [c_95, c_95, c_95, c_152])).
% 2.03/1.28  tff(c_160, plain, (r2_hidden('#skF_8', k4_xboole_0('#skF_9', k1_tarski('#skF_10')))), inference(splitRight, [status(thm)], [c_56])).
% 2.03/1.28  tff(c_171, plain, (r2_hidden('#skF_8', '#skF_9')), inference(resolution, [status(thm)], [c_160, c_6])).
% 2.03/1.28  tff(c_176, plain, $false, inference(negUnitSimplification, [status(thm)], [c_83, c_171])).
% 2.03/1.28  tff(c_177, plain, ('#skF_7'!='#skF_5' | '#skF_10'='#skF_8'), inference(splitRight, [status(thm)], [c_50])).
% 2.03/1.28  tff(c_179, plain, ('#skF_7'!='#skF_5'), inference(splitLeft, [status(thm)], [c_177])).
% 2.03/1.28  tff(c_178, plain, (r2_hidden('#skF_8', '#skF_9')), inference(splitRight, [status(thm)], [c_50])).
% 2.03/1.28  tff(c_52, plain, (r2_hidden('#skF_5', '#skF_6') | '#skF_10'='#skF_8' | ~r2_hidden('#skF_8', '#skF_9')), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.03/1.28  tff(c_192, plain, (r2_hidden('#skF_5', '#skF_6') | '#skF_10'='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_178, c_52])).
% 2.03/1.28  tff(c_193, plain, ('#skF_10'='#skF_8'), inference(splitLeft, [status(thm)], [c_192])).
% 2.03/1.28  tff(c_198, plain, (r2_hidden('#skF_5', '#skF_6') | r2_hidden('#skF_8', k4_xboole_0('#skF_9', k1_tarski('#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_193, c_58])).
% 2.03/1.28  tff(c_199, plain, (r2_hidden('#skF_8', k4_xboole_0('#skF_9', k1_tarski('#skF_8')))), inference(splitLeft, [status(thm)], [c_198])).
% 2.03/1.28  tff(c_4, plain, (![D_6, B_2, A_1]: (~r2_hidden(D_6, B_2) | ~r2_hidden(D_6, k4_xboole_0(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.03/1.28  tff(c_205, plain, (~r2_hidden('#skF_8', k1_tarski('#skF_8'))), inference(resolution, [status(thm)], [c_199, c_4])).
% 2.03/1.28  tff(c_211, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_71, c_205])).
% 2.03/1.28  tff(c_212, plain, (r2_hidden('#skF_5', '#skF_6')), inference(splitRight, [status(thm)], [c_198])).
% 2.03/1.28  tff(c_213, plain, (~r2_hidden('#skF_8', k4_xboole_0('#skF_9', k1_tarski('#skF_8')))), inference(splitRight, [status(thm)], [c_198])).
% 2.03/1.28  tff(c_256, plain, (~r2_hidden('#skF_5', k4_xboole_0('#skF_6', k1_tarski('#skF_7'))) | r2_hidden('#skF_8', k4_xboole_0('#skF_9', k1_tarski('#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_193, c_54])).
% 2.03/1.28  tff(c_257, plain, (~r2_hidden('#skF_5', k4_xboole_0('#skF_6', k1_tarski('#skF_7')))), inference(negUnitSimplification, [status(thm)], [c_213, c_256])).
% 2.03/1.28  tff(c_260, plain, (r2_hidden('#skF_5', k1_tarski('#skF_7')) | ~r2_hidden('#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_2, c_257])).
% 2.03/1.28  tff(c_263, plain, (r2_hidden('#skF_5', k1_tarski('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_212, c_260])).
% 2.03/1.28  tff(c_231, plain, (![E_53, C_54, B_55, A_56]: (E_53=C_54 | E_53=B_55 | E_53=A_56 | ~r2_hidden(E_53, k1_enumset1(A_56, B_55, C_54)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.03/1.28  tff(c_243, plain, (![E_53, A_14]: (E_53=A_14 | E_53=A_14 | E_53=A_14 | ~r2_hidden(E_53, k1_tarski(A_14)))), inference(superposition, [status(thm), theory('equality')], [c_44, c_231])).
% 2.03/1.28  tff(c_266, plain, ('#skF_7'='#skF_5'), inference(resolution, [status(thm)], [c_263, c_243])).
% 2.03/1.28  tff(c_270, plain, $false, inference(negUnitSimplification, [status(thm)], [c_179, c_179, c_179, c_266])).
% 2.03/1.28  tff(c_271, plain, (r2_hidden('#skF_5', '#skF_6')), inference(splitRight, [status(thm)], [c_192])).
% 2.03/1.28  tff(c_277, plain, (![D_59, A_60, B_61]: (r2_hidden(D_59, k4_xboole_0(A_60, B_61)) | r2_hidden(D_59, B_61) | ~r2_hidden(D_59, A_60))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.03/1.28  tff(c_272, plain, ('#skF_10'!='#skF_8'), inference(splitRight, [status(thm)], [c_192])).
% 2.03/1.28  tff(c_48, plain, (~r2_hidden('#skF_5', k4_xboole_0('#skF_6', k1_tarski('#skF_7'))) | '#skF_10'='#skF_8' | ~r2_hidden('#skF_8', '#skF_9')), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.03/1.28  tff(c_275, plain, (~r2_hidden('#skF_5', k4_xboole_0('#skF_6', k1_tarski('#skF_7'))) | '#skF_10'='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_178, c_48])).
% 2.03/1.28  tff(c_276, plain, (~r2_hidden('#skF_5', k4_xboole_0('#skF_6', k1_tarski('#skF_7')))), inference(negUnitSimplification, [status(thm)], [c_272, c_275])).
% 2.03/1.28  tff(c_280, plain, (r2_hidden('#skF_5', k1_tarski('#skF_7')) | ~r2_hidden('#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_277, c_276])).
% 2.03/1.28  tff(c_289, plain, (r2_hidden('#skF_5', k1_tarski('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_271, c_280])).
% 2.03/1.28  tff(c_292, plain, (![E_62, C_63, B_64, A_65]: (E_62=C_63 | E_62=B_64 | E_62=A_65 | ~r2_hidden(E_62, k1_enumset1(A_65, B_64, C_63)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.03/1.28  tff(c_311, plain, (![E_66, A_67]: (E_66=A_67 | E_66=A_67 | E_66=A_67 | ~r2_hidden(E_66, k1_tarski(A_67)))), inference(superposition, [status(thm), theory('equality')], [c_44, c_292])).
% 2.03/1.28  tff(c_314, plain, ('#skF_7'='#skF_5'), inference(resolution, [status(thm)], [c_289, c_311])).
% 2.03/1.28  tff(c_321, plain, $false, inference(negUnitSimplification, [status(thm)], [c_179, c_179, c_179, c_314])).
% 2.03/1.28  tff(c_322, plain, ('#skF_10'='#skF_8'), inference(splitRight, [status(thm)], [c_177])).
% 2.03/1.28  tff(c_323, plain, ('#skF_7'='#skF_5'), inference(splitRight, [status(thm)], [c_177])).
% 2.03/1.28  tff(c_346, plain, (r2_hidden('#skF_8', k4_xboole_0('#skF_9', k1_tarski('#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_322, c_323, c_56])).
% 2.03/1.28  tff(c_352, plain, (~r2_hidden('#skF_8', k1_tarski('#skF_8'))), inference(resolution, [status(thm)], [c_346, c_4])).
% 2.03/1.28  tff(c_358, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_71, c_352])).
% 2.03/1.28  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.03/1.28  
% 2.03/1.28  Inference rules
% 2.03/1.28  ----------------------
% 2.03/1.28  #Ref     : 0
% 2.03/1.28  #Sup     : 56
% 2.03/1.28  #Fact    : 0
% 2.03/1.28  #Define  : 0
% 2.03/1.28  #Split   : 6
% 2.03/1.28  #Chain   : 0
% 2.03/1.28  #Close   : 0
% 2.03/1.28  
% 2.03/1.28  Ordering : KBO
% 2.03/1.28  
% 2.03/1.28  Simplification rules
% 2.03/1.28  ----------------------
% 2.03/1.28  #Subsume      : 5
% 2.03/1.28  #Demod        : 22
% 2.03/1.28  #Tautology    : 40
% 2.03/1.28  #SimpNegUnit  : 8
% 2.03/1.28  #BackRed      : 0
% 2.03/1.28  
% 2.03/1.28  #Partial instantiations: 0
% 2.03/1.28  #Strategies tried      : 1
% 2.03/1.28  
% 2.03/1.28  Timing (in seconds)
% 2.03/1.28  ----------------------
% 2.03/1.28  Preprocessing        : 0.30
% 2.03/1.28  Parsing              : 0.15
% 2.03/1.28  CNF conversion       : 0.02
% 2.03/1.28  Main loop            : 0.21
% 2.03/1.28  Inferencing          : 0.07
% 2.03/1.28  Reduction            : 0.06
% 2.03/1.28  Demodulation         : 0.05
% 2.03/1.28  BG Simplification    : 0.01
% 2.03/1.28  Subsumption          : 0.04
% 2.03/1.28  Abstraction          : 0.01
% 2.03/1.28  MUC search           : 0.00
% 2.03/1.28  Cooper               : 0.00
% 2.03/1.28  Total                : 0.54
% 2.03/1.28  Index Insertion      : 0.00
% 2.03/1.28  Index Deletion       : 0.00
% 2.03/1.28  Index Matching       : 0.00
% 2.03/1.28  BG Taut test         : 0.00
%------------------------------------------------------------------------------
