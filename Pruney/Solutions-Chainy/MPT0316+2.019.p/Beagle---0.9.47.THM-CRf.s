%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:53:59 EST 2020

% Result     : Theorem 2.28s
% Output     : CNFRefutation 2.28s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 156 expanded)
%              Number of leaves         :   23 (  60 expanded)
%              Depth                    :    8
%              Number of atoms          :   94 ( 282 expanded)
%              Number of equality atoms :   25 ( 107 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k4_tarski > k2_zfmisc_1 > k2_tarski > #nlpp > k1_tarski > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_8 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
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

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

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

tff(f_47,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,k1_tarski(B)) = A
    <=> ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_zfmisc_1)).

tff(f_42,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
    <=> A != B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_zfmisc_1)).

tff(f_54,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(k1_tarski(C),D))
      <=> ( A = C
          & r2_hidden(B,D) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t128_zfmisc_1)).

tff(f_37,axiom,(
    ! [A,B,C,D] :
      ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(C,D))
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,D) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l54_zfmisc_1)).

tff(c_371,plain,(
    ! [A_94,B_95] :
      ( k4_xboole_0(A_94,k1_tarski(B_95)) = A_94
      | r2_hidden(B_95,A_94) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_14,plain,(
    ! [B_12] : k4_xboole_0(k1_tarski(B_12),k1_tarski(B_12)) != k1_tarski(B_12) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_387,plain,(
    ! [B_95] : r2_hidden(B_95,k1_tarski(B_95)) ),
    inference(superposition,[status(thm),theory(equality)],[c_371,c_14])).

tff(c_54,plain,(
    ! [A_21,B_22] :
      ( k4_xboole_0(A_21,k1_tarski(B_22)) = A_21
      | r2_hidden(B_22,A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_70,plain,(
    ! [B_22] : r2_hidden(B_22,k1_tarski(B_22)) ),
    inference(superposition,[status(thm),theory(equality)],[c_54,c_14])).

tff(c_26,plain,
    ( '#skF_3' = '#skF_1'
    | ~ r2_hidden('#skF_6','#skF_8')
    | '#skF_7' != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_42,plain,(
    '#skF_7' != '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_26])).

tff(c_32,plain,
    ( '#skF_3' = '#skF_1'
    | r2_hidden(k4_tarski('#skF_5','#skF_6'),k2_zfmisc_1(k1_tarski('#skF_7'),'#skF_8')) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_73,plain,(
    r2_hidden(k4_tarski('#skF_5','#skF_6'),k2_zfmisc_1(k1_tarski('#skF_7'),'#skF_8')) ),
    inference(splitLeft,[status(thm)],[c_32])).

tff(c_123,plain,(
    ! [A_35,C_36,B_37,D_38] :
      ( r2_hidden(A_35,C_36)
      | ~ r2_hidden(k4_tarski(A_35,B_37),k2_zfmisc_1(C_36,D_38)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_127,plain,(
    r2_hidden('#skF_5',k1_tarski('#skF_7')) ),
    inference(resolution,[status(thm)],[c_73,c_123])).

tff(c_75,plain,(
    ! [A_24,B_25] :
      ( k4_xboole_0(k1_tarski(A_24),k1_tarski(B_25)) = k1_tarski(A_24)
      | B_25 = A_24 ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_18,plain,(
    ! [B_14,A_13] :
      ( ~ r2_hidden(B_14,A_13)
      | k4_xboole_0(A_13,k1_tarski(B_14)) != A_13 ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_98,plain,(
    ! [B_25,A_24] :
      ( ~ r2_hidden(B_25,k1_tarski(A_24))
      | B_25 = A_24 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_75,c_18])).

tff(c_130,plain,(
    '#skF_7' = '#skF_5' ),
    inference(resolution,[status(thm)],[c_127,c_98])).

tff(c_134,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_130])).

tff(c_136,plain,(
    ~ r2_hidden(k4_tarski('#skF_5','#skF_6'),k2_zfmisc_1(k1_tarski('#skF_7'),'#skF_8')) ),
    inference(splitRight,[status(thm)],[c_32])).

tff(c_30,plain,
    ( r2_hidden('#skF_2','#skF_4')
    | r2_hidden(k4_tarski('#skF_5','#skF_6'),k2_zfmisc_1(k1_tarski('#skF_7'),'#skF_8')) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_141,plain,(
    r2_hidden(k4_tarski('#skF_5','#skF_6'),k2_zfmisc_1(k1_tarski('#skF_7'),'#skF_8')) ),
    inference(splitLeft,[status(thm)],[c_30])).

tff(c_142,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_136,c_141])).

tff(c_143,plain,(
    r2_hidden('#skF_2','#skF_4') ),
    inference(splitRight,[status(thm)],[c_30])).

tff(c_8,plain,(
    ! [A_7,B_8,C_9,D_10] :
      ( r2_hidden(k4_tarski(A_7,B_8),k2_zfmisc_1(C_9,D_10))
      | ~ r2_hidden(B_8,D_10)
      | ~ r2_hidden(A_7,C_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_135,plain,(
    '#skF_3' = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_32])).

tff(c_28,plain,
    ( ~ r2_hidden(k4_tarski('#skF_1','#skF_2'),k2_zfmisc_1(k1_tarski('#skF_3'),'#skF_4'))
    | r2_hidden(k4_tarski('#skF_5','#skF_6'),k2_zfmisc_1(k1_tarski('#skF_7'),'#skF_8')) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_206,plain,
    ( ~ r2_hidden(k4_tarski('#skF_1','#skF_2'),k2_zfmisc_1(k1_tarski('#skF_1'),'#skF_4'))
    | r2_hidden(k4_tarski('#skF_5','#skF_6'),k2_zfmisc_1(k1_tarski('#skF_7'),'#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_135,c_28])).

tff(c_207,plain,(
    ~ r2_hidden(k4_tarski('#skF_1','#skF_2'),k2_zfmisc_1(k1_tarski('#skF_1'),'#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_136,c_206])).

tff(c_210,plain,
    ( ~ r2_hidden('#skF_2','#skF_4')
    | ~ r2_hidden('#skF_1',k1_tarski('#skF_1')) ),
    inference(resolution,[status(thm)],[c_8,c_207])).

tff(c_214,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_143,c_210])).

tff(c_216,plain,(
    '#skF_7' = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_26])).

tff(c_235,plain,(
    ! [A_63,B_64] :
      ( k4_xboole_0(A_63,k1_tarski(B_64)) = A_63
      | r2_hidden(B_64,A_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_251,plain,(
    ! [B_64] : r2_hidden(B_64,k1_tarski(B_64)) ),
    inference(superposition,[status(thm),theory(equality)],[c_235,c_14])).

tff(c_215,plain,
    ( ~ r2_hidden('#skF_6','#skF_8')
    | '#skF_3' = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_26])).

tff(c_221,plain,(
    ~ r2_hidden('#skF_6','#skF_8') ),
    inference(splitLeft,[status(thm)],[c_215])).

tff(c_299,plain,
    ( '#skF_3' = '#skF_1'
    | r2_hidden(k4_tarski('#skF_5','#skF_6'),k2_zfmisc_1(k1_tarski('#skF_5'),'#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_216,c_32])).

tff(c_300,plain,(
    r2_hidden(k4_tarski('#skF_5','#skF_6'),k2_zfmisc_1(k1_tarski('#skF_5'),'#skF_8')) ),
    inference(splitLeft,[status(thm)],[c_299])).

tff(c_309,plain,(
    ! [B_77,D_78,A_79,C_80] :
      ( r2_hidden(B_77,D_78)
      | ~ r2_hidden(k4_tarski(A_79,B_77),k2_zfmisc_1(C_80,D_78)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_312,plain,(
    r2_hidden('#skF_6','#skF_8') ),
    inference(resolution,[status(thm)],[c_300,c_309])).

tff(c_316,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_221,c_312])).

tff(c_318,plain,(
    ~ r2_hidden(k4_tarski('#skF_5','#skF_6'),k2_zfmisc_1(k1_tarski('#skF_5'),'#skF_8')) ),
    inference(splitRight,[status(thm)],[c_299])).

tff(c_324,plain,
    ( r2_hidden('#skF_2','#skF_4')
    | r2_hidden(k4_tarski('#skF_5','#skF_6'),k2_zfmisc_1(k1_tarski('#skF_5'),'#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_216,c_30])).

tff(c_325,plain,(
    r2_hidden('#skF_2','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_318,c_324])).

tff(c_317,plain,(
    '#skF_3' = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_299])).

tff(c_343,plain,
    ( ~ r2_hidden(k4_tarski('#skF_1','#skF_2'),k2_zfmisc_1(k1_tarski('#skF_1'),'#skF_4'))
    | r2_hidden(k4_tarski('#skF_5','#skF_6'),k2_zfmisc_1(k1_tarski('#skF_5'),'#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_216,c_317,c_28])).

tff(c_344,plain,(
    ~ r2_hidden(k4_tarski('#skF_1','#skF_2'),k2_zfmisc_1(k1_tarski('#skF_1'),'#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_318,c_343])).

tff(c_347,plain,
    ( ~ r2_hidden('#skF_2','#skF_4')
    | ~ r2_hidden('#skF_1',k1_tarski('#skF_1')) ),
    inference(resolution,[status(thm)],[c_8,c_344])).

tff(c_351,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_251,c_325,c_347])).

tff(c_353,plain,(
    r2_hidden('#skF_6','#skF_8') ),
    inference(splitRight,[status(thm)],[c_215])).

tff(c_24,plain,
    ( r2_hidden('#skF_2','#skF_4')
    | ~ r2_hidden('#skF_6','#skF_8')
    | '#skF_7' != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_369,plain,(
    r2_hidden('#skF_2','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_216,c_353,c_24])).

tff(c_440,plain,(
    ! [A_112,B_113,C_114,D_115] :
      ( r2_hidden(k4_tarski(A_112,B_113),k2_zfmisc_1(C_114,D_115))
      | ~ r2_hidden(B_113,D_115)
      | ~ r2_hidden(A_112,C_114) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_352,plain,(
    '#skF_3' = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_215])).

tff(c_22,plain,
    ( ~ r2_hidden(k4_tarski('#skF_1','#skF_2'),k2_zfmisc_1(k1_tarski('#skF_3'),'#skF_4'))
    | ~ r2_hidden('#skF_6','#skF_8')
    | '#skF_7' != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_439,plain,(
    ~ r2_hidden(k4_tarski('#skF_1','#skF_2'),k2_zfmisc_1(k1_tarski('#skF_1'),'#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_216,c_353,c_352,c_22])).

tff(c_443,plain,
    ( ~ r2_hidden('#skF_2','#skF_4')
    | ~ r2_hidden('#skF_1',k1_tarski('#skF_1')) ),
    inference(resolution,[status(thm)],[c_440,c_439])).

tff(c_453,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_387,c_369,c_443])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:33:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.28/1.36  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.28/1.37  
% 2.28/1.37  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.28/1.37  %$ r2_hidden > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k4_tarski > k2_zfmisc_1 > k2_tarski > #nlpp > k1_tarski > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_8 > #skF_4
% 2.28/1.37  
% 2.28/1.37  %Foreground sorts:
% 2.28/1.37  
% 2.28/1.37  
% 2.28/1.37  %Background operators:
% 2.28/1.37  
% 2.28/1.37  
% 2.28/1.37  %Foreground operators:
% 2.28/1.37  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.28/1.37  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.28/1.37  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.28/1.37  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.28/1.37  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.28/1.37  tff('#skF_7', type, '#skF_7': $i).
% 2.28/1.37  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.28/1.37  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.28/1.37  tff('#skF_5', type, '#skF_5': $i).
% 2.28/1.37  tff('#skF_6', type, '#skF_6': $i).
% 2.28/1.37  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.28/1.37  tff('#skF_2', type, '#skF_2': $i).
% 2.28/1.37  tff('#skF_3', type, '#skF_3': $i).
% 2.28/1.37  tff('#skF_1', type, '#skF_1': $i).
% 2.28/1.37  tff('#skF_8', type, '#skF_8': $i).
% 2.28/1.37  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.28/1.37  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.28/1.37  tff('#skF_4', type, '#skF_4': $i).
% 2.28/1.37  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.28/1.37  
% 2.28/1.39  tff(f_47, axiom, (![A, B]: ((k4_xboole_0(A, k1_tarski(B)) = A) <=> ~r2_hidden(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_zfmisc_1)).
% 2.28/1.39  tff(f_42, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) <=> ~(A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_zfmisc_1)).
% 2.28/1.39  tff(f_54, negated_conjecture, ~(![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(k1_tarski(C), D)) <=> ((A = C) & r2_hidden(B, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t128_zfmisc_1)).
% 2.28/1.39  tff(f_37, axiom, (![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(C, D)) <=> (r2_hidden(A, C) & r2_hidden(B, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l54_zfmisc_1)).
% 2.28/1.39  tff(c_371, plain, (![A_94, B_95]: (k4_xboole_0(A_94, k1_tarski(B_95))=A_94 | r2_hidden(B_95, A_94))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.28/1.39  tff(c_14, plain, (![B_12]: (k4_xboole_0(k1_tarski(B_12), k1_tarski(B_12))!=k1_tarski(B_12))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.28/1.39  tff(c_387, plain, (![B_95]: (r2_hidden(B_95, k1_tarski(B_95)))), inference(superposition, [status(thm), theory('equality')], [c_371, c_14])).
% 2.28/1.39  tff(c_54, plain, (![A_21, B_22]: (k4_xboole_0(A_21, k1_tarski(B_22))=A_21 | r2_hidden(B_22, A_21))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.28/1.39  tff(c_70, plain, (![B_22]: (r2_hidden(B_22, k1_tarski(B_22)))), inference(superposition, [status(thm), theory('equality')], [c_54, c_14])).
% 2.28/1.39  tff(c_26, plain, ('#skF_3'='#skF_1' | ~r2_hidden('#skF_6', '#skF_8') | '#skF_7'!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.28/1.39  tff(c_42, plain, ('#skF_7'!='#skF_5'), inference(splitLeft, [status(thm)], [c_26])).
% 2.28/1.39  tff(c_32, plain, ('#skF_3'='#skF_1' | r2_hidden(k4_tarski('#skF_5', '#skF_6'), k2_zfmisc_1(k1_tarski('#skF_7'), '#skF_8'))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.28/1.39  tff(c_73, plain, (r2_hidden(k4_tarski('#skF_5', '#skF_6'), k2_zfmisc_1(k1_tarski('#skF_7'), '#skF_8'))), inference(splitLeft, [status(thm)], [c_32])).
% 2.28/1.39  tff(c_123, plain, (![A_35, C_36, B_37, D_38]: (r2_hidden(A_35, C_36) | ~r2_hidden(k4_tarski(A_35, B_37), k2_zfmisc_1(C_36, D_38)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.28/1.39  tff(c_127, plain, (r2_hidden('#skF_5', k1_tarski('#skF_7'))), inference(resolution, [status(thm)], [c_73, c_123])).
% 2.28/1.39  tff(c_75, plain, (![A_24, B_25]: (k4_xboole_0(k1_tarski(A_24), k1_tarski(B_25))=k1_tarski(A_24) | B_25=A_24)), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.28/1.39  tff(c_18, plain, (![B_14, A_13]: (~r2_hidden(B_14, A_13) | k4_xboole_0(A_13, k1_tarski(B_14))!=A_13)), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.28/1.39  tff(c_98, plain, (![B_25, A_24]: (~r2_hidden(B_25, k1_tarski(A_24)) | B_25=A_24)), inference(superposition, [status(thm), theory('equality')], [c_75, c_18])).
% 2.28/1.39  tff(c_130, plain, ('#skF_7'='#skF_5'), inference(resolution, [status(thm)], [c_127, c_98])).
% 2.28/1.39  tff(c_134, plain, $false, inference(negUnitSimplification, [status(thm)], [c_42, c_130])).
% 2.28/1.39  tff(c_136, plain, (~r2_hidden(k4_tarski('#skF_5', '#skF_6'), k2_zfmisc_1(k1_tarski('#skF_7'), '#skF_8'))), inference(splitRight, [status(thm)], [c_32])).
% 2.28/1.39  tff(c_30, plain, (r2_hidden('#skF_2', '#skF_4') | r2_hidden(k4_tarski('#skF_5', '#skF_6'), k2_zfmisc_1(k1_tarski('#skF_7'), '#skF_8'))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.28/1.39  tff(c_141, plain, (r2_hidden(k4_tarski('#skF_5', '#skF_6'), k2_zfmisc_1(k1_tarski('#skF_7'), '#skF_8'))), inference(splitLeft, [status(thm)], [c_30])).
% 2.28/1.39  tff(c_142, plain, $false, inference(negUnitSimplification, [status(thm)], [c_136, c_141])).
% 2.28/1.39  tff(c_143, plain, (r2_hidden('#skF_2', '#skF_4')), inference(splitRight, [status(thm)], [c_30])).
% 2.28/1.39  tff(c_8, plain, (![A_7, B_8, C_9, D_10]: (r2_hidden(k4_tarski(A_7, B_8), k2_zfmisc_1(C_9, D_10)) | ~r2_hidden(B_8, D_10) | ~r2_hidden(A_7, C_9))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.28/1.39  tff(c_135, plain, ('#skF_3'='#skF_1'), inference(splitRight, [status(thm)], [c_32])).
% 2.28/1.39  tff(c_28, plain, (~r2_hidden(k4_tarski('#skF_1', '#skF_2'), k2_zfmisc_1(k1_tarski('#skF_3'), '#skF_4')) | r2_hidden(k4_tarski('#skF_5', '#skF_6'), k2_zfmisc_1(k1_tarski('#skF_7'), '#skF_8'))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.28/1.39  tff(c_206, plain, (~r2_hidden(k4_tarski('#skF_1', '#skF_2'), k2_zfmisc_1(k1_tarski('#skF_1'), '#skF_4')) | r2_hidden(k4_tarski('#skF_5', '#skF_6'), k2_zfmisc_1(k1_tarski('#skF_7'), '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_135, c_28])).
% 2.28/1.39  tff(c_207, plain, (~r2_hidden(k4_tarski('#skF_1', '#skF_2'), k2_zfmisc_1(k1_tarski('#skF_1'), '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_136, c_206])).
% 2.28/1.39  tff(c_210, plain, (~r2_hidden('#skF_2', '#skF_4') | ~r2_hidden('#skF_1', k1_tarski('#skF_1'))), inference(resolution, [status(thm)], [c_8, c_207])).
% 2.28/1.39  tff(c_214, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_70, c_143, c_210])).
% 2.28/1.39  tff(c_216, plain, ('#skF_7'='#skF_5'), inference(splitRight, [status(thm)], [c_26])).
% 2.28/1.39  tff(c_235, plain, (![A_63, B_64]: (k4_xboole_0(A_63, k1_tarski(B_64))=A_63 | r2_hidden(B_64, A_63))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.28/1.39  tff(c_251, plain, (![B_64]: (r2_hidden(B_64, k1_tarski(B_64)))), inference(superposition, [status(thm), theory('equality')], [c_235, c_14])).
% 2.28/1.39  tff(c_215, plain, (~r2_hidden('#skF_6', '#skF_8') | '#skF_3'='#skF_1'), inference(splitRight, [status(thm)], [c_26])).
% 2.28/1.39  tff(c_221, plain, (~r2_hidden('#skF_6', '#skF_8')), inference(splitLeft, [status(thm)], [c_215])).
% 2.28/1.39  tff(c_299, plain, ('#skF_3'='#skF_1' | r2_hidden(k4_tarski('#skF_5', '#skF_6'), k2_zfmisc_1(k1_tarski('#skF_5'), '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_216, c_32])).
% 2.28/1.39  tff(c_300, plain, (r2_hidden(k4_tarski('#skF_5', '#skF_6'), k2_zfmisc_1(k1_tarski('#skF_5'), '#skF_8'))), inference(splitLeft, [status(thm)], [c_299])).
% 2.28/1.39  tff(c_309, plain, (![B_77, D_78, A_79, C_80]: (r2_hidden(B_77, D_78) | ~r2_hidden(k4_tarski(A_79, B_77), k2_zfmisc_1(C_80, D_78)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.28/1.39  tff(c_312, plain, (r2_hidden('#skF_6', '#skF_8')), inference(resolution, [status(thm)], [c_300, c_309])).
% 2.28/1.39  tff(c_316, plain, $false, inference(negUnitSimplification, [status(thm)], [c_221, c_312])).
% 2.28/1.39  tff(c_318, plain, (~r2_hidden(k4_tarski('#skF_5', '#skF_6'), k2_zfmisc_1(k1_tarski('#skF_5'), '#skF_8'))), inference(splitRight, [status(thm)], [c_299])).
% 2.28/1.39  tff(c_324, plain, (r2_hidden('#skF_2', '#skF_4') | r2_hidden(k4_tarski('#skF_5', '#skF_6'), k2_zfmisc_1(k1_tarski('#skF_5'), '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_216, c_30])).
% 2.28/1.39  tff(c_325, plain, (r2_hidden('#skF_2', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_318, c_324])).
% 2.28/1.39  tff(c_317, plain, ('#skF_3'='#skF_1'), inference(splitRight, [status(thm)], [c_299])).
% 2.28/1.39  tff(c_343, plain, (~r2_hidden(k4_tarski('#skF_1', '#skF_2'), k2_zfmisc_1(k1_tarski('#skF_1'), '#skF_4')) | r2_hidden(k4_tarski('#skF_5', '#skF_6'), k2_zfmisc_1(k1_tarski('#skF_5'), '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_216, c_317, c_28])).
% 2.28/1.39  tff(c_344, plain, (~r2_hidden(k4_tarski('#skF_1', '#skF_2'), k2_zfmisc_1(k1_tarski('#skF_1'), '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_318, c_343])).
% 2.28/1.39  tff(c_347, plain, (~r2_hidden('#skF_2', '#skF_4') | ~r2_hidden('#skF_1', k1_tarski('#skF_1'))), inference(resolution, [status(thm)], [c_8, c_344])).
% 2.28/1.39  tff(c_351, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_251, c_325, c_347])).
% 2.28/1.39  tff(c_353, plain, (r2_hidden('#skF_6', '#skF_8')), inference(splitRight, [status(thm)], [c_215])).
% 2.28/1.39  tff(c_24, plain, (r2_hidden('#skF_2', '#skF_4') | ~r2_hidden('#skF_6', '#skF_8') | '#skF_7'!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.28/1.39  tff(c_369, plain, (r2_hidden('#skF_2', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_216, c_353, c_24])).
% 2.28/1.39  tff(c_440, plain, (![A_112, B_113, C_114, D_115]: (r2_hidden(k4_tarski(A_112, B_113), k2_zfmisc_1(C_114, D_115)) | ~r2_hidden(B_113, D_115) | ~r2_hidden(A_112, C_114))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.28/1.39  tff(c_352, plain, ('#skF_3'='#skF_1'), inference(splitRight, [status(thm)], [c_215])).
% 2.28/1.39  tff(c_22, plain, (~r2_hidden(k4_tarski('#skF_1', '#skF_2'), k2_zfmisc_1(k1_tarski('#skF_3'), '#skF_4')) | ~r2_hidden('#skF_6', '#skF_8') | '#skF_7'!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.28/1.39  tff(c_439, plain, (~r2_hidden(k4_tarski('#skF_1', '#skF_2'), k2_zfmisc_1(k1_tarski('#skF_1'), '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_216, c_353, c_352, c_22])).
% 2.28/1.39  tff(c_443, plain, (~r2_hidden('#skF_2', '#skF_4') | ~r2_hidden('#skF_1', k1_tarski('#skF_1'))), inference(resolution, [status(thm)], [c_440, c_439])).
% 2.28/1.39  tff(c_453, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_387, c_369, c_443])).
% 2.28/1.39  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.28/1.39  
% 2.28/1.39  Inference rules
% 2.28/1.39  ----------------------
% 2.28/1.39  #Ref     : 0
% 2.28/1.39  #Sup     : 80
% 2.28/1.39  #Fact    : 0
% 2.28/1.39  #Define  : 0
% 2.28/1.39  #Split   : 7
% 2.28/1.39  #Chain   : 0
% 2.28/1.39  #Close   : 0
% 2.28/1.39  
% 2.28/1.39  Ordering : KBO
% 2.28/1.39  
% 2.28/1.39  Simplification rules
% 2.28/1.39  ----------------------
% 2.28/1.39  #Subsume      : 6
% 2.28/1.39  #Demod        : 28
% 2.28/1.39  #Tautology    : 65
% 2.28/1.39  #SimpNegUnit  : 6
% 2.28/1.39  #BackRed      : 0
% 2.28/1.39  
% 2.28/1.39  #Partial instantiations: 0
% 2.28/1.39  #Strategies tried      : 1
% 2.28/1.39  
% 2.28/1.39  Timing (in seconds)
% 2.28/1.39  ----------------------
% 2.28/1.39  Preprocessing        : 0.32
% 2.28/1.39  Parsing              : 0.16
% 2.28/1.39  CNF conversion       : 0.02
% 2.28/1.39  Main loop            : 0.29
% 2.28/1.39  Inferencing          : 0.11
% 2.28/1.39  Reduction            : 0.08
% 2.28/1.39  Demodulation         : 0.05
% 2.28/1.39  BG Simplification    : 0.02
% 2.28/1.39  Subsumption          : 0.05
% 2.28/1.39  Abstraction          : 0.02
% 2.28/1.39  MUC search           : 0.00
% 2.28/1.39  Cooper               : 0.00
% 2.28/1.39  Total                : 0.65
% 2.28/1.39  Index Insertion      : 0.00
% 2.28/1.39  Index Deletion       : 0.00
% 2.28/1.39  Index Matching       : 0.00
% 2.28/1.39  BG Taut test         : 0.00
%------------------------------------------------------------------------------
