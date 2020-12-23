%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:51:08 EST 2020

% Result     : Theorem 4.30s
% Output     : CNFRefutation 4.35s
% Verified   : 
% Statistics : Number of formulae       :   73 ( 126 expanded)
%              Number of leaves         :   34 (  58 expanded)
%              Depth                    :    9
%              Number of atoms          :   72 ( 150 expanded)
%              Number of equality atoms :   27 (  59 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_xboole_0 > r2_hidden > r1_tarski > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_5 > #skF_2 > #skF_6 > #skF_4 > #skF_3 > #skF_1

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

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(r2_xboole_0,type,(
    r2_xboole_0: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_102,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r1_tarski(k2_xboole_0(k2_tarski(A,B),C),C)
       => r2_hidden(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_zfmisc_1)).

tff(f_60,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_83,axiom,(
    ! [A,B,C] : k1_enumset1(A,B,C) = k1_enumset1(C,B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t102_enumset1)).

tff(f_89,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_85,axiom,(
    ! [A,B,C] : k1_enumset1(A,B,C) = k2_xboole_0(k2_tarski(A,B),k1_tarski(C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_enumset1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( r2_xboole_0(A,B)
    <=> ( r1_tarski(A,B)
        & A != B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_xboole_0)).

tff(f_58,axiom,(
    ! [A,B] :
      ~ ( r1_tarski(A,B)
        & r2_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_xboole_1)).

tff(f_97,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_79,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

tff(f_34,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(c_78,plain,(
    ~ r2_hidden('#skF_4','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_30,plain,(
    ! [A_24,B_25] : r1_tarski(A_24,k2_xboole_0(A_24,B_25)) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_259,plain,(
    ! [C_106,B_107,A_108] : k1_enumset1(C_106,B_107,A_108) = k1_enumset1(A_108,B_107,C_106) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_68,plain,(
    ! [A_49,B_50] : k1_enumset1(A_49,A_49,B_50) = k2_tarski(A_49,B_50) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_275,plain,(
    ! [C_106,B_107] : k1_enumset1(C_106,B_107,B_107) = k2_tarski(B_107,C_106) ),
    inference(superposition,[status(thm),theory(equality)],[c_259,c_68])).

tff(c_647,plain,(
    ! [A_147,B_148,C_149] : k2_xboole_0(k2_tarski(A_147,B_148),k1_tarski(C_149)) = k1_enumset1(A_147,B_148,C_149) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_799,plain,(
    ! [A_152,B_153,C_154] : r1_tarski(k2_tarski(A_152,B_153),k1_enumset1(A_152,B_153,C_154)) ),
    inference(superposition,[status(thm),theory(equality)],[c_647,c_30])).

tff(c_810,plain,(
    ! [C_106,B_107] : r1_tarski(k2_tarski(C_106,B_107),k2_tarski(B_107,C_106)) ),
    inference(superposition,[status(thm),theory(equality)],[c_275,c_799])).

tff(c_1146,plain,(
    ! [C_170,B_171] : r1_tarski(k2_tarski(C_170,B_171),k2_tarski(B_171,C_170)) ),
    inference(superposition,[status(thm),theory(equality)],[c_275,c_799])).

tff(c_242,plain,(
    ! [A_104,B_105] :
      ( r2_xboole_0(A_104,B_105)
      | B_105 = A_104
      | ~ r1_tarski(A_104,B_105) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_28,plain,(
    ! [B_23,A_22] :
      ( ~ r2_xboole_0(B_23,A_22)
      | ~ r1_tarski(A_22,B_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_253,plain,(
    ! [B_105,A_104] :
      ( ~ r1_tarski(B_105,A_104)
      | B_105 = A_104
      | ~ r1_tarski(A_104,B_105) ) ),
    inference(resolution,[status(thm)],[c_242,c_28])).

tff(c_1154,plain,(
    ! [C_170,B_171] :
      ( k2_tarski(C_170,B_171) = k2_tarski(B_171,C_170)
      | ~ r1_tarski(k2_tarski(B_171,C_170),k2_tarski(C_170,B_171)) ) ),
    inference(resolution,[status(thm)],[c_1146,c_253])).

tff(c_1170,plain,(
    ! [C_172,B_173] : k2_tarski(C_172,B_173) = k2_tarski(B_173,C_172) ),
    inference(demodulation,[status(thm),theory(equality)],[c_810,c_1154])).

tff(c_76,plain,(
    ! [A_63,B_64] : k3_tarski(k2_tarski(A_63,B_64)) = k2_xboole_0(A_63,B_64) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_1364,plain,(
    ! [C_180,B_181] : k3_tarski(k2_tarski(C_180,B_181)) = k2_xboole_0(B_181,C_180) ),
    inference(superposition,[status(thm),theory(equality)],[c_1170,c_76])).

tff(c_1370,plain,(
    ! [C_180,B_181] : k2_xboole_0(C_180,B_181) = k2_xboole_0(B_181,C_180) ),
    inference(superposition,[status(thm),theory(equality)],[c_1364,c_76])).

tff(c_80,plain,(
    r1_tarski(k2_xboole_0(k2_tarski('#skF_4','#skF_5'),'#skF_6'),'#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_415,plain,(
    ! [B_118,A_119] :
      ( ~ r1_tarski(B_118,A_119)
      | B_118 = A_119
      | ~ r1_tarski(A_119,B_118) ) ),
    inference(resolution,[status(thm)],[c_242,c_28])).

tff(c_424,plain,
    ( k2_xboole_0(k2_tarski('#skF_4','#skF_5'),'#skF_6') = '#skF_6'
    | ~ r1_tarski('#skF_6',k2_xboole_0(k2_tarski('#skF_4','#skF_5'),'#skF_6')) ),
    inference(resolution,[status(thm)],[c_80,c_415])).

tff(c_462,plain,(
    ~ r1_tarski('#skF_6',k2_xboole_0(k2_tarski('#skF_4','#skF_5'),'#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_424])).

tff(c_1391,plain,(
    ~ r1_tarski('#skF_6',k2_xboole_0('#skF_6',k2_tarski('#skF_4','#skF_5'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1370,c_462])).

tff(c_1395,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_1391])).

tff(c_1396,plain,(
    k2_xboole_0(k2_tarski('#skF_4','#skF_5'),'#skF_6') = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_424])).

tff(c_1943,plain,(
    ! [A_198,B_199,C_200] : k2_xboole_0(k2_tarski(A_198,B_199),k1_tarski(C_200)) = k1_enumset1(A_198,B_199,C_200) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_1970,plain,(
    ! [A_201,B_202,C_203] : r1_tarski(k2_tarski(A_201,B_202),k1_enumset1(A_201,B_202,C_203)) ),
    inference(superposition,[status(thm),theory(equality)],[c_1943,c_30])).

tff(c_1975,plain,(
    ! [C_106,B_107] : r1_tarski(k2_tarski(C_106,B_107),k2_tarski(B_107,C_106)) ),
    inference(superposition,[status(thm),theory(equality)],[c_275,c_1970])).

tff(c_2020,plain,(
    ! [C_206,B_207] : r1_tarski(k2_tarski(C_206,B_207),k2_tarski(B_207,C_206)) ),
    inference(superposition,[status(thm),theory(equality)],[c_275,c_1970])).

tff(c_2022,plain,(
    ! [C_206,B_207] :
      ( k2_tarski(C_206,B_207) = k2_tarski(B_207,C_206)
      | ~ r1_tarski(k2_tarski(B_207,C_206),k2_tarski(C_206,B_207)) ) ),
    inference(resolution,[status(thm)],[c_2020,c_253])).

tff(c_2031,plain,(
    ! [C_206,B_207] : k2_tarski(C_206,B_207) = k2_tarski(B_207,C_206) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1975,c_2022])).

tff(c_191,plain,(
    ! [A_94,B_95] : k1_enumset1(A_94,A_94,B_95) = k2_tarski(A_94,B_95) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_38,plain,(
    ! [E_37,A_31,B_32] : r2_hidden(E_37,k1_enumset1(A_31,B_32,E_37)) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_200,plain,(
    ! [B_95,A_94] : r2_hidden(B_95,k2_tarski(A_94,B_95)) ),
    inference(superposition,[status(thm),theory(equality)],[c_191,c_38])).

tff(c_440,plain,(
    ! [C_123,B_124,A_125] :
      ( r2_hidden(C_123,B_124)
      | ~ r2_hidden(C_123,A_125)
      | ~ r1_tarski(A_125,B_124) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_2901,plain,(
    ! [B_259,B_260,A_261] :
      ( r2_hidden(B_259,B_260)
      | ~ r1_tarski(k2_tarski(A_261,B_259),B_260) ) ),
    inference(resolution,[status(thm)],[c_200,c_440])).

tff(c_2959,plain,(
    ! [B_267,A_268,B_269] : r2_hidden(B_267,k2_xboole_0(k2_tarski(A_268,B_267),B_269)) ),
    inference(resolution,[status(thm)],[c_30,c_2901])).

tff(c_3009,plain,(
    ! [C_274,B_275,B_276] : r2_hidden(C_274,k2_xboole_0(k2_tarski(C_274,B_275),B_276)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2031,c_2959])).

tff(c_3034,plain,(
    r2_hidden('#skF_4','#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_1396,c_3009])).

tff(c_3047,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_3034])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.36  % Computer   : n023.cluster.edu
% 0.14/0.36  % Model      : x86_64 x86_64
% 0.14/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.36  % Memory     : 8042.1875MB
% 0.14/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.21/0.36  % CPULimit   : 60
% 0.21/0.36  % DateTime   : Tue Dec  1 20:27:35 EST 2020
% 0.21/0.36  % CPUTime    : 
% 0.21/0.37  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.30/1.82  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.35/1.82  
% 4.35/1.82  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.35/1.82  %$ r2_xboole_0 > r2_hidden > r1_tarski > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_5 > #skF_2 > #skF_6 > #skF_4 > #skF_3 > #skF_1
% 4.35/1.82  
% 4.35/1.82  %Foreground sorts:
% 4.35/1.82  
% 4.35/1.82  
% 4.35/1.82  %Background operators:
% 4.35/1.82  
% 4.35/1.82  
% 4.35/1.82  %Foreground operators:
% 4.35/1.82  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.35/1.82  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.35/1.82  tff(k1_tarski, type, k1_tarski: $i > $i).
% 4.35/1.82  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.35/1.82  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.35/1.82  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 4.35/1.82  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 4.35/1.82  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.35/1.82  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 4.35/1.82  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.35/1.82  tff('#skF_5', type, '#skF_5': $i).
% 4.35/1.82  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 4.35/1.82  tff('#skF_6', type, '#skF_6': $i).
% 4.35/1.82  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 4.35/1.82  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 4.35/1.82  tff(r2_xboole_0, type, r2_xboole_0: ($i * $i) > $o).
% 4.35/1.82  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.35/1.82  tff(k3_tarski, type, k3_tarski: $i > $i).
% 4.35/1.82  tff('#skF_4', type, '#skF_4': $i).
% 4.35/1.82  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.35/1.82  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.35/1.82  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 4.35/1.82  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.35/1.82  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 4.35/1.82  
% 4.35/1.84  tff(f_102, negated_conjecture, ~(![A, B, C]: (r1_tarski(k2_xboole_0(k2_tarski(A, B), C), C) => r2_hidden(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_zfmisc_1)).
% 4.35/1.84  tff(f_60, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 4.35/1.84  tff(f_83, axiom, (![A, B, C]: (k1_enumset1(A, B, C) = k1_enumset1(C, B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t102_enumset1)).
% 4.35/1.84  tff(f_89, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 4.35/1.84  tff(f_85, axiom, (![A, B, C]: (k1_enumset1(A, B, C) = k2_xboole_0(k2_tarski(A, B), k1_tarski(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_enumset1)).
% 4.35/1.84  tff(f_41, axiom, (![A, B]: (r2_xboole_0(A, B) <=> (r1_tarski(A, B) & ~(A = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_xboole_0)).
% 4.35/1.84  tff(f_58, axiom, (![A, B]: ~(r1_tarski(A, B) & r2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_xboole_1)).
% 4.35/1.84  tff(f_97, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 4.35/1.84  tff(f_79, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_enumset1)).
% 4.35/1.84  tff(f_34, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 4.35/1.84  tff(c_78, plain, (~r2_hidden('#skF_4', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_102])).
% 4.35/1.84  tff(c_30, plain, (![A_24, B_25]: (r1_tarski(A_24, k2_xboole_0(A_24, B_25)))), inference(cnfTransformation, [status(thm)], [f_60])).
% 4.35/1.84  tff(c_259, plain, (![C_106, B_107, A_108]: (k1_enumset1(C_106, B_107, A_108)=k1_enumset1(A_108, B_107, C_106))), inference(cnfTransformation, [status(thm)], [f_83])).
% 4.35/1.84  tff(c_68, plain, (![A_49, B_50]: (k1_enumset1(A_49, A_49, B_50)=k2_tarski(A_49, B_50))), inference(cnfTransformation, [status(thm)], [f_89])).
% 4.35/1.84  tff(c_275, plain, (![C_106, B_107]: (k1_enumset1(C_106, B_107, B_107)=k2_tarski(B_107, C_106))), inference(superposition, [status(thm), theory('equality')], [c_259, c_68])).
% 4.35/1.84  tff(c_647, plain, (![A_147, B_148, C_149]: (k2_xboole_0(k2_tarski(A_147, B_148), k1_tarski(C_149))=k1_enumset1(A_147, B_148, C_149))), inference(cnfTransformation, [status(thm)], [f_85])).
% 4.35/1.84  tff(c_799, plain, (![A_152, B_153, C_154]: (r1_tarski(k2_tarski(A_152, B_153), k1_enumset1(A_152, B_153, C_154)))), inference(superposition, [status(thm), theory('equality')], [c_647, c_30])).
% 4.35/1.84  tff(c_810, plain, (![C_106, B_107]: (r1_tarski(k2_tarski(C_106, B_107), k2_tarski(B_107, C_106)))), inference(superposition, [status(thm), theory('equality')], [c_275, c_799])).
% 4.35/1.84  tff(c_1146, plain, (![C_170, B_171]: (r1_tarski(k2_tarski(C_170, B_171), k2_tarski(B_171, C_170)))), inference(superposition, [status(thm), theory('equality')], [c_275, c_799])).
% 4.35/1.84  tff(c_242, plain, (![A_104, B_105]: (r2_xboole_0(A_104, B_105) | B_105=A_104 | ~r1_tarski(A_104, B_105))), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.35/1.84  tff(c_28, plain, (![B_23, A_22]: (~r2_xboole_0(B_23, A_22) | ~r1_tarski(A_22, B_23))), inference(cnfTransformation, [status(thm)], [f_58])).
% 4.35/1.84  tff(c_253, plain, (![B_105, A_104]: (~r1_tarski(B_105, A_104) | B_105=A_104 | ~r1_tarski(A_104, B_105))), inference(resolution, [status(thm)], [c_242, c_28])).
% 4.35/1.84  tff(c_1154, plain, (![C_170, B_171]: (k2_tarski(C_170, B_171)=k2_tarski(B_171, C_170) | ~r1_tarski(k2_tarski(B_171, C_170), k2_tarski(C_170, B_171)))), inference(resolution, [status(thm)], [c_1146, c_253])).
% 4.35/1.84  tff(c_1170, plain, (![C_172, B_173]: (k2_tarski(C_172, B_173)=k2_tarski(B_173, C_172))), inference(demodulation, [status(thm), theory('equality')], [c_810, c_1154])).
% 4.35/1.84  tff(c_76, plain, (![A_63, B_64]: (k3_tarski(k2_tarski(A_63, B_64))=k2_xboole_0(A_63, B_64))), inference(cnfTransformation, [status(thm)], [f_97])).
% 4.35/1.84  tff(c_1364, plain, (![C_180, B_181]: (k3_tarski(k2_tarski(C_180, B_181))=k2_xboole_0(B_181, C_180))), inference(superposition, [status(thm), theory('equality')], [c_1170, c_76])).
% 4.35/1.84  tff(c_1370, plain, (![C_180, B_181]: (k2_xboole_0(C_180, B_181)=k2_xboole_0(B_181, C_180))), inference(superposition, [status(thm), theory('equality')], [c_1364, c_76])).
% 4.35/1.84  tff(c_80, plain, (r1_tarski(k2_xboole_0(k2_tarski('#skF_4', '#skF_5'), '#skF_6'), '#skF_6')), inference(cnfTransformation, [status(thm)], [f_102])).
% 4.35/1.84  tff(c_415, plain, (![B_118, A_119]: (~r1_tarski(B_118, A_119) | B_118=A_119 | ~r1_tarski(A_119, B_118))), inference(resolution, [status(thm)], [c_242, c_28])).
% 4.35/1.84  tff(c_424, plain, (k2_xboole_0(k2_tarski('#skF_4', '#skF_5'), '#skF_6')='#skF_6' | ~r1_tarski('#skF_6', k2_xboole_0(k2_tarski('#skF_4', '#skF_5'), '#skF_6'))), inference(resolution, [status(thm)], [c_80, c_415])).
% 4.35/1.84  tff(c_462, plain, (~r1_tarski('#skF_6', k2_xboole_0(k2_tarski('#skF_4', '#skF_5'), '#skF_6'))), inference(splitLeft, [status(thm)], [c_424])).
% 4.35/1.84  tff(c_1391, plain, (~r1_tarski('#skF_6', k2_xboole_0('#skF_6', k2_tarski('#skF_4', '#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_1370, c_462])).
% 4.35/1.84  tff(c_1395, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_30, c_1391])).
% 4.35/1.84  tff(c_1396, plain, (k2_xboole_0(k2_tarski('#skF_4', '#skF_5'), '#skF_6')='#skF_6'), inference(splitRight, [status(thm)], [c_424])).
% 4.35/1.84  tff(c_1943, plain, (![A_198, B_199, C_200]: (k2_xboole_0(k2_tarski(A_198, B_199), k1_tarski(C_200))=k1_enumset1(A_198, B_199, C_200))), inference(cnfTransformation, [status(thm)], [f_85])).
% 4.35/1.84  tff(c_1970, plain, (![A_201, B_202, C_203]: (r1_tarski(k2_tarski(A_201, B_202), k1_enumset1(A_201, B_202, C_203)))), inference(superposition, [status(thm), theory('equality')], [c_1943, c_30])).
% 4.35/1.84  tff(c_1975, plain, (![C_106, B_107]: (r1_tarski(k2_tarski(C_106, B_107), k2_tarski(B_107, C_106)))), inference(superposition, [status(thm), theory('equality')], [c_275, c_1970])).
% 4.35/1.84  tff(c_2020, plain, (![C_206, B_207]: (r1_tarski(k2_tarski(C_206, B_207), k2_tarski(B_207, C_206)))), inference(superposition, [status(thm), theory('equality')], [c_275, c_1970])).
% 4.35/1.84  tff(c_2022, plain, (![C_206, B_207]: (k2_tarski(C_206, B_207)=k2_tarski(B_207, C_206) | ~r1_tarski(k2_tarski(B_207, C_206), k2_tarski(C_206, B_207)))), inference(resolution, [status(thm)], [c_2020, c_253])).
% 4.35/1.84  tff(c_2031, plain, (![C_206, B_207]: (k2_tarski(C_206, B_207)=k2_tarski(B_207, C_206))), inference(demodulation, [status(thm), theory('equality')], [c_1975, c_2022])).
% 4.35/1.84  tff(c_191, plain, (![A_94, B_95]: (k1_enumset1(A_94, A_94, B_95)=k2_tarski(A_94, B_95))), inference(cnfTransformation, [status(thm)], [f_89])).
% 4.35/1.84  tff(c_38, plain, (![E_37, A_31, B_32]: (r2_hidden(E_37, k1_enumset1(A_31, B_32, E_37)))), inference(cnfTransformation, [status(thm)], [f_79])).
% 4.35/1.84  tff(c_200, plain, (![B_95, A_94]: (r2_hidden(B_95, k2_tarski(A_94, B_95)))), inference(superposition, [status(thm), theory('equality')], [c_191, c_38])).
% 4.35/1.84  tff(c_440, plain, (![C_123, B_124, A_125]: (r2_hidden(C_123, B_124) | ~r2_hidden(C_123, A_125) | ~r1_tarski(A_125, B_124))), inference(cnfTransformation, [status(thm)], [f_34])).
% 4.35/1.84  tff(c_2901, plain, (![B_259, B_260, A_261]: (r2_hidden(B_259, B_260) | ~r1_tarski(k2_tarski(A_261, B_259), B_260))), inference(resolution, [status(thm)], [c_200, c_440])).
% 4.35/1.84  tff(c_2959, plain, (![B_267, A_268, B_269]: (r2_hidden(B_267, k2_xboole_0(k2_tarski(A_268, B_267), B_269)))), inference(resolution, [status(thm)], [c_30, c_2901])).
% 4.35/1.84  tff(c_3009, plain, (![C_274, B_275, B_276]: (r2_hidden(C_274, k2_xboole_0(k2_tarski(C_274, B_275), B_276)))), inference(superposition, [status(thm), theory('equality')], [c_2031, c_2959])).
% 4.35/1.84  tff(c_3034, plain, (r2_hidden('#skF_4', '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_1396, c_3009])).
% 4.35/1.84  tff(c_3047, plain, $false, inference(negUnitSimplification, [status(thm)], [c_78, c_3034])).
% 4.35/1.84  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.35/1.84  
% 4.35/1.84  Inference rules
% 4.35/1.84  ----------------------
% 4.35/1.84  #Ref     : 0
% 4.35/1.84  #Sup     : 738
% 4.35/1.84  #Fact    : 0
% 4.35/1.84  #Define  : 0
% 4.35/1.84  #Split   : 2
% 4.35/1.84  #Chain   : 0
% 4.35/1.84  #Close   : 0
% 4.35/1.84  
% 4.35/1.84  Ordering : KBO
% 4.35/1.84  
% 4.35/1.84  Simplification rules
% 4.35/1.84  ----------------------
% 4.35/1.84  #Subsume      : 8
% 4.35/1.84  #Demod        : 385
% 4.35/1.84  #Tautology    : 424
% 4.35/1.84  #SimpNegUnit  : 1
% 4.35/1.84  #BackRed      : 7
% 4.35/1.84  
% 4.35/1.84  #Partial instantiations: 0
% 4.35/1.84  #Strategies tried      : 1
% 4.35/1.84  
% 4.35/1.84  Timing (in seconds)
% 4.35/1.84  ----------------------
% 4.35/1.84  Preprocessing        : 0.35
% 4.35/1.84  Parsing              : 0.18
% 4.35/1.84  CNF conversion       : 0.03
% 4.35/1.84  Main loop            : 0.67
% 4.35/1.84  Inferencing          : 0.21
% 4.35/1.84  Reduction            : 0.28
% 4.35/1.84  Demodulation         : 0.22
% 4.35/1.84  BG Simplification    : 0.03
% 4.35/1.84  Subsumption          : 0.10
% 4.35/1.84  Abstraction          : 0.03
% 4.35/1.84  MUC search           : 0.00
% 4.35/1.84  Cooper               : 0.00
% 4.35/1.84  Total                : 1.05
% 4.35/1.84  Index Insertion      : 0.00
% 4.35/1.84  Index Deletion       : 0.00
% 4.35/1.84  Index Matching       : 0.00
% 4.35/1.84  BG Taut test         : 0.00
%------------------------------------------------------------------------------
