%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:46:08 EST 2020

% Result     : Theorem 10.94s
% Output     : CNFRefutation 10.94s
% Verified   : 
% Statistics : Number of formulae       :   42 (  67 expanded)
%              Number of leaves         :   22 (  34 expanded)
%              Depth                    :    9
%              Number of atoms          :   59 ( 141 expanded)
%              Number of equality atoms :   30 (  62 expanded)
%              Maximal formula depth    :    8 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_1 > #skF_4 > #skF_5 > #skF_6 > #skF_2 > #skF_3

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

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_47,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

tff(f_34,axiom,(
    ! [A,B,C] :
      ( C = k2_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            | r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).

tff(f_51,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_49,axiom,(
    ! [A,B,C] : k1_enumset1(A,B,C) = k2_xboole_0(k1_tarski(A),k2_tarski(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_enumset1)).

tff(f_54,negated_conjecture,(
    ~ ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(c_28,plain,(
    ! [D_16,B_12] : r2_hidden(D_16,k2_tarski(D_16,B_12)) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_533,plain,(
    ! [A_114,B_115,C_116] :
      ( r2_hidden('#skF_1'(A_114,B_115,C_116),B_115)
      | r2_hidden('#skF_1'(A_114,B_115,C_116),A_114)
      | r2_hidden('#skF_2'(A_114,B_115,C_116),C_116)
      | k2_xboole_0(A_114,B_115) = C_116 ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_16,plain,(
    ! [A_1,B_2,C_3] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2,C_3),C_3)
      | r2_hidden('#skF_2'(A_1,B_2,C_3),C_3)
      | k2_xboole_0(A_1,B_2) = C_3 ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_614,plain,(
    ! [A_114,B_115] :
      ( r2_hidden('#skF_1'(A_114,B_115,B_115),A_114)
      | r2_hidden('#skF_2'(A_114,B_115,B_115),B_115)
      | k2_xboole_0(A_114,B_115) = B_115 ) ),
    inference(resolution,[status(thm)],[c_533,c_16])).

tff(c_845,plain,(
    ! [A_124,B_125,C_126] :
      ( r2_hidden('#skF_1'(A_124,B_125,C_126),B_125)
      | r2_hidden('#skF_1'(A_124,B_125,C_126),A_124)
      | ~ r2_hidden('#skF_2'(A_124,B_125,C_126),B_125)
      | k2_xboole_0(A_124,B_125) = C_126 ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_8,plain,(
    ! [A_1,B_2,C_3] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2,C_3),C_3)
      | ~ r2_hidden('#skF_2'(A_1,B_2,C_3),B_2)
      | k2_xboole_0(A_1,B_2) = C_3 ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_1650,plain,(
    ! [A_151,B_152] :
      ( r2_hidden('#skF_1'(A_151,B_152,B_152),A_151)
      | ~ r2_hidden('#skF_2'(A_151,B_152,B_152),B_152)
      | k2_xboole_0(A_151,B_152) = B_152 ) ),
    inference(resolution,[status(thm)],[c_845,c_8])).

tff(c_1676,plain,(
    ! [A_153,B_154] :
      ( r2_hidden('#skF_1'(A_153,B_154,B_154),A_153)
      | k2_xboole_0(A_153,B_154) = B_154 ) ),
    inference(resolution,[status(thm)],[c_614,c_1650])).

tff(c_44,plain,(
    ! [A_20] : k2_tarski(A_20,A_20) = k1_tarski(A_20) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_86,plain,(
    ! [D_37,B_38,A_39] :
      ( D_37 = B_38
      | D_37 = A_39
      | ~ r2_hidden(D_37,k2_tarski(A_39,B_38)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_95,plain,(
    ! [D_37,A_20] :
      ( D_37 = A_20
      | D_37 = A_20
      | ~ r2_hidden(D_37,k1_tarski(A_20)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_86])).

tff(c_1734,plain,(
    ! [A_155,B_156] :
      ( '#skF_1'(k1_tarski(A_155),B_156,B_156) = A_155
      | k2_xboole_0(k1_tarski(A_155),B_156) = B_156 ) ),
    inference(resolution,[status(thm)],[c_1676,c_95])).

tff(c_24409,plain,(
    ! [A_8213,B_8214] :
      ( ~ r2_hidden(A_8213,B_8214)
      | r2_hidden('#skF_2'(k1_tarski(A_8213),B_8214,B_8214),B_8214)
      | k2_xboole_0(k1_tarski(A_8213),B_8214) = B_8214
      | k2_xboole_0(k1_tarski(A_8213),B_8214) = B_8214 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1734,c_16])).

tff(c_1783,plain,(
    ! [A_155,B_156] :
      ( ~ r2_hidden(A_155,B_156)
      | ~ r2_hidden('#skF_2'(k1_tarski(A_155),B_156,B_156),B_156)
      | k2_xboole_0(k1_tarski(A_155),B_156) = B_156
      | k2_xboole_0(k1_tarski(A_155),B_156) = B_156 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1734,c_8])).

tff(c_24490,plain,(
    ! [A_8319,B_8320] :
      ( ~ r2_hidden(A_8319,B_8320)
      | k2_xboole_0(k1_tarski(A_8319),B_8320) = B_8320 ) ),
    inference(resolution,[status(thm)],[c_24409,c_1783])).

tff(c_42,plain,(
    ! [A_17,B_18,C_19] : k2_xboole_0(k1_tarski(A_17),k2_tarski(B_18,C_19)) = k1_enumset1(A_17,B_18,C_19) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_24856,plain,(
    ! [A_8638,B_8639,C_8640] :
      ( k1_enumset1(A_8638,B_8639,C_8640) = k2_tarski(B_8639,C_8640)
      | ~ r2_hidden(A_8638,k2_tarski(B_8639,C_8640)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24490,c_42])).

tff(c_24984,plain,(
    ! [D_16,B_12] : k1_enumset1(D_16,D_16,B_12) = k2_tarski(D_16,B_12) ),
    inference(resolution,[status(thm)],[c_28,c_24856])).

tff(c_46,plain,(
    k1_enumset1('#skF_5','#skF_5','#skF_6') != k2_tarski('#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_25051,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_24984,c_46])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.33  % Computer   : n017.cluster.edu
% 0.14/0.33  % Model      : x86_64 x86_64
% 0.14/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.33  % Memory     : 8042.1875MB
% 0.14/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.33  % CPULimit   : 60
% 0.14/0.33  % DateTime   : Tue Dec  1 14:19:01 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 10.94/4.03  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.94/4.04  
% 10.94/4.04  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.94/4.04  %$ r2_hidden > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_1 > #skF_4 > #skF_5 > #skF_6 > #skF_2 > #skF_3
% 10.94/4.04  
% 10.94/4.04  %Foreground sorts:
% 10.94/4.04  
% 10.94/4.04  
% 10.94/4.04  %Background operators:
% 10.94/4.04  
% 10.94/4.04  
% 10.94/4.04  %Foreground operators:
% 10.94/4.04  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 10.94/4.04  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 10.94/4.04  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 10.94/4.04  tff(k1_tarski, type, k1_tarski: $i > $i).
% 10.94/4.04  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 10.94/4.04  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 10.94/4.04  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 10.94/4.04  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 10.94/4.04  tff('#skF_5', type, '#skF_5': $i).
% 10.94/4.04  tff('#skF_6', type, '#skF_6': $i).
% 10.94/4.04  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 10.94/4.04  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 10.94/4.04  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 10.94/4.04  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 10.94/4.04  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 10.94/4.04  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 10.94/4.04  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 10.94/4.04  
% 10.94/4.05  tff(f_47, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_tarski)).
% 10.94/4.05  tff(f_34, axiom, (![A, B, C]: ((C = k2_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) | r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_xboole_0)).
% 10.94/4.05  tff(f_51, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 10.94/4.05  tff(f_49, axiom, (![A, B, C]: (k1_enumset1(A, B, C) = k2_xboole_0(k1_tarski(A), k2_tarski(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t42_enumset1)).
% 10.94/4.05  tff(f_54, negated_conjecture, ~(![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 10.94/4.05  tff(c_28, plain, (![D_16, B_12]: (r2_hidden(D_16, k2_tarski(D_16, B_12)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 10.94/4.05  tff(c_533, plain, (![A_114, B_115, C_116]: (r2_hidden('#skF_1'(A_114, B_115, C_116), B_115) | r2_hidden('#skF_1'(A_114, B_115, C_116), A_114) | r2_hidden('#skF_2'(A_114, B_115, C_116), C_116) | k2_xboole_0(A_114, B_115)=C_116)), inference(cnfTransformation, [status(thm)], [f_34])).
% 10.94/4.05  tff(c_16, plain, (![A_1, B_2, C_3]: (~r2_hidden('#skF_1'(A_1, B_2, C_3), C_3) | r2_hidden('#skF_2'(A_1, B_2, C_3), C_3) | k2_xboole_0(A_1, B_2)=C_3)), inference(cnfTransformation, [status(thm)], [f_34])).
% 10.94/4.05  tff(c_614, plain, (![A_114, B_115]: (r2_hidden('#skF_1'(A_114, B_115, B_115), A_114) | r2_hidden('#skF_2'(A_114, B_115, B_115), B_115) | k2_xboole_0(A_114, B_115)=B_115)), inference(resolution, [status(thm)], [c_533, c_16])).
% 10.94/4.05  tff(c_845, plain, (![A_124, B_125, C_126]: (r2_hidden('#skF_1'(A_124, B_125, C_126), B_125) | r2_hidden('#skF_1'(A_124, B_125, C_126), A_124) | ~r2_hidden('#skF_2'(A_124, B_125, C_126), B_125) | k2_xboole_0(A_124, B_125)=C_126)), inference(cnfTransformation, [status(thm)], [f_34])).
% 10.94/4.05  tff(c_8, plain, (![A_1, B_2, C_3]: (~r2_hidden('#skF_1'(A_1, B_2, C_3), C_3) | ~r2_hidden('#skF_2'(A_1, B_2, C_3), B_2) | k2_xboole_0(A_1, B_2)=C_3)), inference(cnfTransformation, [status(thm)], [f_34])).
% 10.94/4.05  tff(c_1650, plain, (![A_151, B_152]: (r2_hidden('#skF_1'(A_151, B_152, B_152), A_151) | ~r2_hidden('#skF_2'(A_151, B_152, B_152), B_152) | k2_xboole_0(A_151, B_152)=B_152)), inference(resolution, [status(thm)], [c_845, c_8])).
% 10.94/4.05  tff(c_1676, plain, (![A_153, B_154]: (r2_hidden('#skF_1'(A_153, B_154, B_154), A_153) | k2_xboole_0(A_153, B_154)=B_154)), inference(resolution, [status(thm)], [c_614, c_1650])).
% 10.94/4.05  tff(c_44, plain, (![A_20]: (k2_tarski(A_20, A_20)=k1_tarski(A_20))), inference(cnfTransformation, [status(thm)], [f_51])).
% 10.94/4.05  tff(c_86, plain, (![D_37, B_38, A_39]: (D_37=B_38 | D_37=A_39 | ~r2_hidden(D_37, k2_tarski(A_39, B_38)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 10.94/4.05  tff(c_95, plain, (![D_37, A_20]: (D_37=A_20 | D_37=A_20 | ~r2_hidden(D_37, k1_tarski(A_20)))), inference(superposition, [status(thm), theory('equality')], [c_44, c_86])).
% 10.94/4.05  tff(c_1734, plain, (![A_155, B_156]: ('#skF_1'(k1_tarski(A_155), B_156, B_156)=A_155 | k2_xboole_0(k1_tarski(A_155), B_156)=B_156)), inference(resolution, [status(thm)], [c_1676, c_95])).
% 10.94/4.05  tff(c_24409, plain, (![A_8213, B_8214]: (~r2_hidden(A_8213, B_8214) | r2_hidden('#skF_2'(k1_tarski(A_8213), B_8214, B_8214), B_8214) | k2_xboole_0(k1_tarski(A_8213), B_8214)=B_8214 | k2_xboole_0(k1_tarski(A_8213), B_8214)=B_8214)), inference(superposition, [status(thm), theory('equality')], [c_1734, c_16])).
% 10.94/4.05  tff(c_1783, plain, (![A_155, B_156]: (~r2_hidden(A_155, B_156) | ~r2_hidden('#skF_2'(k1_tarski(A_155), B_156, B_156), B_156) | k2_xboole_0(k1_tarski(A_155), B_156)=B_156 | k2_xboole_0(k1_tarski(A_155), B_156)=B_156)), inference(superposition, [status(thm), theory('equality')], [c_1734, c_8])).
% 10.94/4.05  tff(c_24490, plain, (![A_8319, B_8320]: (~r2_hidden(A_8319, B_8320) | k2_xboole_0(k1_tarski(A_8319), B_8320)=B_8320)), inference(resolution, [status(thm)], [c_24409, c_1783])).
% 10.94/4.05  tff(c_42, plain, (![A_17, B_18, C_19]: (k2_xboole_0(k1_tarski(A_17), k2_tarski(B_18, C_19))=k1_enumset1(A_17, B_18, C_19))), inference(cnfTransformation, [status(thm)], [f_49])).
% 10.94/4.05  tff(c_24856, plain, (![A_8638, B_8639, C_8640]: (k1_enumset1(A_8638, B_8639, C_8640)=k2_tarski(B_8639, C_8640) | ~r2_hidden(A_8638, k2_tarski(B_8639, C_8640)))), inference(superposition, [status(thm), theory('equality')], [c_24490, c_42])).
% 10.94/4.05  tff(c_24984, plain, (![D_16, B_12]: (k1_enumset1(D_16, D_16, B_12)=k2_tarski(D_16, B_12))), inference(resolution, [status(thm)], [c_28, c_24856])).
% 10.94/4.05  tff(c_46, plain, (k1_enumset1('#skF_5', '#skF_5', '#skF_6')!=k2_tarski('#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_54])).
% 10.94/4.05  tff(c_25051, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_24984, c_46])).
% 10.94/4.05  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.94/4.05  
% 10.94/4.05  Inference rules
% 10.94/4.05  ----------------------
% 10.94/4.05  #Ref     : 0
% 10.94/4.05  #Sup     : 4905
% 10.94/4.05  #Fact    : 18
% 10.94/4.05  #Define  : 0
% 10.94/4.05  #Split   : 0
% 10.94/4.05  #Chain   : 0
% 10.94/4.05  #Close   : 0
% 10.94/4.05  
% 10.94/4.05  Ordering : KBO
% 10.94/4.05  
% 10.94/4.05  Simplification rules
% 10.94/4.05  ----------------------
% 10.94/4.05  #Subsume      : 1057
% 10.94/4.05  #Demod        : 2184
% 10.94/4.05  #Tautology    : 1439
% 10.94/4.05  #SimpNegUnit  : 0
% 10.94/4.05  #BackRed      : 2
% 10.94/4.05  
% 10.94/4.05  #Partial instantiations: 4277
% 10.94/4.05  #Strategies tried      : 1
% 10.94/4.05  
% 10.94/4.05  Timing (in seconds)
% 10.94/4.05  ----------------------
% 10.94/4.05  Preprocessing        : 0.29
% 10.94/4.05  Parsing              : 0.14
% 10.94/4.05  CNF conversion       : 0.02
% 10.94/4.05  Main loop            : 3.01
% 10.94/4.05  Inferencing          : 1.01
% 10.94/4.05  Reduction            : 0.69
% 10.94/4.05  Demodulation         : 0.49
% 10.94/4.05  BG Simplification    : 0.16
% 10.94/4.05  Subsumption          : 1.02
% 10.94/4.05  Abstraction          : 0.26
% 10.94/4.05  MUC search           : 0.00
% 10.94/4.05  Cooper               : 0.00
% 10.94/4.05  Total                : 3.33
% 10.94/4.05  Index Insertion      : 0.00
% 10.94/4.05  Index Deletion       : 0.00
% 10.94/4.05  Index Matching       : 0.00
% 10.94/4.05  BG Taut test         : 0.00
%------------------------------------------------------------------------------
