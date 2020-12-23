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
% DateTime   : Thu Dec  3 09:42:45 EST 2020

% Result     : Theorem 3.20s
% Output     : CNFRefutation 3.20s
% Verified   : 
% Statistics : Number of formulae       :   36 (  49 expanded)
%              Number of leaves         :   19 (  26 expanded)
%              Depth                    :    9
%              Number of atoms          :   48 (  82 expanded)
%              Number of equality atoms :   15 (  26 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k4_xboole_0 > #nlpp > k1_xboole_0 > #skF_7 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_5 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_56,negated_conjecture,(
    ~ ! [A,B] :
        ( r1_tarski(A,k4_xboole_0(B,A))
       => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_xboole_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( ! [C] :
          ( r2_hidden(C,A)
        <=> r2_hidden(C,B) )
     => A = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tarski)).

tff(f_51,axiom,(
    ! [A] : k4_xboole_0(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).

tff(f_42,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(c_36,plain,(
    k1_xboole_0 != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_38,plain,(
    r1_tarski('#skF_6',k4_xboole_0('#skF_7','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_32,plain,(
    ! [A_12,B_13] :
      ( r2_hidden('#skF_4'(A_12,B_13),B_13)
      | r2_hidden('#skF_5'(A_12,B_13),A_12)
      | B_13 = A_12 ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_164,plain,(
    ! [A_49,B_50] :
      ( r2_hidden('#skF_4'(A_49,B_50),B_50)
      | r2_hidden('#skF_5'(A_49,B_50),A_49)
      | B_50 = A_49 ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_34,plain,(
    ! [A_15] : k4_xboole_0(k1_xboole_0,A_15) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_63,plain,(
    ! [D_25,B_26,A_27] :
      ( ~ r2_hidden(D_25,B_26)
      | ~ r2_hidden(D_25,k4_xboole_0(A_27,B_26)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_70,plain,(
    ! [D_25,A_15] :
      ( ~ r2_hidden(D_25,A_15)
      | ~ r2_hidden(D_25,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_63])).

tff(c_379,plain,(
    ! [A_75,B_76] :
      ( ~ r2_hidden('#skF_5'(A_75,B_76),k1_xboole_0)
      | r2_hidden('#skF_4'(A_75,B_76),B_76)
      | B_76 = A_75 ) ),
    inference(resolution,[status(thm)],[c_164,c_70])).

tff(c_391,plain,(
    ! [B_13] :
      ( r2_hidden('#skF_4'(k1_xboole_0,B_13),B_13)
      | k1_xboole_0 = B_13 ) ),
    inference(resolution,[status(thm)],[c_32,c_379])).

tff(c_436,plain,(
    ! [B_80] :
      ( r2_hidden('#skF_4'(k1_xboole_0,B_80),B_80)
      | k1_xboole_0 = B_80 ) ),
    inference(resolution,[status(thm)],[c_32,c_379])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_503,plain,(
    ! [B_86,B_87] :
      ( r2_hidden('#skF_4'(k1_xboole_0,B_86),B_87)
      | ~ r1_tarski(B_86,B_87)
      | k1_xboole_0 = B_86 ) ),
    inference(resolution,[status(thm)],[c_436,c_2])).

tff(c_10,plain,(
    ! [D_11,B_7,A_6] :
      ( ~ r2_hidden(D_11,B_7)
      | ~ r2_hidden(D_11,k4_xboole_0(A_6,B_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_1107,plain,(
    ! [B_142,B_143,A_144] :
      ( ~ r2_hidden('#skF_4'(k1_xboole_0,B_142),B_143)
      | ~ r1_tarski(B_142,k4_xboole_0(A_144,B_143))
      | k1_xboole_0 = B_142 ) ),
    inference(resolution,[status(thm)],[c_503,c_10])).

tff(c_1216,plain,(
    ! [B_149,A_150] :
      ( ~ r1_tarski(B_149,k4_xboole_0(A_150,B_149))
      | k1_xboole_0 = B_149 ) ),
    inference(resolution,[status(thm)],[c_391,c_1107])).

tff(c_1226,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(resolution,[status(thm)],[c_38,c_1216])).

tff(c_1235,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_1226])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:02:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.20/1.50  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.20/1.50  
% 3.20/1.50  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.20/1.51  %$ r2_hidden > r1_tarski > k4_xboole_0 > #nlpp > k1_xboole_0 > #skF_7 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_5 > #skF_4
% 3.20/1.51  
% 3.20/1.51  %Foreground sorts:
% 3.20/1.51  
% 3.20/1.51  
% 3.20/1.51  %Background operators:
% 3.20/1.51  
% 3.20/1.51  
% 3.20/1.51  %Foreground operators:
% 3.20/1.51  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.20/1.51  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.20/1.51  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.20/1.51  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.20/1.51  tff('#skF_7', type, '#skF_7': $i).
% 3.20/1.51  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.20/1.51  tff('#skF_6', type, '#skF_6': $i).
% 3.20/1.51  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 3.20/1.51  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.20/1.51  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 3.20/1.51  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.20/1.51  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.20/1.51  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 3.20/1.51  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 3.20/1.51  
% 3.20/1.51  tff(f_56, negated_conjecture, ~(![A, B]: (r1_tarski(A, k4_xboole_0(B, A)) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_xboole_1)).
% 3.20/1.51  tff(f_49, axiom, (![A, B]: ((![C]: (r2_hidden(C, A) <=> r2_hidden(C, B))) => (A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_tarski)).
% 3.20/1.51  tff(f_51, axiom, (![A]: (k4_xboole_0(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_boole)).
% 3.20/1.51  tff(f_42, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_xboole_0)).
% 3.20/1.51  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 3.20/1.51  tff(c_36, plain, (k1_xboole_0!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.20/1.51  tff(c_38, plain, (r1_tarski('#skF_6', k4_xboole_0('#skF_7', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.20/1.51  tff(c_32, plain, (![A_12, B_13]: (r2_hidden('#skF_4'(A_12, B_13), B_13) | r2_hidden('#skF_5'(A_12, B_13), A_12) | B_13=A_12)), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.20/1.51  tff(c_164, plain, (![A_49, B_50]: (r2_hidden('#skF_4'(A_49, B_50), B_50) | r2_hidden('#skF_5'(A_49, B_50), A_49) | B_50=A_49)), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.20/1.51  tff(c_34, plain, (![A_15]: (k4_xboole_0(k1_xboole_0, A_15)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.20/1.51  tff(c_63, plain, (![D_25, B_26, A_27]: (~r2_hidden(D_25, B_26) | ~r2_hidden(D_25, k4_xboole_0(A_27, B_26)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.20/1.51  tff(c_70, plain, (![D_25, A_15]: (~r2_hidden(D_25, A_15) | ~r2_hidden(D_25, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_34, c_63])).
% 3.20/1.51  tff(c_379, plain, (![A_75, B_76]: (~r2_hidden('#skF_5'(A_75, B_76), k1_xboole_0) | r2_hidden('#skF_4'(A_75, B_76), B_76) | B_76=A_75)), inference(resolution, [status(thm)], [c_164, c_70])).
% 3.20/1.51  tff(c_391, plain, (![B_13]: (r2_hidden('#skF_4'(k1_xboole_0, B_13), B_13) | k1_xboole_0=B_13)), inference(resolution, [status(thm)], [c_32, c_379])).
% 3.20/1.51  tff(c_436, plain, (![B_80]: (r2_hidden('#skF_4'(k1_xboole_0, B_80), B_80) | k1_xboole_0=B_80)), inference(resolution, [status(thm)], [c_32, c_379])).
% 3.20/1.51  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.20/1.51  tff(c_503, plain, (![B_86, B_87]: (r2_hidden('#skF_4'(k1_xboole_0, B_86), B_87) | ~r1_tarski(B_86, B_87) | k1_xboole_0=B_86)), inference(resolution, [status(thm)], [c_436, c_2])).
% 3.20/1.51  tff(c_10, plain, (![D_11, B_7, A_6]: (~r2_hidden(D_11, B_7) | ~r2_hidden(D_11, k4_xboole_0(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.20/1.51  tff(c_1107, plain, (![B_142, B_143, A_144]: (~r2_hidden('#skF_4'(k1_xboole_0, B_142), B_143) | ~r1_tarski(B_142, k4_xboole_0(A_144, B_143)) | k1_xboole_0=B_142)), inference(resolution, [status(thm)], [c_503, c_10])).
% 3.20/1.51  tff(c_1216, plain, (![B_149, A_150]: (~r1_tarski(B_149, k4_xboole_0(A_150, B_149)) | k1_xboole_0=B_149)), inference(resolution, [status(thm)], [c_391, c_1107])).
% 3.20/1.51  tff(c_1226, plain, (k1_xboole_0='#skF_6'), inference(resolution, [status(thm)], [c_38, c_1216])).
% 3.20/1.51  tff(c_1235, plain, $false, inference(negUnitSimplification, [status(thm)], [c_36, c_1226])).
% 3.20/1.51  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.20/1.51  
% 3.20/1.51  Inference rules
% 3.20/1.51  ----------------------
% 3.20/1.51  #Ref     : 0
% 3.20/1.51  #Sup     : 259
% 3.20/1.51  #Fact    : 0
% 3.20/1.51  #Define  : 0
% 3.20/1.51  #Split   : 1
% 3.20/1.52  #Chain   : 0
% 3.20/1.52  #Close   : 0
% 3.20/1.52  
% 3.20/1.52  Ordering : KBO
% 3.20/1.52  
% 3.20/1.52  Simplification rules
% 3.20/1.52  ----------------------
% 3.20/1.52  #Subsume      : 58
% 3.20/1.52  #Demod        : 76
% 3.20/1.52  #Tautology    : 70
% 3.20/1.52  #SimpNegUnit  : 11
% 3.20/1.52  #BackRed      : 1
% 3.20/1.52  
% 3.20/1.52  #Partial instantiations: 0
% 3.20/1.52  #Strategies tried      : 1
% 3.20/1.52  
% 3.20/1.52  Timing (in seconds)
% 3.20/1.52  ----------------------
% 3.20/1.52  Preprocessing        : 0.30
% 3.20/1.52  Parsing              : 0.16
% 3.20/1.52  CNF conversion       : 0.02
% 3.20/1.52  Main loop            : 0.43
% 3.20/1.52  Inferencing          : 0.17
% 3.20/1.52  Reduction            : 0.11
% 3.20/1.52  Demodulation         : 0.07
% 3.20/1.52  BG Simplification    : 0.02
% 3.20/1.52  Subsumption          : 0.10
% 3.20/1.52  Abstraction          : 0.02
% 3.20/1.52  MUC search           : 0.00
% 3.20/1.52  Cooper               : 0.00
% 3.20/1.52  Total                : 0.75
% 3.20/1.52  Index Insertion      : 0.00
% 3.20/1.52  Index Deletion       : 0.00
% 3.20/1.52  Index Matching       : 0.00
% 3.20/1.52  BG Taut test         : 0.00
%------------------------------------------------------------------------------
