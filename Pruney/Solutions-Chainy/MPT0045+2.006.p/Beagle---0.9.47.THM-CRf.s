%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:42:45 EST 2020

% Result     : Theorem 3.22s
% Output     : CNFRefutation 3.27s
% Verified   : 
% Statistics : Number of formulae       :   41 (  49 expanded)
%              Number of leaves         :   20 (  26 expanded)
%              Depth                    :   10
%              Number of atoms          :   61 (  85 expanded)
%              Number of equality atoms :   18 (  24 expanded)
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

tff(f_58,negated_conjecture,(
    ~ ! [A,B] :
        ( r1_tarski(A,k4_xboole_0(B,A))
       => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_xboole_1)).

tff(f_51,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( ! [C] :
          ( r2_hidden(C,A)
        <=> r2_hidden(C,B) )
     => A = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tarski)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_53,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_42,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

tff(c_38,plain,(
    k1_xboole_0 != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_40,plain,(
    r1_tarski('#skF_6',k4_xboole_0('#skF_7','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_34,plain,(
    ! [A_15] : r1_tarski(k1_xboole_0,A_15) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_178,plain,(
    ! [A_50,B_51] :
      ( r2_hidden('#skF_4'(A_50,B_51),B_51)
      | r2_hidden('#skF_5'(A_50,B_51),A_50)
      | B_51 = A_50 ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_1340,plain,(
    ! [A_158,B_159,B_160] :
      ( r2_hidden('#skF_5'(A_158,B_159),B_160)
      | ~ r1_tarski(A_158,B_160)
      | r2_hidden('#skF_4'(A_158,B_159),B_159)
      | B_159 = A_158 ) ),
    inference(resolution,[status(thm)],[c_178,c_2])).

tff(c_28,plain,(
    ! [A_12,B_13] :
      ( r2_hidden('#skF_4'(A_12,B_13),B_13)
      | ~ r2_hidden('#skF_5'(A_12,B_13),B_13)
      | B_13 = A_12 ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_1383,plain,(
    ! [A_158,B_160] :
      ( ~ r1_tarski(A_158,B_160)
      | r2_hidden('#skF_4'(A_158,B_160),B_160)
      | B_160 = A_158 ) ),
    inference(resolution,[status(thm)],[c_1340,c_28])).

tff(c_32,plain,(
    ! [A_12,B_13] :
      ( r2_hidden('#skF_4'(A_12,B_13),B_13)
      | r2_hidden('#skF_5'(A_12,B_13),A_12)
      | B_13 = A_12 ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_36,plain,(
    ! [A_16] : k4_xboole_0(A_16,k1_xboole_0) = A_16 ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_51,plain,(
    ! [D_19,B_20,A_21] :
      ( ~ r2_hidden(D_19,B_20)
      | ~ r2_hidden(D_19,k4_xboole_0(A_21,B_20)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_54,plain,(
    ! [D_19,A_16] :
      ( ~ r2_hidden(D_19,k1_xboole_0)
      | ~ r2_hidden(D_19,A_16) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_51])).

tff(c_467,plain,(
    ! [B_82,A_83] :
      ( ~ r2_hidden('#skF_5'(k1_xboole_0,B_82),A_83)
      | r2_hidden('#skF_4'(k1_xboole_0,B_82),B_82)
      | k1_xboole_0 = B_82 ) ),
    inference(resolution,[status(thm)],[c_178,c_54])).

tff(c_480,plain,(
    ! [B_84] :
      ( r2_hidden('#skF_4'(k1_xboole_0,B_84),B_84)
      | k1_xboole_0 = B_84 ) ),
    inference(resolution,[status(thm)],[c_32,c_467])).

tff(c_678,plain,(
    ! [B_100,B_101] :
      ( r2_hidden('#skF_4'(k1_xboole_0,B_100),B_101)
      | ~ r1_tarski(B_100,B_101)
      | k1_xboole_0 = B_100 ) ),
    inference(resolution,[status(thm)],[c_480,c_2])).

tff(c_10,plain,(
    ! [D_11,B_7,A_6] :
      ( ~ r2_hidden(D_11,B_7)
      | ~ r2_hidden(D_11,k4_xboole_0(A_6,B_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_1446,plain,(
    ! [B_163,B_164,A_165] :
      ( ~ r2_hidden('#skF_4'(k1_xboole_0,B_163),B_164)
      | ~ r1_tarski(B_163,k4_xboole_0(A_165,B_164))
      | k1_xboole_0 = B_163 ) ),
    inference(resolution,[status(thm)],[c_678,c_10])).

tff(c_1449,plain,(
    ! [B_160,A_165] :
      ( ~ r1_tarski(B_160,k4_xboole_0(A_165,B_160))
      | ~ r1_tarski(k1_xboole_0,B_160)
      | k1_xboole_0 = B_160 ) ),
    inference(resolution,[status(thm)],[c_1383,c_1446])).

tff(c_1497,plain,(
    ! [B_167,A_168] :
      ( ~ r1_tarski(B_167,k4_xboole_0(A_168,B_167))
      | k1_xboole_0 = B_167 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_1449])).

tff(c_1506,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(resolution,[status(thm)],[c_40,c_1497])).

tff(c_1517,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_1506])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:52:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.22/1.46  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.22/1.47  
% 3.22/1.47  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.22/1.47  %$ r2_hidden > r1_tarski > k4_xboole_0 > #nlpp > k1_xboole_0 > #skF_7 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_5 > #skF_4
% 3.22/1.47  
% 3.22/1.47  %Foreground sorts:
% 3.22/1.47  
% 3.22/1.47  
% 3.22/1.47  %Background operators:
% 3.22/1.47  
% 3.22/1.47  
% 3.22/1.47  %Foreground operators:
% 3.22/1.47  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.22/1.47  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.22/1.47  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.22/1.47  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.22/1.47  tff('#skF_7', type, '#skF_7': $i).
% 3.22/1.47  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.22/1.47  tff('#skF_6', type, '#skF_6': $i).
% 3.22/1.47  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 3.22/1.47  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.22/1.47  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 3.22/1.47  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.22/1.47  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.22/1.47  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 3.22/1.47  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 3.22/1.47  
% 3.27/1.48  tff(f_58, negated_conjecture, ~(![A, B]: (r1_tarski(A, k4_xboole_0(B, A)) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_xboole_1)).
% 3.27/1.48  tff(f_51, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 3.27/1.48  tff(f_49, axiom, (![A, B]: ((![C]: (r2_hidden(C, A) <=> r2_hidden(C, B))) => (A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_tarski)).
% 3.27/1.48  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 3.27/1.48  tff(f_53, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 3.27/1.48  tff(f_42, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 3.27/1.48  tff(c_38, plain, (k1_xboole_0!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.27/1.48  tff(c_40, plain, (r1_tarski('#skF_6', k4_xboole_0('#skF_7', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.27/1.48  tff(c_34, plain, (![A_15]: (r1_tarski(k1_xboole_0, A_15))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.27/1.48  tff(c_178, plain, (![A_50, B_51]: (r2_hidden('#skF_4'(A_50, B_51), B_51) | r2_hidden('#skF_5'(A_50, B_51), A_50) | B_51=A_50)), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.27/1.48  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.27/1.48  tff(c_1340, plain, (![A_158, B_159, B_160]: (r2_hidden('#skF_5'(A_158, B_159), B_160) | ~r1_tarski(A_158, B_160) | r2_hidden('#skF_4'(A_158, B_159), B_159) | B_159=A_158)), inference(resolution, [status(thm)], [c_178, c_2])).
% 3.27/1.48  tff(c_28, plain, (![A_12, B_13]: (r2_hidden('#skF_4'(A_12, B_13), B_13) | ~r2_hidden('#skF_5'(A_12, B_13), B_13) | B_13=A_12)), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.27/1.48  tff(c_1383, plain, (![A_158, B_160]: (~r1_tarski(A_158, B_160) | r2_hidden('#skF_4'(A_158, B_160), B_160) | B_160=A_158)), inference(resolution, [status(thm)], [c_1340, c_28])).
% 3.27/1.48  tff(c_32, plain, (![A_12, B_13]: (r2_hidden('#skF_4'(A_12, B_13), B_13) | r2_hidden('#skF_5'(A_12, B_13), A_12) | B_13=A_12)), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.27/1.48  tff(c_36, plain, (![A_16]: (k4_xboole_0(A_16, k1_xboole_0)=A_16)), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.27/1.48  tff(c_51, plain, (![D_19, B_20, A_21]: (~r2_hidden(D_19, B_20) | ~r2_hidden(D_19, k4_xboole_0(A_21, B_20)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.27/1.48  tff(c_54, plain, (![D_19, A_16]: (~r2_hidden(D_19, k1_xboole_0) | ~r2_hidden(D_19, A_16))), inference(superposition, [status(thm), theory('equality')], [c_36, c_51])).
% 3.27/1.48  tff(c_467, plain, (![B_82, A_83]: (~r2_hidden('#skF_5'(k1_xboole_0, B_82), A_83) | r2_hidden('#skF_4'(k1_xboole_0, B_82), B_82) | k1_xboole_0=B_82)), inference(resolution, [status(thm)], [c_178, c_54])).
% 3.27/1.48  tff(c_480, plain, (![B_84]: (r2_hidden('#skF_4'(k1_xboole_0, B_84), B_84) | k1_xboole_0=B_84)), inference(resolution, [status(thm)], [c_32, c_467])).
% 3.27/1.48  tff(c_678, plain, (![B_100, B_101]: (r2_hidden('#skF_4'(k1_xboole_0, B_100), B_101) | ~r1_tarski(B_100, B_101) | k1_xboole_0=B_100)), inference(resolution, [status(thm)], [c_480, c_2])).
% 3.27/1.48  tff(c_10, plain, (![D_11, B_7, A_6]: (~r2_hidden(D_11, B_7) | ~r2_hidden(D_11, k4_xboole_0(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.27/1.48  tff(c_1446, plain, (![B_163, B_164, A_165]: (~r2_hidden('#skF_4'(k1_xboole_0, B_163), B_164) | ~r1_tarski(B_163, k4_xboole_0(A_165, B_164)) | k1_xboole_0=B_163)), inference(resolution, [status(thm)], [c_678, c_10])).
% 3.27/1.48  tff(c_1449, plain, (![B_160, A_165]: (~r1_tarski(B_160, k4_xboole_0(A_165, B_160)) | ~r1_tarski(k1_xboole_0, B_160) | k1_xboole_0=B_160)), inference(resolution, [status(thm)], [c_1383, c_1446])).
% 3.27/1.48  tff(c_1497, plain, (![B_167, A_168]: (~r1_tarski(B_167, k4_xboole_0(A_168, B_167)) | k1_xboole_0=B_167)), inference(demodulation, [status(thm), theory('equality')], [c_34, c_1449])).
% 3.27/1.48  tff(c_1506, plain, (k1_xboole_0='#skF_6'), inference(resolution, [status(thm)], [c_40, c_1497])).
% 3.27/1.48  tff(c_1517, plain, $false, inference(negUnitSimplification, [status(thm)], [c_38, c_1506])).
% 3.27/1.48  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.27/1.48  
% 3.27/1.48  Inference rules
% 3.27/1.48  ----------------------
% 3.27/1.48  #Ref     : 0
% 3.27/1.48  #Sup     : 311
% 3.27/1.48  #Fact    : 0
% 3.27/1.48  #Define  : 0
% 3.27/1.48  #Split   : 2
% 3.27/1.48  #Chain   : 0
% 3.27/1.48  #Close   : 0
% 3.27/1.48  
% 3.27/1.48  Ordering : KBO
% 3.27/1.48  
% 3.27/1.48  Simplification rules
% 3.27/1.48  ----------------------
% 3.27/1.48  #Subsume      : 83
% 3.27/1.48  #Demod        : 106
% 3.27/1.48  #Tautology    : 97
% 3.27/1.48  #SimpNegUnit  : 11
% 3.27/1.48  #BackRed      : 3
% 3.27/1.48  
% 3.27/1.48  #Partial instantiations: 0
% 3.27/1.48  #Strategies tried      : 1
% 3.27/1.48  
% 3.27/1.48  Timing (in seconds)
% 3.27/1.48  ----------------------
% 3.27/1.48  Preprocessing        : 0.28
% 3.27/1.48  Parsing              : 0.14
% 3.27/1.48  CNF conversion       : 0.02
% 3.27/1.48  Main loop            : 0.44
% 3.27/1.48  Inferencing          : 0.17
% 3.27/1.48  Reduction            : 0.11
% 3.27/1.48  Demodulation         : 0.08
% 3.27/1.48  BG Simplification    : 0.02
% 3.27/1.48  Subsumption          : 0.10
% 3.27/1.48  Abstraction          : 0.02
% 3.27/1.48  MUC search           : 0.00
% 3.27/1.48  Cooper               : 0.00
% 3.27/1.48  Total                : 0.75
% 3.27/1.48  Index Insertion      : 0.00
% 3.27/1.48  Index Deletion       : 0.00
% 3.27/1.48  Index Matching       : 0.00
% 3.27/1.48  BG Taut test         : 0.00
%------------------------------------------------------------------------------
