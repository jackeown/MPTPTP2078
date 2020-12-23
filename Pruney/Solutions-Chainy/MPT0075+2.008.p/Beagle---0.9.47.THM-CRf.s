%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:43:30 EST 2020

% Result     : Theorem 1.92s
% Output     : CNFRefutation 1.92s
% Verified   : 
% Statistics : Number of formulae       :   43 (  60 expanded)
%              Number of leaves         :   22 (  30 expanded)
%              Depth                    :    8
%              Number of atoms          :   45 (  81 expanded)
%              Number of equality atoms :    9 (  18 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > k4_xboole_0 > k3_xboole_0 > #nlpp > k1_xboole_0 > #skF_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(f_74,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ~ v1_xboole_0(C)
       => ~ ( r1_tarski(C,A)
            & r1_tarski(C,B)
            & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t68_xboole_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_63,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_xboole_0(B,C) )
     => r1_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_xboole_1)).

tff(f_55,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_53,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_57,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

tff(c_28,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_26,plain,(
    r1_tarski('#skF_5','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_22,plain,(
    r1_xboole_0('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_151,plain,(
    ! [A_36,C_37,B_38] :
      ( r1_xboole_0(A_36,C_37)
      | ~ r1_xboole_0(B_38,C_37)
      | ~ r1_tarski(A_36,B_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_158,plain,(
    ! [A_39] :
      ( r1_xboole_0(A_39,'#skF_4')
      | ~ r1_tarski(A_39,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_22,c_151])).

tff(c_16,plain,(
    ! [A_14] : k4_xboole_0(A_14,k1_xboole_0) = A_14 ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_24,plain,(
    r1_tarski('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_53,plain,(
    ! [A_28,B_29] :
      ( k4_xboole_0(A_28,B_29) = k1_xboole_0
      | ~ r1_tarski(A_28,B_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_64,plain,(
    k4_xboole_0('#skF_5','#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_24,c_53])).

tff(c_74,plain,(
    ! [A_30,B_31] : k4_xboole_0(A_30,k4_xboole_0(A_30,B_31)) = k3_xboole_0(A_30,B_31) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_92,plain,(
    k4_xboole_0('#skF_5',k1_xboole_0) = k3_xboole_0('#skF_5','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_64,c_74])).

tff(c_99,plain,(
    k3_xboole_0('#skF_5','#skF_4') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_92])).

tff(c_10,plain,(
    ! [A_7,B_8,C_11] :
      ( ~ r1_xboole_0(A_7,B_8)
      | ~ r2_hidden(C_11,k3_xboole_0(A_7,B_8)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_116,plain,(
    ! [C_11] :
      ( ~ r1_xboole_0('#skF_5','#skF_4')
      | ~ r2_hidden(C_11,'#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_99,c_10])).

tff(c_147,plain,(
    ~ r1_xboole_0('#skF_5','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_116])).

tff(c_163,plain,(
    ~ r1_tarski('#skF_5','#skF_3') ),
    inference(resolution,[status(thm)],[c_158,c_147])).

tff(c_170,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_163])).

tff(c_173,plain,(
    ! [C_40] : ~ r2_hidden(C_40,'#skF_5') ),
    inference(splitRight,[status(thm)],[c_116])).

tff(c_177,plain,(
    v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_4,c_173])).

tff(c_181,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_177])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:59:12 EST 2020
% 0.20/0.34  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.92/1.35  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.92/1.36  
% 1.92/1.36  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.92/1.36  %$ r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > k4_xboole_0 > k3_xboole_0 > #nlpp > k1_xboole_0 > #skF_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2
% 1.92/1.36  
% 1.92/1.36  %Foreground sorts:
% 1.92/1.36  
% 1.92/1.36  
% 1.92/1.36  %Background operators:
% 1.92/1.36  
% 1.92/1.36  
% 1.92/1.36  %Foreground operators:
% 1.92/1.36  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.92/1.36  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.92/1.36  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.92/1.36  tff('#skF_1', type, '#skF_1': $i > $i).
% 1.92/1.36  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.92/1.36  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.92/1.36  tff('#skF_5', type, '#skF_5': $i).
% 1.92/1.36  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.92/1.36  tff('#skF_3', type, '#skF_3': $i).
% 1.92/1.36  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.92/1.36  tff('#skF_4', type, '#skF_4': $i).
% 1.92/1.36  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.92/1.36  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 1.92/1.36  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.92/1.36  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.92/1.36  
% 1.92/1.37  tff(f_74, negated_conjecture, ~(![A, B, C]: (~v1_xboole_0(C) => ~((r1_tarski(C, A) & r1_tarski(C, B)) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t68_xboole_1)).
% 1.92/1.37  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 1.92/1.37  tff(f_63, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_xboole_0(B, C)) => r1_xboole_0(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_xboole_1)).
% 1.92/1.37  tff(f_55, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 1.92/1.37  tff(f_53, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 1.92/1.37  tff(f_57, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 1.92/1.37  tff(f_49, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 1.92/1.37  tff(c_28, plain, (~v1_xboole_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_74])).
% 1.92/1.37  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.92/1.37  tff(c_26, plain, (r1_tarski('#skF_5', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_74])).
% 1.92/1.37  tff(c_22, plain, (r1_xboole_0('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_74])).
% 1.92/1.37  tff(c_151, plain, (![A_36, C_37, B_38]: (r1_xboole_0(A_36, C_37) | ~r1_xboole_0(B_38, C_37) | ~r1_tarski(A_36, B_38))), inference(cnfTransformation, [status(thm)], [f_63])).
% 1.92/1.37  tff(c_158, plain, (![A_39]: (r1_xboole_0(A_39, '#skF_4') | ~r1_tarski(A_39, '#skF_3'))), inference(resolution, [status(thm)], [c_22, c_151])).
% 1.92/1.37  tff(c_16, plain, (![A_14]: (k4_xboole_0(A_14, k1_xboole_0)=A_14)), inference(cnfTransformation, [status(thm)], [f_55])).
% 1.92/1.37  tff(c_24, plain, (r1_tarski('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_74])).
% 1.92/1.37  tff(c_53, plain, (![A_28, B_29]: (k4_xboole_0(A_28, B_29)=k1_xboole_0 | ~r1_tarski(A_28, B_29))), inference(cnfTransformation, [status(thm)], [f_53])).
% 1.92/1.37  tff(c_64, plain, (k4_xboole_0('#skF_5', '#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_24, c_53])).
% 1.92/1.37  tff(c_74, plain, (![A_30, B_31]: (k4_xboole_0(A_30, k4_xboole_0(A_30, B_31))=k3_xboole_0(A_30, B_31))), inference(cnfTransformation, [status(thm)], [f_57])).
% 1.92/1.37  tff(c_92, plain, (k4_xboole_0('#skF_5', k1_xboole_0)=k3_xboole_0('#skF_5', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_64, c_74])).
% 1.92/1.37  tff(c_99, plain, (k3_xboole_0('#skF_5', '#skF_4')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_16, c_92])).
% 1.92/1.37  tff(c_10, plain, (![A_7, B_8, C_11]: (~r1_xboole_0(A_7, B_8) | ~r2_hidden(C_11, k3_xboole_0(A_7, B_8)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 1.92/1.37  tff(c_116, plain, (![C_11]: (~r1_xboole_0('#skF_5', '#skF_4') | ~r2_hidden(C_11, '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_99, c_10])).
% 1.92/1.37  tff(c_147, plain, (~r1_xboole_0('#skF_5', '#skF_4')), inference(splitLeft, [status(thm)], [c_116])).
% 1.92/1.37  tff(c_163, plain, (~r1_tarski('#skF_5', '#skF_3')), inference(resolution, [status(thm)], [c_158, c_147])).
% 1.92/1.37  tff(c_170, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_26, c_163])).
% 1.92/1.37  tff(c_173, plain, (![C_40]: (~r2_hidden(C_40, '#skF_5'))), inference(splitRight, [status(thm)], [c_116])).
% 1.92/1.37  tff(c_177, plain, (v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_4, c_173])).
% 1.92/1.37  tff(c_181, plain, $false, inference(negUnitSimplification, [status(thm)], [c_28, c_177])).
% 1.92/1.37  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.92/1.37  
% 1.92/1.37  Inference rules
% 1.92/1.37  ----------------------
% 1.92/1.37  #Ref     : 0
% 1.92/1.37  #Sup     : 40
% 1.92/1.37  #Fact    : 0
% 1.92/1.37  #Define  : 0
% 1.92/1.37  #Split   : 3
% 1.92/1.37  #Chain   : 0
% 1.92/1.37  #Close   : 0
% 1.92/1.37  
% 1.92/1.37  Ordering : KBO
% 1.92/1.37  
% 1.92/1.37  Simplification rules
% 1.92/1.37  ----------------------
% 1.92/1.37  #Subsume      : 0
% 1.92/1.37  #Demod        : 5
% 1.92/1.37  #Tautology    : 20
% 1.92/1.37  #SimpNegUnit  : 1
% 1.92/1.37  #BackRed      : 0
% 1.92/1.37  
% 1.92/1.37  #Partial instantiations: 0
% 1.92/1.37  #Strategies tried      : 1
% 1.92/1.37  
% 1.92/1.37  Timing (in seconds)
% 1.92/1.37  ----------------------
% 2.12/1.37  Preprocessing        : 0.31
% 2.12/1.37  Parsing              : 0.17
% 2.12/1.37  CNF conversion       : 0.02
% 2.12/1.37  Main loop            : 0.15
% 2.12/1.37  Inferencing          : 0.07
% 2.12/1.37  Reduction            : 0.04
% 2.12/1.38  Demodulation         : 0.03
% 2.12/1.38  BG Simplification    : 0.01
% 2.12/1.38  Subsumption          : 0.02
% 2.12/1.38  Abstraction          : 0.01
% 2.12/1.38  MUC search           : 0.00
% 2.12/1.38  Cooper               : 0.00
% 2.12/1.38  Total                : 0.50
% 2.12/1.38  Index Insertion      : 0.00
% 2.12/1.38  Index Deletion       : 0.00
% 2.12/1.38  Index Matching       : 0.00
% 2.12/1.38  BG Taut test         : 0.00
%------------------------------------------------------------------------------
