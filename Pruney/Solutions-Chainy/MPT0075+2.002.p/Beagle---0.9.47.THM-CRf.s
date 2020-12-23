%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:43:30 EST 2020

% Result     : Theorem 2.05s
% Output     : CNFRefutation 2.05s
% Verified   : 
% Statistics : Number of formulae       :   41 (  46 expanded)
%              Number of leaves         :   20 (  25 expanded)
%              Depth                    :    9
%              Number of atoms          :   53 (  77 expanded)
%              Number of equality atoms :    8 (   8 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > k3_xboole_0 > #nlpp > k1_xboole_0 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(f_70,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ~ v1_xboole_0(C)
       => ~ ( r1_tarski(C,A)
            & r1_tarski(C,B)
            & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t68_xboole_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & r2_hidden(C,B) ) )
      & ~ ( ? [C] :
              ( r2_hidden(C,A)
              & r2_hidden(C,B) )
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_36,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_37,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(c_28,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_26,plain,(
    r1_tarski('#skF_5','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_29,plain,(
    ! [A_15,B_16] :
      ( k3_xboole_0(A_15,B_16) = A_15
      | ~ r1_tarski(A_15,B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_37,plain,(
    k3_xboole_0('#skF_5','#skF_3') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_26,c_29])).

tff(c_24,plain,(
    r1_tarski('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_18,plain,(
    ! [A_8,B_9] :
      ( r2_hidden('#skF_2'(A_8,B_9),A_8)
      | r1_xboole_0(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_131,plain,(
    ! [C_38,B_39,A_40] :
      ( r2_hidden(C_38,B_39)
      | ~ r2_hidden(C_38,A_40)
      | ~ r1_tarski(A_40,B_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_151,plain,(
    ! [A_44,B_45,B_46] :
      ( r2_hidden('#skF_2'(A_44,B_45),B_46)
      | ~ r1_tarski(A_44,B_46)
      | r1_xboole_0(A_44,B_45) ) ),
    inference(resolution,[status(thm)],[c_18,c_131])).

tff(c_16,plain,(
    ! [A_8,B_9] :
      ( r2_hidden('#skF_2'(A_8,B_9),B_9)
      | r1_xboole_0(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_22,plain,(
    r1_xboole_0('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_83,plain,(
    ! [A_31,B_32,C_33] :
      ( ~ r1_xboole_0(A_31,B_32)
      | ~ r2_hidden(C_33,B_32)
      | ~ r2_hidden(C_33,A_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_90,plain,(
    ! [C_34] :
      ( ~ r2_hidden(C_34,'#skF_4')
      | ~ r2_hidden(C_34,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_22,c_83])).

tff(c_105,plain,(
    ! [A_8] :
      ( ~ r2_hidden('#skF_2'(A_8,'#skF_3'),'#skF_4')
      | r1_xboole_0(A_8,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_16,c_90])).

tff(c_173,plain,(
    ! [A_47] :
      ( ~ r1_tarski(A_47,'#skF_4')
      | r1_xboole_0(A_47,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_151,c_105])).

tff(c_8,plain,(
    ! [A_6,B_7] :
      ( k3_xboole_0(A_6,B_7) = k1_xboole_0
      | ~ r1_xboole_0(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_207,plain,(
    ! [A_51] :
      ( k3_xboole_0(A_51,'#skF_3') = k1_xboole_0
      | ~ r1_tarski(A_51,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_173,c_8])).

tff(c_214,plain,(
    k3_xboole_0('#skF_5','#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_24,c_207])).

tff(c_218,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_37,c_214])).

tff(c_12,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_247,plain,(
    v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_218,c_12])).

tff(c_249,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_247])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n022.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 18:34:25 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.05/1.29  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.05/1.30  
% 2.05/1.30  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.05/1.30  %$ r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > k3_xboole_0 > #nlpp > k1_xboole_0 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 2.05/1.30  
% 2.05/1.30  %Foreground sorts:
% 2.05/1.30  
% 2.05/1.30  
% 2.05/1.30  %Background operators:
% 2.05/1.30  
% 2.05/1.30  
% 2.05/1.30  %Foreground operators:
% 2.05/1.30  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.05/1.30  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.05/1.30  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.05/1.30  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.05/1.30  tff('#skF_5', type, '#skF_5': $i).
% 2.05/1.30  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.05/1.30  tff('#skF_3', type, '#skF_3': $i).
% 2.05/1.30  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.05/1.30  tff('#skF_4', type, '#skF_4': $i).
% 2.05/1.30  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.05/1.30  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.05/1.30  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.05/1.30  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.05/1.30  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.05/1.30  
% 2.05/1.31  tff(f_70, negated_conjecture, ~(![A, B, C]: (~v1_xboole_0(C) => ~((r1_tarski(C, A) & r1_tarski(C, B)) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t68_xboole_1)).
% 2.05/1.31  tff(f_59, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 2.05/1.31  tff(f_55, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 2.05/1.31  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 2.05/1.31  tff(f_36, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 2.05/1.31  tff(f_37, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.05/1.31  tff(c_28, plain, (~v1_xboole_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.05/1.31  tff(c_26, plain, (r1_tarski('#skF_5', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.05/1.31  tff(c_29, plain, (![A_15, B_16]: (k3_xboole_0(A_15, B_16)=A_15 | ~r1_tarski(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.05/1.31  tff(c_37, plain, (k3_xboole_0('#skF_5', '#skF_3')='#skF_5'), inference(resolution, [status(thm)], [c_26, c_29])).
% 2.05/1.31  tff(c_24, plain, (r1_tarski('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.05/1.31  tff(c_18, plain, (![A_8, B_9]: (r2_hidden('#skF_2'(A_8, B_9), A_8) | r1_xboole_0(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.05/1.31  tff(c_131, plain, (![C_38, B_39, A_40]: (r2_hidden(C_38, B_39) | ~r2_hidden(C_38, A_40) | ~r1_tarski(A_40, B_39))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.05/1.31  tff(c_151, plain, (![A_44, B_45, B_46]: (r2_hidden('#skF_2'(A_44, B_45), B_46) | ~r1_tarski(A_44, B_46) | r1_xboole_0(A_44, B_45))), inference(resolution, [status(thm)], [c_18, c_131])).
% 2.05/1.31  tff(c_16, plain, (![A_8, B_9]: (r2_hidden('#skF_2'(A_8, B_9), B_9) | r1_xboole_0(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.05/1.31  tff(c_22, plain, (r1_xboole_0('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.05/1.31  tff(c_83, plain, (![A_31, B_32, C_33]: (~r1_xboole_0(A_31, B_32) | ~r2_hidden(C_33, B_32) | ~r2_hidden(C_33, A_31))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.05/1.31  tff(c_90, plain, (![C_34]: (~r2_hidden(C_34, '#skF_4') | ~r2_hidden(C_34, '#skF_3'))), inference(resolution, [status(thm)], [c_22, c_83])).
% 2.05/1.31  tff(c_105, plain, (![A_8]: (~r2_hidden('#skF_2'(A_8, '#skF_3'), '#skF_4') | r1_xboole_0(A_8, '#skF_3'))), inference(resolution, [status(thm)], [c_16, c_90])).
% 2.05/1.31  tff(c_173, plain, (![A_47]: (~r1_tarski(A_47, '#skF_4') | r1_xboole_0(A_47, '#skF_3'))), inference(resolution, [status(thm)], [c_151, c_105])).
% 2.05/1.31  tff(c_8, plain, (![A_6, B_7]: (k3_xboole_0(A_6, B_7)=k1_xboole_0 | ~r1_xboole_0(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.05/1.31  tff(c_207, plain, (![A_51]: (k3_xboole_0(A_51, '#skF_3')=k1_xboole_0 | ~r1_tarski(A_51, '#skF_4'))), inference(resolution, [status(thm)], [c_173, c_8])).
% 2.05/1.31  tff(c_214, plain, (k3_xboole_0('#skF_5', '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_24, c_207])).
% 2.05/1.31  tff(c_218, plain, (k1_xboole_0='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_37, c_214])).
% 2.05/1.31  tff(c_12, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.05/1.31  tff(c_247, plain, (v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_218, c_12])).
% 2.05/1.31  tff(c_249, plain, $false, inference(negUnitSimplification, [status(thm)], [c_28, c_247])).
% 2.05/1.31  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.05/1.31  
% 2.05/1.31  Inference rules
% 2.05/1.31  ----------------------
% 2.05/1.31  #Ref     : 0
% 2.05/1.31  #Sup     : 50
% 2.05/1.31  #Fact    : 0
% 2.05/1.31  #Define  : 0
% 2.05/1.31  #Split   : 2
% 2.05/1.31  #Chain   : 0
% 2.05/1.31  #Close   : 0
% 2.05/1.31  
% 2.05/1.31  Ordering : KBO
% 2.05/1.31  
% 2.05/1.31  Simplification rules
% 2.05/1.31  ----------------------
% 2.05/1.31  #Subsume      : 2
% 2.05/1.31  #Demod        : 10
% 2.05/1.31  #Tautology    : 14
% 2.05/1.31  #SimpNegUnit  : 1
% 2.05/1.31  #BackRed      : 7
% 2.05/1.31  
% 2.05/1.31  #Partial instantiations: 0
% 2.05/1.31  #Strategies tried      : 1
% 2.05/1.31  
% 2.05/1.31  Timing (in seconds)
% 2.05/1.31  ----------------------
% 2.05/1.31  Preprocessing        : 0.29
% 2.05/1.31  Parsing              : 0.16
% 2.05/1.31  CNF conversion       : 0.02
% 2.05/1.31  Main loop            : 0.21
% 2.05/1.31  Inferencing          : 0.08
% 2.05/1.31  Reduction            : 0.05
% 2.05/1.31  Demodulation         : 0.04
% 2.05/1.31  BG Simplification    : 0.01
% 2.05/1.31  Subsumption          : 0.05
% 2.05/1.31  Abstraction          : 0.01
% 2.05/1.31  MUC search           : 0.00
% 2.05/1.31  Cooper               : 0.00
% 2.05/1.31  Total                : 0.52
% 2.05/1.31  Index Insertion      : 0.00
% 2.05/1.31  Index Deletion       : 0.00
% 2.05/1.31  Index Matching       : 0.00
% 2.05/1.31  BG Taut test         : 0.00
%------------------------------------------------------------------------------
