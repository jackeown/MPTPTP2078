%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:43:27 EST 2020

% Result     : Theorem 1.71s
% Output     : CNFRefutation 1.71s
% Verified   : 
% Statistics : Number of formulae       :   50 (  70 expanded)
%              Number of leaves         :   25 (  34 expanded)
%              Depth                    :   10
%              Number of atoms          :   53 (  92 expanded)
%              Number of equality atoms :   17 (  33 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(f_78,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( r1_tarski(A,B)
          & r1_tarski(A,C)
          & r1_xboole_0(B,C) )
       => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_xboole_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_69,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_xboole_0(B,C) )
     => r1_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_xboole_1)).

tff(f_59,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_57,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_61,axiom,(
    ! [A,B] : k4_xboole_0(A,k2_xboole_0(A,B)) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).

tff(f_63,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_35,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(c_24,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_30,plain,(
    r1_tarski('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_26,plain,(
    r1_xboole_0('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_192,plain,(
    ! [A_42,C_43,B_44] :
      ( r1_xboole_0(A_42,C_43)
      | ~ r1_xboole_0(B_44,C_43)
      | ~ r1_tarski(A_42,B_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_198,plain,(
    ! [A_42] :
      ( r1_xboole_0(A_42,'#skF_5')
      | ~ r1_tarski(A_42,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_26,c_192])).

tff(c_16,plain,(
    ! [A_15] : k4_xboole_0(A_15,k1_xboole_0) = A_15 ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_28,plain,(
    r1_tarski('#skF_3','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_62,plain,(
    ! [A_32,B_33] :
      ( k2_xboole_0(A_32,B_33) = B_33
      | ~ r1_tarski(A_32,B_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_69,plain,(
    k2_xboole_0('#skF_3','#skF_5') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_28,c_62])).

tff(c_18,plain,(
    ! [A_16,B_17] : k4_xboole_0(A_16,k2_xboole_0(A_16,B_17)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_74,plain,(
    k4_xboole_0('#skF_3','#skF_5') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_69,c_18])).

tff(c_89,plain,(
    ! [A_34,B_35] : k4_xboole_0(A_34,k4_xboole_0(A_34,B_35)) = k3_xboole_0(A_34,B_35) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_104,plain,(
    k4_xboole_0('#skF_3',k1_xboole_0) = k3_xboole_0('#skF_3','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_74,c_89])).

tff(c_113,plain,(
    k3_xboole_0('#skF_3','#skF_5') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_104])).

tff(c_131,plain,(
    ! [A_36,B_37,C_38] :
      ( ~ r1_xboole_0(A_36,B_37)
      | ~ r2_hidden(C_38,k3_xboole_0(A_36,B_37)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_137,plain,(
    ! [C_38] :
      ( ~ r1_xboole_0('#skF_3','#skF_5')
      | ~ r2_hidden(C_38,'#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_113,c_131])).

tff(c_227,plain,(
    ~ r1_xboole_0('#skF_3','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_137])).

tff(c_230,plain,(
    ~ r1_tarski('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_198,c_227])).

tff(c_234,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_230])).

tff(c_237,plain,(
    ! [C_49] : ~ r2_hidden(C_49,'#skF_3') ),
    inference(splitRight,[status(thm)],[c_137])).

tff(c_242,plain,(
    v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_4,c_237])).

tff(c_6,plain,(
    ! [A_5] :
      ( k1_xboole_0 = A_5
      | ~ v1_xboole_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_245,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_242,c_6])).

tff(c_249,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_245])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n013.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 14:36:09 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.71/1.24  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.71/1.24  
% 1.71/1.24  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.71/1.25  %$ r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2
% 1.71/1.25  
% 1.71/1.25  %Foreground sorts:
% 1.71/1.25  
% 1.71/1.25  
% 1.71/1.25  %Background operators:
% 1.71/1.25  
% 1.71/1.25  
% 1.71/1.25  %Foreground operators:
% 1.71/1.25  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.71/1.25  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.71/1.25  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.71/1.25  tff('#skF_1', type, '#skF_1': $i > $i).
% 1.71/1.25  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.71/1.25  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.71/1.25  tff('#skF_5', type, '#skF_5': $i).
% 1.71/1.25  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.71/1.25  tff('#skF_3', type, '#skF_3': $i).
% 1.71/1.25  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.71/1.25  tff('#skF_4', type, '#skF_4': $i).
% 1.71/1.25  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.71/1.25  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 1.71/1.25  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.71/1.25  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.71/1.25  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.71/1.25  
% 1.71/1.26  tff(f_78, negated_conjecture, ~(![A, B, C]: (((r1_tarski(A, B) & r1_tarski(A, C)) & r1_xboole_0(B, C)) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t67_xboole_1)).
% 1.71/1.26  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 1.71/1.26  tff(f_69, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_xboole_0(B, C)) => r1_xboole_0(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t63_xboole_1)).
% 1.71/1.26  tff(f_59, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 1.71/1.26  tff(f_57, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 1.71/1.26  tff(f_61, axiom, (![A, B]: (k4_xboole_0(A, k2_xboole_0(A, B)) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_xboole_1)).
% 1.71/1.26  tff(f_63, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 1.71/1.26  tff(f_53, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 1.71/1.26  tff(f_35, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 1.71/1.26  tff(c_24, plain, (k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_78])).
% 1.71/1.26  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.71/1.26  tff(c_30, plain, (r1_tarski('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_78])).
% 1.71/1.26  tff(c_26, plain, (r1_xboole_0('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_78])).
% 1.71/1.26  tff(c_192, plain, (![A_42, C_43, B_44]: (r1_xboole_0(A_42, C_43) | ~r1_xboole_0(B_44, C_43) | ~r1_tarski(A_42, B_44))), inference(cnfTransformation, [status(thm)], [f_69])).
% 1.71/1.26  tff(c_198, plain, (![A_42]: (r1_xboole_0(A_42, '#skF_5') | ~r1_tarski(A_42, '#skF_4'))), inference(resolution, [status(thm)], [c_26, c_192])).
% 1.71/1.26  tff(c_16, plain, (![A_15]: (k4_xboole_0(A_15, k1_xboole_0)=A_15)), inference(cnfTransformation, [status(thm)], [f_59])).
% 1.71/1.26  tff(c_28, plain, (r1_tarski('#skF_3', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_78])).
% 1.71/1.26  tff(c_62, plain, (![A_32, B_33]: (k2_xboole_0(A_32, B_33)=B_33 | ~r1_tarski(A_32, B_33))), inference(cnfTransformation, [status(thm)], [f_57])).
% 1.71/1.26  tff(c_69, plain, (k2_xboole_0('#skF_3', '#skF_5')='#skF_5'), inference(resolution, [status(thm)], [c_28, c_62])).
% 1.71/1.26  tff(c_18, plain, (![A_16, B_17]: (k4_xboole_0(A_16, k2_xboole_0(A_16, B_17))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_61])).
% 1.71/1.26  tff(c_74, plain, (k4_xboole_0('#skF_3', '#skF_5')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_69, c_18])).
% 1.71/1.26  tff(c_89, plain, (![A_34, B_35]: (k4_xboole_0(A_34, k4_xboole_0(A_34, B_35))=k3_xboole_0(A_34, B_35))), inference(cnfTransformation, [status(thm)], [f_63])).
% 1.71/1.26  tff(c_104, plain, (k4_xboole_0('#skF_3', k1_xboole_0)=k3_xboole_0('#skF_3', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_74, c_89])).
% 1.71/1.26  tff(c_113, plain, (k3_xboole_0('#skF_3', '#skF_5')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_16, c_104])).
% 1.71/1.26  tff(c_131, plain, (![A_36, B_37, C_38]: (~r1_xboole_0(A_36, B_37) | ~r2_hidden(C_38, k3_xboole_0(A_36, B_37)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 1.71/1.26  tff(c_137, plain, (![C_38]: (~r1_xboole_0('#skF_3', '#skF_5') | ~r2_hidden(C_38, '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_113, c_131])).
% 1.71/1.26  tff(c_227, plain, (~r1_xboole_0('#skF_3', '#skF_5')), inference(splitLeft, [status(thm)], [c_137])).
% 1.71/1.26  tff(c_230, plain, (~r1_tarski('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_198, c_227])).
% 1.71/1.26  tff(c_234, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_30, c_230])).
% 1.71/1.26  tff(c_237, plain, (![C_49]: (~r2_hidden(C_49, '#skF_3'))), inference(splitRight, [status(thm)], [c_137])).
% 1.71/1.26  tff(c_242, plain, (v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_4, c_237])).
% 1.71/1.26  tff(c_6, plain, (![A_5]: (k1_xboole_0=A_5 | ~v1_xboole_0(A_5))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.71/1.26  tff(c_245, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_242, c_6])).
% 1.71/1.26  tff(c_249, plain, $false, inference(negUnitSimplification, [status(thm)], [c_24, c_245])).
% 1.71/1.26  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.71/1.26  
% 1.71/1.26  Inference rules
% 1.71/1.26  ----------------------
% 1.71/1.26  #Ref     : 0
% 1.71/1.26  #Sup     : 60
% 1.71/1.26  #Fact    : 0
% 1.71/1.26  #Define  : 0
% 1.71/1.26  #Split   : 2
% 1.71/1.26  #Chain   : 0
% 1.71/1.26  #Close   : 0
% 1.71/1.26  
% 1.71/1.26  Ordering : KBO
% 1.71/1.26  
% 1.71/1.26  Simplification rules
% 1.71/1.26  ----------------------
% 1.71/1.26  #Subsume      : 2
% 1.71/1.26  #Demod        : 8
% 1.71/1.26  #Tautology    : 29
% 1.71/1.26  #SimpNegUnit  : 1
% 1.71/1.26  #BackRed      : 0
% 1.71/1.26  
% 1.71/1.26  #Partial instantiations: 0
% 1.71/1.26  #Strategies tried      : 1
% 1.71/1.26  
% 1.71/1.26  Timing (in seconds)
% 1.71/1.26  ----------------------
% 1.71/1.26  Preprocessing        : 0.28
% 1.71/1.26  Parsing              : 0.15
% 1.71/1.26  CNF conversion       : 0.02
% 1.71/1.26  Main loop            : 0.17
% 1.71/1.26  Inferencing          : 0.07
% 1.71/1.26  Reduction            : 0.05
% 1.71/1.26  Demodulation         : 0.03
% 1.71/1.26  BG Simplification    : 0.01
% 1.71/1.26  Subsumption          : 0.03
% 1.71/1.26  Abstraction          : 0.01
% 1.71/1.26  MUC search           : 0.00
% 1.71/1.26  Cooper               : 0.00
% 1.71/1.26  Total                : 0.48
% 1.71/1.26  Index Insertion      : 0.00
% 1.71/1.26  Index Deletion       : 0.00
% 1.71/1.26  Index Matching       : 0.00
% 1.71/1.26  BG Taut test         : 0.00
%------------------------------------------------------------------------------
