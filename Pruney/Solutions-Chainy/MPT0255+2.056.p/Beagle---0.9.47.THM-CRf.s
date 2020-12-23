%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:51:46 EST 2020

% Result     : Theorem 2.00s
% Output     : CNFRefutation 2.00s
% Verified   : 
% Statistics : Number of formulae       :   44 (  45 expanded)
%              Number of leaves         :   29 (  30 expanded)
%              Depth                    :    7
%              Number of atoms          :   35 (  37 expanded)
%              Number of equality atoms :    8 (   8 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_xboole_0 > #skF_1 > #skF_4 > #skF_7 > #skF_5 > #skF_6 > #skF_3 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

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

tff(f_64,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).

tff(f_33,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_53,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_76,negated_conjecture,(
    ~ ! [A,B,C] : k2_xboole_0(k2_tarski(A,B),C) != k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_zfmisc_1)).

tff(f_55,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(c_22,plain,(
    ! [D_22,B_18] : r2_hidden(D_22,k2_tarski(D_22,B_18)) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_47,plain,(
    ! [B_37,A_38] :
      ( ~ r2_hidden(B_37,A_38)
      | ~ v1_xboole_0(A_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_51,plain,(
    ! [D_22,B_18] : ~ v1_xboole_0(k2_tarski(D_22,B_18)) ),
    inference(resolution,[status(thm)],[c_22,c_47])).

tff(c_6,plain,(
    ! [A_3] :
      ( v1_xboole_0(A_3)
      | r2_hidden('#skF_1'(A_3),A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_14,plain,(
    ! [A_14] : r1_xboole_0(A_14,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_44,plain,(
    k2_xboole_0(k2_tarski('#skF_5','#skF_6'),'#skF_7') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_16,plain,(
    ! [A_15,B_16] : r1_tarski(A_15,k2_xboole_0(A_15,B_16)) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_62,plain,(
    r1_tarski(k2_tarski('#skF_5','#skF_6'),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_16])).

tff(c_159,plain,(
    ! [A_52,B_53] :
      ( k3_xboole_0(A_52,B_53) = A_52
      | ~ r1_tarski(A_52,B_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_174,plain,(
    k3_xboole_0(k2_tarski('#skF_5','#skF_6'),k1_xboole_0) = k2_tarski('#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_62,c_159])).

tff(c_253,plain,(
    ! [A_60,B_61,C_62] :
      ( ~ r1_xboole_0(A_60,B_61)
      | ~ r2_hidden(C_62,k3_xboole_0(A_60,B_61)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_265,plain,(
    ! [C_62] :
      ( ~ r1_xboole_0(k2_tarski('#skF_5','#skF_6'),k1_xboole_0)
      | ~ r2_hidden(C_62,k2_tarski('#skF_5','#skF_6')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_174,c_253])).

tff(c_281,plain,(
    ! [C_64] : ~ r2_hidden(C_64,k2_tarski('#skF_5','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_265])).

tff(c_285,plain,(
    v1_xboole_0(k2_tarski('#skF_5','#skF_6')) ),
    inference(resolution,[status(thm)],[c_6,c_281])).

tff(c_295,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_51,c_285])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:38:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.00/1.23  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.00/1.24  
% 2.00/1.24  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.00/1.24  %$ r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_xboole_0 > #skF_1 > #skF_4 > #skF_7 > #skF_5 > #skF_6 > #skF_3 > #skF_2
% 2.00/1.24  
% 2.00/1.24  %Foreground sorts:
% 2.00/1.24  
% 2.00/1.24  
% 2.00/1.24  %Background operators:
% 2.00/1.24  
% 2.00/1.24  
% 2.00/1.24  %Foreground operators:
% 2.00/1.24  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.00/1.24  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.00/1.24  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.00/1.24  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.00/1.24  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.00/1.24  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 2.00/1.24  tff('#skF_7', type, '#skF_7': $i).
% 2.00/1.24  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.00/1.24  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.00/1.24  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.00/1.24  tff('#skF_5', type, '#skF_5': $i).
% 2.00/1.24  tff('#skF_6', type, '#skF_6': $i).
% 2.00/1.24  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.00/1.24  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.00/1.24  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.00/1.24  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.00/1.24  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 2.00/1.24  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.00/1.24  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.00/1.24  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.00/1.24  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.00/1.24  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.00/1.24  
% 2.00/1.25  tff(f_64, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_tarski)).
% 2.00/1.25  tff(f_33, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 2.00/1.25  tff(f_53, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 2.00/1.25  tff(f_76, negated_conjecture, ~(![A, B, C]: ~(k2_xboole_0(k2_tarski(A, B), C) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t50_zfmisc_1)).
% 2.00/1.25  tff(f_55, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 2.00/1.25  tff(f_51, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 2.00/1.25  tff(f_47, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 2.00/1.25  tff(c_22, plain, (![D_22, B_18]: (r2_hidden(D_22, k2_tarski(D_22, B_18)))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.00/1.25  tff(c_47, plain, (![B_37, A_38]: (~r2_hidden(B_37, A_38) | ~v1_xboole_0(A_38))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.00/1.25  tff(c_51, plain, (![D_22, B_18]: (~v1_xboole_0(k2_tarski(D_22, B_18)))), inference(resolution, [status(thm)], [c_22, c_47])).
% 2.00/1.25  tff(c_6, plain, (![A_3]: (v1_xboole_0(A_3) | r2_hidden('#skF_1'(A_3), A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.00/1.25  tff(c_14, plain, (![A_14]: (r1_xboole_0(A_14, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.00/1.25  tff(c_44, plain, (k2_xboole_0(k2_tarski('#skF_5', '#skF_6'), '#skF_7')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.00/1.25  tff(c_16, plain, (![A_15, B_16]: (r1_tarski(A_15, k2_xboole_0(A_15, B_16)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.00/1.25  tff(c_62, plain, (r1_tarski(k2_tarski('#skF_5', '#skF_6'), k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_44, c_16])).
% 2.00/1.25  tff(c_159, plain, (![A_52, B_53]: (k3_xboole_0(A_52, B_53)=A_52 | ~r1_tarski(A_52, B_53))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.00/1.25  tff(c_174, plain, (k3_xboole_0(k2_tarski('#skF_5', '#skF_6'), k1_xboole_0)=k2_tarski('#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_62, c_159])).
% 2.00/1.25  tff(c_253, plain, (![A_60, B_61, C_62]: (~r1_xboole_0(A_60, B_61) | ~r2_hidden(C_62, k3_xboole_0(A_60, B_61)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.00/1.25  tff(c_265, plain, (![C_62]: (~r1_xboole_0(k2_tarski('#skF_5', '#skF_6'), k1_xboole_0) | ~r2_hidden(C_62, k2_tarski('#skF_5', '#skF_6')))), inference(superposition, [status(thm), theory('equality')], [c_174, c_253])).
% 2.00/1.25  tff(c_281, plain, (![C_64]: (~r2_hidden(C_64, k2_tarski('#skF_5', '#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_265])).
% 2.00/1.25  tff(c_285, plain, (v1_xboole_0(k2_tarski('#skF_5', '#skF_6'))), inference(resolution, [status(thm)], [c_6, c_281])).
% 2.00/1.25  tff(c_295, plain, $false, inference(negUnitSimplification, [status(thm)], [c_51, c_285])).
% 2.00/1.25  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.00/1.25  
% 2.00/1.25  Inference rules
% 2.00/1.25  ----------------------
% 2.00/1.25  #Ref     : 0
% 2.00/1.25  #Sup     : 62
% 2.00/1.25  #Fact    : 0
% 2.00/1.25  #Define  : 0
% 2.00/1.25  #Split   : 0
% 2.00/1.25  #Chain   : 0
% 2.00/1.25  #Close   : 0
% 2.00/1.25  
% 2.00/1.25  Ordering : KBO
% 2.00/1.25  
% 2.00/1.25  Simplification rules
% 2.00/1.25  ----------------------
% 2.00/1.25  #Subsume      : 1
% 2.00/1.25  #Demod        : 18
% 2.00/1.25  #Tautology    : 43
% 2.00/1.25  #SimpNegUnit  : 1
% 2.00/1.25  #BackRed      : 0
% 2.00/1.25  
% 2.00/1.25  #Partial instantiations: 0
% 2.00/1.25  #Strategies tried      : 1
% 2.00/1.25  
% 2.00/1.25  Timing (in seconds)
% 2.00/1.25  ----------------------
% 2.00/1.25  Preprocessing        : 0.29
% 2.00/1.25  Parsing              : 0.15
% 2.00/1.25  CNF conversion       : 0.02
% 2.00/1.25  Main loop            : 0.16
% 2.00/1.25  Inferencing          : 0.05
% 2.00/1.25  Reduction            : 0.06
% 2.00/1.25  Demodulation         : 0.04
% 2.00/1.25  BG Simplification    : 0.01
% 2.00/1.25  Subsumption          : 0.02
% 2.00/1.25  Abstraction          : 0.01
% 2.00/1.25  MUC search           : 0.00
% 2.00/1.25  Cooper               : 0.00
% 2.00/1.25  Total                : 0.48
% 2.00/1.25  Index Insertion      : 0.00
% 2.00/1.25  Index Deletion       : 0.00
% 2.00/1.25  Index Matching       : 0.00
% 2.00/1.25  BG Taut test         : 0.00
%------------------------------------------------------------------------------
