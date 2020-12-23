%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:43:21 EST 2020

% Result     : Theorem 1.85s
% Output     : CNFRefutation 2.04s
% Verified   : 
% Statistics : Number of formulae       :   40 (  70 expanded)
%              Number of leaves         :   20 (  34 expanded)
%              Depth                    :   10
%              Number of atoms          :   49 ( 118 expanded)
%              Number of equality atoms :    8 (  18 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > #nlpp > k1_xboole_0 > #skF_5 > #skF_6 > #skF_4 > #skF_3 > #skF_2 > #skF_1

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

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_67,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( r1_tarski(A,B)
          & r1_xboole_0(B,C) )
       => r1_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_xboole_1)).

tff(f_54,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_46,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_58,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(k3_xboole_0(A,C),k3_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_xboole_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(c_18,plain,(
    ~ r1_xboole_0('#skF_4','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_20,plain,(
    r1_xboole_0('#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_12,plain,(
    ! [A_11] :
      ( r2_hidden('#skF_3'(A_11),A_11)
      | k1_xboole_0 = A_11 ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_40,plain,(
    ! [A_23,B_24,C_25] :
      ( ~ r1_xboole_0(A_23,B_24)
      | ~ r2_hidden(C_25,k3_xboole_0(A_23,B_24)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_51,plain,(
    ! [A_26,B_27] :
      ( ~ r1_xboole_0(A_26,B_27)
      | k3_xboole_0(A_26,B_27) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_12,c_40])).

tff(c_55,plain,(
    k3_xboole_0('#skF_5','#skF_6') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_20,c_51])).

tff(c_10,plain,(
    ! [A_6,B_7,C_10] :
      ( ~ r1_xboole_0(A_6,B_7)
      | ~ r2_hidden(C_10,k3_xboole_0(A_6,B_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_59,plain,(
    ! [C_10] :
      ( ~ r1_xboole_0('#skF_5','#skF_6')
      | ~ r2_hidden(C_10,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_55,c_10])).

tff(c_63,plain,(
    ! [C_10] : ~ r2_hidden(C_10,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_59])).

tff(c_22,plain,(
    r1_tarski('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_98,plain,(
    ! [A_39,C_40,B_41] :
      ( r1_tarski(k3_xboole_0(A_39,C_40),k3_xboole_0(B_41,C_40))
      | ~ r1_tarski(A_39,B_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_104,plain,(
    ! [A_39] :
      ( r1_tarski(k3_xboole_0(A_39,'#skF_6'),k1_xboole_0)
      | ~ r1_tarski(A_39,'#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_55,c_98])).

tff(c_91,plain,(
    ! [C_36,B_37,A_38] :
      ( r2_hidden(C_36,B_37)
      | ~ r2_hidden(C_36,A_38)
      | ~ r1_tarski(A_38,B_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_112,plain,(
    ! [A_43,B_44] :
      ( r2_hidden('#skF_3'(A_43),B_44)
      | ~ r1_tarski(A_43,B_44)
      | k1_xboole_0 = A_43 ) ),
    inference(resolution,[status(thm)],[c_12,c_91])).

tff(c_126,plain,(
    ! [A_45] :
      ( ~ r1_tarski(A_45,k1_xboole_0)
      | k1_xboole_0 = A_45 ) ),
    inference(resolution,[status(thm)],[c_112,c_63])).

tff(c_148,plain,(
    ! [A_46] :
      ( k3_xboole_0(A_46,'#skF_6') = k1_xboole_0
      | ~ r1_tarski(A_46,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_104,c_126])).

tff(c_168,plain,(
    k3_xboole_0('#skF_4','#skF_6') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_22,c_148])).

tff(c_283,plain,(
    ! [A_50,B_51] :
      ( r2_hidden('#skF_2'(A_50,B_51),k3_xboole_0(A_50,B_51))
      | r1_xboole_0(A_50,B_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_291,plain,
    ( r2_hidden('#skF_2'('#skF_4','#skF_6'),k1_xboole_0)
    | r1_xboole_0('#skF_4','#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_168,c_283])).

tff(c_301,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_18,c_63,c_291])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n011.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 14:37:12 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.85/1.23  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.04/1.23  
% 2.04/1.23  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.04/1.23  %$ r2_hidden > r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > #nlpp > k1_xboole_0 > #skF_5 > #skF_6 > #skF_4 > #skF_3 > #skF_2 > #skF_1
% 2.04/1.23  
% 2.04/1.23  %Foreground sorts:
% 2.04/1.23  
% 2.04/1.23  
% 2.04/1.23  %Background operators:
% 2.04/1.23  
% 2.04/1.23  
% 2.04/1.23  %Foreground operators:
% 2.04/1.23  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.04/1.23  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.04/1.23  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.04/1.23  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.04/1.23  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.04/1.23  tff('#skF_5', type, '#skF_5': $i).
% 2.04/1.23  tff('#skF_6', type, '#skF_6': $i).
% 2.04/1.23  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.04/1.23  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.04/1.23  tff('#skF_4', type, '#skF_4': $i).
% 2.04/1.23  tff('#skF_3', type, '#skF_3': $i > $i).
% 2.04/1.23  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.04/1.23  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.04/1.23  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.04/1.23  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.04/1.23  
% 2.04/1.24  tff(f_67, negated_conjecture, ~(![A, B, C]: ((r1_tarski(A, B) & r1_xboole_0(B, C)) => r1_xboole_0(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t63_xboole_1)).
% 2.04/1.24  tff(f_54, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 2.04/1.24  tff(f_46, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 2.04/1.24  tff(f_58, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(k3_xboole_0(A, C), k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t26_xboole_1)).
% 2.04/1.24  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 2.04/1.24  tff(c_18, plain, (~r1_xboole_0('#skF_4', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.04/1.24  tff(c_20, plain, (r1_xboole_0('#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.04/1.24  tff(c_12, plain, (![A_11]: (r2_hidden('#skF_3'(A_11), A_11) | k1_xboole_0=A_11)), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.04/1.24  tff(c_40, plain, (![A_23, B_24, C_25]: (~r1_xboole_0(A_23, B_24) | ~r2_hidden(C_25, k3_xboole_0(A_23, B_24)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.04/1.24  tff(c_51, plain, (![A_26, B_27]: (~r1_xboole_0(A_26, B_27) | k3_xboole_0(A_26, B_27)=k1_xboole_0)), inference(resolution, [status(thm)], [c_12, c_40])).
% 2.04/1.24  tff(c_55, plain, (k3_xboole_0('#skF_5', '#skF_6')=k1_xboole_0), inference(resolution, [status(thm)], [c_20, c_51])).
% 2.04/1.24  tff(c_10, plain, (![A_6, B_7, C_10]: (~r1_xboole_0(A_6, B_7) | ~r2_hidden(C_10, k3_xboole_0(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.04/1.24  tff(c_59, plain, (![C_10]: (~r1_xboole_0('#skF_5', '#skF_6') | ~r2_hidden(C_10, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_55, c_10])).
% 2.04/1.24  tff(c_63, plain, (![C_10]: (~r2_hidden(C_10, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_59])).
% 2.04/1.24  tff(c_22, plain, (r1_tarski('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.04/1.24  tff(c_98, plain, (![A_39, C_40, B_41]: (r1_tarski(k3_xboole_0(A_39, C_40), k3_xboole_0(B_41, C_40)) | ~r1_tarski(A_39, B_41))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.04/1.24  tff(c_104, plain, (![A_39]: (r1_tarski(k3_xboole_0(A_39, '#skF_6'), k1_xboole_0) | ~r1_tarski(A_39, '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_55, c_98])).
% 2.04/1.24  tff(c_91, plain, (![C_36, B_37, A_38]: (r2_hidden(C_36, B_37) | ~r2_hidden(C_36, A_38) | ~r1_tarski(A_38, B_37))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.04/1.24  tff(c_112, plain, (![A_43, B_44]: (r2_hidden('#skF_3'(A_43), B_44) | ~r1_tarski(A_43, B_44) | k1_xboole_0=A_43)), inference(resolution, [status(thm)], [c_12, c_91])).
% 2.04/1.24  tff(c_126, plain, (![A_45]: (~r1_tarski(A_45, k1_xboole_0) | k1_xboole_0=A_45)), inference(resolution, [status(thm)], [c_112, c_63])).
% 2.04/1.24  tff(c_148, plain, (![A_46]: (k3_xboole_0(A_46, '#skF_6')=k1_xboole_0 | ~r1_tarski(A_46, '#skF_5'))), inference(resolution, [status(thm)], [c_104, c_126])).
% 2.04/1.24  tff(c_168, plain, (k3_xboole_0('#skF_4', '#skF_6')=k1_xboole_0), inference(resolution, [status(thm)], [c_22, c_148])).
% 2.04/1.24  tff(c_283, plain, (![A_50, B_51]: (r2_hidden('#skF_2'(A_50, B_51), k3_xboole_0(A_50, B_51)) | r1_xboole_0(A_50, B_51))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.04/1.24  tff(c_291, plain, (r2_hidden('#skF_2'('#skF_4', '#skF_6'), k1_xboole_0) | r1_xboole_0('#skF_4', '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_168, c_283])).
% 2.04/1.24  tff(c_301, plain, $false, inference(negUnitSimplification, [status(thm)], [c_18, c_63, c_291])).
% 2.04/1.24  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.04/1.24  
% 2.04/1.24  Inference rules
% 2.04/1.24  ----------------------
% 2.04/1.24  #Ref     : 0
% 2.04/1.24  #Sup     : 63
% 2.04/1.24  #Fact    : 0
% 2.04/1.24  #Define  : 0
% 2.04/1.24  #Split   : 0
% 2.04/1.24  #Chain   : 0
% 2.04/1.24  #Close   : 0
% 2.04/1.24  
% 2.04/1.24  Ordering : KBO
% 2.04/1.24  
% 2.04/1.24  Simplification rules
% 2.04/1.24  ----------------------
% 2.04/1.24  #Subsume      : 4
% 2.04/1.24  #Demod        : 27
% 2.04/1.24  #Tautology    : 29
% 2.04/1.24  #SimpNegUnit  : 1
% 2.04/1.24  #BackRed      : 0
% 2.04/1.24  
% 2.04/1.24  #Partial instantiations: 0
% 2.04/1.24  #Strategies tried      : 1
% 2.04/1.24  
% 2.04/1.24  Timing (in seconds)
% 2.04/1.24  ----------------------
% 2.04/1.25  Preprocessing        : 0.28
% 2.04/1.25  Parsing              : 0.15
% 2.04/1.25  CNF conversion       : 0.02
% 2.04/1.25  Main loop            : 0.20
% 2.04/1.25  Inferencing          : 0.08
% 2.04/1.25  Reduction            : 0.05
% 2.04/1.25  Demodulation         : 0.04
% 2.04/1.25  BG Simplification    : 0.01
% 2.04/1.25  Subsumption          : 0.04
% 2.04/1.25  Abstraction          : 0.01
% 2.04/1.25  MUC search           : 0.00
% 2.04/1.25  Cooper               : 0.00
% 2.04/1.25  Total                : 0.50
% 2.04/1.25  Index Insertion      : 0.00
% 2.04/1.25  Index Deletion       : 0.00
% 2.04/1.25  Index Matching       : 0.00
% 2.04/1.25  BG Taut test         : 0.00
%------------------------------------------------------------------------------
