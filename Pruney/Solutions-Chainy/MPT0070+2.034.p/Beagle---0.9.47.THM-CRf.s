%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:43:22 EST 2020

% Result     : Theorem 2.03s
% Output     : CNFRefutation 2.03s
% Verified   : 
% Statistics : Number of formulae       :   41 (  50 expanded)
%              Number of leaves         :   20 (  27 expanded)
%              Depth                    :   10
%              Number of atoms          :   54 (  82 expanded)
%              Number of equality atoms :    7 (  10 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k4_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_1 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_72,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( r1_tarski(A,B)
          & r1_xboole_0(B,C) )
       => r1_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_xboole_1)).

tff(f_57,axiom,(
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

tff(f_61,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_65,axiom,(
    ! [A,B] : k4_xboole_0(A,k2_xboole_0(A,B)) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

tff(c_34,plain,(
    ~ r1_xboole_0('#skF_4','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_26,plain,(
    ! [A_9,B_10] :
      ( r2_hidden('#skF_3'(A_9,B_10),A_9)
      | r1_xboole_0(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_24,plain,(
    ! [A_9,B_10] :
      ( r2_hidden('#skF_3'(A_9,B_10),B_10)
      | r1_xboole_0(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_38,plain,(
    r1_tarski('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_63,plain,(
    ! [A_24,B_25] :
      ( k2_xboole_0(A_24,B_25) = B_25
      | ~ r1_tarski(A_24,B_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_67,plain,(
    k2_xboole_0('#skF_4','#skF_5') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_38,c_63])).

tff(c_32,plain,(
    ! [A_17,B_18] : k4_xboole_0(A_17,k2_xboole_0(A_17,B_18)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_71,plain,(
    k4_xboole_0('#skF_4','#skF_5') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_67,c_32])).

tff(c_177,plain,(
    ! [D_47,A_48,B_49] :
      ( r2_hidden(D_47,k4_xboole_0(A_48,B_49))
      | r2_hidden(D_47,B_49)
      | ~ r2_hidden(D_47,A_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_220,plain,(
    ! [D_53] :
      ( r2_hidden(D_53,k1_xboole_0)
      | r2_hidden(D_53,'#skF_5')
      | ~ r2_hidden(D_53,'#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_71,c_177])).

tff(c_100,plain,(
    ! [D_33,A_34,B_35] :
      ( r2_hidden(D_33,A_34)
      | ~ r2_hidden(D_33,k4_xboole_0(A_34,B_35)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_110,plain,(
    ! [D_33,A_17] :
      ( r2_hidden(D_33,A_17)
      | ~ r2_hidden(D_33,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_100])).

tff(c_225,plain,(
    ! [D_53,A_17] :
      ( r2_hidden(D_53,A_17)
      | r2_hidden(D_53,'#skF_5')
      | ~ r2_hidden(D_53,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_220,c_110])).

tff(c_267,plain,(
    ! [D_56] :
      ( ~ r2_hidden(D_56,'#skF_4')
      | r2_hidden(D_56,'#skF_5') ) ),
    inference(factorization,[status(thm),theory(equality)],[c_225])).

tff(c_36,plain,(
    r1_xboole_0('#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_139,plain,(
    ! [A_40,B_41,C_42] :
      ( ~ r1_xboole_0(A_40,B_41)
      | ~ r2_hidden(C_42,B_41)
      | ~ r2_hidden(C_42,A_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_145,plain,(
    ! [C_42] :
      ( ~ r2_hidden(C_42,'#skF_6')
      | ~ r2_hidden(C_42,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_36,c_139])).

tff(c_283,plain,(
    ! [D_60] :
      ( ~ r2_hidden(D_60,'#skF_6')
      | ~ r2_hidden(D_60,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_267,c_145])).

tff(c_294,plain,(
    ! [A_61] :
      ( ~ r2_hidden('#skF_3'(A_61,'#skF_6'),'#skF_4')
      | r1_xboole_0(A_61,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_24,c_283])).

tff(c_298,plain,(
    r1_xboole_0('#skF_4','#skF_6') ),
    inference(resolution,[status(thm)],[c_26,c_294])).

tff(c_302,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_34,c_298])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 16:58:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.03/1.28  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.03/1.28  
% 2.03/1.28  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.03/1.29  %$ r2_hidden > r1_xboole_0 > r1_tarski > k4_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_1 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_4
% 2.03/1.29  
% 2.03/1.29  %Foreground sorts:
% 2.03/1.29  
% 2.03/1.29  
% 2.03/1.29  %Background operators:
% 2.03/1.29  
% 2.03/1.29  
% 2.03/1.29  %Foreground operators:
% 2.03/1.29  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.03/1.29  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.03/1.29  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.03/1.29  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.03/1.29  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.03/1.29  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.03/1.29  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.03/1.29  tff('#skF_5', type, '#skF_5': $i).
% 2.03/1.29  tff('#skF_6', type, '#skF_6': $i).
% 2.03/1.29  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.03/1.29  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.03/1.29  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.03/1.29  tff('#skF_4', type, '#skF_4': $i).
% 2.03/1.29  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.03/1.29  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.03/1.29  
% 2.03/1.30  tff(f_72, negated_conjecture, ~(![A, B, C]: ((r1_tarski(A, B) & r1_xboole_0(B, C)) => r1_xboole_0(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_xboole_1)).
% 2.03/1.30  tff(f_57, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 2.03/1.30  tff(f_61, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 2.03/1.30  tff(f_65, axiom, (![A, B]: (k4_xboole_0(A, k2_xboole_0(A, B)) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_xboole_1)).
% 2.03/1.30  tff(f_35, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_xboole_0)).
% 2.03/1.30  tff(c_34, plain, (~r1_xboole_0('#skF_4', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.03/1.30  tff(c_26, plain, (![A_9, B_10]: (r2_hidden('#skF_3'(A_9, B_10), A_9) | r1_xboole_0(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.03/1.30  tff(c_24, plain, (![A_9, B_10]: (r2_hidden('#skF_3'(A_9, B_10), B_10) | r1_xboole_0(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.03/1.30  tff(c_38, plain, (r1_tarski('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.03/1.30  tff(c_63, plain, (![A_24, B_25]: (k2_xboole_0(A_24, B_25)=B_25 | ~r1_tarski(A_24, B_25))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.03/1.30  tff(c_67, plain, (k2_xboole_0('#skF_4', '#skF_5')='#skF_5'), inference(resolution, [status(thm)], [c_38, c_63])).
% 2.03/1.30  tff(c_32, plain, (![A_17, B_18]: (k4_xboole_0(A_17, k2_xboole_0(A_17, B_18))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.03/1.30  tff(c_71, plain, (k4_xboole_0('#skF_4', '#skF_5')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_67, c_32])).
% 2.03/1.30  tff(c_177, plain, (![D_47, A_48, B_49]: (r2_hidden(D_47, k4_xboole_0(A_48, B_49)) | r2_hidden(D_47, B_49) | ~r2_hidden(D_47, A_48))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.03/1.30  tff(c_220, plain, (![D_53]: (r2_hidden(D_53, k1_xboole_0) | r2_hidden(D_53, '#skF_5') | ~r2_hidden(D_53, '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_71, c_177])).
% 2.03/1.30  tff(c_100, plain, (![D_33, A_34, B_35]: (r2_hidden(D_33, A_34) | ~r2_hidden(D_33, k4_xboole_0(A_34, B_35)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.03/1.30  tff(c_110, plain, (![D_33, A_17]: (r2_hidden(D_33, A_17) | ~r2_hidden(D_33, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_32, c_100])).
% 2.03/1.30  tff(c_225, plain, (![D_53, A_17]: (r2_hidden(D_53, A_17) | r2_hidden(D_53, '#skF_5') | ~r2_hidden(D_53, '#skF_4'))), inference(resolution, [status(thm)], [c_220, c_110])).
% 2.03/1.30  tff(c_267, plain, (![D_56]: (~r2_hidden(D_56, '#skF_4') | r2_hidden(D_56, '#skF_5'))), inference(factorization, [status(thm), theory('equality')], [c_225])).
% 2.03/1.30  tff(c_36, plain, (r1_xboole_0('#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.03/1.30  tff(c_139, plain, (![A_40, B_41, C_42]: (~r1_xboole_0(A_40, B_41) | ~r2_hidden(C_42, B_41) | ~r2_hidden(C_42, A_40))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.03/1.30  tff(c_145, plain, (![C_42]: (~r2_hidden(C_42, '#skF_6') | ~r2_hidden(C_42, '#skF_5'))), inference(resolution, [status(thm)], [c_36, c_139])).
% 2.03/1.30  tff(c_283, plain, (![D_60]: (~r2_hidden(D_60, '#skF_6') | ~r2_hidden(D_60, '#skF_4'))), inference(resolution, [status(thm)], [c_267, c_145])).
% 2.03/1.30  tff(c_294, plain, (![A_61]: (~r2_hidden('#skF_3'(A_61, '#skF_6'), '#skF_4') | r1_xboole_0(A_61, '#skF_6'))), inference(resolution, [status(thm)], [c_24, c_283])).
% 2.03/1.30  tff(c_298, plain, (r1_xboole_0('#skF_4', '#skF_6')), inference(resolution, [status(thm)], [c_26, c_294])).
% 2.03/1.30  tff(c_302, plain, $false, inference(negUnitSimplification, [status(thm)], [c_34, c_34, c_298])).
% 2.03/1.30  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.03/1.30  
% 2.03/1.30  Inference rules
% 2.03/1.30  ----------------------
% 2.03/1.30  #Ref     : 0
% 2.03/1.30  #Sup     : 56
% 2.03/1.30  #Fact    : 2
% 2.03/1.30  #Define  : 0
% 2.03/1.30  #Split   : 0
% 2.03/1.30  #Chain   : 0
% 2.03/1.30  #Close   : 0
% 2.03/1.30  
% 2.03/1.30  Ordering : KBO
% 2.03/1.30  
% 2.03/1.30  Simplification rules
% 2.03/1.30  ----------------------
% 2.03/1.30  #Subsume      : 11
% 2.03/1.30  #Demod        : 9
% 2.03/1.30  #Tautology    : 21
% 2.03/1.30  #SimpNegUnit  : 1
% 2.03/1.30  #BackRed      : 0
% 2.03/1.30  
% 2.03/1.30  #Partial instantiations: 0
% 2.03/1.30  #Strategies tried      : 1
% 2.03/1.30  
% 2.03/1.30  Timing (in seconds)
% 2.03/1.30  ----------------------
% 2.03/1.30  Preprocessing        : 0.27
% 2.03/1.30  Parsing              : 0.14
% 2.03/1.30  CNF conversion       : 0.02
% 2.03/1.30  Main loop            : 0.20
% 2.03/1.30  Inferencing          : 0.08
% 2.03/1.30  Reduction            : 0.05
% 2.03/1.30  Demodulation         : 0.03
% 2.03/1.30  BG Simplification    : 0.01
% 2.03/1.30  Subsumption          : 0.04
% 2.03/1.30  Abstraction          : 0.01
% 2.03/1.30  MUC search           : 0.00
% 2.03/1.30  Cooper               : 0.00
% 2.03/1.30  Total                : 0.50
% 2.03/1.30  Index Insertion      : 0.00
% 2.03/1.30  Index Deletion       : 0.00
% 2.03/1.30  Index Matching       : 0.00
% 2.03/1.30  BG Taut test         : 0.00
%------------------------------------------------------------------------------
