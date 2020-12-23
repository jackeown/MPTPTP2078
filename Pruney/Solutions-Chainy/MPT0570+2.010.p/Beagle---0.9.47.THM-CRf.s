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
% DateTime   : Thu Dec  3 10:01:42 EST 2020

% Result     : Theorem 2.32s
% Output     : CNFRefutation 2.32s
% Verified   : 
% Statistics : Number of formulae       :   43 (  57 expanded)
%              Number of leaves         :   23 (  30 expanded)
%              Depth                    :    7
%              Number of atoms          :   48 (  82 expanded)
%              Number of equality atoms :   15 (  28 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > v1_relat_1 > k4_xboole_0 > k3_xboole_0 > k10_relat_1 > #nlpp > k2_relat_1 > k1_xboole_0 > #skF_3 > #skF_4 > #skF_2 > #skF_1

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

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

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

tff(f_73,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ~ ( A != k1_xboole_0
            & r1_tarski(A,k2_relat_1(B))
            & k10_relat_1(B,A) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t174_relat_1)).

tff(f_34,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_62,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( k10_relat_1(B,A) = k1_xboole_0
      <=> r1_xboole_0(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t173_relat_1)).

tff(f_52,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_48,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_56,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k4_xboole_0(B,A))
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_xboole_1)).

tff(c_26,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( r2_hidden('#skF_1'(A_3,B_4),A_3)
      | r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_28,plain,(
    v1_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_22,plain,(
    k10_relat_1('#skF_4','#skF_3') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_294,plain,(
    ! [B_69,A_70] :
      ( r1_xboole_0(k2_relat_1(B_69),A_70)
      | k10_relat_1(B_69,A_70) != k1_xboole_0
      | ~ v1_relat_1(B_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_24,plain,(
    r1_tarski('#skF_3',k2_relat_1('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_67,plain,(
    ! [A_23,B_24] :
      ( k3_xboole_0(A_23,B_24) = A_23
      | ~ r1_tarski(A_23,B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_71,plain,(
    k3_xboole_0('#skF_3',k2_relat_1('#skF_4')) = '#skF_3' ),
    inference(resolution,[status(thm)],[c_24,c_67])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_77,plain,(
    ! [A_27,B_28,C_29] :
      ( ~ r1_xboole_0(A_27,B_28)
      | ~ r2_hidden(C_29,k3_xboole_0(A_27,B_28)) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_121,plain,(
    ! [A_39,B_40,C_41] :
      ( ~ r1_xboole_0(A_39,B_40)
      | ~ r2_hidden(C_41,k3_xboole_0(B_40,A_39)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_77])).

tff(c_131,plain,(
    ! [C_41] :
      ( ~ r1_xboole_0(k2_relat_1('#skF_4'),'#skF_3')
      | ~ r2_hidden(C_41,'#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_71,c_121])).

tff(c_139,plain,(
    ~ r1_xboole_0(k2_relat_1('#skF_4'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_131])).

tff(c_315,plain,
    ( k10_relat_1('#skF_4','#skF_3') != k1_xboole_0
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_294,c_139])).

tff(c_328,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_22,c_315])).

tff(c_331,plain,(
    ! [C_71] : ~ r2_hidden(C_71,'#skF_3') ),
    inference(splitRight,[status(thm)],[c_131])).

tff(c_338,plain,(
    ! [B_72] : r1_tarski('#skF_3',B_72) ),
    inference(resolution,[status(thm)],[c_8,c_331])).

tff(c_16,plain,(
    ! [A_15,B_16] :
      ( k1_xboole_0 = A_15
      | ~ r1_tarski(A_15,k4_xboole_0(B_16,A_15)) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_345,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_338,c_16])).

tff(c_350,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_345])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:29:06 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.32/1.41  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.32/1.41  
% 2.32/1.41  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.32/1.42  %$ r2_hidden > r1_xboole_0 > r1_tarski > v1_relat_1 > k4_xboole_0 > k3_xboole_0 > k10_relat_1 > #nlpp > k2_relat_1 > k1_xboole_0 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 2.32/1.42  
% 2.32/1.42  %Foreground sorts:
% 2.32/1.42  
% 2.32/1.42  
% 2.32/1.42  %Background operators:
% 2.32/1.42  
% 2.32/1.42  
% 2.32/1.42  %Foreground operators:
% 2.32/1.42  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.32/1.42  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.32/1.42  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.32/1.42  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.32/1.42  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.32/1.42  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.32/1.42  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.32/1.42  tff('#skF_3', type, '#skF_3': $i).
% 2.32/1.42  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.32/1.42  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 2.32/1.42  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.32/1.42  tff('#skF_4', type, '#skF_4': $i).
% 2.32/1.42  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.32/1.42  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.32/1.42  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.32/1.42  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.32/1.42  
% 2.32/1.43  tff(f_73, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => ~((~(A = k1_xboole_0) & r1_tarski(A, k2_relat_1(B))) & (k10_relat_1(B, A) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t174_relat_1)).
% 2.32/1.43  tff(f_34, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 2.32/1.43  tff(f_62, axiom, (![A, B]: (v1_relat_1(B) => ((k10_relat_1(B, A) = k1_xboole_0) <=> r1_xboole_0(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t173_relat_1)).
% 2.32/1.43  tff(f_52, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 2.32/1.43  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 2.32/1.43  tff(f_48, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 2.32/1.43  tff(f_56, axiom, (![A, B]: (r1_tarski(A, k4_xboole_0(B, A)) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_xboole_1)).
% 2.32/1.43  tff(c_26, plain, (k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.32/1.43  tff(c_8, plain, (![A_3, B_4]: (r2_hidden('#skF_1'(A_3, B_4), A_3) | r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.32/1.43  tff(c_28, plain, (v1_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.32/1.43  tff(c_22, plain, (k10_relat_1('#skF_4', '#skF_3')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.32/1.43  tff(c_294, plain, (![B_69, A_70]: (r1_xboole_0(k2_relat_1(B_69), A_70) | k10_relat_1(B_69, A_70)!=k1_xboole_0 | ~v1_relat_1(B_69))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.32/1.43  tff(c_24, plain, (r1_tarski('#skF_3', k2_relat_1('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.32/1.43  tff(c_67, plain, (![A_23, B_24]: (k3_xboole_0(A_23, B_24)=A_23 | ~r1_tarski(A_23, B_24))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.32/1.43  tff(c_71, plain, (k3_xboole_0('#skF_3', k2_relat_1('#skF_4'))='#skF_3'), inference(resolution, [status(thm)], [c_24, c_67])).
% 2.32/1.43  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.32/1.43  tff(c_77, plain, (![A_27, B_28, C_29]: (~r1_xboole_0(A_27, B_28) | ~r2_hidden(C_29, k3_xboole_0(A_27, B_28)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.32/1.43  tff(c_121, plain, (![A_39, B_40, C_41]: (~r1_xboole_0(A_39, B_40) | ~r2_hidden(C_41, k3_xboole_0(B_40, A_39)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_77])).
% 2.32/1.43  tff(c_131, plain, (![C_41]: (~r1_xboole_0(k2_relat_1('#skF_4'), '#skF_3') | ~r2_hidden(C_41, '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_71, c_121])).
% 2.32/1.43  tff(c_139, plain, (~r1_xboole_0(k2_relat_1('#skF_4'), '#skF_3')), inference(splitLeft, [status(thm)], [c_131])).
% 2.32/1.43  tff(c_315, plain, (k10_relat_1('#skF_4', '#skF_3')!=k1_xboole_0 | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_294, c_139])).
% 2.32/1.43  tff(c_328, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_28, c_22, c_315])).
% 2.32/1.43  tff(c_331, plain, (![C_71]: (~r2_hidden(C_71, '#skF_3'))), inference(splitRight, [status(thm)], [c_131])).
% 2.32/1.43  tff(c_338, plain, (![B_72]: (r1_tarski('#skF_3', B_72))), inference(resolution, [status(thm)], [c_8, c_331])).
% 2.32/1.43  tff(c_16, plain, (![A_15, B_16]: (k1_xboole_0=A_15 | ~r1_tarski(A_15, k4_xboole_0(B_16, A_15)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.32/1.43  tff(c_345, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_338, c_16])).
% 2.32/1.43  tff(c_350, plain, $false, inference(negUnitSimplification, [status(thm)], [c_26, c_345])).
% 2.32/1.43  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.32/1.43  
% 2.32/1.43  Inference rules
% 2.32/1.43  ----------------------
% 2.32/1.43  #Ref     : 0
% 2.32/1.43  #Sup     : 78
% 2.32/1.43  #Fact    : 0
% 2.32/1.43  #Define  : 0
% 2.32/1.43  #Split   : 2
% 2.32/1.43  #Chain   : 0
% 2.32/1.43  #Close   : 0
% 2.32/1.43  
% 2.32/1.43  Ordering : KBO
% 2.32/1.43  
% 2.32/1.43  Simplification rules
% 2.32/1.43  ----------------------
% 2.32/1.43  #Subsume      : 21
% 2.32/1.43  #Demod        : 6
% 2.32/1.43  #Tautology    : 17
% 2.32/1.43  #SimpNegUnit  : 2
% 2.32/1.43  #BackRed      : 0
% 2.32/1.43  
% 2.32/1.43  #Partial instantiations: 0
% 2.32/1.43  #Strategies tried      : 1
% 2.32/1.43  
% 2.32/1.43  Timing (in seconds)
% 2.32/1.43  ----------------------
% 2.32/1.43  Preprocessing        : 0.36
% 2.32/1.43  Parsing              : 0.21
% 2.32/1.43  CNF conversion       : 0.02
% 2.32/1.43  Main loop            : 0.27
% 2.32/1.43  Inferencing          : 0.11
% 2.32/1.43  Reduction            : 0.08
% 2.32/1.43  Demodulation         : 0.05
% 2.32/1.43  BG Simplification    : 0.02
% 2.32/1.43  Subsumption          : 0.05
% 2.32/1.43  Abstraction          : 0.01
% 2.32/1.43  MUC search           : 0.00
% 2.32/1.43  Cooper               : 0.00
% 2.32/1.43  Total                : 0.66
% 2.32/1.43  Index Insertion      : 0.00
% 2.32/1.43  Index Deletion       : 0.00
% 2.32/1.43  Index Matching       : 0.00
% 2.32/1.43  BG Taut test         : 0.00
%------------------------------------------------------------------------------
