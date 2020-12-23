%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:01:42 EST 2020

% Result     : Theorem 1.85s
% Output     : CNFRefutation 2.00s
% Verified   : 
% Statistics : Number of formulae       :   46 (  67 expanded)
%              Number of leaves         :   24 (  34 expanded)
%              Depth                    :    8
%              Number of atoms          :   47 (  88 expanded)
%              Number of equality atoms :   20 (  40 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > v1_relat_1 > k3_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k2_relat_1 > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_72,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ~ ( A != k1_xboole_0
            & r1_tarski(A,k2_relat_1(B))
            & k10_relat_1(B,A) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t174_relat_1)).

tff(f_47,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_61,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( k10_relat_1(B,A) = k1_xboole_0
      <=> r1_xboole_0(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t173_relat_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_53,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_55,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

tff(c_22,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_6,plain,(
    ! [A_6] :
      ( r2_hidden('#skF_2'(A_6),A_6)
      | k1_xboole_0 = A_6 ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_24,plain,(
    v1_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_18,plain,(
    k10_relat_1('#skF_4','#skF_3') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_197,plain,(
    ! [B_41,A_42] :
      ( r1_xboole_0(k2_relat_1(B_41),A_42)
      | k10_relat_1(B_41,A_42) != k1_xboole_0
      | ~ v1_relat_1(B_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_20,plain,(
    r1_tarski('#skF_3',k2_relat_1('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_78,plain,(
    ! [A_21,B_22] :
      ( k3_xboole_0(A_21,B_22) = A_21
      | ~ r1_tarski(A_21,B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_82,plain,(
    k3_xboole_0('#skF_3',k2_relat_1('#skF_4')) = '#skF_3' ),
    inference(resolution,[status(thm)],[c_20,c_78])).

tff(c_10,plain,(
    ! [B_11,A_10] : k2_tarski(B_11,A_10) = k2_tarski(A_10,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_63,plain,(
    ! [A_19,B_20] : k1_setfam_1(k2_tarski(A_19,B_20)) = k3_xboole_0(A_19,B_20) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_96,plain,(
    ! [B_26,A_27] : k1_setfam_1(k2_tarski(B_26,A_27)) = k3_xboole_0(A_27,B_26) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_63])).

tff(c_12,plain,(
    ! [A_12,B_13] : k1_setfam_1(k2_tarski(A_12,B_13)) = k3_xboole_0(A_12,B_13) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_119,plain,(
    ! [B_28,A_29] : k3_xboole_0(B_28,A_29) = k3_xboole_0(A_29,B_28) ),
    inference(superposition,[status(thm),theory(equality)],[c_96,c_12])).

tff(c_4,plain,(
    ! [A_1,B_2,C_5] :
      ( ~ r1_xboole_0(A_1,B_2)
      | ~ r2_hidden(C_5,k3_xboole_0(A_1,B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_175,plain,(
    ! [B_34,A_35,C_36] :
      ( ~ r1_xboole_0(B_34,A_35)
      | ~ r2_hidden(C_36,k3_xboole_0(A_35,B_34)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_119,c_4])).

tff(c_187,plain,(
    ! [C_36] :
      ( ~ r1_xboole_0(k2_relat_1('#skF_4'),'#skF_3')
      | ~ r2_hidden(C_36,'#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_82,c_175])).

tff(c_194,plain,(
    ~ r1_xboole_0(k2_relat_1('#skF_4'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_187])).

tff(c_205,plain,
    ( k10_relat_1('#skF_4','#skF_3') != k1_xboole_0
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_197,c_194])).

tff(c_214,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_18,c_205])).

tff(c_222,plain,(
    ! [C_45] : ~ r2_hidden(C_45,'#skF_3') ),
    inference(splitRight,[status(thm)],[c_187])).

tff(c_226,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_6,c_222])).

tff(c_230,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_22,c_226])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:20:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.85/1.31  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.00/1.31  
% 2.00/1.31  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.00/1.31  %$ r2_hidden > r1_xboole_0 > r1_tarski > v1_relat_1 > k3_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k2_relat_1 > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 2.00/1.31  
% 2.00/1.31  %Foreground sorts:
% 2.00/1.31  
% 2.00/1.31  
% 2.00/1.31  %Background operators:
% 2.00/1.31  
% 2.00/1.31  
% 2.00/1.31  %Foreground operators:
% 2.00/1.31  tff('#skF_2', type, '#skF_2': $i > $i).
% 2.00/1.31  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.00/1.31  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.00/1.31  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.00/1.31  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.00/1.31  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.00/1.31  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.00/1.31  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.00/1.31  tff('#skF_3', type, '#skF_3': $i).
% 2.00/1.31  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.00/1.31  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 2.00/1.31  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.00/1.31  tff('#skF_4', type, '#skF_4': $i).
% 2.00/1.31  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.00/1.31  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.00/1.31  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.00/1.31  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.00/1.31  
% 2.00/1.32  tff(f_72, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => ~((~(A = k1_xboole_0) & r1_tarski(A, k2_relat_1(B))) & (k10_relat_1(B, A) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t174_relat_1)).
% 2.00/1.32  tff(f_47, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 2.00/1.32  tff(f_61, axiom, (![A, B]: (v1_relat_1(B) => ((k10_relat_1(B, A) = k1_xboole_0) <=> r1_xboole_0(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t173_relat_1)).
% 2.00/1.32  tff(f_51, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 2.00/1.32  tff(f_53, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 2.00/1.32  tff(f_55, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_setfam_1)).
% 2.00/1.32  tff(f_39, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 2.00/1.32  tff(c_22, plain, (k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.00/1.32  tff(c_6, plain, (![A_6]: (r2_hidden('#skF_2'(A_6), A_6) | k1_xboole_0=A_6)), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.00/1.32  tff(c_24, plain, (v1_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.00/1.32  tff(c_18, plain, (k10_relat_1('#skF_4', '#skF_3')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.00/1.32  tff(c_197, plain, (![B_41, A_42]: (r1_xboole_0(k2_relat_1(B_41), A_42) | k10_relat_1(B_41, A_42)!=k1_xboole_0 | ~v1_relat_1(B_41))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.00/1.32  tff(c_20, plain, (r1_tarski('#skF_3', k2_relat_1('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.00/1.32  tff(c_78, plain, (![A_21, B_22]: (k3_xboole_0(A_21, B_22)=A_21 | ~r1_tarski(A_21, B_22))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.00/1.32  tff(c_82, plain, (k3_xboole_0('#skF_3', k2_relat_1('#skF_4'))='#skF_3'), inference(resolution, [status(thm)], [c_20, c_78])).
% 2.00/1.32  tff(c_10, plain, (![B_11, A_10]: (k2_tarski(B_11, A_10)=k2_tarski(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.00/1.32  tff(c_63, plain, (![A_19, B_20]: (k1_setfam_1(k2_tarski(A_19, B_20))=k3_xboole_0(A_19, B_20))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.00/1.32  tff(c_96, plain, (![B_26, A_27]: (k1_setfam_1(k2_tarski(B_26, A_27))=k3_xboole_0(A_27, B_26))), inference(superposition, [status(thm), theory('equality')], [c_10, c_63])).
% 2.00/1.32  tff(c_12, plain, (![A_12, B_13]: (k1_setfam_1(k2_tarski(A_12, B_13))=k3_xboole_0(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.00/1.32  tff(c_119, plain, (![B_28, A_29]: (k3_xboole_0(B_28, A_29)=k3_xboole_0(A_29, B_28))), inference(superposition, [status(thm), theory('equality')], [c_96, c_12])).
% 2.00/1.32  tff(c_4, plain, (![A_1, B_2, C_5]: (~r1_xboole_0(A_1, B_2) | ~r2_hidden(C_5, k3_xboole_0(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.00/1.32  tff(c_175, plain, (![B_34, A_35, C_36]: (~r1_xboole_0(B_34, A_35) | ~r2_hidden(C_36, k3_xboole_0(A_35, B_34)))), inference(superposition, [status(thm), theory('equality')], [c_119, c_4])).
% 2.00/1.32  tff(c_187, plain, (![C_36]: (~r1_xboole_0(k2_relat_1('#skF_4'), '#skF_3') | ~r2_hidden(C_36, '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_82, c_175])).
% 2.00/1.32  tff(c_194, plain, (~r1_xboole_0(k2_relat_1('#skF_4'), '#skF_3')), inference(splitLeft, [status(thm)], [c_187])).
% 2.00/1.32  tff(c_205, plain, (k10_relat_1('#skF_4', '#skF_3')!=k1_xboole_0 | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_197, c_194])).
% 2.00/1.32  tff(c_214, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_24, c_18, c_205])).
% 2.00/1.32  tff(c_222, plain, (![C_45]: (~r2_hidden(C_45, '#skF_3'))), inference(splitRight, [status(thm)], [c_187])).
% 2.00/1.32  tff(c_226, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_6, c_222])).
% 2.00/1.32  tff(c_230, plain, $false, inference(negUnitSimplification, [status(thm)], [c_22, c_226])).
% 2.00/1.32  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.00/1.32  
% 2.00/1.32  Inference rules
% 2.00/1.32  ----------------------
% 2.00/1.32  #Ref     : 0
% 2.00/1.32  #Sup     : 50
% 2.00/1.32  #Fact    : 0
% 2.00/1.32  #Define  : 0
% 2.00/1.32  #Split   : 2
% 2.00/1.32  #Chain   : 0
% 2.00/1.32  #Close   : 0
% 2.00/1.32  
% 2.00/1.32  Ordering : KBO
% 2.00/1.32  
% 2.00/1.32  Simplification rules
% 2.00/1.32  ----------------------
% 2.00/1.32  #Subsume      : 4
% 2.00/1.32  #Demod        : 5
% 2.00/1.32  #Tautology    : 28
% 2.00/1.32  #SimpNegUnit  : 1
% 2.00/1.32  #BackRed      : 0
% 2.00/1.32  
% 2.00/1.32  #Partial instantiations: 0
% 2.00/1.32  #Strategies tried      : 1
% 2.00/1.32  
% 2.00/1.32  Timing (in seconds)
% 2.00/1.32  ----------------------
% 2.00/1.33  Preprocessing        : 0.33
% 2.00/1.33  Parsing              : 0.17
% 2.00/1.33  CNF conversion       : 0.02
% 2.00/1.33  Main loop            : 0.16
% 2.00/1.33  Inferencing          : 0.06
% 2.00/1.33  Reduction            : 0.05
% 2.00/1.33  Demodulation         : 0.04
% 2.00/1.33  BG Simplification    : 0.01
% 2.00/1.33  Subsumption          : 0.02
% 2.00/1.33  Abstraction          : 0.01
% 2.00/1.33  MUC search           : 0.00
% 2.00/1.33  Cooper               : 0.00
% 2.00/1.33  Total                : 0.52
% 2.00/1.33  Index Insertion      : 0.00
% 2.00/1.33  Index Deletion       : 0.00
% 2.00/1.33  Index Matching       : 0.00
% 2.00/1.33  BG Taut test         : 0.00
%------------------------------------------------------------------------------
