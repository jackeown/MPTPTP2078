%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:01:59 EST 2020

% Result     : Theorem 2.16s
% Output     : CNFRefutation 2.16s
% Verified   : 
% Statistics : Number of formulae       :   43 (  49 expanded)
%              Number of leaves         :   22 (  26 expanded)
%              Depth                    :   12
%              Number of atoms          :   47 (  61 expanded)
%              Number of equality atoms :   17 (  21 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > v1_relat_1 > k7_relat_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > #nlpp > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_59,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ! [B] :
            ( r1_xboole_0(B,k1_relat_1(A))
           => k7_relat_1(A,B) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t187_relat_1)).

tff(f_51,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k7_relat_1(A,k1_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_relat_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k1_relat_1(k7_relat_1(B,A)),k1_relat_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t89_relat_1)).

tff(f_33,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_31,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_xboole_0(A,k4_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t85_xboole_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( k7_relat_1(B,A) = k1_xboole_0
      <=> r1_xboole_0(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_relat_1)).

tff(c_20,plain,(
    k7_relat_1('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_24,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_18,plain,(
    ! [A_13] :
      ( k7_relat_1(A_13,k1_relat_1(A_13)) = A_13
      | ~ v1_relat_1(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_83,plain,(
    ! [B_27,A_28] :
      ( r1_tarski(k1_relat_1(k7_relat_1(B_27,A_28)),k1_relat_1(B_27))
      | ~ v1_relat_1(B_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_8,plain,(
    ! [A_5] : k5_xboole_0(A_5,k1_xboole_0) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_22,plain,(
    r1_xboole_0('#skF_2',k1_relat_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_44,plain,(
    ! [A_19,B_20] :
      ( k3_xboole_0(A_19,B_20) = k1_xboole_0
      | ~ r1_xboole_0(A_19,B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_52,plain,(
    k3_xboole_0('#skF_2',k1_relat_1('#skF_1')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_22,c_44])).

tff(c_57,plain,(
    ! [A_21,B_22] : k5_xboole_0(A_21,k3_xboole_0(A_21,B_22)) = k4_xboole_0(A_21,B_22) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_66,plain,(
    k4_xboole_0('#skF_2',k1_relat_1('#skF_1')) = k5_xboole_0('#skF_2',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_52,c_57])).

tff(c_69,plain,(
    k4_xboole_0('#skF_2',k1_relat_1('#skF_1')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_66])).

tff(c_74,plain,(
    ! [A_23,C_24,B_25] :
      ( r1_xboole_0(A_23,k4_xboole_0(C_24,B_25))
      | ~ r1_tarski(A_23,B_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_80,plain,(
    ! [A_23] :
      ( r1_xboole_0(A_23,'#skF_2')
      | ~ r1_tarski(A_23,k1_relat_1('#skF_1')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_69,c_74])).

tff(c_87,plain,(
    ! [A_28] :
      ( r1_xboole_0(k1_relat_1(k7_relat_1('#skF_1',A_28)),'#skF_2')
      | ~ v1_relat_1('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_83,c_80])).

tff(c_94,plain,(
    ! [A_29] : r1_xboole_0(k1_relat_1(k7_relat_1('#skF_1',A_29)),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_87])).

tff(c_101,plain,
    ( r1_xboole_0(k1_relat_1('#skF_1'),'#skF_2')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_94])).

tff(c_104,plain,(
    r1_xboole_0(k1_relat_1('#skF_1'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_101])).

tff(c_249,plain,(
    ! [B_37,A_38] :
      ( k7_relat_1(B_37,A_38) = k1_xboole_0
      | ~ r1_xboole_0(k1_relat_1(B_37),A_38)
      | ~ v1_relat_1(B_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_262,plain,
    ( k7_relat_1('#skF_1','#skF_2') = k1_xboole_0
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_104,c_249])).

tff(c_278,plain,(
    k7_relat_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_262])).

tff(c_280,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_20,c_278])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n016.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 15:53:19 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.16/1.33  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.16/1.34  
% 2.16/1.34  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.16/1.34  %$ r1_xboole_0 > r1_tarski > v1_relat_1 > k7_relat_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > #nlpp > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1
% 2.16/1.34  
% 2.16/1.34  %Foreground sorts:
% 2.16/1.34  
% 2.16/1.34  
% 2.16/1.34  %Background operators:
% 2.16/1.34  
% 2.16/1.34  
% 2.16/1.34  %Foreground operators:
% 2.16/1.34  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.16/1.34  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.16/1.34  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.16/1.34  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.16/1.34  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.16/1.34  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.16/1.34  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.16/1.34  tff('#skF_2', type, '#skF_2': $i).
% 2.16/1.34  tff('#skF_1', type, '#skF_1': $i).
% 2.16/1.34  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.16/1.34  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.16/1.34  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.16/1.34  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.16/1.34  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.16/1.34  
% 2.16/1.35  tff(f_59, negated_conjecture, ~(![A]: (v1_relat_1(A) => (![B]: (r1_xboole_0(B, k1_relat_1(A)) => (k7_relat_1(A, B) = k1_xboole_0))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t187_relat_1)).
% 2.16/1.35  tff(f_51, axiom, (![A]: (v1_relat_1(A) => (k7_relat_1(A, k1_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_relat_1)).
% 2.16/1.35  tff(f_41, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k7_relat_1(B, A)), k1_relat_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t89_relat_1)).
% 2.16/1.35  tff(f_33, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 2.16/1.35  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 2.16/1.35  tff(f_31, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 2.16/1.35  tff(f_37, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_xboole_0(A, k4_xboole_0(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t85_xboole_1)).
% 2.16/1.35  tff(f_47, axiom, (![A, B]: (v1_relat_1(B) => ((k7_relat_1(B, A) = k1_xboole_0) <=> r1_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t95_relat_1)).
% 2.16/1.35  tff(c_20, plain, (k7_relat_1('#skF_1', '#skF_2')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.16/1.35  tff(c_24, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.16/1.35  tff(c_18, plain, (![A_13]: (k7_relat_1(A_13, k1_relat_1(A_13))=A_13 | ~v1_relat_1(A_13))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.16/1.35  tff(c_83, plain, (![B_27, A_28]: (r1_tarski(k1_relat_1(k7_relat_1(B_27, A_28)), k1_relat_1(B_27)) | ~v1_relat_1(B_27))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.16/1.35  tff(c_8, plain, (![A_5]: (k5_xboole_0(A_5, k1_xboole_0)=A_5)), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.16/1.35  tff(c_22, plain, (r1_xboole_0('#skF_2', k1_relat_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.16/1.35  tff(c_44, plain, (![A_19, B_20]: (k3_xboole_0(A_19, B_20)=k1_xboole_0 | ~r1_xboole_0(A_19, B_20))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.16/1.35  tff(c_52, plain, (k3_xboole_0('#skF_2', k1_relat_1('#skF_1'))=k1_xboole_0), inference(resolution, [status(thm)], [c_22, c_44])).
% 2.16/1.35  tff(c_57, plain, (![A_21, B_22]: (k5_xboole_0(A_21, k3_xboole_0(A_21, B_22))=k4_xboole_0(A_21, B_22))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.16/1.35  tff(c_66, plain, (k4_xboole_0('#skF_2', k1_relat_1('#skF_1'))=k5_xboole_0('#skF_2', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_52, c_57])).
% 2.16/1.35  tff(c_69, plain, (k4_xboole_0('#skF_2', k1_relat_1('#skF_1'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_8, c_66])).
% 2.16/1.35  tff(c_74, plain, (![A_23, C_24, B_25]: (r1_xboole_0(A_23, k4_xboole_0(C_24, B_25)) | ~r1_tarski(A_23, B_25))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.16/1.35  tff(c_80, plain, (![A_23]: (r1_xboole_0(A_23, '#skF_2') | ~r1_tarski(A_23, k1_relat_1('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_69, c_74])).
% 2.16/1.35  tff(c_87, plain, (![A_28]: (r1_xboole_0(k1_relat_1(k7_relat_1('#skF_1', A_28)), '#skF_2') | ~v1_relat_1('#skF_1'))), inference(resolution, [status(thm)], [c_83, c_80])).
% 2.16/1.35  tff(c_94, plain, (![A_29]: (r1_xboole_0(k1_relat_1(k7_relat_1('#skF_1', A_29)), '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_87])).
% 2.16/1.35  tff(c_101, plain, (r1_xboole_0(k1_relat_1('#skF_1'), '#skF_2') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_18, c_94])).
% 2.16/1.35  tff(c_104, plain, (r1_xboole_0(k1_relat_1('#skF_1'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_24, c_101])).
% 2.16/1.35  tff(c_249, plain, (![B_37, A_38]: (k7_relat_1(B_37, A_38)=k1_xboole_0 | ~r1_xboole_0(k1_relat_1(B_37), A_38) | ~v1_relat_1(B_37))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.16/1.35  tff(c_262, plain, (k7_relat_1('#skF_1', '#skF_2')=k1_xboole_0 | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_104, c_249])).
% 2.16/1.35  tff(c_278, plain, (k7_relat_1('#skF_1', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_24, c_262])).
% 2.16/1.35  tff(c_280, plain, $false, inference(negUnitSimplification, [status(thm)], [c_20, c_278])).
% 2.16/1.35  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.16/1.35  
% 2.16/1.35  Inference rules
% 2.16/1.35  ----------------------
% 2.16/1.35  #Ref     : 0
% 2.16/1.35  #Sup     : 64
% 2.16/1.35  #Fact    : 0
% 2.16/1.35  #Define  : 0
% 2.16/1.35  #Split   : 0
% 2.16/1.35  #Chain   : 0
% 2.16/1.35  #Close   : 0
% 2.16/1.35  
% 2.16/1.35  Ordering : KBO
% 2.16/1.35  
% 2.16/1.35  Simplification rules
% 2.16/1.35  ----------------------
% 2.16/1.35  #Subsume      : 0
% 2.16/1.35  #Demod        : 18
% 2.16/1.35  #Tautology    : 36
% 2.16/1.35  #SimpNegUnit  : 1
% 2.16/1.35  #BackRed      : 0
% 2.16/1.35  
% 2.16/1.35  #Partial instantiations: 0
% 2.16/1.35  #Strategies tried      : 1
% 2.16/1.35  
% 2.16/1.35  Timing (in seconds)
% 2.16/1.35  ----------------------
% 2.16/1.36  Preprocessing        : 0.31
% 2.16/1.36  Parsing              : 0.16
% 2.16/1.36  CNF conversion       : 0.02
% 2.16/1.36  Main loop            : 0.19
% 2.16/1.36  Inferencing          : 0.08
% 2.16/1.36  Reduction            : 0.06
% 2.16/1.36  Demodulation         : 0.04
% 2.16/1.36  BG Simplification    : 0.01
% 2.16/1.36  Subsumption          : 0.03
% 2.16/1.36  Abstraction          : 0.01
% 2.16/1.36  MUC search           : 0.00
% 2.16/1.36  Cooper               : 0.00
% 2.16/1.36  Total                : 0.53
% 2.16/1.36  Index Insertion      : 0.00
% 2.16/1.36  Index Deletion       : 0.00
% 2.16/1.36  Index Matching       : 0.00
% 2.16/1.36  BG Taut test         : 0.00
%------------------------------------------------------------------------------
