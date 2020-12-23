%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:01:10 EST 2020

% Result     : Theorem 1.76s
% Output     : CNFRefutation 1.76s
% Verified   : 
% Statistics : Number of formulae       :   35 (  50 expanded)
%              Number of leaves         :   17 (  24 expanded)
%              Depth                    :    6
%              Number of atoms          :   44 (  75 expanded)
%              Number of equality atoms :    6 (   6 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k9_relat_1 > k7_relat_1 > k3_xboole_0 > #nlpp > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff(f_53,negated_conjecture,(
    ~ ! [A,B,C] :
        ( v1_relat_1(C)
       => r1_tarski(k9_relat_1(k7_relat_1(C,A),B),k9_relat_1(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t161_relat_1)).

tff(f_48,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k7_relat_1(B,A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_relat_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k3_xboole_0(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_relat_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ! [C] :
          ( v1_relat_1(C)
         => ( r1_tarski(B,C)
           => r1_tarski(k9_relat_1(B,A),k9_relat_1(C,A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t157_relat_1)).

tff(c_14,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_10,plain,(
    ! [B_12,A_11] :
      ( r1_tarski(k7_relat_1(B_12,A_11),B_12)
      | ~ v1_relat_1(B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_63,plain,(
    ! [A_21,B_22] :
      ( k3_xboole_0(A_21,B_22) = A_21
      | ~ r1_tarski(A_21,B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_66,plain,(
    ! [B_12,A_11] :
      ( k3_xboole_0(k7_relat_1(B_12,A_11),B_12) = k7_relat_1(B_12,A_11)
      | ~ v1_relat_1(B_12) ) ),
    inference(resolution,[status(thm)],[c_10,c_63])).

tff(c_69,plain,(
    ! [B_23,A_24] :
      ( k3_xboole_0(B_23,k7_relat_1(B_23,A_24)) = k7_relat_1(B_23,A_24)
      | ~ v1_relat_1(B_23) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_66])).

tff(c_6,plain,(
    ! [A_5,B_6] :
      ( v1_relat_1(k3_xboole_0(A_5,B_6))
      | ~ v1_relat_1(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_78,plain,(
    ! [B_23,A_24] :
      ( v1_relat_1(k7_relat_1(B_23,A_24))
      | ~ v1_relat_1(B_23)
      | ~ v1_relat_1(B_23) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_69,c_6])).

tff(c_84,plain,(
    ! [B_25,A_26,C_27] :
      ( r1_tarski(k9_relat_1(B_25,A_26),k9_relat_1(C_27,A_26))
      | ~ r1_tarski(B_25,C_27)
      | ~ v1_relat_1(C_27)
      | ~ v1_relat_1(B_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_12,plain,(
    ~ r1_tarski(k9_relat_1(k7_relat_1('#skF_3','#skF_1'),'#skF_2'),k9_relat_1('#skF_3','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_87,plain,
    ( ~ r1_tarski(k7_relat_1('#skF_3','#skF_1'),'#skF_3')
    | ~ v1_relat_1('#skF_3')
    | ~ v1_relat_1(k7_relat_1('#skF_3','#skF_1')) ),
    inference(resolution,[status(thm)],[c_84,c_12])).

tff(c_93,plain,
    ( ~ r1_tarski(k7_relat_1('#skF_3','#skF_1'),'#skF_3')
    | ~ v1_relat_1(k7_relat_1('#skF_3','#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_87])).

tff(c_96,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_3','#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_93])).

tff(c_99,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_78,c_96])).

tff(c_103,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_99])).

tff(c_104,plain,(
    ~ r1_tarski(k7_relat_1('#skF_3','#skF_1'),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_93])).

tff(c_108,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_10,c_104])).

tff(c_112,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_108])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n002.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 11:53:37 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.76/1.13  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.76/1.14  
% 1.76/1.14  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.76/1.14  %$ r1_tarski > v1_relat_1 > k9_relat_1 > k7_relat_1 > k3_xboole_0 > #nlpp > #skF_2 > #skF_3 > #skF_1
% 1.76/1.14  
% 1.76/1.14  %Foreground sorts:
% 1.76/1.14  
% 1.76/1.14  
% 1.76/1.14  %Background operators:
% 1.76/1.14  
% 1.76/1.14  
% 1.76/1.14  %Foreground operators:
% 1.76/1.14  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.76/1.14  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 1.76/1.14  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.76/1.14  tff('#skF_2', type, '#skF_2': $i).
% 1.76/1.14  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 1.76/1.14  tff('#skF_3', type, '#skF_3': $i).
% 1.76/1.14  tff('#skF_1', type, '#skF_1': $i).
% 1.76/1.14  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.76/1.14  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.76/1.14  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.76/1.14  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.76/1.14  
% 1.76/1.15  tff(f_53, negated_conjecture, ~(![A, B, C]: (v1_relat_1(C) => r1_tarski(k9_relat_1(k7_relat_1(C, A), B), k9_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t161_relat_1)).
% 1.76/1.15  tff(f_48, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k7_relat_1(B, A), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t88_relat_1)).
% 1.76/1.15  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 1.76/1.15  tff(f_31, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 1.76/1.15  tff(f_35, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_relat_1)).
% 1.76/1.15  tff(f_44, axiom, (![A, B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (r1_tarski(B, C) => r1_tarski(k9_relat_1(B, A), k9_relat_1(C, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t157_relat_1)).
% 1.76/1.15  tff(c_14, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_53])).
% 1.76/1.15  tff(c_10, plain, (![B_12, A_11]: (r1_tarski(k7_relat_1(B_12, A_11), B_12) | ~v1_relat_1(B_12))), inference(cnfTransformation, [status(thm)], [f_48])).
% 1.76/1.15  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.76/1.15  tff(c_63, plain, (![A_21, B_22]: (k3_xboole_0(A_21, B_22)=A_21 | ~r1_tarski(A_21, B_22))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.76/1.15  tff(c_66, plain, (![B_12, A_11]: (k3_xboole_0(k7_relat_1(B_12, A_11), B_12)=k7_relat_1(B_12, A_11) | ~v1_relat_1(B_12))), inference(resolution, [status(thm)], [c_10, c_63])).
% 1.76/1.15  tff(c_69, plain, (![B_23, A_24]: (k3_xboole_0(B_23, k7_relat_1(B_23, A_24))=k7_relat_1(B_23, A_24) | ~v1_relat_1(B_23))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_66])).
% 1.76/1.15  tff(c_6, plain, (![A_5, B_6]: (v1_relat_1(k3_xboole_0(A_5, B_6)) | ~v1_relat_1(A_5))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.76/1.15  tff(c_78, plain, (![B_23, A_24]: (v1_relat_1(k7_relat_1(B_23, A_24)) | ~v1_relat_1(B_23) | ~v1_relat_1(B_23))), inference(superposition, [status(thm), theory('equality')], [c_69, c_6])).
% 1.76/1.15  tff(c_84, plain, (![B_25, A_26, C_27]: (r1_tarski(k9_relat_1(B_25, A_26), k9_relat_1(C_27, A_26)) | ~r1_tarski(B_25, C_27) | ~v1_relat_1(C_27) | ~v1_relat_1(B_25))), inference(cnfTransformation, [status(thm)], [f_44])).
% 1.76/1.15  tff(c_12, plain, (~r1_tarski(k9_relat_1(k7_relat_1('#skF_3', '#skF_1'), '#skF_2'), k9_relat_1('#skF_3', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_53])).
% 1.76/1.15  tff(c_87, plain, (~r1_tarski(k7_relat_1('#skF_3', '#skF_1'), '#skF_3') | ~v1_relat_1('#skF_3') | ~v1_relat_1(k7_relat_1('#skF_3', '#skF_1'))), inference(resolution, [status(thm)], [c_84, c_12])).
% 1.76/1.15  tff(c_93, plain, (~r1_tarski(k7_relat_1('#skF_3', '#skF_1'), '#skF_3') | ~v1_relat_1(k7_relat_1('#skF_3', '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_87])).
% 1.76/1.15  tff(c_96, plain, (~v1_relat_1(k7_relat_1('#skF_3', '#skF_1'))), inference(splitLeft, [status(thm)], [c_93])).
% 1.76/1.15  tff(c_99, plain, (~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_78, c_96])).
% 1.76/1.15  tff(c_103, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_14, c_99])).
% 1.76/1.15  tff(c_104, plain, (~r1_tarski(k7_relat_1('#skF_3', '#skF_1'), '#skF_3')), inference(splitRight, [status(thm)], [c_93])).
% 1.76/1.15  tff(c_108, plain, (~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_10, c_104])).
% 1.76/1.15  tff(c_112, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_14, c_108])).
% 1.76/1.15  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.76/1.15  
% 1.76/1.15  Inference rules
% 1.76/1.15  ----------------------
% 1.76/1.15  #Ref     : 0
% 1.76/1.15  #Sup     : 21
% 1.76/1.15  #Fact    : 0
% 1.76/1.15  #Define  : 0
% 1.76/1.15  #Split   : 1
% 1.76/1.15  #Chain   : 0
% 1.76/1.15  #Close   : 0
% 1.76/1.15  
% 1.76/1.15  Ordering : KBO
% 1.76/1.15  
% 1.76/1.15  Simplification rules
% 1.76/1.15  ----------------------
% 1.76/1.15  #Subsume      : 3
% 1.76/1.15  #Demod        : 4
% 1.76/1.15  #Tautology    : 11
% 1.76/1.15  #SimpNegUnit  : 0
% 1.76/1.15  #BackRed      : 0
% 1.76/1.15  
% 1.76/1.15  #Partial instantiations: 0
% 1.76/1.15  #Strategies tried      : 1
% 1.76/1.15  
% 1.76/1.15  Timing (in seconds)
% 1.76/1.15  ----------------------
% 1.76/1.15  Preprocessing        : 0.26
% 1.76/1.15  Parsing              : 0.14
% 1.76/1.15  CNF conversion       : 0.01
% 1.76/1.15  Main loop            : 0.13
% 1.76/1.15  Inferencing          : 0.05
% 1.76/1.15  Reduction            : 0.03
% 1.76/1.15  Demodulation         : 0.03
% 1.76/1.15  BG Simplification    : 0.01
% 1.76/1.15  Subsumption          : 0.02
% 1.76/1.15  Abstraction          : 0.01
% 1.76/1.15  MUC search           : 0.00
% 1.76/1.15  Cooper               : 0.00
% 1.76/1.15  Total                : 0.40
% 1.76/1.15  Index Insertion      : 0.00
% 1.76/1.15  Index Deletion       : 0.00
% 1.76/1.15  Index Matching       : 0.00
% 1.76/1.15  BG Taut test         : 0.00
%------------------------------------------------------------------------------
