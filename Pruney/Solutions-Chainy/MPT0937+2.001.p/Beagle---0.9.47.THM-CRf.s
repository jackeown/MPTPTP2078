%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:10:30 EST 2020

% Result     : Theorem 1.82s
% Output     : CNFRefutation 1.82s
% Verified   : 
% Statistics : Number of formulae       :   39 (  49 expanded)
%              Number of leaves         :   21 (  27 expanded)
%              Depth                    :    8
%              Number of atoms          :   59 (  78 expanded)
%              Number of equality atoms :    5 (   7 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > r1_relat_2 > v1_relat_2 > v1_relat_1 > k4_tarski > #nlpp > k3_relat_1 > k1_wellord2 > #skF_3 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(v1_relat_2,type,(
    v1_relat_2: $i > $o )).

tff(k3_relat_1,type,(
    k3_relat_1: $i > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(r1_relat_2,type,(
    r1_relat_2: ( $i * $i ) > $o )).

tff(k1_wellord2,type,(
    k1_wellord2: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_64,axiom,(
    ! [A] : v1_relat_1(k1_wellord2(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_wellord2)).

tff(f_41,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( r1_relat_2(A,B)
        <=> ! [C] :
              ( r2_hidden(C,B)
             => r2_hidden(k4_tarski(C,C),A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_relat_2)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_62,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( B = k1_wellord2(A)
      <=> ( k3_relat_1(B) = A
          & ! [C,D] :
              ( ( r2_hidden(C,A)
                & r2_hidden(D,A) )
             => ( r2_hidden(k4_tarski(C,D),B)
              <=> r1_tarski(C,D) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_wellord2)).

tff(f_47,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( v1_relat_2(A)
      <=> r1_relat_2(A,k3_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_relat_2)).

tff(f_67,negated_conjecture,(
    ~ ! [A] : v1_relat_2(k1_wellord2(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_wellord2)).

tff(c_36,plain,(
    ! [A_22] : v1_relat_1(k1_wellord2(A_22)) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_12,plain,(
    ! [A_3,B_9] :
      ( r2_hidden('#skF_1'(A_3,B_9),B_9)
      | r1_relat_2(A_3,B_9)
      | ~ v1_relat_1(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_32,plain,(
    ! [C_20,D_21,A_14] :
      ( r2_hidden(k4_tarski(C_20,D_21),k1_wellord2(A_14))
      | ~ r1_tarski(C_20,D_21)
      | ~ r2_hidden(D_21,A_14)
      | ~ r2_hidden(C_20,A_14)
      | ~ v1_relat_1(k1_wellord2(A_14)) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_120,plain,(
    ! [C_41,D_42,A_43] :
      ( r2_hidden(k4_tarski(C_41,D_42),k1_wellord2(A_43))
      | ~ r1_tarski(C_41,D_42)
      | ~ r2_hidden(D_42,A_43)
      | ~ r2_hidden(C_41,A_43) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_32])).

tff(c_10,plain,(
    ! [A_3,B_9] :
      ( ~ r2_hidden(k4_tarski('#skF_1'(A_3,B_9),'#skF_1'(A_3,B_9)),A_3)
      | r1_relat_2(A_3,B_9)
      | ~ v1_relat_1(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_124,plain,(
    ! [A_43,B_9] :
      ( r1_relat_2(k1_wellord2(A_43),B_9)
      | ~ v1_relat_1(k1_wellord2(A_43))
      | ~ r1_tarski('#skF_1'(k1_wellord2(A_43),B_9),'#skF_1'(k1_wellord2(A_43),B_9))
      | ~ r2_hidden('#skF_1'(k1_wellord2(A_43),B_9),A_43) ) ),
    inference(resolution,[status(thm)],[c_120,c_10])).

tff(c_136,plain,(
    ! [A_47,B_48] :
      ( r1_relat_2(k1_wellord2(A_47),B_48)
      | ~ r2_hidden('#skF_1'(k1_wellord2(A_47),B_48),A_47) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_36,c_124])).

tff(c_140,plain,(
    ! [B_9] :
      ( r1_relat_2(k1_wellord2(B_9),B_9)
      | ~ v1_relat_1(k1_wellord2(B_9)) ) ),
    inference(resolution,[status(thm)],[c_12,c_136])).

tff(c_143,plain,(
    ! [B_9] : r1_relat_2(k1_wellord2(B_9),B_9) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_140])).

tff(c_30,plain,(
    ! [A_14] :
      ( k3_relat_1(k1_wellord2(A_14)) = A_14
      | ~ v1_relat_1(k1_wellord2(A_14)) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_44,plain,(
    ! [A_14] : k3_relat_1(k1_wellord2(A_14)) = A_14 ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_30])).

tff(c_71,plain,(
    ! [A_30] :
      ( v1_relat_2(A_30)
      | ~ r1_relat_2(A_30,k3_relat_1(A_30))
      | ~ v1_relat_1(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_77,plain,(
    ! [A_14] :
      ( v1_relat_2(k1_wellord2(A_14))
      | ~ r1_relat_2(k1_wellord2(A_14),A_14)
      | ~ v1_relat_1(k1_wellord2(A_14)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_71])).

tff(c_80,plain,(
    ! [A_14] :
      ( v1_relat_2(k1_wellord2(A_14))
      | ~ r1_relat_2(k1_wellord2(A_14),A_14) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_77])).

tff(c_145,plain,(
    ! [A_14] : v1_relat_2(k1_wellord2(A_14)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_143,c_80])).

tff(c_38,plain,(
    ~ v1_relat_2(k1_wellord2('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_150,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_145,c_38])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 12:42:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.82/1.20  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.82/1.20  
% 1.82/1.20  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.82/1.21  %$ r2_hidden > r1_tarski > r1_relat_2 > v1_relat_2 > v1_relat_1 > k4_tarski > #nlpp > k3_relat_1 > k1_wellord2 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 1.82/1.21  
% 1.82/1.21  %Foreground sorts:
% 1.82/1.21  
% 1.82/1.21  
% 1.82/1.21  %Background operators:
% 1.82/1.21  
% 1.82/1.21  
% 1.82/1.21  %Foreground operators:
% 1.82/1.21  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.82/1.21  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.82/1.21  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 1.82/1.21  tff(v1_relat_2, type, v1_relat_2: $i > $o).
% 1.82/1.21  tff(k3_relat_1, type, k3_relat_1: $i > $i).
% 1.82/1.21  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 1.82/1.21  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.82/1.21  tff(r1_relat_2, type, r1_relat_2: ($i * $i) > $o).
% 1.82/1.21  tff(k1_wellord2, type, k1_wellord2: $i > $i).
% 1.82/1.21  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.82/1.21  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.82/1.21  tff('#skF_4', type, '#skF_4': $i).
% 1.82/1.21  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.82/1.21  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 1.82/1.21  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.82/1.21  
% 1.82/1.22  tff(f_64, axiom, (![A]: v1_relat_1(k1_wellord2(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_wellord2)).
% 1.82/1.22  tff(f_41, axiom, (![A]: (v1_relat_1(A) => (![B]: (r1_relat_2(A, B) <=> (![C]: (r2_hidden(C, B) => r2_hidden(k4_tarski(C, C), A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_relat_2)).
% 1.82/1.22  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 1.82/1.22  tff(f_62, axiom, (![A, B]: (v1_relat_1(B) => ((B = k1_wellord2(A)) <=> ((k3_relat_1(B) = A) & (![C, D]: ((r2_hidden(C, A) & r2_hidden(D, A)) => (r2_hidden(k4_tarski(C, D), B) <=> r1_tarski(C, D)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_wellord2)).
% 1.82/1.22  tff(f_47, axiom, (![A]: (v1_relat_1(A) => (v1_relat_2(A) <=> r1_relat_2(A, k3_relat_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d9_relat_2)).
% 1.82/1.22  tff(f_67, negated_conjecture, ~(![A]: v1_relat_2(k1_wellord2(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_wellord2)).
% 1.82/1.22  tff(c_36, plain, (![A_22]: (v1_relat_1(k1_wellord2(A_22)))), inference(cnfTransformation, [status(thm)], [f_64])).
% 1.82/1.22  tff(c_12, plain, (![A_3, B_9]: (r2_hidden('#skF_1'(A_3, B_9), B_9) | r1_relat_2(A_3, B_9) | ~v1_relat_1(A_3))), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.82/1.22  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.82/1.22  tff(c_32, plain, (![C_20, D_21, A_14]: (r2_hidden(k4_tarski(C_20, D_21), k1_wellord2(A_14)) | ~r1_tarski(C_20, D_21) | ~r2_hidden(D_21, A_14) | ~r2_hidden(C_20, A_14) | ~v1_relat_1(k1_wellord2(A_14)))), inference(cnfTransformation, [status(thm)], [f_62])).
% 1.82/1.22  tff(c_120, plain, (![C_41, D_42, A_43]: (r2_hidden(k4_tarski(C_41, D_42), k1_wellord2(A_43)) | ~r1_tarski(C_41, D_42) | ~r2_hidden(D_42, A_43) | ~r2_hidden(C_41, A_43))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_32])).
% 1.82/1.22  tff(c_10, plain, (![A_3, B_9]: (~r2_hidden(k4_tarski('#skF_1'(A_3, B_9), '#skF_1'(A_3, B_9)), A_3) | r1_relat_2(A_3, B_9) | ~v1_relat_1(A_3))), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.82/1.22  tff(c_124, plain, (![A_43, B_9]: (r1_relat_2(k1_wellord2(A_43), B_9) | ~v1_relat_1(k1_wellord2(A_43)) | ~r1_tarski('#skF_1'(k1_wellord2(A_43), B_9), '#skF_1'(k1_wellord2(A_43), B_9)) | ~r2_hidden('#skF_1'(k1_wellord2(A_43), B_9), A_43))), inference(resolution, [status(thm)], [c_120, c_10])).
% 1.82/1.22  tff(c_136, plain, (![A_47, B_48]: (r1_relat_2(k1_wellord2(A_47), B_48) | ~r2_hidden('#skF_1'(k1_wellord2(A_47), B_48), A_47))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_36, c_124])).
% 1.82/1.22  tff(c_140, plain, (![B_9]: (r1_relat_2(k1_wellord2(B_9), B_9) | ~v1_relat_1(k1_wellord2(B_9)))), inference(resolution, [status(thm)], [c_12, c_136])).
% 1.82/1.22  tff(c_143, plain, (![B_9]: (r1_relat_2(k1_wellord2(B_9), B_9))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_140])).
% 1.82/1.22  tff(c_30, plain, (![A_14]: (k3_relat_1(k1_wellord2(A_14))=A_14 | ~v1_relat_1(k1_wellord2(A_14)))), inference(cnfTransformation, [status(thm)], [f_62])).
% 1.82/1.22  tff(c_44, plain, (![A_14]: (k3_relat_1(k1_wellord2(A_14))=A_14)), inference(demodulation, [status(thm), theory('equality')], [c_36, c_30])).
% 1.82/1.22  tff(c_71, plain, (![A_30]: (v1_relat_2(A_30) | ~r1_relat_2(A_30, k3_relat_1(A_30)) | ~v1_relat_1(A_30))), inference(cnfTransformation, [status(thm)], [f_47])).
% 1.82/1.22  tff(c_77, plain, (![A_14]: (v1_relat_2(k1_wellord2(A_14)) | ~r1_relat_2(k1_wellord2(A_14), A_14) | ~v1_relat_1(k1_wellord2(A_14)))), inference(superposition, [status(thm), theory('equality')], [c_44, c_71])).
% 1.82/1.22  tff(c_80, plain, (![A_14]: (v1_relat_2(k1_wellord2(A_14)) | ~r1_relat_2(k1_wellord2(A_14), A_14))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_77])).
% 1.82/1.22  tff(c_145, plain, (![A_14]: (v1_relat_2(k1_wellord2(A_14)))), inference(demodulation, [status(thm), theory('equality')], [c_143, c_80])).
% 1.82/1.22  tff(c_38, plain, (~v1_relat_2(k1_wellord2('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_67])).
% 1.82/1.22  tff(c_150, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_145, c_38])).
% 1.82/1.22  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.82/1.22  
% 1.82/1.22  Inference rules
% 1.82/1.22  ----------------------
% 1.82/1.22  #Ref     : 0
% 1.82/1.22  #Sup     : 18
% 1.82/1.22  #Fact    : 0
% 1.82/1.22  #Define  : 0
% 1.82/1.22  #Split   : 0
% 1.82/1.22  #Chain   : 0
% 1.82/1.22  #Close   : 0
% 1.82/1.22  
% 1.82/1.22  Ordering : KBO
% 1.82/1.22  
% 1.82/1.22  Simplification rules
% 1.82/1.22  ----------------------
% 1.82/1.22  #Subsume      : 0
% 1.82/1.22  #Demod        : 25
% 1.82/1.22  #Tautology    : 14
% 1.82/1.22  #SimpNegUnit  : 0
% 1.82/1.22  #BackRed      : 2
% 1.82/1.22  
% 1.82/1.22  #Partial instantiations: 0
% 1.82/1.22  #Strategies tried      : 1
% 1.82/1.22  
% 1.82/1.22  Timing (in seconds)
% 1.82/1.22  ----------------------
% 1.82/1.22  Preprocessing        : 0.27
% 1.82/1.22  Parsing              : 0.14
% 1.82/1.22  CNF conversion       : 0.02
% 1.82/1.22  Main loop            : 0.14
% 1.82/1.22  Inferencing          : 0.05
% 1.82/1.22  Reduction            : 0.04
% 1.82/1.22  Demodulation         : 0.03
% 1.82/1.22  BG Simplification    : 0.02
% 1.82/1.22  Subsumption          : 0.03
% 1.82/1.22  Abstraction          : 0.01
% 1.82/1.22  MUC search           : 0.00
% 1.82/1.22  Cooper               : 0.00
% 1.82/1.22  Total                : 0.44
% 1.82/1.22  Index Insertion      : 0.00
% 1.82/1.22  Index Deletion       : 0.00
% 1.82/1.22  Index Matching       : 0.00
% 1.82/1.22  BG Taut test         : 0.00
%------------------------------------------------------------------------------
