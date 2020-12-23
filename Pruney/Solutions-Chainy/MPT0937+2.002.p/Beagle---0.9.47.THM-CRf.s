%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:10:30 EST 2020

% Result     : Theorem 1.86s
% Output     : CNFRefutation 1.86s
% Verified   : 
% Statistics : Number of formulae       :   34 (  42 expanded)
%              Number of leaves         :   19 (  24 expanded)
%              Depth                    :    6
%              Number of atoms          :   50 (  67 expanded)
%              Number of equality atoms :    5 (   7 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_relat_2 > v1_relat_1 > k4_tarski > #nlpp > k3_relat_1 > k1_wellord2 > #skF_1 > #skF_3 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(v1_relat_2,type,(
    v1_relat_2: $i > $o )).

tff(k3_relat_1,type,(
    k3_relat_1: $i > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff(f_57,axiom,(
    ! [A] : v1_relat_1(k1_wellord2(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_wellord2)).

tff(f_55,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( B = k1_wellord2(A)
      <=> ( k3_relat_1(B) = A
          & ! [C,D] :
              ( ( r2_hidden(C,A)
                & r2_hidden(D,A) )
             => ( r2_hidden(k4_tarski(C,D),B)
              <=> r1_tarski(C,D) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_wellord2)).

tff(f_40,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( v1_relat_2(A)
      <=> ! [B] :
            ( r2_hidden(B,k3_relat_1(A))
           => r2_hidden(k4_tarski(B,B),A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_wellord1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_60,negated_conjecture,(
    ~ ! [A] : v1_relat_2(k1_wellord2(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_wellord2)).

tff(c_32,plain,(
    ! [A_15] : v1_relat_1(k1_wellord2(A_15)) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_26,plain,(
    ! [A_7] :
      ( k3_relat_1(k1_wellord2(A_7)) = A_7
      | ~ v1_relat_1(k1_wellord2(A_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_40,plain,(
    ! [A_7] : k3_relat_1(k1_wellord2(A_7)) = A_7 ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_26])).

tff(c_60,plain,(
    ! [A_21] :
      ( r2_hidden('#skF_1'(A_21),k3_relat_1(A_21))
      | v1_relat_2(A_21)
      | ~ v1_relat_1(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_63,plain,(
    ! [A_7] :
      ( r2_hidden('#skF_1'(k1_wellord2(A_7)),A_7)
      | v1_relat_2(k1_wellord2(A_7))
      | ~ v1_relat_1(k1_wellord2(A_7)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_60])).

tff(c_65,plain,(
    ! [A_7] :
      ( r2_hidden('#skF_1'(k1_wellord2(A_7)),A_7)
      | v1_relat_2(k1_wellord2(A_7)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_63])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_28,plain,(
    ! [C_13,D_14,A_7] :
      ( r2_hidden(k4_tarski(C_13,D_14),k1_wellord2(A_7))
      | ~ r1_tarski(C_13,D_14)
      | ~ r2_hidden(D_14,A_7)
      | ~ r2_hidden(C_13,A_7)
      | ~ v1_relat_1(k1_wellord2(A_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_104,plain,(
    ! [C_31,D_32,A_33] :
      ( r2_hidden(k4_tarski(C_31,D_32),k1_wellord2(A_33))
      | ~ r1_tarski(C_31,D_32)
      | ~ r2_hidden(D_32,A_33)
      | ~ r2_hidden(C_31,A_33) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_28])).

tff(c_10,plain,(
    ! [A_3] :
      ( ~ r2_hidden(k4_tarski('#skF_1'(A_3),'#skF_1'(A_3)),A_3)
      | v1_relat_2(A_3)
      | ~ v1_relat_1(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_111,plain,(
    ! [A_33] :
      ( v1_relat_2(k1_wellord2(A_33))
      | ~ v1_relat_1(k1_wellord2(A_33))
      | ~ r1_tarski('#skF_1'(k1_wellord2(A_33)),'#skF_1'(k1_wellord2(A_33)))
      | ~ r2_hidden('#skF_1'(k1_wellord2(A_33)),A_33) ) ),
    inference(resolution,[status(thm)],[c_104,c_10])).

tff(c_116,plain,(
    ! [A_34] :
      ( v1_relat_2(k1_wellord2(A_34))
      | ~ r2_hidden('#skF_1'(k1_wellord2(A_34)),A_34) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_32,c_111])).

tff(c_120,plain,(
    ! [A_7] : v1_relat_2(k1_wellord2(A_7)) ),
    inference(resolution,[status(thm)],[c_65,c_116])).

tff(c_34,plain,(
    ~ v1_relat_2(k1_wellord2('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_125,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_120,c_34])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n021.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 11:23:49 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.86/1.20  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.86/1.20  
% 1.86/1.20  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.86/1.21  %$ r2_hidden > r1_tarski > v1_relat_2 > v1_relat_1 > k4_tarski > #nlpp > k3_relat_1 > k1_wellord2 > #skF_1 > #skF_3 > #skF_4 > #skF_2
% 1.86/1.21  
% 1.86/1.21  %Foreground sorts:
% 1.86/1.21  
% 1.86/1.21  
% 1.86/1.21  %Background operators:
% 1.86/1.21  
% 1.86/1.21  
% 1.86/1.21  %Foreground operators:
% 1.86/1.21  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.86/1.21  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.86/1.21  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 1.86/1.21  tff('#skF_1', type, '#skF_1': $i > $i).
% 1.86/1.21  tff(v1_relat_2, type, v1_relat_2: $i > $o).
% 1.86/1.21  tff(k3_relat_1, type, k3_relat_1: $i > $i).
% 1.86/1.21  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 1.86/1.21  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.86/1.21  tff(k1_wellord2, type, k1_wellord2: $i > $i).
% 1.86/1.21  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.86/1.21  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.86/1.21  tff('#skF_4', type, '#skF_4': $i).
% 1.86/1.21  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.86/1.21  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 1.86/1.21  
% 1.86/1.22  tff(f_57, axiom, (![A]: v1_relat_1(k1_wellord2(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_wellord2)).
% 1.86/1.22  tff(f_55, axiom, (![A, B]: (v1_relat_1(B) => ((B = k1_wellord2(A)) <=> ((k3_relat_1(B) = A) & (![C, D]: ((r2_hidden(C, A) & r2_hidden(D, A)) => (r2_hidden(k4_tarski(C, D), B) <=> r1_tarski(C, D)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_wellord2)).
% 1.86/1.22  tff(f_40, axiom, (![A]: (v1_relat_1(A) => (v1_relat_2(A) <=> (![B]: (r2_hidden(B, k3_relat_1(A)) => r2_hidden(k4_tarski(B, B), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l1_wellord1)).
% 1.86/1.22  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 1.86/1.22  tff(f_60, negated_conjecture, ~(![A]: v1_relat_2(k1_wellord2(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_wellord2)).
% 1.86/1.22  tff(c_32, plain, (![A_15]: (v1_relat_1(k1_wellord2(A_15)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 1.86/1.22  tff(c_26, plain, (![A_7]: (k3_relat_1(k1_wellord2(A_7))=A_7 | ~v1_relat_1(k1_wellord2(A_7)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 1.86/1.22  tff(c_40, plain, (![A_7]: (k3_relat_1(k1_wellord2(A_7))=A_7)), inference(demodulation, [status(thm), theory('equality')], [c_32, c_26])).
% 1.86/1.22  tff(c_60, plain, (![A_21]: (r2_hidden('#skF_1'(A_21), k3_relat_1(A_21)) | v1_relat_2(A_21) | ~v1_relat_1(A_21))), inference(cnfTransformation, [status(thm)], [f_40])).
% 1.86/1.22  tff(c_63, plain, (![A_7]: (r2_hidden('#skF_1'(k1_wellord2(A_7)), A_7) | v1_relat_2(k1_wellord2(A_7)) | ~v1_relat_1(k1_wellord2(A_7)))), inference(superposition, [status(thm), theory('equality')], [c_40, c_60])).
% 1.86/1.22  tff(c_65, plain, (![A_7]: (r2_hidden('#skF_1'(k1_wellord2(A_7)), A_7) | v1_relat_2(k1_wellord2(A_7)))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_63])).
% 1.86/1.22  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.86/1.22  tff(c_28, plain, (![C_13, D_14, A_7]: (r2_hidden(k4_tarski(C_13, D_14), k1_wellord2(A_7)) | ~r1_tarski(C_13, D_14) | ~r2_hidden(D_14, A_7) | ~r2_hidden(C_13, A_7) | ~v1_relat_1(k1_wellord2(A_7)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 1.86/1.22  tff(c_104, plain, (![C_31, D_32, A_33]: (r2_hidden(k4_tarski(C_31, D_32), k1_wellord2(A_33)) | ~r1_tarski(C_31, D_32) | ~r2_hidden(D_32, A_33) | ~r2_hidden(C_31, A_33))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_28])).
% 1.86/1.22  tff(c_10, plain, (![A_3]: (~r2_hidden(k4_tarski('#skF_1'(A_3), '#skF_1'(A_3)), A_3) | v1_relat_2(A_3) | ~v1_relat_1(A_3))), inference(cnfTransformation, [status(thm)], [f_40])).
% 1.86/1.22  tff(c_111, plain, (![A_33]: (v1_relat_2(k1_wellord2(A_33)) | ~v1_relat_1(k1_wellord2(A_33)) | ~r1_tarski('#skF_1'(k1_wellord2(A_33)), '#skF_1'(k1_wellord2(A_33))) | ~r2_hidden('#skF_1'(k1_wellord2(A_33)), A_33))), inference(resolution, [status(thm)], [c_104, c_10])).
% 1.86/1.22  tff(c_116, plain, (![A_34]: (v1_relat_2(k1_wellord2(A_34)) | ~r2_hidden('#skF_1'(k1_wellord2(A_34)), A_34))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_32, c_111])).
% 1.86/1.22  tff(c_120, plain, (![A_7]: (v1_relat_2(k1_wellord2(A_7)))), inference(resolution, [status(thm)], [c_65, c_116])).
% 1.86/1.22  tff(c_34, plain, (~v1_relat_2(k1_wellord2('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_60])).
% 1.86/1.22  tff(c_125, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_120, c_34])).
% 1.86/1.22  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.86/1.22  
% 1.86/1.22  Inference rules
% 1.86/1.22  ----------------------
% 1.86/1.22  #Ref     : 0
% 1.86/1.22  #Sup     : 13
% 1.86/1.22  #Fact    : 0
% 1.86/1.22  #Define  : 0
% 1.86/1.22  #Split   : 0
% 1.86/1.22  #Chain   : 0
% 1.86/1.22  #Close   : 0
% 1.86/1.22  
% 1.86/1.22  Ordering : KBO
% 1.86/1.22  
% 1.86/1.22  Simplification rules
% 1.86/1.22  ----------------------
% 1.86/1.22  #Subsume      : 0
% 1.86/1.22  #Demod        : 26
% 1.86/1.22  #Tautology    : 15
% 1.86/1.22  #SimpNegUnit  : 0
% 1.86/1.22  #BackRed      : 1
% 1.86/1.22  
% 1.86/1.22  #Partial instantiations: 0
% 1.86/1.22  #Strategies tried      : 1
% 1.86/1.22  
% 1.86/1.22  Timing (in seconds)
% 1.86/1.22  ----------------------
% 1.95/1.23  Preprocessing        : 0.31
% 1.95/1.23  Parsing              : 0.16
% 1.95/1.23  CNF conversion       : 0.02
% 1.95/1.23  Main loop            : 0.12
% 1.95/1.23  Inferencing          : 0.05
% 1.95/1.23  Reduction            : 0.04
% 1.95/1.23  Demodulation         : 0.03
% 1.95/1.23  BG Simplification    : 0.02
% 1.95/1.23  Subsumption          : 0.02
% 1.95/1.23  Abstraction          : 0.01
% 1.95/1.23  MUC search           : 0.00
% 1.95/1.23  Cooper               : 0.00
% 1.95/1.23  Total                : 0.46
% 1.95/1.23  Index Insertion      : 0.00
% 1.95/1.23  Index Deletion       : 0.00
% 1.95/1.23  Index Matching       : 0.00
% 1.95/1.23  BG Taut test         : 0.00
%------------------------------------------------------------------------------
