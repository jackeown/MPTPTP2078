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
% DateTime   : Thu Dec  3 10:06:34 EST 2020

% Result     : Theorem 1.90s
% Output     : CNFRefutation 1.90s
% Verified   : 
% Statistics : Number of formulae       :   33 (  35 expanded)
%              Number of leaves         :   20 (  22 expanded)
%              Depth                    :    7
%              Number of atoms          :   41 (  47 expanded)
%              Number of equality atoms :    7 (   9 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_relat_1 > k4_tarski > k1_wellord1 > #nlpp > k3_relat_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_4 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_relat_1,type,(
    k3_relat_1: $i > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff(k1_wellord1,type,(
    k1_wellord1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_64,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ( r2_hidden(A,k3_relat_1(B))
          | k1_wellord1(B,A) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_wellord1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_57,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B,C] :
          ( C = k1_wellord1(A,B)
        <=> ! [D] :
              ( r2_hidden(D,C)
            <=> ( D != B
                & r2_hidden(k4_tarski(D,B),A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_wellord1)).

tff(f_44,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(k4_tarski(A,B),C)
       => ( r2_hidden(A,k3_relat_1(C))
          & r2_hidden(B,k3_relat_1(C)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_relat_1)).

tff(f_36,axiom,(
    ! [A] :
      ( r1_tarski(A,k1_xboole_0)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).

tff(c_32,plain,(
    k1_wellord1('#skF_5','#skF_4') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_36,plain,(
    v1_relat_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_73,plain,(
    ! [D_42,B_43,A_44] :
      ( r2_hidden(k4_tarski(D_42,B_43),A_44)
      | ~ r2_hidden(D_42,k1_wellord1(A_44,B_43))
      | ~ v1_relat_1(A_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_10,plain,(
    ! [B_8,C_9,A_7] :
      ( r2_hidden(B_8,k3_relat_1(C_9))
      | ~ r2_hidden(k4_tarski(A_7,B_8),C_9)
      | ~ v1_relat_1(C_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_106,plain,(
    ! [B_48,A_49,D_50] :
      ( r2_hidden(B_48,k3_relat_1(A_49))
      | ~ r2_hidden(D_50,k1_wellord1(A_49,B_48))
      | ~ v1_relat_1(A_49) ) ),
    inference(resolution,[status(thm)],[c_73,c_10])).

tff(c_124,plain,(
    ! [B_54,A_55,B_56] :
      ( r2_hidden(B_54,k3_relat_1(A_55))
      | ~ v1_relat_1(A_55)
      | r1_tarski(k1_wellord1(A_55,B_54),B_56) ) ),
    inference(resolution,[status(thm)],[c_6,c_106])).

tff(c_34,plain,(
    ~ r2_hidden('#skF_4',k3_relat_1('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_145,plain,(
    ! [B_56] :
      ( ~ v1_relat_1('#skF_5')
      | r1_tarski(k1_wellord1('#skF_5','#skF_4'),B_56) ) ),
    inference(resolution,[status(thm)],[c_124,c_34])).

tff(c_156,plain,(
    ! [B_57] : r1_tarski(k1_wellord1('#skF_5','#skF_4'),B_57) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_145])).

tff(c_8,plain,(
    ! [A_6] :
      ( k1_xboole_0 = A_6
      | ~ r1_tarski(A_6,k1_xboole_0) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_160,plain,(
    k1_wellord1('#skF_5','#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_156,c_8])).

tff(c_164,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_160])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:37:34 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.90/1.17  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.90/1.17  
% 1.90/1.17  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.90/1.17  %$ r2_hidden > r1_tarski > v1_relat_1 > k4_tarski > k1_wellord1 > #nlpp > k3_relat_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_4 > #skF_3 > #skF_1
% 1.90/1.17  
% 1.90/1.17  %Foreground sorts:
% 1.90/1.17  
% 1.90/1.17  
% 1.90/1.17  %Background operators:
% 1.90/1.17  
% 1.90/1.17  
% 1.90/1.17  %Foreground operators:
% 1.90/1.17  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.90/1.17  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.90/1.17  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 1.90/1.17  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.90/1.17  tff(k3_relat_1, type, k3_relat_1: $i > $i).
% 1.90/1.17  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.90/1.17  tff('#skF_5', type, '#skF_5': $i).
% 1.90/1.17  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 1.90/1.17  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.90/1.17  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.90/1.17  tff('#skF_4', type, '#skF_4': $i).
% 1.90/1.17  tff(k1_wellord1, type, k1_wellord1: ($i * $i) > $i).
% 1.90/1.17  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 1.90/1.17  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.90/1.17  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.90/1.17  
% 1.90/1.18  tff(f_64, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => (r2_hidden(A, k3_relat_1(B)) | (k1_wellord1(B, A) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_wellord1)).
% 1.90/1.18  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 1.90/1.18  tff(f_57, axiom, (![A]: (v1_relat_1(A) => (![B, C]: ((C = k1_wellord1(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (~(D = B) & r2_hidden(k4_tarski(D, B), A)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_wellord1)).
% 1.90/1.18  tff(f_44, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(k4_tarski(A, B), C) => (r2_hidden(A, k3_relat_1(C)) & r2_hidden(B, k3_relat_1(C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t30_relat_1)).
% 1.90/1.18  tff(f_36, axiom, (![A]: (r1_tarski(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_1)).
% 1.90/1.18  tff(c_32, plain, (k1_wellord1('#skF_5', '#skF_4')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_64])).
% 1.90/1.18  tff(c_36, plain, (v1_relat_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_64])).
% 1.90/1.18  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.90/1.18  tff(c_73, plain, (![D_42, B_43, A_44]: (r2_hidden(k4_tarski(D_42, B_43), A_44) | ~r2_hidden(D_42, k1_wellord1(A_44, B_43)) | ~v1_relat_1(A_44))), inference(cnfTransformation, [status(thm)], [f_57])).
% 1.90/1.18  tff(c_10, plain, (![B_8, C_9, A_7]: (r2_hidden(B_8, k3_relat_1(C_9)) | ~r2_hidden(k4_tarski(A_7, B_8), C_9) | ~v1_relat_1(C_9))), inference(cnfTransformation, [status(thm)], [f_44])).
% 1.90/1.18  tff(c_106, plain, (![B_48, A_49, D_50]: (r2_hidden(B_48, k3_relat_1(A_49)) | ~r2_hidden(D_50, k1_wellord1(A_49, B_48)) | ~v1_relat_1(A_49))), inference(resolution, [status(thm)], [c_73, c_10])).
% 1.90/1.18  tff(c_124, plain, (![B_54, A_55, B_56]: (r2_hidden(B_54, k3_relat_1(A_55)) | ~v1_relat_1(A_55) | r1_tarski(k1_wellord1(A_55, B_54), B_56))), inference(resolution, [status(thm)], [c_6, c_106])).
% 1.90/1.18  tff(c_34, plain, (~r2_hidden('#skF_4', k3_relat_1('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_64])).
% 1.90/1.18  tff(c_145, plain, (![B_56]: (~v1_relat_1('#skF_5') | r1_tarski(k1_wellord1('#skF_5', '#skF_4'), B_56))), inference(resolution, [status(thm)], [c_124, c_34])).
% 1.90/1.18  tff(c_156, plain, (![B_57]: (r1_tarski(k1_wellord1('#skF_5', '#skF_4'), B_57))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_145])).
% 1.90/1.18  tff(c_8, plain, (![A_6]: (k1_xboole_0=A_6 | ~r1_tarski(A_6, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_36])).
% 1.90/1.18  tff(c_160, plain, (k1_wellord1('#skF_5', '#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_156, c_8])).
% 1.90/1.18  tff(c_164, plain, $false, inference(negUnitSimplification, [status(thm)], [c_32, c_160])).
% 1.90/1.18  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.90/1.18  
% 1.90/1.18  Inference rules
% 1.90/1.18  ----------------------
% 1.90/1.18  #Ref     : 0
% 1.90/1.18  #Sup     : 24
% 1.90/1.18  #Fact    : 0
% 1.90/1.18  #Define  : 0
% 1.90/1.18  #Split   : 0
% 1.90/1.18  #Chain   : 0
% 1.90/1.18  #Close   : 0
% 1.90/1.18  
% 1.90/1.18  Ordering : KBO
% 1.90/1.18  
% 1.90/1.18  Simplification rules
% 1.90/1.18  ----------------------
% 1.90/1.18  #Subsume      : 0
% 1.90/1.18  #Demod        : 1
% 1.90/1.18  #Tautology    : 3
% 1.90/1.18  #SimpNegUnit  : 1
% 1.90/1.18  #BackRed      : 0
% 1.90/1.18  
% 1.90/1.18  #Partial instantiations: 0
% 1.90/1.18  #Strategies tried      : 1
% 1.90/1.18  
% 1.90/1.18  Timing (in seconds)
% 1.90/1.18  ----------------------
% 1.90/1.18  Preprocessing        : 0.28
% 1.90/1.18  Parsing              : 0.15
% 1.90/1.19  CNF conversion       : 0.02
% 1.90/1.19  Main loop            : 0.15
% 1.90/1.19  Inferencing          : 0.06
% 1.90/1.19  Reduction            : 0.03
% 1.90/1.19  Demodulation         : 0.02
% 1.90/1.19  BG Simplification    : 0.01
% 1.90/1.19  Subsumption          : 0.04
% 1.90/1.19  Abstraction          : 0.01
% 1.90/1.19  MUC search           : 0.00
% 1.90/1.19  Cooper               : 0.00
% 1.90/1.19  Total                : 0.45
% 1.90/1.19  Index Insertion      : 0.00
% 1.90/1.19  Index Deletion       : 0.00
% 1.90/1.19  Index Matching       : 0.00
% 1.90/1.19  BG Taut test         : 0.00
%------------------------------------------------------------------------------
