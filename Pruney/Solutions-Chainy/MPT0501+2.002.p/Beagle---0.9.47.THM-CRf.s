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
% DateTime   : Thu Dec  3 09:59:48 EST 2020

% Result     : Theorem 1.65s
% Output     : CNFRefutation 1.65s
% Verified   : 
% Statistics : Number of formulae       :   36 (  50 expanded)
%              Number of leaves         :   17 (  24 expanded)
%              Depth                    :    6
%              Number of atoms          :   47 (  77 expanded)
%              Number of equality atoms :    6 (   6 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k7_relat_1 > k3_xboole_0 > #nlpp > k2_relat_1 > k1_relat_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

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

tff(f_55,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => r1_tarski(k2_relat_1(k7_relat_1(B,A)),k2_relat_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t99_relat_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k7_relat_1(B,A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_relat_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k3_xboole_0(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_relat_1)).

tff(f_46,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(A,B)
           => ( r1_tarski(k1_relat_1(A),k1_relat_1(B))
              & r1_tarski(k2_relat_1(A),k2_relat_1(B)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_relat_1)).

tff(c_16,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_12,plain,(
    ! [B_11,A_10] :
      ( r1_tarski(k7_relat_1(B_11,A_10),B_11)
      | ~ v1_relat_1(B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_65,plain,(
    ! [B_20,A_21] :
      ( r1_tarski(k7_relat_1(B_20,A_21),B_20)
      | ~ v1_relat_1(B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_4,plain,(
    ! [A_3,B_4] :
      ( k3_xboole_0(A_3,B_4) = A_3
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_68,plain,(
    ! [B_20,A_21] :
      ( k3_xboole_0(k7_relat_1(B_20,A_21),B_20) = k7_relat_1(B_20,A_21)
      | ~ v1_relat_1(B_20) ) ),
    inference(resolution,[status(thm)],[c_65,c_4])).

tff(c_71,plain,(
    ! [B_22,A_23] :
      ( k3_xboole_0(B_22,k7_relat_1(B_22,A_23)) = k7_relat_1(B_22,A_23)
      | ~ v1_relat_1(B_22) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_68])).

tff(c_6,plain,(
    ! [A_5,B_6] :
      ( v1_relat_1(k3_xboole_0(A_5,B_6))
      | ~ v1_relat_1(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_80,plain,(
    ! [B_22,A_23] :
      ( v1_relat_1(k7_relat_1(B_22,A_23))
      | ~ v1_relat_1(B_22)
      | ~ v1_relat_1(B_22) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_71,c_6])).

tff(c_86,plain,(
    ! [A_24,B_25] :
      ( r1_tarski(k2_relat_1(A_24),k2_relat_1(B_25))
      | ~ r1_tarski(A_24,B_25)
      | ~ v1_relat_1(B_25)
      | ~ v1_relat_1(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_14,plain,(
    ~ r1_tarski(k2_relat_1(k7_relat_1('#skF_2','#skF_1')),k2_relat_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_89,plain,
    ( ~ r1_tarski(k7_relat_1('#skF_2','#skF_1'),'#skF_2')
    | ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1')) ),
    inference(resolution,[status(thm)],[c_86,c_14])).

tff(c_95,plain,
    ( ~ r1_tarski(k7_relat_1('#skF_2','#skF_1'),'#skF_2')
    | ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_89])).

tff(c_98,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_95])).

tff(c_101,plain,(
    ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_80,c_98])).

tff(c_105,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_101])).

tff(c_106,plain,(
    ~ r1_tarski(k7_relat_1('#skF_2','#skF_1'),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_95])).

tff(c_110,plain,(
    ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_12,c_106])).

tff(c_114,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_110])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:01:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.65/1.13  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.65/1.13  
% 1.65/1.13  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.65/1.13  %$ r1_tarski > v1_relat_1 > k7_relat_1 > k3_xboole_0 > #nlpp > k2_relat_1 > k1_relat_1 > #skF_2 > #skF_1
% 1.65/1.13  
% 1.65/1.13  %Foreground sorts:
% 1.65/1.13  
% 1.65/1.13  
% 1.65/1.13  %Background operators:
% 1.65/1.13  
% 1.65/1.13  
% 1.65/1.13  %Foreground operators:
% 1.65/1.13  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.65/1.13  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 1.65/1.13  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.65/1.13  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.65/1.13  tff('#skF_2', type, '#skF_2': $i).
% 1.65/1.13  tff('#skF_1', type, '#skF_1': $i).
% 1.65/1.13  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.65/1.13  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.65/1.13  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.65/1.13  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.65/1.13  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.65/1.13  
% 1.65/1.14  tff(f_55, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => r1_tarski(k2_relat_1(k7_relat_1(B, A)), k2_relat_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t99_relat_1)).
% 1.65/1.14  tff(f_50, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k7_relat_1(B, A), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t88_relat_1)).
% 1.65/1.14  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 1.65/1.14  tff(f_31, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 1.65/1.14  tff(f_35, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_relat_1)).
% 1.65/1.14  tff(f_46, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(A, B) => (r1_tarski(k1_relat_1(A), k1_relat_1(B)) & r1_tarski(k2_relat_1(A), k2_relat_1(B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t25_relat_1)).
% 1.65/1.14  tff(c_16, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_55])).
% 1.65/1.14  tff(c_12, plain, (![B_11, A_10]: (r1_tarski(k7_relat_1(B_11, A_10), B_11) | ~v1_relat_1(B_11))), inference(cnfTransformation, [status(thm)], [f_50])).
% 1.65/1.14  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.65/1.14  tff(c_65, plain, (![B_20, A_21]: (r1_tarski(k7_relat_1(B_20, A_21), B_20) | ~v1_relat_1(B_20))), inference(cnfTransformation, [status(thm)], [f_50])).
% 1.65/1.14  tff(c_4, plain, (![A_3, B_4]: (k3_xboole_0(A_3, B_4)=A_3 | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.65/1.14  tff(c_68, plain, (![B_20, A_21]: (k3_xboole_0(k7_relat_1(B_20, A_21), B_20)=k7_relat_1(B_20, A_21) | ~v1_relat_1(B_20))), inference(resolution, [status(thm)], [c_65, c_4])).
% 1.65/1.14  tff(c_71, plain, (![B_22, A_23]: (k3_xboole_0(B_22, k7_relat_1(B_22, A_23))=k7_relat_1(B_22, A_23) | ~v1_relat_1(B_22))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_68])).
% 1.65/1.14  tff(c_6, plain, (![A_5, B_6]: (v1_relat_1(k3_xboole_0(A_5, B_6)) | ~v1_relat_1(A_5))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.65/1.14  tff(c_80, plain, (![B_22, A_23]: (v1_relat_1(k7_relat_1(B_22, A_23)) | ~v1_relat_1(B_22) | ~v1_relat_1(B_22))), inference(superposition, [status(thm), theory('equality')], [c_71, c_6])).
% 1.65/1.14  tff(c_86, plain, (![A_24, B_25]: (r1_tarski(k2_relat_1(A_24), k2_relat_1(B_25)) | ~r1_tarski(A_24, B_25) | ~v1_relat_1(B_25) | ~v1_relat_1(A_24))), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.65/1.14  tff(c_14, plain, (~r1_tarski(k2_relat_1(k7_relat_1('#skF_2', '#skF_1')), k2_relat_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_55])).
% 1.65/1.14  tff(c_89, plain, (~r1_tarski(k7_relat_1('#skF_2', '#skF_1'), '#skF_2') | ~v1_relat_1('#skF_2') | ~v1_relat_1(k7_relat_1('#skF_2', '#skF_1'))), inference(resolution, [status(thm)], [c_86, c_14])).
% 1.65/1.14  tff(c_95, plain, (~r1_tarski(k7_relat_1('#skF_2', '#skF_1'), '#skF_2') | ~v1_relat_1(k7_relat_1('#skF_2', '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_89])).
% 1.65/1.14  tff(c_98, plain, (~v1_relat_1(k7_relat_1('#skF_2', '#skF_1'))), inference(splitLeft, [status(thm)], [c_95])).
% 1.65/1.14  tff(c_101, plain, (~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_80, c_98])).
% 1.65/1.14  tff(c_105, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_16, c_101])).
% 1.65/1.14  tff(c_106, plain, (~r1_tarski(k7_relat_1('#skF_2', '#skF_1'), '#skF_2')), inference(splitRight, [status(thm)], [c_95])).
% 1.65/1.14  tff(c_110, plain, (~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_12, c_106])).
% 1.65/1.14  tff(c_114, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_16, c_110])).
% 1.65/1.14  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.65/1.14  
% 1.65/1.14  Inference rules
% 1.65/1.14  ----------------------
% 1.65/1.14  #Ref     : 0
% 1.65/1.14  #Sup     : 21
% 1.65/1.14  #Fact    : 0
% 1.65/1.14  #Define  : 0
% 1.65/1.14  #Split   : 1
% 1.65/1.14  #Chain   : 0
% 1.65/1.14  #Close   : 0
% 1.65/1.14  
% 1.65/1.14  Ordering : KBO
% 1.65/1.14  
% 1.65/1.14  Simplification rules
% 1.65/1.14  ----------------------
% 1.65/1.14  #Subsume      : 3
% 1.65/1.14  #Demod        : 4
% 1.65/1.14  #Tautology    : 11
% 1.65/1.14  #SimpNegUnit  : 0
% 1.65/1.14  #BackRed      : 0
% 1.65/1.14  
% 1.65/1.14  #Partial instantiations: 0
% 1.65/1.14  #Strategies tried      : 1
% 1.65/1.14  
% 1.65/1.14  Timing (in seconds)
% 1.65/1.14  ----------------------
% 1.65/1.15  Preprocessing        : 0.25
% 1.65/1.15  Parsing              : 0.14
% 1.65/1.15  CNF conversion       : 0.02
% 1.65/1.15  Main loop            : 0.12
% 1.65/1.15  Inferencing          : 0.05
% 1.65/1.15  Reduction            : 0.03
% 1.65/1.15  Demodulation         : 0.03
% 1.65/1.15  BG Simplification    : 0.01
% 1.65/1.15  Subsumption          : 0.02
% 1.65/1.15  Abstraction          : 0.01
% 1.65/1.15  MUC search           : 0.00
% 1.65/1.15  Cooper               : 0.00
% 1.65/1.15  Total                : 0.40
% 1.65/1.15  Index Insertion      : 0.00
% 1.65/1.15  Index Deletion       : 0.00
% 1.65/1.15  Index Matching       : 0.00
% 1.65/1.15  BG Taut test         : 0.00
%------------------------------------------------------------------------------
