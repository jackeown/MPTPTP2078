%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:04:52 EST 2020

% Result     : Theorem 1.77s
% Output     : CNFRefutation 1.77s
% Verified   : 
% Statistics : Number of formulae       :   33 (  39 expanded)
%              Number of leaves         :   19 (  23 expanded)
%              Depth                    :    5
%              Number of atoms          :   41 (  55 expanded)
%              Number of equality atoms :   15 (  19 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > v1_funct_1 > k9_relat_1 > k3_xboole_0 > k10_relat_1 > #nlpp > k2_relat_1 > k1_relat_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_52,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_relat_1(B)
          & v1_funct_1(B) )
       => k9_relat_1(B,k10_relat_1(B,A)) = k3_xboole_0(A,k9_relat_1(B,k1_relat_1(B))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_funct_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_37,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k10_relat_1(B,A) = k10_relat_1(B,k3_xboole_0(k2_relat_1(B),A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t168_relat_1)).

tff(f_29,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r1_tarski(A,k2_relat_1(B))
       => k9_relat_1(B,k10_relat_1(B,A)) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t147_funct_1)).

tff(f_33,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k9_relat_1(A,k1_relat_1(A)) = k2_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_relat_1)).

tff(c_16,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_14,plain,(
    v1_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_8,plain,(
    ! [B_7,A_6] :
      ( k10_relat_1(B_7,k3_xboole_0(k2_relat_1(B_7),A_6)) = k10_relat_1(B_7,A_6)
      | ~ v1_relat_1(B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_4,plain,(
    ! [A_3,B_4] : r1_tarski(k3_xboole_0(A_3,B_4),A_3) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_125,plain,(
    ! [B_21,A_22] :
      ( k9_relat_1(B_21,k10_relat_1(B_21,A_22)) = A_22
      | ~ r1_tarski(A_22,k2_relat_1(B_21))
      | ~ v1_funct_1(B_21)
      | ~ v1_relat_1(B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_134,plain,(
    ! [B_23,B_24] :
      ( k9_relat_1(B_23,k10_relat_1(B_23,k3_xboole_0(k2_relat_1(B_23),B_24))) = k3_xboole_0(k2_relat_1(B_23),B_24)
      | ~ v1_funct_1(B_23)
      | ~ v1_relat_1(B_23) ) ),
    inference(resolution,[status(thm)],[c_4,c_125])).

tff(c_158,plain,(
    ! [B_25,A_26] :
      ( k9_relat_1(B_25,k10_relat_1(B_25,A_26)) = k3_xboole_0(k2_relat_1(B_25),A_26)
      | ~ v1_funct_1(B_25)
      | ~ v1_relat_1(B_25)
      | ~ v1_relat_1(B_25) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_134])).

tff(c_6,plain,(
    ! [A_5] :
      ( k9_relat_1(A_5,k1_relat_1(A_5)) = k2_relat_1(A_5)
      | ~ v1_relat_1(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_12,plain,(
    k3_xboole_0('#skF_1',k9_relat_1('#skF_2',k1_relat_1('#skF_2'))) != k9_relat_1('#skF_2',k10_relat_1('#skF_2','#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_95,plain,
    ( k9_relat_1('#skF_2',k10_relat_1('#skF_2','#skF_1')) != k3_xboole_0('#skF_1',k2_relat_1('#skF_2'))
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_12])).

tff(c_97,plain,(
    k9_relat_1('#skF_2',k10_relat_1('#skF_2','#skF_1')) != k3_xboole_0('#skF_1',k2_relat_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_95])).

tff(c_168,plain,
    ( k3_xboole_0(k2_relat_1('#skF_2'),'#skF_1') != k3_xboole_0('#skF_1',k2_relat_1('#skF_2'))
    | ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_158,c_97])).

tff(c_184,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_16,c_14,c_2,c_168])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:38:08 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.77/1.23  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.77/1.23  
% 1.77/1.23  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.77/1.23  %$ r1_tarski > v1_relat_1 > v1_funct_1 > k9_relat_1 > k3_xboole_0 > k10_relat_1 > #nlpp > k2_relat_1 > k1_relat_1 > #skF_2 > #skF_1
% 1.77/1.23  
% 1.77/1.23  %Foreground sorts:
% 1.77/1.23  
% 1.77/1.23  
% 1.77/1.23  %Background operators:
% 1.77/1.23  
% 1.77/1.23  
% 1.77/1.23  %Foreground operators:
% 1.77/1.23  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 1.77/1.23  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.77/1.23  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.77/1.23  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.77/1.23  tff('#skF_2', type, '#skF_2': $i).
% 1.77/1.23  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 1.77/1.23  tff('#skF_1', type, '#skF_1': $i).
% 1.77/1.23  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.77/1.23  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 1.77/1.23  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.77/1.23  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.77/1.23  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.77/1.23  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.77/1.23  
% 1.77/1.24  tff(f_52, negated_conjecture, ~(![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (k9_relat_1(B, k10_relat_1(B, A)) = k3_xboole_0(A, k9_relat_1(B, k1_relat_1(B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_funct_1)).
% 1.77/1.24  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 1.77/1.24  tff(f_37, axiom, (![A, B]: (v1_relat_1(B) => (k10_relat_1(B, A) = k10_relat_1(B, k3_xboole_0(k2_relat_1(B), A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t168_relat_1)).
% 1.77/1.24  tff(f_29, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 1.77/1.24  tff(f_45, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r1_tarski(A, k2_relat_1(B)) => (k9_relat_1(B, k10_relat_1(B, A)) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t147_funct_1)).
% 1.77/1.24  tff(f_33, axiom, (![A]: (v1_relat_1(A) => (k9_relat_1(A, k1_relat_1(A)) = k2_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t146_relat_1)).
% 1.77/1.24  tff(c_16, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_52])).
% 1.77/1.24  tff(c_14, plain, (v1_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_52])).
% 1.77/1.24  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.77/1.24  tff(c_8, plain, (![B_7, A_6]: (k10_relat_1(B_7, k3_xboole_0(k2_relat_1(B_7), A_6))=k10_relat_1(B_7, A_6) | ~v1_relat_1(B_7))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.77/1.24  tff(c_4, plain, (![A_3, B_4]: (r1_tarski(k3_xboole_0(A_3, B_4), A_3))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.77/1.24  tff(c_125, plain, (![B_21, A_22]: (k9_relat_1(B_21, k10_relat_1(B_21, A_22))=A_22 | ~r1_tarski(A_22, k2_relat_1(B_21)) | ~v1_funct_1(B_21) | ~v1_relat_1(B_21))), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.77/1.24  tff(c_134, plain, (![B_23, B_24]: (k9_relat_1(B_23, k10_relat_1(B_23, k3_xboole_0(k2_relat_1(B_23), B_24)))=k3_xboole_0(k2_relat_1(B_23), B_24) | ~v1_funct_1(B_23) | ~v1_relat_1(B_23))), inference(resolution, [status(thm)], [c_4, c_125])).
% 1.77/1.24  tff(c_158, plain, (![B_25, A_26]: (k9_relat_1(B_25, k10_relat_1(B_25, A_26))=k3_xboole_0(k2_relat_1(B_25), A_26) | ~v1_funct_1(B_25) | ~v1_relat_1(B_25) | ~v1_relat_1(B_25))), inference(superposition, [status(thm), theory('equality')], [c_8, c_134])).
% 1.77/1.24  tff(c_6, plain, (![A_5]: (k9_relat_1(A_5, k1_relat_1(A_5))=k2_relat_1(A_5) | ~v1_relat_1(A_5))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.77/1.24  tff(c_12, plain, (k3_xboole_0('#skF_1', k9_relat_1('#skF_2', k1_relat_1('#skF_2')))!=k9_relat_1('#skF_2', k10_relat_1('#skF_2', '#skF_1'))), inference(cnfTransformation, [status(thm)], [f_52])).
% 1.77/1.24  tff(c_95, plain, (k9_relat_1('#skF_2', k10_relat_1('#skF_2', '#skF_1'))!=k3_xboole_0('#skF_1', k2_relat_1('#skF_2')) | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_6, c_12])).
% 1.77/1.24  tff(c_97, plain, (k9_relat_1('#skF_2', k10_relat_1('#skF_2', '#skF_1'))!=k3_xboole_0('#skF_1', k2_relat_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_95])).
% 1.77/1.24  tff(c_168, plain, (k3_xboole_0(k2_relat_1('#skF_2'), '#skF_1')!=k3_xboole_0('#skF_1', k2_relat_1('#skF_2')) | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_158, c_97])).
% 1.77/1.24  tff(c_184, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_16, c_16, c_14, c_2, c_168])).
% 1.77/1.24  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.77/1.24  
% 1.77/1.24  Inference rules
% 1.77/1.24  ----------------------
% 1.77/1.24  #Ref     : 0
% 1.77/1.24  #Sup     : 40
% 1.77/1.24  #Fact    : 0
% 1.77/1.24  #Define  : 0
% 1.77/1.24  #Split   : 0
% 1.77/1.24  #Chain   : 0
% 1.77/1.24  #Close   : 0
% 1.77/1.24  
% 1.77/1.24  Ordering : KBO
% 1.77/1.24  
% 1.77/1.24  Simplification rules
% 1.77/1.24  ----------------------
% 1.77/1.24  #Subsume      : 3
% 1.77/1.24  #Demod        : 8
% 1.77/1.24  #Tautology    : 22
% 1.77/1.24  #SimpNegUnit  : 0
% 1.77/1.24  #BackRed      : 0
% 1.77/1.24  
% 1.77/1.24  #Partial instantiations: 0
% 1.77/1.24  #Strategies tried      : 1
% 1.77/1.24  
% 1.77/1.24  Timing (in seconds)
% 1.77/1.24  ----------------------
% 1.77/1.24  Preprocessing        : 0.26
% 1.77/1.24  Parsing              : 0.15
% 1.77/1.24  CNF conversion       : 0.01
% 1.77/1.24  Main loop            : 0.14
% 1.77/1.24  Inferencing          : 0.06
% 1.77/1.24  Reduction            : 0.04
% 1.77/1.24  Demodulation         : 0.03
% 1.77/1.24  BG Simplification    : 0.01
% 1.77/1.24  Subsumption          : 0.02
% 1.77/1.24  Abstraction          : 0.01
% 1.77/1.24  MUC search           : 0.00
% 1.77/1.24  Cooper               : 0.00
% 1.77/1.25  Total                : 0.43
% 1.77/1.25  Index Insertion      : 0.00
% 1.77/1.25  Index Deletion       : 0.00
% 1.77/1.25  Index Matching       : 0.00
% 1.77/1.25  BG Taut test         : 0.00
%------------------------------------------------------------------------------
