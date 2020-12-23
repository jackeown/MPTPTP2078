%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:04:21 EST 2020

% Result     : Theorem 1.67s
% Output     : CNFRefutation 1.82s
% Verified   : 
% Statistics : Number of formulae       :   29 (  37 expanded)
%              Number of leaves         :   15 (  20 expanded)
%              Depth                    :    5
%              Number of atoms          :   33 (  62 expanded)
%              Number of equality atoms :   14 (  26 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > v1_funct_1 > k8_relat_1 > k3_xboole_0 > #nlpp > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k8_relat_1,type,(
    k8_relat_1: ( $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

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

tff(f_50,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_relat_1(C)
          & v1_funct_1(C) )
       => ( r1_tarski(A,B)
         => ( k8_relat_1(B,k8_relat_1(A,C)) = k8_relat_1(A,C)
            & k8_relat_1(A,k8_relat_1(B,C)) = k8_relat_1(A,C) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t97_funct_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_33,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k8_relat_1(A,k8_relat_1(B,C)) = k8_relat_1(k3_xboole_0(A,B),C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t127_relat_1)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r1_tarski(A,B)
       => k8_relat_1(B,k8_relat_1(A,C)) = k8_relat_1(A,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t129_relat_1)).

tff(c_14,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_10,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_15,plain,(
    ! [A_9,B_10] :
      ( k3_xboole_0(A_9,B_10) = A_9
      | ~ r1_tarski(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_19,plain,(
    k3_xboole_0('#skF_1','#skF_2') = '#skF_1' ),
    inference(resolution,[status(thm)],[c_10,c_15])).

tff(c_24,plain,(
    ! [A_11,B_12,C_13] :
      ( k8_relat_1(k3_xboole_0(A_11,B_12),C_13) = k8_relat_1(A_11,k8_relat_1(B_12,C_13))
      | ~ v1_relat_1(C_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_33,plain,(
    ! [C_13] :
      ( k8_relat_1('#skF_1',k8_relat_1('#skF_2',C_13)) = k8_relat_1('#skF_1',C_13)
      | ~ v1_relat_1(C_13) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_19,c_24])).

tff(c_6,plain,(
    ! [B_7,A_6,C_8] :
      ( k8_relat_1(B_7,k8_relat_1(A_6,C_8)) = k8_relat_1(A_6,C_8)
      | ~ r1_tarski(A_6,B_7)
      | ~ v1_relat_1(C_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_8,plain,
    ( k8_relat_1('#skF_1',k8_relat_1('#skF_2','#skF_3')) != k8_relat_1('#skF_1','#skF_3')
    | k8_relat_1('#skF_2',k8_relat_1('#skF_1','#skF_3')) != k8_relat_1('#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_87,plain,(
    k8_relat_1('#skF_2',k8_relat_1('#skF_1','#skF_3')) != k8_relat_1('#skF_1','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_8])).

tff(c_90,plain,
    ( ~ r1_tarski('#skF_1','#skF_2')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_87])).

tff(c_94,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_10,c_90])).

tff(c_95,plain,(
    k8_relat_1('#skF_1',k8_relat_1('#skF_2','#skF_3')) != k8_relat_1('#skF_1','#skF_3') ),
    inference(splitRight,[status(thm)],[c_8])).

tff(c_102,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_33,c_95])).

tff(c_108,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_102])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n004.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 20:00:53 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.67/1.13  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.67/1.13  
% 1.67/1.13  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.67/1.13  %$ r1_tarski > v1_relat_1 > v1_funct_1 > k8_relat_1 > k3_xboole_0 > #nlpp > #skF_2 > #skF_3 > #skF_1
% 1.67/1.13  
% 1.67/1.13  %Foreground sorts:
% 1.67/1.13  
% 1.67/1.13  
% 1.67/1.13  %Background operators:
% 1.67/1.13  
% 1.67/1.13  
% 1.67/1.13  %Foreground operators:
% 1.67/1.13  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 1.67/1.13  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 1.67/1.13  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.67/1.13  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.67/1.13  tff('#skF_2', type, '#skF_2': $i).
% 1.67/1.13  tff('#skF_3', type, '#skF_3': $i).
% 1.67/1.13  tff('#skF_1', type, '#skF_1': $i).
% 1.67/1.13  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.67/1.13  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.67/1.13  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.67/1.13  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.67/1.13  
% 1.82/1.14  tff(f_50, negated_conjecture, ~(![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r1_tarski(A, B) => ((k8_relat_1(B, k8_relat_1(A, C)) = k8_relat_1(A, C)) & (k8_relat_1(A, k8_relat_1(B, C)) = k8_relat_1(A, C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t97_funct_1)).
% 1.82/1.14  tff(f_29, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 1.82/1.14  tff(f_33, axiom, (![A, B, C]: (v1_relat_1(C) => (k8_relat_1(A, k8_relat_1(B, C)) = k8_relat_1(k3_xboole_0(A, B), C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t127_relat_1)).
% 1.82/1.14  tff(f_39, axiom, (![A, B, C]: (v1_relat_1(C) => (r1_tarski(A, B) => (k8_relat_1(B, k8_relat_1(A, C)) = k8_relat_1(A, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t129_relat_1)).
% 1.82/1.14  tff(c_14, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_50])).
% 1.82/1.14  tff(c_10, plain, (r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_50])).
% 1.82/1.14  tff(c_15, plain, (![A_9, B_10]: (k3_xboole_0(A_9, B_10)=A_9 | ~r1_tarski(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.82/1.14  tff(c_19, plain, (k3_xboole_0('#skF_1', '#skF_2')='#skF_1'), inference(resolution, [status(thm)], [c_10, c_15])).
% 1.82/1.14  tff(c_24, plain, (![A_11, B_12, C_13]: (k8_relat_1(k3_xboole_0(A_11, B_12), C_13)=k8_relat_1(A_11, k8_relat_1(B_12, C_13)) | ~v1_relat_1(C_13))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.82/1.14  tff(c_33, plain, (![C_13]: (k8_relat_1('#skF_1', k8_relat_1('#skF_2', C_13))=k8_relat_1('#skF_1', C_13) | ~v1_relat_1(C_13))), inference(superposition, [status(thm), theory('equality')], [c_19, c_24])).
% 1.82/1.14  tff(c_6, plain, (![B_7, A_6, C_8]: (k8_relat_1(B_7, k8_relat_1(A_6, C_8))=k8_relat_1(A_6, C_8) | ~r1_tarski(A_6, B_7) | ~v1_relat_1(C_8))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.82/1.14  tff(c_8, plain, (k8_relat_1('#skF_1', k8_relat_1('#skF_2', '#skF_3'))!=k8_relat_1('#skF_1', '#skF_3') | k8_relat_1('#skF_2', k8_relat_1('#skF_1', '#skF_3'))!=k8_relat_1('#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_50])).
% 1.82/1.14  tff(c_87, plain, (k8_relat_1('#skF_2', k8_relat_1('#skF_1', '#skF_3'))!=k8_relat_1('#skF_1', '#skF_3')), inference(splitLeft, [status(thm)], [c_8])).
% 1.82/1.14  tff(c_90, plain, (~r1_tarski('#skF_1', '#skF_2') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_6, c_87])).
% 1.82/1.14  tff(c_94, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_14, c_10, c_90])).
% 1.82/1.14  tff(c_95, plain, (k8_relat_1('#skF_1', k8_relat_1('#skF_2', '#skF_3'))!=k8_relat_1('#skF_1', '#skF_3')), inference(splitRight, [status(thm)], [c_8])).
% 1.82/1.14  tff(c_102, plain, (~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_33, c_95])).
% 1.82/1.14  tff(c_108, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_14, c_102])).
% 1.82/1.14  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.82/1.14  
% 1.82/1.14  Inference rules
% 1.82/1.14  ----------------------
% 1.82/1.14  #Ref     : 0
% 1.82/1.14  #Sup     : 22
% 1.82/1.14  #Fact    : 0
% 1.82/1.14  #Define  : 0
% 1.82/1.14  #Split   : 2
% 1.82/1.14  #Chain   : 0
% 1.82/1.14  #Close   : 0
% 1.82/1.14  
% 1.82/1.14  Ordering : KBO
% 1.82/1.14  
% 1.82/1.14  Simplification rules
% 1.82/1.14  ----------------------
% 1.82/1.14  #Subsume      : 1
% 1.82/1.14  #Demod        : 4
% 1.82/1.14  #Tautology    : 9
% 1.82/1.14  #SimpNegUnit  : 0
% 1.82/1.14  #BackRed      : 0
% 1.82/1.14  
% 1.82/1.14  #Partial instantiations: 0
% 1.82/1.14  #Strategies tried      : 1
% 1.82/1.14  
% 1.82/1.14  Timing (in seconds)
% 1.82/1.14  ----------------------
% 1.82/1.15  Preprocessing        : 0.26
% 1.82/1.15  Parsing              : 0.15
% 1.82/1.15  CNF conversion       : 0.02
% 1.82/1.15  Main loop            : 0.12
% 1.82/1.15  Inferencing          : 0.06
% 1.82/1.15  Reduction            : 0.03
% 1.82/1.15  Demodulation         : 0.02
% 1.82/1.15  BG Simplification    : 0.01
% 1.82/1.15  Subsumption          : 0.02
% 1.82/1.15  Abstraction          : 0.01
% 1.82/1.15  MUC search           : 0.00
% 1.82/1.15  Cooper               : 0.00
% 1.82/1.15  Total                : 0.40
% 1.82/1.15  Index Insertion      : 0.00
% 1.82/1.15  Index Deletion       : 0.00
% 1.82/1.15  Index Matching       : 0.00
% 1.82/1.15  BG Taut test         : 0.00
%------------------------------------------------------------------------------
