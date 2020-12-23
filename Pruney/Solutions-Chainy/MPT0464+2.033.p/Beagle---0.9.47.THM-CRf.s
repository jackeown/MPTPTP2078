%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:58:47 EST 2020

% Result     : Theorem 1.62s
% Output     : CNFRefutation 1.62s
% Verified   : 
% Statistics : Number of formulae       :   40 (  73 expanded)
%              Number of leaves         :   16 (  33 expanded)
%              Depth                    :    8
%              Number of atoms          :   55 ( 125 expanded)
%              Number of equality atoms :    3 (  14 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k5_relat_1 > k3_xboole_0 > #nlpp > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

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

tff(f_62,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ! [B] :
            ( v1_relat_1(B)
           => ! [C] :
                ( v1_relat_1(C)
               => r1_tarski(k5_relat_1(A,k3_xboole_0(B,C)),k3_xboole_0(k5_relat_1(A,B),k5_relat_1(A,C))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_relat_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_39,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k3_xboole_0(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_relat_1)).

tff(f_29,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_51,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ! [C] :
              ( v1_relat_1(C)
             => ( r1_tarski(A,B)
               => r1_tarski(k5_relat_1(C,A),k5_relat_1(C,B)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_relat_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(A,C) )
     => r1_tarski(A,k3_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_xboole_1)).

tff(c_16,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_60,plain,(
    ! [A_25,B_26] :
      ( v1_relat_1(k3_xboole_0(A_25,B_26))
      | ~ v1_relat_1(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_66,plain,(
    ! [A_1,B_2] :
      ( v1_relat_1(k3_xboole_0(A_1,B_2))
      | ~ v1_relat_1(B_2) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_60])).

tff(c_18,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_21,plain,(
    ! [B_23,A_24] : k3_xboole_0(B_23,A_24) = k3_xboole_0(A_24,B_23) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_4,plain,(
    ! [A_3,B_4] : r1_tarski(k3_xboole_0(A_3,B_4),A_3) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_36,plain,(
    ! [B_23,A_24] : r1_tarski(k3_xboole_0(B_23,A_24),A_24) ),
    inference(superposition,[status(thm),theory(equality)],[c_21,c_4])).

tff(c_10,plain,(
    ! [C_16,A_10,B_14] :
      ( r1_tarski(k5_relat_1(C_16,A_10),k5_relat_1(C_16,B_14))
      | ~ r1_tarski(A_10,B_14)
      | ~ v1_relat_1(C_16)
      | ~ v1_relat_1(B_14)
      | ~ v1_relat_1(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_14,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_84,plain,(
    ! [A_31,B_32,C_33] :
      ( r1_tarski(A_31,k3_xboole_0(B_32,C_33))
      | ~ r1_tarski(A_31,C_33)
      | ~ r1_tarski(A_31,B_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_12,plain,(
    ~ r1_tarski(k5_relat_1('#skF_1',k3_xboole_0('#skF_2','#skF_3')),k3_xboole_0(k5_relat_1('#skF_1','#skF_2'),k5_relat_1('#skF_1','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_19,plain,(
    ~ r1_tarski(k5_relat_1('#skF_1',k3_xboole_0('#skF_3','#skF_2')),k3_xboole_0(k5_relat_1('#skF_1','#skF_3'),k5_relat_1('#skF_1','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_2,c_12])).

tff(c_94,plain,
    ( ~ r1_tarski(k5_relat_1('#skF_1',k3_xboole_0('#skF_3','#skF_2')),k5_relat_1('#skF_1','#skF_2'))
    | ~ r1_tarski(k5_relat_1('#skF_1',k3_xboole_0('#skF_3','#skF_2')),k5_relat_1('#skF_1','#skF_3')) ),
    inference(resolution,[status(thm)],[c_84,c_19])).

tff(c_96,plain,(
    ~ r1_tarski(k5_relat_1('#skF_1',k3_xboole_0('#skF_3','#skF_2')),k5_relat_1('#skF_1','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_94])).

tff(c_99,plain,
    ( ~ r1_tarski(k3_xboole_0('#skF_3','#skF_2'),'#skF_3')
    | ~ v1_relat_1('#skF_1')
    | ~ v1_relat_1('#skF_3')
    | ~ v1_relat_1(k3_xboole_0('#skF_3','#skF_2')) ),
    inference(resolution,[status(thm)],[c_10,c_96])).

tff(c_102,plain,(
    ~ v1_relat_1(k3_xboole_0('#skF_3','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_18,c_4,c_99])).

tff(c_105,plain,(
    ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_66,c_102])).

tff(c_112,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_105])).

tff(c_113,plain,(
    ~ r1_tarski(k5_relat_1('#skF_1',k3_xboole_0('#skF_3','#skF_2')),k5_relat_1('#skF_1','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_94])).

tff(c_117,plain,
    ( ~ r1_tarski(k3_xboole_0('#skF_3','#skF_2'),'#skF_2')
    | ~ v1_relat_1('#skF_1')
    | ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1(k3_xboole_0('#skF_3','#skF_2')) ),
    inference(resolution,[status(thm)],[c_10,c_113])).

tff(c_120,plain,(
    ~ v1_relat_1(k3_xboole_0('#skF_3','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_18,c_36,c_117])).

tff(c_123,plain,(
    ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_66,c_120])).

tff(c_130,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_123])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:36:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.62/1.13  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.62/1.14  
% 1.62/1.14  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.62/1.14  %$ r1_tarski > v1_relat_1 > k5_relat_1 > k3_xboole_0 > #nlpp > #skF_2 > #skF_3 > #skF_1
% 1.62/1.14  
% 1.62/1.14  %Foreground sorts:
% 1.62/1.14  
% 1.62/1.14  
% 1.62/1.14  %Background operators:
% 1.62/1.14  
% 1.62/1.14  
% 1.62/1.14  %Foreground operators:
% 1.62/1.14  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.62/1.14  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 1.62/1.14  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.62/1.14  tff('#skF_2', type, '#skF_2': $i).
% 1.62/1.14  tff('#skF_3', type, '#skF_3': $i).
% 1.62/1.14  tff('#skF_1', type, '#skF_1': $i).
% 1.62/1.14  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.62/1.14  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.62/1.14  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.62/1.14  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.62/1.14  
% 1.62/1.15  tff(f_62, negated_conjecture, ~(![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => r1_tarski(k5_relat_1(A, k3_xboole_0(B, C)), k3_xboole_0(k5_relat_1(A, B), k5_relat_1(A, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_relat_1)).
% 1.62/1.15  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 1.62/1.15  tff(f_39, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_relat_1)).
% 1.62/1.15  tff(f_29, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 1.62/1.15  tff(f_51, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (r1_tarski(A, B) => r1_tarski(k5_relat_1(C, A), k5_relat_1(C, B))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_relat_1)).
% 1.62/1.15  tff(f_35, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(A, C)) => r1_tarski(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t19_xboole_1)).
% 1.62/1.15  tff(c_16, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_62])).
% 1.62/1.15  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.62/1.15  tff(c_60, plain, (![A_25, B_26]: (v1_relat_1(k3_xboole_0(A_25, B_26)) | ~v1_relat_1(A_25))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.62/1.15  tff(c_66, plain, (![A_1, B_2]: (v1_relat_1(k3_xboole_0(A_1, B_2)) | ~v1_relat_1(B_2))), inference(superposition, [status(thm), theory('equality')], [c_2, c_60])).
% 1.62/1.15  tff(c_18, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_62])).
% 1.62/1.15  tff(c_21, plain, (![B_23, A_24]: (k3_xboole_0(B_23, A_24)=k3_xboole_0(A_24, B_23))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.62/1.15  tff(c_4, plain, (![A_3, B_4]: (r1_tarski(k3_xboole_0(A_3, B_4), A_3))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.62/1.15  tff(c_36, plain, (![B_23, A_24]: (r1_tarski(k3_xboole_0(B_23, A_24), A_24))), inference(superposition, [status(thm), theory('equality')], [c_21, c_4])).
% 1.62/1.15  tff(c_10, plain, (![C_16, A_10, B_14]: (r1_tarski(k5_relat_1(C_16, A_10), k5_relat_1(C_16, B_14)) | ~r1_tarski(A_10, B_14) | ~v1_relat_1(C_16) | ~v1_relat_1(B_14) | ~v1_relat_1(A_10))), inference(cnfTransformation, [status(thm)], [f_51])).
% 1.62/1.15  tff(c_14, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_62])).
% 1.62/1.15  tff(c_84, plain, (![A_31, B_32, C_33]: (r1_tarski(A_31, k3_xboole_0(B_32, C_33)) | ~r1_tarski(A_31, C_33) | ~r1_tarski(A_31, B_32))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.62/1.15  tff(c_12, plain, (~r1_tarski(k5_relat_1('#skF_1', k3_xboole_0('#skF_2', '#skF_3')), k3_xboole_0(k5_relat_1('#skF_1', '#skF_2'), k5_relat_1('#skF_1', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_62])).
% 1.62/1.15  tff(c_19, plain, (~r1_tarski(k5_relat_1('#skF_1', k3_xboole_0('#skF_3', '#skF_2')), k3_xboole_0(k5_relat_1('#skF_1', '#skF_3'), k5_relat_1('#skF_1', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_2, c_12])).
% 1.62/1.15  tff(c_94, plain, (~r1_tarski(k5_relat_1('#skF_1', k3_xboole_0('#skF_3', '#skF_2')), k5_relat_1('#skF_1', '#skF_2')) | ~r1_tarski(k5_relat_1('#skF_1', k3_xboole_0('#skF_3', '#skF_2')), k5_relat_1('#skF_1', '#skF_3'))), inference(resolution, [status(thm)], [c_84, c_19])).
% 1.62/1.15  tff(c_96, plain, (~r1_tarski(k5_relat_1('#skF_1', k3_xboole_0('#skF_3', '#skF_2')), k5_relat_1('#skF_1', '#skF_3'))), inference(splitLeft, [status(thm)], [c_94])).
% 1.62/1.15  tff(c_99, plain, (~r1_tarski(k3_xboole_0('#skF_3', '#skF_2'), '#skF_3') | ~v1_relat_1('#skF_1') | ~v1_relat_1('#skF_3') | ~v1_relat_1(k3_xboole_0('#skF_3', '#skF_2'))), inference(resolution, [status(thm)], [c_10, c_96])).
% 1.62/1.15  tff(c_102, plain, (~v1_relat_1(k3_xboole_0('#skF_3', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_18, c_4, c_99])).
% 1.62/1.15  tff(c_105, plain, (~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_66, c_102])).
% 1.62/1.15  tff(c_112, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_16, c_105])).
% 1.62/1.15  tff(c_113, plain, (~r1_tarski(k5_relat_1('#skF_1', k3_xboole_0('#skF_3', '#skF_2')), k5_relat_1('#skF_1', '#skF_2'))), inference(splitRight, [status(thm)], [c_94])).
% 1.62/1.15  tff(c_117, plain, (~r1_tarski(k3_xboole_0('#skF_3', '#skF_2'), '#skF_2') | ~v1_relat_1('#skF_1') | ~v1_relat_1('#skF_2') | ~v1_relat_1(k3_xboole_0('#skF_3', '#skF_2'))), inference(resolution, [status(thm)], [c_10, c_113])).
% 1.62/1.15  tff(c_120, plain, (~v1_relat_1(k3_xboole_0('#skF_3', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_18, c_36, c_117])).
% 1.62/1.15  tff(c_123, plain, (~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_66, c_120])).
% 1.62/1.15  tff(c_130, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_16, c_123])).
% 1.62/1.15  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.62/1.15  
% 1.62/1.15  Inference rules
% 1.62/1.15  ----------------------
% 1.62/1.15  #Ref     : 0
% 1.62/1.15  #Sup     : 25
% 1.62/1.15  #Fact    : 0
% 1.62/1.15  #Define  : 0
% 1.62/1.15  #Split   : 1
% 1.62/1.15  #Chain   : 0
% 1.62/1.15  #Close   : 0
% 1.62/1.15  
% 1.62/1.15  Ordering : KBO
% 1.62/1.15  
% 1.62/1.15  Simplification rules
% 1.62/1.15  ----------------------
% 1.62/1.15  #Subsume      : 5
% 1.62/1.15  #Demod        : 13
% 1.62/1.15  #Tautology    : 11
% 1.62/1.15  #SimpNegUnit  : 0
% 1.62/1.15  #BackRed      : 0
% 1.62/1.15  
% 1.62/1.15  #Partial instantiations: 0
% 1.62/1.15  #Strategies tried      : 1
% 1.62/1.15  
% 1.62/1.15  Timing (in seconds)
% 1.62/1.15  ----------------------
% 1.62/1.15  Preprocessing        : 0.26
% 1.62/1.15  Parsing              : 0.15
% 1.62/1.15  CNF conversion       : 0.02
% 1.62/1.15  Main loop            : 0.13
% 1.62/1.15  Inferencing          : 0.04
% 1.62/1.15  Reduction            : 0.05
% 1.62/1.15  Demodulation         : 0.04
% 1.62/1.15  BG Simplification    : 0.01
% 1.62/1.15  Subsumption          : 0.02
% 1.62/1.15  Abstraction          : 0.00
% 1.62/1.15  MUC search           : 0.00
% 1.62/1.15  Cooper               : 0.00
% 1.62/1.15  Total                : 0.42
% 1.62/1.15  Index Insertion      : 0.00
% 1.62/1.15  Index Deletion       : 0.00
% 1.62/1.15  Index Matching       : 0.00
% 1.62/1.15  BG Taut test         : 0.00
%------------------------------------------------------------------------------
