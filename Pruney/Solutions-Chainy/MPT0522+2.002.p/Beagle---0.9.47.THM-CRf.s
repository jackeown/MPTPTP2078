%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:00:10 EST 2020

% Result     : Theorem 2.08s
% Output     : CNFRefutation 2.17s
% Verified   : 
% Statistics : Number of formulae       :   37 (  54 expanded)
%              Number of leaves         :   17 (  26 expanded)
%              Depth                    :    6
%              Number of atoms          :   51 (  95 expanded)
%              Number of equality atoms :    6 (   6 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k8_relat_1 > k5_relat_1 > k3_xboole_0 > #nlpp > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k8_relat_1,type,(
    k8_relat_1: ( $i * $i ) > $i )).

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

tff(f_59,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ! [C] :
            ( v1_relat_1(C)
           => r1_tarski(k5_relat_1(B,k8_relat_1(A,C)),k5_relat_1(B,C)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t122_relat_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k8_relat_1(A,B),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t117_relat_1)).

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

tff(f_51,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ! [C] :
              ( v1_relat_1(C)
             => ( r1_tarski(A,B)
               => r1_tarski(k5_relat_1(C,A),k5_relat_1(C,B)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_relat_1)).

tff(c_14,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_8,plain,(
    ! [A_7,B_8] :
      ( r1_tarski(k8_relat_1(A_7,B_8),B_8)
      | ~ v1_relat_1(B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_65,plain,(
    ! [A_25,B_26] :
      ( r1_tarski(k8_relat_1(A_25,B_26),B_26)
      | ~ v1_relat_1(B_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_4,plain,(
    ! [A_3,B_4] :
      ( k3_xboole_0(A_3,B_4) = A_3
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_68,plain,(
    ! [A_25,B_26] :
      ( k3_xboole_0(k8_relat_1(A_25,B_26),B_26) = k8_relat_1(A_25,B_26)
      | ~ v1_relat_1(B_26) ) ),
    inference(resolution,[status(thm)],[c_65,c_4])).

tff(c_83,plain,(
    ! [B_30,A_31] :
      ( k3_xboole_0(B_30,k8_relat_1(A_31,B_30)) = k8_relat_1(A_31,B_30)
      | ~ v1_relat_1(B_30) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_68])).

tff(c_6,plain,(
    ! [A_5,B_6] :
      ( v1_relat_1(k3_xboole_0(A_5,B_6))
      | ~ v1_relat_1(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_98,plain,(
    ! [A_32,B_33] :
      ( v1_relat_1(k8_relat_1(A_32,B_33))
      | ~ v1_relat_1(B_33)
      | ~ v1_relat_1(B_33) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_83,c_6])).

tff(c_16,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_71,plain,(
    ! [C_27,A_28,B_29] :
      ( r1_tarski(k5_relat_1(C_27,A_28),k5_relat_1(C_27,B_29))
      | ~ r1_tarski(A_28,B_29)
      | ~ v1_relat_1(C_27)
      | ~ v1_relat_1(B_29)
      | ~ v1_relat_1(A_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_12,plain,(
    ~ r1_tarski(k5_relat_1('#skF_2',k8_relat_1('#skF_1','#skF_3')),k5_relat_1('#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_74,plain,
    ( ~ r1_tarski(k8_relat_1('#skF_1','#skF_3'),'#skF_3')
    | ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1('#skF_3')
    | ~ v1_relat_1(k8_relat_1('#skF_1','#skF_3')) ),
    inference(resolution,[status(thm)],[c_71,c_12])).

tff(c_80,plain,
    ( ~ r1_tarski(k8_relat_1('#skF_1','#skF_3'),'#skF_3')
    | ~ v1_relat_1(k8_relat_1('#skF_1','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_16,c_74])).

tff(c_82,plain,(
    ~ v1_relat_1(k8_relat_1('#skF_1','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_80])).

tff(c_101,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_98,c_82])).

tff(c_105,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_101])).

tff(c_106,plain,(
    ~ r1_tarski(k8_relat_1('#skF_1','#skF_3'),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_80])).

tff(c_110,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_8,c_106])).

tff(c_114,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_110])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:36:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.08/1.49  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.08/1.49  
% 2.08/1.49  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.08/1.50  %$ r1_tarski > v1_relat_1 > k8_relat_1 > k5_relat_1 > k3_xboole_0 > #nlpp > #skF_2 > #skF_3 > #skF_1
% 2.08/1.50  
% 2.08/1.50  %Foreground sorts:
% 2.08/1.50  
% 2.08/1.50  
% 2.08/1.50  %Background operators:
% 2.08/1.50  
% 2.08/1.50  
% 2.08/1.50  %Foreground operators:
% 2.08/1.50  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 2.08/1.50  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.08/1.50  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.08/1.50  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.08/1.50  tff('#skF_2', type, '#skF_2': $i).
% 2.08/1.50  tff('#skF_3', type, '#skF_3': $i).
% 2.08/1.50  tff('#skF_1', type, '#skF_1': $i).
% 2.08/1.50  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.08/1.50  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.08/1.50  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.08/1.50  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.08/1.50  
% 2.17/1.51  tff(f_59, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => r1_tarski(k5_relat_1(B, k8_relat_1(A, C)), k5_relat_1(B, C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t122_relat_1)).
% 2.17/1.51  tff(f_39, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k8_relat_1(A, B), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t117_relat_1)).
% 2.17/1.51  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 2.17/1.51  tff(f_31, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 2.17/1.51  tff(f_35, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_relat_1)).
% 2.17/1.51  tff(f_51, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (r1_tarski(A, B) => r1_tarski(k5_relat_1(C, A), k5_relat_1(C, B))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_relat_1)).
% 2.17/1.51  tff(c_14, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.17/1.51  tff(c_8, plain, (![A_7, B_8]: (r1_tarski(k8_relat_1(A_7, B_8), B_8) | ~v1_relat_1(B_8))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.17/1.51  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.17/1.51  tff(c_65, plain, (![A_25, B_26]: (r1_tarski(k8_relat_1(A_25, B_26), B_26) | ~v1_relat_1(B_26))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.17/1.51  tff(c_4, plain, (![A_3, B_4]: (k3_xboole_0(A_3, B_4)=A_3 | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.17/1.51  tff(c_68, plain, (![A_25, B_26]: (k3_xboole_0(k8_relat_1(A_25, B_26), B_26)=k8_relat_1(A_25, B_26) | ~v1_relat_1(B_26))), inference(resolution, [status(thm)], [c_65, c_4])).
% 2.17/1.51  tff(c_83, plain, (![B_30, A_31]: (k3_xboole_0(B_30, k8_relat_1(A_31, B_30))=k8_relat_1(A_31, B_30) | ~v1_relat_1(B_30))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_68])).
% 2.17/1.51  tff(c_6, plain, (![A_5, B_6]: (v1_relat_1(k3_xboole_0(A_5, B_6)) | ~v1_relat_1(A_5))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.17/1.51  tff(c_98, plain, (![A_32, B_33]: (v1_relat_1(k8_relat_1(A_32, B_33)) | ~v1_relat_1(B_33) | ~v1_relat_1(B_33))), inference(superposition, [status(thm), theory('equality')], [c_83, c_6])).
% 2.17/1.51  tff(c_16, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.17/1.51  tff(c_71, plain, (![C_27, A_28, B_29]: (r1_tarski(k5_relat_1(C_27, A_28), k5_relat_1(C_27, B_29)) | ~r1_tarski(A_28, B_29) | ~v1_relat_1(C_27) | ~v1_relat_1(B_29) | ~v1_relat_1(A_28))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.17/1.51  tff(c_12, plain, (~r1_tarski(k5_relat_1('#skF_2', k8_relat_1('#skF_1', '#skF_3')), k5_relat_1('#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.17/1.51  tff(c_74, plain, (~r1_tarski(k8_relat_1('#skF_1', '#skF_3'), '#skF_3') | ~v1_relat_1('#skF_2') | ~v1_relat_1('#skF_3') | ~v1_relat_1(k8_relat_1('#skF_1', '#skF_3'))), inference(resolution, [status(thm)], [c_71, c_12])).
% 2.17/1.51  tff(c_80, plain, (~r1_tarski(k8_relat_1('#skF_1', '#skF_3'), '#skF_3') | ~v1_relat_1(k8_relat_1('#skF_1', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_16, c_74])).
% 2.17/1.51  tff(c_82, plain, (~v1_relat_1(k8_relat_1('#skF_1', '#skF_3'))), inference(splitLeft, [status(thm)], [c_80])).
% 2.17/1.51  tff(c_101, plain, (~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_98, c_82])).
% 2.17/1.51  tff(c_105, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_14, c_101])).
% 2.17/1.51  tff(c_106, plain, (~r1_tarski(k8_relat_1('#skF_1', '#skF_3'), '#skF_3')), inference(splitRight, [status(thm)], [c_80])).
% 2.17/1.51  tff(c_110, plain, (~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_8, c_106])).
% 2.17/1.51  tff(c_114, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_14, c_110])).
% 2.17/1.51  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.17/1.51  
% 2.17/1.51  Inference rules
% 2.17/1.52  ----------------------
% 2.17/1.52  #Ref     : 0
% 2.17/1.52  #Sup     : 21
% 2.17/1.52  #Fact    : 0
% 2.17/1.52  #Define  : 0
% 2.17/1.52  #Split   : 1
% 2.17/1.52  #Chain   : 0
% 2.17/1.52  #Close   : 0
% 2.17/1.52  
% 2.17/1.52  Ordering : KBO
% 2.17/1.52  
% 2.17/1.52  Simplification rules
% 2.17/1.52  ----------------------
% 2.17/1.52  #Subsume      : 3
% 2.17/1.52  #Demod        : 5
% 2.17/1.52  #Tautology    : 11
% 2.17/1.52  #SimpNegUnit  : 0
% 2.17/1.52  #BackRed      : 0
% 2.17/1.52  
% 2.17/1.52  #Partial instantiations: 0
% 2.17/1.52  #Strategies tried      : 1
% 2.17/1.52  
% 2.17/1.52  Timing (in seconds)
% 2.17/1.52  ----------------------
% 2.17/1.52  Preprocessing        : 0.42
% 2.17/1.52  Parsing              : 0.22
% 2.17/1.52  CNF conversion       : 0.03
% 2.17/1.52  Main loop            : 0.21
% 2.17/1.52  Inferencing          : 0.09
% 2.17/1.52  Reduction            : 0.06
% 2.17/1.52  Demodulation         : 0.05
% 2.17/1.52  BG Simplification    : 0.01
% 2.17/1.52  Subsumption          : 0.03
% 2.17/1.52  Abstraction          : 0.01
% 2.17/1.52  MUC search           : 0.00
% 2.17/1.52  Cooper               : 0.00
% 2.17/1.52  Total                : 0.67
% 2.17/1.52  Index Insertion      : 0.00
% 2.17/1.52  Index Deletion       : 0.00
% 2.17/1.52  Index Matching       : 0.00
% 2.17/1.52  BG Taut test         : 0.00
%------------------------------------------------------------------------------
