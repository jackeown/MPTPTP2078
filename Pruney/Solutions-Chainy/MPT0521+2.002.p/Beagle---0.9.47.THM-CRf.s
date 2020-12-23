%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:00:09 EST 2020

% Result     : Theorem 1.73s
% Output     : CNFRefutation 1.73s
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
           => r1_tarski(k5_relat_1(k8_relat_1(A,B),C),k5_relat_1(B,C)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t121_relat_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k8_relat_1(A,B),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t117_relat_1)).

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

tff(f_51,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ! [C] :
              ( v1_relat_1(C)
             => ( r1_tarski(A,B)
               => r1_tarski(k5_relat_1(A,C),k5_relat_1(B,C)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_relat_1)).

tff(c_16,plain,(
    v1_relat_1('#skF_2') ),
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

tff(c_14,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_71,plain,(
    ! [A_27,C_28,B_29] :
      ( r1_tarski(k5_relat_1(A_27,C_28),k5_relat_1(B_29,C_28))
      | ~ r1_tarski(A_27,B_29)
      | ~ v1_relat_1(C_28)
      | ~ v1_relat_1(B_29)
      | ~ v1_relat_1(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_12,plain,(
    ~ r1_tarski(k5_relat_1(k8_relat_1('#skF_1','#skF_2'),'#skF_3'),k5_relat_1('#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_74,plain,
    ( ~ r1_tarski(k8_relat_1('#skF_1','#skF_2'),'#skF_2')
    | ~ v1_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1(k8_relat_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_71,c_12])).

tff(c_80,plain,
    ( ~ r1_tarski(k8_relat_1('#skF_1','#skF_2'),'#skF_2')
    | ~ v1_relat_1(k8_relat_1('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_14,c_74])).

tff(c_82,plain,(
    ~ v1_relat_1(k8_relat_1('#skF_1','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_80])).

tff(c_101,plain,(
    ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_98,c_82])).

tff(c_105,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_101])).

tff(c_106,plain,(
    ~ r1_tarski(k8_relat_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_80])).

tff(c_110,plain,(
    ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_8,c_106])).

tff(c_114,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_110])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n008.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:21:45 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.73/1.19  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.73/1.19  
% 1.73/1.19  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.73/1.19  %$ r1_tarski > v1_relat_1 > k8_relat_1 > k5_relat_1 > k3_xboole_0 > #nlpp > #skF_2 > #skF_3 > #skF_1
% 1.73/1.19  
% 1.73/1.19  %Foreground sorts:
% 1.73/1.19  
% 1.73/1.19  
% 1.73/1.19  %Background operators:
% 1.73/1.19  
% 1.73/1.19  
% 1.73/1.19  %Foreground operators:
% 1.73/1.19  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 1.73/1.19  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.73/1.19  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 1.73/1.19  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.73/1.19  tff('#skF_2', type, '#skF_2': $i).
% 1.73/1.19  tff('#skF_3', type, '#skF_3': $i).
% 1.73/1.19  tff('#skF_1', type, '#skF_1': $i).
% 1.73/1.19  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.73/1.19  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.73/1.19  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.73/1.19  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.73/1.19  
% 1.73/1.20  tff(f_59, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => r1_tarski(k5_relat_1(k8_relat_1(A, B), C), k5_relat_1(B, C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t121_relat_1)).
% 1.73/1.20  tff(f_39, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k8_relat_1(A, B), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t117_relat_1)).
% 1.73/1.20  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 1.73/1.20  tff(f_31, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 1.73/1.20  tff(f_35, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_relat_1)).
% 1.73/1.20  tff(f_51, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (r1_tarski(A, B) => r1_tarski(k5_relat_1(A, C), k5_relat_1(B, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_relat_1)).
% 1.73/1.20  tff(c_16, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_59])).
% 1.73/1.20  tff(c_8, plain, (![A_7, B_8]: (r1_tarski(k8_relat_1(A_7, B_8), B_8) | ~v1_relat_1(B_8))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.73/1.20  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.73/1.20  tff(c_65, plain, (![A_25, B_26]: (r1_tarski(k8_relat_1(A_25, B_26), B_26) | ~v1_relat_1(B_26))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.73/1.20  tff(c_4, plain, (![A_3, B_4]: (k3_xboole_0(A_3, B_4)=A_3 | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.73/1.20  tff(c_68, plain, (![A_25, B_26]: (k3_xboole_0(k8_relat_1(A_25, B_26), B_26)=k8_relat_1(A_25, B_26) | ~v1_relat_1(B_26))), inference(resolution, [status(thm)], [c_65, c_4])).
% 1.73/1.20  tff(c_83, plain, (![B_30, A_31]: (k3_xboole_0(B_30, k8_relat_1(A_31, B_30))=k8_relat_1(A_31, B_30) | ~v1_relat_1(B_30))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_68])).
% 1.73/1.20  tff(c_6, plain, (![A_5, B_6]: (v1_relat_1(k3_xboole_0(A_5, B_6)) | ~v1_relat_1(A_5))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.73/1.20  tff(c_98, plain, (![A_32, B_33]: (v1_relat_1(k8_relat_1(A_32, B_33)) | ~v1_relat_1(B_33) | ~v1_relat_1(B_33))), inference(superposition, [status(thm), theory('equality')], [c_83, c_6])).
% 1.73/1.20  tff(c_14, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_59])).
% 1.73/1.20  tff(c_71, plain, (![A_27, C_28, B_29]: (r1_tarski(k5_relat_1(A_27, C_28), k5_relat_1(B_29, C_28)) | ~r1_tarski(A_27, B_29) | ~v1_relat_1(C_28) | ~v1_relat_1(B_29) | ~v1_relat_1(A_27))), inference(cnfTransformation, [status(thm)], [f_51])).
% 1.73/1.20  tff(c_12, plain, (~r1_tarski(k5_relat_1(k8_relat_1('#skF_1', '#skF_2'), '#skF_3'), k5_relat_1('#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_59])).
% 1.73/1.20  tff(c_74, plain, (~r1_tarski(k8_relat_1('#skF_1', '#skF_2'), '#skF_2') | ~v1_relat_1('#skF_3') | ~v1_relat_1('#skF_2') | ~v1_relat_1(k8_relat_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_71, c_12])).
% 1.73/1.20  tff(c_80, plain, (~r1_tarski(k8_relat_1('#skF_1', '#skF_2'), '#skF_2') | ~v1_relat_1(k8_relat_1('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_14, c_74])).
% 1.73/1.20  tff(c_82, plain, (~v1_relat_1(k8_relat_1('#skF_1', '#skF_2'))), inference(splitLeft, [status(thm)], [c_80])).
% 1.73/1.20  tff(c_101, plain, (~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_98, c_82])).
% 1.73/1.20  tff(c_105, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_16, c_101])).
% 1.73/1.20  tff(c_106, plain, (~r1_tarski(k8_relat_1('#skF_1', '#skF_2'), '#skF_2')), inference(splitRight, [status(thm)], [c_80])).
% 1.73/1.20  tff(c_110, plain, (~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_8, c_106])).
% 1.73/1.20  tff(c_114, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_16, c_110])).
% 1.73/1.20  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.73/1.20  
% 1.73/1.20  Inference rules
% 1.73/1.20  ----------------------
% 1.73/1.20  #Ref     : 0
% 1.73/1.20  #Sup     : 21
% 1.73/1.20  #Fact    : 0
% 1.73/1.20  #Define  : 0
% 1.73/1.20  #Split   : 1
% 1.73/1.20  #Chain   : 0
% 1.73/1.20  #Close   : 0
% 1.73/1.20  
% 1.73/1.20  Ordering : KBO
% 1.73/1.20  
% 1.73/1.20  Simplification rules
% 1.73/1.20  ----------------------
% 1.73/1.20  #Subsume      : 3
% 1.73/1.20  #Demod        : 5
% 1.73/1.20  #Tautology    : 11
% 1.73/1.20  #SimpNegUnit  : 0
% 1.73/1.20  #BackRed      : 0
% 1.73/1.20  
% 1.73/1.20  #Partial instantiations: 0
% 1.73/1.20  #Strategies tried      : 1
% 1.73/1.20  
% 1.73/1.20  Timing (in seconds)
% 1.73/1.20  ----------------------
% 1.73/1.21  Preprocessing        : 0.27
% 1.73/1.21  Parsing              : 0.16
% 1.73/1.21  CNF conversion       : 0.02
% 1.73/1.21  Main loop            : 0.13
% 1.73/1.21  Inferencing          : 0.06
% 1.73/1.21  Reduction            : 0.04
% 1.73/1.21  Demodulation         : 0.03
% 1.73/1.21  BG Simplification    : 0.01
% 1.73/1.21  Subsumption          : 0.02
% 1.73/1.21  Abstraction          : 0.01
% 1.73/1.21  MUC search           : 0.00
% 1.73/1.21  Cooper               : 0.00
% 1.73/1.21  Total                : 0.43
% 1.73/1.21  Index Insertion      : 0.00
% 1.73/1.21  Index Deletion       : 0.00
% 1.73/1.21  Index Matching       : 0.00
% 1.73/1.21  BG Taut test         : 0.00
%------------------------------------------------------------------------------
