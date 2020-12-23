%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:00:07 EST 2020

% Result     : Theorem 1.92s
% Output     : CNFRefutation 1.92s
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
%$ r1_tarski > v1_relat_1 > k8_relat_1 > k3_xboole_0 > #nlpp > k2_relat_1 > k1_relat_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k8_relat_1,type,(
    k8_relat_1: ( $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

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
       => r1_tarski(k2_relat_1(k8_relat_1(A,B)),k2_relat_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t118_relat_1)).

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

tff(f_50,axiom,(
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

tff(c_8,plain,(
    ! [A_7,B_8] :
      ( r1_tarski(k8_relat_1(A_7,B_8),B_8)
      | ~ v1_relat_1(B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_65,plain,(
    ! [A_20,B_21] :
      ( r1_tarski(k8_relat_1(A_20,B_21),B_21)
      | ~ v1_relat_1(B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_4,plain,(
    ! [A_3,B_4] :
      ( k3_xboole_0(A_3,B_4) = A_3
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_68,plain,(
    ! [A_20,B_21] :
      ( k3_xboole_0(k8_relat_1(A_20,B_21),B_21) = k8_relat_1(A_20,B_21)
      | ~ v1_relat_1(B_21) ) ),
    inference(resolution,[status(thm)],[c_65,c_4])).

tff(c_71,plain,(
    ! [B_22,A_23] :
      ( k3_xboole_0(B_22,k8_relat_1(A_23,B_22)) = k8_relat_1(A_23,B_22)
      | ~ v1_relat_1(B_22) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_68])).

tff(c_6,plain,(
    ! [A_5,B_6] :
      ( v1_relat_1(k3_xboole_0(A_5,B_6))
      | ~ v1_relat_1(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_80,plain,(
    ! [A_23,B_22] :
      ( v1_relat_1(k8_relat_1(A_23,B_22))
      | ~ v1_relat_1(B_22)
      | ~ v1_relat_1(B_22) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_71,c_6])).

tff(c_92,plain,(
    ! [A_28,B_29] :
      ( r1_tarski(k2_relat_1(A_28),k2_relat_1(B_29))
      | ~ r1_tarski(A_28,B_29)
      | ~ v1_relat_1(B_29)
      | ~ v1_relat_1(A_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_14,plain,(
    ~ r1_tarski(k2_relat_1(k8_relat_1('#skF_1','#skF_2')),k2_relat_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_95,plain,
    ( ~ r1_tarski(k8_relat_1('#skF_1','#skF_2'),'#skF_2')
    | ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1(k8_relat_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_92,c_14])).

tff(c_101,plain,
    ( ~ r1_tarski(k8_relat_1('#skF_1','#skF_2'),'#skF_2')
    | ~ v1_relat_1(k8_relat_1('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_95])).

tff(c_103,plain,(
    ~ v1_relat_1(k8_relat_1('#skF_1','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_101])).

tff(c_106,plain,(
    ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_80,c_103])).

tff(c_110,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_106])).

tff(c_111,plain,(
    ~ r1_tarski(k8_relat_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_101])).

tff(c_115,plain,(
    ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_8,c_111])).

tff(c_119,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_115])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:36:59 EST 2020
% 0.20/0.34  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.92/1.25  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.92/1.26  
% 1.92/1.26  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.92/1.26  %$ r1_tarski > v1_relat_1 > k8_relat_1 > k3_xboole_0 > #nlpp > k2_relat_1 > k1_relat_1 > #skF_2 > #skF_1
% 1.92/1.26  
% 1.92/1.26  %Foreground sorts:
% 1.92/1.26  
% 1.92/1.26  
% 1.92/1.26  %Background operators:
% 1.92/1.26  
% 1.92/1.26  
% 1.92/1.26  %Foreground operators:
% 1.92/1.26  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 1.92/1.26  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.92/1.26  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.92/1.26  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.92/1.26  tff('#skF_2', type, '#skF_2': $i).
% 1.92/1.26  tff('#skF_1', type, '#skF_1': $i).
% 1.92/1.26  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.92/1.26  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.92/1.26  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.92/1.26  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.92/1.26  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.92/1.26  
% 1.92/1.27  tff(f_55, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => r1_tarski(k2_relat_1(k8_relat_1(A, B)), k2_relat_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t118_relat_1)).
% 1.92/1.27  tff(f_39, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k8_relat_1(A, B), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t117_relat_1)).
% 1.92/1.27  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 1.92/1.27  tff(f_31, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 1.92/1.27  tff(f_35, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_relat_1)).
% 1.92/1.27  tff(f_50, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(A, B) => (r1_tarski(k1_relat_1(A), k1_relat_1(B)) & r1_tarski(k2_relat_1(A), k2_relat_1(B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t25_relat_1)).
% 1.92/1.27  tff(c_16, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_55])).
% 1.92/1.27  tff(c_8, plain, (![A_7, B_8]: (r1_tarski(k8_relat_1(A_7, B_8), B_8) | ~v1_relat_1(B_8))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.92/1.27  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.92/1.27  tff(c_65, plain, (![A_20, B_21]: (r1_tarski(k8_relat_1(A_20, B_21), B_21) | ~v1_relat_1(B_21))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.92/1.27  tff(c_4, plain, (![A_3, B_4]: (k3_xboole_0(A_3, B_4)=A_3 | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.92/1.27  tff(c_68, plain, (![A_20, B_21]: (k3_xboole_0(k8_relat_1(A_20, B_21), B_21)=k8_relat_1(A_20, B_21) | ~v1_relat_1(B_21))), inference(resolution, [status(thm)], [c_65, c_4])).
% 1.92/1.27  tff(c_71, plain, (![B_22, A_23]: (k3_xboole_0(B_22, k8_relat_1(A_23, B_22))=k8_relat_1(A_23, B_22) | ~v1_relat_1(B_22))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_68])).
% 1.92/1.27  tff(c_6, plain, (![A_5, B_6]: (v1_relat_1(k3_xboole_0(A_5, B_6)) | ~v1_relat_1(A_5))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.92/1.27  tff(c_80, plain, (![A_23, B_22]: (v1_relat_1(k8_relat_1(A_23, B_22)) | ~v1_relat_1(B_22) | ~v1_relat_1(B_22))), inference(superposition, [status(thm), theory('equality')], [c_71, c_6])).
% 1.92/1.27  tff(c_92, plain, (![A_28, B_29]: (r1_tarski(k2_relat_1(A_28), k2_relat_1(B_29)) | ~r1_tarski(A_28, B_29) | ~v1_relat_1(B_29) | ~v1_relat_1(A_28))), inference(cnfTransformation, [status(thm)], [f_50])).
% 1.92/1.27  tff(c_14, plain, (~r1_tarski(k2_relat_1(k8_relat_1('#skF_1', '#skF_2')), k2_relat_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_55])).
% 1.92/1.27  tff(c_95, plain, (~r1_tarski(k8_relat_1('#skF_1', '#skF_2'), '#skF_2') | ~v1_relat_1('#skF_2') | ~v1_relat_1(k8_relat_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_92, c_14])).
% 1.92/1.27  tff(c_101, plain, (~r1_tarski(k8_relat_1('#skF_1', '#skF_2'), '#skF_2') | ~v1_relat_1(k8_relat_1('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_95])).
% 1.92/1.27  tff(c_103, plain, (~v1_relat_1(k8_relat_1('#skF_1', '#skF_2'))), inference(splitLeft, [status(thm)], [c_101])).
% 1.92/1.27  tff(c_106, plain, (~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_80, c_103])).
% 1.92/1.27  tff(c_110, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_16, c_106])).
% 1.92/1.27  tff(c_111, plain, (~r1_tarski(k8_relat_1('#skF_1', '#skF_2'), '#skF_2')), inference(splitRight, [status(thm)], [c_101])).
% 1.92/1.27  tff(c_115, plain, (~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_8, c_111])).
% 1.92/1.27  tff(c_119, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_16, c_115])).
% 1.92/1.27  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.92/1.27  
% 1.92/1.27  Inference rules
% 1.92/1.27  ----------------------
% 1.92/1.27  #Ref     : 0
% 1.92/1.27  #Sup     : 22
% 1.92/1.27  #Fact    : 0
% 1.92/1.27  #Define  : 0
% 1.92/1.27  #Split   : 1
% 1.92/1.27  #Chain   : 0
% 1.92/1.27  #Close   : 0
% 1.92/1.27  
% 1.92/1.27  Ordering : KBO
% 1.92/1.27  
% 1.92/1.27  Simplification rules
% 1.92/1.27  ----------------------
% 1.92/1.27  #Subsume      : 3
% 1.92/1.27  #Demod        : 4
% 1.92/1.27  #Tautology    : 11
% 1.92/1.27  #SimpNegUnit  : 0
% 1.92/1.27  #BackRed      : 0
% 1.92/1.27  
% 1.92/1.27  #Partial instantiations: 0
% 1.92/1.27  #Strategies tried      : 1
% 1.92/1.27  
% 1.92/1.27  Timing (in seconds)
% 1.92/1.27  ----------------------
% 1.92/1.27  Preprocessing        : 0.32
% 1.92/1.27  Parsing              : 0.17
% 1.92/1.27  CNF conversion       : 0.02
% 1.92/1.27  Main loop            : 0.14
% 1.92/1.27  Inferencing          : 0.06
% 1.92/1.27  Reduction            : 0.04
% 1.92/1.27  Demodulation         : 0.03
% 1.92/1.27  BG Simplification    : 0.01
% 1.92/1.27  Subsumption          : 0.02
% 1.92/1.27  Abstraction          : 0.01
% 1.92/1.27  MUC search           : 0.00
% 1.92/1.27  Cooper               : 0.00
% 1.92/1.27  Total                : 0.48
% 1.92/1.27  Index Insertion      : 0.00
% 1.92/1.27  Index Deletion       : 0.00
% 1.92/1.27  Index Matching       : 0.00
% 1.92/1.27  BG Taut test         : 0.00
%------------------------------------------------------------------------------
