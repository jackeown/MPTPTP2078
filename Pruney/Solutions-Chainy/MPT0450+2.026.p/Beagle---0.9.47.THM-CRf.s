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
% DateTime   : Thu Dec  3 09:58:39 EST 2020

% Result     : Theorem 1.76s
% Output     : CNFRefutation 1.86s
% Verified   : 
% Statistics : Number of formulae       :   37 (  58 expanded)
%              Number of leaves         :   15 (  26 expanded)
%              Depth                    :    7
%              Number of atoms          :   48 (  93 expanded)
%              Number of equality atoms :    3 (   6 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k3_xboole_0 > #nlpp > k3_relat_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k3_relat_1,type,(
    k3_relat_1: $i > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff(f_56,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ! [B] :
            ( v1_relat_1(B)
           => r1_tarski(k3_relat_1(k3_xboole_0(A,B)),k3_xboole_0(k3_relat_1(A),k3_relat_1(B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_relat_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_39,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k3_xboole_0(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_relat_1)).

tff(f_29,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_48,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(A,B)
           => r1_tarski(k3_relat_1(A),k3_relat_1(B)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_relat_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(A,C) )
     => r1_tarski(A,k3_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_xboole_1)).

tff(c_14,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_66,plain,(
    ! [A_20,B_21] :
      ( v1_relat_1(k3_xboole_0(A_20,B_21))
      | ~ v1_relat_1(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_69,plain,(
    ! [B_2,A_1] :
      ( v1_relat_1(k3_xboole_0(B_2,A_1))
      | ~ v1_relat_1(A_1) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_66])).

tff(c_18,plain,(
    ! [B_16,A_17] : k3_xboole_0(B_16,A_17) = k3_xboole_0(A_17,B_16) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_4,plain,(
    ! [A_3,B_4] : r1_tarski(k3_xboole_0(A_3,B_4),A_3) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_33,plain,(
    ! [B_16,A_17] : r1_tarski(k3_xboole_0(B_16,A_17),A_17) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_4])).

tff(c_10,plain,(
    ! [A_10,B_12] :
      ( r1_tarski(k3_relat_1(A_10),k3_relat_1(B_12))
      | ~ r1_tarski(A_10,B_12)
      | ~ v1_relat_1(B_12)
      | ~ v1_relat_1(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_16,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_81,plain,(
    ! [A_24,B_25,C_26] :
      ( r1_tarski(A_24,k3_xboole_0(B_25,C_26))
      | ~ r1_tarski(A_24,C_26)
      | ~ r1_tarski(A_24,B_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_12,plain,(
    ~ r1_tarski(k3_relat_1(k3_xboole_0('#skF_1','#skF_2')),k3_xboole_0(k3_relat_1('#skF_1'),k3_relat_1('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_91,plain,
    ( ~ r1_tarski(k3_relat_1(k3_xboole_0('#skF_1','#skF_2')),k3_relat_1('#skF_2'))
    | ~ r1_tarski(k3_relat_1(k3_xboole_0('#skF_1','#skF_2')),k3_relat_1('#skF_1')) ),
    inference(resolution,[status(thm)],[c_81,c_12])).

tff(c_93,plain,(
    ~ r1_tarski(k3_relat_1(k3_xboole_0('#skF_1','#skF_2')),k3_relat_1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_91])).

tff(c_96,plain,
    ( ~ r1_tarski(k3_xboole_0('#skF_1','#skF_2'),'#skF_1')
    | ~ v1_relat_1('#skF_1')
    | ~ v1_relat_1(k3_xboole_0('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_10,c_93])).

tff(c_99,plain,(
    ~ v1_relat_1(k3_xboole_0('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_4,c_96])).

tff(c_102,plain,(
    ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_69,c_99])).

tff(c_109,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_102])).

tff(c_110,plain,(
    ~ r1_tarski(k3_relat_1(k3_xboole_0('#skF_1','#skF_2')),k3_relat_1('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_91])).

tff(c_114,plain,
    ( ~ r1_tarski(k3_xboole_0('#skF_1','#skF_2'),'#skF_2')
    | ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1(k3_xboole_0('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_10,c_110])).

tff(c_117,plain,(
    ~ v1_relat_1(k3_xboole_0('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_33,c_114])).

tff(c_120,plain,(
    ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_69,c_117])).

tff(c_127,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_120])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n010.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 17:49:29 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.76/1.20  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.86/1.20  
% 1.86/1.20  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.86/1.20  %$ r1_tarski > v1_relat_1 > k3_xboole_0 > #nlpp > k3_relat_1 > #skF_2 > #skF_1
% 1.86/1.20  
% 1.86/1.20  %Foreground sorts:
% 1.86/1.20  
% 1.86/1.20  
% 1.86/1.20  %Background operators:
% 1.86/1.20  
% 1.86/1.20  
% 1.86/1.20  %Foreground operators:
% 1.86/1.20  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.86/1.20  tff(k3_relat_1, type, k3_relat_1: $i > $i).
% 1.86/1.20  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.86/1.20  tff('#skF_2', type, '#skF_2': $i).
% 1.86/1.20  tff('#skF_1', type, '#skF_1': $i).
% 1.86/1.20  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.86/1.20  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.86/1.20  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.86/1.20  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.86/1.20  
% 1.86/1.21  tff(f_56, negated_conjecture, ~(![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => r1_tarski(k3_relat_1(k3_xboole_0(A, B)), k3_xboole_0(k3_relat_1(A), k3_relat_1(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t34_relat_1)).
% 1.86/1.21  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 1.86/1.21  tff(f_39, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_relat_1)).
% 1.86/1.21  tff(f_29, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 1.86/1.21  tff(f_48, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(A, B) => r1_tarski(k3_relat_1(A), k3_relat_1(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_relat_1)).
% 1.86/1.21  tff(f_35, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(A, C)) => r1_tarski(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t19_xboole_1)).
% 1.86/1.21  tff(c_14, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_56])).
% 1.86/1.21  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.86/1.21  tff(c_66, plain, (![A_20, B_21]: (v1_relat_1(k3_xboole_0(A_20, B_21)) | ~v1_relat_1(A_20))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.86/1.21  tff(c_69, plain, (![B_2, A_1]: (v1_relat_1(k3_xboole_0(B_2, A_1)) | ~v1_relat_1(A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_66])).
% 1.86/1.21  tff(c_18, plain, (![B_16, A_17]: (k3_xboole_0(B_16, A_17)=k3_xboole_0(A_17, B_16))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.86/1.21  tff(c_4, plain, (![A_3, B_4]: (r1_tarski(k3_xboole_0(A_3, B_4), A_3))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.86/1.21  tff(c_33, plain, (![B_16, A_17]: (r1_tarski(k3_xboole_0(B_16, A_17), A_17))), inference(superposition, [status(thm), theory('equality')], [c_18, c_4])).
% 1.86/1.21  tff(c_10, plain, (![A_10, B_12]: (r1_tarski(k3_relat_1(A_10), k3_relat_1(B_12)) | ~r1_tarski(A_10, B_12) | ~v1_relat_1(B_12) | ~v1_relat_1(A_10))), inference(cnfTransformation, [status(thm)], [f_48])).
% 1.86/1.21  tff(c_16, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_56])).
% 1.86/1.21  tff(c_81, plain, (![A_24, B_25, C_26]: (r1_tarski(A_24, k3_xboole_0(B_25, C_26)) | ~r1_tarski(A_24, C_26) | ~r1_tarski(A_24, B_25))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.86/1.21  tff(c_12, plain, (~r1_tarski(k3_relat_1(k3_xboole_0('#skF_1', '#skF_2')), k3_xboole_0(k3_relat_1('#skF_1'), k3_relat_1('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_56])).
% 1.86/1.21  tff(c_91, plain, (~r1_tarski(k3_relat_1(k3_xboole_0('#skF_1', '#skF_2')), k3_relat_1('#skF_2')) | ~r1_tarski(k3_relat_1(k3_xboole_0('#skF_1', '#skF_2')), k3_relat_1('#skF_1'))), inference(resolution, [status(thm)], [c_81, c_12])).
% 1.86/1.21  tff(c_93, plain, (~r1_tarski(k3_relat_1(k3_xboole_0('#skF_1', '#skF_2')), k3_relat_1('#skF_1'))), inference(splitLeft, [status(thm)], [c_91])).
% 1.86/1.21  tff(c_96, plain, (~r1_tarski(k3_xboole_0('#skF_1', '#skF_2'), '#skF_1') | ~v1_relat_1('#skF_1') | ~v1_relat_1(k3_xboole_0('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_10, c_93])).
% 1.86/1.21  tff(c_99, plain, (~v1_relat_1(k3_xboole_0('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_4, c_96])).
% 1.86/1.21  tff(c_102, plain, (~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_69, c_99])).
% 1.86/1.21  tff(c_109, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_14, c_102])).
% 1.86/1.21  tff(c_110, plain, (~r1_tarski(k3_relat_1(k3_xboole_0('#skF_1', '#skF_2')), k3_relat_1('#skF_2'))), inference(splitRight, [status(thm)], [c_91])).
% 1.86/1.21  tff(c_114, plain, (~r1_tarski(k3_xboole_0('#skF_1', '#skF_2'), '#skF_2') | ~v1_relat_1('#skF_2') | ~v1_relat_1(k3_xboole_0('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_10, c_110])).
% 1.86/1.21  tff(c_117, plain, (~v1_relat_1(k3_xboole_0('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_33, c_114])).
% 1.86/1.21  tff(c_120, plain, (~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_69, c_117])).
% 1.86/1.21  tff(c_127, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_14, c_120])).
% 1.86/1.21  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.86/1.21  
% 1.86/1.21  Inference rules
% 1.86/1.21  ----------------------
% 1.86/1.21  #Ref     : 0
% 1.86/1.21  #Sup     : 25
% 1.86/1.21  #Fact    : 0
% 1.86/1.21  #Define  : 0
% 1.86/1.21  #Split   : 1
% 1.86/1.21  #Chain   : 0
% 1.86/1.21  #Close   : 0
% 1.86/1.21  
% 1.86/1.21  Ordering : KBO
% 1.86/1.21  
% 1.86/1.21  Simplification rules
% 1.86/1.21  ----------------------
% 1.86/1.21  #Subsume      : 5
% 1.86/1.21  #Demod        : 9
% 1.86/1.21  #Tautology    : 11
% 1.86/1.21  #SimpNegUnit  : 0
% 1.86/1.21  #BackRed      : 0
% 1.86/1.21  
% 1.86/1.21  #Partial instantiations: 0
% 1.86/1.21  #Strategies tried      : 1
% 1.86/1.21  
% 1.86/1.21  Timing (in seconds)
% 1.86/1.21  ----------------------
% 1.86/1.22  Preprocessing        : 0.24
% 1.86/1.22  Parsing              : 0.13
% 1.86/1.22  CNF conversion       : 0.02
% 1.86/1.22  Main loop            : 0.13
% 1.86/1.22  Inferencing          : 0.05
% 1.86/1.22  Reduction            : 0.05
% 1.86/1.22  Demodulation         : 0.04
% 1.86/1.22  BG Simplification    : 0.01
% 1.86/1.22  Subsumption          : 0.03
% 1.86/1.22  Abstraction          : 0.01
% 1.86/1.22  MUC search           : 0.00
% 1.86/1.22  Cooper               : 0.00
% 1.86/1.22  Total                : 0.40
% 1.86/1.22  Index Insertion      : 0.00
% 1.86/1.22  Index Deletion       : 0.00
% 1.86/1.22  Index Matching       : 0.00
% 1.86/1.22  BG Taut test         : 0.00
%------------------------------------------------------------------------------
