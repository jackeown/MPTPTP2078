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
% DateTime   : Thu Dec  3 09:58:23 EST 2020

% Result     : Theorem 1.76s
% Output     : CNFRefutation 1.83s
% Verified   : 
% Statistics : Number of formulae       :   40 (  61 expanded)
%              Number of leaves         :   18 (  29 expanded)
%              Depth                    :    7
%              Number of atoms          :   49 (  95 expanded)
%              Number of equality atoms :    3 (   6 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k3_xboole_0 > k2_tarski > #nlpp > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

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

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_60,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ! [B] :
            ( v1_relat_1(B)
           => r1_tarski(k2_relat_1(k3_xboole_0(A,B)),k3_xboole_0(k2_relat_1(A),k2_relat_1(B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t27_relat_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_41,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k3_xboole_0(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_relat_1)).

tff(f_29,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_52,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(A,B)
           => ( r1_tarski(k1_relat_1(A),k1_relat_1(B))
              & r1_tarski(k2_relat_1(A),k2_relat_1(B)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_relat_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(A,C) )
     => r1_tarski(A,k3_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_xboole_1)).

tff(c_18,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_70,plain,(
    ! [A_22,B_23] :
      ( v1_relat_1(k3_xboole_0(A_22,B_23))
      | ~ v1_relat_1(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_76,plain,(
    ! [A_1,B_2] :
      ( v1_relat_1(k3_xboole_0(A_1,B_2))
      | ~ v1_relat_1(B_2) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_70])).

tff(c_22,plain,(
    ! [B_18,A_19] : k3_xboole_0(B_18,A_19) = k3_xboole_0(A_19,B_18) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_4,plain,(
    ! [A_3,B_4] : r1_tarski(k3_xboole_0(A_3,B_4),A_3) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_37,plain,(
    ! [B_18,A_19] : r1_tarski(k3_xboole_0(B_18,A_19),A_19) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_4])).

tff(c_12,plain,(
    ! [A_12,B_14] :
      ( r1_tarski(k2_relat_1(A_12),k2_relat_1(B_14))
      | ~ r1_tarski(A_12,B_14)
      | ~ v1_relat_1(B_14)
      | ~ v1_relat_1(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_20,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_94,plain,(
    ! [A_28,B_29,C_30] :
      ( r1_tarski(A_28,k3_xboole_0(B_29,C_30))
      | ~ r1_tarski(A_28,C_30)
      | ~ r1_tarski(A_28,B_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_16,plain,(
    ~ r1_tarski(k2_relat_1(k3_xboole_0('#skF_1','#skF_2')),k3_xboole_0(k2_relat_1('#skF_1'),k2_relat_1('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_104,plain,
    ( ~ r1_tarski(k2_relat_1(k3_xboole_0('#skF_1','#skF_2')),k2_relat_1('#skF_2'))
    | ~ r1_tarski(k2_relat_1(k3_xboole_0('#skF_1','#skF_2')),k2_relat_1('#skF_1')) ),
    inference(resolution,[status(thm)],[c_94,c_16])).

tff(c_107,plain,(
    ~ r1_tarski(k2_relat_1(k3_xboole_0('#skF_1','#skF_2')),k2_relat_1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_104])).

tff(c_110,plain,
    ( ~ r1_tarski(k3_xboole_0('#skF_1','#skF_2'),'#skF_1')
    | ~ v1_relat_1('#skF_1')
    | ~ v1_relat_1(k3_xboole_0('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_12,c_107])).

tff(c_113,plain,(
    ~ v1_relat_1(k3_xboole_0('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_4,c_110])).

tff(c_116,plain,(
    ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_76,c_113])).

tff(c_123,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_116])).

tff(c_124,plain,(
    ~ r1_tarski(k2_relat_1(k3_xboole_0('#skF_1','#skF_2')),k2_relat_1('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_104])).

tff(c_128,plain,
    ( ~ r1_tarski(k3_xboole_0('#skF_1','#skF_2'),'#skF_2')
    | ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1(k3_xboole_0('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_12,c_124])).

tff(c_131,plain,(
    ~ v1_relat_1(k3_xboole_0('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_37,c_128])).

tff(c_134,plain,(
    ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_76,c_131])).

tff(c_141,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_134])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:10:30 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.76/1.15  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.76/1.15  
% 1.76/1.15  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.76/1.15  %$ r1_tarski > v1_relat_1 > k3_xboole_0 > k2_tarski > #nlpp > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1
% 1.76/1.15  
% 1.76/1.15  %Foreground sorts:
% 1.76/1.15  
% 1.76/1.15  
% 1.76/1.15  %Background operators:
% 1.76/1.15  
% 1.76/1.15  
% 1.76/1.15  %Foreground operators:
% 1.76/1.15  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.76/1.15  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.76/1.15  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.76/1.15  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.76/1.15  tff('#skF_2', type, '#skF_2': $i).
% 1.76/1.15  tff('#skF_1', type, '#skF_1': $i).
% 1.76/1.15  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.76/1.15  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.76/1.15  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.76/1.15  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.76/1.15  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.76/1.15  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 1.76/1.15  
% 1.83/1.16  tff(f_60, negated_conjecture, ~(![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => r1_tarski(k2_relat_1(k3_xboole_0(A, B)), k3_xboole_0(k2_relat_1(A), k2_relat_1(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t27_relat_1)).
% 1.83/1.16  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 1.83/1.16  tff(f_41, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_relat_1)).
% 1.83/1.16  tff(f_29, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 1.83/1.16  tff(f_52, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(A, B) => (r1_tarski(k1_relat_1(A), k1_relat_1(B)) & r1_tarski(k2_relat_1(A), k2_relat_1(B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t25_relat_1)).
% 1.83/1.16  tff(f_35, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(A, C)) => r1_tarski(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t19_xboole_1)).
% 1.83/1.16  tff(c_18, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_60])).
% 1.83/1.16  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.83/1.16  tff(c_70, plain, (![A_22, B_23]: (v1_relat_1(k3_xboole_0(A_22, B_23)) | ~v1_relat_1(A_22))), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.83/1.16  tff(c_76, plain, (![A_1, B_2]: (v1_relat_1(k3_xboole_0(A_1, B_2)) | ~v1_relat_1(B_2))), inference(superposition, [status(thm), theory('equality')], [c_2, c_70])).
% 1.83/1.16  tff(c_22, plain, (![B_18, A_19]: (k3_xboole_0(B_18, A_19)=k3_xboole_0(A_19, B_18))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.83/1.16  tff(c_4, plain, (![A_3, B_4]: (r1_tarski(k3_xboole_0(A_3, B_4), A_3))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.83/1.16  tff(c_37, plain, (![B_18, A_19]: (r1_tarski(k3_xboole_0(B_18, A_19), A_19))), inference(superposition, [status(thm), theory('equality')], [c_22, c_4])).
% 1.83/1.16  tff(c_12, plain, (![A_12, B_14]: (r1_tarski(k2_relat_1(A_12), k2_relat_1(B_14)) | ~r1_tarski(A_12, B_14) | ~v1_relat_1(B_14) | ~v1_relat_1(A_12))), inference(cnfTransformation, [status(thm)], [f_52])).
% 1.83/1.16  tff(c_20, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_60])).
% 1.83/1.16  tff(c_94, plain, (![A_28, B_29, C_30]: (r1_tarski(A_28, k3_xboole_0(B_29, C_30)) | ~r1_tarski(A_28, C_30) | ~r1_tarski(A_28, B_29))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.83/1.16  tff(c_16, plain, (~r1_tarski(k2_relat_1(k3_xboole_0('#skF_1', '#skF_2')), k3_xboole_0(k2_relat_1('#skF_1'), k2_relat_1('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_60])).
% 1.83/1.16  tff(c_104, plain, (~r1_tarski(k2_relat_1(k3_xboole_0('#skF_1', '#skF_2')), k2_relat_1('#skF_2')) | ~r1_tarski(k2_relat_1(k3_xboole_0('#skF_1', '#skF_2')), k2_relat_1('#skF_1'))), inference(resolution, [status(thm)], [c_94, c_16])).
% 1.83/1.16  tff(c_107, plain, (~r1_tarski(k2_relat_1(k3_xboole_0('#skF_1', '#skF_2')), k2_relat_1('#skF_1'))), inference(splitLeft, [status(thm)], [c_104])).
% 1.83/1.16  tff(c_110, plain, (~r1_tarski(k3_xboole_0('#skF_1', '#skF_2'), '#skF_1') | ~v1_relat_1('#skF_1') | ~v1_relat_1(k3_xboole_0('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_12, c_107])).
% 1.83/1.16  tff(c_113, plain, (~v1_relat_1(k3_xboole_0('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_4, c_110])).
% 1.83/1.16  tff(c_116, plain, (~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_76, c_113])).
% 1.83/1.16  tff(c_123, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_18, c_116])).
% 1.83/1.16  tff(c_124, plain, (~r1_tarski(k2_relat_1(k3_xboole_0('#skF_1', '#skF_2')), k2_relat_1('#skF_2'))), inference(splitRight, [status(thm)], [c_104])).
% 1.83/1.16  tff(c_128, plain, (~r1_tarski(k3_xboole_0('#skF_1', '#skF_2'), '#skF_2') | ~v1_relat_1('#skF_2') | ~v1_relat_1(k3_xboole_0('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_12, c_124])).
% 1.83/1.16  tff(c_131, plain, (~v1_relat_1(k3_xboole_0('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_37, c_128])).
% 1.83/1.16  tff(c_134, plain, (~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_76, c_131])).
% 1.83/1.16  tff(c_141, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_18, c_134])).
% 1.83/1.16  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.83/1.16  
% 1.83/1.16  Inference rules
% 1.83/1.16  ----------------------
% 1.83/1.16  #Ref     : 0
% 1.83/1.16  #Sup     : 27
% 1.83/1.16  #Fact    : 0
% 1.83/1.16  #Define  : 0
% 1.83/1.16  #Split   : 1
% 1.83/1.16  #Chain   : 0
% 1.83/1.16  #Close   : 0
% 1.83/1.16  
% 1.83/1.16  Ordering : KBO
% 1.83/1.16  
% 1.83/1.16  Simplification rules
% 1.83/1.16  ----------------------
% 1.83/1.16  #Subsume      : 5
% 1.83/1.16  #Demod        : 9
% 1.83/1.16  #Tautology    : 13
% 1.83/1.16  #SimpNegUnit  : 0
% 1.83/1.16  #BackRed      : 0
% 1.83/1.16  
% 1.83/1.16  #Partial instantiations: 0
% 1.83/1.16  #Strategies tried      : 1
% 1.83/1.16  
% 1.83/1.16  Timing (in seconds)
% 1.83/1.16  ----------------------
% 1.83/1.16  Preprocessing        : 0.26
% 1.83/1.16  Parsing              : 0.15
% 1.83/1.16  CNF conversion       : 0.02
% 1.83/1.16  Main loop            : 0.14
% 1.83/1.16  Inferencing          : 0.05
% 1.83/1.16  Reduction            : 0.05
% 1.83/1.16  Demodulation         : 0.04
% 1.83/1.17  BG Simplification    : 0.01
% 1.83/1.17  Subsumption          : 0.03
% 1.83/1.17  Abstraction          : 0.01
% 1.83/1.17  MUC search           : 0.00
% 1.83/1.17  Cooper               : 0.00
% 1.83/1.17  Total                : 0.43
% 1.83/1.17  Index Insertion      : 0.00
% 1.83/1.17  Index Deletion       : 0.00
% 1.83/1.17  Index Matching       : 0.00
% 1.83/1.17  BG Taut test         : 0.00
%------------------------------------------------------------------------------
