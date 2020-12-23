%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:58:40 EST 2020

% Result     : Theorem 1.91s
% Output     : CNFRefutation 1.91s
% Verified   : 
% Statistics : Number of formulae       :   42 (  71 expanded)
%              Number of leaves         :   17 (  31 expanded)
%              Depth                    :    7
%              Number of atoms          :   53 ( 107 expanded)
%              Number of equality atoms :    4 (  14 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k4_xboole_0 > k3_xboole_0 > #nlpp > k3_relat_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

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

tff(f_58,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ! [B] :
            ( v1_relat_1(B)
           => r1_tarski(k3_relat_1(k3_xboole_0(A,B)),k3_xboole_0(k3_relat_1(A),k3_relat_1(B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_relat_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_37,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k4_xboole_0(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_relat_1)).

tff(f_35,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_50,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(A,B)
           => r1_tarski(k3_relat_1(A),k3_relat_1(B)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_relat_1)).

tff(f_33,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(A,C) )
     => r1_tarski(A,k3_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_xboole_1)).

tff(c_16,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_54,plain,(
    ! [A_22,B_23] : k4_xboole_0(A_22,k4_xboole_0(A_22,B_23)) = k3_xboole_0(A_22,B_23) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_10,plain,(
    ! [A_10,B_11] :
      ( v1_relat_1(k4_xboole_0(A_10,B_11))
      | ~ v1_relat_1(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_92,plain,(
    ! [A_28,B_29] :
      ( v1_relat_1(k3_xboole_0(A_28,B_29))
      | ~ v1_relat_1(A_28) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_54,c_10])).

tff(c_95,plain,(
    ! [B_2,A_1] :
      ( v1_relat_1(k3_xboole_0(B_2,A_1))
      | ~ v1_relat_1(A_1) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_92])).

tff(c_6,plain,(
    ! [A_6,B_7] : r1_tarski(k4_xboole_0(A_6,B_7),A_6) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_75,plain,(
    ! [A_24,B_25] : r1_tarski(k3_xboole_0(A_24,B_25),A_24) ),
    inference(superposition,[status(thm),theory(equality)],[c_54,c_6])).

tff(c_78,plain,(
    ! [B_2,A_1] : r1_tarski(k3_xboole_0(B_2,A_1),A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_75])).

tff(c_12,plain,(
    ! [A_12,B_14] :
      ( r1_tarski(k3_relat_1(A_12),k3_relat_1(B_14))
      | ~ r1_tarski(A_12,B_14)
      | ~ v1_relat_1(B_14)
      | ~ v1_relat_1(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_18,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_66,plain,(
    ! [A_22,B_23] : r1_tarski(k3_xboole_0(A_22,B_23),A_22) ),
    inference(superposition,[status(thm),theory(equality)],[c_54,c_6])).

tff(c_132,plain,(
    ! [A_34,B_35,C_36] :
      ( r1_tarski(A_34,k3_xboole_0(B_35,C_36))
      | ~ r1_tarski(A_34,C_36)
      | ~ r1_tarski(A_34,B_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_14,plain,(
    ~ r1_tarski(k3_relat_1(k3_xboole_0('#skF_1','#skF_2')),k3_xboole_0(k3_relat_1('#skF_1'),k3_relat_1('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_142,plain,
    ( ~ r1_tarski(k3_relat_1(k3_xboole_0('#skF_1','#skF_2')),k3_relat_1('#skF_2'))
    | ~ r1_tarski(k3_relat_1(k3_xboole_0('#skF_1','#skF_2')),k3_relat_1('#skF_1')) ),
    inference(resolution,[status(thm)],[c_132,c_14])).

tff(c_182,plain,(
    ~ r1_tarski(k3_relat_1(k3_xboole_0('#skF_1','#skF_2')),k3_relat_1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_142])).

tff(c_185,plain,
    ( ~ r1_tarski(k3_xboole_0('#skF_1','#skF_2'),'#skF_1')
    | ~ v1_relat_1('#skF_1')
    | ~ v1_relat_1(k3_xboole_0('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_12,c_182])).

tff(c_188,plain,(
    ~ v1_relat_1(k3_xboole_0('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_66,c_185])).

tff(c_191,plain,(
    ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_95,c_188])).

tff(c_198,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_191])).

tff(c_199,plain,(
    ~ r1_tarski(k3_relat_1(k3_xboole_0('#skF_1','#skF_2')),k3_relat_1('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_142])).

tff(c_203,plain,
    ( ~ r1_tarski(k3_xboole_0('#skF_1','#skF_2'),'#skF_2')
    | ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1(k3_xboole_0('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_12,c_199])).

tff(c_206,plain,(
    ~ v1_relat_1(k3_xboole_0('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_78,c_203])).

tff(c_209,plain,(
    ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_95,c_206])).

tff(c_216,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_209])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:32:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.91/1.29  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.91/1.29  
% 1.91/1.29  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.91/1.29  %$ r1_tarski > v1_relat_1 > k4_xboole_0 > k3_xboole_0 > #nlpp > k3_relat_1 > #skF_2 > #skF_1
% 1.91/1.29  
% 1.91/1.29  %Foreground sorts:
% 1.91/1.29  
% 1.91/1.29  
% 1.91/1.29  %Background operators:
% 1.91/1.29  
% 1.91/1.29  
% 1.91/1.29  %Foreground operators:
% 1.91/1.29  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.91/1.29  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.91/1.29  tff(k3_relat_1, type, k3_relat_1: $i > $i).
% 1.91/1.29  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.91/1.29  tff('#skF_2', type, '#skF_2': $i).
% 1.91/1.29  tff('#skF_1', type, '#skF_1': $i).
% 1.91/1.29  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.91/1.29  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.91/1.29  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.91/1.29  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.91/1.29  
% 1.91/1.30  tff(f_58, negated_conjecture, ~(![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => r1_tarski(k3_relat_1(k3_xboole_0(A, B)), k3_xboole_0(k3_relat_1(A), k3_relat_1(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t34_relat_1)).
% 1.91/1.30  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 1.91/1.30  tff(f_37, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 1.91/1.30  tff(f_41, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k4_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_relat_1)).
% 1.91/1.30  tff(f_35, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 1.91/1.30  tff(f_50, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(A, B) => r1_tarski(k3_relat_1(A), k3_relat_1(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_relat_1)).
% 1.91/1.30  tff(f_33, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(A, C)) => r1_tarski(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t19_xboole_1)).
% 1.91/1.30  tff(c_16, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_58])).
% 1.91/1.30  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.91/1.30  tff(c_54, plain, (![A_22, B_23]: (k4_xboole_0(A_22, k4_xboole_0(A_22, B_23))=k3_xboole_0(A_22, B_23))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.91/1.30  tff(c_10, plain, (![A_10, B_11]: (v1_relat_1(k4_xboole_0(A_10, B_11)) | ~v1_relat_1(A_10))), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.91/1.30  tff(c_92, plain, (![A_28, B_29]: (v1_relat_1(k3_xboole_0(A_28, B_29)) | ~v1_relat_1(A_28))), inference(superposition, [status(thm), theory('equality')], [c_54, c_10])).
% 1.91/1.30  tff(c_95, plain, (![B_2, A_1]: (v1_relat_1(k3_xboole_0(B_2, A_1)) | ~v1_relat_1(A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_92])).
% 1.91/1.30  tff(c_6, plain, (![A_6, B_7]: (r1_tarski(k4_xboole_0(A_6, B_7), A_6))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.91/1.30  tff(c_75, plain, (![A_24, B_25]: (r1_tarski(k3_xboole_0(A_24, B_25), A_24))), inference(superposition, [status(thm), theory('equality')], [c_54, c_6])).
% 1.91/1.30  tff(c_78, plain, (![B_2, A_1]: (r1_tarski(k3_xboole_0(B_2, A_1), A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_75])).
% 1.91/1.30  tff(c_12, plain, (![A_12, B_14]: (r1_tarski(k3_relat_1(A_12), k3_relat_1(B_14)) | ~r1_tarski(A_12, B_14) | ~v1_relat_1(B_14) | ~v1_relat_1(A_12))), inference(cnfTransformation, [status(thm)], [f_50])).
% 1.91/1.30  tff(c_18, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_58])).
% 1.91/1.30  tff(c_66, plain, (![A_22, B_23]: (r1_tarski(k3_xboole_0(A_22, B_23), A_22))), inference(superposition, [status(thm), theory('equality')], [c_54, c_6])).
% 1.91/1.30  tff(c_132, plain, (![A_34, B_35, C_36]: (r1_tarski(A_34, k3_xboole_0(B_35, C_36)) | ~r1_tarski(A_34, C_36) | ~r1_tarski(A_34, B_35))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.91/1.30  tff(c_14, plain, (~r1_tarski(k3_relat_1(k3_xboole_0('#skF_1', '#skF_2')), k3_xboole_0(k3_relat_1('#skF_1'), k3_relat_1('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_58])).
% 1.91/1.30  tff(c_142, plain, (~r1_tarski(k3_relat_1(k3_xboole_0('#skF_1', '#skF_2')), k3_relat_1('#skF_2')) | ~r1_tarski(k3_relat_1(k3_xboole_0('#skF_1', '#skF_2')), k3_relat_1('#skF_1'))), inference(resolution, [status(thm)], [c_132, c_14])).
% 1.91/1.30  tff(c_182, plain, (~r1_tarski(k3_relat_1(k3_xboole_0('#skF_1', '#skF_2')), k3_relat_1('#skF_1'))), inference(splitLeft, [status(thm)], [c_142])).
% 1.91/1.30  tff(c_185, plain, (~r1_tarski(k3_xboole_0('#skF_1', '#skF_2'), '#skF_1') | ~v1_relat_1('#skF_1') | ~v1_relat_1(k3_xboole_0('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_12, c_182])).
% 1.91/1.30  tff(c_188, plain, (~v1_relat_1(k3_xboole_0('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_66, c_185])).
% 1.91/1.30  tff(c_191, plain, (~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_95, c_188])).
% 1.91/1.30  tff(c_198, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_16, c_191])).
% 1.91/1.30  tff(c_199, plain, (~r1_tarski(k3_relat_1(k3_xboole_0('#skF_1', '#skF_2')), k3_relat_1('#skF_2'))), inference(splitRight, [status(thm)], [c_142])).
% 1.91/1.30  tff(c_203, plain, (~r1_tarski(k3_xboole_0('#skF_1', '#skF_2'), '#skF_2') | ~v1_relat_1('#skF_2') | ~v1_relat_1(k3_xboole_0('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_12, c_199])).
% 1.91/1.30  tff(c_206, plain, (~v1_relat_1(k3_xboole_0('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_78, c_203])).
% 1.91/1.30  tff(c_209, plain, (~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_95, c_206])).
% 1.91/1.30  tff(c_216, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_16, c_209])).
% 1.91/1.30  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.91/1.30  
% 1.91/1.30  Inference rules
% 1.91/1.30  ----------------------
% 1.91/1.30  #Ref     : 0
% 1.91/1.30  #Sup     : 47
% 1.91/1.30  #Fact    : 0
% 1.91/1.30  #Define  : 0
% 1.91/1.30  #Split   : 1
% 1.91/1.30  #Chain   : 0
% 1.91/1.30  #Close   : 0
% 1.91/1.30  
% 1.91/1.30  Ordering : KBO
% 1.91/1.30  
% 1.91/1.30  Simplification rules
% 1.91/1.30  ----------------------
% 1.91/1.30  #Subsume      : 7
% 1.91/1.30  #Demod        : 15
% 1.91/1.30  #Tautology    : 25
% 1.91/1.30  #SimpNegUnit  : 0
% 1.91/1.30  #BackRed      : 0
% 1.91/1.30  
% 1.91/1.30  #Partial instantiations: 0
% 1.91/1.30  #Strategies tried      : 1
% 1.91/1.30  
% 1.91/1.30  Timing (in seconds)
% 1.91/1.30  ----------------------
% 1.91/1.31  Preprocessing        : 0.29
% 1.91/1.31  Parsing              : 0.16
% 1.91/1.31  CNF conversion       : 0.02
% 1.91/1.31  Main loop            : 0.18
% 1.91/1.31  Inferencing          : 0.06
% 1.91/1.31  Reduction            : 0.07
% 1.91/1.31  Demodulation         : 0.06
% 1.91/1.31  BG Simplification    : 0.01
% 1.91/1.31  Subsumption          : 0.03
% 1.91/1.31  Abstraction          : 0.01
% 1.91/1.31  MUC search           : 0.00
% 1.91/1.31  Cooper               : 0.00
% 1.91/1.31  Total                : 0.51
% 1.91/1.31  Index Insertion      : 0.00
% 1.91/1.31  Index Deletion       : 0.00
% 1.91/1.31  Index Matching       : 0.00
% 1.91/1.31  BG Taut test         : 0.00
%------------------------------------------------------------------------------
