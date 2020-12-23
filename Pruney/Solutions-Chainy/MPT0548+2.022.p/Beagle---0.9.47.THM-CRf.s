%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:00:38 EST 2020

% Result     : Theorem 1.70s
% Output     : CNFRefutation 1.70s
% Verified   : 
% Statistics : Number of formulae       :   38 (  47 expanded)
%              Number of leaves         :   19 (  24 expanded)
%              Depth                    :    7
%              Number of atoms          :   45 (  57 expanded)
%              Number of equality atoms :   23 (  31 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k9_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_58,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_35,axiom,(
    ! [A] : v1_relat_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).

tff(f_54,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ( k1_relat_1(A) = k1_xboole_0
          | k2_relat_1(A) = k1_xboole_0 )
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).

tff(f_39,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k9_relat_1(A,k1_relat_1(A)) = k2_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_relat_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k9_relat_1(B,A),k9_relat_1(B,k1_relat_1(B))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t147_relat_1)).

tff(f_33,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_61,negated_conjecture,(
    ~ ! [A] : k9_relat_1(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t150_relat_1)).

tff(c_24,plain,(
    ! [A_9] : k1_relat_1(k6_relat_1(A_9)) = A_9 ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_10,plain,(
    ! [A_4] : v1_relat_1(k6_relat_1(A_4)) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_59,plain,(
    ! [A_15] :
      ( k1_relat_1(A_15) != k1_xboole_0
      | k1_xboole_0 = A_15
      | ~ v1_relat_1(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_62,plain,(
    ! [A_4] :
      ( k1_relat_1(k6_relat_1(A_4)) != k1_xboole_0
      | k6_relat_1(A_4) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_10,c_59])).

tff(c_71,plain,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_62])).

tff(c_26,plain,(
    ! [A_9] : k2_relat_1(k6_relat_1(A_9)) = A_9 ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_113,plain,(
    ! [A_18] :
      ( k9_relat_1(A_18,k1_relat_1(A_18)) = k2_relat_1(A_18)
      | ~ v1_relat_1(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_122,plain,(
    ! [A_9] :
      ( k9_relat_1(k6_relat_1(A_9),A_9) = k2_relat_1(k6_relat_1(A_9))
      | ~ v1_relat_1(k6_relat_1(A_9)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_113])).

tff(c_129,plain,(
    ! [A_9] : k9_relat_1(k6_relat_1(A_9),A_9) = A_9 ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_26,c_122])).

tff(c_198,plain,(
    ! [B_24,A_25] :
      ( r1_tarski(k9_relat_1(B_24,A_25),k9_relat_1(B_24,k1_relat_1(B_24)))
      | ~ v1_relat_1(B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_219,plain,(
    ! [A_9,A_25] :
      ( r1_tarski(k9_relat_1(k6_relat_1(A_9),A_25),k9_relat_1(k6_relat_1(A_9),A_9))
      | ~ v1_relat_1(k6_relat_1(A_9)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_198])).

tff(c_252,plain,(
    ! [A_27,A_28] : r1_tarski(k9_relat_1(k6_relat_1(A_27),A_28),A_27) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_129,c_219])).

tff(c_8,plain,(
    ! [A_3] : r1_tarski(k1_xboole_0,A_3) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_175,plain,(
    ! [B_21,A_22] :
      ( B_21 = A_22
      | ~ r1_tarski(B_21,A_22)
      | ~ r1_tarski(A_22,B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_184,plain,(
    ! [A_3] :
      ( k1_xboole_0 = A_3
      | ~ r1_tarski(A_3,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_8,c_175])).

tff(c_256,plain,(
    ! [A_28] : k9_relat_1(k6_relat_1(k1_xboole_0),A_28) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_252,c_184])).

tff(c_270,plain,(
    ! [A_28] : k9_relat_1(k1_xboole_0,A_28) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_71,c_256])).

tff(c_28,plain,(
    k9_relat_1(k1_xboole_0,'#skF_1') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_280,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_270,c_28])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:56:11 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.70/1.21  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.70/1.21  
% 1.70/1.21  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.70/1.21  %$ r1_tarski > v1_relat_1 > k9_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_1
% 1.70/1.21  
% 1.70/1.21  %Foreground sorts:
% 1.70/1.21  
% 1.70/1.21  
% 1.70/1.21  %Background operators:
% 1.70/1.21  
% 1.70/1.21  
% 1.70/1.21  %Foreground operators:
% 1.70/1.21  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.70/1.21  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.70/1.21  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.70/1.21  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.70/1.21  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 1.70/1.21  tff('#skF_1', type, '#skF_1': $i).
% 1.70/1.21  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.70/1.21  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.70/1.21  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 1.70/1.21  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.70/1.21  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.70/1.21  
% 1.70/1.22  tff(f_58, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 1.70/1.22  tff(f_35, axiom, (![A]: v1_relat_1(k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 1.70/1.22  tff(f_54, axiom, (![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_relat_1)).
% 1.70/1.22  tff(f_39, axiom, (![A]: (v1_relat_1(A) => (k9_relat_1(A, k1_relat_1(A)) = k2_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t146_relat_1)).
% 1.70/1.22  tff(f_43, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k9_relat_1(B, A), k9_relat_1(B, k1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t147_relat_1)).
% 1.70/1.22  tff(f_33, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 1.70/1.22  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 1.70/1.22  tff(f_61, negated_conjecture, ~(![A]: (k9_relat_1(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t150_relat_1)).
% 1.70/1.22  tff(c_24, plain, (![A_9]: (k1_relat_1(k6_relat_1(A_9))=A_9)), inference(cnfTransformation, [status(thm)], [f_58])).
% 1.70/1.22  tff(c_10, plain, (![A_4]: (v1_relat_1(k6_relat_1(A_4)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.70/1.22  tff(c_59, plain, (![A_15]: (k1_relat_1(A_15)!=k1_xboole_0 | k1_xboole_0=A_15 | ~v1_relat_1(A_15))), inference(cnfTransformation, [status(thm)], [f_54])).
% 1.70/1.22  tff(c_62, plain, (![A_4]: (k1_relat_1(k6_relat_1(A_4))!=k1_xboole_0 | k6_relat_1(A_4)=k1_xboole_0)), inference(resolution, [status(thm)], [c_10, c_59])).
% 1.70/1.22  tff(c_71, plain, (k6_relat_1(k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_24, c_62])).
% 1.70/1.22  tff(c_26, plain, (![A_9]: (k2_relat_1(k6_relat_1(A_9))=A_9)), inference(cnfTransformation, [status(thm)], [f_58])).
% 1.70/1.22  tff(c_113, plain, (![A_18]: (k9_relat_1(A_18, k1_relat_1(A_18))=k2_relat_1(A_18) | ~v1_relat_1(A_18))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.70/1.22  tff(c_122, plain, (![A_9]: (k9_relat_1(k6_relat_1(A_9), A_9)=k2_relat_1(k6_relat_1(A_9)) | ~v1_relat_1(k6_relat_1(A_9)))), inference(superposition, [status(thm), theory('equality')], [c_24, c_113])).
% 1.70/1.22  tff(c_129, plain, (![A_9]: (k9_relat_1(k6_relat_1(A_9), A_9)=A_9)), inference(demodulation, [status(thm), theory('equality')], [c_10, c_26, c_122])).
% 1.70/1.22  tff(c_198, plain, (![B_24, A_25]: (r1_tarski(k9_relat_1(B_24, A_25), k9_relat_1(B_24, k1_relat_1(B_24))) | ~v1_relat_1(B_24))), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.70/1.22  tff(c_219, plain, (![A_9, A_25]: (r1_tarski(k9_relat_1(k6_relat_1(A_9), A_25), k9_relat_1(k6_relat_1(A_9), A_9)) | ~v1_relat_1(k6_relat_1(A_9)))), inference(superposition, [status(thm), theory('equality')], [c_24, c_198])).
% 1.70/1.22  tff(c_252, plain, (![A_27, A_28]: (r1_tarski(k9_relat_1(k6_relat_1(A_27), A_28), A_27))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_129, c_219])).
% 1.70/1.22  tff(c_8, plain, (![A_3]: (r1_tarski(k1_xboole_0, A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.70/1.22  tff(c_175, plain, (![B_21, A_22]: (B_21=A_22 | ~r1_tarski(B_21, A_22) | ~r1_tarski(A_22, B_21))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.70/1.22  tff(c_184, plain, (![A_3]: (k1_xboole_0=A_3 | ~r1_tarski(A_3, k1_xboole_0))), inference(resolution, [status(thm)], [c_8, c_175])).
% 1.70/1.22  tff(c_256, plain, (![A_28]: (k9_relat_1(k6_relat_1(k1_xboole_0), A_28)=k1_xboole_0)), inference(resolution, [status(thm)], [c_252, c_184])).
% 1.70/1.22  tff(c_270, plain, (![A_28]: (k9_relat_1(k1_xboole_0, A_28)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_71, c_256])).
% 1.70/1.22  tff(c_28, plain, (k9_relat_1(k1_xboole_0, '#skF_1')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_61])).
% 1.70/1.22  tff(c_280, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_270, c_28])).
% 1.70/1.22  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.70/1.22  
% 1.70/1.22  Inference rules
% 1.70/1.22  ----------------------
% 1.70/1.22  #Ref     : 0
% 1.70/1.22  #Sup     : 52
% 1.70/1.22  #Fact    : 0
% 1.70/1.22  #Define  : 0
% 1.70/1.22  #Split   : 2
% 1.70/1.22  #Chain   : 0
% 1.70/1.22  #Close   : 0
% 1.70/1.22  
% 1.70/1.22  Ordering : KBO
% 1.70/1.22  
% 1.70/1.22  Simplification rules
% 1.70/1.22  ----------------------
% 1.70/1.22  #Subsume      : 5
% 1.70/1.22  #Demod        : 48
% 1.70/1.22  #Tautology    : 35
% 1.70/1.22  #SimpNegUnit  : 5
% 1.70/1.22  #BackRed      : 4
% 1.70/1.22  
% 1.70/1.22  #Partial instantiations: 0
% 1.70/1.22  #Strategies tried      : 1
% 1.70/1.22  
% 1.70/1.22  Timing (in seconds)
% 1.70/1.22  ----------------------
% 1.70/1.23  Preprocessing        : 0.28
% 1.70/1.23  Parsing              : 0.16
% 1.70/1.23  CNF conversion       : 0.02
% 1.70/1.23  Main loop            : 0.17
% 1.70/1.23  Inferencing          : 0.06
% 1.70/1.23  Reduction            : 0.05
% 1.70/1.23  Demodulation         : 0.04
% 1.70/1.23  BG Simplification    : 0.01
% 1.70/1.23  Subsumption          : 0.02
% 1.70/1.23  Abstraction          : 0.01
% 1.70/1.23  MUC search           : 0.00
% 1.70/1.23  Cooper               : 0.00
% 1.70/1.23  Total                : 0.47
% 1.70/1.23  Index Insertion      : 0.00
% 1.70/1.23  Index Deletion       : 0.00
% 1.70/1.23  Index Matching       : 0.00
% 1.70/1.23  BG Taut test         : 0.00
%------------------------------------------------------------------------------
