%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:59:33 EST 2020

% Result     : Theorem 1.67s
% Output     : CNFRefutation 1.67s
% Verified   : 
% Statistics : Number of formulae       :   31 (  39 expanded)
%              Number of leaves         :   16 (  21 expanded)
%              Depth                    :    8
%              Number of atoms          :   37 (  48 expanded)
%              Number of equality atoms :   13 (  19 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k5_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_relat_1 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

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

tff(f_53,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => k5_relat_1(A,k6_relat_1(k2_relat_1(A))) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t80_relat_1)).

tff(f_27,axiom,(
    ! [A] : v1_relat_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).

tff(f_38,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_42,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k5_relat_1(k6_relat_1(k1_relat_1(A)),A) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t78_relat_1)).

tff(f_34,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => r1_tarski(k2_relat_1(k5_relat_1(A,B)),k2_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_relat_1)).

tff(f_48,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k2_relat_1(B),A)
       => k5_relat_1(B,k6_relat_1(A)) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_relat_1)).

tff(c_16,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_2,plain,(
    ! [A_1] : v1_relat_1(k6_relat_1(A_1)) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_8,plain,(
    ! [A_5] : k2_relat_1(k6_relat_1(A_5)) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_6,plain,(
    ! [A_5] : k1_relat_1(k6_relat_1(A_5)) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_36,plain,(
    ! [A_12] :
      ( k5_relat_1(k6_relat_1(k1_relat_1(A_12)),A_12) = A_12
      | ~ v1_relat_1(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_45,plain,(
    ! [A_5] :
      ( k5_relat_1(k6_relat_1(A_5),k6_relat_1(A_5)) = k6_relat_1(A_5)
      | ~ v1_relat_1(k6_relat_1(A_5)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_36])).

tff(c_49,plain,(
    ! [A_5] : k5_relat_1(k6_relat_1(A_5),k6_relat_1(A_5)) = k6_relat_1(A_5) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_45])).

tff(c_59,plain,(
    ! [A_14,B_15] :
      ( r1_tarski(k2_relat_1(k5_relat_1(A_14,B_15)),k2_relat_1(B_15))
      | ~ v1_relat_1(B_15)
      | ~ v1_relat_1(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_62,plain,(
    ! [A_5] :
      ( r1_tarski(k2_relat_1(k6_relat_1(A_5)),k2_relat_1(k6_relat_1(A_5)))
      | ~ v1_relat_1(k6_relat_1(A_5))
      | ~ v1_relat_1(k6_relat_1(A_5)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_49,c_59])).

tff(c_70,plain,(
    ! [A_5] : r1_tarski(A_5,A_5) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_2,c_8,c_8,c_62])).

tff(c_76,plain,(
    ! [B_17,A_18] :
      ( k5_relat_1(B_17,k6_relat_1(A_18)) = B_17
      | ~ r1_tarski(k2_relat_1(B_17),A_18)
      | ~ v1_relat_1(B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_92,plain,(
    ! [B_19] :
      ( k5_relat_1(B_19,k6_relat_1(k2_relat_1(B_19))) = B_19
      | ~ v1_relat_1(B_19) ) ),
    inference(resolution,[status(thm)],[c_70,c_76])).

tff(c_14,plain,(
    k5_relat_1('#skF_1',k6_relat_1(k2_relat_1('#skF_1'))) != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_101,plain,(
    ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_92,c_14])).

tff(c_114,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_101])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:56:51 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.67/1.13  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.67/1.13  
% 1.67/1.13  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.67/1.13  %$ r1_tarski > v1_relat_1 > k5_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_relat_1 > #skF_1
% 1.67/1.13  
% 1.67/1.13  %Foreground sorts:
% 1.67/1.13  
% 1.67/1.13  
% 1.67/1.13  %Background operators:
% 1.67/1.13  
% 1.67/1.13  
% 1.67/1.13  %Foreground operators:
% 1.67/1.13  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.67/1.13  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 1.67/1.13  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.67/1.13  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.67/1.13  tff('#skF_1', type, '#skF_1': $i).
% 1.67/1.13  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.67/1.13  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.67/1.13  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 1.67/1.13  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.67/1.13  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.67/1.13  
% 1.67/1.14  tff(f_53, negated_conjecture, ~(![A]: (v1_relat_1(A) => (k5_relat_1(A, k6_relat_1(k2_relat_1(A))) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t80_relat_1)).
% 1.67/1.14  tff(f_27, axiom, (![A]: v1_relat_1(k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 1.67/1.14  tff(f_38, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 1.67/1.14  tff(f_42, axiom, (![A]: (v1_relat_1(A) => (k5_relat_1(k6_relat_1(k1_relat_1(A)), A) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t78_relat_1)).
% 1.67/1.14  tff(f_34, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => r1_tarski(k2_relat_1(k5_relat_1(A, B)), k2_relat_1(B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t45_relat_1)).
% 1.67/1.14  tff(f_48, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(B), A) => (k5_relat_1(B, k6_relat_1(A)) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_relat_1)).
% 1.67/1.14  tff(c_16, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_53])).
% 1.67/1.14  tff(c_2, plain, (![A_1]: (v1_relat_1(k6_relat_1(A_1)))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.67/1.14  tff(c_8, plain, (![A_5]: (k2_relat_1(k6_relat_1(A_5))=A_5)), inference(cnfTransformation, [status(thm)], [f_38])).
% 1.67/1.14  tff(c_6, plain, (![A_5]: (k1_relat_1(k6_relat_1(A_5))=A_5)), inference(cnfTransformation, [status(thm)], [f_38])).
% 1.67/1.14  tff(c_36, plain, (![A_12]: (k5_relat_1(k6_relat_1(k1_relat_1(A_12)), A_12)=A_12 | ~v1_relat_1(A_12))), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.67/1.14  tff(c_45, plain, (![A_5]: (k5_relat_1(k6_relat_1(A_5), k6_relat_1(A_5))=k6_relat_1(A_5) | ~v1_relat_1(k6_relat_1(A_5)))), inference(superposition, [status(thm), theory('equality')], [c_6, c_36])).
% 1.67/1.14  tff(c_49, plain, (![A_5]: (k5_relat_1(k6_relat_1(A_5), k6_relat_1(A_5))=k6_relat_1(A_5))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_45])).
% 1.67/1.14  tff(c_59, plain, (![A_14, B_15]: (r1_tarski(k2_relat_1(k5_relat_1(A_14, B_15)), k2_relat_1(B_15)) | ~v1_relat_1(B_15) | ~v1_relat_1(A_14))), inference(cnfTransformation, [status(thm)], [f_34])).
% 1.67/1.14  tff(c_62, plain, (![A_5]: (r1_tarski(k2_relat_1(k6_relat_1(A_5)), k2_relat_1(k6_relat_1(A_5))) | ~v1_relat_1(k6_relat_1(A_5)) | ~v1_relat_1(k6_relat_1(A_5)))), inference(superposition, [status(thm), theory('equality')], [c_49, c_59])).
% 1.67/1.14  tff(c_70, plain, (![A_5]: (r1_tarski(A_5, A_5))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_2, c_8, c_8, c_62])).
% 1.67/1.14  tff(c_76, plain, (![B_17, A_18]: (k5_relat_1(B_17, k6_relat_1(A_18))=B_17 | ~r1_tarski(k2_relat_1(B_17), A_18) | ~v1_relat_1(B_17))), inference(cnfTransformation, [status(thm)], [f_48])).
% 1.67/1.14  tff(c_92, plain, (![B_19]: (k5_relat_1(B_19, k6_relat_1(k2_relat_1(B_19)))=B_19 | ~v1_relat_1(B_19))), inference(resolution, [status(thm)], [c_70, c_76])).
% 1.67/1.14  tff(c_14, plain, (k5_relat_1('#skF_1', k6_relat_1(k2_relat_1('#skF_1')))!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_53])).
% 1.67/1.14  tff(c_101, plain, (~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_92, c_14])).
% 1.67/1.14  tff(c_114, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_16, c_101])).
% 1.67/1.14  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.67/1.14  
% 1.67/1.14  Inference rules
% 1.67/1.14  ----------------------
% 1.67/1.14  #Ref     : 0
% 1.67/1.14  #Sup     : 20
% 1.67/1.14  #Fact    : 0
% 1.67/1.14  #Define  : 0
% 1.67/1.14  #Split   : 0
% 1.67/1.14  #Chain   : 0
% 1.67/1.14  #Close   : 0
% 1.67/1.14  
% 1.67/1.14  Ordering : KBO
% 1.67/1.14  
% 1.67/1.14  Simplification rules
% 1.67/1.14  ----------------------
% 1.67/1.14  #Subsume      : 0
% 1.67/1.14  #Demod        : 13
% 1.67/1.14  #Tautology    : 11
% 1.67/1.14  #SimpNegUnit  : 0
% 1.67/1.14  #BackRed      : 0
% 1.67/1.14  
% 1.67/1.14  #Partial instantiations: 0
% 1.67/1.14  #Strategies tried      : 1
% 1.67/1.14  
% 1.67/1.14  Timing (in seconds)
% 1.67/1.14  ----------------------
% 1.67/1.15  Preprocessing        : 0.27
% 1.67/1.15  Parsing              : 0.15
% 1.67/1.15  CNF conversion       : 0.02
% 1.67/1.15  Main loop            : 0.12
% 1.67/1.15  Inferencing          : 0.05
% 1.67/1.15  Reduction            : 0.03
% 1.67/1.15  Demodulation         : 0.03
% 1.67/1.15  BG Simplification    : 0.01
% 1.67/1.15  Subsumption          : 0.02
% 1.67/1.15  Abstraction          : 0.01
% 1.67/1.15  MUC search           : 0.00
% 1.67/1.15  Cooper               : 0.00
% 1.67/1.15  Total                : 0.41
% 1.67/1.15  Index Insertion      : 0.00
% 1.67/1.15  Index Deletion       : 0.00
% 1.67/1.15  Index Matching       : 0.00
% 1.67/1.15  BG Taut test         : 0.00
%------------------------------------------------------------------------------
