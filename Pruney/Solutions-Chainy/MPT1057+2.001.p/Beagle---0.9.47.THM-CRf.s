%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:17:21 EST 2020

% Result     : Theorem 1.99s
% Output     : CNFRefutation 1.99s
% Verified   : 
% Statistics : Number of formulae       :   36 (  42 expanded)
%              Number of leaves         :   19 (  23 expanded)
%              Depth                    :    9
%              Number of atoms          :   42 (  59 expanded)
%              Number of equality atoms :   17 (  22 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > v1_funct_1 > k9_relat_1 > k7_relat_1 > k3_xboole_0 > #nlpp > k2_relat_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

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

tff(f_53,negated_conjecture,(
    ~ ! [A] :
        ( ( v1_relat_1(A)
          & v1_funct_1(A) )
       => ! [B,C] :
            ( r1_tarski(C,B)
           => k9_relat_1(A,C) = k9_relat_1(k7_relat_1(A,B),C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t174_funct_2)).

tff(f_43,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k7_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k7_relat_1(k7_relat_1(C,A),B) = k7_relat_1(C,k3_xboole_0(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_relat_1)).

tff(c_18,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_10,plain,(
    ! [B_11,A_10] :
      ( k2_relat_1(k7_relat_1(B_11,A_10)) = k9_relat_1(B_11,A_10)
      | ~ v1_relat_1(B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_6,plain,(
    ! [A_5,B_6] :
      ( v1_relat_1(k7_relat_1(A_5,B_6))
      | ~ v1_relat_1(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_14,plain,(
    r1_tarski('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_53,plain,(
    ! [A_18,B_19] :
      ( k3_xboole_0(A_18,B_19) = A_18
      | ~ r1_tarski(A_18,B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_57,plain,(
    k3_xboole_0('#skF_3','#skF_2') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_14,c_53])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_71,plain,(
    ! [C_22,A_23,B_24] :
      ( k7_relat_1(k7_relat_1(C_22,A_23),B_24) = k7_relat_1(C_22,k3_xboole_0(A_23,B_24))
      | ~ v1_relat_1(C_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_92,plain,(
    ! [C_25,A_26,B_27] :
      ( k2_relat_1(k7_relat_1(C_25,k3_xboole_0(A_26,B_27))) = k9_relat_1(k7_relat_1(C_25,A_26),B_27)
      | ~ v1_relat_1(k7_relat_1(C_25,A_26))
      | ~ v1_relat_1(C_25) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_71,c_10])).

tff(c_144,plain,(
    ! [C_30,A_31,B_32] :
      ( k2_relat_1(k7_relat_1(C_30,k3_xboole_0(A_31,B_32))) = k9_relat_1(k7_relat_1(C_30,B_32),A_31)
      | ~ v1_relat_1(k7_relat_1(C_30,B_32))
      | ~ v1_relat_1(C_30) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_92])).

tff(c_179,plain,(
    ! [C_33] :
      ( k9_relat_1(k7_relat_1(C_33,'#skF_2'),'#skF_3') = k2_relat_1(k7_relat_1(C_33,'#skF_3'))
      | ~ v1_relat_1(k7_relat_1(C_33,'#skF_2'))
      | ~ v1_relat_1(C_33) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_57,c_144])).

tff(c_251,plain,(
    ! [A_38] :
      ( k9_relat_1(k7_relat_1(A_38,'#skF_2'),'#skF_3') = k2_relat_1(k7_relat_1(A_38,'#skF_3'))
      | ~ v1_relat_1(A_38) ) ),
    inference(resolution,[status(thm)],[c_6,c_179])).

tff(c_12,plain,(
    k9_relat_1(k7_relat_1('#skF_1','#skF_2'),'#skF_3') != k9_relat_1('#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_257,plain,
    ( k2_relat_1(k7_relat_1('#skF_1','#skF_3')) != k9_relat_1('#skF_1','#skF_3')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_251,c_12])).

tff(c_271,plain,(
    k2_relat_1(k7_relat_1('#skF_1','#skF_3')) != k9_relat_1('#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_257])).

tff(c_275,plain,(
    ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_271])).

tff(c_279,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_275])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:54:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.99/1.28  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.99/1.28  
% 1.99/1.28  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.99/1.28  %$ r1_tarski > v1_relat_1 > v1_funct_1 > k9_relat_1 > k7_relat_1 > k3_xboole_0 > #nlpp > k2_relat_1 > #skF_2 > #skF_3 > #skF_1
% 1.99/1.28  
% 1.99/1.28  %Foreground sorts:
% 1.99/1.28  
% 1.99/1.28  
% 1.99/1.28  %Background operators:
% 1.99/1.28  
% 1.99/1.28  
% 1.99/1.28  %Foreground operators:
% 1.99/1.28  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 1.99/1.28  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.99/1.28  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 1.99/1.28  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.99/1.28  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.99/1.28  tff('#skF_2', type, '#skF_2': $i).
% 1.99/1.28  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 1.99/1.28  tff('#skF_3', type, '#skF_3': $i).
% 1.99/1.28  tff('#skF_1', type, '#skF_1': $i).
% 1.99/1.28  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.99/1.28  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.99/1.28  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.99/1.28  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.99/1.28  
% 1.99/1.29  tff(f_53, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B, C]: (r1_tarski(C, B) => (k9_relat_1(A, C) = k9_relat_1(k7_relat_1(A, B), C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t174_funct_2)).
% 1.99/1.29  tff(f_43, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_relat_1)).
% 1.99/1.29  tff(f_35, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k7_relat_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 1.99/1.29  tff(f_31, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 1.99/1.29  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 1.99/1.29  tff(f_39, axiom, (![A, B, C]: (v1_relat_1(C) => (k7_relat_1(k7_relat_1(C, A), B) = k7_relat_1(C, k3_xboole_0(A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_relat_1)).
% 1.99/1.29  tff(c_18, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_53])).
% 1.99/1.29  tff(c_10, plain, (![B_11, A_10]: (k2_relat_1(k7_relat_1(B_11, A_10))=k9_relat_1(B_11, A_10) | ~v1_relat_1(B_11))), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.99/1.29  tff(c_6, plain, (![A_5, B_6]: (v1_relat_1(k7_relat_1(A_5, B_6)) | ~v1_relat_1(A_5))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.99/1.29  tff(c_14, plain, (r1_tarski('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_53])).
% 1.99/1.29  tff(c_53, plain, (![A_18, B_19]: (k3_xboole_0(A_18, B_19)=A_18 | ~r1_tarski(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.99/1.29  tff(c_57, plain, (k3_xboole_0('#skF_3', '#skF_2')='#skF_3'), inference(resolution, [status(thm)], [c_14, c_53])).
% 1.99/1.29  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.99/1.29  tff(c_71, plain, (![C_22, A_23, B_24]: (k7_relat_1(k7_relat_1(C_22, A_23), B_24)=k7_relat_1(C_22, k3_xboole_0(A_23, B_24)) | ~v1_relat_1(C_22))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.99/1.29  tff(c_92, plain, (![C_25, A_26, B_27]: (k2_relat_1(k7_relat_1(C_25, k3_xboole_0(A_26, B_27)))=k9_relat_1(k7_relat_1(C_25, A_26), B_27) | ~v1_relat_1(k7_relat_1(C_25, A_26)) | ~v1_relat_1(C_25))), inference(superposition, [status(thm), theory('equality')], [c_71, c_10])).
% 1.99/1.29  tff(c_144, plain, (![C_30, A_31, B_32]: (k2_relat_1(k7_relat_1(C_30, k3_xboole_0(A_31, B_32)))=k9_relat_1(k7_relat_1(C_30, B_32), A_31) | ~v1_relat_1(k7_relat_1(C_30, B_32)) | ~v1_relat_1(C_30))), inference(superposition, [status(thm), theory('equality')], [c_2, c_92])).
% 1.99/1.29  tff(c_179, plain, (![C_33]: (k9_relat_1(k7_relat_1(C_33, '#skF_2'), '#skF_3')=k2_relat_1(k7_relat_1(C_33, '#skF_3')) | ~v1_relat_1(k7_relat_1(C_33, '#skF_2')) | ~v1_relat_1(C_33))), inference(superposition, [status(thm), theory('equality')], [c_57, c_144])).
% 1.99/1.29  tff(c_251, plain, (![A_38]: (k9_relat_1(k7_relat_1(A_38, '#skF_2'), '#skF_3')=k2_relat_1(k7_relat_1(A_38, '#skF_3')) | ~v1_relat_1(A_38))), inference(resolution, [status(thm)], [c_6, c_179])).
% 1.99/1.29  tff(c_12, plain, (k9_relat_1(k7_relat_1('#skF_1', '#skF_2'), '#skF_3')!=k9_relat_1('#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_53])).
% 1.99/1.29  tff(c_257, plain, (k2_relat_1(k7_relat_1('#skF_1', '#skF_3'))!=k9_relat_1('#skF_1', '#skF_3') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_251, c_12])).
% 1.99/1.29  tff(c_271, plain, (k2_relat_1(k7_relat_1('#skF_1', '#skF_3'))!=k9_relat_1('#skF_1', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_18, c_257])).
% 1.99/1.29  tff(c_275, plain, (~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_10, c_271])).
% 1.99/1.29  tff(c_279, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_18, c_275])).
% 1.99/1.29  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.99/1.29  
% 1.99/1.29  Inference rules
% 1.99/1.29  ----------------------
% 1.99/1.29  #Ref     : 0
% 1.99/1.29  #Sup     : 67
% 1.99/1.29  #Fact    : 0
% 1.99/1.29  #Define  : 0
% 1.99/1.29  #Split   : 0
% 1.99/1.29  #Chain   : 0
% 1.99/1.29  #Close   : 0
% 1.99/1.29  
% 1.99/1.29  Ordering : KBO
% 1.99/1.29  
% 1.99/1.29  Simplification rules
% 1.99/1.29  ----------------------
% 1.99/1.29  #Subsume      : 6
% 1.99/1.29  #Demod        : 2
% 1.99/1.29  #Tautology    : 24
% 1.99/1.29  #SimpNegUnit  : 0
% 1.99/1.29  #BackRed      : 0
% 1.99/1.29  
% 1.99/1.29  #Partial instantiations: 0
% 1.99/1.29  #Strategies tried      : 1
% 1.99/1.29  
% 1.99/1.29  Timing (in seconds)
% 1.99/1.29  ----------------------
% 1.99/1.30  Preprocessing        : 0.28
% 1.99/1.30  Parsing              : 0.16
% 1.99/1.30  CNF conversion       : 0.02
% 1.99/1.30  Main loop            : 0.23
% 1.99/1.30  Inferencing          : 0.10
% 1.99/1.30  Reduction            : 0.06
% 1.99/1.30  Demodulation         : 0.05
% 1.99/1.30  BG Simplification    : 0.02
% 1.99/1.30  Subsumption          : 0.04
% 1.99/1.30  Abstraction          : 0.01
% 1.99/1.30  MUC search           : 0.00
% 1.99/1.30  Cooper               : 0.00
% 1.99/1.30  Total                : 0.53
% 1.99/1.30  Index Insertion      : 0.00
% 1.99/1.30  Index Deletion       : 0.00
% 1.99/1.30  Index Matching       : 0.00
% 1.99/1.30  BG Taut test         : 0.00
%------------------------------------------------------------------------------
