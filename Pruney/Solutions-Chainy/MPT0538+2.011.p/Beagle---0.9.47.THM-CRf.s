%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:00:24 EST 2020

% Result     : Theorem 1.68s
% Output     : CNFRefutation 1.86s
% Verified   : 
% Statistics : Number of formulae       :   43 (  73 expanded)
%              Number of leaves         :   23 (  34 expanded)
%              Depth                    :   10
%              Number of atoms          :   53 ( 102 expanded)
%              Number of equality atoms :   15 (  24 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_xboole_0 > v1_relat_1 > k8_relat_1 > #nlpp > k2_relat_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k8_relat_1,type,(
    k8_relat_1: ( $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(f_39,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_49,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relat_1)).

tff(f_41,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_53,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_xboole_0(k2_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc11_relat_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_45,axiom,(
    ! [A] :
      ( r1_tarski(A,k1_xboole_0)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).

tff(f_57,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k8_relat_1(k2_relat_1(A),A) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t126_relat_1)).

tff(f_63,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r1_tarski(A,B)
       => k8_relat_1(B,k8_relat_1(A,C)) = k8_relat_1(A,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t129_relat_1)).

tff(f_66,negated_conjecture,(
    ~ ! [A] : k8_relat_1(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t138_relat_1)).

tff(c_12,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_28,plain,(
    ! [A_19] :
      ( v1_relat_1(A_19)
      | ~ v1_xboole_0(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_32,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_12,c_28])).

tff(c_14,plain,(
    ! [A_10] : r1_tarski(k1_xboole_0,A_10) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_20,plain,(
    ! [A_13] :
      ( v1_xboole_0(k2_relat_1(A_13))
      | ~ v1_xboole_0(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_62,plain,(
    ! [A_29,B_30] :
      ( r2_hidden('#skF_2'(A_29,B_30),A_29)
      | r1_tarski(A_29,B_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_79,plain,(
    ! [A_32,B_33] :
      ( ~ v1_xboole_0(A_32)
      | r1_tarski(A_32,B_33) ) ),
    inference(resolution,[status(thm)],[c_62,c_2])).

tff(c_16,plain,(
    ! [A_11] :
      ( k1_xboole_0 = A_11
      | ~ r1_tarski(A_11,k1_xboole_0) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_92,plain,(
    ! [A_37] :
      ( k1_xboole_0 = A_37
      | ~ v1_xboole_0(A_37) ) ),
    inference(resolution,[status(thm)],[c_79,c_16])).

tff(c_102,plain,(
    ! [A_38] :
      ( k2_relat_1(A_38) = k1_xboole_0
      | ~ v1_xboole_0(A_38) ) ),
    inference(resolution,[status(thm)],[c_20,c_92])).

tff(c_110,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_12,c_102])).

tff(c_22,plain,(
    ! [A_14] :
      ( k8_relat_1(k2_relat_1(A_14),A_14) = A_14
      | ~ v1_relat_1(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_114,plain,
    ( k8_relat_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_110,c_22])).

tff(c_124,plain,(
    k8_relat_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_114])).

tff(c_24,plain,(
    ! [B_16,A_15,C_17] :
      ( k8_relat_1(B_16,k8_relat_1(A_15,C_17)) = k8_relat_1(A_15,C_17)
      | ~ r1_tarski(A_15,B_16)
      | ~ v1_relat_1(C_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_161,plain,(
    ! [B_16] :
      ( k8_relat_1(k1_xboole_0,k1_xboole_0) = k8_relat_1(B_16,k1_xboole_0)
      | ~ r1_tarski(k1_xboole_0,B_16)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_124,c_24])).

tff(c_165,plain,(
    ! [B_16] : k8_relat_1(B_16,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_14,c_124,c_161])).

tff(c_26,plain,(
    k8_relat_1('#skF_3',k1_xboole_0) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_170,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_165,c_26])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n003.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 21:04:27 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.68/1.14  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.86/1.15  
% 1.86/1.15  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.86/1.15  %$ r2_hidden > r1_tarski > v1_xboole_0 > v1_relat_1 > k8_relat_1 > #nlpp > k2_relat_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2
% 1.86/1.15  
% 1.86/1.15  %Foreground sorts:
% 1.86/1.15  
% 1.86/1.15  
% 1.86/1.15  %Background operators:
% 1.86/1.15  
% 1.86/1.15  
% 1.86/1.15  %Foreground operators:
% 1.86/1.15  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 1.86/1.15  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.86/1.15  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.86/1.15  tff('#skF_1', type, '#skF_1': $i > $i).
% 1.86/1.15  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.86/1.15  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.86/1.15  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.86/1.15  tff('#skF_3', type, '#skF_3': $i).
% 1.86/1.15  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.86/1.15  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.86/1.15  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.86/1.15  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 1.86/1.15  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.86/1.15  
% 1.86/1.16  tff(f_39, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 1.86/1.16  tff(f_49, axiom, (![A]: (v1_xboole_0(A) => v1_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relat_1)).
% 1.86/1.16  tff(f_41, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 1.86/1.16  tff(f_53, axiom, (![A]: (v1_xboole_0(A) => v1_xboole_0(k2_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc11_relat_1)).
% 1.86/1.16  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 1.86/1.16  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 1.86/1.16  tff(f_45, axiom, (![A]: (r1_tarski(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_1)).
% 1.86/1.16  tff(f_57, axiom, (![A]: (v1_relat_1(A) => (k8_relat_1(k2_relat_1(A), A) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t126_relat_1)).
% 1.86/1.16  tff(f_63, axiom, (![A, B, C]: (v1_relat_1(C) => (r1_tarski(A, B) => (k8_relat_1(B, k8_relat_1(A, C)) = k8_relat_1(A, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t129_relat_1)).
% 1.86/1.16  tff(f_66, negated_conjecture, ~(![A]: (k8_relat_1(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t138_relat_1)).
% 1.86/1.16  tff(c_12, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.86/1.16  tff(c_28, plain, (![A_19]: (v1_relat_1(A_19) | ~v1_xboole_0(A_19))), inference(cnfTransformation, [status(thm)], [f_49])).
% 1.86/1.16  tff(c_32, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_12, c_28])).
% 1.86/1.16  tff(c_14, plain, (![A_10]: (r1_tarski(k1_xboole_0, A_10))), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.86/1.16  tff(c_20, plain, (![A_13]: (v1_xboole_0(k2_relat_1(A_13)) | ~v1_xboole_0(A_13))), inference(cnfTransformation, [status(thm)], [f_53])).
% 1.86/1.16  tff(c_62, plain, (![A_29, B_30]: (r2_hidden('#skF_2'(A_29, B_30), A_29) | r1_tarski(A_29, B_30))), inference(cnfTransformation, [status(thm)], [f_38])).
% 1.86/1.16  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.86/1.16  tff(c_79, plain, (![A_32, B_33]: (~v1_xboole_0(A_32) | r1_tarski(A_32, B_33))), inference(resolution, [status(thm)], [c_62, c_2])).
% 1.86/1.16  tff(c_16, plain, (![A_11]: (k1_xboole_0=A_11 | ~r1_tarski(A_11, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.86/1.16  tff(c_92, plain, (![A_37]: (k1_xboole_0=A_37 | ~v1_xboole_0(A_37))), inference(resolution, [status(thm)], [c_79, c_16])).
% 1.86/1.16  tff(c_102, plain, (![A_38]: (k2_relat_1(A_38)=k1_xboole_0 | ~v1_xboole_0(A_38))), inference(resolution, [status(thm)], [c_20, c_92])).
% 1.86/1.16  tff(c_110, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_12, c_102])).
% 1.86/1.16  tff(c_22, plain, (![A_14]: (k8_relat_1(k2_relat_1(A_14), A_14)=A_14 | ~v1_relat_1(A_14))), inference(cnfTransformation, [status(thm)], [f_57])).
% 1.86/1.16  tff(c_114, plain, (k8_relat_1(k1_xboole_0, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_110, c_22])).
% 1.86/1.16  tff(c_124, plain, (k8_relat_1(k1_xboole_0, k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_32, c_114])).
% 1.86/1.16  tff(c_24, plain, (![B_16, A_15, C_17]: (k8_relat_1(B_16, k8_relat_1(A_15, C_17))=k8_relat_1(A_15, C_17) | ~r1_tarski(A_15, B_16) | ~v1_relat_1(C_17))), inference(cnfTransformation, [status(thm)], [f_63])).
% 1.86/1.16  tff(c_161, plain, (![B_16]: (k8_relat_1(k1_xboole_0, k1_xboole_0)=k8_relat_1(B_16, k1_xboole_0) | ~r1_tarski(k1_xboole_0, B_16) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_124, c_24])).
% 1.86/1.16  tff(c_165, plain, (![B_16]: (k8_relat_1(B_16, k1_xboole_0)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_32, c_14, c_124, c_161])).
% 1.86/1.16  tff(c_26, plain, (k8_relat_1('#skF_3', k1_xboole_0)!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_66])).
% 1.86/1.16  tff(c_170, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_165, c_26])).
% 1.86/1.16  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.86/1.16  
% 1.86/1.16  Inference rules
% 1.86/1.16  ----------------------
% 1.86/1.16  #Ref     : 0
% 1.86/1.16  #Sup     : 31
% 1.86/1.16  #Fact    : 0
% 1.86/1.16  #Define  : 0
% 1.86/1.16  #Split   : 0
% 1.86/1.16  #Chain   : 0
% 1.86/1.16  #Close   : 0
% 1.86/1.16  
% 1.86/1.16  Ordering : KBO
% 1.86/1.16  
% 1.86/1.16  Simplification rules
% 1.86/1.16  ----------------------
% 1.86/1.16  #Subsume      : 0
% 1.86/1.16  #Demod        : 10
% 1.86/1.16  #Tautology    : 17
% 1.86/1.16  #SimpNegUnit  : 0
% 1.86/1.16  #BackRed      : 1
% 1.86/1.16  
% 1.86/1.16  #Partial instantiations: 0
% 1.86/1.16  #Strategies tried      : 1
% 1.86/1.16  
% 1.86/1.16  Timing (in seconds)
% 1.86/1.16  ----------------------
% 1.86/1.17  Preprocessing        : 0.27
% 1.86/1.17  Parsing              : 0.15
% 1.86/1.17  CNF conversion       : 0.02
% 1.86/1.17  Main loop            : 0.15
% 1.86/1.17  Inferencing          : 0.07
% 1.86/1.17  Reduction            : 0.04
% 1.86/1.17  Demodulation         : 0.03
% 1.86/1.17  BG Simplification    : 0.01
% 1.86/1.17  Subsumption          : 0.02
% 1.86/1.17  Abstraction          : 0.01
% 1.86/1.17  MUC search           : 0.00
% 1.86/1.17  Cooper               : 0.00
% 1.86/1.17  Total                : 0.44
% 1.86/1.17  Index Insertion      : 0.00
% 1.86/1.17  Index Deletion       : 0.00
% 1.86/1.17  Index Matching       : 0.00
% 1.86/1.17  BG Taut test         : 0.00
%------------------------------------------------------------------------------
