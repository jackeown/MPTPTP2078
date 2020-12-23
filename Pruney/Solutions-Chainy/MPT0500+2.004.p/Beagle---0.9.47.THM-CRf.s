%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:59:47 EST 2020

% Result     : Theorem 2.14s
% Output     : CNFRefutation 2.16s
% Verified   : 
% Statistics : Number of formulae       :   26 (  27 expanded)
%              Number of leaves         :   15 (  16 expanded)
%              Depth                    :    6
%              Number of atoms          :   29 (  31 expanded)
%              Number of equality atoms :   10 (  11 expanded)
%              Maximal formula depth    :    6 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k7_relat_1 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_relat_1 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_46,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => k7_relat_1(A,k1_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_relat_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k1_relat_1(k7_relat_1(B,A)) = k3_xboole_0(k1_relat_1(B),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t90_relat_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,k2_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k1_relat_1(k7_relat_1(B,A)),k1_relat_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t89_relat_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k1_relat_1(B),A)
       => k7_relat_1(B,A) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t97_relat_1)).

tff(c_12,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_28,plain,(
    ! [B_15,A_16] :
      ( k3_xboole_0(k1_relat_1(B_15),A_16) = k1_relat_1(k7_relat_1(B_15,A_16))
      | ~ v1_relat_1(B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_2,plain,(
    ! [A_1,B_2] : k3_xboole_0(A_1,k2_xboole_0(A_1,B_2)) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_45,plain,(
    ! [B_17,B_18] :
      ( k1_relat_1(k7_relat_1(B_17,k2_xboole_0(k1_relat_1(B_17),B_18))) = k1_relat_1(B_17)
      | ~ v1_relat_1(B_17) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_2])).

tff(c_4,plain,(
    ! [B_4,A_3] :
      ( r1_tarski(k1_relat_1(k7_relat_1(B_4,A_3)),k1_relat_1(B_4))
      | ~ v1_relat_1(B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_72,plain,(
    ! [B_19] :
      ( r1_tarski(k1_relat_1(B_19),k1_relat_1(B_19))
      | ~ v1_relat_1(B_19)
      | ~ v1_relat_1(B_19) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_45,c_4])).

tff(c_8,plain,(
    ! [B_8,A_7] :
      ( k7_relat_1(B_8,A_7) = B_8
      | ~ r1_tarski(k1_relat_1(B_8),A_7)
      | ~ v1_relat_1(B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_83,plain,(
    ! [B_20] :
      ( k7_relat_1(B_20,k1_relat_1(B_20)) = B_20
      | ~ v1_relat_1(B_20) ) ),
    inference(resolution,[status(thm)],[c_72,c_8])).

tff(c_10,plain,(
    k7_relat_1('#skF_1',k1_relat_1('#skF_1')) != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_92,plain,(
    ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_83,c_10])).

tff(c_103,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_92])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:57:10 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.14/1.48  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.14/1.49  
% 2.14/1.49  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.14/1.49  %$ r1_tarski > v1_relat_1 > k7_relat_1 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_relat_1 > #skF_1
% 2.14/1.49  
% 2.14/1.49  %Foreground sorts:
% 2.14/1.49  
% 2.14/1.49  
% 2.14/1.49  %Background operators:
% 2.14/1.49  
% 2.14/1.49  
% 2.14/1.49  %Foreground operators:
% 2.14/1.49  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.14/1.49  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.14/1.49  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.14/1.49  tff('#skF_1', type, '#skF_1': $i).
% 2.14/1.49  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.14/1.49  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.14/1.49  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.14/1.49  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.14/1.49  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.14/1.49  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.14/1.49  
% 2.16/1.50  tff(f_46, negated_conjecture, ~(![A]: (v1_relat_1(A) => (k7_relat_1(A, k1_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_relat_1)).
% 2.16/1.50  tff(f_35, axiom, (![A, B]: (v1_relat_1(B) => (k1_relat_1(k7_relat_1(B, A)) = k3_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t90_relat_1)).
% 2.16/1.50  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, k2_xboole_0(A, B)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t21_xboole_1)).
% 2.16/1.50  tff(f_31, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k7_relat_1(B, A)), k1_relat_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t89_relat_1)).
% 2.16/1.50  tff(f_41, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(B), A) => (k7_relat_1(B, A) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t97_relat_1)).
% 2.16/1.50  tff(c_12, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.16/1.50  tff(c_28, plain, (![B_15, A_16]: (k3_xboole_0(k1_relat_1(B_15), A_16)=k1_relat_1(k7_relat_1(B_15, A_16)) | ~v1_relat_1(B_15))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.16/1.50  tff(c_2, plain, (![A_1, B_2]: (k3_xboole_0(A_1, k2_xboole_0(A_1, B_2))=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.16/1.50  tff(c_45, plain, (![B_17, B_18]: (k1_relat_1(k7_relat_1(B_17, k2_xboole_0(k1_relat_1(B_17), B_18)))=k1_relat_1(B_17) | ~v1_relat_1(B_17))), inference(superposition, [status(thm), theory('equality')], [c_28, c_2])).
% 2.16/1.50  tff(c_4, plain, (![B_4, A_3]: (r1_tarski(k1_relat_1(k7_relat_1(B_4, A_3)), k1_relat_1(B_4)) | ~v1_relat_1(B_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.16/1.50  tff(c_72, plain, (![B_19]: (r1_tarski(k1_relat_1(B_19), k1_relat_1(B_19)) | ~v1_relat_1(B_19) | ~v1_relat_1(B_19))), inference(superposition, [status(thm), theory('equality')], [c_45, c_4])).
% 2.16/1.50  tff(c_8, plain, (![B_8, A_7]: (k7_relat_1(B_8, A_7)=B_8 | ~r1_tarski(k1_relat_1(B_8), A_7) | ~v1_relat_1(B_8))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.16/1.50  tff(c_83, plain, (![B_20]: (k7_relat_1(B_20, k1_relat_1(B_20))=B_20 | ~v1_relat_1(B_20))), inference(resolution, [status(thm)], [c_72, c_8])).
% 2.16/1.50  tff(c_10, plain, (k7_relat_1('#skF_1', k1_relat_1('#skF_1'))!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.16/1.50  tff(c_92, plain, (~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_83, c_10])).
% 2.16/1.50  tff(c_103, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12, c_92])).
% 2.16/1.50  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.16/1.50  
% 2.16/1.50  Inference rules
% 2.16/1.50  ----------------------
% 2.16/1.50  #Ref     : 0
% 2.16/1.50  #Sup     : 23
% 2.16/1.50  #Fact    : 0
% 2.16/1.50  #Define  : 0
% 2.16/1.50  #Split   : 0
% 2.16/1.50  #Chain   : 0
% 2.16/1.50  #Close   : 0
% 2.16/1.50  
% 2.16/1.50  Ordering : KBO
% 2.16/1.50  
% 2.16/1.50  Simplification rules
% 2.16/1.50  ----------------------
% 2.16/1.50  #Subsume      : 2
% 2.16/1.50  #Demod        : 1
% 2.16/1.50  #Tautology    : 7
% 2.16/1.50  #SimpNegUnit  : 0
% 2.16/1.50  #BackRed      : 0
% 2.16/1.50  
% 2.16/1.50  #Partial instantiations: 0
% 2.16/1.50  #Strategies tried      : 1
% 2.16/1.50  
% 2.16/1.50  Timing (in seconds)
% 2.16/1.50  ----------------------
% 2.16/1.51  Preprocessing        : 0.44
% 2.16/1.51  Parsing              : 0.22
% 2.16/1.51  CNF conversion       : 0.02
% 2.16/1.51  Main loop            : 0.18
% 2.16/1.51  Inferencing          : 0.08
% 2.16/1.51  Reduction            : 0.05
% 2.16/1.51  Demodulation         : 0.04
% 2.16/1.51  BG Simplification    : 0.02
% 2.16/1.51  Subsumption          : 0.02
% 2.16/1.51  Abstraction          : 0.02
% 2.16/1.51  MUC search           : 0.00
% 2.16/1.51  Cooper               : 0.00
% 2.16/1.51  Total                : 0.66
% 2.16/1.51  Index Insertion      : 0.00
% 2.16/1.51  Index Deletion       : 0.00
% 2.16/1.51  Index Matching       : 0.00
% 2.16/1.51  BG Taut test         : 0.00
%------------------------------------------------------------------------------
