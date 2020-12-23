%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:02:08 EST 2020

% Result     : Theorem 2.26s
% Output     : CNFRefutation 2.26s
% Verified   : 
% Statistics : Number of formulae       :   39 (  44 expanded)
%              Number of leaves         :   24 (  27 expanded)
%              Depth                    :    7
%              Number of atoms          :   41 (  49 expanded)
%              Number of equality atoms :   12 (  15 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k7_relat_1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_66,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => k7_relat_1(B,A) = k7_relat_1(B,k3_xboole_0(k1_relat_1(B),A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t192_relat_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k7_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k1_relat_1(k7_relat_1(B,A)),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_relat_1)).

tff(f_49,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r1_tarski(A,B)
       => k7_relat_1(k7_relat_1(C,B),A) = k7_relat_1(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t103_relat_1)).

tff(f_61,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k7_relat_1(A,k1_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_relat_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k1_relat_1(k7_relat_1(B,A)) = k3_xboole_0(k1_relat_1(B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t90_relat_1)).

tff(c_28,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_16,plain,(
    ! [A_25,B_26] :
      ( v1_relat_1(k7_relat_1(A_25,B_26))
      | ~ v1_relat_1(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_20,plain,(
    ! [B_31,A_30] :
      ( r1_tarski(k1_relat_1(k7_relat_1(B_31,A_30)),A_30)
      | ~ v1_relat_1(B_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_128,plain,(
    ! [C_58,B_59,A_60] :
      ( k7_relat_1(k7_relat_1(C_58,B_59),A_60) = k7_relat_1(C_58,A_60)
      | ~ r1_tarski(A_60,B_59)
      | ~ v1_relat_1(C_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_24,plain,(
    ! [A_34] :
      ( k7_relat_1(A_34,k1_relat_1(A_34)) = A_34
      | ~ v1_relat_1(A_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_380,plain,(
    ! [C_82,B_83] :
      ( k7_relat_1(C_82,k1_relat_1(k7_relat_1(C_82,B_83))) = k7_relat_1(C_82,B_83)
      | ~ v1_relat_1(k7_relat_1(C_82,B_83))
      | ~ r1_tarski(k1_relat_1(k7_relat_1(C_82,B_83)),B_83)
      | ~ v1_relat_1(C_82) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_128,c_24])).

tff(c_388,plain,(
    ! [B_84,A_85] :
      ( k7_relat_1(B_84,k1_relat_1(k7_relat_1(B_84,A_85))) = k7_relat_1(B_84,A_85)
      | ~ v1_relat_1(k7_relat_1(B_84,A_85))
      | ~ v1_relat_1(B_84) ) ),
    inference(resolution,[status(thm)],[c_20,c_380])).

tff(c_88,plain,(
    ! [B_49,A_50] :
      ( k3_xboole_0(k1_relat_1(B_49),A_50) = k1_relat_1(k7_relat_1(B_49,A_50))
      | ~ v1_relat_1(B_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_26,plain,(
    k7_relat_1('#skF_2',k3_xboole_0(k1_relat_1('#skF_2'),'#skF_1')) != k7_relat_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_94,plain,
    ( k7_relat_1('#skF_2',k1_relat_1(k7_relat_1('#skF_2','#skF_1'))) != k7_relat_1('#skF_2','#skF_1')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_88,c_26])).

tff(c_100,plain,(
    k7_relat_1('#skF_2',k1_relat_1(k7_relat_1('#skF_2','#skF_1'))) != k7_relat_1('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_94])).

tff(c_407,plain,
    ( ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1'))
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_388,c_100])).

tff(c_434,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_407])).

tff(c_440,plain,(
    ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_16,c_434])).

tff(c_444,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_440])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.31  % Computer   : n016.cluster.edu
% 0.12/0.31  % Model      : x86_64 x86_64
% 0.12/0.31  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.31  % Memory     : 8042.1875MB
% 0.12/0.31  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.32  % CPULimit   : 60
% 0.12/0.32  % DateTime   : Tue Dec  1 19:53:49 EST 2020
% 0.12/0.32  % CPUTime    : 
% 0.12/0.32  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.26/1.24  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.26/1.25  
% 2.26/1.25  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.26/1.25  %$ r1_tarski > v1_relat_1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k7_relat_1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1
% 2.26/1.25  
% 2.26/1.25  %Foreground sorts:
% 2.26/1.25  
% 2.26/1.25  
% 2.26/1.25  %Background operators:
% 2.26/1.25  
% 2.26/1.25  
% 2.26/1.25  %Foreground operators:
% 2.26/1.25  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.26/1.25  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.26/1.25  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.26/1.25  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.26/1.25  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.26/1.25  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.26/1.25  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.26/1.25  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.26/1.25  tff('#skF_2', type, '#skF_2': $i).
% 2.26/1.25  tff('#skF_1', type, '#skF_1': $i).
% 2.26/1.25  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.26/1.25  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.26/1.25  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.26/1.25  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.26/1.25  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.26/1.25  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.26/1.25  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.26/1.25  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.26/1.25  
% 2.26/1.26  tff(f_66, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k7_relat_1(B, k3_xboole_0(k1_relat_1(B), A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t192_relat_1)).
% 2.26/1.26  tff(f_43, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k7_relat_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 2.26/1.26  tff(f_53, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k7_relat_1(B, A)), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t87_relat_1)).
% 2.26/1.26  tff(f_49, axiom, (![A, B, C]: (v1_relat_1(C) => (r1_tarski(A, B) => (k7_relat_1(k7_relat_1(C, B), A) = k7_relat_1(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t103_relat_1)).
% 2.26/1.26  tff(f_61, axiom, (![A]: (v1_relat_1(A) => (k7_relat_1(A, k1_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_relat_1)).
% 2.26/1.26  tff(f_57, axiom, (![A, B]: (v1_relat_1(B) => (k1_relat_1(k7_relat_1(B, A)) = k3_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t90_relat_1)).
% 2.26/1.26  tff(c_28, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.26/1.26  tff(c_16, plain, (![A_25, B_26]: (v1_relat_1(k7_relat_1(A_25, B_26)) | ~v1_relat_1(A_25))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.26/1.26  tff(c_20, plain, (![B_31, A_30]: (r1_tarski(k1_relat_1(k7_relat_1(B_31, A_30)), A_30) | ~v1_relat_1(B_31))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.26/1.26  tff(c_128, plain, (![C_58, B_59, A_60]: (k7_relat_1(k7_relat_1(C_58, B_59), A_60)=k7_relat_1(C_58, A_60) | ~r1_tarski(A_60, B_59) | ~v1_relat_1(C_58))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.26/1.26  tff(c_24, plain, (![A_34]: (k7_relat_1(A_34, k1_relat_1(A_34))=A_34 | ~v1_relat_1(A_34))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.26/1.26  tff(c_380, plain, (![C_82, B_83]: (k7_relat_1(C_82, k1_relat_1(k7_relat_1(C_82, B_83)))=k7_relat_1(C_82, B_83) | ~v1_relat_1(k7_relat_1(C_82, B_83)) | ~r1_tarski(k1_relat_1(k7_relat_1(C_82, B_83)), B_83) | ~v1_relat_1(C_82))), inference(superposition, [status(thm), theory('equality')], [c_128, c_24])).
% 2.26/1.26  tff(c_388, plain, (![B_84, A_85]: (k7_relat_1(B_84, k1_relat_1(k7_relat_1(B_84, A_85)))=k7_relat_1(B_84, A_85) | ~v1_relat_1(k7_relat_1(B_84, A_85)) | ~v1_relat_1(B_84))), inference(resolution, [status(thm)], [c_20, c_380])).
% 2.26/1.26  tff(c_88, plain, (![B_49, A_50]: (k3_xboole_0(k1_relat_1(B_49), A_50)=k1_relat_1(k7_relat_1(B_49, A_50)) | ~v1_relat_1(B_49))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.26/1.26  tff(c_26, plain, (k7_relat_1('#skF_2', k3_xboole_0(k1_relat_1('#skF_2'), '#skF_1'))!=k7_relat_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.26/1.26  tff(c_94, plain, (k7_relat_1('#skF_2', k1_relat_1(k7_relat_1('#skF_2', '#skF_1')))!=k7_relat_1('#skF_2', '#skF_1') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_88, c_26])).
% 2.26/1.26  tff(c_100, plain, (k7_relat_1('#skF_2', k1_relat_1(k7_relat_1('#skF_2', '#skF_1')))!=k7_relat_1('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_94])).
% 2.26/1.26  tff(c_407, plain, (~v1_relat_1(k7_relat_1('#skF_2', '#skF_1')) | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_388, c_100])).
% 2.26/1.26  tff(c_434, plain, (~v1_relat_1(k7_relat_1('#skF_2', '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_407])).
% 2.26/1.26  tff(c_440, plain, (~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_16, c_434])).
% 2.26/1.26  tff(c_444, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_28, c_440])).
% 2.26/1.26  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.26/1.26  
% 2.26/1.26  Inference rules
% 2.26/1.26  ----------------------
% 2.26/1.26  #Ref     : 0
% 2.26/1.26  #Sup     : 105
% 2.26/1.26  #Fact    : 0
% 2.26/1.26  #Define  : 0
% 2.26/1.26  #Split   : 0
% 2.26/1.26  #Chain   : 0
% 2.26/1.26  #Close   : 0
% 2.26/1.26  
% 2.26/1.26  Ordering : KBO
% 2.26/1.26  
% 2.26/1.26  Simplification rules
% 2.26/1.26  ----------------------
% 2.26/1.26  #Subsume      : 4
% 2.26/1.26  #Demod        : 34
% 2.26/1.26  #Tautology    : 51
% 2.26/1.26  #SimpNegUnit  : 0
% 2.26/1.26  #BackRed      : 0
% 2.26/1.26  
% 2.26/1.26  #Partial instantiations: 0
% 2.26/1.26  #Strategies tried      : 1
% 2.26/1.26  
% 2.26/1.26  Timing (in seconds)
% 2.26/1.26  ----------------------
% 2.26/1.26  Preprocessing        : 0.29
% 2.26/1.26  Parsing              : 0.16
% 2.26/1.26  CNF conversion       : 0.02
% 2.26/1.26  Main loop            : 0.23
% 2.26/1.26  Inferencing          : 0.10
% 2.26/1.26  Reduction            : 0.07
% 2.26/1.26  Demodulation         : 0.05
% 2.26/1.26  BG Simplification    : 0.02
% 2.26/1.26  Subsumption          : 0.04
% 2.26/1.26  Abstraction          : 0.02
% 2.26/1.26  MUC search           : 0.00
% 2.26/1.26  Cooper               : 0.00
% 2.26/1.26  Total                : 0.55
% 2.26/1.26  Index Insertion      : 0.00
% 2.26/1.26  Index Deletion       : 0.00
% 2.26/1.26  Index Matching       : 0.00
% 2.26/1.26  BG Taut test         : 0.00
%------------------------------------------------------------------------------
