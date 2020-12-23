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
% DateTime   : Thu Dec  3 10:02:05 EST 2020

% Result     : Theorem 14.77s
% Output     : CNFRefutation 14.77s
% Verified   : 
% Statistics : Number of formulae       :   34 (  37 expanded)
%              Number of leaves         :   18 (  20 expanded)
%              Depth                    :    8
%              Number of atoms          :   41 (  46 expanded)
%              Number of equality atoms :   13 (  15 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k7_relat_1 > k4_xboole_0 > k3_xboole_0 > #nlpp > k1_relat_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_56,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => k7_relat_1(B,A) = k7_relat_1(B,k3_xboole_0(k1_relat_1(B),A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t192_relat_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k7_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k1_relat_1(k7_relat_1(B,A)) = k3_xboole_0(k1_relat_1(B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t90_relat_1)).

tff(f_29,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k1_relat_1(B),A)
       => k7_relat_1(B,A) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t97_relat_1)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k7_relat_1(k7_relat_1(C,A),B) = k7_relat_1(C,k3_xboole_0(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_relat_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(c_20,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_10,plain,(
    ! [A_9,B_10] :
      ( v1_relat_1(k7_relat_1(A_9,B_10))
      | ~ v1_relat_1(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_298,plain,(
    ! [B_42,A_43] :
      ( k3_xboole_0(k1_relat_1(B_42),A_43) = k1_relat_1(k7_relat_1(B_42,A_43))
      | ~ v1_relat_1(B_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_4,plain,(
    ! [A_3,B_4] : r1_tarski(k3_xboole_0(A_3,B_4),A_3) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_374,plain,(
    ! [B_46,A_47] :
      ( r1_tarski(k1_relat_1(k7_relat_1(B_46,A_47)),k1_relat_1(B_46))
      | ~ v1_relat_1(B_46) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_298,c_4])).

tff(c_16,plain,(
    ! [B_17,A_16] :
      ( k7_relat_1(B_17,A_16) = B_17
      | ~ r1_tarski(k1_relat_1(B_17),A_16)
      | ~ v1_relat_1(B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_6875,plain,(
    ! [B_146,A_147] :
      ( k7_relat_1(k7_relat_1(B_146,A_147),k1_relat_1(B_146)) = k7_relat_1(B_146,A_147)
      | ~ v1_relat_1(k7_relat_1(B_146,A_147))
      | ~ v1_relat_1(B_146) ) ),
    inference(resolution,[status(thm)],[c_374,c_16])).

tff(c_12,plain,(
    ! [C_13,A_11,B_12] :
      ( k7_relat_1(k7_relat_1(C_13,A_11),B_12) = k7_relat_1(C_13,k3_xboole_0(A_11,B_12))
      | ~ v1_relat_1(C_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_27354,plain,(
    ! [B_323,A_324] :
      ( k7_relat_1(B_323,k3_xboole_0(A_324,k1_relat_1(B_323))) = k7_relat_1(B_323,A_324)
      | ~ v1_relat_1(B_323)
      | ~ v1_relat_1(k7_relat_1(B_323,A_324))
      | ~ v1_relat_1(B_323) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6875,c_12])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_18,plain,(
    k7_relat_1('#skF_2',k3_xboole_0(k1_relat_1('#skF_2'),'#skF_1')) != k7_relat_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_21,plain,(
    k7_relat_1('#skF_2',k3_xboole_0('#skF_1',k1_relat_1('#skF_2'))) != k7_relat_1('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_18])).

tff(c_27634,plain,
    ( ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1'))
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_27354,c_21])).

tff(c_27801,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_27634])).

tff(c_27808,plain,(
    ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_10,c_27801])).

tff(c_27812,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_27808])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n022.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:59:40 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 14.77/6.45  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 14.77/6.46  
% 14.77/6.46  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 14.77/6.46  %$ r1_tarski > v1_relat_1 > k7_relat_1 > k4_xboole_0 > k3_xboole_0 > #nlpp > k1_relat_1 > #skF_2 > #skF_1
% 14.77/6.46  
% 14.77/6.46  %Foreground sorts:
% 14.77/6.46  
% 14.77/6.46  
% 14.77/6.46  %Background operators:
% 14.77/6.46  
% 14.77/6.46  
% 14.77/6.46  %Foreground operators:
% 14.77/6.46  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 14.77/6.46  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 14.77/6.46  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 14.77/6.46  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 14.77/6.46  tff('#skF_2', type, '#skF_2': $i).
% 14.77/6.46  tff('#skF_1', type, '#skF_1': $i).
% 14.77/6.46  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 14.77/6.46  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 14.77/6.46  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 14.77/6.46  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 14.77/6.46  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 14.77/6.46  
% 14.77/6.47  tff(f_56, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k7_relat_1(B, k3_xboole_0(k1_relat_1(B), A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t192_relat_1)).
% 14.77/6.47  tff(f_37, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k7_relat_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 14.77/6.47  tff(f_45, axiom, (![A, B]: (v1_relat_1(B) => (k1_relat_1(k7_relat_1(B, A)) = k3_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t90_relat_1)).
% 14.77/6.47  tff(f_29, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 14.77/6.47  tff(f_51, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(B), A) => (k7_relat_1(B, A) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t97_relat_1)).
% 14.77/6.47  tff(f_41, axiom, (![A, B, C]: (v1_relat_1(C) => (k7_relat_1(k7_relat_1(C, A), B) = k7_relat_1(C, k3_xboole_0(A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_relat_1)).
% 14.77/6.47  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 14.77/6.47  tff(c_20, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_56])).
% 14.77/6.47  tff(c_10, plain, (![A_9, B_10]: (v1_relat_1(k7_relat_1(A_9, B_10)) | ~v1_relat_1(A_9))), inference(cnfTransformation, [status(thm)], [f_37])).
% 14.77/6.47  tff(c_298, plain, (![B_42, A_43]: (k3_xboole_0(k1_relat_1(B_42), A_43)=k1_relat_1(k7_relat_1(B_42, A_43)) | ~v1_relat_1(B_42))), inference(cnfTransformation, [status(thm)], [f_45])).
% 14.77/6.47  tff(c_4, plain, (![A_3, B_4]: (r1_tarski(k3_xboole_0(A_3, B_4), A_3))), inference(cnfTransformation, [status(thm)], [f_29])).
% 14.77/6.47  tff(c_374, plain, (![B_46, A_47]: (r1_tarski(k1_relat_1(k7_relat_1(B_46, A_47)), k1_relat_1(B_46)) | ~v1_relat_1(B_46))), inference(superposition, [status(thm), theory('equality')], [c_298, c_4])).
% 14.77/6.47  tff(c_16, plain, (![B_17, A_16]: (k7_relat_1(B_17, A_16)=B_17 | ~r1_tarski(k1_relat_1(B_17), A_16) | ~v1_relat_1(B_17))), inference(cnfTransformation, [status(thm)], [f_51])).
% 14.77/6.47  tff(c_6875, plain, (![B_146, A_147]: (k7_relat_1(k7_relat_1(B_146, A_147), k1_relat_1(B_146))=k7_relat_1(B_146, A_147) | ~v1_relat_1(k7_relat_1(B_146, A_147)) | ~v1_relat_1(B_146))), inference(resolution, [status(thm)], [c_374, c_16])).
% 14.77/6.47  tff(c_12, plain, (![C_13, A_11, B_12]: (k7_relat_1(k7_relat_1(C_13, A_11), B_12)=k7_relat_1(C_13, k3_xboole_0(A_11, B_12)) | ~v1_relat_1(C_13))), inference(cnfTransformation, [status(thm)], [f_41])).
% 14.77/6.47  tff(c_27354, plain, (![B_323, A_324]: (k7_relat_1(B_323, k3_xboole_0(A_324, k1_relat_1(B_323)))=k7_relat_1(B_323, A_324) | ~v1_relat_1(B_323) | ~v1_relat_1(k7_relat_1(B_323, A_324)) | ~v1_relat_1(B_323))), inference(superposition, [status(thm), theory('equality')], [c_6875, c_12])).
% 14.77/6.47  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 14.77/6.47  tff(c_18, plain, (k7_relat_1('#skF_2', k3_xboole_0(k1_relat_1('#skF_2'), '#skF_1'))!=k7_relat_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_56])).
% 14.77/6.47  tff(c_21, plain, (k7_relat_1('#skF_2', k3_xboole_0('#skF_1', k1_relat_1('#skF_2')))!=k7_relat_1('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_18])).
% 14.77/6.47  tff(c_27634, plain, (~v1_relat_1(k7_relat_1('#skF_2', '#skF_1')) | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_27354, c_21])).
% 14.77/6.47  tff(c_27801, plain, (~v1_relat_1(k7_relat_1('#skF_2', '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_27634])).
% 14.77/6.47  tff(c_27808, plain, (~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_10, c_27801])).
% 14.77/6.47  tff(c_27812, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_20, c_27808])).
% 14.77/6.47  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 14.77/6.47  
% 14.77/6.47  Inference rules
% 14.77/6.47  ----------------------
% 14.77/6.47  #Ref     : 0
% 14.77/6.47  #Sup     : 7531
% 14.77/6.47  #Fact    : 0
% 14.77/6.47  #Define  : 0
% 14.77/6.47  #Split   : 0
% 14.77/6.47  #Chain   : 0
% 14.77/6.47  #Close   : 0
% 14.77/6.47  
% 14.77/6.47  Ordering : KBO
% 14.77/6.47  
% 14.77/6.47  Simplification rules
% 14.77/6.47  ----------------------
% 14.77/6.47  #Subsume      : 1066
% 14.77/6.47  #Demod        : 9277
% 14.77/6.47  #Tautology    : 2233
% 14.77/6.47  #SimpNegUnit  : 0
% 14.77/6.47  #BackRed      : 0
% 14.77/6.47  
% 14.77/6.47  #Partial instantiations: 0
% 14.77/6.47  #Strategies tried      : 1
% 14.77/6.47  
% 14.77/6.47  Timing (in seconds)
% 14.77/6.47  ----------------------
% 14.77/6.47  Preprocessing        : 0.29
% 14.77/6.47  Parsing              : 0.16
% 14.77/6.47  CNF conversion       : 0.01
% 14.77/6.47  Main loop            : 5.33
% 14.77/6.47  Inferencing          : 1.03
% 14.77/6.47  Reduction            : 2.98
% 14.77/6.47  Demodulation         : 2.71
% 14.77/6.47  BG Simplification    : 0.16
% 14.77/6.47  Subsumption          : 0.98
% 14.77/6.47  Abstraction          : 0.26
% 14.77/6.47  MUC search           : 0.00
% 14.77/6.47  Cooper               : 0.00
% 14.77/6.47  Total                : 5.65
% 14.77/6.47  Index Insertion      : 0.00
% 14.77/6.47  Index Deletion       : 0.00
% 14.77/6.47  Index Matching       : 0.00
% 14.77/6.47  BG Taut test         : 0.00
%------------------------------------------------------------------------------
