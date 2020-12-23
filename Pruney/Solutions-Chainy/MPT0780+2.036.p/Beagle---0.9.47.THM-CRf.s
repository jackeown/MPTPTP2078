%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:06:43 EST 2020

% Result     : Theorem 1.67s
% Output     : CNFRefutation 1.67s
% Verified   : 
% Statistics : Number of formulae       :   31 (  35 expanded)
%              Number of leaves         :   18 (  21 expanded)
%              Depth                    :    5
%              Number of atoms          :   28 (  38 expanded)
%              Number of equality atoms :   15 (  18 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k3_xboole_0 > k2_xboole_0 > k2_wellord1 > k2_tarski > #nlpp > k1_setfam_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k2_wellord1,type,(
    k2_wellord1: ( $i * $i ) > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_48,negated_conjecture,(
    ~ ! [A,B,C] :
        ( v1_relat_1(C)
       => ( r1_tarski(A,B)
         => k2_wellord1(k2_wellord1(C,B),A) = k2_wellord1(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_wellord1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] : k3_xboole_0(A,k2_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_xboole_1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k2_wellord1(k2_wellord1(C,A),B) = k2_wellord1(C,k3_xboole_0(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_wellord1)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k2_wellord1(k2_wellord1(C,A),B) = k2_wellord1(k2_wellord1(C,B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t27_wellord1)).

tff(c_16,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_14,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_26,plain,(
    ! [A_15,B_16] :
      ( k2_xboole_0(A_15,B_16) = B_16
      | ~ r1_tarski(A_15,B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_30,plain,(
    k2_xboole_0('#skF_1','#skF_2') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_14,c_26])).

tff(c_4,plain,(
    ! [A_3,B_4] : k3_xboole_0(A_3,k2_xboole_0(A_3,B_4)) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_34,plain,(
    k3_xboole_0('#skF_1','#skF_2') = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_4])).

tff(c_118,plain,(
    ! [C_22,A_23,B_24] :
      ( k2_wellord1(k2_wellord1(C_22,A_23),B_24) = k2_wellord1(C_22,k3_xboole_0(A_23,B_24))
      | ~ v1_relat_1(C_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_51,plain,(
    ! [C_19,B_20,A_21] :
      ( k2_wellord1(k2_wellord1(C_19,B_20),A_21) = k2_wellord1(k2_wellord1(C_19,A_21),B_20)
      | ~ v1_relat_1(C_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_12,plain,(
    k2_wellord1(k2_wellord1('#skF_3','#skF_2'),'#skF_1') != k2_wellord1('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_78,plain,
    ( k2_wellord1(k2_wellord1('#skF_3','#skF_1'),'#skF_2') != k2_wellord1('#skF_3','#skF_1')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_51,c_12])).

tff(c_111,plain,(
    k2_wellord1(k2_wellord1('#skF_3','#skF_1'),'#skF_2') != k2_wellord1('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_78])).

tff(c_127,plain,
    ( k2_wellord1('#skF_3',k3_xboole_0('#skF_1','#skF_2')) != k2_wellord1('#skF_3','#skF_1')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_118,c_111])).

tff(c_164,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_34,c_127])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:43:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.67/1.14  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.67/1.14  
% 1.67/1.14  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.67/1.14  %$ r1_tarski > v1_relat_1 > k3_xboole_0 > k2_xboole_0 > k2_wellord1 > k2_tarski > #nlpp > k1_setfam_1 > #skF_2 > #skF_3 > #skF_1
% 1.67/1.14  
% 1.67/1.14  %Foreground sorts:
% 1.67/1.14  
% 1.67/1.14  
% 1.67/1.14  %Background operators:
% 1.67/1.14  
% 1.67/1.14  
% 1.67/1.14  %Foreground operators:
% 1.67/1.14  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.67/1.14  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.67/1.14  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.67/1.14  tff('#skF_2', type, '#skF_2': $i).
% 1.67/1.14  tff('#skF_3', type, '#skF_3': $i).
% 1.67/1.14  tff('#skF_1', type, '#skF_1': $i).
% 1.67/1.14  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.67/1.14  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.67/1.14  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.67/1.14  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.67/1.14  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.67/1.14  tff(k2_wellord1, type, k2_wellord1: ($i * $i) > $i).
% 1.67/1.14  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 1.67/1.14  
% 1.67/1.15  tff(f_48, negated_conjecture, ~(![A, B, C]: (v1_relat_1(C) => (r1_tarski(A, B) => (k2_wellord1(k2_wellord1(C, B), A) = k2_wellord1(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_wellord1)).
% 1.67/1.15  tff(f_29, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 1.67/1.15  tff(f_31, axiom, (![A, B]: (k3_xboole_0(A, k2_xboole_0(A, B)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t21_xboole_1)).
% 1.67/1.15  tff(f_37, axiom, (![A, B, C]: (v1_relat_1(C) => (k2_wellord1(k2_wellord1(C, A), B) = k2_wellord1(C, k3_xboole_0(A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t26_wellord1)).
% 1.67/1.15  tff(f_41, axiom, (![A, B, C]: (v1_relat_1(C) => (k2_wellord1(k2_wellord1(C, A), B) = k2_wellord1(k2_wellord1(C, B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t27_wellord1)).
% 1.67/1.15  tff(c_16, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_48])).
% 1.67/1.15  tff(c_14, plain, (r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_48])).
% 1.67/1.15  tff(c_26, plain, (![A_15, B_16]: (k2_xboole_0(A_15, B_16)=B_16 | ~r1_tarski(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.67/1.15  tff(c_30, plain, (k2_xboole_0('#skF_1', '#skF_2')='#skF_2'), inference(resolution, [status(thm)], [c_14, c_26])).
% 1.67/1.15  tff(c_4, plain, (![A_3, B_4]: (k3_xboole_0(A_3, k2_xboole_0(A_3, B_4))=A_3)), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.67/1.15  tff(c_34, plain, (k3_xboole_0('#skF_1', '#skF_2')='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_30, c_4])).
% 1.67/1.15  tff(c_118, plain, (![C_22, A_23, B_24]: (k2_wellord1(k2_wellord1(C_22, A_23), B_24)=k2_wellord1(C_22, k3_xboole_0(A_23, B_24)) | ~v1_relat_1(C_22))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.67/1.15  tff(c_51, plain, (![C_19, B_20, A_21]: (k2_wellord1(k2_wellord1(C_19, B_20), A_21)=k2_wellord1(k2_wellord1(C_19, A_21), B_20) | ~v1_relat_1(C_19))), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.67/1.15  tff(c_12, plain, (k2_wellord1(k2_wellord1('#skF_3', '#skF_2'), '#skF_1')!=k2_wellord1('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_48])).
% 1.67/1.15  tff(c_78, plain, (k2_wellord1(k2_wellord1('#skF_3', '#skF_1'), '#skF_2')!=k2_wellord1('#skF_3', '#skF_1') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_51, c_12])).
% 1.67/1.15  tff(c_111, plain, (k2_wellord1(k2_wellord1('#skF_3', '#skF_1'), '#skF_2')!=k2_wellord1('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_16, c_78])).
% 1.67/1.15  tff(c_127, plain, (k2_wellord1('#skF_3', k3_xboole_0('#skF_1', '#skF_2'))!=k2_wellord1('#skF_3', '#skF_1') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_118, c_111])).
% 1.67/1.15  tff(c_164, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_16, c_34, c_127])).
% 1.67/1.15  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.67/1.15  
% 1.67/1.15  Inference rules
% 1.67/1.15  ----------------------
% 1.67/1.15  #Ref     : 0
% 1.67/1.15  #Sup     : 42
% 1.67/1.15  #Fact    : 0
% 1.67/1.15  #Define  : 0
% 1.67/1.15  #Split   : 0
% 1.67/1.15  #Chain   : 0
% 1.67/1.15  #Close   : 0
% 1.67/1.15  
% 1.67/1.15  Ordering : KBO
% 1.67/1.15  
% 1.67/1.15  Simplification rules
% 1.67/1.15  ----------------------
% 1.67/1.15  #Subsume      : 1
% 1.67/1.15  #Demod        : 4
% 1.67/1.15  #Tautology    : 17
% 1.67/1.15  #SimpNegUnit  : 0
% 1.67/1.15  #BackRed      : 0
% 1.67/1.15  
% 1.67/1.15  #Partial instantiations: 0
% 1.67/1.15  #Strategies tried      : 1
% 1.67/1.15  
% 1.67/1.15  Timing (in seconds)
% 1.67/1.15  ----------------------
% 1.67/1.15  Preprocessing        : 0.26
% 1.67/1.15  Parsing              : 0.14
% 1.67/1.15  CNF conversion       : 0.02
% 1.67/1.15  Main loop            : 0.14
% 1.67/1.15  Inferencing          : 0.07
% 1.67/1.15  Reduction            : 0.03
% 1.67/1.15  Demodulation         : 0.03
% 1.67/1.16  BG Simplification    : 0.01
% 1.67/1.16  Subsumption          : 0.02
% 1.67/1.16  Abstraction          : 0.01
% 1.67/1.16  MUC search           : 0.00
% 1.67/1.16  Cooper               : 0.00
% 1.67/1.16  Total                : 0.42
% 1.67/1.16  Index Insertion      : 0.00
% 1.67/1.16  Index Deletion       : 0.00
% 1.67/1.16  Index Matching       : 0.00
% 1.67/1.16  BG Taut test         : 0.00
%------------------------------------------------------------------------------
