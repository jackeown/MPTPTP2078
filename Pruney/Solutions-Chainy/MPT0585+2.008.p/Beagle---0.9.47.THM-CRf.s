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
% DateTime   : Thu Dec  3 10:02:01 EST 2020

% Result     : Theorem 2.10s
% Output     : CNFRefutation 2.22s
% Verified   : 
% Statistics : Number of formulae       :   30 (  37 expanded)
%              Number of leaves         :   14 (  19 expanded)
%              Depth                    :    7
%              Number of atoms          :   40 (  56 expanded)
%              Number of equality atoms :   17 (  23 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_relat_1 > k7_relat_1 > k3_xboole_0 > #nlpp > k1_relat_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

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

tff(f_47,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ! [B] :
            ( v1_relat_1(B)
           => k7_relat_1(A,k1_relat_1(B)) = k7_relat_1(A,k1_relat_1(k7_relat_1(B,k1_relat_1(A)))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t189_relat_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k1_relat_1(k7_relat_1(B,A)) = k3_xboole_0(k1_relat_1(B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t90_relat_1)).

tff(f_39,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k7_relat_1(A,k1_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_relat_1)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k7_relat_1(k7_relat_1(C,A),B) = k7_relat_1(C,k3_xboole_0(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_relat_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(c_14,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_6,plain,(
    ! [B_7,A_6] :
      ( k3_xboole_0(k1_relat_1(B_7),A_6) = k1_relat_1(k7_relat_1(B_7,A_6))
      | ~ v1_relat_1(B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_8,plain,(
    ! [A_8] :
      ( k7_relat_1(A_8,k1_relat_1(A_8)) = A_8
      | ~ v1_relat_1(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_111,plain,(
    ! [C_17,A_18,B_19] :
      ( k7_relat_1(k7_relat_1(C_17,A_18),B_19) = k7_relat_1(C_17,k3_xboole_0(A_18,B_19))
      | ~ v1_relat_1(C_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_137,plain,(
    ! [A_20,B_21] :
      ( k7_relat_1(A_20,k3_xboole_0(k1_relat_1(A_20),B_21)) = k7_relat_1(A_20,B_21)
      | ~ v1_relat_1(A_20)
      | ~ v1_relat_1(A_20) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_111])).

tff(c_386,plain,(
    ! [B_28,A_29] :
      ( k7_relat_1(B_28,k1_relat_1(k7_relat_1(B_28,A_29))) = k7_relat_1(B_28,A_29)
      | ~ v1_relat_1(B_28)
      | ~ v1_relat_1(B_28)
      | ~ v1_relat_1(B_28) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_137])).

tff(c_12,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_57,plain,(
    ! [B_13,A_14] :
      ( k3_xboole_0(k1_relat_1(B_13),A_14) = k1_relat_1(k7_relat_1(B_13,A_14))
      | ~ v1_relat_1(B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_80,plain,(
    ! [A_15,B_16] :
      ( k3_xboole_0(A_15,k1_relat_1(B_16)) = k1_relat_1(k7_relat_1(B_16,A_15))
      | ~ v1_relat_1(B_16) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_57,c_2])).

tff(c_217,plain,(
    ! [B_25,B_24] :
      ( k1_relat_1(k7_relat_1(B_25,k1_relat_1(B_24))) = k1_relat_1(k7_relat_1(B_24,k1_relat_1(B_25)))
      | ~ v1_relat_1(B_25)
      | ~ v1_relat_1(B_24) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_80])).

tff(c_10,plain,(
    k7_relat_1('#skF_1',k1_relat_1(k7_relat_1('#skF_2',k1_relat_1('#skF_1')))) != k7_relat_1('#skF_1',k1_relat_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_262,plain,
    ( k7_relat_1('#skF_1',k1_relat_1(k7_relat_1('#skF_1',k1_relat_1('#skF_2')))) != k7_relat_1('#skF_1',k1_relat_1('#skF_2'))
    | ~ v1_relat_1('#skF_1')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_217,c_10])).

tff(c_315,plain,(
    k7_relat_1('#skF_1',k1_relat_1(k7_relat_1('#skF_1',k1_relat_1('#skF_2')))) != k7_relat_1('#skF_1',k1_relat_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_14,c_262])).

tff(c_395,plain,(
    ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_386,c_315])).

tff(c_442,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_395])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n022.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 17:32:11 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.10/1.22  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.10/1.22  
% 2.10/1.22  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.10/1.22  %$ v1_relat_1 > k7_relat_1 > k3_xboole_0 > #nlpp > k1_relat_1 > #skF_2 > #skF_1
% 2.10/1.22  
% 2.10/1.22  %Foreground sorts:
% 2.10/1.22  
% 2.10/1.22  
% 2.10/1.22  %Background operators:
% 2.10/1.22  
% 2.10/1.22  
% 2.10/1.22  %Foreground operators:
% 2.10/1.22  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.10/1.22  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.10/1.22  tff('#skF_2', type, '#skF_2': $i).
% 2.10/1.22  tff('#skF_1', type, '#skF_1': $i).
% 2.10/1.22  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.10/1.22  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.10/1.22  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.10/1.22  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.10/1.22  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.10/1.22  
% 2.22/1.23  tff(f_47, negated_conjecture, ~(![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k7_relat_1(A, k1_relat_1(B)) = k7_relat_1(A, k1_relat_1(k7_relat_1(B, k1_relat_1(A))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t189_relat_1)).
% 2.22/1.23  tff(f_35, axiom, (![A, B]: (v1_relat_1(B) => (k1_relat_1(k7_relat_1(B, A)) = k3_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t90_relat_1)).
% 2.22/1.23  tff(f_39, axiom, (![A]: (v1_relat_1(A) => (k7_relat_1(A, k1_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_relat_1)).
% 2.22/1.23  tff(f_31, axiom, (![A, B, C]: (v1_relat_1(C) => (k7_relat_1(k7_relat_1(C, A), B) = k7_relat_1(C, k3_xboole_0(A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_relat_1)).
% 2.22/1.23  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 2.22/1.23  tff(c_14, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.22/1.23  tff(c_6, plain, (![B_7, A_6]: (k3_xboole_0(k1_relat_1(B_7), A_6)=k1_relat_1(k7_relat_1(B_7, A_6)) | ~v1_relat_1(B_7))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.22/1.23  tff(c_8, plain, (![A_8]: (k7_relat_1(A_8, k1_relat_1(A_8))=A_8 | ~v1_relat_1(A_8))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.22/1.23  tff(c_111, plain, (![C_17, A_18, B_19]: (k7_relat_1(k7_relat_1(C_17, A_18), B_19)=k7_relat_1(C_17, k3_xboole_0(A_18, B_19)) | ~v1_relat_1(C_17))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.22/1.23  tff(c_137, plain, (![A_20, B_21]: (k7_relat_1(A_20, k3_xboole_0(k1_relat_1(A_20), B_21))=k7_relat_1(A_20, B_21) | ~v1_relat_1(A_20) | ~v1_relat_1(A_20))), inference(superposition, [status(thm), theory('equality')], [c_8, c_111])).
% 2.22/1.23  tff(c_386, plain, (![B_28, A_29]: (k7_relat_1(B_28, k1_relat_1(k7_relat_1(B_28, A_29)))=k7_relat_1(B_28, A_29) | ~v1_relat_1(B_28) | ~v1_relat_1(B_28) | ~v1_relat_1(B_28))), inference(superposition, [status(thm), theory('equality')], [c_6, c_137])).
% 2.22/1.23  tff(c_12, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.22/1.23  tff(c_57, plain, (![B_13, A_14]: (k3_xboole_0(k1_relat_1(B_13), A_14)=k1_relat_1(k7_relat_1(B_13, A_14)) | ~v1_relat_1(B_13))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.22/1.23  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.22/1.23  tff(c_80, plain, (![A_15, B_16]: (k3_xboole_0(A_15, k1_relat_1(B_16))=k1_relat_1(k7_relat_1(B_16, A_15)) | ~v1_relat_1(B_16))), inference(superposition, [status(thm), theory('equality')], [c_57, c_2])).
% 2.22/1.23  tff(c_217, plain, (![B_25, B_24]: (k1_relat_1(k7_relat_1(B_25, k1_relat_1(B_24)))=k1_relat_1(k7_relat_1(B_24, k1_relat_1(B_25))) | ~v1_relat_1(B_25) | ~v1_relat_1(B_24))), inference(superposition, [status(thm), theory('equality')], [c_6, c_80])).
% 2.22/1.23  tff(c_10, plain, (k7_relat_1('#skF_1', k1_relat_1(k7_relat_1('#skF_2', k1_relat_1('#skF_1'))))!=k7_relat_1('#skF_1', k1_relat_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.22/1.23  tff(c_262, plain, (k7_relat_1('#skF_1', k1_relat_1(k7_relat_1('#skF_1', k1_relat_1('#skF_2'))))!=k7_relat_1('#skF_1', k1_relat_1('#skF_2')) | ~v1_relat_1('#skF_1') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_217, c_10])).
% 2.22/1.23  tff(c_315, plain, (k7_relat_1('#skF_1', k1_relat_1(k7_relat_1('#skF_1', k1_relat_1('#skF_2'))))!=k7_relat_1('#skF_1', k1_relat_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_14, c_262])).
% 2.22/1.23  tff(c_395, plain, (~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_386, c_315])).
% 2.22/1.23  tff(c_442, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_14, c_395])).
% 2.22/1.23  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.22/1.23  
% 2.22/1.23  Inference rules
% 2.22/1.23  ----------------------
% 2.22/1.23  #Ref     : 0
% 2.22/1.23  #Sup     : 114
% 2.22/1.23  #Fact    : 0
% 2.22/1.23  #Define  : 0
% 2.22/1.23  #Split   : 0
% 2.22/1.23  #Chain   : 0
% 2.22/1.23  #Close   : 0
% 2.22/1.23  
% 2.22/1.23  Ordering : KBO
% 2.22/1.23  
% 2.22/1.23  Simplification rules
% 2.22/1.23  ----------------------
% 2.22/1.23  #Subsume      : 13
% 2.22/1.23  #Demod        : 9
% 2.22/1.23  #Tautology    : 34
% 2.22/1.23  #SimpNegUnit  : 0
% 2.22/1.23  #BackRed      : 0
% 2.22/1.23  
% 2.22/1.23  #Partial instantiations: 0
% 2.22/1.23  #Strategies tried      : 1
% 2.22/1.23  
% 2.22/1.23  Timing (in seconds)
% 2.22/1.23  ----------------------
% 2.22/1.24  Preprocessing        : 0.26
% 2.22/1.24  Parsing              : 0.14
% 2.22/1.24  CNF conversion       : 0.02
% 2.22/1.24  Main loop            : 0.24
% 2.22/1.24  Inferencing          : 0.10
% 2.22/1.24  Reduction            : 0.07
% 2.22/1.24  Demodulation         : 0.05
% 2.22/1.24  BG Simplification    : 0.02
% 2.22/1.24  Subsumption          : 0.04
% 2.22/1.24  Abstraction          : 0.02
% 2.22/1.24  MUC search           : 0.00
% 2.22/1.24  Cooper               : 0.00
% 2.22/1.24  Total                : 0.52
% 2.22/1.24  Index Insertion      : 0.00
% 2.22/1.24  Index Deletion       : 0.00
% 2.22/1.24  Index Matching       : 0.00
% 2.22/1.24  BG Taut test         : 0.00
%------------------------------------------------------------------------------
