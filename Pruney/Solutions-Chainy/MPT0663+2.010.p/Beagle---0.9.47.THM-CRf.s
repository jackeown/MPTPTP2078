%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:04:12 EST 2020

% Result     : Theorem 1.63s
% Output     : CNFRefutation 1.63s
% Verified   : 
% Statistics : Number of formulae       :   31 (  38 expanded)
%              Number of leaves         :   17 (  22 expanded)
%              Depth                    :    7
%              Number of atoms          :   33 (  52 expanded)
%              Number of equality atoms :   11 (  17 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v1_relat_1 > v1_funct_1 > k7_relat_1 > k3_xboole_0 > k1_funct_1 > #nlpp > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

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

tff(f_48,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_relat_1(C)
          & v1_funct_1(C) )
       => ( r2_hidden(A,k3_xboole_0(k1_relat_1(C),B))
         => k1_funct_1(k7_relat_1(C,B),A) = k1_funct_1(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_funct_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k1_relat_1(k7_relat_1(B,A)) = k3_xboole_0(k1_relat_1(B),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t90_relat_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( r2_hidden(A,k1_relat_1(k7_relat_1(C,B)))
       => k1_funct_1(k7_relat_1(C,B),A) = k1_funct_1(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_funct_1)).

tff(c_8,plain,(
    k1_funct_1(k7_relat_1('#skF_3','#skF_2'),'#skF_1') != k1_funct_1('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_14,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_12,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_49,plain,(
    ! [B_10,A_11] :
      ( k3_xboole_0(k1_relat_1(B_10),A_11) = k1_relat_1(k7_relat_1(B_10,A_11))
      | ~ v1_relat_1(B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_72,plain,(
    ! [A_12,B_13] :
      ( k3_xboole_0(A_12,k1_relat_1(B_13)) = k1_relat_1(k7_relat_1(B_13,A_12))
      | ~ v1_relat_1(B_13) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_49,c_2])).

tff(c_10,plain,(
    r2_hidden('#skF_1',k3_xboole_0(k1_relat_1('#skF_3'),'#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_15,plain,(
    r2_hidden('#skF_1',k3_xboole_0('#skF_2',k1_relat_1('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_10])).

tff(c_88,plain,
    ( r2_hidden('#skF_1',k1_relat_1(k7_relat_1('#skF_3','#skF_2')))
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_72,c_15])).

tff(c_106,plain,(
    r2_hidden('#skF_1',k1_relat_1(k7_relat_1('#skF_3','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_88])).

tff(c_108,plain,(
    ! [C_14,B_15,A_16] :
      ( k1_funct_1(k7_relat_1(C_14,B_15),A_16) = k1_funct_1(C_14,A_16)
      | ~ r2_hidden(A_16,k1_relat_1(k7_relat_1(C_14,B_15)))
      | ~ v1_funct_1(C_14)
      | ~ v1_relat_1(C_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_111,plain,
    ( k1_funct_1(k7_relat_1('#skF_3','#skF_2'),'#skF_1') = k1_funct_1('#skF_3','#skF_1')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_106,c_108])).

tff(c_114,plain,(
    k1_funct_1(k7_relat_1('#skF_3','#skF_2'),'#skF_1') = k1_funct_1('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_12,c_111])).

tff(c_116,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_8,c_114])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:15:16 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.63/1.13  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.63/1.13  
% 1.63/1.13  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.63/1.13  %$ r2_hidden > v1_relat_1 > v1_funct_1 > k7_relat_1 > k3_xboole_0 > k1_funct_1 > #nlpp > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 1.63/1.13  
% 1.63/1.13  %Foreground sorts:
% 1.63/1.13  
% 1.63/1.13  
% 1.63/1.13  %Background operators:
% 1.63/1.13  
% 1.63/1.13  
% 1.63/1.13  %Foreground operators:
% 1.63/1.13  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 1.63/1.13  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.63/1.13  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.63/1.13  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 1.63/1.13  tff('#skF_2', type, '#skF_2': $i).
% 1.63/1.13  tff('#skF_3', type, '#skF_3': $i).
% 1.63/1.13  tff('#skF_1', type, '#skF_1': $i).
% 1.63/1.13  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 1.63/1.13  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.63/1.13  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.63/1.13  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.63/1.13  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.63/1.13  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.63/1.13  
% 1.63/1.14  tff(f_48, negated_conjecture, ~(![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(A, k3_xboole_0(k1_relat_1(C), B)) => (k1_funct_1(k7_relat_1(C, B), A) = k1_funct_1(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_funct_1)).
% 1.63/1.14  tff(f_31, axiom, (![A, B]: (v1_relat_1(B) => (k1_relat_1(k7_relat_1(B, A)) = k3_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t90_relat_1)).
% 1.63/1.14  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 1.63/1.14  tff(f_39, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(A, k1_relat_1(k7_relat_1(C, B))) => (k1_funct_1(k7_relat_1(C, B), A) = k1_funct_1(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_funct_1)).
% 1.63/1.14  tff(c_8, plain, (k1_funct_1(k7_relat_1('#skF_3', '#skF_2'), '#skF_1')!=k1_funct_1('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_48])).
% 1.63/1.14  tff(c_14, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_48])).
% 1.63/1.14  tff(c_12, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_48])).
% 1.63/1.14  tff(c_49, plain, (![B_10, A_11]: (k3_xboole_0(k1_relat_1(B_10), A_11)=k1_relat_1(k7_relat_1(B_10, A_11)) | ~v1_relat_1(B_10))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.63/1.14  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.63/1.14  tff(c_72, plain, (![A_12, B_13]: (k3_xboole_0(A_12, k1_relat_1(B_13))=k1_relat_1(k7_relat_1(B_13, A_12)) | ~v1_relat_1(B_13))), inference(superposition, [status(thm), theory('equality')], [c_49, c_2])).
% 1.63/1.14  tff(c_10, plain, (r2_hidden('#skF_1', k3_xboole_0(k1_relat_1('#skF_3'), '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_48])).
% 1.63/1.14  tff(c_15, plain, (r2_hidden('#skF_1', k3_xboole_0('#skF_2', k1_relat_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_10])).
% 1.63/1.14  tff(c_88, plain, (r2_hidden('#skF_1', k1_relat_1(k7_relat_1('#skF_3', '#skF_2'))) | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_72, c_15])).
% 1.63/1.14  tff(c_106, plain, (r2_hidden('#skF_1', k1_relat_1(k7_relat_1('#skF_3', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_88])).
% 1.63/1.14  tff(c_108, plain, (![C_14, B_15, A_16]: (k1_funct_1(k7_relat_1(C_14, B_15), A_16)=k1_funct_1(C_14, A_16) | ~r2_hidden(A_16, k1_relat_1(k7_relat_1(C_14, B_15))) | ~v1_funct_1(C_14) | ~v1_relat_1(C_14))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.63/1.14  tff(c_111, plain, (k1_funct_1(k7_relat_1('#skF_3', '#skF_2'), '#skF_1')=k1_funct_1('#skF_3', '#skF_1') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_106, c_108])).
% 1.63/1.14  tff(c_114, plain, (k1_funct_1(k7_relat_1('#skF_3', '#skF_2'), '#skF_1')=k1_funct_1('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_14, c_12, c_111])).
% 1.63/1.14  tff(c_116, plain, $false, inference(negUnitSimplification, [status(thm)], [c_8, c_114])).
% 1.63/1.14  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.63/1.14  
% 1.63/1.14  Inference rules
% 1.63/1.14  ----------------------
% 1.63/1.14  #Ref     : 0
% 1.63/1.14  #Sup     : 24
% 1.63/1.14  #Fact    : 0
% 1.63/1.14  #Define  : 0
% 1.63/1.14  #Split   : 0
% 1.63/1.14  #Chain   : 0
% 1.63/1.14  #Close   : 0
% 1.63/1.14  
% 1.63/1.14  Ordering : KBO
% 1.63/1.14  
% 1.63/1.14  Simplification rules
% 1.63/1.14  ----------------------
% 1.63/1.14  #Subsume      : 5
% 1.63/1.14  #Demod        : 4
% 1.63/1.14  #Tautology    : 12
% 1.63/1.14  #SimpNegUnit  : 1
% 1.63/1.14  #BackRed      : 0
% 1.63/1.14  
% 1.63/1.14  #Partial instantiations: 0
% 1.63/1.14  #Strategies tried      : 1
% 1.63/1.14  
% 1.63/1.14  Timing (in seconds)
% 1.63/1.14  ----------------------
% 1.63/1.15  Preprocessing        : 0.27
% 1.63/1.15  Parsing              : 0.15
% 1.63/1.15  CNF conversion       : 0.02
% 1.63/1.15  Main loop            : 0.11
% 1.63/1.15  Inferencing          : 0.04
% 1.63/1.15  Reduction            : 0.04
% 1.63/1.15  Demodulation         : 0.03
% 1.63/1.15  BG Simplification    : 0.01
% 1.63/1.15  Subsumption          : 0.01
% 1.63/1.15  Abstraction          : 0.01
% 1.63/1.15  MUC search           : 0.00
% 1.63/1.15  Cooper               : 0.00
% 1.63/1.15  Total                : 0.40
% 1.63/1.15  Index Insertion      : 0.00
% 1.63/1.15  Index Deletion       : 0.00
% 1.63/1.15  Index Matching       : 0.00
% 1.63/1.15  BG Taut test         : 0.00
%------------------------------------------------------------------------------
