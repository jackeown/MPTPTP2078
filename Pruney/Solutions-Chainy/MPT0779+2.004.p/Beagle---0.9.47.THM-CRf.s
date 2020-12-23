%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:06:39 EST 2020

% Result     : Theorem 1.94s
% Output     : CNFRefutation 2.04s
% Verified   : 
% Statistics : Number of formulae       :   41 (  45 expanded)
%              Number of leaves         :   27 (  30 expanded)
%              Depth                    :    6
%              Number of atoms          :   29 (  36 expanded)
%              Number of equality atoms :   17 (  23 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_relat_1 > v1_funct_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_relat_1 > k3_xboole_0 > k2_wellord1 > k2_tarski > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

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

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(k2_wellord1,type,(
    k2_wellord1: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_62,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => k2_wellord1(k2_wellord1(B,A),A) = k2_wellord1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_wellord1)).

tff(f_43,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_51,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v1_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).

tff(f_53,axiom,(
    ! [A,B] : k5_relat_1(k6_relat_1(B),k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_funct_1)).

tff(f_47,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k5_relat_1(A,k6_relat_1(k2_relat_1(A))) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t80_relat_1)).

tff(f_57,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k2_wellord1(k2_wellord1(C,A),B) = k2_wellord1(C,k3_xboole_0(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_wellord1)).

tff(c_32,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_16,plain,(
    ! [A_30] : k1_relat_1(k6_relat_1(A_30)) = A_30 ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_22,plain,(
    ! [A_32] : v1_relat_1(k6_relat_1(A_32)) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_18,plain,(
    ! [A_30] : k2_relat_1(k6_relat_1(A_30)) = A_30 ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_94,plain,(
    ! [B_48,A_49] : k5_relat_1(k6_relat_1(B_48),k6_relat_1(A_49)) = k6_relat_1(k3_xboole_0(A_49,B_48)) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_20,plain,(
    ! [A_31] :
      ( k5_relat_1(A_31,k6_relat_1(k2_relat_1(A_31))) = A_31
      | ~ v1_relat_1(A_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_105,plain,(
    ! [B_48] :
      ( k6_relat_1(k3_xboole_0(k2_relat_1(k6_relat_1(B_48)),B_48)) = k6_relat_1(B_48)
      | ~ v1_relat_1(k6_relat_1(B_48)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_94,c_20])).

tff(c_122,plain,(
    ! [B_50] : k6_relat_1(k3_xboole_0(B_50,B_50)) = k6_relat_1(B_50) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_18,c_105])).

tff(c_140,plain,(
    ! [B_50] : k3_xboole_0(B_50,B_50) = k1_relat_1(k6_relat_1(B_50)) ),
    inference(superposition,[status(thm),theory(equality)],[c_122,c_16])).

tff(c_156,plain,(
    ! [B_50] : k3_xboole_0(B_50,B_50) = B_50 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_140])).

tff(c_195,plain,(
    ! [C_59,A_60,B_61] :
      ( k2_wellord1(k2_wellord1(C_59,A_60),B_61) = k2_wellord1(C_59,k3_xboole_0(A_60,B_61))
      | ~ v1_relat_1(C_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_30,plain,(
    k2_wellord1(k2_wellord1('#skF_2','#skF_1'),'#skF_1') != k2_wellord1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_204,plain,
    ( k2_wellord1('#skF_2',k3_xboole_0('#skF_1','#skF_1')) != k2_wellord1('#skF_2','#skF_1')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_195,c_30])).

tff(c_214,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_156,c_204])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:56:11 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.94/1.21  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.94/1.22  
% 1.94/1.22  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.02/1.22  %$ v1_relat_1 > v1_funct_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_relat_1 > k3_xboole_0 > k2_wellord1 > k2_tarski > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1
% 2.02/1.22  
% 2.02/1.22  %Foreground sorts:
% 2.02/1.22  
% 2.02/1.22  
% 2.02/1.22  %Background operators:
% 2.02/1.22  
% 2.02/1.22  
% 2.02/1.22  %Foreground operators:
% 2.02/1.22  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.02/1.22  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.02/1.22  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.02/1.22  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.02/1.22  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.02/1.22  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.02/1.22  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.02/1.22  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.02/1.22  tff('#skF_2', type, '#skF_2': $i).
% 2.02/1.22  tff('#skF_1', type, '#skF_1': $i).
% 2.02/1.22  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.02/1.22  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.02/1.22  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.02/1.22  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.02/1.22  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 2.02/1.22  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.02/1.22  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.02/1.22  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.02/1.22  tff(k2_wellord1, type, k2_wellord1: ($i * $i) > $i).
% 2.02/1.22  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.02/1.22  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.02/1.22  
% 2.04/1.23  tff(f_62, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => (k2_wellord1(k2_wellord1(B, A), A) = k2_wellord1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_wellord1)).
% 2.04/1.23  tff(f_43, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 2.04/1.23  tff(f_51, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v1_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc3_funct_1)).
% 2.04/1.23  tff(f_53, axiom, (![A, B]: (k5_relat_1(k6_relat_1(B), k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_funct_1)).
% 2.04/1.23  tff(f_47, axiom, (![A]: (v1_relat_1(A) => (k5_relat_1(A, k6_relat_1(k2_relat_1(A))) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t80_relat_1)).
% 2.04/1.23  tff(f_57, axiom, (![A, B, C]: (v1_relat_1(C) => (k2_wellord1(k2_wellord1(C, A), B) = k2_wellord1(C, k3_xboole_0(A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t26_wellord1)).
% 2.04/1.23  tff(c_32, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.04/1.23  tff(c_16, plain, (![A_30]: (k1_relat_1(k6_relat_1(A_30))=A_30)), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.04/1.23  tff(c_22, plain, (![A_32]: (v1_relat_1(k6_relat_1(A_32)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.04/1.23  tff(c_18, plain, (![A_30]: (k2_relat_1(k6_relat_1(A_30))=A_30)), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.04/1.23  tff(c_94, plain, (![B_48, A_49]: (k5_relat_1(k6_relat_1(B_48), k6_relat_1(A_49))=k6_relat_1(k3_xboole_0(A_49, B_48)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.04/1.23  tff(c_20, plain, (![A_31]: (k5_relat_1(A_31, k6_relat_1(k2_relat_1(A_31)))=A_31 | ~v1_relat_1(A_31))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.04/1.23  tff(c_105, plain, (![B_48]: (k6_relat_1(k3_xboole_0(k2_relat_1(k6_relat_1(B_48)), B_48))=k6_relat_1(B_48) | ~v1_relat_1(k6_relat_1(B_48)))), inference(superposition, [status(thm), theory('equality')], [c_94, c_20])).
% 2.04/1.23  tff(c_122, plain, (![B_50]: (k6_relat_1(k3_xboole_0(B_50, B_50))=k6_relat_1(B_50))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_18, c_105])).
% 2.04/1.23  tff(c_140, plain, (![B_50]: (k3_xboole_0(B_50, B_50)=k1_relat_1(k6_relat_1(B_50)))), inference(superposition, [status(thm), theory('equality')], [c_122, c_16])).
% 2.04/1.23  tff(c_156, plain, (![B_50]: (k3_xboole_0(B_50, B_50)=B_50)), inference(demodulation, [status(thm), theory('equality')], [c_16, c_140])).
% 2.04/1.23  tff(c_195, plain, (![C_59, A_60, B_61]: (k2_wellord1(k2_wellord1(C_59, A_60), B_61)=k2_wellord1(C_59, k3_xboole_0(A_60, B_61)) | ~v1_relat_1(C_59))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.04/1.23  tff(c_30, plain, (k2_wellord1(k2_wellord1('#skF_2', '#skF_1'), '#skF_1')!=k2_wellord1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.04/1.23  tff(c_204, plain, (k2_wellord1('#skF_2', k3_xboole_0('#skF_1', '#skF_1'))!=k2_wellord1('#skF_2', '#skF_1') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_195, c_30])).
% 2.04/1.23  tff(c_214, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_32, c_156, c_204])).
% 2.04/1.23  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.04/1.23  
% 2.04/1.23  Inference rules
% 2.04/1.23  ----------------------
% 2.04/1.23  #Ref     : 0
% 2.04/1.23  #Sup     : 40
% 2.04/1.23  #Fact    : 0
% 2.04/1.23  #Define  : 0
% 2.04/1.23  #Split   : 0
% 2.04/1.23  #Chain   : 0
% 2.04/1.23  #Close   : 0
% 2.04/1.23  
% 2.04/1.23  Ordering : KBO
% 2.04/1.23  
% 2.04/1.23  Simplification rules
% 2.04/1.23  ----------------------
% 2.04/1.23  #Subsume      : 0
% 2.04/1.23  #Demod        : 26
% 2.04/1.23  #Tautology    : 34
% 2.04/1.23  #SimpNegUnit  : 0
% 2.04/1.23  #BackRed      : 0
% 2.04/1.23  
% 2.04/1.23  #Partial instantiations: 0
% 2.04/1.23  #Strategies tried      : 1
% 2.04/1.23  
% 2.04/1.23  Timing (in seconds)
% 2.04/1.23  ----------------------
% 2.04/1.23  Preprocessing        : 0.32
% 2.04/1.23  Parsing              : 0.17
% 2.04/1.23  CNF conversion       : 0.02
% 2.04/1.23  Main loop            : 0.13
% 2.04/1.23  Inferencing          : 0.05
% 2.04/1.23  Reduction            : 0.04
% 2.04/1.23  Demodulation         : 0.03
% 2.04/1.23  BG Simplification    : 0.01
% 2.04/1.23  Subsumption          : 0.01
% 2.04/1.23  Abstraction          : 0.01
% 2.04/1.23  MUC search           : 0.00
% 2.04/1.23  Cooper               : 0.00
% 2.04/1.23  Total                : 0.47
% 2.04/1.23  Index Insertion      : 0.00
% 2.04/1.23  Index Deletion       : 0.00
% 2.04/1.23  Index Matching       : 0.00
% 2.04/1.23  BG Taut test         : 0.00
%------------------------------------------------------------------------------
