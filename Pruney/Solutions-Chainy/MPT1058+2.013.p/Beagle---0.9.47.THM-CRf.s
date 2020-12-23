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
% DateTime   : Thu Dec  3 10:17:23 EST 2020

% Result     : Theorem 3.26s
% Output     : CNFRefutation 3.26s
% Verified   : 
% Statistics : Number of formulae       :   44 (  47 expanded)
%              Number of leaves         :   25 (  28 expanded)
%              Depth                    :    8
%              Number of atoms          :   38 (  47 expanded)
%              Number of equality atoms :   21 (  24 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > v1_relat_1 > v1_funct_1 > k1_enumset1 > k7_relat_1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_73,negated_conjecture,(
    ~ ! [A] :
        ( ( v1_relat_1(A)
          & v1_funct_1(A) )
       => ! [B,C] :
            ( r1_tarski(k10_relat_1(A,C),B)
           => k10_relat_1(A,C) = k10_relat_1(k7_relat_1(A,B),C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t175_funct_2)).

tff(f_55,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_59,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

tff(f_53,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_xboole_0(A,k4_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t85_xboole_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_45,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_63,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k10_relat_1(k7_relat_1(C,A),B) = k3_xboole_0(A,k10_relat_1(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t139_funct_1)).

tff(c_32,plain,(
    k10_relat_1(k7_relat_1('#skF_1','#skF_2'),'#skF_3') != k10_relat_1('#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_38,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_24,plain,(
    ! [B_18,A_17] : k2_tarski(B_18,A_17) = k2_tarski(A_17,B_18) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_104,plain,(
    ! [A_41,B_42] : k1_setfam_1(k2_tarski(A_41,B_42)) = k3_xboole_0(A_41,B_42) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_119,plain,(
    ! [B_43,A_44] : k1_setfam_1(k2_tarski(B_43,A_44)) = k3_xboole_0(A_44,B_43) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_104])).

tff(c_28,plain,(
    ! [A_21,B_22] : k1_setfam_1(k2_tarski(A_21,B_22)) = k3_xboole_0(A_21,B_22) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_125,plain,(
    ! [B_43,A_44] : k3_xboole_0(B_43,A_44) = k3_xboole_0(A_44,B_43) ),
    inference(superposition,[status(thm),theory(equality)],[c_119,c_28])).

tff(c_34,plain,(
    r1_tarski(k10_relat_1('#skF_1','#skF_3'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_175,plain,(
    ! [A_47,C_48,B_49] :
      ( r1_xboole_0(A_47,k4_xboole_0(C_48,B_49))
      | ~ r1_tarski(A_47,B_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_18,plain,(
    ! [A_12,B_13] :
      ( k4_xboole_0(A_12,B_13) = A_12
      | ~ r1_xboole_0(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_1171,plain,(
    ! [A_103,C_104,B_105] :
      ( k4_xboole_0(A_103,k4_xboole_0(C_104,B_105)) = A_103
      | ~ r1_tarski(A_103,B_105) ) ),
    inference(resolution,[status(thm)],[c_175,c_18])).

tff(c_16,plain,(
    ! [A_10,B_11] : k4_xboole_0(A_10,k4_xboole_0(A_10,B_11)) = k3_xboole_0(A_10,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_1270,plain,(
    ! [C_106,B_107] :
      ( k3_xboole_0(C_106,B_107) = C_106
      | ~ r1_tarski(C_106,B_107) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1171,c_16])).

tff(c_1328,plain,(
    k3_xboole_0(k10_relat_1('#skF_1','#skF_3'),'#skF_2') = k10_relat_1('#skF_1','#skF_3') ),
    inference(resolution,[status(thm)],[c_34,c_1270])).

tff(c_1358,plain,(
    k3_xboole_0('#skF_2',k10_relat_1('#skF_1','#skF_3')) = k10_relat_1('#skF_1','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_125,c_1328])).

tff(c_30,plain,(
    ! [A_23,C_25,B_24] :
      ( k3_xboole_0(A_23,k10_relat_1(C_25,B_24)) = k10_relat_1(k7_relat_1(C_25,A_23),B_24)
      | ~ v1_relat_1(C_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_1758,plain,
    ( k10_relat_1(k7_relat_1('#skF_1','#skF_2'),'#skF_3') = k10_relat_1('#skF_1','#skF_3')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_1358,c_30])).

tff(c_1778,plain,(
    k10_relat_1(k7_relat_1('#skF_1','#skF_2'),'#skF_3') = k10_relat_1('#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_1758])).

tff(c_1780,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_1778])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:11:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.26/1.56  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.26/1.57  
% 3.26/1.57  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.26/1.57  %$ r1_xboole_0 > r1_tarski > v1_relat_1 > v1_funct_1 > k1_enumset1 > k7_relat_1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 3.26/1.57  
% 3.26/1.57  %Foreground sorts:
% 3.26/1.57  
% 3.26/1.57  
% 3.26/1.57  %Background operators:
% 3.26/1.57  
% 3.26/1.57  
% 3.26/1.57  %Foreground operators:
% 3.26/1.57  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.26/1.57  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.26/1.57  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.26/1.57  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 3.26/1.57  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.26/1.57  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.26/1.57  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.26/1.57  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.26/1.57  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.26/1.57  tff('#skF_2', type, '#skF_2': $i).
% 3.26/1.57  tff('#skF_3', type, '#skF_3': $i).
% 3.26/1.57  tff('#skF_1', type, '#skF_1': $i).
% 3.26/1.57  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.26/1.57  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 3.26/1.57  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.26/1.57  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.26/1.57  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.26/1.57  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 3.26/1.57  
% 3.26/1.58  tff(f_73, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B, C]: (r1_tarski(k10_relat_1(A, C), B) => (k10_relat_1(A, C) = k10_relat_1(k7_relat_1(A, B), C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t175_funct_2)).
% 3.26/1.58  tff(f_55, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 3.26/1.58  tff(f_59, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 3.26/1.58  tff(f_53, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_xboole_0(A, k4_xboole_0(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t85_xboole_1)).
% 3.26/1.58  tff(f_49, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_xboole_1)).
% 3.26/1.58  tff(f_45, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 3.26/1.58  tff(f_63, axiom, (![A, B, C]: (v1_relat_1(C) => (k10_relat_1(k7_relat_1(C, A), B) = k3_xboole_0(A, k10_relat_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t139_funct_1)).
% 3.26/1.58  tff(c_32, plain, (k10_relat_1(k7_relat_1('#skF_1', '#skF_2'), '#skF_3')!=k10_relat_1('#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.26/1.58  tff(c_38, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.26/1.58  tff(c_24, plain, (![B_18, A_17]: (k2_tarski(B_18, A_17)=k2_tarski(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.26/1.58  tff(c_104, plain, (![A_41, B_42]: (k1_setfam_1(k2_tarski(A_41, B_42))=k3_xboole_0(A_41, B_42))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.26/1.58  tff(c_119, plain, (![B_43, A_44]: (k1_setfam_1(k2_tarski(B_43, A_44))=k3_xboole_0(A_44, B_43))), inference(superposition, [status(thm), theory('equality')], [c_24, c_104])).
% 3.26/1.58  tff(c_28, plain, (![A_21, B_22]: (k1_setfam_1(k2_tarski(A_21, B_22))=k3_xboole_0(A_21, B_22))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.26/1.58  tff(c_125, plain, (![B_43, A_44]: (k3_xboole_0(B_43, A_44)=k3_xboole_0(A_44, B_43))), inference(superposition, [status(thm), theory('equality')], [c_119, c_28])).
% 3.26/1.58  tff(c_34, plain, (r1_tarski(k10_relat_1('#skF_1', '#skF_3'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.26/1.58  tff(c_175, plain, (![A_47, C_48, B_49]: (r1_xboole_0(A_47, k4_xboole_0(C_48, B_49)) | ~r1_tarski(A_47, B_49))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.26/1.58  tff(c_18, plain, (![A_12, B_13]: (k4_xboole_0(A_12, B_13)=A_12 | ~r1_xboole_0(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.26/1.58  tff(c_1171, plain, (![A_103, C_104, B_105]: (k4_xboole_0(A_103, k4_xboole_0(C_104, B_105))=A_103 | ~r1_tarski(A_103, B_105))), inference(resolution, [status(thm)], [c_175, c_18])).
% 3.26/1.58  tff(c_16, plain, (![A_10, B_11]: (k4_xboole_0(A_10, k4_xboole_0(A_10, B_11))=k3_xboole_0(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.26/1.58  tff(c_1270, plain, (![C_106, B_107]: (k3_xboole_0(C_106, B_107)=C_106 | ~r1_tarski(C_106, B_107))), inference(superposition, [status(thm), theory('equality')], [c_1171, c_16])).
% 3.26/1.58  tff(c_1328, plain, (k3_xboole_0(k10_relat_1('#skF_1', '#skF_3'), '#skF_2')=k10_relat_1('#skF_1', '#skF_3')), inference(resolution, [status(thm)], [c_34, c_1270])).
% 3.26/1.58  tff(c_1358, plain, (k3_xboole_0('#skF_2', k10_relat_1('#skF_1', '#skF_3'))=k10_relat_1('#skF_1', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_125, c_1328])).
% 3.26/1.58  tff(c_30, plain, (![A_23, C_25, B_24]: (k3_xboole_0(A_23, k10_relat_1(C_25, B_24))=k10_relat_1(k7_relat_1(C_25, A_23), B_24) | ~v1_relat_1(C_25))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.26/1.58  tff(c_1758, plain, (k10_relat_1(k7_relat_1('#skF_1', '#skF_2'), '#skF_3')=k10_relat_1('#skF_1', '#skF_3') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_1358, c_30])).
% 3.26/1.58  tff(c_1778, plain, (k10_relat_1(k7_relat_1('#skF_1', '#skF_2'), '#skF_3')=k10_relat_1('#skF_1', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_1758])).
% 3.26/1.58  tff(c_1780, plain, $false, inference(negUnitSimplification, [status(thm)], [c_32, c_1778])).
% 3.26/1.58  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.26/1.58  
% 3.26/1.58  Inference rules
% 3.26/1.58  ----------------------
% 3.26/1.58  #Ref     : 0
% 3.26/1.58  #Sup     : 410
% 3.26/1.58  #Fact    : 0
% 3.26/1.58  #Define  : 0
% 3.26/1.58  #Split   : 1
% 3.26/1.58  #Chain   : 0
% 3.26/1.58  #Close   : 0
% 3.26/1.58  
% 3.26/1.58  Ordering : KBO
% 3.26/1.58  
% 3.26/1.58  Simplification rules
% 3.26/1.58  ----------------------
% 3.26/1.58  #Subsume      : 7
% 3.26/1.58  #Demod        : 287
% 3.26/1.58  #Tautology    : 260
% 3.26/1.58  #SimpNegUnit  : 1
% 3.26/1.58  #BackRed      : 1
% 3.26/1.58  
% 3.26/1.58  #Partial instantiations: 0
% 3.26/1.58  #Strategies tried      : 1
% 3.26/1.58  
% 3.26/1.58  Timing (in seconds)
% 3.26/1.58  ----------------------
% 3.26/1.58  Preprocessing        : 0.32
% 3.26/1.58  Parsing              : 0.17
% 3.26/1.58  CNF conversion       : 0.02
% 3.26/1.58  Main loop            : 0.49
% 3.26/1.58  Inferencing          : 0.15
% 3.26/1.58  Reduction            : 0.20
% 3.26/1.58  Demodulation         : 0.16
% 3.26/1.59  BG Simplification    : 0.02
% 3.26/1.59  Subsumption          : 0.08
% 3.26/1.59  Abstraction          : 0.03
% 3.26/1.59  MUC search           : 0.00
% 3.26/1.59  Cooper               : 0.00
% 3.26/1.59  Total                : 0.84
% 3.26/1.59  Index Insertion      : 0.00
% 3.26/1.59  Index Deletion       : 0.00
% 3.26/1.59  Index Matching       : 0.00
% 3.26/1.59  BG Taut test         : 0.00
%------------------------------------------------------------------------------
