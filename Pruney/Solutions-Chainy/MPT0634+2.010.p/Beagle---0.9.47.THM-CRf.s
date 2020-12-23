%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:03:20 EST 2020

% Result     : Theorem 1.55s
% Output     : CNFRefutation 1.55s
% Verified   : 
% Statistics : Number of formulae       :   26 (  29 expanded)
%              Number of leaves         :   18 (  20 expanded)
%              Depth                    :    5
%              Number of atoms          :   18 (  25 expanded)
%              Number of equality atoms :    8 (  10 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_relat_1 > v1_funct_1 > k1_enumset1 > k7_relat_1 > k5_relat_1 > k3_xboole_0 > k2_tarski > #nlpp > k6_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_44,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_relat_1(B)
          & v1_funct_1(B) )
       => k1_relat_1(k5_relat_1(k6_relat_1(A),B)) = k3_xboole_0(k1_relat_1(B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_funct_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k1_relat_1(k7_relat_1(B,A)) = k3_xboole_0(k1_relat_1(B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t90_relat_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k7_relat_1(B,A) = k5_relat_1(k6_relat_1(A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).

tff(c_14,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_47,plain,(
    ! [B_15,A_16] :
      ( k3_xboole_0(k1_relat_1(B_15),A_16) = k1_relat_1(k7_relat_1(B_15,A_16))
      | ~ v1_relat_1(B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_8,plain,(
    ! [A_7,B_8] :
      ( k5_relat_1(k6_relat_1(A_7),B_8) = k7_relat_1(B_8,A_7)
      | ~ v1_relat_1(B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_10,plain,(
    k1_relat_1(k5_relat_1(k6_relat_1('#skF_1'),'#skF_2')) != k3_xboole_0(k1_relat_1('#skF_2'),'#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_44,plain,
    ( k3_xboole_0(k1_relat_1('#skF_2'),'#skF_1') != k1_relat_1(k7_relat_1('#skF_2','#skF_1'))
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_10])).

tff(c_46,plain,(
    k3_xboole_0(k1_relat_1('#skF_2'),'#skF_1') != k1_relat_1(k7_relat_1('#skF_2','#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_44])).

tff(c_53,plain,(
    ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_47,c_46])).

tff(c_61,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_53])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n001.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 18:04:45 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.55/1.12  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.55/1.12  
% 1.55/1.12  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.55/1.13  %$ v1_relat_1 > v1_funct_1 > k1_enumset1 > k7_relat_1 > k5_relat_1 > k3_xboole_0 > k2_tarski > #nlpp > k6_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1
% 1.55/1.13  
% 1.55/1.13  %Foreground sorts:
% 1.55/1.13  
% 1.55/1.13  
% 1.55/1.13  %Background operators:
% 1.55/1.13  
% 1.55/1.13  
% 1.55/1.13  %Foreground operators:
% 1.55/1.13  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 1.55/1.13  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.55/1.13  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 1.55/1.13  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 1.55/1.13  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.55/1.13  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.55/1.13  tff('#skF_2', type, '#skF_2': $i).
% 1.55/1.13  tff('#skF_1', type, '#skF_1': $i).
% 1.55/1.13  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.55/1.13  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.55/1.13  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 1.55/1.13  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.55/1.13  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.55/1.13  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.55/1.13  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 1.55/1.13  
% 1.55/1.13  tff(f_44, negated_conjecture, ~(![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (k1_relat_1(k5_relat_1(k6_relat_1(A), B)) = k3_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t37_funct_1)).
% 1.55/1.13  tff(f_33, axiom, (![A, B]: (v1_relat_1(B) => (k1_relat_1(k7_relat_1(B, A)) = k3_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t90_relat_1)).
% 1.55/1.13  tff(f_37, axiom, (![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k5_relat_1(k6_relat_1(A), B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t94_relat_1)).
% 1.55/1.13  tff(c_14, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_44])).
% 1.55/1.13  tff(c_47, plain, (![B_15, A_16]: (k3_xboole_0(k1_relat_1(B_15), A_16)=k1_relat_1(k7_relat_1(B_15, A_16)) | ~v1_relat_1(B_15))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.55/1.13  tff(c_8, plain, (![A_7, B_8]: (k5_relat_1(k6_relat_1(A_7), B_8)=k7_relat_1(B_8, A_7) | ~v1_relat_1(B_8))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.55/1.13  tff(c_10, plain, (k1_relat_1(k5_relat_1(k6_relat_1('#skF_1'), '#skF_2'))!=k3_xboole_0(k1_relat_1('#skF_2'), '#skF_1')), inference(cnfTransformation, [status(thm)], [f_44])).
% 1.55/1.13  tff(c_44, plain, (k3_xboole_0(k1_relat_1('#skF_2'), '#skF_1')!=k1_relat_1(k7_relat_1('#skF_2', '#skF_1')) | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_8, c_10])).
% 1.55/1.13  tff(c_46, plain, (k3_xboole_0(k1_relat_1('#skF_2'), '#skF_1')!=k1_relat_1(k7_relat_1('#skF_2', '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_44])).
% 1.55/1.13  tff(c_53, plain, (~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_47, c_46])).
% 1.55/1.13  tff(c_61, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_14, c_53])).
% 1.55/1.13  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.55/1.13  
% 1.55/1.13  Inference rules
% 1.55/1.13  ----------------------
% 1.55/1.13  #Ref     : 0
% 1.55/1.13  #Sup     : 10
% 1.55/1.13  #Fact    : 0
% 1.55/1.13  #Define  : 0
% 1.55/1.13  #Split   : 0
% 1.55/1.13  #Chain   : 0
% 1.55/1.13  #Close   : 0
% 1.55/1.13  
% 1.55/1.13  Ordering : KBO
% 1.55/1.13  
% 1.55/1.13  Simplification rules
% 1.55/1.13  ----------------------
% 1.55/1.13  #Subsume      : 0
% 1.55/1.13  #Demod        : 2
% 1.55/1.13  #Tautology    : 7
% 1.55/1.13  #SimpNegUnit  : 0
% 1.55/1.13  #BackRed      : 0
% 1.55/1.13  
% 1.55/1.13  #Partial instantiations: 0
% 1.55/1.13  #Strategies tried      : 1
% 1.55/1.13  
% 1.55/1.13  Timing (in seconds)
% 1.55/1.13  ----------------------
% 1.55/1.13  Preprocessing        : 0.27
% 1.55/1.13  Parsing              : 0.15
% 1.55/1.14  CNF conversion       : 0.01
% 1.55/1.14  Main loop            : 0.07
% 1.55/1.14  Inferencing          : 0.03
% 1.55/1.14  Reduction            : 0.02
% 1.55/1.14  Demodulation         : 0.02
% 1.55/1.14  BG Simplification    : 0.01
% 1.55/1.14  Subsumption          : 0.01
% 1.55/1.14  Abstraction          : 0.01
% 1.55/1.14  MUC search           : 0.00
% 1.55/1.14  Cooper               : 0.00
% 1.55/1.14  Total                : 0.36
% 1.55/1.14  Index Insertion      : 0.00
% 1.55/1.14  Index Deletion       : 0.00
% 1.55/1.14  Index Matching       : 0.00
% 1.55/1.14  BG Taut test         : 0.00
%------------------------------------------------------------------------------
