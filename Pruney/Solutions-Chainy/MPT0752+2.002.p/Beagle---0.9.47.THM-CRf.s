%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:06:26 EST 2020

% Result     : Theorem 1.62s
% Output     : CNFRefutation 1.84s
% Verified   : 
% Statistics : Number of formulae       :   44 (  66 expanded)
%              Number of leaves         :   23 (  32 expanded)
%              Depth                    :    7
%              Number of atoms          :   53 (  88 expanded)
%              Number of equality atoms :    8 (   8 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > r1_tarski > v5_ordinal1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k4_xboole_0 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(v5_ordinal1,type,(
    v5_ordinal1: $i > $o )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_32,axiom,(
    ! [A] : k4_xboole_0(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).

tff(f_30,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_xboole_1)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_36,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relat_1)).

tff(f_45,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_42,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_53,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v5_ordinal1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc4_ordinal1)).

tff(f_49,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_funct_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_funct_1)).

tff(f_62,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(k1_xboole_0)
        & v5_relat_1(k1_xboole_0,A)
        & v1_funct_1(k1_xboole_0)
        & v5_ordinal1(k1_xboole_0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_ordinal1)).

tff(c_8,plain,(
    ! [A_3] : k4_xboole_0(k1_xboole_0,A_3) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( r1_tarski(A_1,B_2)
      | k4_xboole_0(A_1,B_2) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_33,plain,(
    ! [A_9] :
      ( v1_relat_1(A_9)
      | ~ v1_xboole_0(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_37,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_2,c_33])).

tff(c_16,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_80,plain,(
    ! [B_20,A_21] :
      ( v5_relat_1(B_20,A_21)
      | ~ r1_tarski(k2_relat_1(B_20),A_21)
      | ~ v1_relat_1(B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_90,plain,(
    ! [A_21] :
      ( v5_relat_1(k1_xboole_0,A_21)
      | ~ r1_tarski(k1_xboole_0,A_21)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_80])).

tff(c_95,plain,(
    ! [A_22] :
      ( v5_relat_1(k1_xboole_0,A_22)
      | ~ r1_tarski(k1_xboole_0,A_22) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_37,c_90])).

tff(c_22,plain,(
    ! [A_8] :
      ( v5_ordinal1(A_8)
      | ~ v1_xboole_0(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_45,plain,(
    ! [A_11] :
      ( v1_funct_1(A_11)
      | ~ v1_xboole_0(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_49,plain,(
    v1_funct_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_2,c_45])).

tff(c_24,plain,
    ( ~ v1_relat_1(k1_xboole_0)
    | ~ v5_relat_1(k1_xboole_0,'#skF_1')
    | ~ v1_funct_1(k1_xboole_0)
    | ~ v5_ordinal1(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_52,plain,
    ( ~ v5_relat_1(k1_xboole_0,'#skF_1')
    | ~ v5_ordinal1(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_49,c_37,c_24])).

tff(c_53,plain,(
    ~ v5_ordinal1(k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_52])).

tff(c_56,plain,(
    ~ v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_22,c_53])).

tff(c_60,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_56])).

tff(c_61,plain,(
    ~ v5_relat_1(k1_xboole_0,'#skF_1') ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_103,plain,(
    ~ r1_tarski(k1_xboole_0,'#skF_1') ),
    inference(resolution,[status(thm)],[c_95,c_61])).

tff(c_106,plain,(
    k4_xboole_0(k1_xboole_0,'#skF_1') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_4,c_103])).

tff(c_110,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_106])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n007.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 19:46:36 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.62/1.18  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.84/1.18  
% 1.84/1.18  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.84/1.19  %$ v5_relat_1 > r1_tarski > v5_ordinal1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k4_xboole_0 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_1
% 1.84/1.19  
% 1.84/1.19  %Foreground sorts:
% 1.84/1.19  
% 1.84/1.19  
% 1.84/1.19  %Background operators:
% 1.84/1.19  
% 1.84/1.19  
% 1.84/1.19  %Foreground operators:
% 1.84/1.19  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 1.84/1.19  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.84/1.19  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.84/1.19  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.84/1.19  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.84/1.19  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.84/1.19  tff(v5_ordinal1, type, v5_ordinal1: $i > $o).
% 1.84/1.19  tff('#skF_1', type, '#skF_1': $i).
% 1.84/1.19  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 1.84/1.19  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.84/1.19  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.84/1.19  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.84/1.19  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.84/1.19  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.84/1.19  
% 1.84/1.20  tff(f_32, axiom, (![A]: (k4_xboole_0(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_boole)).
% 1.84/1.20  tff(f_30, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t37_xboole_1)).
% 1.84/1.20  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 1.84/1.20  tff(f_36, axiom, (![A]: (v1_xboole_0(A) => v1_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relat_1)).
% 1.84/1.20  tff(f_45, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 1.84/1.20  tff(f_42, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 1.84/1.20  tff(f_53, axiom, (![A]: (v1_xboole_0(A) => v5_ordinal1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc4_ordinal1)).
% 1.84/1.20  tff(f_49, axiom, (![A]: (v1_xboole_0(A) => v1_funct_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_funct_1)).
% 1.84/1.20  tff(f_62, negated_conjecture, ~(![A]: (((v1_relat_1(k1_xboole_0) & v5_relat_1(k1_xboole_0, A)) & v1_funct_1(k1_xboole_0)) & v5_ordinal1(k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t45_ordinal1)).
% 1.84/1.20  tff(c_8, plain, (![A_3]: (k4_xboole_0(k1_xboole_0, A_3)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.84/1.20  tff(c_4, plain, (![A_1, B_2]: (r1_tarski(A_1, B_2) | k4_xboole_0(A_1, B_2)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_30])).
% 1.84/1.20  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 1.84/1.20  tff(c_33, plain, (![A_9]: (v1_relat_1(A_9) | ~v1_xboole_0(A_9))), inference(cnfTransformation, [status(thm)], [f_36])).
% 1.84/1.20  tff(c_37, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_33])).
% 1.84/1.20  tff(c_16, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.84/1.20  tff(c_80, plain, (![B_20, A_21]: (v5_relat_1(B_20, A_21) | ~r1_tarski(k2_relat_1(B_20), A_21) | ~v1_relat_1(B_20))), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.84/1.20  tff(c_90, plain, (![A_21]: (v5_relat_1(k1_xboole_0, A_21) | ~r1_tarski(k1_xboole_0, A_21) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_16, c_80])).
% 1.84/1.20  tff(c_95, plain, (![A_22]: (v5_relat_1(k1_xboole_0, A_22) | ~r1_tarski(k1_xboole_0, A_22))), inference(demodulation, [status(thm), theory('equality')], [c_37, c_90])).
% 1.84/1.20  tff(c_22, plain, (![A_8]: (v5_ordinal1(A_8) | ~v1_xboole_0(A_8))), inference(cnfTransformation, [status(thm)], [f_53])).
% 1.84/1.20  tff(c_45, plain, (![A_11]: (v1_funct_1(A_11) | ~v1_xboole_0(A_11))), inference(cnfTransformation, [status(thm)], [f_49])).
% 1.84/1.20  tff(c_49, plain, (v1_funct_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_45])).
% 1.84/1.20  tff(c_24, plain, (~v1_relat_1(k1_xboole_0) | ~v5_relat_1(k1_xboole_0, '#skF_1') | ~v1_funct_1(k1_xboole_0) | ~v5_ordinal1(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_62])).
% 1.84/1.20  tff(c_52, plain, (~v5_relat_1(k1_xboole_0, '#skF_1') | ~v5_ordinal1(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_49, c_37, c_24])).
% 1.84/1.20  tff(c_53, plain, (~v5_ordinal1(k1_xboole_0)), inference(splitLeft, [status(thm)], [c_52])).
% 1.84/1.20  tff(c_56, plain, (~v1_xboole_0(k1_xboole_0)), inference(resolution, [status(thm)], [c_22, c_53])).
% 1.84/1.20  tff(c_60, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2, c_56])).
% 1.84/1.20  tff(c_61, plain, (~v5_relat_1(k1_xboole_0, '#skF_1')), inference(splitRight, [status(thm)], [c_52])).
% 1.84/1.20  tff(c_103, plain, (~r1_tarski(k1_xboole_0, '#skF_1')), inference(resolution, [status(thm)], [c_95, c_61])).
% 1.84/1.20  tff(c_106, plain, (k4_xboole_0(k1_xboole_0, '#skF_1')!=k1_xboole_0), inference(resolution, [status(thm)], [c_4, c_103])).
% 1.84/1.20  tff(c_110, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_8, c_106])).
% 1.84/1.20  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.84/1.20  
% 1.84/1.20  Inference rules
% 1.84/1.20  ----------------------
% 1.84/1.20  #Ref     : 0
% 1.84/1.20  #Sup     : 18
% 1.84/1.20  #Fact    : 0
% 1.84/1.20  #Define  : 0
% 1.84/1.20  #Split   : 1
% 1.84/1.20  #Chain   : 0
% 1.84/1.20  #Close   : 0
% 1.84/1.20  
% 1.84/1.20  Ordering : KBO
% 1.84/1.20  
% 1.84/1.20  Simplification rules
% 1.84/1.20  ----------------------
% 1.84/1.20  #Subsume      : 0
% 1.84/1.20  #Demod        : 6
% 1.84/1.20  #Tautology    : 9
% 1.84/1.20  #SimpNegUnit  : 0
% 1.84/1.20  #BackRed      : 0
% 1.84/1.20  
% 1.84/1.20  #Partial instantiations: 0
% 1.84/1.20  #Strategies tried      : 1
% 1.84/1.20  
% 1.84/1.20  Timing (in seconds)
% 1.84/1.20  ----------------------
% 1.84/1.20  Preprocessing        : 0.28
% 1.84/1.20  Parsing              : 0.16
% 1.84/1.20  CNF conversion       : 0.02
% 1.84/1.20  Main loop            : 0.13
% 1.84/1.20  Inferencing          : 0.06
% 1.84/1.20  Reduction            : 0.03
% 1.84/1.20  Demodulation         : 0.02
% 1.84/1.20  BG Simplification    : 0.01
% 1.84/1.20  Subsumption          : 0.02
% 1.84/1.20  Abstraction          : 0.00
% 1.84/1.20  MUC search           : 0.00
% 1.84/1.20  Cooper               : 0.00
% 1.84/1.20  Total                : 0.44
% 1.84/1.20  Index Insertion      : 0.00
% 1.84/1.20  Index Deletion       : 0.00
% 1.84/1.20  Index Matching       : 0.00
% 1.84/1.20  BG Taut test         : 0.00
%------------------------------------------------------------------------------
