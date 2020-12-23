%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:00:37 EST 2020

% Result     : Theorem 1.88s
% Output     : CNFRefutation 1.88s
% Verified   : 
% Statistics : Number of formulae       :   38 (  44 expanded)
%              Number of leaves         :   21 (  24 expanded)
%              Depth                    :    8
%              Number of atoms          :   41 (  50 expanded)
%              Number of equality atoms :   21 (  23 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > v1_xboole_0 > v1_relat_1 > k9_relat_1 > k7_relat_1 > k4_xboole_0 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

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

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_36,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relat_1)).

tff(f_43,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_28,axiom,(
    ! [A] : k4_xboole_0(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( k7_relat_1(B,A) = k1_xboole_0
      <=> r1_xboole_0(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_relat_1)).

tff(f_40,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_52,negated_conjecture,(
    ~ ! [A] : k9_relat_1(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t150_relat_1)).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_38,plain,(
    ! [A_10] :
      ( v1_relat_1(A_10)
      | ~ v1_xboole_0(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_42,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_2,c_38])).

tff(c_14,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_4,plain,(
    ! [A_1] : k4_xboole_0(k1_xboole_0,A_1) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_8,plain,(
    ! [A_2,B_3] :
      ( r1_xboole_0(A_2,B_3)
      | k4_xboole_0(A_2,B_3) != A_2 ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_16,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_74,plain,(
    ! [B_20,A_21] :
      ( k7_relat_1(B_20,A_21) = k1_xboole_0
      | ~ r1_xboole_0(k1_relat_1(B_20),A_21)
      | ~ v1_relat_1(B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_84,plain,(
    ! [A_21] :
      ( k7_relat_1(k1_xboole_0,A_21) = k1_xboole_0
      | ~ r1_xboole_0(k1_xboole_0,A_21)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_74])).

tff(c_89,plain,(
    ! [A_22] :
      ( k7_relat_1(k1_xboole_0,A_22) = k1_xboole_0
      | ~ r1_xboole_0(k1_xboole_0,A_22) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_84])).

tff(c_96,plain,(
    ! [B_3] :
      ( k7_relat_1(k1_xboole_0,B_3) = k1_xboole_0
      | k4_xboole_0(k1_xboole_0,B_3) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_8,c_89])).

tff(c_104,plain,(
    ! [B_23] : k7_relat_1(k1_xboole_0,B_23) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_96])).

tff(c_12,plain,(
    ! [B_6,A_5] :
      ( k2_relat_1(k7_relat_1(B_6,A_5)) = k9_relat_1(B_6,A_5)
      | ~ v1_relat_1(B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_109,plain,(
    ! [B_23] :
      ( k9_relat_1(k1_xboole_0,B_23) = k2_relat_1(k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_104,c_12])).

tff(c_114,plain,(
    ! [B_23] : k9_relat_1(k1_xboole_0,B_23) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_14,c_109])).

tff(c_22,plain,(
    k9_relat_1(k1_xboole_0,'#skF_1') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_138,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_114,c_22])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:50:56 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.88/1.19  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.88/1.20  
% 1.88/1.20  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.88/1.20  %$ r1_xboole_0 > v1_xboole_0 > v1_relat_1 > k9_relat_1 > k7_relat_1 > k4_xboole_0 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_1
% 1.88/1.20  
% 1.88/1.20  %Foreground sorts:
% 1.88/1.20  
% 1.88/1.20  
% 1.88/1.20  %Background operators:
% 1.88/1.20  
% 1.88/1.20  
% 1.88/1.20  %Foreground operators:
% 1.88/1.20  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.88/1.20  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.88/1.20  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 1.88/1.20  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.88/1.20  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.88/1.20  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.88/1.20  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 1.88/1.20  tff('#skF_1', type, '#skF_1': $i).
% 1.88/1.20  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.88/1.20  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.88/1.20  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.88/1.20  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.88/1.20  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.88/1.20  
% 1.88/1.21  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 1.88/1.21  tff(f_36, axiom, (![A]: (v1_xboole_0(A) => v1_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relat_1)).
% 1.88/1.21  tff(f_43, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 1.88/1.21  tff(f_28, axiom, (![A]: (k4_xboole_0(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_boole)).
% 1.88/1.21  tff(f_32, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 1.88/1.21  tff(f_49, axiom, (![A, B]: (v1_relat_1(B) => ((k7_relat_1(B, A) = k1_xboole_0) <=> r1_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t95_relat_1)).
% 1.88/1.21  tff(f_40, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_relat_1)).
% 1.88/1.21  tff(f_52, negated_conjecture, ~(![A]: (k9_relat_1(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t150_relat_1)).
% 1.88/1.21  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 1.88/1.21  tff(c_38, plain, (![A_10]: (v1_relat_1(A_10) | ~v1_xboole_0(A_10))), inference(cnfTransformation, [status(thm)], [f_36])).
% 1.88/1.21  tff(c_42, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_38])).
% 1.88/1.21  tff(c_14, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.88/1.21  tff(c_4, plain, (![A_1]: (k4_xboole_0(k1_xboole_0, A_1)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_28])).
% 1.88/1.21  tff(c_8, plain, (![A_2, B_3]: (r1_xboole_0(A_2, B_3) | k4_xboole_0(A_2, B_3)!=A_2)), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.88/1.21  tff(c_16, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.88/1.21  tff(c_74, plain, (![B_20, A_21]: (k7_relat_1(B_20, A_21)=k1_xboole_0 | ~r1_xboole_0(k1_relat_1(B_20), A_21) | ~v1_relat_1(B_20))), inference(cnfTransformation, [status(thm)], [f_49])).
% 1.88/1.21  tff(c_84, plain, (![A_21]: (k7_relat_1(k1_xboole_0, A_21)=k1_xboole_0 | ~r1_xboole_0(k1_xboole_0, A_21) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_16, c_74])).
% 1.88/1.21  tff(c_89, plain, (![A_22]: (k7_relat_1(k1_xboole_0, A_22)=k1_xboole_0 | ~r1_xboole_0(k1_xboole_0, A_22))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_84])).
% 1.88/1.21  tff(c_96, plain, (![B_3]: (k7_relat_1(k1_xboole_0, B_3)=k1_xboole_0 | k4_xboole_0(k1_xboole_0, B_3)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_89])).
% 1.88/1.21  tff(c_104, plain, (![B_23]: (k7_relat_1(k1_xboole_0, B_23)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_4, c_96])).
% 1.88/1.21  tff(c_12, plain, (![B_6, A_5]: (k2_relat_1(k7_relat_1(B_6, A_5))=k9_relat_1(B_6, A_5) | ~v1_relat_1(B_6))), inference(cnfTransformation, [status(thm)], [f_40])).
% 1.88/1.21  tff(c_109, plain, (![B_23]: (k9_relat_1(k1_xboole_0, B_23)=k2_relat_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_104, c_12])).
% 1.88/1.21  tff(c_114, plain, (![B_23]: (k9_relat_1(k1_xboole_0, B_23)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_42, c_14, c_109])).
% 1.88/1.21  tff(c_22, plain, (k9_relat_1(k1_xboole_0, '#skF_1')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_52])).
% 1.88/1.21  tff(c_138, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_114, c_22])).
% 1.88/1.21  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.88/1.21  
% 1.88/1.21  Inference rules
% 1.88/1.21  ----------------------
% 1.88/1.21  #Ref     : 0
% 1.88/1.21  #Sup     : 25
% 1.88/1.21  #Fact    : 0
% 1.88/1.21  #Define  : 0
% 1.88/1.21  #Split   : 0
% 1.88/1.21  #Chain   : 0
% 1.88/1.21  #Close   : 0
% 1.88/1.21  
% 1.88/1.21  Ordering : KBO
% 1.88/1.21  
% 1.88/1.21  Simplification rules
% 1.88/1.21  ----------------------
% 1.88/1.21  #Subsume      : 0
% 1.88/1.21  #Demod        : 14
% 1.88/1.21  #Tautology    : 19
% 1.88/1.21  #SimpNegUnit  : 0
% 1.88/1.21  #BackRed      : 2
% 1.88/1.21  
% 1.88/1.21  #Partial instantiations: 0
% 1.88/1.21  #Strategies tried      : 1
% 1.88/1.21  
% 1.88/1.21  Timing (in seconds)
% 1.88/1.21  ----------------------
% 1.88/1.21  Preprocessing        : 0.27
% 1.88/1.21  Parsing              : 0.16
% 1.88/1.21  CNF conversion       : 0.02
% 1.88/1.21  Main loop            : 0.13
% 1.88/1.21  Inferencing          : 0.06
% 1.88/1.21  Reduction            : 0.03
% 1.88/1.21  Demodulation         : 0.02
% 1.88/1.21  BG Simplification    : 0.01
% 1.88/1.21  Subsumption          : 0.02
% 1.88/1.21  Abstraction          : 0.01
% 1.88/1.21  MUC search           : 0.00
% 1.88/1.21  Cooper               : 0.00
% 1.88/1.21  Total                : 0.42
% 1.88/1.21  Index Insertion      : 0.00
% 1.88/1.21  Index Deletion       : 0.00
% 1.88/1.21  Index Matching       : 0.00
% 1.88/1.21  BG Taut test         : 0.00
%------------------------------------------------------------------------------
