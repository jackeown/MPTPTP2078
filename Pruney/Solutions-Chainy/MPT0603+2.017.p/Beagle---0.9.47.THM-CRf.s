%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:02:26 EST 2020

% Result     : Theorem 1.80s
% Output     : CNFRefutation 1.80s
% Verified   : 
% Statistics : Number of formulae       :   34 (  39 expanded)
%              Number of leaves         :   20 (  24 expanded)
%              Depth                    :    5
%              Number of atoms          :   34 (  46 expanded)
%              Number of equality atoms :   17 (  21 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > v1_relat_1 > k1_enumset1 > k7_relat_1 > k3_xboole_0 > k2_tarski > #nlpp > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

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

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_52,negated_conjecture,(
    ~ ! [A,B,C] :
        ( v1_relat_1(C)
       => ( r1_xboole_0(A,B)
         => k7_relat_1(k7_relat_1(C,A),B) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t207_relat_1)).

tff(f_31,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_45,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( k7_relat_1(B,A) = k1_xboole_0
      <=> r1_xboole_0(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_relat_1)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k7_relat_1(k7_relat_1(C,A),B) = k7_relat_1(C,k3_xboole_0(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_relat_1)).

tff(c_22,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_6,plain,(
    ! [A_3] : k3_xboole_0(A_3,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( r1_xboole_0(A_1,B_2)
      | k3_xboole_0(A_1,B_2) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_67,plain,(
    ! [B_24,A_25] :
      ( k7_relat_1(B_24,A_25) = k1_xboole_0
      | ~ r1_xboole_0(k1_relat_1(B_24),A_25)
      | ~ v1_relat_1(B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_96,plain,(
    ! [B_28,B_29] :
      ( k7_relat_1(B_28,B_29) = k1_xboole_0
      | ~ v1_relat_1(B_28)
      | k3_xboole_0(k1_relat_1(B_28),B_29) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_4,c_67])).

tff(c_106,plain,(
    ! [B_30] :
      ( k7_relat_1(B_30,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(B_30) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_96])).

tff(c_110,plain,(
    k7_relat_1('#skF_3',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_22,c_106])).

tff(c_20,plain,(
    r1_xboole_0('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_30,plain,(
    ! [A_14,B_15] :
      ( k3_xboole_0(A_14,B_15) = k1_xboole_0
      | ~ r1_xboole_0(A_14,B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_34,plain,(
    k3_xboole_0('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_20,c_30])).

tff(c_115,plain,(
    ! [C_31,A_32,B_33] :
      ( k7_relat_1(k7_relat_1(C_31,A_32),B_33) = k7_relat_1(C_31,k3_xboole_0(A_32,B_33))
      | ~ v1_relat_1(C_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_18,plain,(
    k7_relat_1(k7_relat_1('#skF_3','#skF_1'),'#skF_2') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_124,plain,
    ( k7_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2')) != k1_xboole_0
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_115,c_18])).

tff(c_137,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_110,c_34,c_124])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:51:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.80/1.20  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.80/1.21  
% 1.80/1.21  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.80/1.21  %$ r1_xboole_0 > v1_relat_1 > k1_enumset1 > k7_relat_1 > k3_xboole_0 > k2_tarski > #nlpp > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 1.80/1.21  
% 1.80/1.21  %Foreground sorts:
% 1.80/1.21  
% 1.80/1.21  
% 1.80/1.21  %Background operators:
% 1.80/1.21  
% 1.80/1.21  
% 1.80/1.21  %Foreground operators:
% 1.80/1.21  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.80/1.21  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 1.80/1.21  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.80/1.21  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.80/1.21  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.80/1.21  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.80/1.21  tff('#skF_2', type, '#skF_2': $i).
% 1.80/1.21  tff('#skF_3', type, '#skF_3': $i).
% 1.80/1.21  tff('#skF_1', type, '#skF_1': $i).
% 1.80/1.21  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.80/1.21  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.80/1.21  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.80/1.21  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.80/1.21  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.80/1.21  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 1.80/1.21  
% 1.80/1.22  tff(f_52, negated_conjecture, ~(![A, B, C]: (v1_relat_1(C) => (r1_xboole_0(A, B) => (k7_relat_1(k7_relat_1(C, A), B) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t207_relat_1)).
% 1.80/1.22  tff(f_31, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 1.80/1.22  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 1.80/1.22  tff(f_45, axiom, (![A, B]: (v1_relat_1(B) => ((k7_relat_1(B, A) = k1_xboole_0) <=> r1_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t95_relat_1)).
% 1.80/1.22  tff(f_39, axiom, (![A, B, C]: (v1_relat_1(C) => (k7_relat_1(k7_relat_1(C, A), B) = k7_relat_1(C, k3_xboole_0(A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_relat_1)).
% 1.80/1.22  tff(c_22, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_52])).
% 1.80/1.22  tff(c_6, plain, (![A_3]: (k3_xboole_0(A_3, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.80/1.22  tff(c_4, plain, (![A_1, B_2]: (r1_xboole_0(A_1, B_2) | k3_xboole_0(A_1, B_2)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.80/1.22  tff(c_67, plain, (![B_24, A_25]: (k7_relat_1(B_24, A_25)=k1_xboole_0 | ~r1_xboole_0(k1_relat_1(B_24), A_25) | ~v1_relat_1(B_24))), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.80/1.22  tff(c_96, plain, (![B_28, B_29]: (k7_relat_1(B_28, B_29)=k1_xboole_0 | ~v1_relat_1(B_28) | k3_xboole_0(k1_relat_1(B_28), B_29)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_4, c_67])).
% 1.80/1.22  tff(c_106, plain, (![B_30]: (k7_relat_1(B_30, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(B_30))), inference(superposition, [status(thm), theory('equality')], [c_6, c_96])).
% 1.80/1.22  tff(c_110, plain, (k7_relat_1('#skF_3', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_22, c_106])).
% 1.80/1.22  tff(c_20, plain, (r1_xboole_0('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_52])).
% 1.80/1.22  tff(c_30, plain, (![A_14, B_15]: (k3_xboole_0(A_14, B_15)=k1_xboole_0 | ~r1_xboole_0(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.80/1.22  tff(c_34, plain, (k3_xboole_0('#skF_1', '#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_20, c_30])).
% 1.80/1.22  tff(c_115, plain, (![C_31, A_32, B_33]: (k7_relat_1(k7_relat_1(C_31, A_32), B_33)=k7_relat_1(C_31, k3_xboole_0(A_32, B_33)) | ~v1_relat_1(C_31))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.80/1.22  tff(c_18, plain, (k7_relat_1(k7_relat_1('#skF_3', '#skF_1'), '#skF_2')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_52])).
% 1.80/1.22  tff(c_124, plain, (k7_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2'))!=k1_xboole_0 | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_115, c_18])).
% 1.80/1.22  tff(c_137, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_22, c_110, c_34, c_124])).
% 1.80/1.22  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.80/1.22  
% 1.80/1.22  Inference rules
% 1.80/1.22  ----------------------
% 1.80/1.22  #Ref     : 0
% 1.80/1.22  #Sup     : 28
% 1.80/1.22  #Fact    : 0
% 1.80/1.22  #Define  : 0
% 1.80/1.22  #Split   : 0
% 1.80/1.22  #Chain   : 0
% 1.80/1.22  #Close   : 0
% 1.80/1.22  
% 1.80/1.22  Ordering : KBO
% 1.80/1.22  
% 1.80/1.22  Simplification rules
% 1.80/1.22  ----------------------
% 1.80/1.22  #Subsume      : 0
% 1.80/1.22  #Demod        : 3
% 1.80/1.22  #Tautology    : 18
% 1.80/1.22  #SimpNegUnit  : 0
% 1.80/1.22  #BackRed      : 0
% 1.80/1.22  
% 1.80/1.22  #Partial instantiations: 0
% 1.80/1.22  #Strategies tried      : 1
% 1.80/1.22  
% 1.80/1.22  Timing (in seconds)
% 1.80/1.22  ----------------------
% 1.80/1.22  Preprocessing        : 0.30
% 1.80/1.22  Parsing              : 0.16
% 1.80/1.22  CNF conversion       : 0.02
% 1.80/1.22  Main loop            : 0.12
% 1.80/1.22  Inferencing          : 0.05
% 1.80/1.22  Reduction            : 0.03
% 1.80/1.22  Demodulation         : 0.02
% 1.80/1.22  BG Simplification    : 0.01
% 1.80/1.22  Subsumption          : 0.02
% 1.80/1.22  Abstraction          : 0.01
% 1.80/1.22  MUC search           : 0.00
% 1.80/1.22  Cooper               : 0.00
% 1.80/1.22  Total                : 0.45
% 1.80/1.22  Index Insertion      : 0.00
% 1.80/1.22  Index Deletion       : 0.00
% 1.80/1.22  Index Matching       : 0.00
% 1.80/1.22  BG Taut test         : 0.00
%------------------------------------------------------------------------------
