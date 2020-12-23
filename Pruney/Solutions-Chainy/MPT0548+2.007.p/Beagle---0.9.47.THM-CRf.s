%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:00:36 EST 2020

% Result     : Theorem 1.66s
% Output     : CNFRefutation 1.66s
% Verified   : 
% Statistics : Number of formulae       :   32 (  34 expanded)
%              Number of leaves         :   19 (  20 expanded)
%              Depth                    :    5
%              Number of atoms          :   28 (  30 expanded)
%              Number of equality atoms :   14 (  14 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_xboole_0 > v1_relat_1 > k9_relat_1 > k7_relat_1 > #nlpp > k2_relat_1 > k1_relat_1 > o_0_0_xboole_0 > k1_xboole_0 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(o_0_0_xboole_0,type,(
    o_0_0_xboole_0: $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

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
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_o_0_0_xboole_0)).

tff(f_30,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_34,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relat_1)).

tff(f_43,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_36,axiom,(
    ! [A] : k7_relat_1(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t111_relat_1)).

tff(f_40,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_46,negated_conjecture,(
    ~ ! [A] : k9_relat_1(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t150_relat_1)).

tff(c_2,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_30,plain,(
    ! [A_7] :
      ( k1_xboole_0 = A_7
      | ~ v1_xboole_0(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_34,plain,(
    o_0_0_xboole_0 = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2,c_30])).

tff(c_25,plain,(
    ! [A_6] :
      ( v1_relat_1(A_6)
      | ~ v1_xboole_0(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_29,plain,(
    v1_relat_1(o_0_0_xboole_0) ),
    inference(resolution,[status(thm)],[c_2,c_25])).

tff(c_35,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_29])).

tff(c_12,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_8,plain,(
    ! [A_3] : k7_relat_1(k1_xboole_0,A_3) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_58,plain,(
    ! [B_9,A_10] :
      ( k2_relat_1(k7_relat_1(B_9,A_10)) = k9_relat_1(B_9,A_10)
      | ~ v1_relat_1(B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_67,plain,(
    ! [A_3] :
      ( k9_relat_1(k1_xboole_0,A_3) = k2_relat_1(k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_58])).

tff(c_71,plain,(
    ! [A_3] : k9_relat_1(k1_xboole_0,A_3) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_35,c_12,c_67])).

tff(c_16,plain,(
    k9_relat_1(k1_xboole_0,'#skF_1') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_74,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_71,c_16])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:50:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.66/1.10  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.66/1.10  
% 1.66/1.10  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.66/1.11  %$ v1_xboole_0 > v1_relat_1 > k9_relat_1 > k7_relat_1 > #nlpp > k2_relat_1 > k1_relat_1 > o_0_0_xboole_0 > k1_xboole_0 > #skF_1
% 1.66/1.11  
% 1.66/1.11  %Foreground sorts:
% 1.66/1.11  
% 1.66/1.11  
% 1.66/1.11  %Background operators:
% 1.66/1.11  
% 1.66/1.11  
% 1.66/1.11  %Foreground operators:
% 1.66/1.11  tff(o_0_0_xboole_0, type, o_0_0_xboole_0: $i).
% 1.66/1.11  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.66/1.11  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 1.66/1.11  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.66/1.11  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.66/1.11  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 1.66/1.11  tff('#skF_1', type, '#skF_1': $i).
% 1.66/1.11  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.66/1.11  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.66/1.11  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.66/1.11  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.66/1.11  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.66/1.11  
% 1.66/1.12  tff(f_26, axiom, v1_xboole_0(o_0_0_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_o_0_0_xboole_0)).
% 1.66/1.12  tff(f_30, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 1.66/1.12  tff(f_34, axiom, (![A]: (v1_xboole_0(A) => v1_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relat_1)).
% 1.66/1.12  tff(f_43, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 1.66/1.12  tff(f_36, axiom, (![A]: (k7_relat_1(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t111_relat_1)).
% 1.66/1.12  tff(f_40, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_relat_1)).
% 1.66/1.12  tff(f_46, negated_conjecture, ~(![A]: (k9_relat_1(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t150_relat_1)).
% 1.66/1.12  tff(c_2, plain, (v1_xboole_0(o_0_0_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 1.66/1.12  tff(c_30, plain, (![A_7]: (k1_xboole_0=A_7 | ~v1_xboole_0(A_7))), inference(cnfTransformation, [status(thm)], [f_30])).
% 1.66/1.12  tff(c_34, plain, (o_0_0_xboole_0=k1_xboole_0), inference(resolution, [status(thm)], [c_2, c_30])).
% 1.66/1.12  tff(c_25, plain, (![A_6]: (v1_relat_1(A_6) | ~v1_xboole_0(A_6))), inference(cnfTransformation, [status(thm)], [f_34])).
% 1.66/1.12  tff(c_29, plain, (v1_relat_1(o_0_0_xboole_0)), inference(resolution, [status(thm)], [c_2, c_25])).
% 1.66/1.12  tff(c_35, plain, (v1_relat_1(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_34, c_29])).
% 1.66/1.12  tff(c_12, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.66/1.12  tff(c_8, plain, (![A_3]: (k7_relat_1(k1_xboole_0, A_3)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_36])).
% 1.66/1.12  tff(c_58, plain, (![B_9, A_10]: (k2_relat_1(k7_relat_1(B_9, A_10))=k9_relat_1(B_9, A_10) | ~v1_relat_1(B_9))), inference(cnfTransformation, [status(thm)], [f_40])).
% 1.66/1.12  tff(c_67, plain, (![A_3]: (k9_relat_1(k1_xboole_0, A_3)=k2_relat_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_8, c_58])).
% 1.66/1.12  tff(c_71, plain, (![A_3]: (k9_relat_1(k1_xboole_0, A_3)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_35, c_12, c_67])).
% 1.66/1.12  tff(c_16, plain, (k9_relat_1(k1_xboole_0, '#skF_1')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.66/1.12  tff(c_74, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_71, c_16])).
% 1.66/1.12  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.66/1.12  
% 1.66/1.12  Inference rules
% 1.66/1.12  ----------------------
% 1.66/1.12  #Ref     : 0
% 1.66/1.12  #Sup     : 15
% 1.66/1.12  #Fact    : 0
% 1.66/1.12  #Define  : 0
% 1.66/1.12  #Split   : 0
% 1.66/1.12  #Chain   : 0
% 1.66/1.12  #Close   : 0
% 1.66/1.12  
% 1.66/1.12  Ordering : KBO
% 1.66/1.12  
% 1.66/1.12  Simplification rules
% 1.66/1.12  ----------------------
% 1.66/1.12  #Subsume      : 0
% 1.66/1.12  #Demod        : 6
% 1.66/1.12  #Tautology    : 12
% 1.66/1.12  #SimpNegUnit  : 0
% 1.66/1.12  #BackRed      : 3
% 1.66/1.12  
% 1.66/1.12  #Partial instantiations: 0
% 1.66/1.12  #Strategies tried      : 1
% 1.66/1.12  
% 1.66/1.12  Timing (in seconds)
% 1.66/1.12  ----------------------
% 1.66/1.12  Preprocessing        : 0.26
% 1.66/1.12  Parsing              : 0.15
% 1.66/1.12  CNF conversion       : 0.01
% 1.66/1.12  Main loop            : 0.10
% 1.66/1.12  Inferencing          : 0.05
% 1.66/1.12  Reduction            : 0.03
% 1.66/1.12  Demodulation         : 0.02
% 1.66/1.12  BG Simplification    : 0.01
% 1.66/1.12  Subsumption          : 0.01
% 1.66/1.12  Abstraction          : 0.00
% 1.66/1.12  MUC search           : 0.00
% 1.66/1.12  Cooper               : 0.00
% 1.66/1.12  Total                : 0.39
% 1.66/1.12  Index Insertion      : 0.00
% 1.66/1.12  Index Deletion       : 0.00
% 1.66/1.12  Index Matching       : 0.00
% 1.66/1.12  BG Taut test         : 0.00
%------------------------------------------------------------------------------
