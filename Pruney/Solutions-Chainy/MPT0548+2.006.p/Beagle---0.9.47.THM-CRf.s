%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:00:36 EST 2020

% Result     : Theorem 1.68s
% Output     : CNFRefutation 1.68s
% Verified   : 
% Statistics : Number of formulae       :   31 (  31 expanded)
%              Number of leaves         :   19 (  19 expanded)
%              Depth                    :    5
%              Number of atoms          :   25 (  25 expanded)
%              Number of equality atoms :   13 (  13 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_xboole_0 > v1_relat_1 > k9_relat_1 > k7_relat_1 > #nlpp > k2_relat_1 > k1_subset_1 > k1_relat_1 > k1_xboole_0 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
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

tff(k1_subset_1,type,(
    k1_subset_1: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_27,axiom,(
    ! [A] : k1_subset_1(A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_subset_1)).

tff(f_29,axiom,(
    ! [A] : v1_xboole_0(k1_subset_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc13_subset_1)).

tff(f_33,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relat_1)).

tff(f_42,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_35,axiom,(
    ! [A] : k7_relat_1(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t111_relat_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_45,negated_conjecture,(
    ~ ! [A] : k9_relat_1(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t150_relat_1)).

tff(c_2,plain,(
    ! [A_1] : k1_subset_1(A_1) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_4,plain,(
    ! [A_2] : v1_xboole_0(k1_subset_1(A_2)) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_17,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_4])).

tff(c_40,plain,(
    ! [A_9] :
      ( v1_relat_1(A_9)
      | ~ v1_xboole_0(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_44,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_17,c_40])).

tff(c_12,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_8,plain,(
    ! [A_4] : k7_relat_1(k1_xboole_0,A_4) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_45,plain,(
    ! [B_10,A_11] :
      ( k2_relat_1(k7_relat_1(B_10,A_11)) = k9_relat_1(B_10,A_11)
      | ~ v1_relat_1(B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_54,plain,(
    ! [A_4] :
      ( k9_relat_1(k1_xboole_0,A_4) = k2_relat_1(k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_45])).

tff(c_58,plain,(
    ! [A_4] : k9_relat_1(k1_xboole_0,A_4) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_12,c_54])).

tff(c_16,plain,(
    k9_relat_1(k1_xboole_0,'#skF_1') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_61,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_16])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n001.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 14:16:44 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.68/1.10  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.68/1.10  
% 1.68/1.10  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.68/1.10  %$ v1_xboole_0 > v1_relat_1 > k9_relat_1 > k7_relat_1 > #nlpp > k2_relat_1 > k1_subset_1 > k1_relat_1 > k1_xboole_0 > #skF_1
% 1.68/1.10  
% 1.68/1.10  %Foreground sorts:
% 1.68/1.10  
% 1.68/1.10  
% 1.68/1.10  %Background operators:
% 1.68/1.10  
% 1.68/1.10  
% 1.68/1.10  %Foreground operators:
% 1.68/1.10  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.68/1.10  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 1.68/1.10  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.68/1.10  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.68/1.10  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 1.68/1.10  tff('#skF_1', type, '#skF_1': $i).
% 1.68/1.10  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.68/1.10  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.68/1.10  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.68/1.10  tff(k1_subset_1, type, k1_subset_1: $i > $i).
% 1.68/1.10  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.68/1.10  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.68/1.10  
% 1.68/1.11  tff(f_27, axiom, (![A]: (k1_subset_1(A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_subset_1)).
% 1.68/1.11  tff(f_29, axiom, (![A]: v1_xboole_0(k1_subset_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc13_subset_1)).
% 1.68/1.11  tff(f_33, axiom, (![A]: (v1_xboole_0(A) => v1_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relat_1)).
% 1.68/1.11  tff(f_42, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 1.68/1.11  tff(f_35, axiom, (![A]: (k7_relat_1(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t111_relat_1)).
% 1.68/1.11  tff(f_39, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_relat_1)).
% 1.68/1.11  tff(f_45, negated_conjecture, ~(![A]: (k9_relat_1(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t150_relat_1)).
% 1.68/1.11  tff(c_2, plain, (![A_1]: (k1_subset_1(A_1)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.68/1.11  tff(c_4, plain, (![A_2]: (v1_xboole_0(k1_subset_1(A_2)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.68/1.11  tff(c_17, plain, (v1_xboole_0(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_2, c_4])).
% 1.68/1.11  tff(c_40, plain, (![A_9]: (v1_relat_1(A_9) | ~v1_xboole_0(A_9))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.68/1.11  tff(c_44, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_17, c_40])).
% 1.68/1.11  tff(c_12, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.68/1.11  tff(c_8, plain, (![A_4]: (k7_relat_1(k1_xboole_0, A_4)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.68/1.11  tff(c_45, plain, (![B_10, A_11]: (k2_relat_1(k7_relat_1(B_10, A_11))=k9_relat_1(B_10, A_11) | ~v1_relat_1(B_10))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.68/1.11  tff(c_54, plain, (![A_4]: (k9_relat_1(k1_xboole_0, A_4)=k2_relat_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_8, c_45])).
% 1.68/1.11  tff(c_58, plain, (![A_4]: (k9_relat_1(k1_xboole_0, A_4)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_44, c_12, c_54])).
% 1.68/1.11  tff(c_16, plain, (k9_relat_1(k1_xboole_0, '#skF_1')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.68/1.11  tff(c_61, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_58, c_16])).
% 1.68/1.11  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.68/1.11  
% 1.68/1.11  Inference rules
% 1.68/1.11  ----------------------
% 1.68/1.11  #Ref     : 0
% 1.68/1.11  #Sup     : 12
% 1.68/1.11  #Fact    : 0
% 1.68/1.11  #Define  : 0
% 1.68/1.11  #Split   : 0
% 1.68/1.11  #Chain   : 0
% 1.68/1.11  #Close   : 0
% 1.68/1.11  
% 1.68/1.11  Ordering : KBO
% 1.68/1.11  
% 1.68/1.11  Simplification rules
% 1.68/1.11  ----------------------
% 1.68/1.11  #Subsume      : 0
% 1.68/1.11  #Demod        : 4
% 1.68/1.11  #Tautology    : 10
% 1.68/1.11  #SimpNegUnit  : 0
% 1.68/1.11  #BackRed      : 1
% 1.68/1.11  
% 1.68/1.11  #Partial instantiations: 0
% 1.68/1.11  #Strategies tried      : 1
% 1.68/1.11  
% 1.68/1.11  Timing (in seconds)
% 1.68/1.11  ----------------------
% 1.68/1.11  Preprocessing        : 0.26
% 1.68/1.11  Parsing              : 0.14
% 1.68/1.11  CNF conversion       : 0.02
% 1.68/1.11  Main loop            : 0.09
% 1.68/1.11  Inferencing          : 0.05
% 1.68/1.11  Reduction            : 0.03
% 1.68/1.11  Demodulation         : 0.02
% 1.68/1.12  BG Simplification    : 0.01
% 1.68/1.12  Subsumption          : 0.01
% 1.68/1.12  Abstraction          : 0.00
% 1.68/1.12  MUC search           : 0.00
% 1.68/1.12  Cooper               : 0.00
% 1.68/1.12  Total                : 0.38
% 1.68/1.12  Index Insertion      : 0.00
% 1.68/1.12  Index Deletion       : 0.00
% 1.68/1.12  Index Matching       : 0.00
% 1.68/1.12  BG Taut test         : 0.00
%------------------------------------------------------------------------------
