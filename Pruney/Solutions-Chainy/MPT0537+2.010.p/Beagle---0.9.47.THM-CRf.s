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
% DateTime   : Thu Dec  3 10:00:21 EST 2020

% Result     : Theorem 1.60s
% Output     : CNFRefutation 1.60s
% Verified   : 
% Statistics : Number of formulae       :   26 (  27 expanded)
%              Number of leaves         :   15 (  16 expanded)
%              Depth                    :    5
%              Number of atoms          :   32 (  34 expanded)
%              Number of equality atoms :   14 (  15 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k8_relat_1 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k8_relat_1,type,(
    k8_relat_1: ( $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_50,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => k8_relat_1(k1_xboole_0,A) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t137_relat_1)).

tff(f_27,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(A,k2_relat_1(B))
       => k2_relat_1(k8_relat_1(A,B)) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t120_relat_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => v1_relat_1(k8_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k8_relat_1)).

tff(f_45,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ( k1_relat_1(A) = k1_xboole_0
          | k2_relat_1(A) = k1_xboole_0 )
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).

tff(c_12,plain,(
    k8_relat_1(k1_xboole_0,'#skF_1') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_14,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_2,plain,(
    ! [A_1] : r1_tarski(k1_xboole_0,A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_37,plain,(
    ! [A_12,B_13] :
      ( k2_relat_1(k8_relat_1(A_12,B_13)) = A_12
      | ~ r1_tarski(A_12,k2_relat_1(B_13))
      | ~ v1_relat_1(B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_42,plain,(
    ! [B_13] :
      ( k2_relat_1(k8_relat_1(k1_xboole_0,B_13)) = k1_xboole_0
      | ~ v1_relat_1(B_13) ) ),
    inference(resolution,[status(thm)],[c_2,c_37])).

tff(c_4,plain,(
    ! [A_2,B_3] :
      ( v1_relat_1(k8_relat_1(A_2,B_3))
      | ~ v1_relat_1(B_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_17,plain,(
    ! [A_10] :
      ( k2_relat_1(A_10) != k1_xboole_0
      | k1_xboole_0 = A_10
      | ~ v1_relat_1(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_55,plain,(
    ! [A_15,B_16] :
      ( k2_relat_1(k8_relat_1(A_15,B_16)) != k1_xboole_0
      | k8_relat_1(A_15,B_16) = k1_xboole_0
      | ~ v1_relat_1(B_16) ) ),
    inference(resolution,[status(thm)],[c_4,c_17])).

tff(c_60,plain,(
    ! [B_17] :
      ( k8_relat_1(k1_xboole_0,B_17) = k1_xboole_0
      | ~ v1_relat_1(B_17) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_55])).

tff(c_66,plain,(
    k8_relat_1(k1_xboole_0,'#skF_1') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_14,c_60])).

tff(c_71,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_12,c_66])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:44:41 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.60/1.16  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.60/1.17  
% 1.60/1.17  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.60/1.17  %$ r1_tarski > v1_relat_1 > k8_relat_1 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_1
% 1.60/1.17  
% 1.60/1.17  %Foreground sorts:
% 1.60/1.17  
% 1.60/1.17  
% 1.60/1.17  %Background operators:
% 1.60/1.17  
% 1.60/1.17  
% 1.60/1.17  %Foreground operators:
% 1.60/1.17  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 1.60/1.17  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.60/1.17  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.60/1.17  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.60/1.17  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.60/1.17  tff('#skF_1', type, '#skF_1': $i).
% 1.60/1.17  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.60/1.17  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.60/1.17  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.60/1.17  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.60/1.17  
% 1.60/1.18  tff(f_50, negated_conjecture, ~(![A]: (v1_relat_1(A) => (k8_relat_1(k1_xboole_0, A) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t137_relat_1)).
% 1.60/1.18  tff(f_27, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 1.60/1.18  tff(f_37, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(A, k2_relat_1(B)) => (k2_relat_1(k8_relat_1(A, B)) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t120_relat_1)).
% 1.60/1.18  tff(f_31, axiom, (![A, B]: (v1_relat_1(B) => v1_relat_1(k8_relat_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k8_relat_1)).
% 1.60/1.18  tff(f_45, axiom, (![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_relat_1)).
% 1.60/1.18  tff(c_12, plain, (k8_relat_1(k1_xboole_0, '#skF_1')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_50])).
% 1.60/1.18  tff(c_14, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_50])).
% 1.60/1.18  tff(c_2, plain, (![A_1]: (r1_tarski(k1_xboole_0, A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.60/1.18  tff(c_37, plain, (![A_12, B_13]: (k2_relat_1(k8_relat_1(A_12, B_13))=A_12 | ~r1_tarski(A_12, k2_relat_1(B_13)) | ~v1_relat_1(B_13))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.60/1.18  tff(c_42, plain, (![B_13]: (k2_relat_1(k8_relat_1(k1_xboole_0, B_13))=k1_xboole_0 | ~v1_relat_1(B_13))), inference(resolution, [status(thm)], [c_2, c_37])).
% 1.60/1.18  tff(c_4, plain, (![A_2, B_3]: (v1_relat_1(k8_relat_1(A_2, B_3)) | ~v1_relat_1(B_3))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.60/1.18  tff(c_17, plain, (![A_10]: (k2_relat_1(A_10)!=k1_xboole_0 | k1_xboole_0=A_10 | ~v1_relat_1(A_10))), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.60/1.18  tff(c_55, plain, (![A_15, B_16]: (k2_relat_1(k8_relat_1(A_15, B_16))!=k1_xboole_0 | k8_relat_1(A_15, B_16)=k1_xboole_0 | ~v1_relat_1(B_16))), inference(resolution, [status(thm)], [c_4, c_17])).
% 1.60/1.18  tff(c_60, plain, (![B_17]: (k8_relat_1(k1_xboole_0, B_17)=k1_xboole_0 | ~v1_relat_1(B_17))), inference(superposition, [status(thm), theory('equality')], [c_42, c_55])).
% 1.60/1.18  tff(c_66, plain, (k8_relat_1(k1_xboole_0, '#skF_1')=k1_xboole_0), inference(resolution, [status(thm)], [c_14, c_60])).
% 1.60/1.18  tff(c_71, plain, $false, inference(negUnitSimplification, [status(thm)], [c_12, c_66])).
% 1.60/1.18  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.60/1.18  
% 1.60/1.18  Inference rules
% 1.60/1.18  ----------------------
% 1.60/1.18  #Ref     : 0
% 1.60/1.18  #Sup     : 11
% 1.60/1.18  #Fact    : 0
% 1.60/1.18  #Define  : 0
% 1.60/1.18  #Split   : 2
% 1.60/1.18  #Chain   : 0
% 1.60/1.18  #Close   : 0
% 1.60/1.18  
% 1.60/1.18  Ordering : KBO
% 1.60/1.18  
% 1.60/1.18  Simplification rules
% 1.60/1.18  ----------------------
% 1.60/1.18  #Subsume      : 0
% 1.60/1.18  #Demod        : 0
% 1.60/1.18  #Tautology    : 2
% 1.60/1.18  #SimpNegUnit  : 1
% 1.60/1.18  #BackRed      : 0
% 1.60/1.18  
% 1.60/1.18  #Partial instantiations: 0
% 1.60/1.18  #Strategies tried      : 1
% 1.60/1.18  
% 1.60/1.18  Timing (in seconds)
% 1.60/1.18  ----------------------
% 1.60/1.18  Preprocessing        : 0.27
% 1.60/1.18  Parsing              : 0.15
% 1.60/1.18  CNF conversion       : 0.02
% 1.60/1.18  Main loop            : 0.11
% 1.60/1.18  Inferencing          : 0.05
% 1.60/1.18  Reduction            : 0.02
% 1.60/1.18  Demodulation         : 0.01
% 1.60/1.18  BG Simplification    : 0.01
% 1.60/1.18  Subsumption          : 0.02
% 1.60/1.18  Abstraction          : 0.00
% 1.60/1.18  MUC search           : 0.00
% 1.60/1.18  Cooper               : 0.00
% 1.60/1.18  Total                : 0.40
% 1.60/1.18  Index Insertion      : 0.00
% 1.60/1.18  Index Deletion       : 0.00
% 1.60/1.18  Index Matching       : 0.00
% 1.60/1.18  BG Taut test         : 0.00
%------------------------------------------------------------------------------
