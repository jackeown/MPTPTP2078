%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:00:21 EST 2020

% Result     : Theorem 1.56s
% Output     : CNFRefutation 1.56s
% Verified   : 
% Statistics : Number of formulae       :   21 (  22 expanded)
%              Number of leaves         :   12 (  13 expanded)
%              Depth                    :    5
%              Number of atoms          :   24 (  26 expanded)
%              Number of equality atoms :    7 (   8 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_xboole_0 > v1_relat_1 > k8_relat_1 > #nlpp > k1_xboole_0 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k8_relat_1,type,(
    k8_relat_1: ( $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

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

tff(f_43,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => k8_relat_1(k1_xboole_0,A) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t137_relat_1)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_38,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(A)
        & v1_xboole_0(B) )
     => ( v1_xboole_0(k8_relat_1(B,A))
        & v1_relat_1(k8_relat_1(B,A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc18_relat_1)).

tff(f_30,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(c_10,plain,(
    k8_relat_1(k1_xboole_0,'#skF_1') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_12,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_19,plain,(
    ! [B_5,A_6] :
      ( v1_xboole_0(k8_relat_1(B_5,A_6))
      | ~ v1_xboole_0(B_5)
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_4,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_25,plain,(
    ! [B_9,A_10] :
      ( k8_relat_1(B_9,A_10) = k1_xboole_0
      | ~ v1_xboole_0(B_9)
      | ~ v1_relat_1(A_10) ) ),
    inference(resolution,[status(thm)],[c_19,c_4])).

tff(c_32,plain,(
    ! [A_11] :
      ( k8_relat_1(k1_xboole_0,A_11) = k1_xboole_0
      | ~ v1_relat_1(A_11) ) ),
    inference(resolution,[status(thm)],[c_2,c_25])).

tff(c_38,plain,(
    k8_relat_1(k1_xboole_0,'#skF_1') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_12,c_32])).

tff(c_43,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_10,c_38])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n007.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 12:49:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.56/1.10  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.56/1.10  
% 1.56/1.10  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.56/1.10  %$ v1_xboole_0 > v1_relat_1 > k8_relat_1 > #nlpp > k1_xboole_0 > #skF_1
% 1.56/1.10  
% 1.56/1.10  %Foreground sorts:
% 1.56/1.10  
% 1.56/1.10  
% 1.56/1.10  %Background operators:
% 1.56/1.10  
% 1.56/1.10  
% 1.56/1.10  %Foreground operators:
% 1.56/1.10  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 1.56/1.10  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.56/1.10  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.56/1.10  tff('#skF_1', type, '#skF_1': $i).
% 1.56/1.10  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.56/1.10  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.56/1.10  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.56/1.10  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.56/1.10  
% 1.56/1.11  tff(f_43, negated_conjecture, ~(![A]: (v1_relat_1(A) => (k8_relat_1(k1_xboole_0, A) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t137_relat_1)).
% 1.56/1.11  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 1.56/1.11  tff(f_38, axiom, (![A, B]: ((v1_relat_1(A) & v1_xboole_0(B)) => (v1_xboole_0(k8_relat_1(B, A)) & v1_relat_1(k8_relat_1(B, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc18_relat_1)).
% 1.56/1.11  tff(f_30, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 1.56/1.11  tff(c_10, plain, (k8_relat_1(k1_xboole_0, '#skF_1')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.56/1.11  tff(c_12, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.56/1.11  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 1.56/1.11  tff(c_19, plain, (![B_5, A_6]: (v1_xboole_0(k8_relat_1(B_5, A_6)) | ~v1_xboole_0(B_5) | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_38])).
% 1.56/1.11  tff(c_4, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_30])).
% 1.56/1.11  tff(c_25, plain, (![B_9, A_10]: (k8_relat_1(B_9, A_10)=k1_xboole_0 | ~v1_xboole_0(B_9) | ~v1_relat_1(A_10))), inference(resolution, [status(thm)], [c_19, c_4])).
% 1.56/1.11  tff(c_32, plain, (![A_11]: (k8_relat_1(k1_xboole_0, A_11)=k1_xboole_0 | ~v1_relat_1(A_11))), inference(resolution, [status(thm)], [c_2, c_25])).
% 1.56/1.11  tff(c_38, plain, (k8_relat_1(k1_xboole_0, '#skF_1')=k1_xboole_0), inference(resolution, [status(thm)], [c_12, c_32])).
% 1.56/1.11  tff(c_43, plain, $false, inference(negUnitSimplification, [status(thm)], [c_10, c_38])).
% 1.56/1.11  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.56/1.11  
% 1.56/1.11  Inference rules
% 1.56/1.11  ----------------------
% 1.56/1.11  #Ref     : 0
% 1.56/1.11  #Sup     : 6
% 1.56/1.11  #Fact    : 0
% 1.56/1.11  #Define  : 0
% 1.56/1.11  #Split   : 0
% 1.56/1.11  #Chain   : 0
% 1.56/1.11  #Close   : 0
% 1.56/1.11  
% 1.56/1.11  Ordering : KBO
% 1.56/1.11  
% 1.56/1.11  Simplification rules
% 1.56/1.11  ----------------------
% 1.56/1.11  #Subsume      : 0
% 1.56/1.11  #Demod        : 0
% 1.56/1.11  #Tautology    : 1
% 1.56/1.11  #SimpNegUnit  : 1
% 1.56/1.11  #BackRed      : 0
% 1.56/1.11  
% 1.56/1.11  #Partial instantiations: 0
% 1.56/1.11  #Strategies tried      : 1
% 1.56/1.11  
% 1.56/1.11  Timing (in seconds)
% 1.56/1.11  ----------------------
% 1.56/1.11  Preprocessing        : 0.23
% 1.56/1.11  Parsing              : 0.12
% 1.56/1.11  CNF conversion       : 0.01
% 1.56/1.11  Main loop            : 0.08
% 1.56/1.11  Inferencing          : 0.04
% 1.56/1.11  Reduction            : 0.02
% 1.56/1.11  Demodulation         : 0.01
% 1.56/1.11  BG Simplification    : 0.01
% 1.56/1.11  Subsumption          : 0.02
% 1.56/1.11  Abstraction          : 0.00
% 1.56/1.11  MUC search           : 0.00
% 1.56/1.11  Cooper               : 0.00
% 1.56/1.11  Total                : 0.33
% 1.56/1.11  Index Insertion      : 0.00
% 1.56/1.11  Index Deletion       : 0.00
% 1.56/1.11  Index Matching       : 0.00
% 1.56/1.11  BG Taut test         : 0.00
%------------------------------------------------------------------------------
