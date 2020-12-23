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
% DateTime   : Thu Dec  3 09:59:29 EST 2020

% Result     : Theorem 1.60s
% Output     : CNFRefutation 1.60s
% Verified   : 
% Statistics : Number of formulae       :   18 (  18 expanded)
%              Number of leaves         :   11 (  11 expanded)
%              Depth                    :    4
%              Number of atoms          :   17 (  17 expanded)
%              Number of equality atoms :    6 (   6 expanded)
%              Maximal formula depth    :    4 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_xboole_0 > v1_relat_1 > #nlpp > k4_relat_1 > k1_xboole_0

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k4_relat_1,type,(
    k4_relat_1: $i > $i )).

tff(f_38,negated_conjecture,(
    k4_relat_1(k1_xboole_0) != k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_relat_1)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_36,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => ( v1_xboole_0(k4_relat_1(A))
        & v1_relat_1(k4_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc14_relat_1)).

tff(f_30,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_boole)).

tff(c_10,plain,(
    k4_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_18,plain,(
    ! [A_5] :
      ( v1_xboole_0(k4_relat_1(A_5))
      | ~ v1_xboole_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_4,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_23,plain,(
    ! [A_6] :
      ( k4_relat_1(A_6) = k1_xboole_0
      | ~ v1_xboole_0(A_6) ) ),
    inference(resolution,[status(thm)],[c_18,c_4])).

tff(c_29,plain,(
    k4_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2,c_23])).

tff(c_34,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_10,c_29])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n001.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 18:57:00 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.60/1.16  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.60/1.16  
% 1.60/1.16  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.60/1.16  %$ v1_xboole_0 > v1_relat_1 > #nlpp > k4_relat_1 > k1_xboole_0
% 1.60/1.16  
% 1.60/1.16  %Foreground sorts:
% 1.60/1.16  
% 1.60/1.16  
% 1.60/1.16  %Background operators:
% 1.60/1.16  
% 1.60/1.16  
% 1.60/1.16  %Foreground operators:
% 1.60/1.16  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.60/1.16  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.60/1.16  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.60/1.16  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.60/1.16  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.60/1.16  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.60/1.16  tff(k4_relat_1, type, k4_relat_1: $i > $i).
% 1.60/1.16  
% 1.60/1.17  tff(f_38, negated_conjecture, ~(k4_relat_1(k1_xboole_0) = k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t66_relat_1)).
% 1.60/1.17  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 1.60/1.17  tff(f_36, axiom, (![A]: (v1_xboole_0(A) => (v1_xboole_0(k4_relat_1(A)) & v1_relat_1(k4_relat_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc14_relat_1)).
% 1.60/1.17  tff(f_30, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_boole)).
% 1.60/1.17  tff(c_10, plain, (k4_relat_1(k1_xboole_0)!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_38])).
% 1.60/1.17  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 1.60/1.17  tff(c_18, plain, (![A_5]: (v1_xboole_0(k4_relat_1(A_5)) | ~v1_xboole_0(A_5))), inference(cnfTransformation, [status(thm)], [f_36])).
% 1.60/1.17  tff(c_4, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_30])).
% 1.60/1.17  tff(c_23, plain, (![A_6]: (k4_relat_1(A_6)=k1_xboole_0 | ~v1_xboole_0(A_6))), inference(resolution, [status(thm)], [c_18, c_4])).
% 1.60/1.17  tff(c_29, plain, (k4_relat_1(k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_2, c_23])).
% 1.60/1.17  tff(c_34, plain, $false, inference(negUnitSimplification, [status(thm)], [c_10, c_29])).
% 1.60/1.17  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.60/1.17  
% 1.60/1.17  Inference rules
% 1.60/1.17  ----------------------
% 1.60/1.17  #Ref     : 0
% 1.60/1.17  #Sup     : 4
% 1.60/1.17  #Fact    : 0
% 1.60/1.17  #Define  : 0
% 1.60/1.17  #Split   : 0
% 1.60/1.17  #Chain   : 0
% 1.60/1.17  #Close   : 0
% 1.60/1.17  
% 1.60/1.17  Ordering : KBO
% 1.60/1.17  
% 1.60/1.17  Simplification rules
% 1.60/1.17  ----------------------
% 1.60/1.17  #Subsume      : 0
% 1.60/1.17  #Demod        : 0
% 1.60/1.17  #Tautology    : 1
% 1.60/1.17  #SimpNegUnit  : 1
% 1.60/1.17  #BackRed      : 0
% 1.60/1.17  
% 1.60/1.17  #Partial instantiations: 0
% 1.60/1.17  #Strategies tried      : 1
% 1.60/1.17  
% 1.60/1.17  Timing (in seconds)
% 1.60/1.17  ----------------------
% 1.60/1.17  Preprocessing        : 0.27
% 1.60/1.17  Parsing              : 0.15
% 1.60/1.17  CNF conversion       : 0.02
% 1.60/1.17  Main loop            : 0.08
% 1.60/1.17  Inferencing          : 0.04
% 1.60/1.17  Reduction            : 0.02
% 1.60/1.17  Demodulation         : 0.01
% 1.60/1.17  BG Simplification    : 0.01
% 1.60/1.17  Subsumption          : 0.02
% 1.60/1.17  Abstraction          : 0.00
% 1.60/1.17  MUC search           : 0.00
% 1.60/1.17  Cooper               : 0.00
% 1.60/1.17  Total                : 0.38
% 1.60/1.17  Index Insertion      : 0.00
% 1.60/1.17  Index Deletion       : 0.00
% 1.60/1.17  Index Matching       : 0.00
% 1.60/1.17  BG Taut test         : 0.00
%------------------------------------------------------------------------------
