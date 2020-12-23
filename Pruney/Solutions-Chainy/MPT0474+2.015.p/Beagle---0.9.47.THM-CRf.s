%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:59:29 EST 2020

% Result     : Theorem 1.51s
% Output     : CNFRefutation 1.51s
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

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
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n022.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 14:34:41 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.51/1.06  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.51/1.07  
% 1.51/1.07  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.51/1.07  %$ v1_xboole_0 > v1_relat_1 > #nlpp > k4_relat_1 > k1_xboole_0
% 1.51/1.07  
% 1.51/1.07  %Foreground sorts:
% 1.51/1.07  
% 1.51/1.07  
% 1.51/1.07  %Background operators:
% 1.51/1.07  
% 1.51/1.07  
% 1.51/1.07  %Foreground operators:
% 1.51/1.07  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.51/1.07  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.51/1.07  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.51/1.07  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.51/1.07  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.51/1.07  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.51/1.07  tff(k4_relat_1, type, k4_relat_1: $i > $i).
% 1.51/1.07  
% 1.51/1.07  tff(f_38, negated_conjecture, ~(k4_relat_1(k1_xboole_0) = k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t66_relat_1)).
% 1.51/1.07  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 1.51/1.07  tff(f_36, axiom, (![A]: (v1_xboole_0(A) => (v1_xboole_0(k4_relat_1(A)) & v1_relat_1(k4_relat_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc14_relat_1)).
% 1.51/1.07  tff(f_30, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 1.51/1.07  tff(c_10, plain, (k4_relat_1(k1_xboole_0)!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_38])).
% 1.51/1.07  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 1.51/1.07  tff(c_18, plain, (![A_5]: (v1_xboole_0(k4_relat_1(A_5)) | ~v1_xboole_0(A_5))), inference(cnfTransformation, [status(thm)], [f_36])).
% 1.51/1.07  tff(c_4, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_30])).
% 1.51/1.07  tff(c_23, plain, (![A_6]: (k4_relat_1(A_6)=k1_xboole_0 | ~v1_xboole_0(A_6))), inference(resolution, [status(thm)], [c_18, c_4])).
% 1.51/1.07  tff(c_29, plain, (k4_relat_1(k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_2, c_23])).
% 1.51/1.07  tff(c_34, plain, $false, inference(negUnitSimplification, [status(thm)], [c_10, c_29])).
% 1.51/1.07  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.51/1.07  
% 1.51/1.07  Inference rules
% 1.51/1.07  ----------------------
% 1.51/1.07  #Ref     : 0
% 1.51/1.07  #Sup     : 4
% 1.51/1.07  #Fact    : 0
% 1.51/1.07  #Define  : 0
% 1.51/1.07  #Split   : 0
% 1.51/1.07  #Chain   : 0
% 1.51/1.07  #Close   : 0
% 1.51/1.07  
% 1.51/1.07  Ordering : KBO
% 1.51/1.07  
% 1.51/1.07  Simplification rules
% 1.51/1.07  ----------------------
% 1.51/1.07  #Subsume      : 0
% 1.51/1.07  #Demod        : 0
% 1.51/1.07  #Tautology    : 1
% 1.51/1.07  #SimpNegUnit  : 1
% 1.51/1.07  #BackRed      : 0
% 1.51/1.07  
% 1.51/1.07  #Partial instantiations: 0
% 1.51/1.07  #Strategies tried      : 1
% 1.51/1.07  
% 1.51/1.07  Timing (in seconds)
% 1.51/1.07  ----------------------
% 1.51/1.08  Preprocessing        : 0.24
% 1.51/1.08  Parsing              : 0.14
% 1.51/1.08  CNF conversion       : 0.01
% 1.51/1.08  Main loop            : 0.07
% 1.51/1.08  Inferencing          : 0.04
% 1.51/1.08  Reduction            : 0.02
% 1.51/1.08  Demodulation         : 0.01
% 1.51/1.08  BG Simplification    : 0.01
% 1.51/1.08  Subsumption          : 0.01
% 1.51/1.08  Abstraction          : 0.00
% 1.51/1.08  MUC search           : 0.00
% 1.51/1.08  Cooper               : 0.00
% 1.51/1.08  Total                : 0.33
% 1.51/1.08  Index Insertion      : 0.00
% 1.51/1.08  Index Deletion       : 0.00
% 1.51/1.08  Index Matching       : 0.00
% 1.51/1.08  BG Taut test         : 0.00
%------------------------------------------------------------------------------
