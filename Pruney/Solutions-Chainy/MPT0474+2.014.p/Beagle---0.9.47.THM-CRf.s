%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:59:29 EST 2020

% Result     : Theorem 1.45s
% Output     : CNFRefutation 1.57s
% Verified   : 
% Statistics : Number of formulae       :   22 (  25 expanded)
%              Number of leaves         :   12 (  14 expanded)
%              Depth                    :    5
%              Number of atoms          :   21 (  25 expanded)
%              Number of equality atoms :    8 (   9 expanded)
%              Maximal formula depth    :    4 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_xboole_0 > v1_relat_1 > #nlpp > k4_relat_1 > o_0_0_xboole_0 > k1_xboole_0

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(o_0_0_xboole_0,type,(
    o_0_0_xboole_0: $i )).

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
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_o_0_0_xboole_0)).

tff(f_30,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_36,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => ( v1_xboole_0(k4_relat_1(A))
        & v1_relat_1(k4_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc14_relat_1)).

tff(c_10,plain,(
    k4_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_2,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_11,plain,(
    ! [A_3] :
      ( k1_xboole_0 = A_3
      | ~ v1_xboole_0(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_15,plain,(
    o_0_0_xboole_0 = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2,c_11])).

tff(c_16,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_15,c_2])).

tff(c_27,plain,(
    ! [A_5] :
      ( v1_xboole_0(k4_relat_1(A_5))
      | ~ v1_xboole_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_4,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_32,plain,(
    ! [A_6] :
      ( k4_relat_1(A_6) = k1_xboole_0
      | ~ v1_xboole_0(A_6) ) ),
    inference(resolution,[status(thm)],[c_27,c_4])).

tff(c_38,plain,(
    k4_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_16,c_32])).

tff(c_43,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_10,c_38])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:41:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.45/1.03  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.45/1.03  
% 1.45/1.03  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.45/1.04  %$ v1_xboole_0 > v1_relat_1 > #nlpp > k4_relat_1 > o_0_0_xboole_0 > k1_xboole_0
% 1.45/1.04  
% 1.45/1.04  %Foreground sorts:
% 1.45/1.04  
% 1.45/1.04  
% 1.45/1.04  %Background operators:
% 1.45/1.04  
% 1.45/1.04  
% 1.45/1.04  %Foreground operators:
% 1.45/1.04  tff(o_0_0_xboole_0, type, o_0_0_xboole_0: $i).
% 1.45/1.04  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.45/1.04  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.45/1.04  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.45/1.04  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.45/1.04  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.45/1.04  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.45/1.04  tff(k4_relat_1, type, k4_relat_1: $i > $i).
% 1.45/1.04  
% 1.57/1.04  tff(f_38, negated_conjecture, ~(k4_relat_1(k1_xboole_0) = k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t66_relat_1)).
% 1.57/1.04  tff(f_26, axiom, v1_xboole_0(o_0_0_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_o_0_0_xboole_0)).
% 1.57/1.04  tff(f_30, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 1.57/1.04  tff(f_36, axiom, (![A]: (v1_xboole_0(A) => (v1_xboole_0(k4_relat_1(A)) & v1_relat_1(k4_relat_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc14_relat_1)).
% 1.57/1.04  tff(c_10, plain, (k4_relat_1(k1_xboole_0)!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_38])).
% 1.57/1.04  tff(c_2, plain, (v1_xboole_0(o_0_0_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 1.57/1.04  tff(c_11, plain, (![A_3]: (k1_xboole_0=A_3 | ~v1_xboole_0(A_3))), inference(cnfTransformation, [status(thm)], [f_30])).
% 1.57/1.04  tff(c_15, plain, (o_0_0_xboole_0=k1_xboole_0), inference(resolution, [status(thm)], [c_2, c_11])).
% 1.57/1.04  tff(c_16, plain, (v1_xboole_0(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_15, c_2])).
% 1.57/1.04  tff(c_27, plain, (![A_5]: (v1_xboole_0(k4_relat_1(A_5)) | ~v1_xboole_0(A_5))), inference(cnfTransformation, [status(thm)], [f_36])).
% 1.57/1.04  tff(c_4, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_30])).
% 1.57/1.04  tff(c_32, plain, (![A_6]: (k4_relat_1(A_6)=k1_xboole_0 | ~v1_xboole_0(A_6))), inference(resolution, [status(thm)], [c_27, c_4])).
% 1.57/1.04  tff(c_38, plain, (k4_relat_1(k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_16, c_32])).
% 1.57/1.04  tff(c_43, plain, $false, inference(negUnitSimplification, [status(thm)], [c_10, c_38])).
% 1.57/1.04  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.57/1.04  
% 1.57/1.04  Inference rules
% 1.57/1.04  ----------------------
% 1.57/1.04  #Ref     : 0
% 1.57/1.04  #Sup     : 7
% 1.57/1.04  #Fact    : 0
% 1.57/1.04  #Define  : 0
% 1.57/1.04  #Split   : 0
% 1.57/1.04  #Chain   : 0
% 1.57/1.04  #Close   : 0
% 1.57/1.04  
% 1.57/1.04  Ordering : KBO
% 1.57/1.04  
% 1.57/1.04  Simplification rules
% 1.57/1.04  ----------------------
% 1.57/1.04  #Subsume      : 0
% 1.57/1.04  #Demod        : 1
% 1.57/1.04  #Tautology    : 3
% 1.57/1.04  #SimpNegUnit  : 1
% 1.57/1.04  #BackRed      : 1
% 1.57/1.04  
% 1.57/1.04  #Partial instantiations: 0
% 1.57/1.04  #Strategies tried      : 1
% 1.57/1.04  
% 1.57/1.04  Timing (in seconds)
% 1.57/1.04  ----------------------
% 1.57/1.05  Preprocessing        : 0.23
% 1.57/1.05  Parsing              : 0.13
% 1.57/1.05  CNF conversion       : 0.01
% 1.57/1.05  Main loop            : 0.07
% 1.57/1.05  Inferencing          : 0.03
% 1.57/1.05  Reduction            : 0.02
% 1.57/1.05  Demodulation         : 0.01
% 1.57/1.05  BG Simplification    : 0.01
% 1.57/1.05  Subsumption          : 0.01
% 1.57/1.05  Abstraction          : 0.00
% 1.57/1.05  MUC search           : 0.00
% 1.57/1.05  Cooper               : 0.00
% 1.57/1.05  Total                : 0.33
% 1.57/1.05  Index Insertion      : 0.00
% 1.57/1.05  Index Deletion       : 0.00
% 1.57/1.05  Index Matching       : 0.00
% 1.57/1.05  BG Taut test         : 0.00
%------------------------------------------------------------------------------
