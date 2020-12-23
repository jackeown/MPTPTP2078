%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:59:29 EST 2020

% Result     : Theorem 1.59s
% Output     : CNFRefutation 1.59s
% Verified   : 
% Statistics : Number of formulae       :   19 (  21 expanded)
%              Number of leaves         :   11 (  12 expanded)
%              Depth                    :    5
%              Number of atoms          :   21 (  23 expanded)
%              Number of equality atoms :    7 (   7 expanded)
%              Maximal formula depth    :    7 (   3 average)
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

tff(f_42,negated_conjecture,(
    k4_relat_1(k1_xboole_0) != k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_relat_1)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_40,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => ( v1_xboole_0(k4_relat_1(A))
        & v1_relat_1(k4_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc14_relat_1)).

tff(f_34,axiom,(
    ! [A,B] :
      ~ ( v1_xboole_0(A)
        & A != B
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_boole)).

tff(c_10,plain,(
    k4_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_8,plain,(
    ! [A_3] :
      ( v1_xboole_0(k4_relat_1(A_3))
      | ~ v1_xboole_0(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_13,plain,(
    ! [B_6,A_7] :
      ( ~ v1_xboole_0(B_6)
      | B_6 = A_7
      | ~ v1_xboole_0(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_20,plain,(
    ! [A_8] :
      ( k1_xboole_0 = A_8
      | ~ v1_xboole_0(A_8) ) ),
    inference(resolution,[status(thm)],[c_2,c_13])).

tff(c_30,plain,(
    ! [A_9] :
      ( k4_relat_1(A_9) = k1_xboole_0
      | ~ v1_xboole_0(A_9) ) ),
    inference(resolution,[status(thm)],[c_8,c_20])).

tff(c_36,plain,(
    k4_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2,c_30])).

tff(c_41,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_10,c_36])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n015.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 12:07:08 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.59/1.15  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.59/1.15  
% 1.59/1.15  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.59/1.15  %$ v1_xboole_0 > v1_relat_1 > #nlpp > k4_relat_1 > k1_xboole_0
% 1.59/1.15  
% 1.59/1.15  %Foreground sorts:
% 1.59/1.15  
% 1.59/1.15  
% 1.59/1.15  %Background operators:
% 1.59/1.15  
% 1.59/1.15  
% 1.59/1.15  %Foreground operators:
% 1.59/1.15  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.59/1.15  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.59/1.15  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.59/1.15  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.59/1.15  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.59/1.15  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.59/1.15  tff(k4_relat_1, type, k4_relat_1: $i > $i).
% 1.59/1.15  
% 1.59/1.16  tff(f_42, negated_conjecture, ~(k4_relat_1(k1_xboole_0) = k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t66_relat_1)).
% 1.59/1.16  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 1.59/1.16  tff(f_40, axiom, (![A]: (v1_xboole_0(A) => (v1_xboole_0(k4_relat_1(A)) & v1_relat_1(k4_relat_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc14_relat_1)).
% 1.59/1.16  tff(f_34, axiom, (![A, B]: ~((v1_xboole_0(A) & ~(A = B)) & v1_xboole_0(B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_boole)).
% 1.59/1.16  tff(c_10, plain, (k4_relat_1(k1_xboole_0)!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.59/1.16  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 1.59/1.16  tff(c_8, plain, (![A_3]: (v1_xboole_0(k4_relat_1(A_3)) | ~v1_xboole_0(A_3))), inference(cnfTransformation, [status(thm)], [f_40])).
% 1.59/1.16  tff(c_13, plain, (![B_6, A_7]: (~v1_xboole_0(B_6) | B_6=A_7 | ~v1_xboole_0(A_7))), inference(cnfTransformation, [status(thm)], [f_34])).
% 1.59/1.16  tff(c_20, plain, (![A_8]: (k1_xboole_0=A_8 | ~v1_xboole_0(A_8))), inference(resolution, [status(thm)], [c_2, c_13])).
% 1.59/1.16  tff(c_30, plain, (![A_9]: (k4_relat_1(A_9)=k1_xboole_0 | ~v1_xboole_0(A_9))), inference(resolution, [status(thm)], [c_8, c_20])).
% 1.59/1.16  tff(c_36, plain, (k4_relat_1(k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_2, c_30])).
% 1.59/1.16  tff(c_41, plain, $false, inference(negUnitSimplification, [status(thm)], [c_10, c_36])).
% 1.59/1.16  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.59/1.16  
% 1.59/1.16  Inference rules
% 1.59/1.16  ----------------------
% 1.59/1.16  #Ref     : 0
% 1.59/1.16  #Sup     : 6
% 1.59/1.16  #Fact    : 0
% 1.59/1.16  #Define  : 0
% 1.59/1.16  #Split   : 0
% 1.59/1.16  #Chain   : 0
% 1.59/1.16  #Close   : 0
% 1.59/1.16  
% 1.59/1.16  Ordering : KBO
% 1.59/1.16  
% 1.59/1.16  Simplification rules
% 1.59/1.16  ----------------------
% 1.59/1.16  #Subsume      : 0
% 1.59/1.16  #Demod        : 0
% 1.59/1.16  #Tautology    : 1
% 1.59/1.16  #SimpNegUnit  : 1
% 1.59/1.16  #BackRed      : 0
% 1.59/1.16  
% 1.59/1.16  #Partial instantiations: 0
% 1.59/1.16  #Strategies tried      : 1
% 1.59/1.16  
% 1.59/1.16  Timing (in seconds)
% 1.59/1.16  ----------------------
% 1.59/1.16  Preprocessing        : 0.26
% 1.59/1.16  Parsing              : 0.14
% 1.59/1.16  CNF conversion       : 0.01
% 1.59/1.16  Main loop            : 0.08
% 1.59/1.16  Inferencing          : 0.04
% 1.59/1.16  Reduction            : 0.02
% 1.59/1.16  Demodulation         : 0.01
% 1.59/1.16  BG Simplification    : 0.01
% 1.59/1.16  Subsumption          : 0.01
% 1.59/1.16  Abstraction          : 0.00
% 1.59/1.16  MUC search           : 0.00
% 1.59/1.16  Cooper               : 0.00
% 1.59/1.16  Total                : 0.37
% 1.59/1.16  Index Insertion      : 0.00
% 1.59/1.16  Index Deletion       : 0.00
% 1.59/1.16  Index Matching       : 0.00
% 1.59/1.16  BG Taut test         : 0.00
%------------------------------------------------------------------------------
