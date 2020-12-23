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
% DateTime   : Thu Dec  3 10:00:00 EST 2020

% Result     : Theorem 1.58s
% Output     : CNFRefutation 1.58s
% Verified   : 
% Statistics : Number of formulae       :   23 (  25 expanded)
%              Number of leaves         :   13 (  14 expanded)
%              Depth                    :    5
%              Number of atoms          :   27 (  29 expanded)
%              Number of equality atoms :    7 (   7 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_xboole_0 > v1_relat_1 > k7_relat_1 > #nlpp > k1_xboole_0 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

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

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_34,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relat_1)).

tff(f_42,axiom,(
    ! [A,B] :
      ( ( v1_xboole_0(A)
        & v1_relat_1(A) )
     => ( v1_xboole_0(k7_relat_1(A,B))
        & v1_relat_1(k7_relat_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc17_relat_1)).

tff(f_30,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_45,negated_conjecture,(
    ~ ! [A] : k7_relat_1(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t111_relat_1)).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_13,plain,(
    ! [A_5] :
      ( v1_relat_1(A_5)
      | ~ v1_xboole_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_17,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_2,c_13])).

tff(c_24,plain,(
    ! [A_7,B_8] :
      ( v1_xboole_0(k7_relat_1(A_7,B_8))
      | ~ v1_relat_1(A_7)
      | ~ v1_xboole_0(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_4,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_34,plain,(
    ! [A_11,B_12] :
      ( k7_relat_1(A_11,B_12) = k1_xboole_0
      | ~ v1_relat_1(A_11)
      | ~ v1_xboole_0(A_11) ) ),
    inference(resolution,[status(thm)],[c_24,c_4])).

tff(c_38,plain,(
    ! [B_12] :
      ( k7_relat_1(k1_xboole_0,B_12) = k1_xboole_0
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_2,c_34])).

tff(c_42,plain,(
    ! [B_12] : k7_relat_1(k1_xboole_0,B_12) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_17,c_38])).

tff(c_12,plain,(
    k7_relat_1(k1_xboole_0,'#skF_1') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_49,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_12])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.13/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.15  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.35  % Computer   : n007.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 19:29:51 EST 2020
% 0.15/0.36  % CPUTime    : 
% 0.15/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.58/1.11  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.58/1.11  
% 1.58/1.11  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.58/1.11  %$ v1_xboole_0 > v1_relat_1 > k7_relat_1 > #nlpp > k1_xboole_0 > #skF_1
% 1.58/1.11  
% 1.58/1.11  %Foreground sorts:
% 1.58/1.11  
% 1.58/1.11  
% 1.58/1.11  %Background operators:
% 1.58/1.11  
% 1.58/1.11  
% 1.58/1.11  %Foreground operators:
% 1.58/1.11  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.58/1.11  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 1.58/1.11  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.58/1.11  tff('#skF_1', type, '#skF_1': $i).
% 1.58/1.11  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.58/1.11  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.58/1.11  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.58/1.11  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.58/1.11  
% 1.58/1.12  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 1.58/1.12  tff(f_34, axiom, (![A]: (v1_xboole_0(A) => v1_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relat_1)).
% 1.58/1.12  tff(f_42, axiom, (![A, B]: ((v1_xboole_0(A) & v1_relat_1(A)) => (v1_xboole_0(k7_relat_1(A, B)) & v1_relat_1(k7_relat_1(A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc17_relat_1)).
% 1.58/1.12  tff(f_30, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 1.58/1.12  tff(f_45, negated_conjecture, ~(![A]: (k7_relat_1(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t111_relat_1)).
% 1.58/1.12  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 1.58/1.12  tff(c_13, plain, (![A_5]: (v1_relat_1(A_5) | ~v1_xboole_0(A_5))), inference(cnfTransformation, [status(thm)], [f_34])).
% 1.58/1.12  tff(c_17, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_13])).
% 1.58/1.12  tff(c_24, plain, (![A_7, B_8]: (v1_xboole_0(k7_relat_1(A_7, B_8)) | ~v1_relat_1(A_7) | ~v1_xboole_0(A_7))), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.58/1.12  tff(c_4, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_30])).
% 1.58/1.12  tff(c_34, plain, (![A_11, B_12]: (k7_relat_1(A_11, B_12)=k1_xboole_0 | ~v1_relat_1(A_11) | ~v1_xboole_0(A_11))), inference(resolution, [status(thm)], [c_24, c_4])).
% 1.58/1.12  tff(c_38, plain, (![B_12]: (k7_relat_1(k1_xboole_0, B_12)=k1_xboole_0 | ~v1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_2, c_34])).
% 1.58/1.12  tff(c_42, plain, (![B_12]: (k7_relat_1(k1_xboole_0, B_12)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_17, c_38])).
% 1.58/1.12  tff(c_12, plain, (k7_relat_1(k1_xboole_0, '#skF_1')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.58/1.12  tff(c_49, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_42, c_12])).
% 1.58/1.12  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.58/1.12  
% 1.58/1.12  Inference rules
% 1.58/1.12  ----------------------
% 1.58/1.12  #Ref     : 0
% 1.58/1.12  #Sup     : 7
% 1.58/1.12  #Fact    : 0
% 1.58/1.12  #Define  : 0
% 1.58/1.12  #Split   : 0
% 1.58/1.12  #Chain   : 0
% 1.58/1.12  #Close   : 0
% 1.58/1.12  
% 1.58/1.12  Ordering : KBO
% 1.58/1.12  
% 1.58/1.12  Simplification rules
% 1.58/1.12  ----------------------
% 1.58/1.12  #Subsume      : 1
% 1.58/1.12  #Demod        : 2
% 1.58/1.12  #Tautology    : 1
% 1.58/1.12  #SimpNegUnit  : 0
% 1.58/1.12  #BackRed      : 1
% 1.58/1.12  
% 1.58/1.12  #Partial instantiations: 0
% 1.58/1.12  #Strategies tried      : 1
% 1.58/1.12  
% 1.58/1.12  Timing (in seconds)
% 1.58/1.12  ----------------------
% 1.58/1.12  Preprocessing        : 0.25
% 1.58/1.12  Parsing              : 0.14
% 1.58/1.12  CNF conversion       : 0.01
% 1.58/1.12  Main loop            : 0.10
% 1.58/1.12  Inferencing          : 0.04
% 1.58/1.12  Reduction            : 0.02
% 1.58/1.12  Demodulation         : 0.02
% 1.58/1.12  BG Simplification    : 0.01
% 1.58/1.12  Subsumption          : 0.02
% 1.58/1.12  Abstraction          : 0.00
% 1.58/1.13  MUC search           : 0.00
% 1.58/1.13  Cooper               : 0.00
% 1.58/1.13  Total                : 0.36
% 1.58/1.13  Index Insertion      : 0.00
% 1.58/1.13  Index Deletion       : 0.00
% 1.58/1.13  Index Matching       : 0.00
% 1.58/1.13  BG Taut test         : 0.00
%------------------------------------------------------------------------------
