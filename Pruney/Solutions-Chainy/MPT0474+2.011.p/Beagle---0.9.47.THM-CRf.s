%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:59:29 EST 2020

% Result     : Theorem 1.71s
% Output     : CNFRefutation 1.71s
% Verified   : 
% Statistics : Number of formulae       :   24 (  24 expanded)
%              Number of leaves         :   15 (  15 expanded)
%              Depth                    :    5
%              Number of atoms          :   23 (  23 expanded)
%              Number of equality atoms :    7 (   7 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v1_xboole_0 > v1_relat_1 > #nlpp > k4_relat_1 > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

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

tff(f_48,negated_conjecture,(
    k4_relat_1(k1_xboole_0) != k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_relat_1)).

tff(f_32,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_46,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => ( v1_xboole_0(k4_relat_1(A))
        & v1_relat_1(k4_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc14_relat_1)).

tff(f_40,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(c_14,plain,(
    k4_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_6,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_12,plain,(
    ! [A_7] :
      ( v1_xboole_0(k4_relat_1(A_7))
      | ~ v1_xboole_0(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_18,plain,(
    ! [A_12] :
      ( r2_hidden('#skF_2'(A_12),A_12)
      | k1_xboole_0 = A_12 ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_23,plain,(
    ! [A_13] :
      ( ~ v1_xboole_0(A_13)
      | k1_xboole_0 = A_13 ) ),
    inference(resolution,[status(thm)],[c_18,c_2])).

tff(c_33,plain,(
    ! [A_14] :
      ( k4_relat_1(A_14) = k1_xboole_0
      | ~ v1_xboole_0(A_14) ) ),
    inference(resolution,[status(thm)],[c_12,c_23])).

tff(c_39,plain,(
    k4_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_6,c_33])).

tff(c_44,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_14,c_39])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:11:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.71/1.16  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.71/1.17  
% 1.71/1.17  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.71/1.17  %$ r2_hidden > v1_xboole_0 > v1_relat_1 > #nlpp > k4_relat_1 > k1_xboole_0 > #skF_2 > #skF_1
% 1.71/1.17  
% 1.71/1.17  %Foreground sorts:
% 1.71/1.17  
% 1.71/1.17  
% 1.71/1.17  %Background operators:
% 1.71/1.17  
% 1.71/1.17  
% 1.71/1.17  %Foreground operators:
% 1.71/1.17  tff('#skF_2', type, '#skF_2': $i > $i).
% 1.71/1.17  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.71/1.17  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.71/1.17  tff('#skF_1', type, '#skF_1': $i > $i).
% 1.71/1.17  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.71/1.17  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.71/1.17  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.71/1.17  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.71/1.17  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.71/1.17  tff(k4_relat_1, type, k4_relat_1: $i > $i).
% 1.71/1.17  
% 1.71/1.17  tff(f_48, negated_conjecture, ~(k4_relat_1(k1_xboole_0) = k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t66_relat_1)).
% 1.71/1.17  tff(f_32, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 1.71/1.17  tff(f_46, axiom, (![A]: (v1_xboole_0(A) => (v1_xboole_0(k4_relat_1(A)) & v1_relat_1(k4_relat_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc14_relat_1)).
% 1.71/1.17  tff(f_40, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 1.71/1.17  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 1.71/1.17  tff(c_14, plain, (k4_relat_1(k1_xboole_0)!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_48])).
% 1.71/1.17  tff(c_6, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.71/1.17  tff(c_12, plain, (![A_7]: (v1_xboole_0(k4_relat_1(A_7)) | ~v1_xboole_0(A_7))), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.71/1.17  tff(c_18, plain, (![A_12]: (r2_hidden('#skF_2'(A_12), A_12) | k1_xboole_0=A_12)), inference(cnfTransformation, [status(thm)], [f_40])).
% 1.71/1.17  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.71/1.17  tff(c_23, plain, (![A_13]: (~v1_xboole_0(A_13) | k1_xboole_0=A_13)), inference(resolution, [status(thm)], [c_18, c_2])).
% 1.71/1.17  tff(c_33, plain, (![A_14]: (k4_relat_1(A_14)=k1_xboole_0 | ~v1_xboole_0(A_14))), inference(resolution, [status(thm)], [c_12, c_23])).
% 1.71/1.17  tff(c_39, plain, (k4_relat_1(k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_6, c_33])).
% 1.71/1.17  tff(c_44, plain, $false, inference(negUnitSimplification, [status(thm)], [c_14, c_39])).
% 1.71/1.17  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.71/1.17  
% 1.71/1.17  Inference rules
% 1.71/1.17  ----------------------
% 1.71/1.17  #Ref     : 0
% 1.71/1.17  #Sup     : 5
% 1.71/1.17  #Fact    : 0
% 1.71/1.17  #Define  : 0
% 1.71/1.17  #Split   : 0
% 1.71/1.17  #Chain   : 0
% 1.71/1.17  #Close   : 0
% 1.71/1.17  
% 1.71/1.17  Ordering : KBO
% 1.71/1.17  
% 1.71/1.17  Simplification rules
% 1.71/1.17  ----------------------
% 1.71/1.17  #Subsume      : 0
% 1.71/1.17  #Demod        : 0
% 1.71/1.17  #Tautology    : 1
% 1.71/1.17  #SimpNegUnit  : 1
% 1.71/1.17  #BackRed      : 0
% 1.71/1.17  
% 1.71/1.17  #Partial instantiations: 0
% 1.71/1.17  #Strategies tried      : 1
% 1.71/1.17  
% 1.71/1.17  Timing (in seconds)
% 1.71/1.17  ----------------------
% 1.71/1.18  Preprocessing        : 0.26
% 1.71/1.18  Parsing              : 0.15
% 1.71/1.18  CNF conversion       : 0.02
% 1.71/1.18  Main loop            : 0.08
% 1.71/1.18  Inferencing          : 0.04
% 1.71/1.18  Reduction            : 0.02
% 1.71/1.18  Demodulation         : 0.01
% 1.71/1.18  BG Simplification    : 0.01
% 1.71/1.18  Subsumption          : 0.01
% 1.71/1.18  Abstraction          : 0.00
% 1.71/1.18  MUC search           : 0.00
% 1.71/1.18  Cooper               : 0.00
% 1.71/1.18  Total                : 0.37
% 1.71/1.18  Index Insertion      : 0.00
% 1.71/1.18  Index Deletion       : 0.00
% 1.71/1.18  Index Matching       : 0.00
% 1.71/1.18  BG Taut test         : 0.00
%------------------------------------------------------------------------------
