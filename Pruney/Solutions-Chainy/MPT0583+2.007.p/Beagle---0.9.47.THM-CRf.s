%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:01:59 EST 2020

% Result     : Theorem 1.51s
% Output     : CNFRefutation 1.60s
% Verified   : 
% Statistics : Number of formulae       :   22 (  24 expanded)
%              Number of leaves         :   13 (  15 expanded)
%              Depth                    :    5
%              Number of atoms          :   21 (  27 expanded)
%              Number of equality atoms :    6 (   8 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > v1_relat_1 > k7_relat_1 > #nlpp > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

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

tff(f_43,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ! [B] :
            ( r1_xboole_0(B,k1_relat_1(A))
           => k7_relat_1(A,B) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t187_relat_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_35,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( k7_relat_1(B,A) = k1_xboole_0
      <=> r1_xboole_0(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_relat_1)).

tff(c_8,plain,(
    k7_relat_1('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_12,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_10,plain,(
    r1_xboole_0('#skF_2',k1_relat_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_13,plain,(
    ! [B_6,A_7] :
      ( r1_xboole_0(B_6,A_7)
      | ~ r1_xboole_0(A_7,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_16,plain,(
    r1_xboole_0(k1_relat_1('#skF_1'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_10,c_13])).

tff(c_21,plain,(
    ! [B_8,A_9] :
      ( k7_relat_1(B_8,A_9) = k1_xboole_0
      | ~ r1_xboole_0(k1_relat_1(B_8),A_9)
      | ~ v1_relat_1(B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_24,plain,
    ( k7_relat_1('#skF_1','#skF_2') = k1_xboole_0
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_16,c_21])).

tff(c_27,plain,(
    k7_relat_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_24])).

tff(c_29,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_8,c_27])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n020.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 14:19:22 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.51/1.07  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.60/1.08  
% 1.60/1.08  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.60/1.08  %$ r1_xboole_0 > v1_relat_1 > k7_relat_1 > #nlpp > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1
% 1.60/1.08  
% 1.60/1.08  %Foreground sorts:
% 1.60/1.08  
% 1.60/1.08  
% 1.60/1.08  %Background operators:
% 1.60/1.08  
% 1.60/1.08  
% 1.60/1.08  %Foreground operators:
% 1.60/1.08  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.60/1.08  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 1.60/1.08  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.60/1.08  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.60/1.08  tff('#skF_2', type, '#skF_2': $i).
% 1.60/1.08  tff('#skF_1', type, '#skF_1': $i).
% 1.60/1.08  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.60/1.08  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.60/1.08  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.60/1.08  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.60/1.08  
% 1.60/1.10  tff(f_43, negated_conjecture, ~(![A]: (v1_relat_1(A) => (![B]: (r1_xboole_0(B, k1_relat_1(A)) => (k7_relat_1(A, B) = k1_xboole_0))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t187_relat_1)).
% 1.60/1.10  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 1.60/1.10  tff(f_35, axiom, (![A, B]: (v1_relat_1(B) => ((k7_relat_1(B, A) = k1_xboole_0) <=> r1_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t95_relat_1)).
% 1.60/1.10  tff(c_8, plain, (k7_relat_1('#skF_1', '#skF_2')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.60/1.10  tff(c_12, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.60/1.10  tff(c_10, plain, (r1_xboole_0('#skF_2', k1_relat_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.60/1.10  tff(c_13, plain, (![B_6, A_7]: (r1_xboole_0(B_6, A_7) | ~r1_xboole_0(A_7, B_6))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.60/1.10  tff(c_16, plain, (r1_xboole_0(k1_relat_1('#skF_1'), '#skF_2')), inference(resolution, [status(thm)], [c_10, c_13])).
% 1.60/1.10  tff(c_21, plain, (![B_8, A_9]: (k7_relat_1(B_8, A_9)=k1_xboole_0 | ~r1_xboole_0(k1_relat_1(B_8), A_9) | ~v1_relat_1(B_8))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.60/1.10  tff(c_24, plain, (k7_relat_1('#skF_1', '#skF_2')=k1_xboole_0 | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_16, c_21])).
% 1.60/1.10  tff(c_27, plain, (k7_relat_1('#skF_1', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_12, c_24])).
% 1.60/1.10  tff(c_29, plain, $false, inference(negUnitSimplification, [status(thm)], [c_8, c_27])).
% 1.60/1.10  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.60/1.10  
% 1.60/1.10  Inference rules
% 1.60/1.10  ----------------------
% 1.60/1.10  #Ref     : 0
% 1.60/1.10  #Sup     : 3
% 1.60/1.10  #Fact    : 0
% 1.60/1.10  #Define  : 0
% 1.60/1.10  #Split   : 0
% 1.60/1.10  #Chain   : 0
% 1.60/1.10  #Close   : 0
% 1.60/1.10  
% 1.60/1.10  Ordering : KBO
% 1.60/1.10  
% 1.60/1.10  Simplification rules
% 1.60/1.10  ----------------------
% 1.60/1.10  #Subsume      : 0
% 1.60/1.10  #Demod        : 2
% 1.60/1.10  #Tautology    : 1
% 1.60/1.10  #SimpNegUnit  : 1
% 1.60/1.10  #BackRed      : 0
% 1.60/1.10  
% 1.60/1.10  #Partial instantiations: 0
% 1.60/1.10  #Strategies tried      : 1
% 1.60/1.10  
% 1.60/1.10  Timing (in seconds)
% 1.60/1.10  ----------------------
% 1.60/1.10  Preprocessing        : 0.24
% 1.60/1.10  Parsing              : 0.14
% 1.60/1.10  CNF conversion       : 0.01
% 1.60/1.11  Main loop            : 0.07
% 1.60/1.11  Inferencing          : 0.03
% 1.60/1.11  Reduction            : 0.02
% 1.60/1.11  Demodulation         : 0.01
% 1.60/1.11  BG Simplification    : 0.01
% 1.60/1.11  Subsumption          : 0.01
% 1.60/1.11  Abstraction          : 0.00
% 1.60/1.11  MUC search           : 0.00
% 1.60/1.11  Cooper               : 0.00
% 1.60/1.11  Total                : 0.35
% 1.60/1.11  Index Insertion      : 0.00
% 1.60/1.11  Index Deletion       : 0.00
% 1.60/1.11  Index Matching       : 0.00
% 1.60/1.11  BG Taut test         : 0.00
%------------------------------------------------------------------------------
