%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:02:02 EST 2020

% Result     : Theorem 1.56s
% Output     : CNFRefutation 1.71s
% Verified   : 
% Statistics : Number of formulae       :   16 (  18 expanded)
%              Number of leaves         :   10 (  12 expanded)
%              Depth                    :    3
%              Number of atoms          :   16 (  22 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_relat_1 > v1_relat_1 > k7_relat_1 > #nlpp > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(v3_relat_1,type,(
    v3_relat_1: $i > $o )).

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

tff(f_42,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ~ ( ~ v3_relat_1(k7_relat_1(B,A))
            & v3_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t190_relat_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(A)
        & v3_relat_1(A) )
     => ( v1_relat_1(k7_relat_1(A,B))
        & v3_relat_1(k7_relat_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc19_relat_1)).

tff(c_10,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_6,plain,(
    v3_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_11,plain,(
    ! [A_3,B_4] :
      ( v3_relat_1(k7_relat_1(A_3,B_4))
      | ~ v3_relat_1(A_3)
      | ~ v1_relat_1(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_8,plain,(
    ~ v3_relat_1(k7_relat_1('#skF_2','#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_14,plain,
    ( ~ v3_relat_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_11,c_8])).

tff(c_18,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_6,c_14])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n025.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 19:47:21 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.56/1.16  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.71/1.16  
% 1.71/1.16  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.71/1.17  %$ v3_relat_1 > v1_relat_1 > k7_relat_1 > #nlpp > #skF_2 > #skF_1
% 1.71/1.17  
% 1.71/1.17  %Foreground sorts:
% 1.71/1.17  
% 1.71/1.17  
% 1.71/1.17  %Background operators:
% 1.71/1.17  
% 1.71/1.17  
% 1.71/1.17  %Foreground operators:
% 1.71/1.17  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.71/1.17  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 1.71/1.17  tff(v3_relat_1, type, v3_relat_1: $i > $o).
% 1.71/1.17  tff('#skF_2', type, '#skF_2': $i).
% 1.71/1.17  tff('#skF_1', type, '#skF_1': $i).
% 1.71/1.17  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.71/1.17  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.71/1.17  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.71/1.17  
% 1.71/1.18  tff(f_42, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => ~(~v3_relat_1(k7_relat_1(B, A)) & v3_relat_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t190_relat_1)).
% 1.71/1.18  tff(f_33, axiom, (![A, B]: ((v1_relat_1(A) & v3_relat_1(A)) => (v1_relat_1(k7_relat_1(A, B)) & v3_relat_1(k7_relat_1(A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc19_relat_1)).
% 1.71/1.18  tff(c_10, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.71/1.18  tff(c_6, plain, (v3_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.71/1.18  tff(c_11, plain, (![A_3, B_4]: (v3_relat_1(k7_relat_1(A_3, B_4)) | ~v3_relat_1(A_3) | ~v1_relat_1(A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.71/1.18  tff(c_8, plain, (~v3_relat_1(k7_relat_1('#skF_2', '#skF_1'))), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.71/1.18  tff(c_14, plain, (~v3_relat_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_11, c_8])).
% 1.71/1.18  tff(c_18, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_10, c_6, c_14])).
% 1.71/1.18  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.71/1.18  
% 1.71/1.18  Inference rules
% 1.71/1.18  ----------------------
% 1.71/1.18  #Ref     : 0
% 1.71/1.18  #Sup     : 1
% 1.71/1.18  #Fact    : 0
% 1.71/1.18  #Define  : 0
% 1.71/1.18  #Split   : 0
% 1.71/1.18  #Chain   : 0
% 1.71/1.18  #Close   : 0
% 1.71/1.18  
% 1.71/1.18  Ordering : KBO
% 1.71/1.18  
% 1.71/1.18  Simplification rules
% 1.71/1.18  ----------------------
% 1.71/1.18  #Subsume      : 0
% 1.71/1.18  #Demod        : 2
% 1.71/1.18  #Tautology    : 0
% 1.71/1.18  #SimpNegUnit  : 0
% 1.71/1.18  #BackRed      : 0
% 1.71/1.18  
% 1.71/1.18  #Partial instantiations: 0
% 1.71/1.18  #Strategies tried      : 1
% 1.71/1.18  
% 1.71/1.18  Timing (in seconds)
% 1.71/1.18  ----------------------
% 1.71/1.19  Preprocessing        : 0.27
% 1.71/1.19  Parsing              : 0.15
% 1.71/1.19  CNF conversion       : 0.02
% 1.71/1.19  Main loop            : 0.07
% 1.71/1.19  Inferencing          : 0.03
% 1.71/1.19  Reduction            : 0.02
% 1.71/1.19  Demodulation         : 0.02
% 1.71/1.19  BG Simplification    : 0.01
% 1.71/1.19  Subsumption          : 0.01
% 1.71/1.19  Abstraction          : 0.00
% 1.71/1.19  MUC search           : 0.00
% 1.71/1.19  Cooper               : 0.00
% 1.71/1.19  Total                : 0.37
% 1.71/1.19  Index Insertion      : 0.00
% 1.71/1.19  Index Deletion       : 0.00
% 1.71/1.19  Index Matching       : 0.00
% 1.71/1.19  BG Taut test         : 0.00
%------------------------------------------------------------------------------
