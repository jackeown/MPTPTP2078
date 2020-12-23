%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:01:14 EST 2020

% Result     : Theorem 2.04s
% Output     : CNFRefutation 2.04s
% Verified   : 
% Statistics : Number of formulae       :   33 (  35 expanded)
%              Number of leaves         :   22 (  24 expanded)
%              Depth                    :    6
%              Number of atoms          :   34 (  39 expanded)
%              Number of equality atoms :    1 (   1 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_relat_1 > k4_tarski > k10_relat_1 > #nlpp > k2_relat_1 > k1_relat_1 > #skF_6 > #skF_7 > #skF_3 > #skF_5 > #skF_8 > #skF_2 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_56,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => r1_tarski(k10_relat_1(B,A),k1_relat_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t167_relat_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k10_relat_1(C,B))
      <=> ? [D] :
            ( r2_hidden(D,k2_relat_1(C))
            & r2_hidden(k4_tarski(A,D),C)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t166_relat_1)).

tff(f_40,axiom,(
    ! [A,B] :
      ( B = k1_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(C,D),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_1)).

tff(c_30,plain,(
    v1_relat_1('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_75,plain,(
    ! [A_62,B_63,C_64] :
      ( r2_hidden(k4_tarski(A_62,'#skF_6'(A_62,B_63,C_64)),C_64)
      | ~ r2_hidden(A_62,k10_relat_1(C_64,B_63))
      | ~ v1_relat_1(C_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_10,plain,(
    ! [C_21,A_6,D_24] :
      ( r2_hidden(C_21,k1_relat_1(A_6))
      | ~ r2_hidden(k4_tarski(C_21,D_24),A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_91,plain,(
    ! [A_67,C_68,B_69] :
      ( r2_hidden(A_67,k1_relat_1(C_68))
      | ~ r2_hidden(A_67,k10_relat_1(C_68,B_69))
      | ~ v1_relat_1(C_68) ) ),
    inference(resolution,[status(thm)],[c_75,c_10])).

tff(c_144,plain,(
    ! [C_72,B_73,B_74] :
      ( r2_hidden('#skF_1'(k10_relat_1(C_72,B_73),B_74),k1_relat_1(C_72))
      | ~ v1_relat_1(C_72)
      | r1_tarski(k10_relat_1(C_72,B_73),B_74) ) ),
    inference(resolution,[status(thm)],[c_6,c_91])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_162,plain,(
    ! [C_78,B_79] :
      ( ~ v1_relat_1(C_78)
      | r1_tarski(k10_relat_1(C_78,B_79),k1_relat_1(C_78)) ) ),
    inference(resolution,[status(thm)],[c_144,c_4])).

tff(c_28,plain,(
    ~ r1_tarski(k10_relat_1('#skF_8','#skF_7'),k1_relat_1('#skF_8')) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_167,plain,(
    ~ v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_162,c_28])).

tff(c_172,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_167])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:35:22 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.04/1.30  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.04/1.30  
% 2.04/1.30  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.04/1.31  %$ r2_hidden > r1_tarski > v1_relat_1 > k4_tarski > k10_relat_1 > #nlpp > k2_relat_1 > k1_relat_1 > #skF_6 > #skF_7 > #skF_3 > #skF_5 > #skF_8 > #skF_2 > #skF_1 > #skF_4
% 2.04/1.31  
% 2.04/1.31  %Foreground sorts:
% 2.04/1.31  
% 2.04/1.31  
% 2.04/1.31  %Background operators:
% 2.04/1.31  
% 2.04/1.31  
% 2.04/1.31  %Foreground operators:
% 2.04/1.31  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.04/1.31  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.04/1.31  tff('#skF_6', type, '#skF_6': ($i * $i * $i) > $i).
% 2.04/1.31  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.04/1.31  tff('#skF_7', type, '#skF_7': $i).
% 2.04/1.31  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.04/1.31  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.04/1.31  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.04/1.31  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 2.04/1.31  tff('#skF_8', type, '#skF_8': $i).
% 2.04/1.31  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.04/1.31  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 2.04/1.31  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.04/1.31  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.04/1.31  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.04/1.31  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.04/1.31  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.04/1.31  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 2.04/1.31  
% 2.04/1.31  tff(f_56, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => r1_tarski(k10_relat_1(B, A), k1_relat_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t167_relat_1)).
% 2.04/1.31  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 2.04/1.31  tff(f_51, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k10_relat_1(C, B)) <=> (?[D]: ((r2_hidden(D, k2_relat_1(C)) & r2_hidden(k4_tarski(A, D), C)) & r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t166_relat_1)).
% 2.04/1.31  tff(f_40, axiom, (![A, B]: ((B = k1_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(C, D), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_relat_1)).
% 2.04/1.31  tff(c_30, plain, (v1_relat_1('#skF_8')), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.04/1.31  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.04/1.31  tff(c_75, plain, (![A_62, B_63, C_64]: (r2_hidden(k4_tarski(A_62, '#skF_6'(A_62, B_63, C_64)), C_64) | ~r2_hidden(A_62, k10_relat_1(C_64, B_63)) | ~v1_relat_1(C_64))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.04/1.31  tff(c_10, plain, (![C_21, A_6, D_24]: (r2_hidden(C_21, k1_relat_1(A_6)) | ~r2_hidden(k4_tarski(C_21, D_24), A_6))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.04/1.31  tff(c_91, plain, (![A_67, C_68, B_69]: (r2_hidden(A_67, k1_relat_1(C_68)) | ~r2_hidden(A_67, k10_relat_1(C_68, B_69)) | ~v1_relat_1(C_68))), inference(resolution, [status(thm)], [c_75, c_10])).
% 2.04/1.31  tff(c_144, plain, (![C_72, B_73, B_74]: (r2_hidden('#skF_1'(k10_relat_1(C_72, B_73), B_74), k1_relat_1(C_72)) | ~v1_relat_1(C_72) | r1_tarski(k10_relat_1(C_72, B_73), B_74))), inference(resolution, [status(thm)], [c_6, c_91])).
% 2.04/1.31  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.04/1.31  tff(c_162, plain, (![C_78, B_79]: (~v1_relat_1(C_78) | r1_tarski(k10_relat_1(C_78, B_79), k1_relat_1(C_78)))), inference(resolution, [status(thm)], [c_144, c_4])).
% 2.04/1.31  tff(c_28, plain, (~r1_tarski(k10_relat_1('#skF_8', '#skF_7'), k1_relat_1('#skF_8'))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.04/1.31  tff(c_167, plain, (~v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_162, c_28])).
% 2.04/1.31  tff(c_172, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_30, c_167])).
% 2.04/1.31  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.04/1.31  
% 2.04/1.31  Inference rules
% 2.04/1.31  ----------------------
% 2.04/1.31  #Ref     : 0
% 2.04/1.31  #Sup     : 30
% 2.04/1.31  #Fact    : 0
% 2.04/1.31  #Define  : 0
% 2.04/1.31  #Split   : 0
% 2.04/1.31  #Chain   : 0
% 2.04/1.31  #Close   : 0
% 2.04/1.31  
% 2.04/1.31  Ordering : KBO
% 2.04/1.31  
% 2.04/1.31  Simplification rules
% 2.04/1.31  ----------------------
% 2.04/1.31  #Subsume      : 2
% 2.04/1.31  #Demod        : 1
% 2.04/1.31  #Tautology    : 3
% 2.04/1.31  #SimpNegUnit  : 0
% 2.04/1.31  #BackRed      : 0
% 2.04/1.31  
% 2.04/1.31  #Partial instantiations: 0
% 2.04/1.31  #Strategies tried      : 1
% 2.04/1.31  
% 2.04/1.31  Timing (in seconds)
% 2.04/1.31  ----------------------
% 2.04/1.32  Preprocessing        : 0.32
% 2.04/1.32  Parsing              : 0.17
% 2.04/1.32  CNF conversion       : 0.03
% 2.04/1.32  Main loop            : 0.18
% 2.04/1.32  Inferencing          : 0.07
% 2.04/1.32  Reduction            : 0.04
% 2.04/1.32  Demodulation         : 0.03
% 2.04/1.32  BG Simplification    : 0.02
% 2.04/1.32  Subsumption          : 0.04
% 2.04/1.32  Abstraction          : 0.01
% 2.04/1.32  MUC search           : 0.00
% 2.04/1.32  Cooper               : 0.00
% 2.04/1.32  Total                : 0.52
% 2.04/1.32  Index Insertion      : 0.00
% 2.04/1.32  Index Deletion       : 0.00
% 2.04/1.32  Index Matching       : 0.00
% 2.04/1.32  BG Taut test         : 0.00
%------------------------------------------------------------------------------
