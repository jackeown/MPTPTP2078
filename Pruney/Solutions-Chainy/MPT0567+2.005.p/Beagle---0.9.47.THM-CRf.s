%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:01:15 EST 2020

% Result     : Theorem 2.28s
% Output     : CNFRefutation 2.28s
% Verified   : 
% Statistics : Number of formulae       :   30 (  35 expanded)
%              Number of leaves         :   19 (  22 expanded)
%              Depth                    :    7
%              Number of atoms          :   34 (  42 expanded)
%              Number of equality atoms :    9 (  10 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v1_xboole_0 > v1_relat_1 > k4_tarski > k10_relat_1 > #nlpp > k1_xboole_0 > #skF_1 > #skF_4 > #skF_6 > #skF_2 > #skF_5 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(f_50,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => k10_relat_1(A,k1_xboole_0) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t171_relat_1)).

tff(f_32,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_45,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B,C] :
          ( C = k10_relat_1(A,B)
        <=> ! [D] :
              ( r2_hidden(D,C)
            <=> ? [E] :
                  ( r2_hidden(k4_tarski(D,E),A)
                  & r2_hidden(E,B) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d14_relat_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(c_26,plain,(
    k10_relat_1('#skF_6',k1_xboole_0) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_28,plain,(
    v1_relat_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_6,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_173,plain,(
    ! [A_96,B_97,C_98] :
      ( r2_hidden('#skF_3'(A_96,B_97,C_98),B_97)
      | r2_hidden('#skF_4'(A_96,B_97,C_98),C_98)
      | k10_relat_1(A_96,B_97) = C_98
      | ~ v1_relat_1(A_96) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_239,plain,(
    ! [B_102,A_103,C_104] :
      ( ~ v1_xboole_0(B_102)
      | r2_hidden('#skF_4'(A_103,B_102,C_104),C_104)
      | k10_relat_1(A_103,B_102) = C_104
      | ~ v1_relat_1(A_103) ) ),
    inference(resolution,[status(thm)],[c_173,c_2])).

tff(c_272,plain,(
    ! [C_105,B_106,A_107] :
      ( ~ v1_xboole_0(C_105)
      | ~ v1_xboole_0(B_106)
      | k10_relat_1(A_107,B_106) = C_105
      | ~ v1_relat_1(A_107) ) ),
    inference(resolution,[status(thm)],[c_239,c_2])).

tff(c_291,plain,(
    ! [B_108,A_109] :
      ( ~ v1_xboole_0(B_108)
      | k10_relat_1(A_109,B_108) = k1_xboole_0
      | ~ v1_relat_1(A_109) ) ),
    inference(resolution,[status(thm)],[c_6,c_272])).

tff(c_310,plain,(
    ! [A_110] :
      ( k10_relat_1(A_110,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(A_110) ) ),
    inference(resolution,[status(thm)],[c_6,c_291])).

tff(c_313,plain,(
    k10_relat_1('#skF_6',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_28,c_310])).

tff(c_317,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_313])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n013.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 13:44:39 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.28/1.33  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.28/1.33  
% 2.28/1.33  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.28/1.33  %$ r2_hidden > v1_xboole_0 > v1_relat_1 > k4_tarski > k10_relat_1 > #nlpp > k1_xboole_0 > #skF_1 > #skF_4 > #skF_6 > #skF_2 > #skF_5 > #skF_3
% 2.28/1.33  
% 2.28/1.33  %Foreground sorts:
% 2.28/1.33  
% 2.28/1.33  
% 2.28/1.33  %Background operators:
% 2.28/1.33  
% 2.28/1.33  
% 2.28/1.33  %Foreground operators:
% 2.28/1.33  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.28/1.33  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.28/1.33  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.28/1.33  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.28/1.33  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.28/1.33  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 2.28/1.33  tff('#skF_6', type, '#skF_6': $i).
% 2.28/1.33  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.28/1.33  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.28/1.33  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 2.28/1.33  tff('#skF_5', type, '#skF_5': ($i * $i * $i * $i) > $i).
% 2.28/1.33  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.28/1.33  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 2.28/1.33  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.28/1.33  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.28/1.33  
% 2.28/1.34  tff(f_50, negated_conjecture, ~(![A]: (v1_relat_1(A) => (k10_relat_1(A, k1_xboole_0) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t171_relat_1)).
% 2.28/1.34  tff(f_32, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.28/1.34  tff(f_45, axiom, (![A]: (v1_relat_1(A) => (![B, C]: ((C = k10_relat_1(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (?[E]: (r2_hidden(k4_tarski(D, E), A) & r2_hidden(E, B))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d14_relat_1)).
% 2.28/1.34  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 2.28/1.34  tff(c_26, plain, (k10_relat_1('#skF_6', k1_xboole_0)!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.28/1.34  tff(c_28, plain, (v1_relat_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.28/1.34  tff(c_6, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.28/1.34  tff(c_173, plain, (![A_96, B_97, C_98]: (r2_hidden('#skF_3'(A_96, B_97, C_98), B_97) | r2_hidden('#skF_4'(A_96, B_97, C_98), C_98) | k10_relat_1(A_96, B_97)=C_98 | ~v1_relat_1(A_96))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.28/1.34  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.28/1.34  tff(c_239, plain, (![B_102, A_103, C_104]: (~v1_xboole_0(B_102) | r2_hidden('#skF_4'(A_103, B_102, C_104), C_104) | k10_relat_1(A_103, B_102)=C_104 | ~v1_relat_1(A_103))), inference(resolution, [status(thm)], [c_173, c_2])).
% 2.28/1.34  tff(c_272, plain, (![C_105, B_106, A_107]: (~v1_xboole_0(C_105) | ~v1_xboole_0(B_106) | k10_relat_1(A_107, B_106)=C_105 | ~v1_relat_1(A_107))), inference(resolution, [status(thm)], [c_239, c_2])).
% 2.28/1.34  tff(c_291, plain, (![B_108, A_109]: (~v1_xboole_0(B_108) | k10_relat_1(A_109, B_108)=k1_xboole_0 | ~v1_relat_1(A_109))), inference(resolution, [status(thm)], [c_6, c_272])).
% 2.28/1.34  tff(c_310, plain, (![A_110]: (k10_relat_1(A_110, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(A_110))), inference(resolution, [status(thm)], [c_6, c_291])).
% 2.28/1.34  tff(c_313, plain, (k10_relat_1('#skF_6', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_28, c_310])).
% 2.28/1.34  tff(c_317, plain, $false, inference(negUnitSimplification, [status(thm)], [c_26, c_313])).
% 2.28/1.34  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.28/1.34  
% 2.28/1.34  Inference rules
% 2.28/1.34  ----------------------
% 2.28/1.34  #Ref     : 0
% 2.28/1.34  #Sup     : 62
% 2.28/1.34  #Fact    : 0
% 2.28/1.34  #Define  : 0
% 2.28/1.34  #Split   : 0
% 2.28/1.34  #Chain   : 0
% 2.28/1.34  #Close   : 0
% 2.28/1.34  
% 2.28/1.34  Ordering : KBO
% 2.28/1.34  
% 2.28/1.34  Simplification rules
% 2.28/1.34  ----------------------
% 2.28/1.34  #Subsume      : 6
% 2.28/1.34  #Demod        : 0
% 2.28/1.34  #Tautology    : 1
% 2.28/1.34  #SimpNegUnit  : 1
% 2.28/1.34  #BackRed      : 0
% 2.28/1.34  
% 2.28/1.34  #Partial instantiations: 0
% 2.28/1.34  #Strategies tried      : 1
% 2.28/1.34  
% 2.28/1.34  Timing (in seconds)
% 2.28/1.34  ----------------------
% 2.28/1.34  Preprocessing        : 0.26
% 2.28/1.34  Parsing              : 0.13
% 2.28/1.34  CNF conversion       : 0.03
% 2.28/1.34  Main loop            : 0.25
% 2.28/1.34  Inferencing          : 0.11
% 2.28/1.34  Reduction            : 0.05
% 2.28/1.34  Demodulation         : 0.03
% 2.28/1.34  BG Simplification    : 0.02
% 2.28/1.34  Subsumption          : 0.07
% 2.28/1.34  Abstraction          : 0.01
% 2.28/1.34  MUC search           : 0.00
% 2.28/1.34  Cooper               : 0.00
% 2.28/1.35  Total                : 0.53
% 2.28/1.35  Index Insertion      : 0.00
% 2.28/1.35  Index Deletion       : 0.00
% 2.28/1.35  Index Matching       : 0.00
% 2.28/1.35  BG Taut test         : 0.00
%------------------------------------------------------------------------------
