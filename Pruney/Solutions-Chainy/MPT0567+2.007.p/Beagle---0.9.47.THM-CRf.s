%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:01:15 EST 2020

% Result     : Theorem 1.81s
% Output     : CNFRefutation 1.81s
% Verified   : 
% Statistics : Number of formulae       :   30 (  36 expanded)
%              Number of leaves         :   20 (  23 expanded)
%              Depth                    :    6
%              Number of atoms          :   27 (  36 expanded)
%              Number of equality atoms :    7 (   8 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > v1_relat_1 > k4_tarski > k2_tarski > k10_relat_1 > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_4 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(f_52,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => k10_relat_1(A,k1_xboole_0) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t171_relat_1)).

tff(f_47,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B,C] :
          ( C = k10_relat_1(A,B)
        <=> ! [D] :
              ( r2_hidden(D,C)
            <=> ? [E] :
                  ( r2_hidden(k4_tarski(D,E),A)
                  & r2_hidden(E,B) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d14_relat_1)).

tff(f_27,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_34,axiom,(
    ! [A,B] :
      ~ ( r1_xboole_0(k1_tarski(A),B)
        & r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l24_zfmisc_1)).

tff(c_26,plain,(
    k10_relat_1('#skF_5',k1_xboole_0) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_28,plain,(
    v1_relat_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_100,plain,(
    ! [A_74,B_75,C_76] :
      ( r2_hidden('#skF_2'(A_74,B_75,C_76),B_75)
      | r2_hidden('#skF_3'(A_74,B_75,C_76),C_76)
      | k10_relat_1(A_74,B_75) = C_76
      | ~ v1_relat_1(A_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_2,plain,(
    ! [A_1] : r1_xboole_0(A_1,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_39,plain,(
    ! [A_49,B_50] :
      ( ~ r2_hidden(A_49,B_50)
      | ~ r1_xboole_0(k1_tarski(A_49),B_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_44,plain,(
    ! [A_49] : ~ r2_hidden(A_49,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_2,c_39])).

tff(c_144,plain,(
    ! [A_77,C_78] :
      ( r2_hidden('#skF_3'(A_77,k1_xboole_0,C_78),C_78)
      | k10_relat_1(A_77,k1_xboole_0) = C_78
      | ~ v1_relat_1(A_77) ) ),
    inference(resolution,[status(thm)],[c_100,c_44])).

tff(c_168,plain,(
    ! [A_79] :
      ( k10_relat_1(A_79,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(A_79) ) ),
    inference(resolution,[status(thm)],[c_144,c_44])).

tff(c_171,plain,(
    k10_relat_1('#skF_5',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_28,c_168])).

tff(c_175,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_171])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:52:23 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.81/1.15  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.81/1.16  
% 1.81/1.16  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.81/1.16  %$ r2_hidden > r1_xboole_0 > v1_relat_1 > k4_tarski > k2_tarski > k10_relat_1 > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_4 > #skF_3
% 1.81/1.16  
% 1.81/1.16  %Foreground sorts:
% 1.81/1.16  
% 1.81/1.16  
% 1.81/1.16  %Background operators:
% 1.81/1.16  
% 1.81/1.16  
% 1.81/1.16  %Foreground operators:
% 1.81/1.16  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 1.81/1.16  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.81/1.16  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.81/1.16  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.81/1.16  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 1.81/1.16  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.81/1.16  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.81/1.16  tff('#skF_5', type, '#skF_5': $i).
% 1.81/1.16  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.81/1.16  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 1.81/1.16  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i) > $i).
% 1.81/1.16  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.81/1.16  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 1.81/1.16  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.81/1.16  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 1.81/1.16  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.81/1.16  
% 1.81/1.17  tff(f_52, negated_conjecture, ~(![A]: (v1_relat_1(A) => (k10_relat_1(A, k1_xboole_0) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t171_relat_1)).
% 1.81/1.17  tff(f_47, axiom, (![A]: (v1_relat_1(A) => (![B, C]: ((C = k10_relat_1(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (?[E]: (r2_hidden(k4_tarski(D, E), A) & r2_hidden(E, B))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d14_relat_1)).
% 1.81/1.17  tff(f_27, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 1.81/1.17  tff(f_34, axiom, (![A, B]: ~(r1_xboole_0(k1_tarski(A), B) & r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l24_zfmisc_1)).
% 1.81/1.17  tff(c_26, plain, (k10_relat_1('#skF_5', k1_xboole_0)!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_52])).
% 1.81/1.17  tff(c_28, plain, (v1_relat_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_52])).
% 1.81/1.17  tff(c_100, plain, (![A_74, B_75, C_76]: (r2_hidden('#skF_2'(A_74, B_75, C_76), B_75) | r2_hidden('#skF_3'(A_74, B_75, C_76), C_76) | k10_relat_1(A_74, B_75)=C_76 | ~v1_relat_1(A_74))), inference(cnfTransformation, [status(thm)], [f_47])).
% 1.81/1.17  tff(c_2, plain, (![A_1]: (r1_xboole_0(A_1, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.81/1.17  tff(c_39, plain, (![A_49, B_50]: (~r2_hidden(A_49, B_50) | ~r1_xboole_0(k1_tarski(A_49), B_50))), inference(cnfTransformation, [status(thm)], [f_34])).
% 1.81/1.17  tff(c_44, plain, (![A_49]: (~r2_hidden(A_49, k1_xboole_0))), inference(resolution, [status(thm)], [c_2, c_39])).
% 1.81/1.17  tff(c_144, plain, (![A_77, C_78]: (r2_hidden('#skF_3'(A_77, k1_xboole_0, C_78), C_78) | k10_relat_1(A_77, k1_xboole_0)=C_78 | ~v1_relat_1(A_77))), inference(resolution, [status(thm)], [c_100, c_44])).
% 1.81/1.17  tff(c_168, plain, (![A_79]: (k10_relat_1(A_79, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(A_79))), inference(resolution, [status(thm)], [c_144, c_44])).
% 1.81/1.17  tff(c_171, plain, (k10_relat_1('#skF_5', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_28, c_168])).
% 1.81/1.17  tff(c_175, plain, $false, inference(negUnitSimplification, [status(thm)], [c_26, c_171])).
% 1.81/1.17  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.81/1.17  
% 1.81/1.17  Inference rules
% 1.81/1.17  ----------------------
% 1.81/1.17  #Ref     : 0
% 1.81/1.17  #Sup     : 28
% 1.81/1.17  #Fact    : 0
% 1.81/1.17  #Define  : 0
% 1.81/1.17  #Split   : 1
% 1.81/1.17  #Chain   : 0
% 1.81/1.17  #Close   : 0
% 1.81/1.17  
% 1.81/1.17  Ordering : KBO
% 1.81/1.17  
% 1.81/1.17  Simplification rules
% 1.81/1.17  ----------------------
% 1.81/1.17  #Subsume      : 0
% 1.81/1.17  #Demod        : 0
% 1.81/1.17  #Tautology    : 2
% 1.81/1.17  #SimpNegUnit  : 1
% 1.81/1.17  #BackRed      : 0
% 1.81/1.17  
% 1.81/1.17  #Partial instantiations: 0
% 1.81/1.17  #Strategies tried      : 1
% 1.81/1.17  
% 1.81/1.17  Timing (in seconds)
% 1.81/1.17  ----------------------
% 1.81/1.17  Preprocessing        : 0.28
% 1.81/1.17  Parsing              : 0.14
% 1.81/1.17  CNF conversion       : 0.02
% 1.81/1.17  Main loop            : 0.15
% 1.81/1.17  Inferencing          : 0.05
% 1.81/1.17  Reduction            : 0.03
% 1.81/1.17  Demodulation         : 0.02
% 1.81/1.17  BG Simplification    : 0.01
% 1.81/1.17  Subsumption          : 0.04
% 1.81/1.17  Abstraction          : 0.01
% 1.81/1.17  MUC search           : 0.00
% 1.81/1.17  Cooper               : 0.00
% 1.81/1.17  Total                : 0.44
% 1.81/1.17  Index Insertion      : 0.00
% 1.81/1.17  Index Deletion       : 0.00
% 1.81/1.17  Index Matching       : 0.00
% 1.81/1.17  BG Taut test         : 0.00
%------------------------------------------------------------------------------
