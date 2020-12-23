%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:01:16 EST 2020

% Result     : Theorem 2.07s
% Output     : CNFRefutation 2.07s
% Verified   : 
% Statistics : Number of formulae       :   33 (  42 expanded)
%              Number of leaves         :   21 (  25 expanded)
%              Depth                    :    7
%              Number of atoms          :   33 (  48 expanded)
%              Number of equality atoms :    9 (  12 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > v1_relat_1 > k4_tarski > k3_xboole_0 > k10_relat_1 > #nlpp > k1_xboole_0 > #skF_4 > #skF_6 > #skF_2 > #skF_5 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_61,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => k10_relat_1(A,k1_xboole_0) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t171_relat_1)).

tff(f_56,axiom,(
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

tff(f_43,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_41,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

tff(f_39,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

tff(c_28,plain,(
    k10_relat_1('#skF_6',k1_xboole_0) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_30,plain,(
    v1_relat_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_208,plain,(
    ! [A_92,B_93,C_94] :
      ( r2_hidden('#skF_3'(A_92,B_93,C_94),B_93)
      | r2_hidden('#skF_4'(A_92,B_93,C_94),C_94)
      | k10_relat_1(A_92,B_93) = C_94
      | ~ v1_relat_1(A_92) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_8,plain,(
    ! [A_7] : r1_xboole_0(A_7,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_6,plain,(
    ! [A_6] : k3_xboole_0(A_6,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_39,plain,(
    ! [A_52,B_53,C_54] :
      ( ~ r1_xboole_0(A_52,B_53)
      | ~ r2_hidden(C_54,k3_xboole_0(A_52,B_53)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_42,plain,(
    ! [A_6,C_54] :
      ( ~ r1_xboole_0(A_6,k1_xboole_0)
      | ~ r2_hidden(C_54,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_39])).

tff(c_44,plain,(
    ! [C_54] : ~ r2_hidden(C_54,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_42])).

tff(c_292,plain,(
    ! [A_95,B_96] :
      ( r2_hidden('#skF_3'(A_95,B_96,k1_xboole_0),B_96)
      | k10_relat_1(A_95,B_96) = k1_xboole_0
      | ~ v1_relat_1(A_95) ) ),
    inference(resolution,[status(thm)],[c_208,c_44])).

tff(c_336,plain,(
    ! [A_97] :
      ( k10_relat_1(A_97,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(A_97) ) ),
    inference(resolution,[status(thm)],[c_292,c_44])).

tff(c_339,plain,(
    k10_relat_1('#skF_6',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_30,c_336])).

tff(c_343,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_339])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.35  % Computer   : n008.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 12:02:45 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.07/1.30  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.07/1.30  
% 2.07/1.30  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.07/1.30  %$ r2_hidden > r1_xboole_0 > v1_relat_1 > k4_tarski > k3_xboole_0 > k10_relat_1 > #nlpp > k1_xboole_0 > #skF_4 > #skF_6 > #skF_2 > #skF_5 > #skF_3 > #skF_1
% 2.07/1.30  
% 2.07/1.30  %Foreground sorts:
% 2.07/1.30  
% 2.07/1.30  
% 2.07/1.30  %Background operators:
% 2.07/1.30  
% 2.07/1.30  
% 2.07/1.30  %Foreground operators:
% 2.07/1.30  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.07/1.30  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.07/1.30  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.07/1.30  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.07/1.30  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 2.07/1.30  tff('#skF_6', type, '#skF_6': $i).
% 2.07/1.30  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.07/1.30  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.07/1.30  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.07/1.30  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 2.07/1.30  tff('#skF_5', type, '#skF_5': ($i * $i * $i * $i) > $i).
% 2.07/1.30  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.07/1.30  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 2.07/1.30  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.07/1.30  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.07/1.30  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.07/1.30  
% 2.07/1.31  tff(f_61, negated_conjecture, ~(![A]: (v1_relat_1(A) => (k10_relat_1(A, k1_xboole_0) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t171_relat_1)).
% 2.07/1.31  tff(f_56, axiom, (![A]: (v1_relat_1(A) => (![B, C]: ((C = k10_relat_1(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (?[E]: (r2_hidden(k4_tarski(D, E), A) & r2_hidden(E, B))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d14_relat_1)).
% 2.07/1.31  tff(f_43, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 2.07/1.31  tff(f_41, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 2.07/1.31  tff(f_39, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 2.07/1.31  tff(c_28, plain, (k10_relat_1('#skF_6', k1_xboole_0)!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.07/1.31  tff(c_30, plain, (v1_relat_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.07/1.31  tff(c_208, plain, (![A_92, B_93, C_94]: (r2_hidden('#skF_3'(A_92, B_93, C_94), B_93) | r2_hidden('#skF_4'(A_92, B_93, C_94), C_94) | k10_relat_1(A_92, B_93)=C_94 | ~v1_relat_1(A_92))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.07/1.31  tff(c_8, plain, (![A_7]: (r1_xboole_0(A_7, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.07/1.31  tff(c_6, plain, (![A_6]: (k3_xboole_0(A_6, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.07/1.31  tff(c_39, plain, (![A_52, B_53, C_54]: (~r1_xboole_0(A_52, B_53) | ~r2_hidden(C_54, k3_xboole_0(A_52, B_53)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.07/1.31  tff(c_42, plain, (![A_6, C_54]: (~r1_xboole_0(A_6, k1_xboole_0) | ~r2_hidden(C_54, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_6, c_39])).
% 2.07/1.31  tff(c_44, plain, (![C_54]: (~r2_hidden(C_54, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_42])).
% 2.07/1.31  tff(c_292, plain, (![A_95, B_96]: (r2_hidden('#skF_3'(A_95, B_96, k1_xboole_0), B_96) | k10_relat_1(A_95, B_96)=k1_xboole_0 | ~v1_relat_1(A_95))), inference(resolution, [status(thm)], [c_208, c_44])).
% 2.07/1.31  tff(c_336, plain, (![A_97]: (k10_relat_1(A_97, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(A_97))), inference(resolution, [status(thm)], [c_292, c_44])).
% 2.07/1.31  tff(c_339, plain, (k10_relat_1('#skF_6', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_30, c_336])).
% 2.07/1.31  tff(c_343, plain, $false, inference(negUnitSimplification, [status(thm)], [c_28, c_339])).
% 2.07/1.31  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.07/1.31  
% 2.07/1.31  Inference rules
% 2.07/1.31  ----------------------
% 2.07/1.31  #Ref     : 0
% 2.07/1.31  #Sup     : 62
% 2.07/1.31  #Fact    : 0
% 2.07/1.31  #Define  : 0
% 2.07/1.31  #Split   : 1
% 2.07/1.31  #Chain   : 0
% 2.07/1.31  #Close   : 0
% 2.07/1.31  
% 2.07/1.31  Ordering : KBO
% 2.07/1.31  
% 2.07/1.31  Simplification rules
% 2.07/1.31  ----------------------
% 2.07/1.31  #Subsume      : 10
% 2.07/1.31  #Demod        : 4
% 2.07/1.31  #Tautology    : 4
% 2.07/1.31  #SimpNegUnit  : 1
% 2.07/1.31  #BackRed      : 0
% 2.07/1.31  
% 2.07/1.31  #Partial instantiations: 0
% 2.07/1.31  #Strategies tried      : 1
% 2.07/1.31  
% 2.07/1.31  Timing (in seconds)
% 2.07/1.31  ----------------------
% 2.07/1.31  Preprocessing        : 0.29
% 2.07/1.31  Parsing              : 0.15
% 2.07/1.31  CNF conversion       : 0.03
% 2.07/1.31  Main loop            : 0.24
% 2.07/1.31  Inferencing          : 0.10
% 2.07/1.31  Reduction            : 0.05
% 2.07/1.31  Demodulation         : 0.04
% 2.07/1.31  BG Simplification    : 0.02
% 2.07/1.31  Subsumption          : 0.06
% 2.07/1.31  Abstraction          : 0.01
% 2.07/1.31  MUC search           : 0.00
% 2.07/1.31  Cooper               : 0.00
% 2.07/1.32  Total                : 0.55
% 2.07/1.32  Index Insertion      : 0.00
% 2.07/1.32  Index Deletion       : 0.00
% 2.07/1.32  Index Matching       : 0.00
% 2.07/1.32  BG Taut test         : 0.00
%------------------------------------------------------------------------------
