%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:01:18 EST 2020

% Result     : Theorem 2.40s
% Output     : CNFRefutation 2.40s
% Verified   : 
% Statistics : Number of formulae       :   38 (  39 expanded)
%              Number of leaves         :   23 (  24 expanded)
%              Depth                    :    8
%              Number of atoms          :   42 (  44 expanded)
%              Number of equality atoms :    8 (   9 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > v1_relat_1 > k4_tarski > k3_xboole_0 > k10_relat_1 > #nlpp > k2_relat_1 > k1_xboole_0 > #skF_4 > #skF_3 > #skF_2 > #skF_1

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

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_70,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => k10_relat_1(A,k1_xboole_0) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t171_relat_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_65,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k10_relat_1(C,B))
      <=> ? [D] :
            ( r2_hidden(D,k2_relat_1(C))
            & r2_hidden(k4_tarski(A,D),C)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t166_relat_1)).

tff(f_54,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_48,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_46,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_52,axiom,(
    ! [A] :
      ( r1_tarski(A,k1_xboole_0)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).

tff(c_26,plain,(
    k10_relat_1('#skF_4',k1_xboole_0) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_28,plain,(
    v1_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_110,plain,(
    ! [A_43,B_44,C_45] :
      ( r2_hidden('#skF_3'(A_43,B_44,C_45),B_44)
      | ~ r2_hidden(A_43,k10_relat_1(C_45,B_44))
      | ~ v1_relat_1(C_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_16,plain,(
    ! [A_13] : r1_xboole_0(A_13,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_12,plain,(
    ! [A_11] : k3_xboole_0(A_11,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_38,plain,(
    ! [A_23,B_24,C_25] :
      ( ~ r1_xboole_0(A_23,B_24)
      | ~ r2_hidden(C_25,k3_xboole_0(A_23,B_24)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_41,plain,(
    ! [A_11,C_25] :
      ( ~ r1_xboole_0(A_11,k1_xboole_0)
      | ~ r2_hidden(C_25,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_38])).

tff(c_43,plain,(
    ! [C_25] : ~ r2_hidden(C_25,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_41])).

tff(c_124,plain,(
    ! [A_46,C_47] :
      ( ~ r2_hidden(A_46,k10_relat_1(C_47,k1_xboole_0))
      | ~ v1_relat_1(C_47) ) ),
    inference(resolution,[status(thm)],[c_110,c_43])).

tff(c_135,plain,(
    ! [C_48,B_49] :
      ( ~ v1_relat_1(C_48)
      | r1_tarski(k10_relat_1(C_48,k1_xboole_0),B_49) ) ),
    inference(resolution,[status(thm)],[c_6,c_124])).

tff(c_14,plain,(
    ! [A_12] :
      ( k1_xboole_0 = A_12
      | ~ r1_tarski(A_12,k1_xboole_0) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_141,plain,(
    ! [C_50] :
      ( k10_relat_1(C_50,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(C_50) ) ),
    inference(resolution,[status(thm)],[c_135,c_14])).

tff(c_144,plain,(
    k10_relat_1('#skF_4',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_28,c_141])).

tff(c_148,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_144])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.01/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.19/0.34  % CPULimit   : 60
% 0.19/0.34  % DateTime   : Tue Dec  1 20:46:11 EST 2020
% 0.19/0.34  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.40/2.03  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.40/2.04  
% 2.40/2.04  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.40/2.04  %$ r2_hidden > r1_xboole_0 > r1_tarski > v1_relat_1 > k4_tarski > k3_xboole_0 > k10_relat_1 > #nlpp > k2_relat_1 > k1_xboole_0 > #skF_4 > #skF_3 > #skF_2 > #skF_1
% 2.40/2.04  
% 2.40/2.04  %Foreground sorts:
% 2.40/2.04  
% 2.40/2.04  
% 2.40/2.04  %Background operators:
% 2.40/2.04  
% 2.40/2.04  
% 2.40/2.04  %Foreground operators:
% 2.40/2.04  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.40/2.04  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.40/2.04  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.40/2.04  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.40/2.04  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.40/2.04  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.40/2.04  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.40/2.04  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.40/2.04  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 2.40/2.04  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.40/2.04  tff('#skF_4', type, '#skF_4': $i).
% 2.40/2.04  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 2.40/2.04  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.40/2.04  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.40/2.04  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.40/2.04  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.40/2.05  
% 2.40/2.06  tff(f_70, negated_conjecture, ~(![A]: (v1_relat_1(A) => (k10_relat_1(A, k1_xboole_0) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t171_relat_1)).
% 2.40/2.06  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 2.40/2.06  tff(f_65, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k10_relat_1(C, B)) <=> (?[D]: ((r2_hidden(D, k2_relat_1(C)) & r2_hidden(k4_tarski(A, D), C)) & r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t166_relat_1)).
% 2.40/2.06  tff(f_54, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 2.40/2.06  tff(f_48, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 2.40/2.06  tff(f_46, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 2.40/2.06  tff(f_52, axiom, (![A]: (r1_tarski(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_1)).
% 2.40/2.06  tff(c_26, plain, (k10_relat_1('#skF_4', k1_xboole_0)!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.40/2.06  tff(c_28, plain, (v1_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.40/2.06  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.40/2.06  tff(c_110, plain, (![A_43, B_44, C_45]: (r2_hidden('#skF_3'(A_43, B_44, C_45), B_44) | ~r2_hidden(A_43, k10_relat_1(C_45, B_44)) | ~v1_relat_1(C_45))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.40/2.06  tff(c_16, plain, (![A_13]: (r1_xboole_0(A_13, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.40/2.06  tff(c_12, plain, (![A_11]: (k3_xboole_0(A_11, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.40/2.06  tff(c_38, plain, (![A_23, B_24, C_25]: (~r1_xboole_0(A_23, B_24) | ~r2_hidden(C_25, k3_xboole_0(A_23, B_24)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.40/2.06  tff(c_41, plain, (![A_11, C_25]: (~r1_xboole_0(A_11, k1_xboole_0) | ~r2_hidden(C_25, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_12, c_38])).
% 2.40/2.06  tff(c_43, plain, (![C_25]: (~r2_hidden(C_25, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_41])).
% 2.40/2.06  tff(c_124, plain, (![A_46, C_47]: (~r2_hidden(A_46, k10_relat_1(C_47, k1_xboole_0)) | ~v1_relat_1(C_47))), inference(resolution, [status(thm)], [c_110, c_43])).
% 2.40/2.06  tff(c_135, plain, (![C_48, B_49]: (~v1_relat_1(C_48) | r1_tarski(k10_relat_1(C_48, k1_xboole_0), B_49))), inference(resolution, [status(thm)], [c_6, c_124])).
% 2.40/2.06  tff(c_14, plain, (![A_12]: (k1_xboole_0=A_12 | ~r1_tarski(A_12, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.40/2.06  tff(c_141, plain, (![C_50]: (k10_relat_1(C_50, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(C_50))), inference(resolution, [status(thm)], [c_135, c_14])).
% 2.40/2.06  tff(c_144, plain, (k10_relat_1('#skF_4', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_28, c_141])).
% 2.40/2.06  tff(c_148, plain, $false, inference(negUnitSimplification, [status(thm)], [c_26, c_144])).
% 2.40/2.06  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.40/2.06  
% 2.40/2.06  Inference rules
% 2.40/2.06  ----------------------
% 2.40/2.06  #Ref     : 0
% 2.40/2.06  #Sup     : 22
% 2.40/2.06  #Fact    : 0
% 2.40/2.06  #Define  : 0
% 2.40/2.06  #Split   : 0
% 2.40/2.06  #Chain   : 0
% 2.40/2.06  #Close   : 0
% 2.40/2.06  
% 2.40/2.06  Ordering : KBO
% 2.40/2.06  
% 2.40/2.06  Simplification rules
% 2.40/2.06  ----------------------
% 2.40/2.06  #Subsume      : 0
% 2.40/2.06  #Demod        : 5
% 2.40/2.06  #Tautology    : 8
% 2.40/2.06  #SimpNegUnit  : 2
% 2.40/2.06  #BackRed      : 0
% 2.40/2.06  
% 2.40/2.06  #Partial instantiations: 0
% 2.40/2.06  #Strategies tried      : 1
% 2.40/2.06  
% 2.40/2.06  Timing (in seconds)
% 2.40/2.06  ----------------------
% 2.40/2.07  Preprocessing        : 0.60
% 2.40/2.07  Parsing              : 0.35
% 2.40/2.07  CNF conversion       : 0.05
% 2.40/2.07  Main loop            : 0.36
% 2.40/2.07  Inferencing          : 0.17
% 2.40/2.08  Reduction            : 0.09
% 2.40/2.08  Demodulation         : 0.06
% 2.40/2.08  BG Simplification    : 0.02
% 2.40/2.08  Subsumption          : 0.06
% 2.40/2.08  Abstraction          : 0.02
% 2.40/2.08  MUC search           : 0.00
% 2.40/2.08  Cooper               : 0.00
% 2.40/2.08  Total                : 1.02
% 2.40/2.08  Index Insertion      : 0.00
% 2.40/2.08  Index Deletion       : 0.00
% 2.53/2.08  Index Matching       : 0.00
% 2.53/2.08  BG Taut test         : 0.00
%------------------------------------------------------------------------------
