%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:01:15 EST 2020

% Result     : Theorem 2.19s
% Output     : CNFRefutation 2.60s
% Verified   : 
% Statistics : Number of formulae       :   37 (  43 expanded)
%              Number of leaves         :   27 (  30 expanded)
%              Depth                    :    6
%              Number of atoms          :   27 (  36 expanded)
%              Number of equality atoms :   10 (  14 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k10_relat_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_6 > #skF_1 > #skF_7 > #skF_2 > #skF_4 > #skF_3 > #skF_5

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_92,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => k10_relat_1(A,k1_xboole_0) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t171_relat_1)).

tff(f_66,axiom,(
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
    ! [A] : k4_xboole_0(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).

tff(f_38,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k4_xboole_0(B,k1_tarski(C)))
    <=> ( r2_hidden(A,B)
        & A != C ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_zfmisc_1)).

tff(c_52,plain,(
    k10_relat_1('#skF_7',k1_xboole_0) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_54,plain,(
    v1_relat_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_448,plain,(
    ! [A_130,B_131,C_132] :
      ( r2_hidden('#skF_2'(A_130,B_131,C_132),B_131)
      | r2_hidden('#skF_3'(A_130,B_131,C_132),C_132)
      | k10_relat_1(A_130,B_131) = C_132
      | ~ v1_relat_1(A_130) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_6,plain,(
    ! [A_4] : k4_xboole_0(k1_xboole_0,A_4) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_72,plain,(
    ! [C_80,B_81] : ~ r2_hidden(C_80,k4_xboole_0(B_81,k1_tarski(C_80))) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_75,plain,(
    ! [C_80] : ~ r2_hidden(C_80,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_72])).

tff(c_499,plain,(
    ! [A_135,C_136] :
      ( r2_hidden('#skF_3'(A_135,k1_xboole_0,C_136),C_136)
      | k10_relat_1(A_135,k1_xboole_0) = C_136
      | ~ v1_relat_1(A_135) ) ),
    inference(resolution,[status(thm)],[c_448,c_75])).

tff(c_523,plain,(
    ! [A_137] :
      ( k10_relat_1(A_137,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(A_137) ) ),
    inference(resolution,[status(thm)],[c_499,c_75])).

tff(c_529,plain,(
    k10_relat_1('#skF_7',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_54,c_523])).

tff(c_535,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_529])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n002.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 15:10:21 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.19/1.33  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.19/1.33  
% 2.19/1.33  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.19/1.33  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k10_relat_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_6 > #skF_1 > #skF_7 > #skF_2 > #skF_4 > #skF_3 > #skF_5
% 2.19/1.33  
% 2.19/1.33  %Foreground sorts:
% 2.19/1.33  
% 2.19/1.33  
% 2.19/1.33  %Background operators:
% 2.19/1.33  
% 2.19/1.33  
% 2.19/1.33  %Foreground operators:
% 2.19/1.33  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 2.19/1.33  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.19/1.33  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.19/1.33  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.19/1.33  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.19/1.33  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.19/1.33  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.19/1.33  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.19/1.33  tff('#skF_7', type, '#skF_7': $i).
% 2.19/1.33  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.19/1.33  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.19/1.33  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.19/1.33  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.19/1.33  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i) > $i).
% 2.19/1.33  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.19/1.34  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 2.19/1.34  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.19/1.34  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 2.19/1.34  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.19/1.34  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.19/1.34  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 2.19/1.34  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.19/1.34  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.19/1.34  
% 2.60/1.34  tff(f_92, negated_conjecture, ~(![A]: (v1_relat_1(A) => (k10_relat_1(A, k1_xboole_0) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t171_relat_1)).
% 2.60/1.34  tff(f_66, axiom, (![A]: (v1_relat_1(A) => (![B, C]: ((C = k10_relat_1(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (?[E]: (r2_hidden(k4_tarski(D, E), A) & r2_hidden(E, B))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d14_relat_1)).
% 2.60/1.34  tff(f_31, axiom, (![A]: (k4_xboole_0(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_boole)).
% 2.60/1.34  tff(f_38, axiom, (![A, B, C]: (r2_hidden(A, k4_xboole_0(B, k1_tarski(C))) <=> (r2_hidden(A, B) & ~(A = C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_zfmisc_1)).
% 2.60/1.34  tff(c_52, plain, (k10_relat_1('#skF_7', k1_xboole_0)!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.60/1.34  tff(c_54, plain, (v1_relat_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.60/1.34  tff(c_448, plain, (![A_130, B_131, C_132]: (r2_hidden('#skF_2'(A_130, B_131, C_132), B_131) | r2_hidden('#skF_3'(A_130, B_131, C_132), C_132) | k10_relat_1(A_130, B_131)=C_132 | ~v1_relat_1(A_130))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.60/1.34  tff(c_6, plain, (![A_4]: (k4_xboole_0(k1_xboole_0, A_4)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.60/1.34  tff(c_72, plain, (![C_80, B_81]: (~r2_hidden(C_80, k4_xboole_0(B_81, k1_tarski(C_80))))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.60/1.34  tff(c_75, plain, (![C_80]: (~r2_hidden(C_80, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_6, c_72])).
% 2.60/1.34  tff(c_499, plain, (![A_135, C_136]: (r2_hidden('#skF_3'(A_135, k1_xboole_0, C_136), C_136) | k10_relat_1(A_135, k1_xboole_0)=C_136 | ~v1_relat_1(A_135))), inference(resolution, [status(thm)], [c_448, c_75])).
% 2.60/1.34  tff(c_523, plain, (![A_137]: (k10_relat_1(A_137, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(A_137))), inference(resolution, [status(thm)], [c_499, c_75])).
% 2.60/1.34  tff(c_529, plain, (k10_relat_1('#skF_7', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_54, c_523])).
% 2.60/1.34  tff(c_535, plain, $false, inference(negUnitSimplification, [status(thm)], [c_52, c_529])).
% 2.60/1.34  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.60/1.34  
% 2.60/1.34  Inference rules
% 2.60/1.34  ----------------------
% 2.60/1.34  #Ref     : 0
% 2.60/1.34  #Sup     : 104
% 2.60/1.34  #Fact    : 0
% 2.60/1.34  #Define  : 0
% 2.60/1.34  #Split   : 1
% 2.60/1.34  #Chain   : 0
% 2.60/1.34  #Close   : 0
% 2.60/1.34  
% 2.60/1.34  Ordering : KBO
% 2.60/1.34  
% 2.60/1.34  Simplification rules
% 2.60/1.34  ----------------------
% 2.60/1.34  #Subsume      : 10
% 2.60/1.34  #Demod        : 61
% 2.60/1.34  #Tautology    : 54
% 2.60/1.34  #SimpNegUnit  : 6
% 2.60/1.34  #BackRed      : 1
% 2.60/1.34  
% 2.60/1.34  #Partial instantiations: 0
% 2.60/1.34  #Strategies tried      : 1
% 2.60/1.34  
% 2.60/1.34  Timing (in seconds)
% 2.60/1.34  ----------------------
% 2.60/1.35  Preprocessing        : 0.32
% 2.60/1.35  Parsing              : 0.17
% 2.60/1.35  CNF conversion       : 0.03
% 2.60/1.35  Main loop            : 0.27
% 2.60/1.35  Inferencing          : 0.10
% 2.60/1.35  Reduction            : 0.08
% 2.60/1.35  Demodulation         : 0.06
% 2.60/1.35  BG Simplification    : 0.02
% 2.60/1.35  Subsumption          : 0.04
% 2.60/1.35  Abstraction          : 0.01
% 2.60/1.35  MUC search           : 0.00
% 2.60/1.35  Cooper               : 0.00
% 2.60/1.35  Total                : 0.61
% 2.60/1.35  Index Insertion      : 0.00
% 2.60/1.35  Index Deletion       : 0.00
% 2.60/1.35  Index Matching       : 0.00
% 2.60/1.35  BG Taut test         : 0.00
%------------------------------------------------------------------------------
