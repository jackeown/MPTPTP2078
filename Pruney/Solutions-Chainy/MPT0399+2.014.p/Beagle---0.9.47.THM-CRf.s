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
% DateTime   : Thu Dec  3 09:57:33 EST 2020

% Result     : Theorem 2.37s
% Output     : CNFRefutation 2.37s
% Verified   : 
% Statistics : Number of formulae       :   39 (  40 expanded)
%              Number of leaves         :   26 (  27 expanded)
%              Depth                    :    7
%              Number of atoms          :   33 (  35 expanded)
%              Number of equality atoms :    5 (   6 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > r1_setfam_1 > v1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_tarski > #nlpp > k1_xboole_0 > #skF_1 > #skF_4 > #skF_3 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r1_setfam_1,type,(
    r1_setfam_1: ( $i * $i ) > $o )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(f_71,negated_conjecture,(
    ~ ! [A] :
        ( r1_setfam_1(A,k1_xboole_0)
       => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_setfam_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_66,axiom,(
    ! [A,B] :
      ( r1_setfam_1(A,B)
    <=> ! [C] :
          ~ ( r2_hidden(C,A)
            & ! [D] :
                ~ ( r2_hidden(D,B)
                  & r1_tarski(C,D) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_setfam_1)).

tff(f_37,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_54,axiom,(
    ! [A,B,C] :
      ~ ( r1_xboole_0(k2_tarski(A,B),C)
        & r2_hidden(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_zfmisc_1)).

tff(f_35,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(c_32,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_34,plain,(
    r1_setfam_1('#skF_4',k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_106,plain,(
    ! [A_78,B_79,C_80] :
      ( r2_hidden('#skF_3'(A_78,B_79,C_80),B_79)
      | ~ r2_hidden(C_80,A_78)
      | ~ r1_setfam_1(A_78,B_79) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_8,plain,(
    ! [A_6] : r1_xboole_0(A_6,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_52,plain,(
    ! [A_56,C_57,B_58] :
      ( ~ r2_hidden(A_56,C_57)
      | ~ r1_xboole_0(k2_tarski(A_56,B_58),C_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_57,plain,(
    ! [A_56] : ~ r2_hidden(A_56,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_8,c_52])).

tff(c_116,plain,(
    ! [C_81,A_82] :
      ( ~ r2_hidden(C_81,A_82)
      | ~ r1_setfam_1(A_82,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_106,c_57])).

tff(c_138,plain,(
    ! [A_88] :
      ( ~ r1_setfam_1(A_88,k1_xboole_0)
      | v1_xboole_0(A_88) ) ),
    inference(resolution,[status(thm)],[c_4,c_116])).

tff(c_153,plain,(
    v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_34,c_138])).

tff(c_6,plain,(
    ! [A_5] :
      ( k1_xboole_0 = A_5
      | ~ v1_xboole_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_156,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_153,c_6])).

tff(c_160,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_156])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n008.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 15:58:45 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.37/1.54  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.37/1.54  
% 2.37/1.54  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.37/1.54  %$ r2_hidden > r1_xboole_0 > r1_tarski > r1_setfam_1 > v1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_tarski > #nlpp > k1_xboole_0 > #skF_1 > #skF_4 > #skF_3 > #skF_2
% 2.37/1.54  
% 2.37/1.54  %Foreground sorts:
% 2.37/1.54  
% 2.37/1.54  
% 2.37/1.54  %Background operators:
% 2.37/1.54  
% 2.37/1.54  
% 2.37/1.54  %Foreground operators:
% 2.37/1.54  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.37/1.54  tff(r1_setfam_1, type, r1_setfam_1: ($i * $i) > $o).
% 2.37/1.54  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.37/1.54  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.37/1.54  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.37/1.54  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.37/1.54  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.37/1.54  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.37/1.54  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.37/1.54  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.37/1.54  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.37/1.54  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.37/1.54  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.37/1.54  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.37/1.54  tff('#skF_4', type, '#skF_4': $i).
% 2.37/1.54  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 2.37/1.54  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.37/1.54  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.37/1.54  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.37/1.54  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.37/1.54  
% 2.37/1.56  tff(f_71, negated_conjecture, ~(![A]: (r1_setfam_1(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t21_setfam_1)).
% 2.37/1.56  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 2.37/1.56  tff(f_66, axiom, (![A, B]: (r1_setfam_1(A, B) <=> (![C]: ~(r2_hidden(C, A) & (![D]: ~(r2_hidden(D, B) & r1_tarski(C, D))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_setfam_1)).
% 2.37/1.56  tff(f_37, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 2.37/1.56  tff(f_54, axiom, (![A, B, C]: ~(r1_xboole_0(k2_tarski(A, B), C) & r2_hidden(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_zfmisc_1)).
% 2.37/1.56  tff(f_35, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 2.37/1.56  tff(c_32, plain, (k1_xboole_0!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.37/1.56  tff(c_34, plain, (r1_setfam_1('#skF_4', k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.37/1.56  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.37/1.56  tff(c_106, plain, (![A_78, B_79, C_80]: (r2_hidden('#skF_3'(A_78, B_79, C_80), B_79) | ~r2_hidden(C_80, A_78) | ~r1_setfam_1(A_78, B_79))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.37/1.56  tff(c_8, plain, (![A_6]: (r1_xboole_0(A_6, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.37/1.56  tff(c_52, plain, (![A_56, C_57, B_58]: (~r2_hidden(A_56, C_57) | ~r1_xboole_0(k2_tarski(A_56, B_58), C_57))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.37/1.56  tff(c_57, plain, (![A_56]: (~r2_hidden(A_56, k1_xboole_0))), inference(resolution, [status(thm)], [c_8, c_52])).
% 2.37/1.56  tff(c_116, plain, (![C_81, A_82]: (~r2_hidden(C_81, A_82) | ~r1_setfam_1(A_82, k1_xboole_0))), inference(resolution, [status(thm)], [c_106, c_57])).
% 2.37/1.56  tff(c_138, plain, (![A_88]: (~r1_setfam_1(A_88, k1_xboole_0) | v1_xboole_0(A_88))), inference(resolution, [status(thm)], [c_4, c_116])).
% 2.37/1.56  tff(c_153, plain, (v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_34, c_138])).
% 2.37/1.56  tff(c_6, plain, (![A_5]: (k1_xboole_0=A_5 | ~v1_xboole_0(A_5))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.37/1.56  tff(c_156, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_153, c_6])).
% 2.37/1.56  tff(c_160, plain, $false, inference(negUnitSimplification, [status(thm)], [c_32, c_156])).
% 2.37/1.56  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.37/1.56  
% 2.37/1.56  Inference rules
% 2.37/1.56  ----------------------
% 2.37/1.56  #Ref     : 0
% 2.37/1.56  #Sup     : 24
% 2.37/1.56  #Fact    : 0
% 2.37/1.56  #Define  : 0
% 2.37/1.56  #Split   : 0
% 2.37/1.56  #Chain   : 0
% 2.37/1.56  #Close   : 0
% 2.37/1.56  
% 2.37/1.56  Ordering : KBO
% 2.37/1.56  
% 2.37/1.56  Simplification rules
% 2.37/1.56  ----------------------
% 2.37/1.56  #Subsume      : 0
% 2.37/1.56  #Demod        : 1
% 2.37/1.56  #Tautology    : 12
% 2.37/1.56  #SimpNegUnit  : 1
% 2.37/1.56  #BackRed      : 0
% 2.37/1.56  
% 2.37/1.56  #Partial instantiations: 0
% 2.37/1.56  #Strategies tried      : 1
% 2.37/1.56  
% 2.37/1.56  Timing (in seconds)
% 2.37/1.56  ----------------------
% 2.37/1.56  Preprocessing        : 0.49
% 2.37/1.56  Parsing              : 0.25
% 2.37/1.56  CNF conversion       : 0.04
% 2.37/1.56  Main loop            : 0.22
% 2.37/1.56  Inferencing          : 0.10
% 2.37/1.56  Reduction            : 0.06
% 2.37/1.56  Demodulation         : 0.04
% 2.37/1.56  BG Simplification    : 0.03
% 2.37/1.56  Subsumption          : 0.03
% 2.37/1.56  Abstraction          : 0.01
% 2.37/1.56  MUC search           : 0.00
% 2.37/1.56  Cooper               : 0.00
% 2.37/1.56  Total                : 0.74
% 2.37/1.56  Index Insertion      : 0.00
% 2.37/1.56  Index Deletion       : 0.00
% 2.37/1.56  Index Matching       : 0.00
% 2.37/1.56  BG Taut test         : 0.00
%------------------------------------------------------------------------------
