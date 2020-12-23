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
% DateTime   : Thu Dec  3 09:57:33 EST 2020

% Result     : Theorem 1.99s
% Output     : CNFRefutation 1.99s
% Verified   : 
% Statistics : Number of formulae       :   40 (  41 expanded)
%              Number of leaves         :   27 (  28 expanded)
%              Depth                    :    7
%              Number of atoms          :   33 (  35 expanded)
%              Number of equality atoms :    5 (   6 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > r1_setfam_1 > v1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_4 > #skF_3 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r1_setfam_1,type,(
    r1_setfam_1: ( $i * $i ) > $o )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

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

tff(f_73,negated_conjecture,(
    ~ ! [A] :
        ( r1_setfam_1(A,k1_xboole_0)
       => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_setfam_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_68,axiom,(
    ! [A,B] :
      ( r1_setfam_1(A,B)
    <=> ! [C] :
          ~ ( r2_hidden(C,A)
            & ! [D] :
                ~ ( r2_hidden(D,B)
                  & r1_tarski(C,D) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_setfam_1)).

tff(f_37,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_56,axiom,(
    ! [A,B] :
      ~ ( r1_xboole_0(k1_tarski(A),B)
        & r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l24_zfmisc_1)).

tff(f_35,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(c_34,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_36,plain,(
    r1_setfam_1('#skF_4',k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_117,plain,(
    ! [A_78,B_79,C_80] :
      ( r2_hidden('#skF_3'(A_78,B_79,C_80),B_79)
      | ~ r2_hidden(C_80,A_78)
      | ~ r1_setfam_1(A_78,B_79) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_8,plain,(
    ! [A_6] : r1_xboole_0(A_6,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_63,plain,(
    ! [A_57,B_58] :
      ( ~ r2_hidden(A_57,B_58)
      | ~ r1_xboole_0(k1_tarski(A_57),B_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_68,plain,(
    ! [A_57] : ~ r2_hidden(A_57,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_8,c_63])).

tff(c_136,plain,(
    ! [C_86,A_87] :
      ( ~ r2_hidden(C_86,A_87)
      | ~ r1_setfam_1(A_87,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_117,c_68])).

tff(c_149,plain,(
    ! [A_88] :
      ( ~ r1_setfam_1(A_88,k1_xboole_0)
      | v1_xboole_0(A_88) ) ),
    inference(resolution,[status(thm)],[c_4,c_136])).

tff(c_164,plain,(
    v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_36,c_149])).

tff(c_6,plain,(
    ! [A_5] :
      ( k1_xboole_0 = A_5
      | ~ v1_xboole_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_167,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_164,c_6])).

tff(c_171,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_167])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n020.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 11:49:37 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.99/1.19  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.99/1.19  
% 1.99/1.19  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.99/1.19  %$ r2_hidden > r1_xboole_0 > r1_tarski > r1_setfam_1 > v1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_4 > #skF_3 > #skF_2
% 1.99/1.19  
% 1.99/1.19  %Foreground sorts:
% 1.99/1.19  
% 1.99/1.19  
% 1.99/1.19  %Background operators:
% 1.99/1.19  
% 1.99/1.19  
% 1.99/1.19  %Foreground operators:
% 1.99/1.19  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.99/1.19  tff(r1_setfam_1, type, r1_setfam_1: ($i * $i) > $o).
% 1.99/1.19  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.99/1.19  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.99/1.19  tff('#skF_1', type, '#skF_1': $i > $i).
% 1.99/1.19  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.99/1.19  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 1.99/1.19  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.99/1.19  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.99/1.19  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.99/1.19  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.99/1.19  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.99/1.19  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 1.99/1.19  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 1.99/1.19  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.99/1.19  tff('#skF_4', type, '#skF_4': $i).
% 1.99/1.19  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 1.99/1.19  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.99/1.19  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 1.99/1.19  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 1.99/1.19  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.99/1.19  
% 1.99/1.20  tff(f_73, negated_conjecture, ~(![A]: (r1_setfam_1(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t21_setfam_1)).
% 1.99/1.20  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 1.99/1.20  tff(f_68, axiom, (![A, B]: (r1_setfam_1(A, B) <=> (![C]: ~(r2_hidden(C, A) & (![D]: ~(r2_hidden(D, B) & r1_tarski(C, D))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_setfam_1)).
% 1.99/1.20  tff(f_37, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 1.99/1.20  tff(f_56, axiom, (![A, B]: ~(r1_xboole_0(k1_tarski(A), B) & r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l24_zfmisc_1)).
% 1.99/1.20  tff(f_35, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 1.99/1.20  tff(c_34, plain, (k1_xboole_0!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_73])).
% 1.99/1.20  tff(c_36, plain, (r1_setfam_1('#skF_4', k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_73])).
% 1.99/1.20  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.99/1.20  tff(c_117, plain, (![A_78, B_79, C_80]: (r2_hidden('#skF_3'(A_78, B_79, C_80), B_79) | ~r2_hidden(C_80, A_78) | ~r1_setfam_1(A_78, B_79))), inference(cnfTransformation, [status(thm)], [f_68])).
% 1.99/1.20  tff(c_8, plain, (![A_6]: (r1_xboole_0(A_6, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.99/1.20  tff(c_63, plain, (![A_57, B_58]: (~r2_hidden(A_57, B_58) | ~r1_xboole_0(k1_tarski(A_57), B_58))), inference(cnfTransformation, [status(thm)], [f_56])).
% 1.99/1.20  tff(c_68, plain, (![A_57]: (~r2_hidden(A_57, k1_xboole_0))), inference(resolution, [status(thm)], [c_8, c_63])).
% 1.99/1.20  tff(c_136, plain, (![C_86, A_87]: (~r2_hidden(C_86, A_87) | ~r1_setfam_1(A_87, k1_xboole_0))), inference(resolution, [status(thm)], [c_117, c_68])).
% 1.99/1.20  tff(c_149, plain, (![A_88]: (~r1_setfam_1(A_88, k1_xboole_0) | v1_xboole_0(A_88))), inference(resolution, [status(thm)], [c_4, c_136])).
% 1.99/1.20  tff(c_164, plain, (v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_36, c_149])).
% 1.99/1.20  tff(c_6, plain, (![A_5]: (k1_xboole_0=A_5 | ~v1_xboole_0(A_5))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.99/1.20  tff(c_167, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_164, c_6])).
% 1.99/1.20  tff(c_171, plain, $false, inference(negUnitSimplification, [status(thm)], [c_34, c_167])).
% 1.99/1.20  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.99/1.20  
% 1.99/1.20  Inference rules
% 1.99/1.20  ----------------------
% 1.99/1.20  #Ref     : 0
% 1.99/1.20  #Sup     : 26
% 1.99/1.20  #Fact    : 0
% 1.99/1.20  #Define  : 0
% 1.99/1.20  #Split   : 0
% 1.99/1.20  #Chain   : 0
% 1.99/1.20  #Close   : 0
% 1.99/1.20  
% 1.99/1.20  Ordering : KBO
% 1.99/1.20  
% 1.99/1.20  Simplification rules
% 1.99/1.20  ----------------------
% 1.99/1.20  #Subsume      : 0
% 1.99/1.20  #Demod        : 1
% 1.99/1.20  #Tautology    : 14
% 1.99/1.20  #SimpNegUnit  : 1
% 1.99/1.20  #BackRed      : 0
% 1.99/1.20  
% 1.99/1.20  #Partial instantiations: 0
% 1.99/1.20  #Strategies tried      : 1
% 1.99/1.20  
% 1.99/1.20  Timing (in seconds)
% 1.99/1.20  ----------------------
% 1.99/1.20  Preprocessing        : 0.32
% 1.99/1.20  Parsing              : 0.17
% 1.99/1.20  CNF conversion       : 0.02
% 1.99/1.20  Main loop            : 0.14
% 1.99/1.20  Inferencing          : 0.06
% 1.99/1.20  Reduction            : 0.04
% 1.99/1.20  Demodulation         : 0.03
% 1.99/1.20  BG Simplification    : 0.02
% 1.99/1.20  Subsumption          : 0.02
% 1.99/1.20  Abstraction          : 0.01
% 1.99/1.20  MUC search           : 0.00
% 1.99/1.20  Cooper               : 0.00
% 1.99/1.20  Total                : 0.49
% 1.99/1.20  Index Insertion      : 0.00
% 1.99/1.20  Index Deletion       : 0.00
% 1.99/1.20  Index Matching       : 0.00
% 1.99/1.21  BG Taut test         : 0.00
%------------------------------------------------------------------------------
