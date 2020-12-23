%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:57:36 EST 2020

% Result     : Theorem 2.05s
% Output     : CNFRefutation 2.05s
% Verified   : 
% Statistics : Number of formulae       :   43 (  44 expanded)
%              Number of leaves         :   26 (  27 expanded)
%              Depth                    :    8
%              Number of atoms          :   44 (  46 expanded)
%              Number of equality atoms :    9 (  10 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > r1_setfam_1 > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_tarski > #nlpp > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_4 > #skF_3 > #skF_5 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r1_setfam_1,type,(
    r1_setfam_1: ( $i * $i ) > $o )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_82,negated_conjecture,(
    ~ ! [A] :
        ( r1_setfam_1(A,k1_xboole_0)
       => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_setfam_1)).

tff(f_51,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_75,axiom,(
    ! [A,B] :
      ( r1_setfam_1(A,B)
    <=> ! [C] :
          ~ ( r2_hidden(C,A)
            & ! [D] :
                ~ ( r2_hidden(D,B)
                  & r1_tarski(C,D) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_setfam_1)).

tff(f_59,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_53,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_57,axiom,(
    ! [A] :
      ( r1_tarski(A,k1_xboole_0)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

tff(c_30,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_32,plain,(
    r1_setfam_1('#skF_5',k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_8,plain,(
    ! [A_8] :
      ( r2_hidden('#skF_2'(A_8),A_8)
      | k1_xboole_0 = A_8 ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_197,plain,(
    ! [A_71,B_72,C_73] :
      ( r2_hidden('#skF_4'(A_71,B_72,C_73),B_72)
      | ~ r2_hidden(C_73,A_71)
      | ~ r1_setfam_1(A_71,B_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_14,plain,(
    ! [A_13] : r1_xboole_0(A_13,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_41,plain,(
    ! [B_37,A_38] :
      ( r1_xboole_0(B_37,A_38)
      | ~ r1_xboole_0(A_38,B_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_44,plain,(
    ! [A_13] : r1_xboole_0(k1_xboole_0,A_13) ),
    inference(resolution,[status(thm)],[c_14,c_41])).

tff(c_35,plain,(
    ! [A_35,B_36] : r1_tarski(k3_xboole_0(A_35,B_36),A_35) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_12,plain,(
    ! [A_12] :
      ( k1_xboole_0 = A_12
      | ~ r1_tarski(A_12,k1_xboole_0) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_40,plain,(
    ! [B_36] : k3_xboole_0(k1_xboole_0,B_36) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_35,c_12])).

tff(c_85,plain,(
    ! [A_48,B_49,C_50] :
      ( ~ r1_xboole_0(A_48,B_49)
      | ~ r2_hidden(C_50,k3_xboole_0(A_48,B_49)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_96,plain,(
    ! [B_36,C_50] :
      ( ~ r1_xboole_0(k1_xboole_0,B_36)
      | ~ r2_hidden(C_50,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_85])).

tff(c_100,plain,(
    ! [C_50] : ~ r2_hidden(C_50,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_96])).

tff(c_221,plain,(
    ! [C_78,A_79] :
      ( ~ r2_hidden(C_78,A_79)
      | ~ r1_setfam_1(A_79,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_197,c_100])).

tff(c_238,plain,(
    ! [A_80] :
      ( ~ r1_setfam_1(A_80,k1_xboole_0)
      | k1_xboole_0 = A_80 ) ),
    inference(resolution,[status(thm)],[c_8,c_221])).

tff(c_249,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_32,c_238])).

tff(c_256,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_249])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.36  % Computer   : n022.cluster.edu
% 0.15/0.36  % Model      : x86_64 x86_64
% 0.15/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.36  % Memory     : 8042.1875MB
% 0.15/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.36  % CPULimit   : 60
% 0.15/0.36  % DateTime   : Tue Dec  1 11:39:55 EST 2020
% 0.15/0.36  % CPUTime    : 
% 0.15/0.37  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.05/1.25  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.05/1.25  
% 2.05/1.25  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.05/1.25  %$ r2_hidden > r1_xboole_0 > r1_tarski > r1_setfam_1 > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_tarski > #nlpp > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_4 > #skF_3 > #skF_5 > #skF_1
% 2.05/1.25  
% 2.05/1.25  %Foreground sorts:
% 2.05/1.25  
% 2.05/1.25  
% 2.05/1.25  %Background operators:
% 2.05/1.25  
% 2.05/1.25  
% 2.05/1.25  %Foreground operators:
% 2.05/1.25  tff('#skF_2', type, '#skF_2': $i > $i).
% 2.05/1.25  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.05/1.25  tff(r1_setfam_1, type, r1_setfam_1: ($i * $i) > $o).
% 2.05/1.25  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.05/1.25  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.05/1.25  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 2.05/1.25  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.05/1.25  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.05/1.25  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.05/1.25  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.05/1.25  tff('#skF_5', type, '#skF_5': $i).
% 2.05/1.25  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.05/1.25  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.05/1.25  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.05/1.25  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.05/1.25  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.05/1.25  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.05/1.25  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.05/1.25  
% 2.05/1.26  tff(f_82, negated_conjecture, ~(![A]: (r1_setfam_1(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t21_setfam_1)).
% 2.05/1.26  tff(f_51, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 2.05/1.26  tff(f_75, axiom, (![A, B]: (r1_setfam_1(A, B) <=> (![C]: ~(r2_hidden(C, A) & (![D]: ~(r2_hidden(D, B) & r1_tarski(C, D))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_setfam_1)).
% 2.05/1.26  tff(f_59, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 2.05/1.26  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 2.05/1.26  tff(f_53, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 2.05/1.26  tff(f_57, axiom, (![A]: (r1_tarski(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_1)).
% 2.05/1.26  tff(f_43, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 2.05/1.26  tff(c_30, plain, (k1_xboole_0!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.05/1.26  tff(c_32, plain, (r1_setfam_1('#skF_5', k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.05/1.26  tff(c_8, plain, (![A_8]: (r2_hidden('#skF_2'(A_8), A_8) | k1_xboole_0=A_8)), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.05/1.26  tff(c_197, plain, (![A_71, B_72, C_73]: (r2_hidden('#skF_4'(A_71, B_72, C_73), B_72) | ~r2_hidden(C_73, A_71) | ~r1_setfam_1(A_71, B_72))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.05/1.26  tff(c_14, plain, (![A_13]: (r1_xboole_0(A_13, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.05/1.26  tff(c_41, plain, (![B_37, A_38]: (r1_xboole_0(B_37, A_38) | ~r1_xboole_0(A_38, B_37))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.05/1.26  tff(c_44, plain, (![A_13]: (r1_xboole_0(k1_xboole_0, A_13))), inference(resolution, [status(thm)], [c_14, c_41])).
% 2.05/1.26  tff(c_35, plain, (![A_35, B_36]: (r1_tarski(k3_xboole_0(A_35, B_36), A_35))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.05/1.26  tff(c_12, plain, (![A_12]: (k1_xboole_0=A_12 | ~r1_tarski(A_12, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.05/1.26  tff(c_40, plain, (![B_36]: (k3_xboole_0(k1_xboole_0, B_36)=k1_xboole_0)), inference(resolution, [status(thm)], [c_35, c_12])).
% 2.05/1.26  tff(c_85, plain, (![A_48, B_49, C_50]: (~r1_xboole_0(A_48, B_49) | ~r2_hidden(C_50, k3_xboole_0(A_48, B_49)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.05/1.26  tff(c_96, plain, (![B_36, C_50]: (~r1_xboole_0(k1_xboole_0, B_36) | ~r2_hidden(C_50, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_40, c_85])).
% 2.05/1.26  tff(c_100, plain, (![C_50]: (~r2_hidden(C_50, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_96])).
% 2.05/1.26  tff(c_221, plain, (![C_78, A_79]: (~r2_hidden(C_78, A_79) | ~r1_setfam_1(A_79, k1_xboole_0))), inference(resolution, [status(thm)], [c_197, c_100])).
% 2.05/1.26  tff(c_238, plain, (![A_80]: (~r1_setfam_1(A_80, k1_xboole_0) | k1_xboole_0=A_80)), inference(resolution, [status(thm)], [c_8, c_221])).
% 2.05/1.26  tff(c_249, plain, (k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_32, c_238])).
% 2.05/1.26  tff(c_256, plain, $false, inference(negUnitSimplification, [status(thm)], [c_30, c_249])).
% 2.05/1.26  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.05/1.26  
% 2.05/1.26  Inference rules
% 2.05/1.26  ----------------------
% 2.05/1.26  #Ref     : 0
% 2.05/1.26  #Sup     : 46
% 2.05/1.26  #Fact    : 0
% 2.05/1.26  #Define  : 0
% 2.05/1.26  #Split   : 0
% 2.05/1.26  #Chain   : 0
% 2.05/1.26  #Close   : 0
% 2.05/1.26  
% 2.05/1.26  Ordering : KBO
% 2.05/1.26  
% 2.05/1.26  Simplification rules
% 2.05/1.26  ----------------------
% 2.05/1.26  #Subsume      : 2
% 2.05/1.26  #Demod        : 11
% 2.05/1.26  #Tautology    : 24
% 2.05/1.26  #SimpNegUnit  : 3
% 2.05/1.26  #BackRed      : 0
% 2.05/1.26  
% 2.05/1.26  #Partial instantiations: 0
% 2.05/1.26  #Strategies tried      : 1
% 2.05/1.26  
% 2.05/1.26  Timing (in seconds)
% 2.05/1.26  ----------------------
% 2.05/1.27  Preprocessing        : 0.31
% 2.05/1.27  Parsing              : 0.17
% 2.05/1.27  CNF conversion       : 0.02
% 2.05/1.27  Main loop            : 0.17
% 2.05/1.27  Inferencing          : 0.07
% 2.05/1.27  Reduction            : 0.05
% 2.05/1.27  Demodulation         : 0.03
% 2.05/1.27  BG Simplification    : 0.01
% 2.05/1.27  Subsumption          : 0.02
% 2.05/1.27  Abstraction          : 0.01
% 2.05/1.27  MUC search           : 0.00
% 2.05/1.27  Cooper               : 0.00
% 2.05/1.27  Total                : 0.50
% 2.05/1.27  Index Insertion      : 0.00
% 2.05/1.27  Index Deletion       : 0.00
% 2.05/1.27  Index Matching       : 0.00
% 2.05/1.27  BG Taut test         : 0.00
%------------------------------------------------------------------------------
