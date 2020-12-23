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
% DateTime   : Thu Dec  3 09:57:37 EST 2020

% Result     : Theorem 1.78s
% Output     : CNFRefutation 1.88s
% Verified   : 
% Statistics : Number of formulae       :   29 (  30 expanded)
%              Number of leaves         :   18 (  19 expanded)
%              Depth                    :    6
%              Number of atoms          :   29 (  31 expanded)
%              Number of equality atoms :   10 (  11 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > r1_setfam_1 > k4_xboole_0 > k2_tarski > #nlpp > k1_xboole_0 > #skF_1 > #skF_4 > #skF_3 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r1_setfam_1,type,(
    r1_setfam_1: ( $i * $i ) > $o )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

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

tff(f_60,negated_conjecture,(
    ~ ! [A] :
        ( r1_setfam_1(A,k1_xboole_0)
       => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_setfam_1)).

tff(f_33,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_55,axiom,(
    ! [A,B] :
      ( r1_setfam_1(A,B)
    <=> ! [C] :
          ~ ( r2_hidden(C,A)
            & ! [D] :
                ~ ( r2_hidden(D,B)
                  & r1_tarski(C,D) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_setfam_1)).

tff(f_35,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( k4_xboole_0(k2_tarski(A,B),C) = k2_tarski(A,B)
    <=> ( ~ r2_hidden(A,C)
        & ~ r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_zfmisc_1)).

tff(c_20,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_22,plain,(
    r1_setfam_1('#skF_4',k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_2,plain,(
    ! [A_1] :
      ( r2_hidden('#skF_1'(A_1),A_1)
      | k1_xboole_0 = A_1 ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_66,plain,(
    ! [A_37,B_38,C_39] :
      ( r2_hidden('#skF_3'(A_37,B_38,C_39),B_38)
      | ~ r2_hidden(C_39,A_37)
      | ~ r1_setfam_1(A_37,B_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_4,plain,(
    ! [A_3] : k4_xboole_0(A_3,k1_xboole_0) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_35,plain,(
    ! [A_26,C_27,B_28] :
      ( ~ r2_hidden(A_26,C_27)
      | k4_xboole_0(k2_tarski(A_26,B_28),C_27) != k2_tarski(A_26,B_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_40,plain,(
    ! [A_26] : ~ r2_hidden(A_26,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_35])).

tff(c_72,plain,(
    ! [C_40,A_41] :
      ( ~ r2_hidden(C_40,A_41)
      | ~ r1_setfam_1(A_41,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_66,c_40])).

tff(c_85,plain,(
    ! [A_42] :
      ( ~ r1_setfam_1(A_42,k1_xboole_0)
      | k1_xboole_0 = A_42 ) ),
    inference(resolution,[status(thm)],[c_2,c_72])).

tff(c_92,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_22,c_85])).

tff(c_98,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_20,c_92])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.05/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.05/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n025.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 20:53:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.78/1.23  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.88/1.23  
% 1.88/1.23  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.88/1.23  %$ r2_hidden > r1_tarski > r1_setfam_1 > k4_xboole_0 > k2_tarski > #nlpp > k1_xboole_0 > #skF_1 > #skF_4 > #skF_3 > #skF_2
% 1.88/1.23  
% 1.88/1.23  %Foreground sorts:
% 1.88/1.23  
% 1.88/1.23  
% 1.88/1.23  %Background operators:
% 1.88/1.23  
% 1.88/1.23  
% 1.88/1.23  %Foreground operators:
% 1.88/1.23  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.88/1.23  tff(r1_setfam_1, type, r1_setfam_1: ($i * $i) > $o).
% 1.88/1.23  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.88/1.23  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.88/1.23  tff('#skF_1', type, '#skF_1': $i > $i).
% 1.88/1.23  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.88/1.23  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.88/1.23  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.88/1.23  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.88/1.23  tff('#skF_4', type, '#skF_4': $i).
% 1.88/1.23  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 1.88/1.23  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.88/1.23  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 1.88/1.23  
% 1.88/1.24  tff(f_60, negated_conjecture, ~(![A]: (r1_setfam_1(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t21_setfam_1)).
% 1.88/1.24  tff(f_33, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 1.88/1.24  tff(f_55, axiom, (![A, B]: (r1_setfam_1(A, B) <=> (![C]: ~(r2_hidden(C, A) & (![D]: ~(r2_hidden(D, B) & r1_tarski(C, D))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_setfam_1)).
% 1.88/1.24  tff(f_35, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 1.88/1.24  tff(f_43, axiom, (![A, B, C]: ((k4_xboole_0(k2_tarski(A, B), C) = k2_tarski(A, B)) <=> (~r2_hidden(A, C) & ~r2_hidden(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_zfmisc_1)).
% 1.88/1.24  tff(c_20, plain, (k1_xboole_0!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_60])).
% 1.88/1.24  tff(c_22, plain, (r1_setfam_1('#skF_4', k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_60])).
% 1.88/1.24  tff(c_2, plain, (![A_1]: (r2_hidden('#skF_1'(A_1), A_1) | k1_xboole_0=A_1)), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.88/1.24  tff(c_66, plain, (![A_37, B_38, C_39]: (r2_hidden('#skF_3'(A_37, B_38, C_39), B_38) | ~r2_hidden(C_39, A_37) | ~r1_setfam_1(A_37, B_38))), inference(cnfTransformation, [status(thm)], [f_55])).
% 1.88/1.24  tff(c_4, plain, (![A_3]: (k4_xboole_0(A_3, k1_xboole_0)=A_3)), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.88/1.24  tff(c_35, plain, (![A_26, C_27, B_28]: (~r2_hidden(A_26, C_27) | k4_xboole_0(k2_tarski(A_26, B_28), C_27)!=k2_tarski(A_26, B_28))), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.88/1.24  tff(c_40, plain, (![A_26]: (~r2_hidden(A_26, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_4, c_35])).
% 1.88/1.24  tff(c_72, plain, (![C_40, A_41]: (~r2_hidden(C_40, A_41) | ~r1_setfam_1(A_41, k1_xboole_0))), inference(resolution, [status(thm)], [c_66, c_40])).
% 1.88/1.24  tff(c_85, plain, (![A_42]: (~r1_setfam_1(A_42, k1_xboole_0) | k1_xboole_0=A_42)), inference(resolution, [status(thm)], [c_2, c_72])).
% 1.88/1.24  tff(c_92, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_22, c_85])).
% 1.88/1.24  tff(c_98, plain, $false, inference(negUnitSimplification, [status(thm)], [c_20, c_92])).
% 1.88/1.24  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.88/1.24  
% 1.88/1.24  Inference rules
% 1.88/1.24  ----------------------
% 1.88/1.24  #Ref     : 0
% 1.88/1.24  #Sup     : 13
% 1.88/1.24  #Fact    : 0
% 1.88/1.24  #Define  : 0
% 1.88/1.24  #Split   : 0
% 1.88/1.24  #Chain   : 0
% 1.88/1.24  #Close   : 0
% 1.88/1.24  
% 1.88/1.24  Ordering : KBO
% 1.88/1.24  
% 1.88/1.24  Simplification rules
% 1.88/1.24  ----------------------
% 1.88/1.24  #Subsume      : 1
% 1.88/1.24  #Demod        : 0
% 1.88/1.24  #Tautology    : 4
% 1.88/1.24  #SimpNegUnit  : 1
% 1.88/1.24  #BackRed      : 0
% 1.88/1.24  
% 1.88/1.24  #Partial instantiations: 0
% 1.88/1.24  #Strategies tried      : 1
% 1.88/1.24  
% 1.88/1.24  Timing (in seconds)
% 1.88/1.24  ----------------------
% 1.91/1.25  Preprocessing        : 0.31
% 1.91/1.25  Parsing              : 0.16
% 1.91/1.25  CNF conversion       : 0.02
% 1.91/1.25  Main loop            : 0.11
% 1.91/1.25  Inferencing          : 0.05
% 1.91/1.25  Reduction            : 0.03
% 1.91/1.25  Demodulation         : 0.02
% 1.91/1.25  BG Simplification    : 0.01
% 1.91/1.25  Subsumption          : 0.02
% 1.91/1.25  Abstraction          : 0.01
% 1.91/1.25  MUC search           : 0.00
% 1.91/1.25  Cooper               : 0.00
% 1.91/1.25  Total                : 0.44
% 1.91/1.25  Index Insertion      : 0.00
% 1.91/1.25  Index Deletion       : 0.00
% 1.91/1.25  Index Matching       : 0.00
% 1.91/1.25  BG Taut test         : 0.00
%------------------------------------------------------------------------------
