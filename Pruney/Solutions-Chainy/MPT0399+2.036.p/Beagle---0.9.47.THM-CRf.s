%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:57:36 EST 2020

% Result     : Theorem 1.66s
% Output     : CNFRefutation 1.66s
% Verified   : 
% Statistics : Number of formulae       :   28 (  29 expanded)
%              Number of leaves         :   17 (  18 expanded)
%              Depth                    :    6
%              Number of atoms          :   28 (  30 expanded)
%              Number of equality atoms :   10 (  11 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > r1_setfam_1 > k2_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_1 > #skF_4 > #skF_3 > #skF_2

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

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(f_59,negated_conjecture,(
    ~ ! [A] :
        ( r1_setfam_1(A,k1_xboole_0)
       => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_setfam_1)).

tff(f_33,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_54,axiom,(
    ! [A,B] :
      ( r1_setfam_1(A,B)
    <=> ! [C] :
          ~ ( r2_hidden(C,A)
            & ! [D] :
                ~ ( r2_hidden(D,B)
                  & r1_tarski(C,D) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_setfam_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_42,axiom,(
    ! [A,B] : ~ r2_hidden(A,k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_zfmisc_1)).

tff(c_20,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_22,plain,(
    r1_setfam_1('#skF_4',k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_2,plain,(
    ! [A_1] :
      ( r2_hidden('#skF_1'(A_1),A_1)
      | k1_xboole_0 = A_1 ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_79,plain,(
    ! [A_33,B_34,C_35] :
      ( r2_hidden('#skF_3'(A_33,B_34,C_35),B_34)
      | ~ r2_hidden(C_35,A_33)
      | ~ r1_setfam_1(A_33,B_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_6,plain,(
    ! [A_3] : k2_zfmisc_1(A_3,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_45,plain,(
    ! [A_21,B_22] : ~ r2_hidden(A_21,k2_zfmisc_1(A_21,B_22)) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_48,plain,(
    ! [A_3] : ~ r2_hidden(A_3,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_45])).

tff(c_85,plain,(
    ! [C_36,A_37] :
      ( ~ r2_hidden(C_36,A_37)
      | ~ r1_setfam_1(A_37,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_79,c_48])).

tff(c_98,plain,(
    ! [A_38] :
      ( ~ r1_setfam_1(A_38,k1_xboole_0)
      | k1_xboole_0 = A_38 ) ),
    inference(resolution,[status(thm)],[c_2,c_85])).

tff(c_105,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_22,c_98])).

tff(c_111,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_20,c_105])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n012.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 15:19:22 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.66/1.09  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.66/1.09  
% 1.66/1.09  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.66/1.09  %$ r2_hidden > r1_tarski > r1_setfam_1 > k2_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_1 > #skF_4 > #skF_3 > #skF_2
% 1.66/1.09  
% 1.66/1.09  %Foreground sorts:
% 1.66/1.09  
% 1.66/1.09  
% 1.66/1.09  %Background operators:
% 1.66/1.09  
% 1.66/1.09  
% 1.66/1.09  %Foreground operators:
% 1.66/1.09  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.66/1.09  tff(r1_setfam_1, type, r1_setfam_1: ($i * $i) > $o).
% 1.66/1.09  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.66/1.09  tff('#skF_1', type, '#skF_1': $i > $i).
% 1.66/1.09  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.66/1.09  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.66/1.09  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.66/1.09  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.66/1.09  tff('#skF_4', type, '#skF_4': $i).
% 1.66/1.09  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 1.66/1.09  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.66/1.09  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 1.66/1.09  
% 1.66/1.10  tff(f_59, negated_conjecture, ~(![A]: (r1_setfam_1(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t21_setfam_1)).
% 1.66/1.10  tff(f_33, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 1.66/1.10  tff(f_54, axiom, (![A, B]: (r1_setfam_1(A, B) <=> (![C]: ~(r2_hidden(C, A) & (![D]: ~(r2_hidden(D, B) & r1_tarski(C, D))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_setfam_1)).
% 1.66/1.10  tff(f_39, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 1.66/1.10  tff(f_42, axiom, (![A, B]: ~r2_hidden(A, k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t152_zfmisc_1)).
% 1.66/1.10  tff(c_20, plain, (k1_xboole_0!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_59])).
% 1.66/1.10  tff(c_22, plain, (r1_setfam_1('#skF_4', k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_59])).
% 1.66/1.10  tff(c_2, plain, (![A_1]: (r2_hidden('#skF_1'(A_1), A_1) | k1_xboole_0=A_1)), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.66/1.10  tff(c_79, plain, (![A_33, B_34, C_35]: (r2_hidden('#skF_3'(A_33, B_34, C_35), B_34) | ~r2_hidden(C_35, A_33) | ~r1_setfam_1(A_33, B_34))), inference(cnfTransformation, [status(thm)], [f_54])).
% 1.66/1.10  tff(c_6, plain, (![A_3]: (k2_zfmisc_1(A_3, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.66/1.10  tff(c_45, plain, (![A_21, B_22]: (~r2_hidden(A_21, k2_zfmisc_1(A_21, B_22)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.66/1.10  tff(c_48, plain, (![A_3]: (~r2_hidden(A_3, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_6, c_45])).
% 1.66/1.10  tff(c_85, plain, (![C_36, A_37]: (~r2_hidden(C_36, A_37) | ~r1_setfam_1(A_37, k1_xboole_0))), inference(resolution, [status(thm)], [c_79, c_48])).
% 1.66/1.10  tff(c_98, plain, (![A_38]: (~r1_setfam_1(A_38, k1_xboole_0) | k1_xboole_0=A_38)), inference(resolution, [status(thm)], [c_2, c_85])).
% 1.66/1.10  tff(c_105, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_22, c_98])).
% 1.66/1.10  tff(c_111, plain, $false, inference(negUnitSimplification, [status(thm)], [c_20, c_105])).
% 1.66/1.10  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.66/1.10  
% 1.66/1.10  Inference rules
% 1.66/1.10  ----------------------
% 1.66/1.10  #Ref     : 0
% 1.66/1.10  #Sup     : 18
% 1.66/1.10  #Fact    : 0
% 1.66/1.10  #Define  : 0
% 1.66/1.10  #Split   : 0
% 1.66/1.10  #Chain   : 0
% 1.66/1.10  #Close   : 0
% 1.66/1.10  
% 1.66/1.10  Ordering : KBO
% 1.66/1.10  
% 1.66/1.10  Simplification rules
% 1.66/1.10  ----------------------
% 1.66/1.10  #Subsume      : 1
% 1.66/1.10  #Demod        : 0
% 1.66/1.10  #Tautology    : 10
% 1.66/1.10  #SimpNegUnit  : 1
% 1.66/1.10  #BackRed      : 0
% 1.66/1.10  
% 1.66/1.10  #Partial instantiations: 0
% 1.66/1.10  #Strategies tried      : 1
% 1.66/1.10  
% 1.66/1.10  Timing (in seconds)
% 1.66/1.10  ----------------------
% 1.66/1.10  Preprocessing        : 0.26
% 1.66/1.10  Parsing              : 0.14
% 1.66/1.10  CNF conversion       : 0.02
% 1.66/1.10  Main loop            : 0.09
% 1.66/1.10  Inferencing          : 0.04
% 1.66/1.10  Reduction            : 0.03
% 1.66/1.10  Demodulation         : 0.01
% 1.66/1.10  BG Simplification    : 0.01
% 1.66/1.10  Subsumption          : 0.02
% 1.66/1.10  Abstraction          : 0.00
% 1.66/1.10  MUC search           : 0.00
% 1.66/1.10  Cooper               : 0.00
% 1.66/1.10  Total                : 0.38
% 1.66/1.10  Index Insertion      : 0.00
% 1.66/1.10  Index Deletion       : 0.00
% 1.66/1.10  Index Matching       : 0.00
% 1.66/1.10  BG Taut test         : 0.00
%------------------------------------------------------------------------------
