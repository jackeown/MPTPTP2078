%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:52:09 EST 2020

% Result     : Theorem 2.03s
% Output     : CNFRefutation 2.03s
% Verified   : 
% Statistics : Number of formulae       :   35 (  36 expanded)
%              Number of leaves         :   24 (  25 expanded)
%              Depth                    :    5
%              Number of atoms          :   29 (  31 expanded)
%              Number of equality atoms :    5 (   5 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k2_tarski > #nlpp > #skF_1 > #skF_5 > #skF_3 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

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

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(f_69,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( r1_xboole_0(k2_tarski(A,B),C)
          & r2_hidden(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_zfmisc_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_63,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_tarski(A,B),C)
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_zfmisc_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

tff(c_48,plain,(
    r2_hidden('#skF_3','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_24,plain,(
    ! [B_8] : r1_tarski(B_8,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_90,plain,(
    ! [A_55,C_56,B_57] :
      ( r2_hidden(A_55,C_56)
      | ~ r1_tarski(k2_tarski(A_55,B_57),C_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_95,plain,(
    ! [A_55,B_57] : r2_hidden(A_55,k2_tarski(A_55,B_57)) ),
    inference(resolution,[status(thm)],[c_24,c_90])).

tff(c_50,plain,(
    r1_xboole_0(k2_tarski('#skF_3','#skF_4'),'#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_62,plain,(
    ! [A_44,B_45] :
      ( k4_xboole_0(A_44,B_45) = A_44
      | ~ r1_xboole_0(A_44,B_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_66,plain,(
    k4_xboole_0(k2_tarski('#skF_3','#skF_4'),'#skF_5') = k2_tarski('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_50,c_62])).

tff(c_101,plain,(
    ! [D_63,B_64,A_65] :
      ( ~ r2_hidden(D_63,B_64)
      | ~ r2_hidden(D_63,k4_xboole_0(A_65,B_64)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_105,plain,(
    ! [D_66] :
      ( ~ r2_hidden(D_66,'#skF_5')
      | ~ r2_hidden(D_66,k2_tarski('#skF_3','#skF_4')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_66,c_101])).

tff(c_109,plain,(
    ~ r2_hidden('#skF_3','#skF_5') ),
    inference(resolution,[status(thm)],[c_95,c_105])).

tff(c_117,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_109])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n010.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 13:47:14 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.18/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.03/1.24  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.03/1.24  
% 2.03/1.24  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.03/1.25  %$ r2_hidden > r1_xboole_0 > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k2_tarski > #nlpp > #skF_1 > #skF_5 > #skF_3 > #skF_2 > #skF_4
% 2.03/1.25  
% 2.03/1.25  %Foreground sorts:
% 2.03/1.25  
% 2.03/1.25  
% 2.03/1.25  %Background operators:
% 2.03/1.25  
% 2.03/1.25  
% 2.03/1.25  %Foreground operators:
% 2.03/1.25  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.03/1.25  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.03/1.25  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.03/1.25  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.03/1.25  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.03/1.25  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.03/1.25  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.03/1.25  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.03/1.25  tff('#skF_5', type, '#skF_5': $i).
% 2.03/1.25  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.03/1.25  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.03/1.25  tff('#skF_3', type, '#skF_3': $i).
% 2.03/1.25  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.03/1.25  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.03/1.25  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.03/1.25  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.03/1.25  tff('#skF_4', type, '#skF_4': $i).
% 2.03/1.25  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.03/1.25  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.03/1.25  
% 2.03/1.26  tff(f_69, negated_conjecture, ~(![A, B, C]: ~(r1_xboole_0(k2_tarski(A, B), C) & r2_hidden(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_zfmisc_1)).
% 2.03/1.26  tff(f_41, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.03/1.26  tff(f_63, axiom, (![A, B, C]: (r1_tarski(k2_tarski(A, B), C) <=> (r2_hidden(A, C) & r2_hidden(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 2.03/1.26  tff(f_45, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 2.03/1.26  tff(f_35, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_xboole_0)).
% 2.03/1.26  tff(c_48, plain, (r2_hidden('#skF_3', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.03/1.26  tff(c_24, plain, (![B_8]: (r1_tarski(B_8, B_8))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.03/1.26  tff(c_90, plain, (![A_55, C_56, B_57]: (r2_hidden(A_55, C_56) | ~r1_tarski(k2_tarski(A_55, B_57), C_56))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.03/1.26  tff(c_95, plain, (![A_55, B_57]: (r2_hidden(A_55, k2_tarski(A_55, B_57)))), inference(resolution, [status(thm)], [c_24, c_90])).
% 2.03/1.26  tff(c_50, plain, (r1_xboole_0(k2_tarski('#skF_3', '#skF_4'), '#skF_5')), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.03/1.26  tff(c_62, plain, (![A_44, B_45]: (k4_xboole_0(A_44, B_45)=A_44 | ~r1_xboole_0(A_44, B_45))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.03/1.26  tff(c_66, plain, (k4_xboole_0(k2_tarski('#skF_3', '#skF_4'), '#skF_5')=k2_tarski('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_50, c_62])).
% 2.03/1.26  tff(c_101, plain, (![D_63, B_64, A_65]: (~r2_hidden(D_63, B_64) | ~r2_hidden(D_63, k4_xboole_0(A_65, B_64)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.03/1.26  tff(c_105, plain, (![D_66]: (~r2_hidden(D_66, '#skF_5') | ~r2_hidden(D_66, k2_tarski('#skF_3', '#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_66, c_101])).
% 2.03/1.26  tff(c_109, plain, (~r2_hidden('#skF_3', '#skF_5')), inference(resolution, [status(thm)], [c_95, c_105])).
% 2.03/1.26  tff(c_117, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_48, c_109])).
% 2.03/1.26  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.03/1.26  
% 2.03/1.26  Inference rules
% 2.03/1.26  ----------------------
% 2.03/1.26  #Ref     : 0
% 2.03/1.26  #Sup     : 13
% 2.03/1.26  #Fact    : 0
% 2.03/1.26  #Define  : 0
% 2.03/1.26  #Split   : 0
% 2.03/1.26  #Chain   : 0
% 2.03/1.26  #Close   : 0
% 2.03/1.26  
% 2.03/1.26  Ordering : KBO
% 2.03/1.26  
% 2.03/1.26  Simplification rules
% 2.03/1.26  ----------------------
% 2.03/1.26  #Subsume      : 0
% 2.03/1.26  #Demod        : 3
% 2.03/1.26  #Tautology    : 8
% 2.03/1.26  #SimpNegUnit  : 0
% 2.03/1.26  #BackRed      : 0
% 2.03/1.26  
% 2.03/1.26  #Partial instantiations: 0
% 2.03/1.26  #Strategies tried      : 1
% 2.03/1.26  
% 2.03/1.26  Timing (in seconds)
% 2.03/1.26  ----------------------
% 2.03/1.26  Preprocessing        : 0.38
% 2.03/1.26  Parsing              : 0.19
% 2.03/1.26  CNF conversion       : 0.03
% 2.03/1.26  Main loop            : 0.13
% 2.03/1.26  Inferencing          : 0.04
% 2.03/1.26  Reduction            : 0.04
% 2.03/1.26  Demodulation         : 0.03
% 2.03/1.26  BG Simplification    : 0.02
% 2.03/1.26  Subsumption          : 0.03
% 2.03/1.26  Abstraction          : 0.01
% 2.03/1.26  MUC search           : 0.00
% 2.03/1.26  Cooper               : 0.00
% 2.03/1.26  Total                : 0.54
% 2.03/1.26  Index Insertion      : 0.00
% 2.03/1.26  Index Deletion       : 0.00
% 2.03/1.26  Index Matching       : 0.00
% 2.03/1.26  BG Taut test         : 0.00
%------------------------------------------------------------------------------
