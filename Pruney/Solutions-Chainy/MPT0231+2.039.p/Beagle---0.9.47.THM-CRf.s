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
% DateTime   : Thu Dec  3 09:49:19 EST 2020

% Result     : Theorem 1.63s
% Output     : CNFRefutation 1.63s
% Verified   : 
% Statistics : Number of formulae       :   22 (  23 expanded)
%              Number of leaves         :   13 (  14 expanded)
%              Depth                    :    5
%              Number of atoms          :   21 (  23 expanded)
%              Number of equality atoms :    5 (   6 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(f_44,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r1_tarski(k2_tarski(A,B),k1_tarski(C))
       => A = C ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_zfmisc_1)).

tff(f_35,axiom,(
    ! [A,B] : r1_tarski(k1_tarski(A),k2_tarski(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_zfmisc_1)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),k1_tarski(B))
     => A = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_zfmisc_1)).

tff(c_10,plain,(
    '#skF_3' != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_6,plain,(
    ! [A_5,B_6] : r1_tarski(k1_tarski(A_5),k2_tarski(A_5,B_6)) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_12,plain,(
    r1_tarski(k2_tarski('#skF_1','#skF_2'),k1_tarski('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_33,plain,(
    ! [A_15,C_16,B_17] :
      ( r1_tarski(A_15,C_16)
      | ~ r1_tarski(B_17,C_16)
      | ~ r1_tarski(A_15,B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_50,plain,(
    ! [A_21] :
      ( r1_tarski(A_21,k1_tarski('#skF_3'))
      | ~ r1_tarski(A_21,k2_tarski('#skF_1','#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_12,c_33])).

tff(c_60,plain,(
    r1_tarski(k1_tarski('#skF_1'),k1_tarski('#skF_3')) ),
    inference(resolution,[status(thm)],[c_6,c_50])).

tff(c_8,plain,(
    ! [B_8,A_7] :
      ( B_8 = A_7
      | ~ r1_tarski(k1_tarski(A_7),k1_tarski(B_8)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_65,plain,(
    '#skF_3' = '#skF_1' ),
    inference(resolution,[status(thm)],[c_60,c_8])).

tff(c_70,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_10,c_65])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.36  % Computer   : n010.cluster.edu
% 0.15/0.36  % Model      : x86_64 x86_64
% 0.15/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.36  % Memory     : 8042.1875MB
% 0.15/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.36  % CPULimit   : 60
% 0.15/0.36  % DateTime   : Tue Dec  1 10:25:59 EST 2020
% 0.15/0.36  % CPUTime    : 
% 0.15/0.37  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.63/1.11  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.63/1.11  
% 1.63/1.11  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.63/1.11  %$ r1_tarski > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1
% 1.63/1.11  
% 1.63/1.11  %Foreground sorts:
% 1.63/1.11  
% 1.63/1.11  
% 1.63/1.11  %Background operators:
% 1.63/1.11  
% 1.63/1.11  
% 1.63/1.11  %Foreground operators:
% 1.63/1.11  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.63/1.11  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.63/1.11  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.63/1.11  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.63/1.11  tff('#skF_2', type, '#skF_2': $i).
% 1.63/1.11  tff('#skF_3', type, '#skF_3': $i).
% 1.63/1.11  tff('#skF_1', type, '#skF_1': $i).
% 1.63/1.11  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.63/1.11  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.63/1.11  
% 1.63/1.12  tff(f_44, negated_conjecture, ~(![A, B, C]: (r1_tarski(k2_tarski(A, B), k1_tarski(C)) => (A = C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t26_zfmisc_1)).
% 1.63/1.12  tff(f_35, axiom, (![A, B]: r1_tarski(k1_tarski(A), k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_zfmisc_1)).
% 1.63/1.12  tff(f_31, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 1.63/1.12  tff(f_39, axiom, (![A, B]: (r1_tarski(k1_tarski(A), k1_tarski(B)) => (A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_zfmisc_1)).
% 1.63/1.12  tff(c_10, plain, ('#skF_3'!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_44])).
% 1.63/1.12  tff(c_6, plain, (![A_5, B_6]: (r1_tarski(k1_tarski(A_5), k2_tarski(A_5, B_6)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.63/1.12  tff(c_12, plain, (r1_tarski(k2_tarski('#skF_1', '#skF_2'), k1_tarski('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_44])).
% 1.63/1.12  tff(c_33, plain, (![A_15, C_16, B_17]: (r1_tarski(A_15, C_16) | ~r1_tarski(B_17, C_16) | ~r1_tarski(A_15, B_17))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.63/1.12  tff(c_50, plain, (![A_21]: (r1_tarski(A_21, k1_tarski('#skF_3')) | ~r1_tarski(A_21, k2_tarski('#skF_1', '#skF_2')))), inference(resolution, [status(thm)], [c_12, c_33])).
% 1.63/1.12  tff(c_60, plain, (r1_tarski(k1_tarski('#skF_1'), k1_tarski('#skF_3'))), inference(resolution, [status(thm)], [c_6, c_50])).
% 1.63/1.12  tff(c_8, plain, (![B_8, A_7]: (B_8=A_7 | ~r1_tarski(k1_tarski(A_7), k1_tarski(B_8)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.63/1.12  tff(c_65, plain, ('#skF_3'='#skF_1'), inference(resolution, [status(thm)], [c_60, c_8])).
% 1.63/1.12  tff(c_70, plain, $false, inference(negUnitSimplification, [status(thm)], [c_10, c_65])).
% 1.63/1.12  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.63/1.12  
% 1.63/1.12  Inference rules
% 1.63/1.12  ----------------------
% 1.63/1.12  #Ref     : 0
% 1.63/1.12  #Sup     : 13
% 1.63/1.12  #Fact    : 0
% 1.63/1.12  #Define  : 0
% 1.63/1.12  #Split   : 0
% 1.63/1.12  #Chain   : 0
% 1.63/1.12  #Close   : 0
% 1.63/1.12  
% 1.63/1.12  Ordering : KBO
% 1.63/1.12  
% 1.63/1.12  Simplification rules
% 1.63/1.12  ----------------------
% 1.63/1.12  #Subsume      : 0
% 1.63/1.12  #Demod        : 0
% 1.63/1.12  #Tautology    : 5
% 1.63/1.12  #SimpNegUnit  : 1
% 1.63/1.12  #BackRed      : 0
% 1.63/1.12  
% 1.63/1.12  #Partial instantiations: 0
% 1.63/1.12  #Strategies tried      : 1
% 1.63/1.12  
% 1.63/1.12  Timing (in seconds)
% 1.63/1.12  ----------------------
% 1.63/1.12  Preprocessing        : 0.26
% 1.63/1.12  Parsing              : 0.14
% 1.63/1.12  CNF conversion       : 0.01
% 1.63/1.12  Main loop            : 0.09
% 1.63/1.12  Inferencing          : 0.04
% 1.63/1.12  Reduction            : 0.03
% 1.63/1.12  Demodulation         : 0.02
% 1.63/1.12  BG Simplification    : 0.01
% 1.63/1.12  Subsumption          : 0.02
% 1.63/1.12  Abstraction          : 0.00
% 1.63/1.12  MUC search           : 0.00
% 1.63/1.12  Cooper               : 0.00
% 1.63/1.12  Total                : 0.38
% 1.63/1.12  Index Insertion      : 0.00
% 1.63/1.12  Index Deletion       : 0.00
% 1.63/1.12  Index Matching       : 0.00
% 1.63/1.12  BG Taut test         : 0.00
%------------------------------------------------------------------------------
