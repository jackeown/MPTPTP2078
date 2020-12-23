%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:47:52 EST 2020

% Result     : Theorem 1.56s
% Output     : CNFRefutation 1.56s
% Verified   : 
% Statistics : Number of formulae       :   22 (  23 expanded)
%              Number of leaves         :   13 (  14 expanded)
%              Depth                    :    5
%              Number of atoms          :   16 (  18 expanded)
%              Number of equality atoms :    9 (  11 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_1

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

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_40,negated_conjecture,(
    ~ ! [A,B] :
        ( k2_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
       => A = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_zfmisc_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_29,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),k1_tarski(B))
     => A = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_zfmisc_1)).

tff(c_10,plain,(
    '#skF_2' != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_12,plain,(
    k2_xboole_0(k1_tarski('#skF_1'),k1_tarski('#skF_2')) = k1_tarski('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_23,plain,(
    ! [B_11,A_12] : k2_xboole_0(B_11,A_12) = k2_xboole_0(A_12,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_4,plain,(
    ! [A_3,B_4] : r1_tarski(A_3,k2_xboole_0(A_3,B_4)) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_38,plain,(
    ! [A_12,B_11] : r1_tarski(A_12,k2_xboole_0(B_11,A_12)) ),
    inference(superposition,[status(thm),theory(equality)],[c_23,c_4])).

tff(c_74,plain,(
    r1_tarski(k1_tarski('#skF_2'),k1_tarski('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_38])).

tff(c_82,plain,(
    ! [B_15,A_16] :
      ( B_15 = A_16
      | ~ r1_tarski(k1_tarski(A_16),k1_tarski(B_15)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_85,plain,(
    '#skF_2' = '#skF_1' ),
    inference(resolution,[status(thm)],[c_74,c_82])).

tff(c_92,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_10,c_85])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n005.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 17:16:32 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.56/1.06  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.56/1.06  
% 1.56/1.06  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.56/1.07  %$ r1_tarski > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_1
% 1.56/1.07  
% 1.56/1.07  %Foreground sorts:
% 1.56/1.07  
% 1.56/1.07  
% 1.56/1.07  %Background operators:
% 1.56/1.07  
% 1.56/1.07  
% 1.56/1.07  %Foreground operators:
% 1.56/1.07  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.56/1.07  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.56/1.07  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.56/1.07  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.56/1.07  tff('#skF_2', type, '#skF_2': $i).
% 1.56/1.07  tff('#skF_1', type, '#skF_1': $i).
% 1.56/1.07  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.56/1.07  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.56/1.07  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.56/1.07  
% 1.56/1.07  tff(f_40, negated_conjecture, ~(![A, B]: ((k2_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) => (A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t13_zfmisc_1)).
% 1.56/1.07  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 1.56/1.07  tff(f_29, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 1.56/1.07  tff(f_35, axiom, (![A, B]: (r1_tarski(k1_tarski(A), k1_tarski(B)) => (A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_zfmisc_1)).
% 1.56/1.07  tff(c_10, plain, ('#skF_2'!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_40])).
% 1.56/1.07  tff(c_12, plain, (k2_xboole_0(k1_tarski('#skF_1'), k1_tarski('#skF_2'))=k1_tarski('#skF_1')), inference(cnfTransformation, [status(thm)], [f_40])).
% 1.56/1.07  tff(c_23, plain, (![B_11, A_12]: (k2_xboole_0(B_11, A_12)=k2_xboole_0(A_12, B_11))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.56/1.07  tff(c_4, plain, (![A_3, B_4]: (r1_tarski(A_3, k2_xboole_0(A_3, B_4)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.56/1.07  tff(c_38, plain, (![A_12, B_11]: (r1_tarski(A_12, k2_xboole_0(B_11, A_12)))), inference(superposition, [status(thm), theory('equality')], [c_23, c_4])).
% 1.56/1.07  tff(c_74, plain, (r1_tarski(k1_tarski('#skF_2'), k1_tarski('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_12, c_38])).
% 1.56/1.07  tff(c_82, plain, (![B_15, A_16]: (B_15=A_16 | ~r1_tarski(k1_tarski(A_16), k1_tarski(B_15)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.56/1.07  tff(c_85, plain, ('#skF_2'='#skF_1'), inference(resolution, [status(thm)], [c_74, c_82])).
% 1.56/1.07  tff(c_92, plain, $false, inference(negUnitSimplification, [status(thm)], [c_10, c_85])).
% 1.56/1.07  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.56/1.07  
% 1.56/1.07  Inference rules
% 1.56/1.07  ----------------------
% 1.56/1.07  #Ref     : 0
% 1.56/1.07  #Sup     : 20
% 1.56/1.07  #Fact    : 0
% 1.56/1.07  #Define  : 0
% 1.56/1.07  #Split   : 0
% 1.56/1.07  #Chain   : 0
% 1.56/1.07  #Close   : 0
% 1.56/1.07  
% 1.56/1.07  Ordering : KBO
% 1.56/1.07  
% 1.56/1.07  Simplification rules
% 1.56/1.07  ----------------------
% 1.56/1.07  #Subsume      : 0
% 1.56/1.07  #Demod        : 3
% 1.56/1.07  #Tautology    : 15
% 1.56/1.07  #SimpNegUnit  : 1
% 1.56/1.07  #BackRed      : 0
% 1.56/1.07  
% 1.56/1.07  #Partial instantiations: 0
% 1.56/1.07  #Strategies tried      : 1
% 1.56/1.07  
% 1.56/1.07  Timing (in seconds)
% 1.56/1.07  ----------------------
% 1.56/1.08  Preprocessing        : 0.25
% 1.56/1.08  Parsing              : 0.13
% 1.56/1.08  CNF conversion       : 0.01
% 1.56/1.08  Main loop            : 0.09
% 1.56/1.08  Inferencing          : 0.03
% 1.56/1.08  Reduction            : 0.03
% 1.56/1.08  Demodulation         : 0.02
% 1.56/1.08  BG Simplification    : 0.01
% 1.56/1.08  Subsumption          : 0.01
% 1.56/1.08  Abstraction          : 0.00
% 1.56/1.08  MUC search           : 0.00
% 1.56/1.08  Cooper               : 0.00
% 1.56/1.08  Total                : 0.36
% 1.56/1.08  Index Insertion      : 0.00
% 1.56/1.08  Index Deletion       : 0.00
% 1.56/1.08  Index Matching       : 0.00
% 1.56/1.08  BG Taut test         : 0.00
%------------------------------------------------------------------------------
