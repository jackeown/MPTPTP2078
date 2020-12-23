%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:48:51 EST 2020

% Result     : Theorem 2.13s
% Output     : CNFRefutation 2.13s
% Verified   : 
% Statistics : Number of formulae       :   31 (  31 expanded)
%              Number of leaves         :   22 (  22 expanded)
%              Depth                    :    5
%              Number of atoms          :   16 (  16 expanded)
%              Number of equality atoms :   11 (  11 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(f_33,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_47,axiom,(
    ! [A,B] : r1_tarski(k1_tarski(A),k2_tarski(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_zfmisc_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_50,negated_conjecture,(
    ~ ! [A,B] : k4_xboole_0(k1_tarski(A),k2_tarski(A,B)) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_zfmisc_1)).

tff(c_6,plain,(
    ! [A_5] : k5_xboole_0(A_5,A_5) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_20,plain,(
    ! [A_27,B_28] : r1_tarski(k1_tarski(A_27),k2_tarski(A_27,B_28)) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_44,plain,(
    ! [A_34,B_35] :
      ( k3_xboole_0(A_34,B_35) = A_34
      | ~ r1_tarski(A_34,B_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_100,plain,(
    ! [A_45,B_46] : k3_xboole_0(k1_tarski(A_45),k2_tarski(A_45,B_46)) = k1_tarski(A_45) ),
    inference(resolution,[status(thm)],[c_20,c_44])).

tff(c_2,plain,(
    ! [A_1,B_2] : k5_xboole_0(A_1,k3_xboole_0(A_1,B_2)) = k4_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_106,plain,(
    ! [A_45,B_46] : k5_xboole_0(k1_tarski(A_45),k1_tarski(A_45)) = k4_xboole_0(k1_tarski(A_45),k2_tarski(A_45,B_46)) ),
    inference(superposition,[status(thm),theory(equality)],[c_100,c_2])).

tff(c_114,plain,(
    ! [A_45,B_46] : k4_xboole_0(k1_tarski(A_45),k2_tarski(A_45,B_46)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_106])).

tff(c_22,plain,(
    k4_xboole_0(k1_tarski('#skF_1'),k2_tarski('#skF_1','#skF_2')) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_119,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_114,c_22])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.36  % Computer   : n022.cluster.edu
% 0.15/0.36  % Model      : x86_64 x86_64
% 0.15/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.36  % Memory     : 8042.1875MB
% 0.15/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.36  % CPULimit   : 60
% 0.15/0.36  % DateTime   : Tue Dec  1 11:14:11 EST 2020
% 0.15/0.36  % CPUTime    : 
% 0.15/0.37  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.13/1.51  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.13/1.51  
% 2.13/1.51  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.13/1.52  %$ r1_tarski > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1
% 2.13/1.52  
% 2.13/1.52  %Foreground sorts:
% 2.13/1.52  
% 2.13/1.52  
% 2.13/1.52  %Background operators:
% 2.13/1.52  
% 2.13/1.52  
% 2.13/1.52  %Foreground operators:
% 2.13/1.52  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.13/1.52  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.13/1.52  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.13/1.52  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.13/1.52  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.13/1.52  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.13/1.52  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.13/1.52  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.13/1.52  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.13/1.52  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.13/1.52  tff('#skF_2', type, '#skF_2': $i).
% 2.13/1.52  tff('#skF_1', type, '#skF_1': $i).
% 2.13/1.52  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.13/1.52  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.13/1.52  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.13/1.52  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.13/1.52  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.13/1.52  
% 2.13/1.53  tff(f_33, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t92_xboole_1)).
% 2.13/1.53  tff(f_47, axiom, (![A, B]: r1_tarski(k1_tarski(A), k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_zfmisc_1)).
% 2.13/1.53  tff(f_31, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 2.13/1.53  tff(f_27, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 2.13/1.53  tff(f_50, negated_conjecture, ~(![A, B]: (k4_xboole_0(k1_tarski(A), k2_tarski(A, B)) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_zfmisc_1)).
% 2.13/1.53  tff(c_6, plain, (![A_5]: (k5_xboole_0(A_5, A_5)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.13/1.53  tff(c_20, plain, (![A_27, B_28]: (r1_tarski(k1_tarski(A_27), k2_tarski(A_27, B_28)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.13/1.53  tff(c_44, plain, (![A_34, B_35]: (k3_xboole_0(A_34, B_35)=A_34 | ~r1_tarski(A_34, B_35))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.13/1.53  tff(c_100, plain, (![A_45, B_46]: (k3_xboole_0(k1_tarski(A_45), k2_tarski(A_45, B_46))=k1_tarski(A_45))), inference(resolution, [status(thm)], [c_20, c_44])).
% 2.13/1.53  tff(c_2, plain, (![A_1, B_2]: (k5_xboole_0(A_1, k3_xboole_0(A_1, B_2))=k4_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.13/1.53  tff(c_106, plain, (![A_45, B_46]: (k5_xboole_0(k1_tarski(A_45), k1_tarski(A_45))=k4_xboole_0(k1_tarski(A_45), k2_tarski(A_45, B_46)))), inference(superposition, [status(thm), theory('equality')], [c_100, c_2])).
% 2.13/1.53  tff(c_114, plain, (![A_45, B_46]: (k4_xboole_0(k1_tarski(A_45), k2_tarski(A_45, B_46))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_106])).
% 2.13/1.53  tff(c_22, plain, (k4_xboole_0(k1_tarski('#skF_1'), k2_tarski('#skF_1', '#skF_2'))!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.13/1.53  tff(c_119, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_114, c_22])).
% 2.13/1.53  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.13/1.53  
% 2.13/1.53  Inference rules
% 2.13/1.53  ----------------------
% 2.13/1.53  #Ref     : 0
% 2.13/1.53  #Sup     : 22
% 2.13/1.53  #Fact    : 0
% 2.13/1.53  #Define  : 0
% 2.13/1.53  #Split   : 0
% 2.13/1.53  #Chain   : 0
% 2.13/1.53  #Close   : 0
% 2.13/1.53  
% 2.13/1.53  Ordering : KBO
% 2.13/1.53  
% 2.13/1.53  Simplification rules
% 2.13/1.53  ----------------------
% 2.13/1.53  #Subsume      : 0
% 2.13/1.53  #Demod        : 4
% 2.13/1.53  #Tautology    : 17
% 2.13/1.53  #SimpNegUnit  : 0
% 2.13/1.53  #BackRed      : 1
% 2.13/1.53  
% 2.13/1.53  #Partial instantiations: 0
% 2.13/1.53  #Strategies tried      : 1
% 2.13/1.53  
% 2.13/1.53  Timing (in seconds)
% 2.13/1.53  ----------------------
% 2.23/1.53  Preprocessing        : 0.45
% 2.23/1.53  Parsing              : 0.23
% 2.23/1.54  CNF conversion       : 0.03
% 2.23/1.54  Main loop            : 0.17
% 2.23/1.54  Inferencing          : 0.07
% 2.23/1.54  Reduction            : 0.05
% 2.23/1.54  Demodulation         : 0.04
% 2.23/1.54  BG Simplification    : 0.02
% 2.23/1.54  Subsumption          : 0.02
% 2.23/1.54  Abstraction          : 0.02
% 2.23/1.54  MUC search           : 0.00
% 2.23/1.54  Cooper               : 0.00
% 2.23/1.54  Total                : 0.66
% 2.23/1.54  Index Insertion      : 0.00
% 2.23/1.54  Index Deletion       : 0.00
% 2.23/1.54  Index Matching       : 0.00
% 2.23/1.54  BG Taut test         : 0.00
%------------------------------------------------------------------------------
