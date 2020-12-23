%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:53:54 EST 2020

% Result     : Theorem 1.83s
% Output     : CNFRefutation 1.83s
% Verified   : 
% Statistics : Number of formulae       :   35 (  43 expanded)
%              Number of leaves         :   18 (  23 expanded)
%              Depth                    :    6
%              Number of atoms          :   27 (  41 expanded)
%              Number of equality atoms :   20 (  28 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_33,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_44,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( r1_tarski(A,B)
          & r1_tarski(C,D) )
       => k3_xboole_0(k2_zfmisc_1(A,D),k2_zfmisc_1(B,C)) = k2_zfmisc_1(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t124_zfmisc_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_37,axiom,(
    ! [A,B,C,D] : k2_zfmisc_1(k3_xboole_0(A,B),k3_xboole_0(C,D)) = k3_xboole_0(k2_zfmisc_1(A,C),k2_zfmisc_1(B,D)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t123_zfmisc_1)).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_8,plain,(
    ! [A_5] : k4_xboole_0(A_5,k1_xboole_0) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_16,plain,(
    r1_tarski('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_63,plain,(
    ! [A_17,B_18] :
      ( k4_xboole_0(A_17,B_18) = k1_xboole_0
      | ~ r1_tarski(A_17,B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_74,plain,(
    k4_xboole_0('#skF_3','#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_16,c_63])).

tff(c_84,plain,(
    ! [A_19,B_20] : k4_xboole_0(A_19,k4_xboole_0(A_19,B_20)) = k3_xboole_0(A_19,B_20) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_102,plain,(
    k4_xboole_0('#skF_3',k1_xboole_0) = k3_xboole_0('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_74,c_84])).

tff(c_109,plain,(
    k3_xboole_0('#skF_4','#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_8,c_102])).

tff(c_18,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_75,plain,(
    k4_xboole_0('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_18,c_63])).

tff(c_99,plain,(
    k4_xboole_0('#skF_1',k1_xboole_0) = k3_xboole_0('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_75,c_84])).

tff(c_108,plain,(
    k3_xboole_0('#skF_1','#skF_2') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_99])).

tff(c_12,plain,(
    ! [A_8,C_10,B_9,D_11] : k3_xboole_0(k2_zfmisc_1(A_8,C_10),k2_zfmisc_1(B_9,D_11)) = k2_zfmisc_1(k3_xboole_0(A_8,B_9),k3_xboole_0(C_10,D_11)) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_14,plain,(
    k3_xboole_0(k2_zfmisc_1('#skF_1','#skF_4'),k2_zfmisc_1('#skF_2','#skF_3')) != k2_zfmisc_1('#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_19,plain,(
    k2_zfmisc_1(k3_xboole_0('#skF_1','#skF_2'),k3_xboole_0('#skF_4','#skF_3')) != k2_zfmisc_1('#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_14])).

tff(c_110,plain,(
    k2_zfmisc_1('#skF_1',k3_xboole_0('#skF_4','#skF_3')) != k2_zfmisc_1('#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_108,c_19])).

tff(c_188,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_109,c_110])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n006.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 10:33:07 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.83/1.21  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.83/1.21  
% 1.83/1.21  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.83/1.21  %$ r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 1.83/1.21  
% 1.83/1.21  %Foreground sorts:
% 1.83/1.21  
% 1.83/1.21  
% 1.83/1.21  %Background operators:
% 1.83/1.21  
% 1.83/1.21  
% 1.83/1.21  %Foreground operators:
% 1.83/1.21  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.83/1.21  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.83/1.21  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.83/1.21  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.83/1.21  tff('#skF_2', type, '#skF_2': $i).
% 1.83/1.21  tff('#skF_3', type, '#skF_3': $i).
% 1.83/1.21  tff('#skF_1', type, '#skF_1': $i).
% 1.83/1.21  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.83/1.21  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.83/1.21  tff('#skF_4', type, '#skF_4': $i).
% 1.83/1.21  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.83/1.21  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.83/1.21  
% 1.83/1.22  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 1.83/1.22  tff(f_33, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 1.83/1.22  tff(f_44, negated_conjecture, ~(![A, B, C, D]: ((r1_tarski(A, B) & r1_tarski(C, D)) => (k3_xboole_0(k2_zfmisc_1(A, D), k2_zfmisc_1(B, C)) = k2_zfmisc_1(A, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t124_zfmisc_1)).
% 1.83/1.22  tff(f_31, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 1.83/1.22  tff(f_35, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 1.83/1.22  tff(f_37, axiom, (![A, B, C, D]: (k2_zfmisc_1(k3_xboole_0(A, B), k3_xboole_0(C, D)) = k3_xboole_0(k2_zfmisc_1(A, C), k2_zfmisc_1(B, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t123_zfmisc_1)).
% 1.83/1.22  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.83/1.22  tff(c_8, plain, (![A_5]: (k4_xboole_0(A_5, k1_xboole_0)=A_5)), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.83/1.22  tff(c_16, plain, (r1_tarski('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_44])).
% 1.83/1.22  tff(c_63, plain, (![A_17, B_18]: (k4_xboole_0(A_17, B_18)=k1_xboole_0 | ~r1_tarski(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.83/1.22  tff(c_74, plain, (k4_xboole_0('#skF_3', '#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_16, c_63])).
% 1.83/1.22  tff(c_84, plain, (![A_19, B_20]: (k4_xboole_0(A_19, k4_xboole_0(A_19, B_20))=k3_xboole_0(A_19, B_20))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.83/1.22  tff(c_102, plain, (k4_xboole_0('#skF_3', k1_xboole_0)=k3_xboole_0('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_74, c_84])).
% 1.83/1.22  tff(c_109, plain, (k3_xboole_0('#skF_4', '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_2, c_8, c_102])).
% 1.83/1.22  tff(c_18, plain, (r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_44])).
% 1.83/1.22  tff(c_75, plain, (k4_xboole_0('#skF_1', '#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_18, c_63])).
% 1.83/1.22  tff(c_99, plain, (k4_xboole_0('#skF_1', k1_xboole_0)=k3_xboole_0('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_75, c_84])).
% 1.83/1.22  tff(c_108, plain, (k3_xboole_0('#skF_1', '#skF_2')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_8, c_99])).
% 1.83/1.22  tff(c_12, plain, (![A_8, C_10, B_9, D_11]: (k3_xboole_0(k2_zfmisc_1(A_8, C_10), k2_zfmisc_1(B_9, D_11))=k2_zfmisc_1(k3_xboole_0(A_8, B_9), k3_xboole_0(C_10, D_11)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.83/1.22  tff(c_14, plain, (k3_xboole_0(k2_zfmisc_1('#skF_1', '#skF_4'), k2_zfmisc_1('#skF_2', '#skF_3'))!=k2_zfmisc_1('#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_44])).
% 1.83/1.22  tff(c_19, plain, (k2_zfmisc_1(k3_xboole_0('#skF_1', '#skF_2'), k3_xboole_0('#skF_4', '#skF_3'))!=k2_zfmisc_1('#skF_1', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_12, c_14])).
% 1.83/1.22  tff(c_110, plain, (k2_zfmisc_1('#skF_1', k3_xboole_0('#skF_4', '#skF_3'))!=k2_zfmisc_1('#skF_1', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_108, c_19])).
% 1.83/1.22  tff(c_188, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_109, c_110])).
% 1.83/1.22  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.83/1.22  
% 1.83/1.22  Inference rules
% 1.83/1.22  ----------------------
% 1.83/1.22  #Ref     : 0
% 1.83/1.22  #Sup     : 47
% 1.83/1.22  #Fact    : 0
% 1.83/1.22  #Define  : 0
% 1.83/1.22  #Split   : 0
% 1.83/1.22  #Chain   : 0
% 1.83/1.22  #Close   : 0
% 1.83/1.22  
% 1.83/1.22  Ordering : KBO
% 1.83/1.22  
% 1.83/1.22  Simplification rules
% 1.83/1.22  ----------------------
% 1.83/1.22  #Subsume      : 2
% 1.83/1.22  #Demod        : 9
% 1.83/1.22  #Tautology    : 29
% 1.83/1.22  #SimpNegUnit  : 0
% 1.83/1.22  #BackRed      : 1
% 1.83/1.22  
% 1.83/1.22  #Partial instantiations: 0
% 1.83/1.22  #Strategies tried      : 1
% 1.83/1.22  
% 1.83/1.22  Timing (in seconds)
% 1.83/1.22  ----------------------
% 1.83/1.23  Preprocessing        : 0.28
% 1.83/1.23  Parsing              : 0.16
% 1.83/1.23  CNF conversion       : 0.02
% 1.83/1.23  Main loop            : 0.15
% 1.83/1.23  Inferencing          : 0.05
% 1.83/1.23  Reduction            : 0.05
% 1.83/1.23  Demodulation         : 0.05
% 1.83/1.23  BG Simplification    : 0.01
% 1.83/1.23  Subsumption          : 0.02
% 1.83/1.23  Abstraction          : 0.01
% 1.83/1.23  MUC search           : 0.00
% 1.83/1.23  Cooper               : 0.00
% 1.83/1.23  Total                : 0.45
% 1.83/1.23  Index Insertion      : 0.00
% 1.83/1.23  Index Deletion       : 0.00
% 1.83/1.23  Index Matching       : 0.00
% 1.83/1.23  BG Taut test         : 0.00
%------------------------------------------------------------------------------
