%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:53:55 EST 2020

% Result     : Theorem 1.67s
% Output     : CNFRefutation 1.67s
% Verified   : 
% Statistics : Number of formulae       :   32 (  38 expanded)
%              Number of leaves         :   17 (  21 expanded)
%              Depth                    :    5
%              Number of atoms          :   24 (  36 expanded)
%              Number of equality atoms :   17 (  23 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k5_xboole_0 > k3_xboole_0 > k2_zfmisc_1 > k2_xboole_0 > #nlpp > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_44,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( r1_tarski(A,B)
          & r1_tarski(C,D) )
       => k3_xboole_0(k2_zfmisc_1(A,D),k2_zfmisc_1(B,C)) = k2_zfmisc_1(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t124_zfmisc_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] : k3_xboole_0(A,k2_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_37,axiom,(
    ! [A,B,C,D] : k2_zfmisc_1(k3_xboole_0(A,B),k3_xboole_0(C,D)) = k3_xboole_0(k2_zfmisc_1(A,C),k2_zfmisc_1(B,D)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_zfmisc_1)).

tff(c_14,plain,(
    r1_tarski('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_60,plain,(
    ! [A_17,B_18] :
      ( k2_xboole_0(A_17,B_18) = B_18
      | ~ r1_tarski(A_17,B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_67,plain,(
    k2_xboole_0('#skF_3','#skF_4') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_14,c_60])).

tff(c_6,plain,(
    ! [A_5,B_6] : k3_xboole_0(A_5,k2_xboole_0(A_5,B_6)) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_92,plain,(
    k3_xboole_0('#skF_3','#skF_4') = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_67,c_6])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_113,plain,(
    k3_xboole_0('#skF_4','#skF_3') = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_92,c_2])).

tff(c_16,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_68,plain,(
    k2_xboole_0('#skF_1','#skF_2') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_16,c_60])).

tff(c_103,plain,(
    k3_xboole_0('#skF_1','#skF_2') = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_68,c_6])).

tff(c_10,plain,(
    ! [A_9,C_11,B_10,D_12] : k3_xboole_0(k2_zfmisc_1(A_9,C_11),k2_zfmisc_1(B_10,D_12)) = k2_zfmisc_1(k3_xboole_0(A_9,B_10),k3_xboole_0(C_11,D_12)) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_12,plain,(
    k3_xboole_0(k2_zfmisc_1('#skF_1','#skF_4'),k2_zfmisc_1('#skF_2','#skF_3')) != k2_zfmisc_1('#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_17,plain,(
    k2_zfmisc_1(k3_xboole_0('#skF_1','#skF_2'),k3_xboole_0('#skF_4','#skF_3')) != k2_zfmisc_1('#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_12])).

tff(c_123,plain,(
    k2_zfmisc_1('#skF_1',k3_xboole_0('#skF_4','#skF_3')) != k2_zfmisc_1('#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_103,c_17])).

tff(c_175,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_113,c_123])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:38:56 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.67/1.14  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.67/1.15  
% 1.67/1.15  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.67/1.15  %$ r1_tarski > k5_xboole_0 > k3_xboole_0 > k2_zfmisc_1 > k2_xboole_0 > #nlpp > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 1.67/1.15  
% 1.67/1.15  %Foreground sorts:
% 1.67/1.15  
% 1.67/1.15  
% 1.67/1.15  %Background operators:
% 1.67/1.15  
% 1.67/1.15  
% 1.67/1.15  %Foreground operators:
% 1.67/1.15  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.67/1.15  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 1.67/1.15  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.67/1.15  tff('#skF_2', type, '#skF_2': $i).
% 1.67/1.15  tff('#skF_3', type, '#skF_3': $i).
% 1.67/1.15  tff('#skF_1', type, '#skF_1': $i).
% 1.67/1.15  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.67/1.15  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.67/1.15  tff('#skF_4', type, '#skF_4': $i).
% 1.67/1.15  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.67/1.15  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.67/1.15  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.67/1.15  
% 1.67/1.16  tff(f_44, negated_conjecture, ~(![A, B, C, D]: ((r1_tarski(A, B) & r1_tarski(C, D)) => (k3_xboole_0(k2_zfmisc_1(A, D), k2_zfmisc_1(B, C)) = k2_zfmisc_1(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t124_zfmisc_1)).
% 1.67/1.16  tff(f_31, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 1.67/1.16  tff(f_33, axiom, (![A, B]: (k3_xboole_0(A, k2_xboole_0(A, B)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t21_xboole_1)).
% 1.67/1.16  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 1.67/1.16  tff(f_37, axiom, (![A, B, C, D]: (k2_zfmisc_1(k3_xboole_0(A, B), k3_xboole_0(C, D)) = k3_xboole_0(k2_zfmisc_1(A, C), k2_zfmisc_1(B, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t123_zfmisc_1)).
% 1.67/1.16  tff(c_14, plain, (r1_tarski('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_44])).
% 1.67/1.16  tff(c_60, plain, (![A_17, B_18]: (k2_xboole_0(A_17, B_18)=B_18 | ~r1_tarski(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.67/1.16  tff(c_67, plain, (k2_xboole_0('#skF_3', '#skF_4')='#skF_4'), inference(resolution, [status(thm)], [c_14, c_60])).
% 1.67/1.16  tff(c_6, plain, (![A_5, B_6]: (k3_xboole_0(A_5, k2_xboole_0(A_5, B_6))=A_5)), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.67/1.16  tff(c_92, plain, (k3_xboole_0('#skF_3', '#skF_4')='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_67, c_6])).
% 1.67/1.16  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.67/1.16  tff(c_113, plain, (k3_xboole_0('#skF_4', '#skF_3')='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_92, c_2])).
% 1.67/1.16  tff(c_16, plain, (r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_44])).
% 1.67/1.16  tff(c_68, plain, (k2_xboole_0('#skF_1', '#skF_2')='#skF_2'), inference(resolution, [status(thm)], [c_16, c_60])).
% 1.67/1.16  tff(c_103, plain, (k3_xboole_0('#skF_1', '#skF_2')='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_68, c_6])).
% 1.67/1.16  tff(c_10, plain, (![A_9, C_11, B_10, D_12]: (k3_xboole_0(k2_zfmisc_1(A_9, C_11), k2_zfmisc_1(B_10, D_12))=k2_zfmisc_1(k3_xboole_0(A_9, B_10), k3_xboole_0(C_11, D_12)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.67/1.16  tff(c_12, plain, (k3_xboole_0(k2_zfmisc_1('#skF_1', '#skF_4'), k2_zfmisc_1('#skF_2', '#skF_3'))!=k2_zfmisc_1('#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_44])).
% 1.67/1.16  tff(c_17, plain, (k2_zfmisc_1(k3_xboole_0('#skF_1', '#skF_2'), k3_xboole_0('#skF_4', '#skF_3'))!=k2_zfmisc_1('#skF_1', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_10, c_12])).
% 1.67/1.16  tff(c_123, plain, (k2_zfmisc_1('#skF_1', k3_xboole_0('#skF_4', '#skF_3'))!=k2_zfmisc_1('#skF_1', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_103, c_17])).
% 1.67/1.16  tff(c_175, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_113, c_123])).
% 1.67/1.16  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.67/1.16  
% 1.67/1.16  Inference rules
% 1.67/1.16  ----------------------
% 1.67/1.16  #Ref     : 0
% 1.67/1.16  #Sup     : 46
% 1.67/1.16  #Fact    : 0
% 1.67/1.16  #Define  : 0
% 1.67/1.16  #Split   : 0
% 1.67/1.16  #Chain   : 0
% 1.67/1.16  #Close   : 0
% 1.67/1.16  
% 1.67/1.16  Ordering : KBO
% 1.67/1.16  
% 1.67/1.16  Simplification rules
% 1.67/1.16  ----------------------
% 1.67/1.16  #Subsume      : 0
% 1.67/1.16  #Demod        : 13
% 1.67/1.16  #Tautology    : 31
% 1.67/1.16  #SimpNegUnit  : 0
% 1.67/1.16  #BackRed      : 1
% 1.67/1.16  
% 1.67/1.16  #Partial instantiations: 0
% 1.67/1.16  #Strategies tried      : 1
% 1.67/1.16  
% 1.67/1.16  Timing (in seconds)
% 1.67/1.16  ----------------------
% 1.67/1.16  Preprocessing        : 0.27
% 1.67/1.16  Parsing              : 0.14
% 1.67/1.16  CNF conversion       : 0.02
% 1.67/1.16  Main loop            : 0.14
% 1.67/1.16  Inferencing          : 0.05
% 1.67/1.16  Reduction            : 0.05
% 1.67/1.16  Demodulation         : 0.04
% 1.67/1.16  BG Simplification    : 0.01
% 1.67/1.16  Subsumption          : 0.02
% 1.67/1.16  Abstraction          : 0.01
% 1.67/1.16  MUC search           : 0.00
% 1.67/1.16  Cooper               : 0.00
% 1.67/1.16  Total                : 0.44
% 1.67/1.16  Index Insertion      : 0.00
% 1.67/1.16  Index Deletion       : 0.00
% 1.67/1.16  Index Matching       : 0.00
% 1.67/1.16  BG Taut test         : 0.00
%------------------------------------------------------------------------------
