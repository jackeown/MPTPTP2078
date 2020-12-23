%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:51:50 EST 2020

% Result     : Theorem 1.94s
% Output     : CNFRefutation 2.07s
% Verified   : 
% Statistics : Number of formulae       :   42 (  61 expanded)
%              Number of leaves         :   21 (  30 expanded)
%              Depth                    :    7
%              Number of atoms          :   38 (  66 expanded)
%              Number of equality atoms :   19 (  26 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_xboole_0 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(f_44,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_xboole_0(k1_tarski(A),k1_tarski(B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_enumset1)).

tff(f_28,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_59,negated_conjecture,(
    ~ ! [A,B,C] : k2_xboole_0(k2_tarski(A,B),C) != k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_zfmisc_1)).

tff(f_34,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(A)
     => ~ v1_xboole_0(k2_xboole_0(B,A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc5_xboole_0)).

tff(f_42,axiom,(
    ! [A,B] :
      ~ ( v1_xboole_0(A)
        & A != B
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_boole)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_55,axiom,(
    ! [A,B] : k2_xboole_0(k1_tarski(A),B) != k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_zfmisc_1)).

tff(c_279,plain,(
    ! [A_44,B_45] : k2_xboole_0(k1_tarski(A_44),k1_tarski(B_45)) = k2_tarski(A_44,B_45) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_4,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_22,plain,(
    k2_xboole_0(k2_tarski('#skF_1','#skF_2'),'#skF_3') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_6,plain,(
    ! [B_4,A_3] :
      ( ~ v1_xboole_0(k2_xboole_0(B_4,A_3))
      | v1_xboole_0(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_90,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | v1_xboole_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_6])).

tff(c_100,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_90])).

tff(c_120,plain,(
    ! [B_28,A_29] :
      ( ~ v1_xboole_0(B_28)
      | B_28 = A_29
      | ~ v1_xboole_0(A_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_130,plain,(
    ! [A_30] :
      ( k1_xboole_0 = A_30
      | ~ v1_xboole_0(A_30) ) ),
    inference(resolution,[status(thm)],[c_4,c_120])).

tff(c_141,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_100,c_130])).

tff(c_34,plain,(
    ! [B_24,A_25] : k2_xboole_0(B_24,A_25) = k2_xboole_0(A_25,B_24) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_20,plain,(
    ! [A_17,B_18] : k2_xboole_0(k1_tarski(A_17),B_18) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_60,plain,(
    ! [A_25,A_17] : k2_xboole_0(A_25,k1_tarski(A_17)) != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_20])).

tff(c_146,plain,(
    ! [A_25,A_17] : k2_xboole_0(A_25,k1_tarski(A_17)) != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_141,c_60])).

tff(c_291,plain,(
    ! [A_44,B_45] : k2_tarski(A_44,B_45) != '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_279,c_146])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_87,plain,(
    k2_xboole_0('#skF_3',k2_tarski('#skF_1','#skF_2')) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_2])).

tff(c_114,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | v1_xboole_0(k2_tarski('#skF_1','#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_87,c_6])).

tff(c_118,plain,(
    v1_xboole_0(k2_tarski('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_114])).

tff(c_155,plain,(
    ! [A_31] :
      ( A_31 = '#skF_3'
      | ~ v1_xboole_0(A_31) ) ),
    inference(resolution,[status(thm)],[c_100,c_120])).

tff(c_162,plain,(
    k2_tarski('#skF_1','#skF_2') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_118,c_155])).

tff(c_321,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_291,c_162])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:50:45 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.94/1.23  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.94/1.23  
% 1.94/1.23  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.94/1.23  %$ v1_xboole_0 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 1.94/1.23  
% 1.94/1.23  %Foreground sorts:
% 1.94/1.23  
% 1.94/1.23  
% 1.94/1.23  %Background operators:
% 1.94/1.23  
% 1.94/1.23  
% 1.94/1.23  %Foreground operators:
% 1.94/1.23  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.94/1.23  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.94/1.23  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.94/1.23  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.94/1.23  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.94/1.23  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.94/1.23  tff('#skF_2', type, '#skF_2': $i).
% 1.94/1.23  tff('#skF_3', type, '#skF_3': $i).
% 1.94/1.23  tff('#skF_1', type, '#skF_1': $i).
% 1.94/1.23  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.94/1.23  tff(k3_tarski, type, k3_tarski: $i > $i).
% 1.94/1.23  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.94/1.23  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.94/1.23  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.94/1.23  
% 2.07/1.24  tff(f_44, axiom, (![A, B]: (k2_tarski(A, B) = k2_xboole_0(k1_tarski(A), k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_enumset1)).
% 2.07/1.24  tff(f_28, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.07/1.24  tff(f_59, negated_conjecture, ~(![A, B, C]: ~(k2_xboole_0(k2_tarski(A, B), C) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t50_zfmisc_1)).
% 2.07/1.24  tff(f_34, axiom, (![A, B]: (~v1_xboole_0(A) => ~v1_xboole_0(k2_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc5_xboole_0)).
% 2.07/1.24  tff(f_42, axiom, (![A, B]: ~((v1_xboole_0(A) & ~(A = B)) & v1_xboole_0(B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_boole)).
% 2.07/1.24  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 2.07/1.24  tff(f_55, axiom, (![A, B]: ~(k2_xboole_0(k1_tarski(A), B) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_zfmisc_1)).
% 2.07/1.24  tff(c_279, plain, (![A_44, B_45]: (k2_xboole_0(k1_tarski(A_44), k1_tarski(B_45))=k2_tarski(A_44, B_45))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.07/1.24  tff(c_4, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_28])).
% 2.07/1.24  tff(c_22, plain, (k2_xboole_0(k2_tarski('#skF_1', '#skF_2'), '#skF_3')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.07/1.24  tff(c_6, plain, (![B_4, A_3]: (~v1_xboole_0(k2_xboole_0(B_4, A_3)) | v1_xboole_0(A_3))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.07/1.24  tff(c_90, plain, (~v1_xboole_0(k1_xboole_0) | v1_xboole_0('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_22, c_6])).
% 2.07/1.24  tff(c_100, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_90])).
% 2.07/1.24  tff(c_120, plain, (![B_28, A_29]: (~v1_xboole_0(B_28) | B_28=A_29 | ~v1_xboole_0(A_29))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.07/1.24  tff(c_130, plain, (![A_30]: (k1_xboole_0=A_30 | ~v1_xboole_0(A_30))), inference(resolution, [status(thm)], [c_4, c_120])).
% 2.07/1.24  tff(c_141, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_100, c_130])).
% 2.07/1.24  tff(c_34, plain, (![B_24, A_25]: (k2_xboole_0(B_24, A_25)=k2_xboole_0(A_25, B_24))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.07/1.24  tff(c_20, plain, (![A_17, B_18]: (k2_xboole_0(k1_tarski(A_17), B_18)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.07/1.24  tff(c_60, plain, (![A_25, A_17]: (k2_xboole_0(A_25, k1_tarski(A_17))!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_34, c_20])).
% 2.07/1.24  tff(c_146, plain, (![A_25, A_17]: (k2_xboole_0(A_25, k1_tarski(A_17))!='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_141, c_60])).
% 2.07/1.24  tff(c_291, plain, (![A_44, B_45]: (k2_tarski(A_44, B_45)!='#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_279, c_146])).
% 2.07/1.24  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.07/1.24  tff(c_87, plain, (k2_xboole_0('#skF_3', k2_tarski('#skF_1', '#skF_2'))=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_22, c_2])).
% 2.07/1.24  tff(c_114, plain, (~v1_xboole_0(k1_xboole_0) | v1_xboole_0(k2_tarski('#skF_1', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_87, c_6])).
% 2.07/1.24  tff(c_118, plain, (v1_xboole_0(k2_tarski('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_114])).
% 2.07/1.24  tff(c_155, plain, (![A_31]: (A_31='#skF_3' | ~v1_xboole_0(A_31))), inference(resolution, [status(thm)], [c_100, c_120])).
% 2.07/1.24  tff(c_162, plain, (k2_tarski('#skF_1', '#skF_2')='#skF_3'), inference(resolution, [status(thm)], [c_118, c_155])).
% 2.07/1.24  tff(c_321, plain, $false, inference(negUnitSimplification, [status(thm)], [c_291, c_162])).
% 2.07/1.24  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.07/1.24  
% 2.07/1.24  Inference rules
% 2.07/1.24  ----------------------
% 2.07/1.24  #Ref     : 0
% 2.07/1.24  #Sup     : 78
% 2.07/1.24  #Fact    : 0
% 2.07/1.24  #Define  : 0
% 2.07/1.24  #Split   : 1
% 2.07/1.24  #Chain   : 0
% 2.07/1.24  #Close   : 0
% 2.07/1.24  
% 2.07/1.24  Ordering : KBO
% 2.07/1.24  
% 2.07/1.24  Simplification rules
% 2.07/1.24  ----------------------
% 2.07/1.24  #Subsume      : 15
% 2.07/1.24  #Demod        : 27
% 2.07/1.24  #Tautology    : 39
% 2.07/1.24  #SimpNegUnit  : 1
% 2.07/1.24  #BackRed      : 8
% 2.07/1.24  
% 2.07/1.24  #Partial instantiations: 0
% 2.07/1.24  #Strategies tried      : 1
% 2.07/1.24  
% 2.07/1.24  Timing (in seconds)
% 2.07/1.24  ----------------------
% 2.07/1.25  Preprocessing        : 0.29
% 2.07/1.25  Parsing              : 0.15
% 2.07/1.25  CNF conversion       : 0.02
% 2.07/1.25  Main loop            : 0.20
% 2.07/1.25  Inferencing          : 0.07
% 2.07/1.25  Reduction            : 0.07
% 2.07/1.25  Demodulation         : 0.06
% 2.07/1.25  BG Simplification    : 0.01
% 2.07/1.25  Subsumption          : 0.03
% 2.07/1.25  Abstraction          : 0.01
% 2.07/1.25  MUC search           : 0.00
% 2.07/1.25  Cooper               : 0.00
% 2.07/1.25  Total                : 0.51
% 2.07/1.25  Index Insertion      : 0.00
% 2.07/1.25  Index Deletion       : 0.00
% 2.07/1.25  Index Matching       : 0.00
% 2.07/1.25  BG Taut test         : 0.00
%------------------------------------------------------------------------------
