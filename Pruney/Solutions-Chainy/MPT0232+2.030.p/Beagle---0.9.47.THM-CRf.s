%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:49:23 EST 2020

% Result     : Theorem 3.53s
% Output     : CNFRefutation 3.53s
% Verified   : 
% Statistics : Number of formulae       :   39 (  52 expanded)
%              Number of leaves         :   20 (  26 expanded)
%              Depth                    :    6
%              Number of atoms          :   32 (  53 expanded)
%              Number of equality atoms :   25 (  35 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k2_enumset1 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_53,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r1_tarski(k2_tarski(A,B),k1_tarski(C))
       => k2_tarski(A,B) = k1_tarski(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t27_zfmisc_1)).

tff(f_48,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_tarski(A,B),k1_tarski(C))
     => A = C ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_zfmisc_1)).

tff(f_37,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_35,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k2_tarski(A,B),k2_tarski(C,D)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_enumset1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_33,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(C,B,D,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t117_enumset1)).

tff(f_39,axiom,(
    ! [A,B] : k2_enumset1(A,A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_enumset1)).

tff(f_31,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(B,C,A,D) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l123_enumset1)).

tff(c_22,plain,(
    r1_tarski(k2_tarski('#skF_1','#skF_2'),k1_tarski('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_38,plain,(
    ! [C_27,A_28,B_29] :
      ( C_27 = A_28
      | ~ r1_tarski(k2_tarski(A_28,B_29),k1_tarski(C_27)) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_45,plain,(
    '#skF_3' = '#skF_1' ),
    inference(resolution,[status(thm)],[c_22,c_38])).

tff(c_20,plain,(
    k2_tarski('#skF_1','#skF_2') != k1_tarski('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_47,plain,(
    k2_tarski('#skF_1','#skF_2') != k1_tarski('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_45,c_20])).

tff(c_10,plain,(
    ! [A_15] : k2_tarski(A_15,A_15) = k1_tarski(A_15) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_302,plain,(
    ! [A_48,B_49,C_50,D_51] : k2_xboole_0(k2_tarski(A_48,B_49),k2_tarski(C_50,D_51)) = k2_enumset1(A_48,B_49,C_50,D_51) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_1563,plain,(
    ! [A_82,B_83,A_84] : k2_xboole_0(k2_tarski(A_82,B_83),k1_tarski(A_84)) = k2_enumset1(A_82,B_83,A_84,A_84) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_302])).

tff(c_33,plain,(
    ! [A_25,B_26] :
      ( k2_xboole_0(A_25,B_26) = B_26
      | ~ r1_tarski(A_25,B_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_37,plain,(
    k2_xboole_0(k2_tarski('#skF_1','#skF_2'),k1_tarski('#skF_3')) = k1_tarski('#skF_3') ),
    inference(resolution,[status(thm)],[c_22,c_33])).

tff(c_61,plain,(
    k2_xboole_0(k2_tarski('#skF_1','#skF_2'),k1_tarski('#skF_1')) = k1_tarski('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_45,c_45,c_37])).

tff(c_1634,plain,(
    k2_enumset1('#skF_1','#skF_2','#skF_1','#skF_1') = k1_tarski('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_1563,c_61])).

tff(c_93,plain,(
    ! [C_36,B_37,D_38,A_39] : k2_enumset1(C_36,B_37,D_38,A_39) = k2_enumset1(A_39,B_37,C_36,D_38) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_12,plain,(
    ! [A_16,B_17] : k2_enumset1(A_16,A_16,A_16,B_17) = k2_tarski(A_16,B_17) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_189,plain,(
    ! [C_44,D_45] : k2_enumset1(C_44,C_44,D_45,C_44) = k2_tarski(C_44,D_45) ),
    inference(superposition,[status(thm),theory(equality)],[c_93,c_12])).

tff(c_4,plain,(
    ! [B_4,C_5,A_3,D_6] : k2_enumset1(B_4,C_5,A_3,D_6) = k2_enumset1(A_3,B_4,C_5,D_6) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_198,plain,(
    ! [C_44,D_45] : k2_enumset1(C_44,D_45,C_44,C_44) = k2_tarski(C_44,D_45) ),
    inference(superposition,[status(thm),theory(equality)],[c_189,c_4])).

tff(c_1755,plain,(
    k2_tarski('#skF_1','#skF_2') = k1_tarski('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_1634,c_198])).

tff(c_1789,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_47,c_1755])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n021.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 20:59:04 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.53/1.59  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.53/1.59  
% 3.53/1.59  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.53/1.60  %$ r1_tarski > k2_enumset1 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1
% 3.53/1.60  
% 3.53/1.60  %Foreground sorts:
% 3.53/1.60  
% 3.53/1.60  
% 3.53/1.60  %Background operators:
% 3.53/1.60  
% 3.53/1.60  
% 3.53/1.60  %Foreground operators:
% 3.53/1.60  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.53/1.60  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.53/1.60  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.53/1.60  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.53/1.60  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.53/1.60  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.53/1.60  tff('#skF_2', type, '#skF_2': $i).
% 3.53/1.60  tff('#skF_3', type, '#skF_3': $i).
% 3.53/1.60  tff('#skF_1', type, '#skF_1': $i).
% 3.53/1.60  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.53/1.60  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.53/1.60  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.53/1.60  
% 3.53/1.61  tff(f_53, negated_conjecture, ~(![A, B, C]: (r1_tarski(k2_tarski(A, B), k1_tarski(C)) => (k2_tarski(A, B) = k1_tarski(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t27_zfmisc_1)).
% 3.53/1.61  tff(f_48, axiom, (![A, B, C]: (r1_tarski(k2_tarski(A, B), k1_tarski(C)) => (A = C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t26_zfmisc_1)).
% 3.53/1.61  tff(f_37, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 3.53/1.61  tff(f_35, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k2_tarski(A, B), k2_tarski(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t45_enumset1)).
% 3.53/1.61  tff(f_29, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 3.53/1.61  tff(f_33, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(C, B, D, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t117_enumset1)).
% 3.53/1.61  tff(f_39, axiom, (![A, B]: (k2_enumset1(A, A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t77_enumset1)).
% 3.53/1.61  tff(f_31, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(B, C, A, D))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l123_enumset1)).
% 3.53/1.61  tff(c_22, plain, (r1_tarski(k2_tarski('#skF_1', '#skF_2'), k1_tarski('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.53/1.61  tff(c_38, plain, (![C_27, A_28, B_29]: (C_27=A_28 | ~r1_tarski(k2_tarski(A_28, B_29), k1_tarski(C_27)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.53/1.61  tff(c_45, plain, ('#skF_3'='#skF_1'), inference(resolution, [status(thm)], [c_22, c_38])).
% 3.53/1.61  tff(c_20, plain, (k2_tarski('#skF_1', '#skF_2')!=k1_tarski('#skF_3')), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.53/1.61  tff(c_47, plain, (k2_tarski('#skF_1', '#skF_2')!=k1_tarski('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_45, c_20])).
% 3.53/1.61  tff(c_10, plain, (![A_15]: (k2_tarski(A_15, A_15)=k1_tarski(A_15))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.53/1.61  tff(c_302, plain, (![A_48, B_49, C_50, D_51]: (k2_xboole_0(k2_tarski(A_48, B_49), k2_tarski(C_50, D_51))=k2_enumset1(A_48, B_49, C_50, D_51))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.53/1.61  tff(c_1563, plain, (![A_82, B_83, A_84]: (k2_xboole_0(k2_tarski(A_82, B_83), k1_tarski(A_84))=k2_enumset1(A_82, B_83, A_84, A_84))), inference(superposition, [status(thm), theory('equality')], [c_10, c_302])).
% 3.53/1.61  tff(c_33, plain, (![A_25, B_26]: (k2_xboole_0(A_25, B_26)=B_26 | ~r1_tarski(A_25, B_26))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.53/1.61  tff(c_37, plain, (k2_xboole_0(k2_tarski('#skF_1', '#skF_2'), k1_tarski('#skF_3'))=k1_tarski('#skF_3')), inference(resolution, [status(thm)], [c_22, c_33])).
% 3.53/1.61  tff(c_61, plain, (k2_xboole_0(k2_tarski('#skF_1', '#skF_2'), k1_tarski('#skF_1'))=k1_tarski('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_45, c_45, c_37])).
% 3.53/1.61  tff(c_1634, plain, (k2_enumset1('#skF_1', '#skF_2', '#skF_1', '#skF_1')=k1_tarski('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_1563, c_61])).
% 3.53/1.61  tff(c_93, plain, (![C_36, B_37, D_38, A_39]: (k2_enumset1(C_36, B_37, D_38, A_39)=k2_enumset1(A_39, B_37, C_36, D_38))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.53/1.61  tff(c_12, plain, (![A_16, B_17]: (k2_enumset1(A_16, A_16, A_16, B_17)=k2_tarski(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.53/1.61  tff(c_189, plain, (![C_44, D_45]: (k2_enumset1(C_44, C_44, D_45, C_44)=k2_tarski(C_44, D_45))), inference(superposition, [status(thm), theory('equality')], [c_93, c_12])).
% 3.53/1.61  tff(c_4, plain, (![B_4, C_5, A_3, D_6]: (k2_enumset1(B_4, C_5, A_3, D_6)=k2_enumset1(A_3, B_4, C_5, D_6))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.53/1.61  tff(c_198, plain, (![C_44, D_45]: (k2_enumset1(C_44, D_45, C_44, C_44)=k2_tarski(C_44, D_45))), inference(superposition, [status(thm), theory('equality')], [c_189, c_4])).
% 3.53/1.61  tff(c_1755, plain, (k2_tarski('#skF_1', '#skF_2')=k1_tarski('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_1634, c_198])).
% 3.53/1.61  tff(c_1789, plain, $false, inference(negUnitSimplification, [status(thm)], [c_47, c_1755])).
% 3.53/1.61  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.53/1.61  
% 3.53/1.61  Inference rules
% 3.53/1.61  ----------------------
% 3.53/1.61  #Ref     : 0
% 3.53/1.61  #Sup     : 478
% 3.53/1.61  #Fact    : 0
% 3.53/1.61  #Define  : 0
% 3.53/1.61  #Split   : 0
% 3.53/1.61  #Chain   : 0
% 3.53/1.61  #Close   : 0
% 3.53/1.61  
% 3.53/1.61  Ordering : KBO
% 3.53/1.61  
% 3.53/1.61  Simplification rules
% 3.53/1.61  ----------------------
% 3.53/1.61  #Subsume      : 146
% 3.53/1.61  #Demod        : 163
% 3.53/1.61  #Tautology    : 200
% 3.53/1.61  #SimpNegUnit  : 1
% 3.53/1.61  #BackRed      : 2
% 3.53/1.61  
% 3.53/1.61  #Partial instantiations: 0
% 3.53/1.61  #Strategies tried      : 1
% 3.53/1.61  
% 3.53/1.61  Timing (in seconds)
% 3.53/1.61  ----------------------
% 3.53/1.61  Preprocessing        : 0.30
% 3.53/1.61  Parsing              : 0.16
% 3.53/1.61  CNF conversion       : 0.02
% 3.53/1.61  Main loop            : 0.56
% 3.53/1.61  Inferencing          : 0.19
% 3.53/1.61  Reduction            : 0.25
% 3.53/1.61  Demodulation         : 0.21
% 3.53/1.61  BG Simplification    : 0.02
% 3.53/1.61  Subsumption          : 0.07
% 3.53/1.61  Abstraction          : 0.03
% 3.53/1.61  MUC search           : 0.00
% 3.53/1.61  Cooper               : 0.00
% 3.53/1.61  Total                : 0.88
% 3.53/1.61  Index Insertion      : 0.00
% 3.53/1.61  Index Deletion       : 0.00
% 3.53/1.61  Index Matching       : 0.00
% 3.53/1.61  BG Taut test         : 0.00
%------------------------------------------------------------------------------
