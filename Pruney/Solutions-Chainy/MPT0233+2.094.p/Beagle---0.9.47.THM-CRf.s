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
% DateTime   : Thu Dec  3 09:49:33 EST 2020

% Result     : Theorem 2.67s
% Output     : CNFRefutation 2.90s
% Verified   : 
% Statistics : Number of formulae       :   47 (  52 expanded)
%              Number of leaves         :   26 (  30 expanded)
%              Depth                    :    8
%              Number of atoms          :   43 (  55 expanded)
%              Number of equality atoms :   19 (  25 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

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

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(f_78,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ~ ( r1_tarski(k2_tarski(A,B),k2_tarski(C,D))
          & A != C
          & A != D ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_zfmisc_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_59,axiom,(
    ! [A,B] : k3_xboole_0(k1_tarski(A),k2_tarski(A,B)) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_zfmisc_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_43,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_xboole_0(A,B),C)
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).

tff(f_68,axiom,(
    ! [A,B,C] :
      ~ ( r1_tarski(k1_tarski(A),k2_tarski(B,C))
        & A != B
        & A != C ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_zfmisc_1)).

tff(c_36,plain,(
    '#skF_3' != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_34,plain,(
    '#skF_1' != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_38,plain,(
    r1_tarski(k2_tarski('#skF_1','#skF_2'),k2_tarski('#skF_3','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_109,plain,(
    ! [A_55,B_56] :
      ( k2_xboole_0(A_55,B_56) = B_56
      | ~ r1_tarski(A_55,B_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_122,plain,(
    k2_xboole_0(k2_tarski('#skF_1','#skF_2'),k2_tarski('#skF_3','#skF_4')) = k2_tarski('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_38,c_109])).

tff(c_436,plain,(
    ! [A_90,B_91] : k3_xboole_0(k1_tarski(A_90),k2_tarski(A_90,B_91)) = k1_tarski(A_90) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_51,plain,(
    ! [B_49,A_50] : k3_xboole_0(B_49,A_50) = k3_xboole_0(A_50,B_49) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_14,plain,(
    ! [A_10,B_11] : r1_tarski(k3_xboole_0(A_10,B_11),A_10) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_66,plain,(
    ! [B_49,A_50] : r1_tarski(k3_xboole_0(B_49,A_50),A_50) ),
    inference(superposition,[status(thm),theory(equality)],[c_51,c_14])).

tff(c_123,plain,(
    ! [B_49,A_50] : k2_xboole_0(k3_xboole_0(B_49,A_50),A_50) = A_50 ),
    inference(resolution,[status(thm)],[c_66,c_109])).

tff(c_8,plain,(
    ! [B_4] : r1_tarski(B_4,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_178,plain,(
    ! [A_62,C_63,B_64] :
      ( r1_tarski(A_62,C_63)
      | ~ r1_tarski(k2_xboole_0(A_62,B_64),C_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_193,plain,(
    ! [A_65,B_66] : r1_tarski(A_65,k2_xboole_0(A_65,B_66)) ),
    inference(resolution,[status(thm)],[c_8,c_178])).

tff(c_10,plain,(
    ! [A_5,C_7,B_6] :
      ( r1_tarski(A_5,C_7)
      | ~ r1_tarski(k2_xboole_0(A_5,B_6),C_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_216,plain,(
    ! [A_67,B_68,B_69] : r1_tarski(A_67,k2_xboole_0(k2_xboole_0(A_67,B_68),B_69)) ),
    inference(resolution,[status(thm)],[c_193,c_10])).

tff(c_226,plain,(
    ! [B_49,A_50,B_69] : r1_tarski(k3_xboole_0(B_49,A_50),k2_xboole_0(A_50,B_69)) ),
    inference(superposition,[status(thm),theory(equality)],[c_123,c_216])).

tff(c_688,plain,(
    ! [A_108,B_109,B_110] : r1_tarski(k1_tarski(A_108),k2_xboole_0(k2_tarski(A_108,B_109),B_110)) ),
    inference(superposition,[status(thm),theory(equality)],[c_436,c_226])).

tff(c_700,plain,(
    r1_tarski(k1_tarski('#skF_1'),k2_tarski('#skF_3','#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_122,c_688])).

tff(c_881,plain,(
    ! [C_120,A_121,B_122] :
      ( C_120 = A_121
      | B_122 = A_121
      | ~ r1_tarski(k1_tarski(A_121),k2_tarski(B_122,C_120)) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_884,plain,
    ( '#skF_1' = '#skF_4'
    | '#skF_3' = '#skF_1' ),
    inference(resolution,[status(thm)],[c_700,c_881])).

tff(c_894,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_34,c_884])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:12:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.67/1.40  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.67/1.41  
% 2.67/1.41  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.67/1.41  %$ r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.67/1.41  
% 2.67/1.41  %Foreground sorts:
% 2.67/1.41  
% 2.67/1.41  
% 2.67/1.41  %Background operators:
% 2.67/1.41  
% 2.67/1.41  
% 2.67/1.41  %Foreground operators:
% 2.67/1.41  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.67/1.41  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.67/1.41  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.67/1.41  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.67/1.41  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.67/1.41  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.67/1.41  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.67/1.41  tff('#skF_2', type, '#skF_2': $i).
% 2.67/1.41  tff('#skF_3', type, '#skF_3': $i).
% 2.67/1.41  tff('#skF_1', type, '#skF_1': $i).
% 2.67/1.41  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.67/1.41  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.67/1.41  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.67/1.41  tff('#skF_4', type, '#skF_4': $i).
% 2.67/1.41  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.67/1.41  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.67/1.41  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.67/1.41  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.67/1.41  
% 2.90/1.42  tff(f_78, negated_conjecture, ~(![A, B, C, D]: ~((r1_tarski(k2_tarski(A, B), k2_tarski(C, D)) & ~(A = C)) & ~(A = D))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_zfmisc_1)).
% 2.90/1.42  tff(f_41, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 2.90/1.42  tff(f_59, axiom, (![A, B]: (k3_xboole_0(k1_tarski(A), k2_tarski(A, B)) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t19_zfmisc_1)).
% 2.90/1.42  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 2.90/1.42  tff(f_43, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 2.90/1.42  tff(f_33, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.90/1.42  tff(f_37, axiom, (![A, B, C]: (r1_tarski(k2_xboole_0(A, B), C) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_xboole_1)).
% 2.90/1.42  tff(f_68, axiom, (![A, B, C]: ~((r1_tarski(k1_tarski(A), k2_tarski(B, C)) & ~(A = B)) & ~(A = C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t25_zfmisc_1)).
% 2.90/1.42  tff(c_36, plain, ('#skF_3'!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.90/1.42  tff(c_34, plain, ('#skF_1'!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.90/1.42  tff(c_38, plain, (r1_tarski(k2_tarski('#skF_1', '#skF_2'), k2_tarski('#skF_3', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.90/1.42  tff(c_109, plain, (![A_55, B_56]: (k2_xboole_0(A_55, B_56)=B_56 | ~r1_tarski(A_55, B_56))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.90/1.42  tff(c_122, plain, (k2_xboole_0(k2_tarski('#skF_1', '#skF_2'), k2_tarski('#skF_3', '#skF_4'))=k2_tarski('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_38, c_109])).
% 2.90/1.42  tff(c_436, plain, (![A_90, B_91]: (k3_xboole_0(k1_tarski(A_90), k2_tarski(A_90, B_91))=k1_tarski(A_90))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.90/1.42  tff(c_51, plain, (![B_49, A_50]: (k3_xboole_0(B_49, A_50)=k3_xboole_0(A_50, B_49))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.90/1.42  tff(c_14, plain, (![A_10, B_11]: (r1_tarski(k3_xboole_0(A_10, B_11), A_10))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.90/1.42  tff(c_66, plain, (![B_49, A_50]: (r1_tarski(k3_xboole_0(B_49, A_50), A_50))), inference(superposition, [status(thm), theory('equality')], [c_51, c_14])).
% 2.90/1.42  tff(c_123, plain, (![B_49, A_50]: (k2_xboole_0(k3_xboole_0(B_49, A_50), A_50)=A_50)), inference(resolution, [status(thm)], [c_66, c_109])).
% 2.90/1.42  tff(c_8, plain, (![B_4]: (r1_tarski(B_4, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.90/1.42  tff(c_178, plain, (![A_62, C_63, B_64]: (r1_tarski(A_62, C_63) | ~r1_tarski(k2_xboole_0(A_62, B_64), C_63))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.90/1.42  tff(c_193, plain, (![A_65, B_66]: (r1_tarski(A_65, k2_xboole_0(A_65, B_66)))), inference(resolution, [status(thm)], [c_8, c_178])).
% 2.90/1.42  tff(c_10, plain, (![A_5, C_7, B_6]: (r1_tarski(A_5, C_7) | ~r1_tarski(k2_xboole_0(A_5, B_6), C_7))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.90/1.42  tff(c_216, plain, (![A_67, B_68, B_69]: (r1_tarski(A_67, k2_xboole_0(k2_xboole_0(A_67, B_68), B_69)))), inference(resolution, [status(thm)], [c_193, c_10])).
% 2.90/1.42  tff(c_226, plain, (![B_49, A_50, B_69]: (r1_tarski(k3_xboole_0(B_49, A_50), k2_xboole_0(A_50, B_69)))), inference(superposition, [status(thm), theory('equality')], [c_123, c_216])).
% 2.90/1.42  tff(c_688, plain, (![A_108, B_109, B_110]: (r1_tarski(k1_tarski(A_108), k2_xboole_0(k2_tarski(A_108, B_109), B_110)))), inference(superposition, [status(thm), theory('equality')], [c_436, c_226])).
% 2.90/1.42  tff(c_700, plain, (r1_tarski(k1_tarski('#skF_1'), k2_tarski('#skF_3', '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_122, c_688])).
% 2.90/1.42  tff(c_881, plain, (![C_120, A_121, B_122]: (C_120=A_121 | B_122=A_121 | ~r1_tarski(k1_tarski(A_121), k2_tarski(B_122, C_120)))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.90/1.42  tff(c_884, plain, ('#skF_1'='#skF_4' | '#skF_3'='#skF_1'), inference(resolution, [status(thm)], [c_700, c_881])).
% 2.90/1.42  tff(c_894, plain, $false, inference(negUnitSimplification, [status(thm)], [c_36, c_34, c_884])).
% 2.90/1.42  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.90/1.42  
% 2.90/1.42  Inference rules
% 2.90/1.42  ----------------------
% 2.90/1.42  #Ref     : 0
% 2.90/1.42  #Sup     : 214
% 2.90/1.42  #Fact    : 0
% 2.90/1.42  #Define  : 0
% 2.90/1.42  #Split   : 1
% 2.90/1.42  #Chain   : 0
% 2.90/1.42  #Close   : 0
% 2.90/1.42  
% 2.90/1.42  Ordering : KBO
% 2.90/1.42  
% 2.90/1.42  Simplification rules
% 2.90/1.42  ----------------------
% 2.90/1.42  #Subsume      : 5
% 2.90/1.42  #Demod        : 89
% 2.90/1.42  #Tautology    : 125
% 2.90/1.42  #SimpNegUnit  : 1
% 2.90/1.42  #BackRed      : 0
% 2.90/1.42  
% 2.90/1.42  #Partial instantiations: 0
% 2.90/1.42  #Strategies tried      : 1
% 2.90/1.42  
% 2.90/1.42  Timing (in seconds)
% 2.90/1.42  ----------------------
% 2.90/1.42  Preprocessing        : 0.33
% 2.90/1.43  Parsing              : 0.17
% 2.90/1.43  CNF conversion       : 0.02
% 2.90/1.43  Main loop            : 0.34
% 2.90/1.43  Inferencing          : 0.11
% 2.90/1.43  Reduction            : 0.13
% 2.90/1.43  Demodulation         : 0.10
% 2.90/1.43  BG Simplification    : 0.02
% 2.90/1.43  Subsumption          : 0.06
% 2.90/1.43  Abstraction          : 0.02
% 2.90/1.43  MUC search           : 0.00
% 2.90/1.43  Cooper               : 0.00
% 2.90/1.43  Total                : 0.69
% 2.90/1.43  Index Insertion      : 0.00
% 2.90/1.43  Index Deletion       : 0.00
% 2.90/1.43  Index Matching       : 0.00
% 2.90/1.43  BG Taut test         : 0.00
%------------------------------------------------------------------------------
