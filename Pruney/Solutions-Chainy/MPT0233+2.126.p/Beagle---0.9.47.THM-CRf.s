%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:49:37 EST 2020

% Result     : Theorem 2.19s
% Output     : CNFRefutation 2.19s
% Verified   : 
% Statistics : Number of formulae       :   51 (  55 expanded)
%              Number of leaves         :   28 (  31 expanded)
%              Depth                    :    8
%              Number of atoms          :   48 (  56 expanded)
%              Number of equality atoms :   25 (  31 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

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

tff(f_72,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ~ ( r1_tarski(k2_tarski(A,B),k2_tarski(C,D))
          & A != C
          & A != D ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_zfmisc_1)).

tff(f_41,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_43,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_45,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_39,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k1_enumset1(A,B,C),k1_tarski(D)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_enumset1)).

tff(f_37,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k3_xboole_0(B,C))
     => r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_xboole_1)).

tff(f_62,axiom,(
    ! [A,B,C] :
      ~ ( r1_tarski(k1_tarski(A),k2_tarski(B,C))
        & A != B
        & A != C ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_zfmisc_1)).

tff(c_30,plain,(
    '#skF_3' != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_28,plain,(
    '#skF_1' != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_12,plain,(
    ! [A_14] : k2_tarski(A_14,A_14) = k1_tarski(A_14) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_14,plain,(
    ! [A_15,B_16] : k1_enumset1(A_15,A_15,B_16) = k2_tarski(A_15,B_16) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_16,plain,(
    ! [A_17,B_18,C_19] : k2_enumset1(A_17,A_17,B_18,C_19) = k1_enumset1(A_17,B_18,C_19) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_255,plain,(
    ! [A_85,B_86,C_87,D_88] : k2_xboole_0(k1_enumset1(A_85,B_86,C_87),k1_tarski(D_88)) = k2_enumset1(A_85,B_86,C_87,D_88) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_8,plain,(
    ! [A_8,B_9] : r1_tarski(A_8,k2_xboole_0(A_8,B_9)) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_283,plain,(
    ! [A_89,B_90,C_91,D_92] : r1_tarski(k1_enumset1(A_89,B_90,C_91),k2_enumset1(A_89,B_90,C_91,D_92)) ),
    inference(superposition,[status(thm),theory(equality)],[c_255,c_8])).

tff(c_289,plain,(
    ! [A_17,B_18,C_19] : r1_tarski(k1_enumset1(A_17,A_17,B_18),k1_enumset1(A_17,B_18,C_19)) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_283])).

tff(c_296,plain,(
    ! [A_93,B_94,C_95] : r1_tarski(k2_tarski(A_93,B_94),k1_enumset1(A_93,B_94,C_95)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_289])).

tff(c_302,plain,(
    ! [A_15,B_16] : r1_tarski(k2_tarski(A_15,A_15),k2_tarski(A_15,B_16)) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_296])).

tff(c_309,plain,(
    ! [A_96,B_97] : r1_tarski(k1_tarski(A_96),k2_tarski(A_96,B_97)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_302])).

tff(c_32,plain,(
    r1_tarski(k2_tarski('#skF_1','#skF_2'),k2_tarski('#skF_3','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_76,plain,(
    ! [A_50,B_51] :
      ( k3_xboole_0(A_50,B_51) = A_50
      | ~ r1_tarski(A_50,B_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_83,plain,(
    k3_xboole_0(k2_tarski('#skF_1','#skF_2'),k2_tarski('#skF_3','#skF_4')) = k2_tarski('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_32,c_76])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_107,plain,(
    ! [A_56,B_57,C_58] :
      ( r1_tarski(A_56,B_57)
      | ~ r1_tarski(A_56,k3_xboole_0(B_57,C_58)) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_120,plain,(
    ! [A_59,A_60,B_61] :
      ( r1_tarski(A_59,A_60)
      | ~ r1_tarski(A_59,k3_xboole_0(B_61,A_60)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_107])).

tff(c_235,plain,(
    ! [A_79] :
      ( r1_tarski(A_79,k2_tarski('#skF_3','#skF_4'))
      | ~ r1_tarski(A_79,k2_tarski('#skF_1','#skF_2')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_83,c_120])).

tff(c_26,plain,(
    ! [C_44,A_42,B_43] :
      ( C_44 = A_42
      | B_43 = A_42
      | ~ r1_tarski(k1_tarski(A_42),k2_tarski(B_43,C_44)) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_243,plain,(
    ! [A_42] :
      ( A_42 = '#skF_4'
      | A_42 = '#skF_3'
      | ~ r1_tarski(k1_tarski(A_42),k2_tarski('#skF_1','#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_235,c_26])).

tff(c_313,plain,
    ( '#skF_1' = '#skF_4'
    | '#skF_3' = '#skF_1' ),
    inference(resolution,[status(thm)],[c_309,c_243])).

tff(c_326,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_28,c_313])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n020.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 15:13:37 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.19/1.26  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.19/1.26  
% 2.19/1.26  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.19/1.27  %$ r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.19/1.27  
% 2.19/1.27  %Foreground sorts:
% 2.19/1.27  
% 2.19/1.27  
% 2.19/1.27  %Background operators:
% 2.19/1.27  
% 2.19/1.27  
% 2.19/1.27  %Foreground operators:
% 2.19/1.27  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.19/1.27  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.19/1.27  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.19/1.27  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.19/1.27  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.19/1.27  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.19/1.27  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.19/1.27  tff('#skF_2', type, '#skF_2': $i).
% 2.19/1.27  tff('#skF_3', type, '#skF_3': $i).
% 2.19/1.27  tff('#skF_1', type, '#skF_1': $i).
% 2.19/1.27  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.19/1.27  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.19/1.27  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.19/1.27  tff('#skF_4', type, '#skF_4': $i).
% 2.19/1.27  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.19/1.27  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.19/1.27  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.19/1.27  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.19/1.27  
% 2.19/1.28  tff(f_72, negated_conjecture, ~(![A, B, C, D]: ~((r1_tarski(k2_tarski(A, B), k2_tarski(C, D)) & ~(A = C)) & ~(A = D))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_zfmisc_1)).
% 2.19/1.28  tff(f_41, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 2.19/1.28  tff(f_43, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 2.19/1.28  tff(f_45, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 2.19/1.28  tff(f_39, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k1_enumset1(A, B, C), k1_tarski(D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_enumset1)).
% 2.19/1.28  tff(f_37, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 2.19/1.28  tff(f_35, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 2.19/1.28  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 2.19/1.28  tff(f_31, axiom, (![A, B, C]: (r1_tarski(A, k3_xboole_0(B, C)) => r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t18_xboole_1)).
% 2.19/1.28  tff(f_62, axiom, (![A, B, C]: ~((r1_tarski(k1_tarski(A), k2_tarski(B, C)) & ~(A = B)) & ~(A = C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t25_zfmisc_1)).
% 2.19/1.28  tff(c_30, plain, ('#skF_3'!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.19/1.28  tff(c_28, plain, ('#skF_1'!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.19/1.28  tff(c_12, plain, (![A_14]: (k2_tarski(A_14, A_14)=k1_tarski(A_14))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.19/1.28  tff(c_14, plain, (![A_15, B_16]: (k1_enumset1(A_15, A_15, B_16)=k2_tarski(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.19/1.28  tff(c_16, plain, (![A_17, B_18, C_19]: (k2_enumset1(A_17, A_17, B_18, C_19)=k1_enumset1(A_17, B_18, C_19))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.19/1.28  tff(c_255, plain, (![A_85, B_86, C_87, D_88]: (k2_xboole_0(k1_enumset1(A_85, B_86, C_87), k1_tarski(D_88))=k2_enumset1(A_85, B_86, C_87, D_88))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.19/1.28  tff(c_8, plain, (![A_8, B_9]: (r1_tarski(A_8, k2_xboole_0(A_8, B_9)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.19/1.28  tff(c_283, plain, (![A_89, B_90, C_91, D_92]: (r1_tarski(k1_enumset1(A_89, B_90, C_91), k2_enumset1(A_89, B_90, C_91, D_92)))), inference(superposition, [status(thm), theory('equality')], [c_255, c_8])).
% 2.19/1.28  tff(c_289, plain, (![A_17, B_18, C_19]: (r1_tarski(k1_enumset1(A_17, A_17, B_18), k1_enumset1(A_17, B_18, C_19)))), inference(superposition, [status(thm), theory('equality')], [c_16, c_283])).
% 2.19/1.28  tff(c_296, plain, (![A_93, B_94, C_95]: (r1_tarski(k2_tarski(A_93, B_94), k1_enumset1(A_93, B_94, C_95)))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_289])).
% 2.19/1.28  tff(c_302, plain, (![A_15, B_16]: (r1_tarski(k2_tarski(A_15, A_15), k2_tarski(A_15, B_16)))), inference(superposition, [status(thm), theory('equality')], [c_14, c_296])).
% 2.19/1.28  tff(c_309, plain, (![A_96, B_97]: (r1_tarski(k1_tarski(A_96), k2_tarski(A_96, B_97)))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_302])).
% 2.19/1.28  tff(c_32, plain, (r1_tarski(k2_tarski('#skF_1', '#skF_2'), k2_tarski('#skF_3', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.19/1.28  tff(c_76, plain, (![A_50, B_51]: (k3_xboole_0(A_50, B_51)=A_50 | ~r1_tarski(A_50, B_51))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.19/1.28  tff(c_83, plain, (k3_xboole_0(k2_tarski('#skF_1', '#skF_2'), k2_tarski('#skF_3', '#skF_4'))=k2_tarski('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_32, c_76])).
% 2.19/1.28  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.19/1.28  tff(c_107, plain, (![A_56, B_57, C_58]: (r1_tarski(A_56, B_57) | ~r1_tarski(A_56, k3_xboole_0(B_57, C_58)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.19/1.28  tff(c_120, plain, (![A_59, A_60, B_61]: (r1_tarski(A_59, A_60) | ~r1_tarski(A_59, k3_xboole_0(B_61, A_60)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_107])).
% 2.19/1.28  tff(c_235, plain, (![A_79]: (r1_tarski(A_79, k2_tarski('#skF_3', '#skF_4')) | ~r1_tarski(A_79, k2_tarski('#skF_1', '#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_83, c_120])).
% 2.19/1.28  tff(c_26, plain, (![C_44, A_42, B_43]: (C_44=A_42 | B_43=A_42 | ~r1_tarski(k1_tarski(A_42), k2_tarski(B_43, C_44)))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.19/1.28  tff(c_243, plain, (![A_42]: (A_42='#skF_4' | A_42='#skF_3' | ~r1_tarski(k1_tarski(A_42), k2_tarski('#skF_1', '#skF_2')))), inference(resolution, [status(thm)], [c_235, c_26])).
% 2.19/1.28  tff(c_313, plain, ('#skF_1'='#skF_4' | '#skF_3'='#skF_1'), inference(resolution, [status(thm)], [c_309, c_243])).
% 2.19/1.28  tff(c_326, plain, $false, inference(negUnitSimplification, [status(thm)], [c_30, c_28, c_313])).
% 2.19/1.28  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.19/1.28  
% 2.19/1.28  Inference rules
% 2.19/1.28  ----------------------
% 2.19/1.28  #Ref     : 0
% 2.19/1.28  #Sup     : 74
% 2.19/1.28  #Fact    : 0
% 2.19/1.28  #Define  : 0
% 2.19/1.28  #Split   : 0
% 2.19/1.28  #Chain   : 0
% 2.19/1.28  #Close   : 0
% 2.19/1.28  
% 2.19/1.28  Ordering : KBO
% 2.19/1.28  
% 2.19/1.28  Simplification rules
% 2.19/1.28  ----------------------
% 2.19/1.28  #Subsume      : 10
% 2.19/1.28  #Demod        : 5
% 2.19/1.28  #Tautology    : 32
% 2.19/1.28  #SimpNegUnit  : 1
% 2.19/1.28  #BackRed      : 0
% 2.19/1.28  
% 2.19/1.28  #Partial instantiations: 0
% 2.19/1.28  #Strategies tried      : 1
% 2.19/1.28  
% 2.19/1.28  Timing (in seconds)
% 2.19/1.28  ----------------------
% 2.19/1.28  Preprocessing        : 0.32
% 2.19/1.28  Parsing              : 0.17
% 2.19/1.28  CNF conversion       : 0.02
% 2.19/1.28  Main loop            : 0.21
% 2.19/1.28  Inferencing          : 0.08
% 2.19/1.28  Reduction            : 0.07
% 2.19/1.28  Demodulation         : 0.05
% 2.19/1.28  BG Simplification    : 0.02
% 2.19/1.28  Subsumption          : 0.04
% 2.19/1.28  Abstraction          : 0.01
% 2.19/1.28  MUC search           : 0.00
% 2.19/1.28  Cooper               : 0.00
% 2.19/1.28  Total                : 0.56
% 2.19/1.28  Index Insertion      : 0.00
% 2.19/1.28  Index Deletion       : 0.00
% 2.19/1.28  Index Matching       : 0.00
% 2.19/1.28  BG Taut test         : 0.00
%------------------------------------------------------------------------------
