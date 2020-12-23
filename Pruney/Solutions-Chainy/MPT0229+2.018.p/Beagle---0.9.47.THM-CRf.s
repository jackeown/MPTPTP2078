%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:48:55 EST 2020

% Result     : Theorem 2.11s
% Output     : CNFRefutation 2.11s
% Verified   : 
% Statistics : Number of formulae       :   47 (  60 expanded)
%              Number of leaves         :   25 (  33 expanded)
%              Depth                    :    9
%              Number of atoms          :   45 (  65 expanded)
%              Number of equality atoms :   33 (  49 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i ) > $i )).

tff(f_65,negated_conjecture,(
    ~ ! [A,B] :
        ( r1_tarski(k1_tarski(A),k1_tarski(B))
       => A = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_zfmisc_1)).

tff(f_50,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_48,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_52,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_46,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k1_enumset1(A,B,C),k1_tarski(D)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_enumset1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_44,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

tff(c_44,plain,(
    '#skF_3' != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_32,plain,(
    ! [A_15,B_16] : k1_enumset1(A_15,A_15,B_16) = k2_tarski(A_15,B_16) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_30,plain,(
    ! [A_14] : k2_tarski(A_14,A_14) = k1_tarski(A_14) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_34,plain,(
    ! [A_17,B_18,C_19] : k2_enumset1(A_17,A_17,B_18,C_19) = k1_enumset1(A_17,B_18,C_19) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_154,plain,(
    ! [A_77,B_78,C_79,D_80] : k2_xboole_0(k1_enumset1(A_77,B_78,C_79),k1_tarski(D_80)) = k2_enumset1(A_77,B_78,C_79,D_80) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_163,plain,(
    ! [A_15,B_16,D_80] : k2_xboole_0(k2_tarski(A_15,B_16),k1_tarski(D_80)) = k2_enumset1(A_15,A_15,B_16,D_80) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_154])).

tff(c_176,plain,(
    ! [A_86,B_87,D_88] : k2_xboole_0(k2_tarski(A_86,B_87),k1_tarski(D_88)) = k1_enumset1(A_86,B_87,D_88) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_163])).

tff(c_185,plain,(
    ! [A_14,D_88] : k2_xboole_0(k1_tarski(A_14),k1_tarski(D_88)) = k1_enumset1(A_14,A_14,D_88) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_176])).

tff(c_189,plain,(
    ! [A_89,D_90] : k2_xboole_0(k1_tarski(A_89),k1_tarski(D_90)) = k2_tarski(A_89,D_90) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_185])).

tff(c_46,plain,(
    r1_tarski(k1_tarski('#skF_3'),k1_tarski('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_59,plain,(
    ! [A_52,B_53] :
      ( k2_xboole_0(A_52,B_53) = B_53
      | ~ r1_tarski(A_52,B_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_63,plain,(
    k2_xboole_0(k1_tarski('#skF_3'),k1_tarski('#skF_4')) = k1_tarski('#skF_4') ),
    inference(resolution,[status(thm)],[c_46,c_59])).

tff(c_195,plain,(
    k2_tarski('#skF_3','#skF_4') = k1_tarski('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_189,c_63])).

tff(c_64,plain,(
    ! [A_54,B_55] : k1_enumset1(A_54,A_54,B_55) = k2_tarski(A_54,B_55) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_10,plain,(
    ! [E_9,B_4,C_5] : r2_hidden(E_9,k1_enumset1(E_9,B_4,C_5)) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_76,plain,(
    ! [A_54,B_55] : r2_hidden(A_54,k2_tarski(A_54,B_55)) ),
    inference(superposition,[status(thm),theory(equality)],[c_64,c_10])).

tff(c_213,plain,(
    r2_hidden('#skF_3',k1_tarski('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_195,c_76])).

tff(c_115,plain,(
    ! [E_68,C_69,B_70,A_71] :
      ( E_68 = C_69
      | E_68 = B_70
      | E_68 = A_71
      | ~ r2_hidden(E_68,k1_enumset1(A_71,B_70,C_69)) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_134,plain,(
    ! [E_72,B_73,A_74] :
      ( E_72 = B_73
      | E_72 = A_74
      | E_72 = A_74
      | ~ r2_hidden(E_72,k2_tarski(A_74,B_73)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_115])).

tff(c_143,plain,(
    ! [E_72,A_14] :
      ( E_72 = A_14
      | E_72 = A_14
      | E_72 = A_14
      | ~ r2_hidden(E_72,k1_tarski(A_14)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_134])).

tff(c_224,plain,(
    '#skF_3' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_213,c_143])).

tff(c_228,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_44,c_44,c_224])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.35  % Computer   : n007.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 14:40:36 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.11/1.27  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.11/1.27  
% 2.11/1.27  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.11/1.28  %$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 2.11/1.28  
% 2.11/1.28  %Foreground sorts:
% 2.11/1.28  
% 2.11/1.28  
% 2.11/1.28  %Background operators:
% 2.11/1.28  
% 2.11/1.28  
% 2.11/1.28  %Foreground operators:
% 2.11/1.28  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.11/1.28  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.11/1.28  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.11/1.28  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.11/1.28  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.11/1.28  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.11/1.28  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.11/1.28  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 2.11/1.28  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.11/1.28  tff('#skF_3', type, '#skF_3': $i).
% 2.11/1.28  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.11/1.28  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.11/1.28  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.11/1.28  tff('#skF_4', type, '#skF_4': $i).
% 2.11/1.28  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.11/1.28  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.11/1.28  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.11/1.28  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 2.11/1.28  
% 2.11/1.29  tff(f_65, negated_conjecture, ~(![A, B]: (r1_tarski(k1_tarski(A), k1_tarski(B)) => (A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t24_zfmisc_1)).
% 2.11/1.29  tff(f_50, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 2.11/1.29  tff(f_48, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 2.11/1.29  tff(f_52, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 2.11/1.29  tff(f_46, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k1_enumset1(A, B, C), k1_tarski(D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_enumset1)).
% 2.11/1.29  tff(f_29, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 2.11/1.29  tff(f_44, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_enumset1)).
% 2.11/1.29  tff(c_44, plain, ('#skF_3'!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.11/1.29  tff(c_32, plain, (![A_15, B_16]: (k1_enumset1(A_15, A_15, B_16)=k2_tarski(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.11/1.29  tff(c_30, plain, (![A_14]: (k2_tarski(A_14, A_14)=k1_tarski(A_14))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.11/1.29  tff(c_34, plain, (![A_17, B_18, C_19]: (k2_enumset1(A_17, A_17, B_18, C_19)=k1_enumset1(A_17, B_18, C_19))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.11/1.29  tff(c_154, plain, (![A_77, B_78, C_79, D_80]: (k2_xboole_0(k1_enumset1(A_77, B_78, C_79), k1_tarski(D_80))=k2_enumset1(A_77, B_78, C_79, D_80))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.11/1.29  tff(c_163, plain, (![A_15, B_16, D_80]: (k2_xboole_0(k2_tarski(A_15, B_16), k1_tarski(D_80))=k2_enumset1(A_15, A_15, B_16, D_80))), inference(superposition, [status(thm), theory('equality')], [c_32, c_154])).
% 2.11/1.29  tff(c_176, plain, (![A_86, B_87, D_88]: (k2_xboole_0(k2_tarski(A_86, B_87), k1_tarski(D_88))=k1_enumset1(A_86, B_87, D_88))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_163])).
% 2.11/1.29  tff(c_185, plain, (![A_14, D_88]: (k2_xboole_0(k1_tarski(A_14), k1_tarski(D_88))=k1_enumset1(A_14, A_14, D_88))), inference(superposition, [status(thm), theory('equality')], [c_30, c_176])).
% 2.11/1.29  tff(c_189, plain, (![A_89, D_90]: (k2_xboole_0(k1_tarski(A_89), k1_tarski(D_90))=k2_tarski(A_89, D_90))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_185])).
% 2.11/1.29  tff(c_46, plain, (r1_tarski(k1_tarski('#skF_3'), k1_tarski('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.11/1.29  tff(c_59, plain, (![A_52, B_53]: (k2_xboole_0(A_52, B_53)=B_53 | ~r1_tarski(A_52, B_53))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.11/1.29  tff(c_63, plain, (k2_xboole_0(k1_tarski('#skF_3'), k1_tarski('#skF_4'))=k1_tarski('#skF_4')), inference(resolution, [status(thm)], [c_46, c_59])).
% 2.11/1.29  tff(c_195, plain, (k2_tarski('#skF_3', '#skF_4')=k1_tarski('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_189, c_63])).
% 2.11/1.29  tff(c_64, plain, (![A_54, B_55]: (k1_enumset1(A_54, A_54, B_55)=k2_tarski(A_54, B_55))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.11/1.29  tff(c_10, plain, (![E_9, B_4, C_5]: (r2_hidden(E_9, k1_enumset1(E_9, B_4, C_5)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.11/1.29  tff(c_76, plain, (![A_54, B_55]: (r2_hidden(A_54, k2_tarski(A_54, B_55)))), inference(superposition, [status(thm), theory('equality')], [c_64, c_10])).
% 2.11/1.29  tff(c_213, plain, (r2_hidden('#skF_3', k1_tarski('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_195, c_76])).
% 2.11/1.29  tff(c_115, plain, (![E_68, C_69, B_70, A_71]: (E_68=C_69 | E_68=B_70 | E_68=A_71 | ~r2_hidden(E_68, k1_enumset1(A_71, B_70, C_69)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.11/1.29  tff(c_134, plain, (![E_72, B_73, A_74]: (E_72=B_73 | E_72=A_74 | E_72=A_74 | ~r2_hidden(E_72, k2_tarski(A_74, B_73)))), inference(superposition, [status(thm), theory('equality')], [c_32, c_115])).
% 2.11/1.29  tff(c_143, plain, (![E_72, A_14]: (E_72=A_14 | E_72=A_14 | E_72=A_14 | ~r2_hidden(E_72, k1_tarski(A_14)))), inference(superposition, [status(thm), theory('equality')], [c_30, c_134])).
% 2.11/1.29  tff(c_224, plain, ('#skF_3'='#skF_4'), inference(resolution, [status(thm)], [c_213, c_143])).
% 2.11/1.29  tff(c_228, plain, $false, inference(negUnitSimplification, [status(thm)], [c_44, c_44, c_44, c_224])).
% 2.11/1.29  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.11/1.29  
% 2.11/1.29  Inference rules
% 2.11/1.29  ----------------------
% 2.11/1.29  #Ref     : 0
% 2.11/1.29  #Sup     : 43
% 2.11/1.29  #Fact    : 0
% 2.11/1.29  #Define  : 0
% 2.11/1.29  #Split   : 0
% 2.11/1.29  #Chain   : 0
% 2.11/1.29  #Close   : 0
% 2.11/1.29  
% 2.11/1.29  Ordering : KBO
% 2.11/1.29  
% 2.11/1.29  Simplification rules
% 2.11/1.29  ----------------------
% 2.11/1.29  #Subsume      : 0
% 2.11/1.29  #Demod        : 6
% 2.11/1.29  #Tautology    : 29
% 2.11/1.29  #SimpNegUnit  : 1
% 2.11/1.29  #BackRed      : 0
% 2.11/1.29  
% 2.11/1.29  #Partial instantiations: 0
% 2.11/1.29  #Strategies tried      : 1
% 2.11/1.29  
% 2.11/1.29  Timing (in seconds)
% 2.11/1.29  ----------------------
% 2.11/1.29  Preprocessing        : 0.30
% 2.11/1.29  Parsing              : 0.15
% 2.11/1.29  CNF conversion       : 0.02
% 2.11/1.29  Main loop            : 0.15
% 2.11/1.29  Inferencing          : 0.05
% 2.11/1.29  Reduction            : 0.05
% 2.11/1.29  Demodulation         : 0.04
% 2.11/1.29  BG Simplification    : 0.01
% 2.11/1.29  Subsumption          : 0.03
% 2.11/1.29  Abstraction          : 0.01
% 2.11/1.29  MUC search           : 0.00
% 2.11/1.29  Cooper               : 0.00
% 2.11/1.29  Total                : 0.48
% 2.11/1.29  Index Insertion      : 0.00
% 2.11/1.29  Index Deletion       : 0.00
% 2.11/1.29  Index Matching       : 0.00
% 2.11/1.29  BG Taut test         : 0.00
%------------------------------------------------------------------------------
