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
% DateTime   : Thu Dec  3 09:48:17 EST 2020

% Result     : Theorem 2.86s
% Output     : CNFRefutation 2.86s
% Verified   : 
% Statistics : Number of formulae       :   49 (  56 expanded)
%              Number of leaves         :   28 (  33 expanded)
%              Depth                    :    7
%              Number of atoms          :   45 (  59 expanded)
%              Number of equality atoms :   33 (  46 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_4 > #skF_1

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

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i ) > $i )).

tff(f_75,negated_conjecture,(
    ~ ! [A,B] :
        ( k3_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
       => A = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_zfmisc_1)).

tff(f_29,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_35,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_56,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_xboole_0(k1_tarski(A),k1_tarski(B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_enumset1)).

tff(f_60,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_54,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

tff(f_58,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(c_54,plain,(
    '#skF_3' != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_56,plain,(
    k3_xboole_0(k1_tarski('#skF_3'),k1_tarski('#skF_4')) = k1_tarski('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_4,plain,(
    ! [B_4,A_3] : k3_xboole_0(B_4,A_3) = k3_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_160,plain,(
    k3_xboole_0(k1_tarski('#skF_4'),k1_tarski('#skF_3')) = k1_tarski('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_56,c_4])).

tff(c_8,plain,(
    ! [A_7,B_8] : r1_tarski(k3_xboole_0(A_7,B_8),A_7) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_207,plain,(
    ! [A_70,B_71] :
      ( k2_xboole_0(A_70,B_71) = B_71
      | ~ r1_tarski(A_70,B_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_281,plain,(
    ! [A_79,B_80] : k2_xboole_0(k3_xboole_0(A_79,B_80),A_79) = A_79 ),
    inference(resolution,[status(thm)],[c_8,c_207])).

tff(c_296,plain,(
    k2_xboole_0(k1_tarski('#skF_3'),k1_tarski('#skF_4')) = k1_tarski('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_160,c_281])).

tff(c_38,plain,(
    ! [A_20,B_21] : k2_xboole_0(k1_tarski(A_20),k1_tarski(B_21)) = k2_tarski(A_20,B_21) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_475,plain,(
    k2_tarski('#skF_3','#skF_4') = k1_tarski('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_296,c_38])).

tff(c_224,plain,(
    ! [A_72,B_73] : k1_enumset1(A_72,A_72,B_73) = k2_tarski(A_72,B_73) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_18,plain,(
    ! [E_19,A_13,C_15] : r2_hidden(E_19,k1_enumset1(A_13,E_19,C_15)) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_233,plain,(
    ! [A_72,B_73] : r2_hidden(A_72,k2_tarski(A_72,B_73)) ),
    inference(superposition,[status(thm),theory(equality)],[c_224,c_18])).

tff(c_497,plain,(
    r2_hidden('#skF_3',k1_tarski('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_475,c_233])).

tff(c_40,plain,(
    ! [A_22] : k2_tarski(A_22,A_22) = k1_tarski(A_22) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_42,plain,(
    ! [A_23,B_24] : k1_enumset1(A_23,A_23,B_24) = k2_tarski(A_23,B_24) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_616,plain,(
    ! [E_98,C_99,B_100,A_101] :
      ( E_98 = C_99
      | E_98 = B_100
      | E_98 = A_101
      | ~ r2_hidden(E_98,k1_enumset1(A_101,B_100,C_99)) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_815,plain,(
    ! [E_111,B_112,A_113] :
      ( E_111 = B_112
      | E_111 = A_113
      | E_111 = A_113
      | ~ r2_hidden(E_111,k2_tarski(A_113,B_112)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_616])).

tff(c_857,plain,(
    ! [E_115,A_116] :
      ( E_115 = A_116
      | E_115 = A_116
      | E_115 = A_116
      | ~ r2_hidden(E_115,k1_tarski(A_116)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_815])).

tff(c_860,plain,(
    '#skF_3' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_497,c_857])).

tff(c_867,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_54,c_54,c_860])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n012.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 18:02:22 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.86/1.41  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.86/1.41  
% 2.86/1.41  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.86/1.41  %$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 2.86/1.41  
% 2.86/1.41  %Foreground sorts:
% 2.86/1.41  
% 2.86/1.41  
% 2.86/1.41  %Background operators:
% 2.86/1.41  
% 2.86/1.41  
% 2.86/1.41  %Foreground operators:
% 2.86/1.41  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.86/1.41  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.86/1.41  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.86/1.41  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.86/1.41  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.86/1.41  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.86/1.41  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.86/1.41  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.86/1.41  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 2.86/1.41  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.86/1.41  tff('#skF_3', type, '#skF_3': $i).
% 2.86/1.41  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.86/1.41  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.86/1.41  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.86/1.41  tff('#skF_4', type, '#skF_4': $i).
% 2.86/1.41  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.86/1.41  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.86/1.41  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.86/1.41  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.86/1.41  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 2.86/1.41  
% 2.86/1.43  tff(f_75, negated_conjecture, ~(![A, B]: ((k3_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) => (A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t18_zfmisc_1)).
% 2.86/1.43  tff(f_29, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 2.86/1.43  tff(f_35, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 2.86/1.43  tff(f_33, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 2.86/1.43  tff(f_56, axiom, (![A, B]: (k2_tarski(A, B) = k2_xboole_0(k1_tarski(A), k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_enumset1)).
% 2.86/1.43  tff(f_60, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 2.86/1.43  tff(f_54, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_enumset1)).
% 2.86/1.43  tff(f_58, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 2.86/1.43  tff(c_54, plain, ('#skF_3'!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.86/1.43  tff(c_56, plain, (k3_xboole_0(k1_tarski('#skF_3'), k1_tarski('#skF_4'))=k1_tarski('#skF_3')), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.86/1.43  tff(c_4, plain, (![B_4, A_3]: (k3_xboole_0(B_4, A_3)=k3_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.86/1.43  tff(c_160, plain, (k3_xboole_0(k1_tarski('#skF_4'), k1_tarski('#skF_3'))=k1_tarski('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_56, c_4])).
% 2.86/1.43  tff(c_8, plain, (![A_7, B_8]: (r1_tarski(k3_xboole_0(A_7, B_8), A_7))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.86/1.43  tff(c_207, plain, (![A_70, B_71]: (k2_xboole_0(A_70, B_71)=B_71 | ~r1_tarski(A_70, B_71))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.86/1.43  tff(c_281, plain, (![A_79, B_80]: (k2_xboole_0(k3_xboole_0(A_79, B_80), A_79)=A_79)), inference(resolution, [status(thm)], [c_8, c_207])).
% 2.86/1.43  tff(c_296, plain, (k2_xboole_0(k1_tarski('#skF_3'), k1_tarski('#skF_4'))=k1_tarski('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_160, c_281])).
% 2.86/1.43  tff(c_38, plain, (![A_20, B_21]: (k2_xboole_0(k1_tarski(A_20), k1_tarski(B_21))=k2_tarski(A_20, B_21))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.86/1.43  tff(c_475, plain, (k2_tarski('#skF_3', '#skF_4')=k1_tarski('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_296, c_38])).
% 2.86/1.43  tff(c_224, plain, (![A_72, B_73]: (k1_enumset1(A_72, A_72, B_73)=k2_tarski(A_72, B_73))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.86/1.43  tff(c_18, plain, (![E_19, A_13, C_15]: (r2_hidden(E_19, k1_enumset1(A_13, E_19, C_15)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.86/1.43  tff(c_233, plain, (![A_72, B_73]: (r2_hidden(A_72, k2_tarski(A_72, B_73)))), inference(superposition, [status(thm), theory('equality')], [c_224, c_18])).
% 2.86/1.43  tff(c_497, plain, (r2_hidden('#skF_3', k1_tarski('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_475, c_233])).
% 2.86/1.43  tff(c_40, plain, (![A_22]: (k2_tarski(A_22, A_22)=k1_tarski(A_22))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.86/1.43  tff(c_42, plain, (![A_23, B_24]: (k1_enumset1(A_23, A_23, B_24)=k2_tarski(A_23, B_24))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.86/1.43  tff(c_616, plain, (![E_98, C_99, B_100, A_101]: (E_98=C_99 | E_98=B_100 | E_98=A_101 | ~r2_hidden(E_98, k1_enumset1(A_101, B_100, C_99)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.86/1.43  tff(c_815, plain, (![E_111, B_112, A_113]: (E_111=B_112 | E_111=A_113 | E_111=A_113 | ~r2_hidden(E_111, k2_tarski(A_113, B_112)))), inference(superposition, [status(thm), theory('equality')], [c_42, c_616])).
% 2.86/1.43  tff(c_857, plain, (![E_115, A_116]: (E_115=A_116 | E_115=A_116 | E_115=A_116 | ~r2_hidden(E_115, k1_tarski(A_116)))), inference(superposition, [status(thm), theory('equality')], [c_40, c_815])).
% 2.86/1.43  tff(c_860, plain, ('#skF_3'='#skF_4'), inference(resolution, [status(thm)], [c_497, c_857])).
% 2.86/1.43  tff(c_867, plain, $false, inference(negUnitSimplification, [status(thm)], [c_54, c_54, c_54, c_860])).
% 2.86/1.43  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.86/1.43  
% 2.86/1.43  Inference rules
% 2.86/1.43  ----------------------
% 2.86/1.43  #Ref     : 0
% 2.86/1.43  #Sup     : 208
% 2.86/1.43  #Fact    : 0
% 2.86/1.43  #Define  : 0
% 2.86/1.43  #Split   : 0
% 2.86/1.43  #Chain   : 0
% 2.86/1.43  #Close   : 0
% 2.86/1.43  
% 2.86/1.43  Ordering : KBO
% 2.86/1.43  
% 2.86/1.43  Simplification rules
% 2.86/1.43  ----------------------
% 2.86/1.43  #Subsume      : 6
% 2.86/1.43  #Demod        : 97
% 2.86/1.43  #Tautology    : 148
% 2.86/1.43  #SimpNegUnit  : 3
% 2.86/1.43  #BackRed      : 0
% 2.86/1.43  
% 2.86/1.43  #Partial instantiations: 0
% 2.86/1.43  #Strategies tried      : 1
% 2.86/1.43  
% 2.86/1.43  Timing (in seconds)
% 2.86/1.43  ----------------------
% 2.86/1.43  Preprocessing        : 0.32
% 2.86/1.43  Parsing              : 0.17
% 2.86/1.43  CNF conversion       : 0.02
% 2.86/1.43  Main loop            : 0.35
% 2.86/1.43  Inferencing          : 0.11
% 2.86/1.43  Reduction            : 0.14
% 2.86/1.43  Demodulation         : 0.11
% 2.86/1.43  BG Simplification    : 0.02
% 2.86/1.43  Subsumption          : 0.06
% 2.86/1.43  Abstraction          : 0.02
% 2.86/1.43  MUC search           : 0.00
% 2.86/1.43  Cooper               : 0.00
% 2.86/1.43  Total                : 0.70
% 2.86/1.43  Index Insertion      : 0.00
% 2.86/1.43  Index Deletion       : 0.00
% 2.86/1.43  Index Matching       : 0.00
% 2.86/1.43  BG Taut test         : 0.00
%------------------------------------------------------------------------------
