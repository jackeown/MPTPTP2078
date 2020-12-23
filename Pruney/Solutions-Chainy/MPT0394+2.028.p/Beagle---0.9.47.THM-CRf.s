%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:57:24 EST 2020

% Result     : Theorem 3.75s
% Output     : CNFRefutation 3.86s
% Verified   : 
% Statistics : Number of formulae       :   61 (  96 expanded)
%              Number of leaves         :   33 (  47 expanded)
%              Depth                    :   11
%              Number of atoms          :   60 ( 107 expanded)
%              Number of equality atoms :   44 (  76 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_setfam_1 > k1_xboole_0 > #skF_4 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_82,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_76,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

tff(f_90,axiom,(
    ! [A,B] : k3_xboole_0(k1_tarski(A),k2_tarski(A,B)) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_zfmisc_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_61,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_102,axiom,(
    ! [A] : k1_setfam_1(k1_tarski(A)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_setfam_1)).

tff(f_84,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_86,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_78,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k1_enumset1(A,B,C),k1_tarski(D)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_enumset1)).

tff(f_100,axiom,(
    ! [A,B] :
      ~ ( A != k1_xboole_0
        & B != k1_xboole_0
        & k1_setfam_1(k2_xboole_0(A,B)) != k3_xboole_0(k1_setfam_1(A),k1_setfam_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_setfam_1)).

tff(f_105,negated_conjecture,(
    ~ ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

tff(c_44,plain,(
    ! [A_32] : k2_tarski(A_32,A_32) = k1_tarski(A_32) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_77,plain,(
    ! [D_47,B_48] : r2_hidden(D_47,k2_tarski(D_47,B_48)) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_80,plain,(
    ! [A_32] : r2_hidden(A_32,k1_tarski(A_32)) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_77])).

tff(c_161,plain,(
    ! [A_70,B_71] : k3_xboole_0(k1_tarski(A_70),k2_tarski(A_70,B_71)) = k1_tarski(A_70) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_173,plain,(
    ! [A_32] : k3_xboole_0(k1_tarski(A_32),k1_tarski(A_32)) = k1_tarski(A_32) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_161])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( r1_xboole_0(A_1,B_2)
      | k3_xboole_0(A_1,B_2) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_176,plain,(
    ! [A_72] : k3_xboole_0(k1_tarski(A_72),k1_tarski(A_72)) = k1_tarski(A_72) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_161])).

tff(c_14,plain,(
    ! [A_8,B_9,C_12] :
      ( ~ r1_xboole_0(A_8,B_9)
      | ~ r2_hidden(C_12,k3_xboole_0(A_8,B_9)) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_375,plain,(
    ! [A_105,C_106] :
      ( ~ r1_xboole_0(k1_tarski(A_105),k1_tarski(A_105))
      | ~ r2_hidden(C_106,k1_tarski(A_105)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_176,c_14])).

tff(c_384,plain,(
    ! [C_106,A_105] :
      ( ~ r2_hidden(C_106,k1_tarski(A_105))
      | k3_xboole_0(k1_tarski(A_105),k1_tarski(A_105)) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_4,c_375])).

tff(c_389,plain,(
    ! [C_107,A_108] :
      ( ~ r2_hidden(C_107,k1_tarski(A_108))
      | k1_tarski(A_108) != k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_173,c_384])).

tff(c_403,plain,(
    ! [A_32] : k1_tarski(A_32) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_80,c_389])).

tff(c_56,plain,(
    ! [A_44] : k1_setfam_1(k1_tarski(A_44)) = A_44 ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_46,plain,(
    ! [A_33,B_34] : k1_enumset1(A_33,A_33,B_34) = k2_tarski(A_33,B_34) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_48,plain,(
    ! [A_35,B_36,C_37] : k2_enumset1(A_35,A_35,B_36,C_37) = k1_enumset1(A_35,B_36,C_37) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_405,plain,(
    ! [A_110,B_111,C_112,D_113] : k2_xboole_0(k1_enumset1(A_110,B_111,C_112),k1_tarski(D_113)) = k2_enumset1(A_110,B_111,C_112,D_113) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_414,plain,(
    ! [A_33,B_34,D_113] : k2_xboole_0(k2_tarski(A_33,B_34),k1_tarski(D_113)) = k2_enumset1(A_33,A_33,B_34,D_113) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_405])).

tff(c_592,plain,(
    ! [A_128,B_129,D_130] : k2_xboole_0(k2_tarski(A_128,B_129),k1_tarski(D_130)) = k1_enumset1(A_128,B_129,D_130) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_414])).

tff(c_601,plain,(
    ! [A_32,D_130] : k2_xboole_0(k1_tarski(A_32),k1_tarski(D_130)) = k1_enumset1(A_32,A_32,D_130) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_592])).

tff(c_604,plain,(
    ! [A_32,D_130] : k2_xboole_0(k1_tarski(A_32),k1_tarski(D_130)) = k2_tarski(A_32,D_130) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_601])).

tff(c_499,plain,(
    ! [A_121,B_122] :
      ( k3_xboole_0(k1_setfam_1(A_121),k1_setfam_1(B_122)) = k1_setfam_1(k2_xboole_0(A_121,B_122))
      | k1_xboole_0 = B_122
      | k1_xboole_0 = A_121 ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_529,plain,(
    ! [A_121,A_44] :
      ( k1_setfam_1(k2_xboole_0(A_121,k1_tarski(A_44))) = k3_xboole_0(k1_setfam_1(A_121),A_44)
      | k1_tarski(A_44) = k1_xboole_0
      | k1_xboole_0 = A_121 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_56,c_499])).

tff(c_1457,plain,(
    ! [A_217,A_218] :
      ( k1_setfam_1(k2_xboole_0(A_217,k1_tarski(A_218))) = k3_xboole_0(k1_setfam_1(A_217),A_218)
      | k1_xboole_0 = A_217 ) ),
    inference(negUnitSimplification,[status(thm)],[c_403,c_529])).

tff(c_1475,plain,(
    ! [A_32,D_130] :
      ( k3_xboole_0(k1_setfam_1(k1_tarski(A_32)),D_130) = k1_setfam_1(k2_tarski(A_32,D_130))
      | k1_tarski(A_32) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_604,c_1457])).

tff(c_1488,plain,(
    ! [A_32,D_130] :
      ( k1_setfam_1(k2_tarski(A_32,D_130)) = k3_xboole_0(A_32,D_130)
      | k1_tarski(A_32) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_1475])).

tff(c_1489,plain,(
    ! [A_32,D_130] : k1_setfam_1(k2_tarski(A_32,D_130)) = k3_xboole_0(A_32,D_130) ),
    inference(negUnitSimplification,[status(thm)],[c_403,c_1488])).

tff(c_58,plain,(
    k1_setfam_1(k2_tarski('#skF_5','#skF_6')) != k3_xboole_0('#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_2538,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1489,c_58])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n013.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 11:30:39 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.75/1.77  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.75/1.78  
% 3.75/1.78  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.75/1.78  %$ r2_hidden > r1_xboole_0 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_setfam_1 > k1_xboole_0 > #skF_4 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_1
% 3.75/1.78  
% 3.75/1.78  %Foreground sorts:
% 3.75/1.78  
% 3.75/1.78  
% 3.75/1.78  %Background operators:
% 3.75/1.78  
% 3.75/1.78  
% 3.75/1.78  %Foreground operators:
% 3.75/1.78  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.75/1.78  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.75/1.78  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.75/1.78  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.75/1.78  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.75/1.78  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.75/1.78  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 3.75/1.78  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.75/1.78  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.75/1.78  tff('#skF_5', type, '#skF_5': $i).
% 3.75/1.78  tff('#skF_6', type, '#skF_6': $i).
% 3.75/1.78  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.75/1.78  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.75/1.78  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.75/1.78  tff(k3_tarski, type, k3_tarski: $i > $i).
% 3.75/1.78  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 3.75/1.78  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.75/1.78  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.75/1.78  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.75/1.78  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.75/1.78  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.75/1.78  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 3.75/1.78  
% 3.86/1.79  tff(f_82, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 3.86/1.79  tff(f_76, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_tarski)).
% 3.86/1.79  tff(f_90, axiom, (![A, B]: (k3_xboole_0(k1_tarski(A), k2_tarski(A, B)) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t19_zfmisc_1)).
% 3.86/1.79  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 3.86/1.79  tff(f_61, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 3.86/1.79  tff(f_102, axiom, (![A]: (k1_setfam_1(k1_tarski(A)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_setfam_1)).
% 3.86/1.79  tff(f_84, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 3.86/1.79  tff(f_86, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 3.86/1.79  tff(f_78, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k1_enumset1(A, B, C), k1_tarski(D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_enumset1)).
% 3.86/1.79  tff(f_100, axiom, (![A, B]: ~((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(k1_setfam_1(k2_xboole_0(A, B)) = k3_xboole_0(k1_setfam_1(A), k1_setfam_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_setfam_1)).
% 3.86/1.79  tff(f_105, negated_conjecture, ~(![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_setfam_1)).
% 3.86/1.79  tff(c_44, plain, (![A_32]: (k2_tarski(A_32, A_32)=k1_tarski(A_32))), inference(cnfTransformation, [status(thm)], [f_82])).
% 3.86/1.79  tff(c_77, plain, (![D_47, B_48]: (r2_hidden(D_47, k2_tarski(D_47, B_48)))), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.86/1.79  tff(c_80, plain, (![A_32]: (r2_hidden(A_32, k1_tarski(A_32)))), inference(superposition, [status(thm), theory('equality')], [c_44, c_77])).
% 3.86/1.79  tff(c_161, plain, (![A_70, B_71]: (k3_xboole_0(k1_tarski(A_70), k2_tarski(A_70, B_71))=k1_tarski(A_70))), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.86/1.79  tff(c_173, plain, (![A_32]: (k3_xboole_0(k1_tarski(A_32), k1_tarski(A_32))=k1_tarski(A_32))), inference(superposition, [status(thm), theory('equality')], [c_44, c_161])).
% 3.86/1.79  tff(c_4, plain, (![A_1, B_2]: (r1_xboole_0(A_1, B_2) | k3_xboole_0(A_1, B_2)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.86/1.79  tff(c_176, plain, (![A_72]: (k3_xboole_0(k1_tarski(A_72), k1_tarski(A_72))=k1_tarski(A_72))), inference(superposition, [status(thm), theory('equality')], [c_44, c_161])).
% 3.86/1.79  tff(c_14, plain, (![A_8, B_9, C_12]: (~r1_xboole_0(A_8, B_9) | ~r2_hidden(C_12, k3_xboole_0(A_8, B_9)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.86/1.79  tff(c_375, plain, (![A_105, C_106]: (~r1_xboole_0(k1_tarski(A_105), k1_tarski(A_105)) | ~r2_hidden(C_106, k1_tarski(A_105)))), inference(superposition, [status(thm), theory('equality')], [c_176, c_14])).
% 3.86/1.79  tff(c_384, plain, (![C_106, A_105]: (~r2_hidden(C_106, k1_tarski(A_105)) | k3_xboole_0(k1_tarski(A_105), k1_tarski(A_105))!=k1_xboole_0)), inference(resolution, [status(thm)], [c_4, c_375])).
% 3.86/1.79  tff(c_389, plain, (![C_107, A_108]: (~r2_hidden(C_107, k1_tarski(A_108)) | k1_tarski(A_108)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_173, c_384])).
% 3.86/1.79  tff(c_403, plain, (![A_32]: (k1_tarski(A_32)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_80, c_389])).
% 3.86/1.79  tff(c_56, plain, (![A_44]: (k1_setfam_1(k1_tarski(A_44))=A_44)), inference(cnfTransformation, [status(thm)], [f_102])).
% 3.86/1.79  tff(c_46, plain, (![A_33, B_34]: (k1_enumset1(A_33, A_33, B_34)=k2_tarski(A_33, B_34))), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.86/1.79  tff(c_48, plain, (![A_35, B_36, C_37]: (k2_enumset1(A_35, A_35, B_36, C_37)=k1_enumset1(A_35, B_36, C_37))), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.86/1.79  tff(c_405, plain, (![A_110, B_111, C_112, D_113]: (k2_xboole_0(k1_enumset1(A_110, B_111, C_112), k1_tarski(D_113))=k2_enumset1(A_110, B_111, C_112, D_113))), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.86/1.79  tff(c_414, plain, (![A_33, B_34, D_113]: (k2_xboole_0(k2_tarski(A_33, B_34), k1_tarski(D_113))=k2_enumset1(A_33, A_33, B_34, D_113))), inference(superposition, [status(thm), theory('equality')], [c_46, c_405])).
% 3.86/1.79  tff(c_592, plain, (![A_128, B_129, D_130]: (k2_xboole_0(k2_tarski(A_128, B_129), k1_tarski(D_130))=k1_enumset1(A_128, B_129, D_130))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_414])).
% 3.86/1.79  tff(c_601, plain, (![A_32, D_130]: (k2_xboole_0(k1_tarski(A_32), k1_tarski(D_130))=k1_enumset1(A_32, A_32, D_130))), inference(superposition, [status(thm), theory('equality')], [c_44, c_592])).
% 3.86/1.79  tff(c_604, plain, (![A_32, D_130]: (k2_xboole_0(k1_tarski(A_32), k1_tarski(D_130))=k2_tarski(A_32, D_130))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_601])).
% 3.86/1.79  tff(c_499, plain, (![A_121, B_122]: (k3_xboole_0(k1_setfam_1(A_121), k1_setfam_1(B_122))=k1_setfam_1(k2_xboole_0(A_121, B_122)) | k1_xboole_0=B_122 | k1_xboole_0=A_121)), inference(cnfTransformation, [status(thm)], [f_100])).
% 3.86/1.79  tff(c_529, plain, (![A_121, A_44]: (k1_setfam_1(k2_xboole_0(A_121, k1_tarski(A_44)))=k3_xboole_0(k1_setfam_1(A_121), A_44) | k1_tarski(A_44)=k1_xboole_0 | k1_xboole_0=A_121)), inference(superposition, [status(thm), theory('equality')], [c_56, c_499])).
% 3.86/1.79  tff(c_1457, plain, (![A_217, A_218]: (k1_setfam_1(k2_xboole_0(A_217, k1_tarski(A_218)))=k3_xboole_0(k1_setfam_1(A_217), A_218) | k1_xboole_0=A_217)), inference(negUnitSimplification, [status(thm)], [c_403, c_529])).
% 3.86/1.79  tff(c_1475, plain, (![A_32, D_130]: (k3_xboole_0(k1_setfam_1(k1_tarski(A_32)), D_130)=k1_setfam_1(k2_tarski(A_32, D_130)) | k1_tarski(A_32)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_604, c_1457])).
% 3.86/1.79  tff(c_1488, plain, (![A_32, D_130]: (k1_setfam_1(k2_tarski(A_32, D_130))=k3_xboole_0(A_32, D_130) | k1_tarski(A_32)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_56, c_1475])).
% 3.86/1.79  tff(c_1489, plain, (![A_32, D_130]: (k1_setfam_1(k2_tarski(A_32, D_130))=k3_xboole_0(A_32, D_130))), inference(negUnitSimplification, [status(thm)], [c_403, c_1488])).
% 3.86/1.79  tff(c_58, plain, (k1_setfam_1(k2_tarski('#skF_5', '#skF_6'))!=k3_xboole_0('#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_105])).
% 3.86/1.79  tff(c_2538, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1489, c_58])).
% 3.86/1.79  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.86/1.79  
% 3.86/1.79  Inference rules
% 3.86/1.79  ----------------------
% 3.86/1.79  #Ref     : 0
% 3.86/1.79  #Sup     : 611
% 3.86/1.79  #Fact    : 0
% 3.86/1.79  #Define  : 0
% 3.86/1.79  #Split   : 0
% 3.86/1.79  #Chain   : 0
% 3.86/1.79  #Close   : 0
% 3.86/1.79  
% 3.86/1.79  Ordering : KBO
% 3.86/1.79  
% 3.86/1.79  Simplification rules
% 3.86/1.79  ----------------------
% 3.86/1.79  #Subsume      : 142
% 3.86/1.79  #Demod        : 95
% 3.86/1.79  #Tautology    : 206
% 3.86/1.79  #SimpNegUnit  : 29
% 3.86/1.79  #BackRed      : 1
% 3.86/1.79  
% 3.86/1.79  #Partial instantiations: 0
% 3.86/1.79  #Strategies tried      : 1
% 3.86/1.79  
% 3.86/1.79  Timing (in seconds)
% 3.86/1.79  ----------------------
% 3.86/1.80  Preprocessing        : 0.45
% 3.86/1.80  Parsing              : 0.26
% 3.86/1.80  CNF conversion       : 0.03
% 3.86/1.80  Main loop            : 0.54
% 3.86/1.80  Inferencing          : 0.21
% 3.86/1.80  Reduction            : 0.16
% 3.86/1.80  Demodulation         : 0.11
% 3.86/1.80  BG Simplification    : 0.03
% 3.86/1.80  Subsumption          : 0.10
% 3.86/1.80  Abstraction          : 0.04
% 3.86/1.80  MUC search           : 0.00
% 3.86/1.80  Cooper               : 0.00
% 3.86/1.80  Total                : 1.02
% 3.86/1.80  Index Insertion      : 0.00
% 3.86/1.80  Index Deletion       : 0.00
% 3.86/1.80  Index Matching       : 0.00
% 3.86/1.80  BG Taut test         : 0.00
%------------------------------------------------------------------------------
