%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:51:20 EST 2020

% Result     : Theorem 5.86s
% Output     : CNFRefutation 6.15s
% Verified   : 
% Statistics : Number of formulae       :   65 ( 130 expanded)
%              Number of leaves         :   34 (  59 expanded)
%              Depth                    :   11
%              Number of atoms          :   59 ( 144 expanded)
%              Number of equality atoms :   27 (  70 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

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

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

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

tff(f_44,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_85,negated_conjecture,(
    ~ ! [A,B] : k2_xboole_0(k1_tarski(A),B) != k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_zfmisc_1)).

tff(f_56,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_81,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_50,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_40,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_67,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_65,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

tff(f_27,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k5_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

tff(f_48,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

tff(f_34,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k5_xboole_0(B,C))
    <=> ~ ( r2_hidden(A,B)
        <=> r2_hidden(A,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_0)).

tff(c_24,plain,(
    ! [A_10] : r1_tarski(k1_xboole_0,A_10) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_72,plain,(
    k2_xboole_0(k1_tarski('#skF_3'),'#skF_4') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_36,plain,(
    ! [B_21,A_20] : k2_tarski(B_21,A_20) = k2_tarski(A_20,B_21) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_264,plain,(
    ! [A_77,B_78] : k3_tarski(k2_tarski(A_77,B_78)) = k2_xboole_0(A_77,B_78) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_307,plain,(
    ! [B_81,A_82] : k3_tarski(k2_tarski(B_81,A_82)) = k2_xboole_0(A_82,B_81) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_264])).

tff(c_70,plain,(
    ! [A_56,B_57] : k3_tarski(k2_tarski(A_56,B_57)) = k2_xboole_0(A_56,B_57) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_333,plain,(
    ! [B_83,A_84] : k2_xboole_0(B_83,A_84) = k2_xboole_0(A_84,B_83) ),
    inference(superposition,[status(thm),theory(equality)],[c_307,c_70])).

tff(c_30,plain,(
    ! [A_13,B_14] : r1_tarski(A_13,k2_xboole_0(A_13,B_14)) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_384,plain,(
    ! [A_85,B_86] : r1_tarski(A_85,k2_xboole_0(B_86,A_85)) ),
    inference(superposition,[status(thm),theory(equality)],[c_333,c_30])).

tff(c_396,plain,(
    r1_tarski('#skF_4',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_72,c_384])).

tff(c_16,plain,(
    ! [B_7,A_6] :
      ( B_7 = A_6
      | ~ r1_tarski(B_7,A_6)
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_441,plain,
    ( k1_xboole_0 = '#skF_4'
    | ~ r1_tarski(k1_xboole_0,'#skF_4') ),
    inference(resolution,[status(thm)],[c_396,c_16])).

tff(c_444,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_441])).

tff(c_97,plain,(
    ! [A_64,B_65] : r1_tarski(A_64,k2_xboole_0(A_64,B_65)) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_100,plain,(
    r1_tarski(k1_tarski('#skF_3'),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_72,c_97])).

tff(c_400,plain,(
    ! [B_87,A_88] :
      ( B_87 = A_88
      | ~ r1_tarski(B_87,A_88)
      | ~ r1_tarski(A_88,B_87) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_406,plain,
    ( k1_tarski('#skF_3') = k1_xboole_0
    | ~ r1_tarski(k1_xboole_0,k1_tarski('#skF_3')) ),
    inference(resolution,[status(thm)],[c_100,c_400])).

tff(c_417,plain,(
    k1_tarski('#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_406])).

tff(c_101,plain,(
    ! [A_66] : k2_tarski(A_66,A_66) = k1_tarski(A_66) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_42,plain,(
    ! [D_27,B_23] : r2_hidden(D_27,k2_tarski(D_27,B_23)) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_107,plain,(
    ! [A_66] : r2_hidden(A_66,k1_tarski(A_66)) ),
    inference(superposition,[status(thm),theory(equality)],[c_101,c_42])).

tff(c_436,plain,(
    r2_hidden('#skF_3',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_417,c_107])).

tff(c_471,plain,(
    r2_hidden('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_444,c_436])).

tff(c_119,plain,(
    ! [B_70,A_71] : k5_xboole_0(B_70,A_71) = k5_xboole_0(A_71,B_70) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_28,plain,(
    ! [A_12] : k5_xboole_0(A_12,k1_xboole_0) = A_12 ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_135,plain,(
    ! [A_71] : k5_xboole_0(k1_xboole_0,A_71) = A_71 ),
    inference(superposition,[status(thm),theory(equality)],[c_119,c_28])).

tff(c_473,plain,(
    ! [A_71] : k5_xboole_0('#skF_4',A_71) = A_71 ),
    inference(demodulation,[status(thm),theory(equality)],[c_444,c_135])).

tff(c_1397,plain,(
    ! [A_128,C_129,B_130] :
      ( ~ r2_hidden(A_128,C_129)
      | ~ r2_hidden(A_128,B_130)
      | ~ r2_hidden(A_128,k5_xboole_0(B_130,C_129)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_6537,plain,(
    ! [A_10700,A_10701] :
      ( ~ r2_hidden(A_10700,A_10701)
      | ~ r2_hidden(A_10700,'#skF_4')
      | ~ r2_hidden(A_10700,A_10701) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_473,c_1397])).

tff(c_6549,plain,(
    ~ r2_hidden('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_471,c_6537])).

tff(c_6564,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_471,c_6549])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n005.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:47:02 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.86/2.21  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.86/2.22  
% 5.86/2.22  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.15/2.22  %$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2 > #skF_4
% 6.15/2.22  
% 6.15/2.22  %Foreground sorts:
% 6.15/2.22  
% 6.15/2.22  
% 6.15/2.22  %Background operators:
% 6.15/2.22  
% 6.15/2.22  
% 6.15/2.22  %Foreground operators:
% 6.15/2.22  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 6.15/2.22  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.15/2.22  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 6.15/2.22  tff(k1_tarski, type, k1_tarski: $i > $i).
% 6.15/2.22  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 6.15/2.22  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 6.15/2.22  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 6.15/2.22  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 6.15/2.22  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.15/2.22  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 6.15/2.22  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 6.15/2.22  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 6.15/2.22  tff('#skF_3', type, '#skF_3': $i).
% 6.15/2.22  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 6.15/2.22  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 6.15/2.22  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 6.15/2.22  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.15/2.22  tff(k3_tarski, type, k3_tarski: $i > $i).
% 6.15/2.22  tff('#skF_4', type, '#skF_4': $i).
% 6.15/2.22  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.15/2.22  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 6.15/2.22  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 6.15/2.22  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 6.15/2.22  
% 6.15/2.25  tff(f_44, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 6.15/2.25  tff(f_85, negated_conjecture, ~(![A, B]: ~(k2_xboole_0(k1_tarski(A), B) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_zfmisc_1)).
% 6.15/2.25  tff(f_56, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 6.15/2.25  tff(f_81, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 6.15/2.25  tff(f_50, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 6.15/2.25  tff(f_40, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 6.15/2.25  tff(f_67, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 6.15/2.25  tff(f_65, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_tarski)).
% 6.15/2.25  tff(f_27, axiom, (![A, B]: (k5_xboole_0(A, B) = k5_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 6.15/2.25  tff(f_48, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 6.15/2.25  tff(f_34, axiom, (![A, B, C]: (r2_hidden(A, k5_xboole_0(B, C)) <=> ~(r2_hidden(A, B) <=> r2_hidden(A, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_0)).
% 6.15/2.25  tff(c_24, plain, (![A_10]: (r1_tarski(k1_xboole_0, A_10))), inference(cnfTransformation, [status(thm)], [f_44])).
% 6.15/2.25  tff(c_72, plain, (k2_xboole_0(k1_tarski('#skF_3'), '#skF_4')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_85])).
% 6.15/2.25  tff(c_36, plain, (![B_21, A_20]: (k2_tarski(B_21, A_20)=k2_tarski(A_20, B_21))), inference(cnfTransformation, [status(thm)], [f_56])).
% 6.15/2.25  tff(c_264, plain, (![A_77, B_78]: (k3_tarski(k2_tarski(A_77, B_78))=k2_xboole_0(A_77, B_78))), inference(cnfTransformation, [status(thm)], [f_81])).
% 6.15/2.25  tff(c_307, plain, (![B_81, A_82]: (k3_tarski(k2_tarski(B_81, A_82))=k2_xboole_0(A_82, B_81))), inference(superposition, [status(thm), theory('equality')], [c_36, c_264])).
% 6.15/2.25  tff(c_70, plain, (![A_56, B_57]: (k3_tarski(k2_tarski(A_56, B_57))=k2_xboole_0(A_56, B_57))), inference(cnfTransformation, [status(thm)], [f_81])).
% 6.15/2.25  tff(c_333, plain, (![B_83, A_84]: (k2_xboole_0(B_83, A_84)=k2_xboole_0(A_84, B_83))), inference(superposition, [status(thm), theory('equality')], [c_307, c_70])).
% 6.15/2.25  tff(c_30, plain, (![A_13, B_14]: (r1_tarski(A_13, k2_xboole_0(A_13, B_14)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 6.15/2.25  tff(c_384, plain, (![A_85, B_86]: (r1_tarski(A_85, k2_xboole_0(B_86, A_85)))), inference(superposition, [status(thm), theory('equality')], [c_333, c_30])).
% 6.15/2.25  tff(c_396, plain, (r1_tarski('#skF_4', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_72, c_384])).
% 6.15/2.25  tff(c_16, plain, (![B_7, A_6]: (B_7=A_6 | ~r1_tarski(B_7, A_6) | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_40])).
% 6.15/2.25  tff(c_441, plain, (k1_xboole_0='#skF_4' | ~r1_tarski(k1_xboole_0, '#skF_4')), inference(resolution, [status(thm)], [c_396, c_16])).
% 6.15/2.25  tff(c_444, plain, (k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_24, c_441])).
% 6.15/2.25  tff(c_97, plain, (![A_64, B_65]: (r1_tarski(A_64, k2_xboole_0(A_64, B_65)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 6.15/2.25  tff(c_100, plain, (r1_tarski(k1_tarski('#skF_3'), k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_72, c_97])).
% 6.15/2.25  tff(c_400, plain, (![B_87, A_88]: (B_87=A_88 | ~r1_tarski(B_87, A_88) | ~r1_tarski(A_88, B_87))), inference(cnfTransformation, [status(thm)], [f_40])).
% 6.15/2.25  tff(c_406, plain, (k1_tarski('#skF_3')=k1_xboole_0 | ~r1_tarski(k1_xboole_0, k1_tarski('#skF_3'))), inference(resolution, [status(thm)], [c_100, c_400])).
% 6.15/2.25  tff(c_417, plain, (k1_tarski('#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_24, c_406])).
% 6.15/2.25  tff(c_101, plain, (![A_66]: (k2_tarski(A_66, A_66)=k1_tarski(A_66))), inference(cnfTransformation, [status(thm)], [f_67])).
% 6.15/2.25  tff(c_42, plain, (![D_27, B_23]: (r2_hidden(D_27, k2_tarski(D_27, B_23)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 6.15/2.25  tff(c_107, plain, (![A_66]: (r2_hidden(A_66, k1_tarski(A_66)))), inference(superposition, [status(thm), theory('equality')], [c_101, c_42])).
% 6.15/2.25  tff(c_436, plain, (r2_hidden('#skF_3', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_417, c_107])).
% 6.15/2.25  tff(c_471, plain, (r2_hidden('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_444, c_436])).
% 6.15/2.25  tff(c_119, plain, (![B_70, A_71]: (k5_xboole_0(B_70, A_71)=k5_xboole_0(A_71, B_70))), inference(cnfTransformation, [status(thm)], [f_27])).
% 6.15/2.25  tff(c_28, plain, (![A_12]: (k5_xboole_0(A_12, k1_xboole_0)=A_12)), inference(cnfTransformation, [status(thm)], [f_48])).
% 6.15/2.25  tff(c_135, plain, (![A_71]: (k5_xboole_0(k1_xboole_0, A_71)=A_71)), inference(superposition, [status(thm), theory('equality')], [c_119, c_28])).
% 6.15/2.25  tff(c_473, plain, (![A_71]: (k5_xboole_0('#skF_4', A_71)=A_71)), inference(demodulation, [status(thm), theory('equality')], [c_444, c_135])).
% 6.15/2.25  tff(c_1397, plain, (![A_128, C_129, B_130]: (~r2_hidden(A_128, C_129) | ~r2_hidden(A_128, B_130) | ~r2_hidden(A_128, k5_xboole_0(B_130, C_129)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 6.15/2.25  tff(c_6537, plain, (![A_10700, A_10701]: (~r2_hidden(A_10700, A_10701) | ~r2_hidden(A_10700, '#skF_4') | ~r2_hidden(A_10700, A_10701))), inference(superposition, [status(thm), theory('equality')], [c_473, c_1397])).
% 6.15/2.25  tff(c_6549, plain, (~r2_hidden('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_471, c_6537])).
% 6.15/2.25  tff(c_6564, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_471, c_6549])).
% 6.15/2.25  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.15/2.25  
% 6.15/2.25  Inference rules
% 6.15/2.25  ----------------------
% 6.15/2.25  #Ref     : 0
% 6.15/2.25  #Sup     : 1336
% 6.15/2.25  #Fact    : 6
% 6.15/2.25  #Define  : 0
% 6.15/2.25  #Split   : 1
% 6.15/2.25  #Chain   : 0
% 6.15/2.25  #Close   : 0
% 6.15/2.25  
% 6.15/2.25  Ordering : KBO
% 6.15/2.25  
% 6.15/2.25  Simplification rules
% 6.15/2.25  ----------------------
% 6.15/2.25  #Subsume      : 72
% 6.15/2.25  #Demod        : 882
% 6.15/2.25  #Tautology    : 688
% 6.15/2.25  #SimpNegUnit  : 0
% 6.15/2.25  #BackRed      : 17
% 6.15/2.25  
% 6.15/2.25  #Partial instantiations: 3708
% 6.15/2.25  #Strategies tried      : 1
% 6.15/2.25  
% 6.15/2.25  Timing (in seconds)
% 6.15/2.25  ----------------------
% 6.15/2.25  Preprocessing        : 0.33
% 6.15/2.25  Parsing              : 0.17
% 6.15/2.25  CNF conversion       : 0.02
% 6.15/2.25  Main loop            : 1.15
% 6.15/2.25  Inferencing          : 0.43
% 6.15/2.25  Reduction            : 0.46
% 6.15/2.25  Demodulation         : 0.39
% 6.15/2.25  BG Simplification    : 0.05
% 6.15/2.25  Subsumption          : 0.16
% 6.15/2.25  Abstraction          : 0.05
% 6.15/2.25  MUC search           : 0.00
% 6.15/2.25  Cooper               : 0.00
% 6.15/2.25  Total                : 1.53
% 6.15/2.25  Index Insertion      : 0.00
% 6.15/2.25  Index Deletion       : 0.00
% 6.15/2.25  Index Matching       : 0.00
% 6.15/2.25  BG Taut test         : 0.00
%------------------------------------------------------------------------------
