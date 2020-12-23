%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:51:24 EST 2020

% Result     : Theorem 2.12s
% Output     : CNFRefutation 2.12s
% Verified   : 
% Statistics : Number of formulae       :   53 (  87 expanded)
%              Number of leaves         :   33 (  45 expanded)
%              Depth                    :    9
%              Number of atoms          :   40 (  92 expanded)
%              Number of equality atoms :   21 (  37 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_2',type,(
    '#skF_2': $i > $i )).

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

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_65,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_51,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_49,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_61,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_90,negated_conjecture,(
    ~ ! [A,B] : k2_xboole_0(k1_tarski(A),B) != k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_zfmisc_1)).

tff(f_63,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_86,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
    <=> A != B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_zfmisc_1)).

tff(c_22,plain,(
    ! [A_20] : k5_xboole_0(A_20,A_20) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_2,plain,(
    ! [A_1] : k3_xboole_0(A_1,A_1) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_376,plain,(
    ! [A_80,B_81] : k5_xboole_0(A_80,k3_xboole_0(A_80,B_81)) = k4_xboole_0(A_80,B_81) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_391,plain,(
    ! [A_1] : k5_xboole_0(A_1,A_1) = k4_xboole_0(A_1,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_376])).

tff(c_396,plain,(
    ! [A_1] : k4_xboole_0(A_1,A_1) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_391])).

tff(c_8,plain,(
    ! [A_8] :
      ( r2_hidden('#skF_2'(A_8),A_8)
      | k1_xboole_0 = A_8 ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_18,plain,(
    ! [A_17] : r1_xboole_0(A_17,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_44,plain,(
    k2_xboole_0(k1_tarski('#skF_3'),'#skF_4') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_20,plain,(
    ! [A_18,B_19] : r1_tarski(A_18,k2_xboole_0(A_18,B_19)) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_94,plain,(
    r1_tarski(k1_tarski('#skF_3'),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_20])).

tff(c_133,plain,(
    ! [A_59,B_60] :
      ( k3_xboole_0(A_59,B_60) = A_59
      | ~ r1_tarski(A_59,B_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_140,plain,(
    k3_xboole_0(k1_tarski('#skF_3'),k1_xboole_0) = k1_tarski('#skF_3') ),
    inference(resolution,[status(thm)],[c_94,c_133])).

tff(c_281,plain,(
    ! [A_75,B_76,C_77] :
      ( ~ r1_xboole_0(A_75,B_76)
      | ~ r2_hidden(C_77,k3_xboole_0(A_75,B_76)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_284,plain,(
    ! [C_77] :
      ( ~ r1_xboole_0(k1_tarski('#skF_3'),k1_xboole_0)
      | ~ r2_hidden(C_77,k1_tarski('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_140,c_281])).

tff(c_298,plain,(
    ! [C_78] : ~ r2_hidden(C_78,k1_tarski('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_284])).

tff(c_303,plain,(
    k1_tarski('#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_8,c_298])).

tff(c_40,plain,(
    ! [B_47] : k4_xboole_0(k1_tarski(B_47),k1_tarski(B_47)) != k1_tarski(B_47) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_322,plain,(
    k4_xboole_0(k1_tarski('#skF_3'),k1_xboole_0) != k1_tarski('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_303,c_40])).

tff(c_326,plain,(
    k4_xboole_0(k1_xboole_0,k1_xboole_0) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_303,c_303,c_322])).

tff(c_401,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_396,c_326])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n018.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 16:02:42 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.20/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.12/1.30  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.12/1.30  
% 2.12/1.30  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.12/1.30  %$ r2_hidden > r1_xboole_0 > r1_tarski > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 2.12/1.30  
% 2.12/1.30  %Foreground sorts:
% 2.12/1.30  
% 2.12/1.30  
% 2.12/1.30  %Background operators:
% 2.12/1.30  
% 2.12/1.30  
% 2.12/1.30  %Foreground operators:
% 2.12/1.30  tff('#skF_2', type, '#skF_2': $i > $i).
% 2.12/1.30  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.12/1.30  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.12/1.30  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.12/1.30  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.12/1.30  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.12/1.30  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.12/1.30  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.12/1.30  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.12/1.30  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.12/1.30  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.12/1.30  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.12/1.30  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.12/1.30  tff('#skF_3', type, '#skF_3': $i).
% 2.12/1.30  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.12/1.30  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.12/1.30  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.12/1.30  tff('#skF_4', type, '#skF_4': $i).
% 2.12/1.30  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.12/1.30  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.12/1.30  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.12/1.30  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.12/1.30  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.12/1.30  
% 2.12/1.31  tff(f_65, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t92_xboole_1)).
% 2.12/1.31  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 2.12/1.31  tff(f_51, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 2.12/1.31  tff(f_49, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 2.12/1.31  tff(f_61, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 2.12/1.31  tff(f_90, negated_conjecture, ~(![A, B]: ~(k2_xboole_0(k1_tarski(A), B) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_zfmisc_1)).
% 2.12/1.31  tff(f_63, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 2.12/1.31  tff(f_55, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 2.12/1.31  tff(f_41, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 2.12/1.31  tff(f_86, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) <=> ~(A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_zfmisc_1)).
% 2.12/1.31  tff(c_22, plain, (![A_20]: (k5_xboole_0(A_20, A_20)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.12/1.31  tff(c_2, plain, (![A_1]: (k3_xboole_0(A_1, A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.12/1.31  tff(c_376, plain, (![A_80, B_81]: (k5_xboole_0(A_80, k3_xboole_0(A_80, B_81))=k4_xboole_0(A_80, B_81))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.12/1.31  tff(c_391, plain, (![A_1]: (k5_xboole_0(A_1, A_1)=k4_xboole_0(A_1, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_376])).
% 2.12/1.31  tff(c_396, plain, (![A_1]: (k4_xboole_0(A_1, A_1)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_22, c_391])).
% 2.12/1.31  tff(c_8, plain, (![A_8]: (r2_hidden('#skF_2'(A_8), A_8) | k1_xboole_0=A_8)), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.12/1.31  tff(c_18, plain, (![A_17]: (r1_xboole_0(A_17, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.12/1.31  tff(c_44, plain, (k2_xboole_0(k1_tarski('#skF_3'), '#skF_4')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.12/1.31  tff(c_20, plain, (![A_18, B_19]: (r1_tarski(A_18, k2_xboole_0(A_18, B_19)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.12/1.31  tff(c_94, plain, (r1_tarski(k1_tarski('#skF_3'), k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_44, c_20])).
% 2.12/1.31  tff(c_133, plain, (![A_59, B_60]: (k3_xboole_0(A_59, B_60)=A_59 | ~r1_tarski(A_59, B_60))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.12/1.31  tff(c_140, plain, (k3_xboole_0(k1_tarski('#skF_3'), k1_xboole_0)=k1_tarski('#skF_3')), inference(resolution, [status(thm)], [c_94, c_133])).
% 2.12/1.31  tff(c_281, plain, (![A_75, B_76, C_77]: (~r1_xboole_0(A_75, B_76) | ~r2_hidden(C_77, k3_xboole_0(A_75, B_76)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.12/1.31  tff(c_284, plain, (![C_77]: (~r1_xboole_0(k1_tarski('#skF_3'), k1_xboole_0) | ~r2_hidden(C_77, k1_tarski('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_140, c_281])).
% 2.12/1.31  tff(c_298, plain, (![C_78]: (~r2_hidden(C_78, k1_tarski('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_284])).
% 2.12/1.31  tff(c_303, plain, (k1_tarski('#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_8, c_298])).
% 2.12/1.31  tff(c_40, plain, (![B_47]: (k4_xboole_0(k1_tarski(B_47), k1_tarski(B_47))!=k1_tarski(B_47))), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.12/1.31  tff(c_322, plain, (k4_xboole_0(k1_tarski('#skF_3'), k1_xboole_0)!=k1_tarski('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_303, c_40])).
% 2.12/1.31  tff(c_326, plain, (k4_xboole_0(k1_xboole_0, k1_xboole_0)!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_303, c_303, c_322])).
% 2.12/1.31  tff(c_401, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_396, c_326])).
% 2.12/1.31  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.12/1.31  
% 2.12/1.31  Inference rules
% 2.12/1.31  ----------------------
% 2.12/1.31  #Ref     : 0
% 2.12/1.31  #Sup     : 90
% 2.12/1.31  #Fact    : 0
% 2.12/1.31  #Define  : 0
% 2.12/1.31  #Split   : 0
% 2.12/1.31  #Chain   : 0
% 2.12/1.31  #Close   : 0
% 2.12/1.31  
% 2.12/1.31  Ordering : KBO
% 2.12/1.31  
% 2.12/1.31  Simplification rules
% 2.12/1.31  ----------------------
% 2.12/1.31  #Subsume      : 1
% 2.12/1.31  #Demod        : 29
% 2.12/1.31  #Tautology    : 60
% 2.12/1.31  #SimpNegUnit  : 0
% 2.12/1.31  #BackRed      : 7
% 2.12/1.31  
% 2.12/1.31  #Partial instantiations: 0
% 2.12/1.31  #Strategies tried      : 1
% 2.12/1.31  
% 2.12/1.31  Timing (in seconds)
% 2.12/1.31  ----------------------
% 2.12/1.32  Preprocessing        : 0.30
% 2.12/1.32  Parsing              : 0.16
% 2.12/1.32  CNF conversion       : 0.02
% 2.12/1.32  Main loop            : 0.19
% 2.12/1.32  Inferencing          : 0.07
% 2.12/1.32  Reduction            : 0.07
% 2.12/1.32  Demodulation         : 0.05
% 2.12/1.32  BG Simplification    : 0.02
% 2.12/1.32  Subsumption          : 0.02
% 2.12/1.32  Abstraction          : 0.01
% 2.12/1.32  MUC search           : 0.00
% 2.12/1.32  Cooper               : 0.00
% 2.12/1.32  Total                : 0.52
% 2.12/1.32  Index Insertion      : 0.00
% 2.12/1.32  Index Deletion       : 0.00
% 2.12/1.32  Index Matching       : 0.00
% 2.12/1.32  BG Taut test         : 0.00
%------------------------------------------------------------------------------
