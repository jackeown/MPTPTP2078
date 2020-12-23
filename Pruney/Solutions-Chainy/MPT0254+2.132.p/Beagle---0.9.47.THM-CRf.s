%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:51:36 EST 2020

% Result     : Theorem 3.90s
% Output     : CNFRefutation 3.90s
% Verified   : 
% Statistics : Number of formulae       :   57 (  64 expanded)
%              Number of leaves         :   33 (  37 expanded)
%              Depth                    :    6
%              Number of atoms          :   60 (  75 expanded)
%              Number of equality atoms :   24 (  28 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1

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

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_65,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_36,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_53,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_94,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
    <=> A != B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_zfmisc_1)).

tff(f_98,negated_conjecture,(
    ~ ! [A,B] : k2_xboole_0(k1_tarski(A),B) != k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_zfmisc_1)).

tff(f_61,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_51,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k5_xboole_0(B,C))
    <=> ~ ( r2_hidden(A,B)
        <=> r2_hidden(A,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_0)).

tff(f_59,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

tff(c_38,plain,(
    ! [A_25] : k5_xboole_0(A_25,A_25) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_10,plain,(
    ! [A_8] : k3_xboole_0(A_8,A_8) = A_8 ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_260,plain,(
    ! [A_99,B_100] : k5_xboole_0(A_99,k3_xboole_0(A_99,B_100)) = k4_xboole_0(A_99,B_100) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_269,plain,(
    ! [A_8] : k5_xboole_0(A_8,A_8) = k4_xboole_0(A_8,A_8) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_260])).

tff(c_272,plain,(
    ! [A_8] : k4_xboole_0(A_8,A_8) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_269])).

tff(c_64,plain,(
    ! [B_76] : k4_xboole_0(k1_tarski(B_76),k1_tarski(B_76)) != k1_tarski(B_76) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_273,plain,(
    ! [B_76] : k1_tarski(B_76) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_272,c_64])).

tff(c_68,plain,(
    k2_xboole_0(k1_tarski('#skF_3'),'#skF_4') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_34,plain,(
    ! [A_20,B_21] : r1_tarski(A_20,k2_xboole_0(A_20,B_21)) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_138,plain,(
    r1_tarski(k1_tarski('#skF_3'),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_68,c_34])).

tff(c_24,plain,(
    ! [A_13] :
      ( r2_hidden('#skF_2'(A_13),A_13)
      | k1_xboole_0 = A_13 ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_309,plain,(
    ! [C_110,B_111,A_112] :
      ( r2_hidden(C_110,B_111)
      | ~ r2_hidden(C_110,A_112)
      | ~ r1_tarski(A_112,B_111) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_2962,plain,(
    ! [A_200,B_201] :
      ( r2_hidden('#skF_2'(A_200),B_201)
      | ~ r1_tarski(A_200,B_201)
      | k1_xboole_0 = A_200 ) ),
    inference(resolution,[status(thm)],[c_24,c_309])).

tff(c_1088,plain,(
    ! [A_135,B_136,C_137] :
      ( r2_hidden(A_135,B_136)
      | r2_hidden(A_135,C_137)
      | ~ r2_hidden(A_135,k5_xboole_0(B_136,C_137)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_1126,plain,(
    ! [A_135,A_25] :
      ( r2_hidden(A_135,A_25)
      | r2_hidden(A_135,A_25)
      | ~ r2_hidden(A_135,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_1088])).

tff(c_2976,plain,(
    ! [A_200,A_25] :
      ( r2_hidden('#skF_2'(A_200),A_25)
      | ~ r1_tarski(A_200,k1_xboole_0)
      | k1_xboole_0 = A_200 ) ),
    inference(resolution,[status(thm)],[c_2962,c_1126])).

tff(c_315,plain,(
    ! [A_13,B_111] :
      ( r2_hidden('#skF_2'(A_13),B_111)
      | ~ r1_tarski(A_13,B_111)
      | k1_xboole_0 = A_13 ) ),
    inference(resolution,[status(thm)],[c_24,c_309])).

tff(c_32,plain,(
    ! [A_19] : k5_xboole_0(A_19,k1_xboole_0) = A_19 ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_1706,plain,(
    ! [A_149,C_150,B_151] :
      ( ~ r2_hidden(A_149,C_150)
      | ~ r2_hidden(A_149,B_151)
      | ~ r2_hidden(A_149,k5_xboole_0(B_151,C_150)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_3018,plain,(
    ! [A_212,A_213] :
      ( ~ r2_hidden(A_212,k1_xboole_0)
      | ~ r2_hidden(A_212,A_213)
      | ~ r2_hidden(A_212,A_213) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_1706])).

tff(c_3056,plain,(
    ! [A_216,A_217] :
      ( ~ r2_hidden('#skF_2'(A_216),A_217)
      | ~ r1_tarski(A_216,k1_xboole_0)
      | k1_xboole_0 = A_216 ) ),
    inference(resolution,[status(thm)],[c_315,c_3018])).

tff(c_3079,plain,(
    ! [A_218] :
      ( ~ r1_tarski(A_218,k1_xboole_0)
      | k1_xboole_0 = A_218 ) ),
    inference(resolution,[status(thm)],[c_2976,c_3056])).

tff(c_3082,plain,(
    k1_tarski('#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_138,c_3079])).

tff(c_3094,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_273,c_3082])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n005.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 15:23:32 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.90/1.68  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.90/1.69  
% 3.90/1.69  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.90/1.69  %$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 3.90/1.69  
% 3.90/1.69  %Foreground sorts:
% 3.90/1.69  
% 3.90/1.69  
% 3.90/1.69  %Background operators:
% 3.90/1.69  
% 3.90/1.69  
% 3.90/1.69  %Foreground operators:
% 3.90/1.69  tff('#skF_2', type, '#skF_2': $i > $i).
% 3.90/1.69  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.90/1.69  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.90/1.69  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.90/1.69  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.90/1.69  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.90/1.69  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.90/1.69  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.90/1.69  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.90/1.69  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.90/1.69  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.90/1.69  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.90/1.69  tff('#skF_3', type, '#skF_3': $i).
% 3.90/1.69  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.90/1.69  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.90/1.69  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.90/1.69  tff(k3_tarski, type, k3_tarski: $i > $i).
% 3.90/1.69  tff('#skF_4', type, '#skF_4': $i).
% 3.90/1.69  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.90/1.69  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.90/1.69  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.90/1.69  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.90/1.69  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.90/1.69  
% 3.90/1.71  tff(f_65, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t92_xboole_1)).
% 3.90/1.71  tff(f_36, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 3.90/1.71  tff(f_53, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 3.90/1.71  tff(f_94, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) <=> ~(A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_zfmisc_1)).
% 3.90/1.71  tff(f_98, negated_conjecture, ~(![A, B]: ~(k2_xboole_0(k1_tarski(A), B) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_zfmisc_1)).
% 3.90/1.71  tff(f_61, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 3.90/1.71  tff(f_51, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 3.90/1.71  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 3.90/1.71  tff(f_43, axiom, (![A, B, C]: (r2_hidden(A, k5_xboole_0(B, C)) <=> ~(r2_hidden(A, B) <=> r2_hidden(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_0)).
% 3.90/1.71  tff(f_59, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 3.90/1.71  tff(c_38, plain, (![A_25]: (k5_xboole_0(A_25, A_25)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.90/1.71  tff(c_10, plain, (![A_8]: (k3_xboole_0(A_8, A_8)=A_8)), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.90/1.71  tff(c_260, plain, (![A_99, B_100]: (k5_xboole_0(A_99, k3_xboole_0(A_99, B_100))=k4_xboole_0(A_99, B_100))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.90/1.71  tff(c_269, plain, (![A_8]: (k5_xboole_0(A_8, A_8)=k4_xboole_0(A_8, A_8))), inference(superposition, [status(thm), theory('equality')], [c_10, c_260])).
% 3.90/1.71  tff(c_272, plain, (![A_8]: (k4_xboole_0(A_8, A_8)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_38, c_269])).
% 3.90/1.71  tff(c_64, plain, (![B_76]: (k4_xboole_0(k1_tarski(B_76), k1_tarski(B_76))!=k1_tarski(B_76))), inference(cnfTransformation, [status(thm)], [f_94])).
% 3.90/1.71  tff(c_273, plain, (![B_76]: (k1_tarski(B_76)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_272, c_64])).
% 3.90/1.71  tff(c_68, plain, (k2_xboole_0(k1_tarski('#skF_3'), '#skF_4')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_98])).
% 3.90/1.71  tff(c_34, plain, (![A_20, B_21]: (r1_tarski(A_20, k2_xboole_0(A_20, B_21)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.90/1.71  tff(c_138, plain, (r1_tarski(k1_tarski('#skF_3'), k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_68, c_34])).
% 3.90/1.71  tff(c_24, plain, (![A_13]: (r2_hidden('#skF_2'(A_13), A_13) | k1_xboole_0=A_13)), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.90/1.71  tff(c_309, plain, (![C_110, B_111, A_112]: (r2_hidden(C_110, B_111) | ~r2_hidden(C_110, A_112) | ~r1_tarski(A_112, B_111))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.90/1.71  tff(c_2962, plain, (![A_200, B_201]: (r2_hidden('#skF_2'(A_200), B_201) | ~r1_tarski(A_200, B_201) | k1_xboole_0=A_200)), inference(resolution, [status(thm)], [c_24, c_309])).
% 3.90/1.71  tff(c_1088, plain, (![A_135, B_136, C_137]: (r2_hidden(A_135, B_136) | r2_hidden(A_135, C_137) | ~r2_hidden(A_135, k5_xboole_0(B_136, C_137)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.90/1.71  tff(c_1126, plain, (![A_135, A_25]: (r2_hidden(A_135, A_25) | r2_hidden(A_135, A_25) | ~r2_hidden(A_135, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_38, c_1088])).
% 3.90/1.71  tff(c_2976, plain, (![A_200, A_25]: (r2_hidden('#skF_2'(A_200), A_25) | ~r1_tarski(A_200, k1_xboole_0) | k1_xboole_0=A_200)), inference(resolution, [status(thm)], [c_2962, c_1126])).
% 3.90/1.71  tff(c_315, plain, (![A_13, B_111]: (r2_hidden('#skF_2'(A_13), B_111) | ~r1_tarski(A_13, B_111) | k1_xboole_0=A_13)), inference(resolution, [status(thm)], [c_24, c_309])).
% 3.90/1.71  tff(c_32, plain, (![A_19]: (k5_xboole_0(A_19, k1_xboole_0)=A_19)), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.90/1.71  tff(c_1706, plain, (![A_149, C_150, B_151]: (~r2_hidden(A_149, C_150) | ~r2_hidden(A_149, B_151) | ~r2_hidden(A_149, k5_xboole_0(B_151, C_150)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.90/1.71  tff(c_3018, plain, (![A_212, A_213]: (~r2_hidden(A_212, k1_xboole_0) | ~r2_hidden(A_212, A_213) | ~r2_hidden(A_212, A_213))), inference(superposition, [status(thm), theory('equality')], [c_32, c_1706])).
% 3.90/1.71  tff(c_3056, plain, (![A_216, A_217]: (~r2_hidden('#skF_2'(A_216), A_217) | ~r1_tarski(A_216, k1_xboole_0) | k1_xboole_0=A_216)), inference(resolution, [status(thm)], [c_315, c_3018])).
% 3.90/1.71  tff(c_3079, plain, (![A_218]: (~r1_tarski(A_218, k1_xboole_0) | k1_xboole_0=A_218)), inference(resolution, [status(thm)], [c_2976, c_3056])).
% 3.90/1.71  tff(c_3082, plain, (k1_tarski('#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_138, c_3079])).
% 3.90/1.71  tff(c_3094, plain, $false, inference(negUnitSimplification, [status(thm)], [c_273, c_3082])).
% 3.90/1.71  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.90/1.71  
% 3.90/1.71  Inference rules
% 3.90/1.71  ----------------------
% 3.90/1.71  #Ref     : 0
% 3.90/1.71  #Sup     : 772
% 3.90/1.71  #Fact    : 0
% 3.90/1.71  #Define  : 0
% 3.90/1.71  #Split   : 0
% 3.90/1.71  #Chain   : 0
% 3.90/1.71  #Close   : 0
% 3.90/1.71  
% 3.90/1.71  Ordering : KBO
% 3.90/1.71  
% 3.90/1.71  Simplification rules
% 3.90/1.71  ----------------------
% 3.90/1.71  #Subsume      : 24
% 3.90/1.71  #Demod        : 459
% 3.90/1.71  #Tautology    : 466
% 3.90/1.71  #SimpNegUnit  : 5
% 3.90/1.71  #BackRed      : 8
% 3.90/1.71  
% 3.90/1.71  #Partial instantiations: 0
% 3.90/1.71  #Strategies tried      : 1
% 3.90/1.71  
% 3.90/1.71  Timing (in seconds)
% 3.90/1.71  ----------------------
% 3.90/1.72  Preprocessing        : 0.33
% 3.90/1.72  Parsing              : 0.18
% 3.90/1.72  CNF conversion       : 0.02
% 3.90/1.72  Main loop            : 0.61
% 3.90/1.72  Inferencing          : 0.20
% 3.90/1.72  Reduction            : 0.24
% 3.90/1.72  Demodulation         : 0.19
% 3.90/1.72  BG Simplification    : 0.03
% 3.90/1.72  Subsumption          : 0.09
% 3.90/1.72  Abstraction          : 0.03
% 3.90/1.72  MUC search           : 0.00
% 3.90/1.72  Cooper               : 0.00
% 3.90/1.72  Total                : 0.98
% 3.90/1.72  Index Insertion      : 0.00
% 3.90/1.72  Index Deletion       : 0.00
% 3.90/1.72  Index Matching       : 0.00
% 3.90/1.72  BG Taut test         : 0.00
%------------------------------------------------------------------------------
