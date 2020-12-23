%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:53:07 EST 2020

% Result     : Theorem 7.11s
% Output     : CNFRefutation 7.11s
% Verified   : 
% Statistics : Number of formulae       :   51 (  60 expanded)
%              Number of leaves         :   28 (  33 expanded)
%              Depth                    :    8
%              Number of atoms          :   54 (  67 expanded)
%              Number of equality atoms :   24 (  34 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1

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

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(f_46,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_64,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => k3_xboole_0(B,k1_tarski(A)) = k1_tarski(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l31_zfmisc_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_42,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_75,negated_conjecture,(
    ~ ! [A,B] :
        ( k4_xboole_0(k1_tarski(A),B) = k1_xboole_0
        | k4_xboole_0(k1_tarski(A),B) = k1_tarski(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_zfmisc_1)).

tff(f_40,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_70,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_tarski(A,B),C)
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).

tff(f_34,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k5_xboole_0(B,C))
    <=> ~ ( r2_hidden(A,B)
        <=> r2_hidden(A,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_0)).

tff(f_44,axiom,(
    ! [A,B,C] : k5_xboole_0(k3_xboole_0(A,B),k3_xboole_0(C,B)) = k3_xboole_0(k5_xboole_0(A,C),B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t112_xboole_1)).

tff(c_26,plain,(
    ! [A_13] : k5_xboole_0(A_13,A_13) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_198,plain,(
    ! [B_73,A_74] :
      ( k3_xboole_0(B_73,k1_tarski(A_74)) = k1_tarski(A_74)
      | ~ r2_hidden(A_74,B_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_148,plain,(
    ! [A_67,B_68] : k5_xboole_0(A_67,k3_xboole_0(A_67,B_68)) = k4_xboole_0(A_67,B_68) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_160,plain,(
    ! [B_2,A_1] : k5_xboole_0(B_2,k3_xboole_0(A_1,B_2)) = k4_xboole_0(B_2,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_148])).

tff(c_204,plain,(
    ! [A_74,B_73] :
      ( k5_xboole_0(k1_tarski(A_74),k1_tarski(A_74)) = k4_xboole_0(k1_tarski(A_74),B_73)
      | ~ r2_hidden(A_74,B_73) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_198,c_160])).

tff(c_237,plain,(
    ! [A_78,B_79] :
      ( k4_xboole_0(k1_tarski(A_78),B_79) = k1_xboole_0
      | ~ r2_hidden(A_78,B_79) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_204])).

tff(c_52,plain,(
    k4_xboole_0(k1_tarski('#skF_1'),'#skF_2') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_251,plain,(
    ~ r2_hidden('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_237,c_52])).

tff(c_20,plain,(
    ! [B_7] : r1_tarski(B_7,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_126,plain,(
    ! [B_59,C_60,A_61] :
      ( r2_hidden(B_59,C_60)
      | ~ r1_tarski(k2_tarski(A_61,B_59),C_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_134,plain,(
    ! [B_59,A_61] : r2_hidden(B_59,k2_tarski(A_61,B_59)) ),
    inference(resolution,[status(thm)],[c_20,c_126])).

tff(c_14,plain,(
    ! [A_3,C_5,B_4] :
      ( r2_hidden(A_3,C_5)
      | ~ r2_hidden(A_3,B_4)
      | r2_hidden(A_3,k5_xboole_0(B_4,C_5)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_42,plain,(
    ! [B_43,A_42] :
      ( k3_xboole_0(B_43,k1_tarski(A_42)) = k1_tarski(A_42)
      | ~ r2_hidden(A_42,B_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_422,plain,(
    ! [A_110,B_111,C_112] : k5_xboole_0(k3_xboole_0(A_110,B_111),k3_xboole_0(C_112,B_111)) = k3_xboole_0(k5_xboole_0(A_110,C_112),B_111) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_457,plain,(
    ! [A_42,C_112,B_43] :
      ( k5_xboole_0(k1_tarski(A_42),k3_xboole_0(C_112,k1_tarski(A_42))) = k3_xboole_0(k5_xboole_0(B_43,C_112),k1_tarski(A_42))
      | ~ r2_hidden(A_42,B_43) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_422])).

tff(c_3972,plain,(
    ! [B_212,C_213,A_214] :
      ( k3_xboole_0(k5_xboole_0(B_212,C_213),k1_tarski(A_214)) = k4_xboole_0(k1_tarski(A_214),C_213)
      | ~ r2_hidden(A_214,B_212) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_160,c_457])).

tff(c_7797,plain,(
    ! [A_300,C_301,B_302] :
      ( k4_xboole_0(k1_tarski(A_300),C_301) = k1_tarski(A_300)
      | ~ r2_hidden(A_300,k5_xboole_0(B_302,C_301))
      | ~ r2_hidden(A_300,B_302) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3972,c_42])).

tff(c_7967,plain,(
    ! [A_305,C_306,B_307] :
      ( k4_xboole_0(k1_tarski(A_305),C_306) = k1_tarski(A_305)
      | r2_hidden(A_305,C_306)
      | ~ r2_hidden(A_305,B_307) ) ),
    inference(resolution,[status(thm)],[c_14,c_7797])).

tff(c_8019,plain,(
    ! [B_308,C_309] :
      ( k4_xboole_0(k1_tarski(B_308),C_309) = k1_tarski(B_308)
      | r2_hidden(B_308,C_309) ) ),
    inference(resolution,[status(thm)],[c_134,c_7967])).

tff(c_50,plain,(
    k4_xboole_0(k1_tarski('#skF_1'),'#skF_2') != k1_tarski('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_8110,plain,(
    r2_hidden('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_8019,c_50])).

tff(c_8143,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_251,c_8110])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n003.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 09:25:27 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.11/2.52  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.11/2.52  
% 7.11/2.52  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.11/2.52  %$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1
% 7.11/2.52  
% 7.11/2.52  %Foreground sorts:
% 7.11/2.52  
% 7.11/2.52  
% 7.11/2.52  %Background operators:
% 7.11/2.52  
% 7.11/2.52  
% 7.11/2.52  %Foreground operators:
% 7.11/2.52  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.11/2.52  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 7.11/2.52  tff(k1_tarski, type, k1_tarski: $i > $i).
% 7.11/2.52  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 7.11/2.52  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 7.11/2.52  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 7.11/2.52  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 7.11/2.52  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.11/2.52  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 7.11/2.52  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 7.11/2.52  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 7.11/2.52  tff('#skF_2', type, '#skF_2': $i).
% 7.11/2.52  tff('#skF_1', type, '#skF_1': $i).
% 7.11/2.52  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 7.11/2.52  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 7.11/2.52  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.11/2.52  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.11/2.52  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 7.11/2.52  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 7.11/2.52  
% 7.11/2.53  tff(f_46, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t92_xboole_1)).
% 7.11/2.53  tff(f_64, axiom, (![A, B]: (r2_hidden(A, B) => (k3_xboole_0(B, k1_tarski(A)) = k1_tarski(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l31_zfmisc_1)).
% 7.11/2.53  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 7.11/2.53  tff(f_42, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 7.11/2.53  tff(f_75, negated_conjecture, ~(![A, B]: ((k4_xboole_0(k1_tarski(A), B) = k1_xboole_0) | (k4_xboole_0(k1_tarski(A), B) = k1_tarski(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_zfmisc_1)).
% 7.11/2.53  tff(f_40, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 7.11/2.53  tff(f_70, axiom, (![A, B, C]: (r1_tarski(k2_tarski(A, B), C) <=> (r2_hidden(A, C) & r2_hidden(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 7.11/2.53  tff(f_34, axiom, (![A, B, C]: (r2_hidden(A, k5_xboole_0(B, C)) <=> ~(r2_hidden(A, B) <=> r2_hidden(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_0)).
% 7.11/2.53  tff(f_44, axiom, (![A, B, C]: (k5_xboole_0(k3_xboole_0(A, B), k3_xboole_0(C, B)) = k3_xboole_0(k5_xboole_0(A, C), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t112_xboole_1)).
% 7.11/2.53  tff(c_26, plain, (![A_13]: (k5_xboole_0(A_13, A_13)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_46])).
% 7.11/2.53  tff(c_198, plain, (![B_73, A_74]: (k3_xboole_0(B_73, k1_tarski(A_74))=k1_tarski(A_74) | ~r2_hidden(A_74, B_73))), inference(cnfTransformation, [status(thm)], [f_64])).
% 7.11/2.53  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 7.11/2.53  tff(c_148, plain, (![A_67, B_68]: (k5_xboole_0(A_67, k3_xboole_0(A_67, B_68))=k4_xboole_0(A_67, B_68))), inference(cnfTransformation, [status(thm)], [f_42])).
% 7.11/2.53  tff(c_160, plain, (![B_2, A_1]: (k5_xboole_0(B_2, k3_xboole_0(A_1, B_2))=k4_xboole_0(B_2, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_148])).
% 7.11/2.53  tff(c_204, plain, (![A_74, B_73]: (k5_xboole_0(k1_tarski(A_74), k1_tarski(A_74))=k4_xboole_0(k1_tarski(A_74), B_73) | ~r2_hidden(A_74, B_73))), inference(superposition, [status(thm), theory('equality')], [c_198, c_160])).
% 7.11/2.53  tff(c_237, plain, (![A_78, B_79]: (k4_xboole_0(k1_tarski(A_78), B_79)=k1_xboole_0 | ~r2_hidden(A_78, B_79))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_204])).
% 7.11/2.53  tff(c_52, plain, (k4_xboole_0(k1_tarski('#skF_1'), '#skF_2')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_75])).
% 7.11/2.53  tff(c_251, plain, (~r2_hidden('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_237, c_52])).
% 7.11/2.53  tff(c_20, plain, (![B_7]: (r1_tarski(B_7, B_7))), inference(cnfTransformation, [status(thm)], [f_40])).
% 7.11/2.53  tff(c_126, plain, (![B_59, C_60, A_61]: (r2_hidden(B_59, C_60) | ~r1_tarski(k2_tarski(A_61, B_59), C_60))), inference(cnfTransformation, [status(thm)], [f_70])).
% 7.11/2.53  tff(c_134, plain, (![B_59, A_61]: (r2_hidden(B_59, k2_tarski(A_61, B_59)))), inference(resolution, [status(thm)], [c_20, c_126])).
% 7.11/2.53  tff(c_14, plain, (![A_3, C_5, B_4]: (r2_hidden(A_3, C_5) | ~r2_hidden(A_3, B_4) | r2_hidden(A_3, k5_xboole_0(B_4, C_5)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 7.11/2.53  tff(c_42, plain, (![B_43, A_42]: (k3_xboole_0(B_43, k1_tarski(A_42))=k1_tarski(A_42) | ~r2_hidden(A_42, B_43))), inference(cnfTransformation, [status(thm)], [f_64])).
% 7.11/2.53  tff(c_422, plain, (![A_110, B_111, C_112]: (k5_xboole_0(k3_xboole_0(A_110, B_111), k3_xboole_0(C_112, B_111))=k3_xboole_0(k5_xboole_0(A_110, C_112), B_111))), inference(cnfTransformation, [status(thm)], [f_44])).
% 7.11/2.53  tff(c_457, plain, (![A_42, C_112, B_43]: (k5_xboole_0(k1_tarski(A_42), k3_xboole_0(C_112, k1_tarski(A_42)))=k3_xboole_0(k5_xboole_0(B_43, C_112), k1_tarski(A_42)) | ~r2_hidden(A_42, B_43))), inference(superposition, [status(thm), theory('equality')], [c_42, c_422])).
% 7.11/2.53  tff(c_3972, plain, (![B_212, C_213, A_214]: (k3_xboole_0(k5_xboole_0(B_212, C_213), k1_tarski(A_214))=k4_xboole_0(k1_tarski(A_214), C_213) | ~r2_hidden(A_214, B_212))), inference(demodulation, [status(thm), theory('equality')], [c_160, c_457])).
% 7.11/2.53  tff(c_7797, plain, (![A_300, C_301, B_302]: (k4_xboole_0(k1_tarski(A_300), C_301)=k1_tarski(A_300) | ~r2_hidden(A_300, k5_xboole_0(B_302, C_301)) | ~r2_hidden(A_300, B_302))), inference(superposition, [status(thm), theory('equality')], [c_3972, c_42])).
% 7.11/2.53  tff(c_7967, plain, (![A_305, C_306, B_307]: (k4_xboole_0(k1_tarski(A_305), C_306)=k1_tarski(A_305) | r2_hidden(A_305, C_306) | ~r2_hidden(A_305, B_307))), inference(resolution, [status(thm)], [c_14, c_7797])).
% 7.11/2.53  tff(c_8019, plain, (![B_308, C_309]: (k4_xboole_0(k1_tarski(B_308), C_309)=k1_tarski(B_308) | r2_hidden(B_308, C_309))), inference(resolution, [status(thm)], [c_134, c_7967])).
% 7.11/2.53  tff(c_50, plain, (k4_xboole_0(k1_tarski('#skF_1'), '#skF_2')!=k1_tarski('#skF_1')), inference(cnfTransformation, [status(thm)], [f_75])).
% 7.11/2.53  tff(c_8110, plain, (r2_hidden('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_8019, c_50])).
% 7.11/2.53  tff(c_8143, plain, $false, inference(negUnitSimplification, [status(thm)], [c_251, c_8110])).
% 7.11/2.53  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.11/2.53  
% 7.11/2.53  Inference rules
% 7.11/2.53  ----------------------
% 7.11/2.53  #Ref     : 0
% 7.11/2.53  #Sup     : 2009
% 7.11/2.53  #Fact    : 0
% 7.11/2.53  #Define  : 0
% 7.11/2.53  #Split   : 0
% 7.11/2.53  #Chain   : 0
% 7.11/2.53  #Close   : 0
% 7.11/2.53  
% 7.11/2.53  Ordering : KBO
% 7.11/2.53  
% 7.11/2.53  Simplification rules
% 7.11/2.53  ----------------------
% 7.11/2.53  #Subsume      : 453
% 7.11/2.53  #Demod        : 1617
% 7.11/2.53  #Tautology    : 572
% 7.11/2.53  #SimpNegUnit  : 163
% 7.11/2.53  #BackRed      : 6
% 7.11/2.53  
% 7.11/2.53  #Partial instantiations: 0
% 7.11/2.53  #Strategies tried      : 1
% 7.11/2.53  
% 7.11/2.53  Timing (in seconds)
% 7.11/2.53  ----------------------
% 7.11/2.54  Preprocessing        : 0.33
% 7.11/2.54  Parsing              : 0.17
% 7.11/2.54  CNF conversion       : 0.02
% 7.11/2.54  Main loop            : 1.45
% 7.11/2.54  Inferencing          : 0.40
% 7.11/2.54  Reduction            : 0.68
% 7.11/2.54  Demodulation         : 0.55
% 7.11/2.54  BG Simplification    : 0.06
% 7.11/2.54  Subsumption          : 0.25
% 7.11/2.54  Abstraction          : 0.07
% 7.11/2.54  MUC search           : 0.00
% 7.11/2.54  Cooper               : 0.00
% 7.11/2.54  Total                : 1.80
% 7.11/2.54  Index Insertion      : 0.00
% 7.11/2.54  Index Deletion       : 0.00
% 7.11/2.54  Index Matching       : 0.00
% 7.11/2.54  BG Taut test         : 0.00
%------------------------------------------------------------------------------
