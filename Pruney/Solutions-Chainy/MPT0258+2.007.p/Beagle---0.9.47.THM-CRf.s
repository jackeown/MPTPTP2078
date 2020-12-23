%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:52:07 EST 2020

% Result     : Theorem 27.98s
% Output     : CNFRefutation 27.99s
% Verified   : 
% Statistics : Number of formulae       :   56 (  76 expanded)
%              Number of leaves         :   30 (  41 expanded)
%              Depth                    :    9
%              Number of atoms          :   50 (  74 expanded)
%              Number of equality atoms :   29 (  49 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

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

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(f_76,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( r2_hidden(A,B)
          & r2_hidden(C,B) )
       => k3_xboole_0(k2_tarski(A,C),B) = k2_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t53_zfmisc_1)).

tff(f_31,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_39,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k2_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

tff(f_41,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k5_xboole_0(k5_xboole_0(A,B),k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k5_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

tff(f_37,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_69,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_tarski(A,B),C)
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(c_48,plain,(
    r2_hidden('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_46,plain,(
    r2_hidden('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_6,plain,(
    ! [A_5] : k3_xboole_0(A_5,A_5) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_12,plain,(
    ! [A_12] : k5_xboole_0(A_12,A_12) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_4,plain,(
    ! [A_3] : k2_xboole_0(A_3,A_3) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_306,plain,(
    ! [A_96,B_97] : k5_xboole_0(k5_xboole_0(A_96,B_97),k2_xboole_0(A_96,B_97)) = k3_xboole_0(A_96,B_97) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_361,plain,(
    ! [A_3] : k5_xboole_0(k5_xboole_0(A_3,A_3),A_3) = k3_xboole_0(A_3,A_3) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_306])).

tff(c_369,plain,(
    ! [A_98] : k5_xboole_0(k1_xboole_0,A_98) = A_98 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_12,c_361])).

tff(c_2,plain,(
    ! [B_2,A_1] : k5_xboole_0(B_2,A_1) = k5_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_400,plain,(
    ! [A_98] : k5_xboole_0(A_98,k1_xboole_0) = A_98 ),
    inference(superposition,[status(thm),theory(equality)],[c_369,c_2])).

tff(c_166,plain,(
    ! [A_90,B_91,C_92] : k5_xboole_0(k5_xboole_0(A_90,B_91),C_92) = k5_xboole_0(A_90,k5_xboole_0(B_91,C_92)) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_182,plain,(
    ! [A_90,B_91] : k5_xboole_0(A_90,k5_xboole_0(B_91,k5_xboole_0(A_90,B_91))) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_166,c_12])).

tff(c_367,plain,(
    ! [A_3] : k5_xboole_0(k1_xboole_0,A_3) = A_3 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_12,c_361])).

tff(c_205,plain,(
    ! [A_12,C_92] : k5_xboole_0(A_12,k5_xboole_0(A_12,C_92)) = k5_xboole_0(k1_xboole_0,C_92) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_166])).

tff(c_583,plain,(
    ! [A_107,C_108] : k5_xboole_0(A_107,k5_xboole_0(A_107,C_108)) = C_108 ),
    inference(demodulation,[status(thm),theory(equality)],[c_367,c_205])).

tff(c_636,plain,(
    ! [B_91,A_90] : k5_xboole_0(B_91,k5_xboole_0(A_90,B_91)) = k5_xboole_0(A_90,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_182,c_583])).

tff(c_670,plain,(
    ! [B_91,A_90] : k5_xboole_0(B_91,k5_xboole_0(A_90,B_91)) = A_90 ),
    inference(demodulation,[status(thm),theory(equality)],[c_400,c_636])).

tff(c_566,plain,(
    ! [A_104,B_105,C_106] :
      ( r1_tarski(k2_tarski(A_104,B_105),C_106)
      | ~ r2_hidden(B_105,C_106)
      | ~ r2_hidden(A_104,C_106) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_8,plain,(
    ! [A_7,B_8] :
      ( k2_xboole_0(A_7,B_8) = B_8
      | ~ r1_tarski(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_5278,plain,(
    ! [A_200,B_201,C_202] :
      ( k2_xboole_0(k2_tarski(A_200,B_201),C_202) = C_202
      | ~ r2_hidden(B_201,C_202)
      | ~ r2_hidden(A_200,C_202) ) ),
    inference(resolution,[status(thm)],[c_566,c_8])).

tff(c_14,plain,(
    ! [A_13,B_14] : k5_xboole_0(k5_xboole_0(A_13,B_14),k2_xboole_0(A_13,B_14)) = k3_xboole_0(A_13,B_14) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_5312,plain,(
    ! [A_200,B_201,C_202] :
      ( k5_xboole_0(k5_xboole_0(k2_tarski(A_200,B_201),C_202),C_202) = k3_xboole_0(k2_tarski(A_200,B_201),C_202)
      | ~ r2_hidden(B_201,C_202)
      | ~ r2_hidden(A_200,C_202) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5278,c_14])).

tff(c_63052,plain,(
    ! [A_432,B_433,C_434] :
      ( k3_xboole_0(k2_tarski(A_432,B_433),C_434) = k2_tarski(A_432,B_433)
      | ~ r2_hidden(B_433,C_434)
      | ~ r2_hidden(A_432,C_434) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_670,c_2,c_5312])).

tff(c_44,plain,(
    k3_xboole_0(k2_tarski('#skF_1','#skF_3'),'#skF_2') != k2_tarski('#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_63140,plain,
    ( ~ r2_hidden('#skF_3','#skF_2')
    | ~ r2_hidden('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_63052,c_44])).

tff(c_63180,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_63140])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:27:00 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 27.98/20.19  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 27.99/20.20  
% 27.99/20.20  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 27.99/20.20  %$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 27.99/20.20  
% 27.99/20.20  %Foreground sorts:
% 27.99/20.20  
% 27.99/20.20  
% 27.99/20.20  %Background operators:
% 27.99/20.20  
% 27.99/20.20  
% 27.99/20.20  %Foreground operators:
% 27.99/20.20  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 27.99/20.20  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 27.99/20.20  tff(k1_tarski, type, k1_tarski: $i > $i).
% 27.99/20.20  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 27.99/20.20  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 27.99/20.20  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 27.99/20.20  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 27.99/20.20  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 27.99/20.20  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 27.99/20.20  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 27.99/20.20  tff('#skF_2', type, '#skF_2': $i).
% 27.99/20.20  tff('#skF_3', type, '#skF_3': $i).
% 27.99/20.20  tff('#skF_1', type, '#skF_1': $i).
% 27.99/20.20  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 27.99/20.20  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 27.99/20.20  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 27.99/20.20  tff(k3_tarski, type, k3_tarski: $i > $i).
% 27.99/20.20  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 27.99/20.20  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 27.99/20.20  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 27.99/20.20  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 27.99/20.20  
% 27.99/20.21  tff(f_76, negated_conjecture, ~(![A, B, C]: ((r2_hidden(A, B) & r2_hidden(C, B)) => (k3_xboole_0(k2_tarski(A, C), B) = k2_tarski(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t53_zfmisc_1)).
% 27.99/20.21  tff(f_31, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 27.99/20.21  tff(f_39, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t92_xboole_1)).
% 27.99/20.21  tff(f_29, axiom, (![A, B]: (k2_xboole_0(A, A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k2_xboole_0)).
% 27.99/20.21  tff(f_41, axiom, (![A, B]: (k3_xboole_0(A, B) = k5_xboole_0(k5_xboole_0(A, B), k2_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t95_xboole_1)).
% 27.99/20.21  tff(f_27, axiom, (![A, B]: (k5_xboole_0(A, B) = k5_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 27.99/20.21  tff(f_37, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_xboole_1)).
% 27.99/20.21  tff(f_69, axiom, (![A, B, C]: (r1_tarski(k2_tarski(A, B), C) <=> (r2_hidden(A, C) & r2_hidden(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 27.99/20.21  tff(f_35, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 27.99/20.21  tff(c_48, plain, (r2_hidden('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_76])).
% 27.99/20.21  tff(c_46, plain, (r2_hidden('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_76])).
% 27.99/20.21  tff(c_6, plain, (![A_5]: (k3_xboole_0(A_5, A_5)=A_5)), inference(cnfTransformation, [status(thm)], [f_31])).
% 27.99/20.21  tff(c_12, plain, (![A_12]: (k5_xboole_0(A_12, A_12)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 27.99/20.21  tff(c_4, plain, (![A_3]: (k2_xboole_0(A_3, A_3)=A_3)), inference(cnfTransformation, [status(thm)], [f_29])).
% 27.99/20.21  tff(c_306, plain, (![A_96, B_97]: (k5_xboole_0(k5_xboole_0(A_96, B_97), k2_xboole_0(A_96, B_97))=k3_xboole_0(A_96, B_97))), inference(cnfTransformation, [status(thm)], [f_41])).
% 27.99/20.21  tff(c_361, plain, (![A_3]: (k5_xboole_0(k5_xboole_0(A_3, A_3), A_3)=k3_xboole_0(A_3, A_3))), inference(superposition, [status(thm), theory('equality')], [c_4, c_306])).
% 27.99/20.21  tff(c_369, plain, (![A_98]: (k5_xboole_0(k1_xboole_0, A_98)=A_98)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_12, c_361])).
% 27.99/20.21  tff(c_2, plain, (![B_2, A_1]: (k5_xboole_0(B_2, A_1)=k5_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 27.99/20.21  tff(c_400, plain, (![A_98]: (k5_xboole_0(A_98, k1_xboole_0)=A_98)), inference(superposition, [status(thm), theory('equality')], [c_369, c_2])).
% 27.99/20.21  tff(c_166, plain, (![A_90, B_91, C_92]: (k5_xboole_0(k5_xboole_0(A_90, B_91), C_92)=k5_xboole_0(A_90, k5_xboole_0(B_91, C_92)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 27.99/20.21  tff(c_182, plain, (![A_90, B_91]: (k5_xboole_0(A_90, k5_xboole_0(B_91, k5_xboole_0(A_90, B_91)))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_166, c_12])).
% 27.99/20.21  tff(c_367, plain, (![A_3]: (k5_xboole_0(k1_xboole_0, A_3)=A_3)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_12, c_361])).
% 27.99/20.21  tff(c_205, plain, (![A_12, C_92]: (k5_xboole_0(A_12, k5_xboole_0(A_12, C_92))=k5_xboole_0(k1_xboole_0, C_92))), inference(superposition, [status(thm), theory('equality')], [c_12, c_166])).
% 27.99/20.21  tff(c_583, plain, (![A_107, C_108]: (k5_xboole_0(A_107, k5_xboole_0(A_107, C_108))=C_108)), inference(demodulation, [status(thm), theory('equality')], [c_367, c_205])).
% 27.99/20.21  tff(c_636, plain, (![B_91, A_90]: (k5_xboole_0(B_91, k5_xboole_0(A_90, B_91))=k5_xboole_0(A_90, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_182, c_583])).
% 27.99/20.21  tff(c_670, plain, (![B_91, A_90]: (k5_xboole_0(B_91, k5_xboole_0(A_90, B_91))=A_90)), inference(demodulation, [status(thm), theory('equality')], [c_400, c_636])).
% 27.99/20.21  tff(c_566, plain, (![A_104, B_105, C_106]: (r1_tarski(k2_tarski(A_104, B_105), C_106) | ~r2_hidden(B_105, C_106) | ~r2_hidden(A_104, C_106))), inference(cnfTransformation, [status(thm)], [f_69])).
% 27.99/20.21  tff(c_8, plain, (![A_7, B_8]: (k2_xboole_0(A_7, B_8)=B_8 | ~r1_tarski(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_35])).
% 27.99/20.21  tff(c_5278, plain, (![A_200, B_201, C_202]: (k2_xboole_0(k2_tarski(A_200, B_201), C_202)=C_202 | ~r2_hidden(B_201, C_202) | ~r2_hidden(A_200, C_202))), inference(resolution, [status(thm)], [c_566, c_8])).
% 27.99/20.21  tff(c_14, plain, (![A_13, B_14]: (k5_xboole_0(k5_xboole_0(A_13, B_14), k2_xboole_0(A_13, B_14))=k3_xboole_0(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_41])).
% 27.99/20.21  tff(c_5312, plain, (![A_200, B_201, C_202]: (k5_xboole_0(k5_xboole_0(k2_tarski(A_200, B_201), C_202), C_202)=k3_xboole_0(k2_tarski(A_200, B_201), C_202) | ~r2_hidden(B_201, C_202) | ~r2_hidden(A_200, C_202))), inference(superposition, [status(thm), theory('equality')], [c_5278, c_14])).
% 27.99/20.21  tff(c_63052, plain, (![A_432, B_433, C_434]: (k3_xboole_0(k2_tarski(A_432, B_433), C_434)=k2_tarski(A_432, B_433) | ~r2_hidden(B_433, C_434) | ~r2_hidden(A_432, C_434))), inference(demodulation, [status(thm), theory('equality')], [c_670, c_2, c_5312])).
% 27.99/20.21  tff(c_44, plain, (k3_xboole_0(k2_tarski('#skF_1', '#skF_3'), '#skF_2')!=k2_tarski('#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_76])).
% 27.99/20.21  tff(c_63140, plain, (~r2_hidden('#skF_3', '#skF_2') | ~r2_hidden('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_63052, c_44])).
% 27.99/20.21  tff(c_63180, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_63140])).
% 27.99/20.21  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 27.99/20.21  
% 27.99/20.21  Inference rules
% 27.99/20.21  ----------------------
% 27.99/20.21  #Ref     : 0
% 27.99/20.21  #Sup     : 16619
% 27.99/20.21  #Fact    : 0
% 27.99/20.21  #Define  : 0
% 27.99/20.21  #Split   : 0
% 27.99/20.21  #Chain   : 0
% 27.99/20.21  #Close   : 0
% 27.99/20.21  
% 27.99/20.21  Ordering : KBO
% 27.99/20.21  
% 27.99/20.21  Simplification rules
% 27.99/20.21  ----------------------
% 27.99/20.21  #Subsume      : 1212
% 27.99/20.21  #Demod        : 24634
% 27.99/20.21  #Tautology    : 4614
% 27.99/20.21  #SimpNegUnit  : 0
% 27.99/20.21  #BackRed      : 2
% 27.99/20.21  
% 27.99/20.21  #Partial instantiations: 0
% 27.99/20.21  #Strategies tried      : 1
% 27.99/20.21  
% 27.99/20.21  Timing (in seconds)
% 27.99/20.21  ----------------------
% 27.99/20.22  Preprocessing        : 0.32
% 27.99/20.22  Parsing              : 0.17
% 27.99/20.22  CNF conversion       : 0.02
% 27.99/20.22  Main loop            : 19.12
% 27.99/20.22  Inferencing          : 1.73
% 27.99/20.22  Reduction            : 14.88
% 27.99/20.22  Demodulation         : 14.40
% 27.99/20.22  BG Simplification    : 0.34
% 27.99/20.22  Subsumption          : 1.82
% 27.99/20.22  Abstraction          : 0.56
% 27.99/20.22  MUC search           : 0.00
% 27.99/20.22  Cooper               : 0.00
% 27.99/20.22  Total                : 19.47
% 27.99/20.22  Index Insertion      : 0.00
% 27.99/20.22  Index Deletion       : 0.00
% 27.99/20.22  Index Matching       : 0.00
% 27.99/20.22  BG Taut test         : 0.00
%------------------------------------------------------------------------------
