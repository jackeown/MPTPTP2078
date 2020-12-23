%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:54:55 EST 2020

% Result     : Theorem 8.87s
% Output     : CNFRefutation 9.11s
% Verified   : 
% Statistics : Number of formulae       :   57 (  99 expanded)
%              Number of leaves         :   26 (  45 expanded)
%              Depth                    :   12
%              Number of atoms          :   57 ( 122 expanded)
%              Number of equality atoms :   37 (  81 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(f_68,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( r1_tarski(A,B)
          & k3_xboole_0(B,C) = k1_tarski(D)
          & r2_hidden(D,A) )
       => k3_xboole_0(A,C) = k1_tarski(D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_zfmisc_1)).

tff(f_47,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_59,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & r2_hidden(C,B) )
     => k3_xboole_0(k2_tarski(A,C),B) = k2_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t53_zfmisc_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_29,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_35,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_39,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_45,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_41,axiom,(
    ! [A,B,C] : k3_xboole_0(k3_xboole_0(A,B),C) = k3_xboole_0(A,k3_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_xboole_1)).

tff(c_32,plain,(
    k3_xboole_0('#skF_1','#skF_3') != k1_tarski('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_34,plain,(
    r2_hidden('#skF_4','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_22,plain,(
    ! [A_16] : k2_tarski(A_16,A_16) = k1_tarski(A_16) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_2024,plain,(
    ! [A_84,C_85,B_86] :
      ( k3_xboole_0(k2_tarski(A_84,C_85),B_86) = k2_tarski(A_84,C_85)
      | ~ r2_hidden(C_85,B_86)
      | ~ r2_hidden(A_84,B_86) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_2116,plain,(
    ! [A_16,B_86] :
      ( k3_xboole_0(k1_tarski(A_16),B_86) = k2_tarski(A_16,A_16)
      | ~ r2_hidden(A_16,B_86)
      | ~ r2_hidden(A_16,B_86) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_2024])).

tff(c_13716,plain,(
    ! [A_170,B_171] :
      ( k3_xboole_0(k1_tarski(A_170),B_171) = k1_tarski(A_170)
      | ~ r2_hidden(A_170,B_171)
      | ~ r2_hidden(A_170,B_171) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_2116])).

tff(c_36,plain,(
    k3_xboole_0('#skF_2','#skF_3') = k1_tarski('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_4,plain,(
    ! [A_3] : k3_xboole_0(A_3,A_3) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_10,plain,(
    ! [B_6] : r1_tarski(B_6,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_115,plain,(
    ! [A_34,B_35] :
      ( k4_xboole_0(A_34,B_35) = k1_xboole_0
      | ~ r1_tarski(A_34,B_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_122,plain,(
    ! [B_6] : k4_xboole_0(B_6,B_6) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_10,c_115])).

tff(c_167,plain,(
    ! [A_43,B_44] : k4_xboole_0(A_43,k4_xboole_0(A_43,B_44)) = k3_xboole_0(A_43,B_44) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_185,plain,(
    ! [B_6] : k4_xboole_0(B_6,k1_xboole_0) = k3_xboole_0(B_6,B_6) ),
    inference(superposition,[status(thm),theory(equality)],[c_122,c_167])).

tff(c_188,plain,(
    ! [B_6] : k4_xboole_0(B_6,k1_xboole_0) = B_6 ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_185])).

tff(c_38,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_123,plain,(
    k4_xboole_0('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_38,c_115])).

tff(c_182,plain,(
    k4_xboole_0('#skF_1',k1_xboole_0) = k3_xboole_0('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_123,c_167])).

tff(c_383,plain,(
    k3_xboole_0('#skF_1','#skF_2') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_188,c_182])).

tff(c_825,plain,(
    ! [A_64,B_65,C_66] : k3_xboole_0(k3_xboole_0(A_64,B_65),C_66) = k3_xboole_0(A_64,k3_xboole_0(B_65,C_66)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_1171,plain,(
    ! [C_70] : k3_xboole_0('#skF_1',k3_xboole_0('#skF_2',C_70)) = k3_xboole_0('#skF_1',C_70) ),
    inference(superposition,[status(thm),theory(equality)],[c_383,c_825])).

tff(c_1235,plain,(
    ! [A_1] : k3_xboole_0('#skF_1',k3_xboole_0(A_1,'#skF_2')) = k3_xboole_0('#skF_1',A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_1171])).

tff(c_3699,plain,(
    ! [C_102,A_103,B_104] : k3_xboole_0(C_102,k3_xboole_0(A_103,B_104)) = k3_xboole_0(A_103,k3_xboole_0(B_104,C_102)) ),
    inference(superposition,[status(thm),theory(equality)],[c_825,c_2])).

tff(c_4234,plain,(
    ! [A_3,C_102] : k3_xboole_0(A_3,k3_xboole_0(A_3,C_102)) = k3_xboole_0(C_102,A_3) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_3699])).

tff(c_4924,plain,(
    ! [C_109] : k3_xboole_0('#skF_1',k3_xboole_0('#skF_2',C_109)) = k3_xboole_0(C_109,'#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_383,c_3699])).

tff(c_5022,plain,(
    ! [C_102] : k3_xboole_0(k3_xboole_0('#skF_2',C_102),'#skF_1') = k3_xboole_0('#skF_1',k3_xboole_0(C_102,'#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_4234,c_4924])).

tff(c_6561,plain,(
    ! [C_119] : k3_xboole_0(k3_xboole_0('#skF_2',C_119),'#skF_1') = k3_xboole_0('#skF_1',C_119) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1235,c_5022])).

tff(c_6724,plain,(
    k3_xboole_0(k1_tarski('#skF_4'),'#skF_1') = k3_xboole_0('#skF_1','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_6561])).

tff(c_13795,plain,
    ( k3_xboole_0('#skF_1','#skF_3') = k1_tarski('#skF_4')
    | ~ r2_hidden('#skF_4','#skF_1')
    | ~ r2_hidden('#skF_4','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_13716,c_6724])).

tff(c_14034,plain,(
    k3_xboole_0('#skF_1','#skF_3') = k1_tarski('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_34,c_13795])).

tff(c_14036,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_14034])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n010.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 09:12:29 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.87/3.27  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.87/3.28  
% 8.87/3.28  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.87/3.28  %$ r2_hidden > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 8.87/3.28  
% 8.87/3.28  %Foreground sorts:
% 8.87/3.28  
% 8.87/3.28  
% 8.87/3.28  %Background operators:
% 8.87/3.28  
% 8.87/3.28  
% 8.87/3.28  %Foreground operators:
% 8.87/3.28  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.87/3.28  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 8.87/3.28  tff(k1_tarski, type, k1_tarski: $i > $i).
% 8.87/3.28  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 8.87/3.28  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 8.87/3.28  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 8.87/3.28  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 8.87/3.28  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 8.87/3.28  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 8.87/3.28  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 8.87/3.28  tff('#skF_2', type, '#skF_2': $i).
% 8.87/3.28  tff('#skF_3', type, '#skF_3': $i).
% 8.87/3.28  tff('#skF_1', type, '#skF_1': $i).
% 8.87/3.28  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.87/3.28  tff('#skF_4', type, '#skF_4': $i).
% 8.87/3.28  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.87/3.28  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 8.87/3.28  
% 9.11/3.29  tff(f_68, negated_conjecture, ~(![A, B, C, D]: (((r1_tarski(A, B) & (k3_xboole_0(B, C) = k1_tarski(D))) & r2_hidden(D, A)) => (k3_xboole_0(A, C) = k1_tarski(D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_zfmisc_1)).
% 9.11/3.29  tff(f_47, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 9.11/3.29  tff(f_59, axiom, (![A, B, C]: ((r2_hidden(A, B) & r2_hidden(C, B)) => (k3_xboole_0(k2_tarski(A, C), B) = k2_tarski(A, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t53_zfmisc_1)).
% 9.11/3.29  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 9.11/3.29  tff(f_29, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 9.11/3.29  tff(f_35, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 9.11/3.29  tff(f_39, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 9.11/3.29  tff(f_45, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 9.11/3.29  tff(f_41, axiom, (![A, B, C]: (k3_xboole_0(k3_xboole_0(A, B), C) = k3_xboole_0(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t16_xboole_1)).
% 9.11/3.29  tff(c_32, plain, (k3_xboole_0('#skF_1', '#skF_3')!=k1_tarski('#skF_4')), inference(cnfTransformation, [status(thm)], [f_68])).
% 9.11/3.29  tff(c_34, plain, (r2_hidden('#skF_4', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_68])).
% 9.11/3.29  tff(c_22, plain, (![A_16]: (k2_tarski(A_16, A_16)=k1_tarski(A_16))), inference(cnfTransformation, [status(thm)], [f_47])).
% 9.11/3.29  tff(c_2024, plain, (![A_84, C_85, B_86]: (k3_xboole_0(k2_tarski(A_84, C_85), B_86)=k2_tarski(A_84, C_85) | ~r2_hidden(C_85, B_86) | ~r2_hidden(A_84, B_86))), inference(cnfTransformation, [status(thm)], [f_59])).
% 9.11/3.29  tff(c_2116, plain, (![A_16, B_86]: (k3_xboole_0(k1_tarski(A_16), B_86)=k2_tarski(A_16, A_16) | ~r2_hidden(A_16, B_86) | ~r2_hidden(A_16, B_86))), inference(superposition, [status(thm), theory('equality')], [c_22, c_2024])).
% 9.11/3.29  tff(c_13716, plain, (![A_170, B_171]: (k3_xboole_0(k1_tarski(A_170), B_171)=k1_tarski(A_170) | ~r2_hidden(A_170, B_171) | ~r2_hidden(A_170, B_171))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_2116])).
% 9.11/3.29  tff(c_36, plain, (k3_xboole_0('#skF_2', '#skF_3')=k1_tarski('#skF_4')), inference(cnfTransformation, [status(thm)], [f_68])).
% 9.11/3.29  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 9.11/3.29  tff(c_4, plain, (![A_3]: (k3_xboole_0(A_3, A_3)=A_3)), inference(cnfTransformation, [status(thm)], [f_29])).
% 9.11/3.29  tff(c_10, plain, (![B_6]: (r1_tarski(B_6, B_6))), inference(cnfTransformation, [status(thm)], [f_35])).
% 9.11/3.29  tff(c_115, plain, (![A_34, B_35]: (k4_xboole_0(A_34, B_35)=k1_xboole_0 | ~r1_tarski(A_34, B_35))), inference(cnfTransformation, [status(thm)], [f_39])).
% 9.11/3.29  tff(c_122, plain, (![B_6]: (k4_xboole_0(B_6, B_6)=k1_xboole_0)), inference(resolution, [status(thm)], [c_10, c_115])).
% 9.11/3.29  tff(c_167, plain, (![A_43, B_44]: (k4_xboole_0(A_43, k4_xboole_0(A_43, B_44))=k3_xboole_0(A_43, B_44))), inference(cnfTransformation, [status(thm)], [f_45])).
% 9.11/3.29  tff(c_185, plain, (![B_6]: (k4_xboole_0(B_6, k1_xboole_0)=k3_xboole_0(B_6, B_6))), inference(superposition, [status(thm), theory('equality')], [c_122, c_167])).
% 9.11/3.29  tff(c_188, plain, (![B_6]: (k4_xboole_0(B_6, k1_xboole_0)=B_6)), inference(demodulation, [status(thm), theory('equality')], [c_4, c_185])).
% 9.11/3.29  tff(c_38, plain, (r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_68])).
% 9.11/3.29  tff(c_123, plain, (k4_xboole_0('#skF_1', '#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_38, c_115])).
% 9.11/3.29  tff(c_182, plain, (k4_xboole_0('#skF_1', k1_xboole_0)=k3_xboole_0('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_123, c_167])).
% 9.11/3.29  tff(c_383, plain, (k3_xboole_0('#skF_1', '#skF_2')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_188, c_182])).
% 9.11/3.29  tff(c_825, plain, (![A_64, B_65, C_66]: (k3_xboole_0(k3_xboole_0(A_64, B_65), C_66)=k3_xboole_0(A_64, k3_xboole_0(B_65, C_66)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 9.11/3.29  tff(c_1171, plain, (![C_70]: (k3_xboole_0('#skF_1', k3_xboole_0('#skF_2', C_70))=k3_xboole_0('#skF_1', C_70))), inference(superposition, [status(thm), theory('equality')], [c_383, c_825])).
% 9.11/3.29  tff(c_1235, plain, (![A_1]: (k3_xboole_0('#skF_1', k3_xboole_0(A_1, '#skF_2'))=k3_xboole_0('#skF_1', A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_1171])).
% 9.11/3.29  tff(c_3699, plain, (![C_102, A_103, B_104]: (k3_xboole_0(C_102, k3_xboole_0(A_103, B_104))=k3_xboole_0(A_103, k3_xboole_0(B_104, C_102)))), inference(superposition, [status(thm), theory('equality')], [c_825, c_2])).
% 9.11/3.29  tff(c_4234, plain, (![A_3, C_102]: (k3_xboole_0(A_3, k3_xboole_0(A_3, C_102))=k3_xboole_0(C_102, A_3))), inference(superposition, [status(thm), theory('equality')], [c_4, c_3699])).
% 9.11/3.29  tff(c_4924, plain, (![C_109]: (k3_xboole_0('#skF_1', k3_xboole_0('#skF_2', C_109))=k3_xboole_0(C_109, '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_383, c_3699])).
% 9.11/3.29  tff(c_5022, plain, (![C_102]: (k3_xboole_0(k3_xboole_0('#skF_2', C_102), '#skF_1')=k3_xboole_0('#skF_1', k3_xboole_0(C_102, '#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_4234, c_4924])).
% 9.11/3.29  tff(c_6561, plain, (![C_119]: (k3_xboole_0(k3_xboole_0('#skF_2', C_119), '#skF_1')=k3_xboole_0('#skF_1', C_119))), inference(demodulation, [status(thm), theory('equality')], [c_1235, c_5022])).
% 9.11/3.29  tff(c_6724, plain, (k3_xboole_0(k1_tarski('#skF_4'), '#skF_1')=k3_xboole_0('#skF_1', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_36, c_6561])).
% 9.11/3.29  tff(c_13795, plain, (k3_xboole_0('#skF_1', '#skF_3')=k1_tarski('#skF_4') | ~r2_hidden('#skF_4', '#skF_1') | ~r2_hidden('#skF_4', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_13716, c_6724])).
% 9.11/3.29  tff(c_14034, plain, (k3_xboole_0('#skF_1', '#skF_3')=k1_tarski('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_34, c_13795])).
% 9.11/3.29  tff(c_14036, plain, $false, inference(negUnitSimplification, [status(thm)], [c_32, c_14034])).
% 9.11/3.29  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.11/3.29  
% 9.11/3.29  Inference rules
% 9.11/3.29  ----------------------
% 9.11/3.29  #Ref     : 0
% 9.11/3.29  #Sup     : 3423
% 9.11/3.29  #Fact    : 0
% 9.11/3.29  #Define  : 0
% 9.11/3.29  #Split   : 1
% 9.11/3.29  #Chain   : 0
% 9.11/3.29  #Close   : 0
% 9.11/3.29  
% 9.11/3.29  Ordering : KBO
% 9.11/3.29  
% 9.11/3.29  Simplification rules
% 9.11/3.29  ----------------------
% 9.11/3.29  #Subsume      : 100
% 9.11/3.29  #Demod        : 4150
% 9.11/3.29  #Tautology    : 2223
% 9.11/3.29  #SimpNegUnit  : 1
% 9.11/3.29  #BackRed      : 3
% 9.11/3.29  
% 9.11/3.29  #Partial instantiations: 0
% 9.11/3.29  #Strategies tried      : 1
% 9.11/3.29  
% 9.11/3.29  Timing (in seconds)
% 9.11/3.29  ----------------------
% 9.11/3.30  Preprocessing        : 0.31
% 9.11/3.30  Parsing              : 0.17
% 9.11/3.30  CNF conversion       : 0.02
% 9.11/3.30  Main loop            : 2.21
% 9.11/3.30  Inferencing          : 0.47
% 9.11/3.30  Reduction            : 1.31
% 9.11/3.30  Demodulation         : 1.17
% 9.11/3.30  BG Simplification    : 0.06
% 9.11/3.30  Subsumption          : 0.28
% 9.11/3.30  Abstraction          : 0.09
% 9.11/3.30  MUC search           : 0.00
% 9.11/3.30  Cooper               : 0.00
% 9.11/3.30  Total                : 2.55
% 9.11/3.30  Index Insertion      : 0.00
% 9.11/3.30  Index Deletion       : 0.00
% 9.11/3.30  Index Matching       : 0.00
% 9.11/3.30  BG Taut test         : 0.00
%------------------------------------------------------------------------------
