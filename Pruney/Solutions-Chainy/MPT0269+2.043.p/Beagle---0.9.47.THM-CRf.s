%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:52:49 EST 2020

% Result     : Theorem 2.92s
% Output     : CNFRefutation 3.20s
% Verified   : 
% Statistics : Number of formulae       :   54 (  77 expanded)
%              Number of leaves         :   28 (  39 expanded)
%              Depth                    :   12
%              Number of atoms          :   43 (  70 expanded)
%              Number of equality atoms :   37 (  64 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

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

tff(f_69,negated_conjecture,(
    ~ ! [A,B] :
        ~ ( k4_xboole_0(A,k1_tarski(B)) = k1_xboole_0
          & A != k1_xboole_0
          & A != k1_tarski(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_zfmisc_1)).

tff(f_33,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

tff(f_31,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_37,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_41,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k5_xboole_0(k5_xboole_0(A,B),k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

tff(f_29,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_39,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k1_tarski(B))
    <=> ( A = k1_xboole_0
        | A = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).

tff(c_38,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_36,plain,(
    k1_tarski('#skF_2') != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_8,plain,(
    ! [A_7] : k5_xboole_0(A_7,k1_xboole_0) = A_7 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_40,plain,(
    k4_xboole_0('#skF_1',k1_tarski('#skF_2')) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_6,plain,(
    ! [A_5,B_6] : k5_xboole_0(A_5,k3_xboole_0(A_5,B_6)) = k4_xboole_0(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_295,plain,(
    ! [A_63,B_64,C_65] : k5_xboole_0(k5_xboole_0(A_63,B_64),C_65) = k5_xboole_0(A_63,k5_xboole_0(B_64,C_65)) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_16,plain,(
    ! [A_14,B_15] : k5_xboole_0(k5_xboole_0(A_14,B_15),k2_xboole_0(A_14,B_15)) = k3_xboole_0(A_14,B_15) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_1218,plain,(
    ! [A_92,B_93] : k5_xboole_0(A_92,k5_xboole_0(B_93,k2_xboole_0(A_92,B_93))) = k3_xboole_0(A_92,B_93) ),
    inference(superposition,[status(thm),theory(equality)],[c_295,c_16])).

tff(c_2,plain,(
    ! [A_1] : k2_xboole_0(A_1,A_1) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_4,plain,(
    ! [A_3] : k3_xboole_0(A_3,A_3) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_14,plain,(
    ! [A_13] : k5_xboole_0(A_13,A_13) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_178,plain,(
    ! [A_58,B_59] : k5_xboole_0(k5_xboole_0(A_58,B_59),k2_xboole_0(A_58,B_59)) = k3_xboole_0(A_58,B_59) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_196,plain,(
    ! [A_13] : k5_xboole_0(k1_xboole_0,k2_xboole_0(A_13,A_13)) = k3_xboole_0(A_13,A_13) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_178])).

tff(c_205,plain,(
    ! [A_13] : k5_xboole_0(k1_xboole_0,A_13) = A_13 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_4,c_196])).

tff(c_356,plain,(
    ! [A_13,C_65] : k5_xboole_0(A_13,k5_xboole_0(A_13,C_65)) = k5_xboole_0(k1_xboole_0,C_65) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_295])).

tff(c_374,plain,(
    ! [A_13,C_65] : k5_xboole_0(A_13,k5_xboole_0(A_13,C_65)) = C_65 ),
    inference(demodulation,[status(thm),theory(equality)],[c_205,c_356])).

tff(c_1233,plain,(
    ! [B_93,A_92] : k5_xboole_0(B_93,k2_xboole_0(A_92,B_93)) = k5_xboole_0(A_92,k3_xboole_0(A_92,B_93)) ),
    inference(superposition,[status(thm),theory(equality)],[c_1218,c_374])).

tff(c_1299,plain,(
    ! [B_94,A_95] : k5_xboole_0(B_94,k2_xboole_0(A_95,B_94)) = k4_xboole_0(A_95,B_94) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_1233])).

tff(c_1627,plain,(
    ! [B_103,A_104] : k5_xboole_0(B_103,k4_xboole_0(A_104,B_103)) = k2_xboole_0(A_104,B_103) ),
    inference(superposition,[status(thm),theory(equality)],[c_1299,c_374])).

tff(c_1687,plain,(
    k5_xboole_0(k1_tarski('#skF_2'),k1_xboole_0) = k2_xboole_0('#skF_1',k1_tarski('#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_1627])).

tff(c_1698,plain,(
    k2_xboole_0('#skF_1',k1_tarski('#skF_2')) = k1_tarski('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_1687])).

tff(c_10,plain,(
    ! [A_8,B_9] : r1_tarski(A_8,k2_xboole_0(A_8,B_9)) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_1708,plain,(
    r1_tarski('#skF_1',k1_tarski('#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1698,c_10])).

tff(c_28,plain,(
    ! [B_32,A_31] :
      ( k1_tarski(B_32) = A_31
      | k1_xboole_0 = A_31
      | ~ r1_tarski(A_31,k1_tarski(B_32)) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_1716,plain,
    ( k1_tarski('#skF_2') = '#skF_1'
    | k1_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_1708,c_28])).

tff(c_1720,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_36,c_1716])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n006.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 15:57:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.92/1.45  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.92/1.46  
% 2.92/1.46  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.19/1.46  %$ r1_tarski > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1
% 3.19/1.46  
% 3.19/1.46  %Foreground sorts:
% 3.19/1.46  
% 3.19/1.46  
% 3.19/1.46  %Background operators:
% 3.19/1.46  
% 3.19/1.46  
% 3.19/1.46  %Foreground operators:
% 3.19/1.46  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.19/1.46  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.19/1.46  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.19/1.46  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.19/1.46  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.19/1.46  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.19/1.46  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.19/1.46  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.19/1.46  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.19/1.46  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.19/1.46  tff('#skF_2', type, '#skF_2': $i).
% 3.19/1.46  tff('#skF_1', type, '#skF_1': $i).
% 3.19/1.46  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.19/1.46  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.19/1.46  tff(k3_tarski, type, k3_tarski: $i > $i).
% 3.19/1.46  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.19/1.46  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.19/1.46  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.19/1.46  
% 3.20/1.47  tff(f_69, negated_conjecture, ~(![A, B]: ~(((k4_xboole_0(A, k1_tarski(B)) = k1_xboole_0) & ~(A = k1_xboole_0)) & ~(A = k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t66_zfmisc_1)).
% 3.20/1.47  tff(f_33, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 3.20/1.47  tff(f_31, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 3.20/1.47  tff(f_37, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_xboole_1)).
% 3.20/1.47  tff(f_41, axiom, (![A, B]: (k3_xboole_0(A, B) = k5_xboole_0(k5_xboole_0(A, B), k2_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t95_xboole_1)).
% 3.20/1.47  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k2_xboole_0)).
% 3.20/1.47  tff(f_29, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 3.20/1.47  tff(f_39, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t92_xboole_1)).
% 3.20/1.47  tff(f_35, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 3.20/1.47  tff(f_57, axiom, (![A, B]: (r1_tarski(A, k1_tarski(B)) <=> ((A = k1_xboole_0) | (A = k1_tarski(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_zfmisc_1)).
% 3.20/1.47  tff(c_38, plain, (k1_xboole_0!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.20/1.47  tff(c_36, plain, (k1_tarski('#skF_2')!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.20/1.47  tff(c_8, plain, (![A_7]: (k5_xboole_0(A_7, k1_xboole_0)=A_7)), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.20/1.47  tff(c_40, plain, (k4_xboole_0('#skF_1', k1_tarski('#skF_2'))=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.20/1.47  tff(c_6, plain, (![A_5, B_6]: (k5_xboole_0(A_5, k3_xboole_0(A_5, B_6))=k4_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.20/1.47  tff(c_295, plain, (![A_63, B_64, C_65]: (k5_xboole_0(k5_xboole_0(A_63, B_64), C_65)=k5_xboole_0(A_63, k5_xboole_0(B_64, C_65)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.20/1.47  tff(c_16, plain, (![A_14, B_15]: (k5_xboole_0(k5_xboole_0(A_14, B_15), k2_xboole_0(A_14, B_15))=k3_xboole_0(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.20/1.47  tff(c_1218, plain, (![A_92, B_93]: (k5_xboole_0(A_92, k5_xboole_0(B_93, k2_xboole_0(A_92, B_93)))=k3_xboole_0(A_92, B_93))), inference(superposition, [status(thm), theory('equality')], [c_295, c_16])).
% 3.20/1.47  tff(c_2, plain, (![A_1]: (k2_xboole_0(A_1, A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.20/1.47  tff(c_4, plain, (![A_3]: (k3_xboole_0(A_3, A_3)=A_3)), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.20/1.47  tff(c_14, plain, (![A_13]: (k5_xboole_0(A_13, A_13)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.20/1.47  tff(c_178, plain, (![A_58, B_59]: (k5_xboole_0(k5_xboole_0(A_58, B_59), k2_xboole_0(A_58, B_59))=k3_xboole_0(A_58, B_59))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.20/1.47  tff(c_196, plain, (![A_13]: (k5_xboole_0(k1_xboole_0, k2_xboole_0(A_13, A_13))=k3_xboole_0(A_13, A_13))), inference(superposition, [status(thm), theory('equality')], [c_14, c_178])).
% 3.20/1.47  tff(c_205, plain, (![A_13]: (k5_xboole_0(k1_xboole_0, A_13)=A_13)), inference(demodulation, [status(thm), theory('equality')], [c_2, c_4, c_196])).
% 3.20/1.47  tff(c_356, plain, (![A_13, C_65]: (k5_xboole_0(A_13, k5_xboole_0(A_13, C_65))=k5_xboole_0(k1_xboole_0, C_65))), inference(superposition, [status(thm), theory('equality')], [c_14, c_295])).
% 3.20/1.47  tff(c_374, plain, (![A_13, C_65]: (k5_xboole_0(A_13, k5_xboole_0(A_13, C_65))=C_65)), inference(demodulation, [status(thm), theory('equality')], [c_205, c_356])).
% 3.20/1.47  tff(c_1233, plain, (![B_93, A_92]: (k5_xboole_0(B_93, k2_xboole_0(A_92, B_93))=k5_xboole_0(A_92, k3_xboole_0(A_92, B_93)))), inference(superposition, [status(thm), theory('equality')], [c_1218, c_374])).
% 3.20/1.47  tff(c_1299, plain, (![B_94, A_95]: (k5_xboole_0(B_94, k2_xboole_0(A_95, B_94))=k4_xboole_0(A_95, B_94))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_1233])).
% 3.20/1.47  tff(c_1627, plain, (![B_103, A_104]: (k5_xboole_0(B_103, k4_xboole_0(A_104, B_103))=k2_xboole_0(A_104, B_103))), inference(superposition, [status(thm), theory('equality')], [c_1299, c_374])).
% 3.20/1.47  tff(c_1687, plain, (k5_xboole_0(k1_tarski('#skF_2'), k1_xboole_0)=k2_xboole_0('#skF_1', k1_tarski('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_40, c_1627])).
% 3.20/1.47  tff(c_1698, plain, (k2_xboole_0('#skF_1', k1_tarski('#skF_2'))=k1_tarski('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_8, c_1687])).
% 3.20/1.47  tff(c_10, plain, (![A_8, B_9]: (r1_tarski(A_8, k2_xboole_0(A_8, B_9)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.20/1.47  tff(c_1708, plain, (r1_tarski('#skF_1', k1_tarski('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_1698, c_10])).
% 3.20/1.47  tff(c_28, plain, (![B_32, A_31]: (k1_tarski(B_32)=A_31 | k1_xboole_0=A_31 | ~r1_tarski(A_31, k1_tarski(B_32)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.20/1.47  tff(c_1716, plain, (k1_tarski('#skF_2')='#skF_1' | k1_xboole_0='#skF_1'), inference(resolution, [status(thm)], [c_1708, c_28])).
% 3.20/1.47  tff(c_1720, plain, $false, inference(negUnitSimplification, [status(thm)], [c_38, c_36, c_1716])).
% 3.20/1.47  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.20/1.47  
% 3.20/1.47  Inference rules
% 3.20/1.47  ----------------------
% 3.20/1.47  #Ref     : 0
% 3.20/1.47  #Sup     : 417
% 3.20/1.47  #Fact    : 0
% 3.20/1.47  #Define  : 0
% 3.20/1.47  #Split   : 0
% 3.20/1.47  #Chain   : 0
% 3.20/1.47  #Close   : 0
% 3.20/1.47  
% 3.20/1.47  Ordering : KBO
% 3.20/1.47  
% 3.20/1.47  Simplification rules
% 3.20/1.47  ----------------------
% 3.20/1.47  #Subsume      : 3
% 3.20/1.47  #Demod        : 254
% 3.20/1.47  #Tautology    : 266
% 3.20/1.47  #SimpNegUnit  : 1
% 3.20/1.47  #BackRed      : 2
% 3.20/1.47  
% 3.20/1.47  #Partial instantiations: 0
% 3.20/1.47  #Strategies tried      : 1
% 3.20/1.47  
% 3.20/1.47  Timing (in seconds)
% 3.20/1.47  ----------------------
% 3.20/1.48  Preprocessing        : 0.30
% 3.20/1.48  Parsing              : 0.16
% 3.20/1.48  CNF conversion       : 0.02
% 3.20/1.48  Main loop            : 0.41
% 3.20/1.48  Inferencing          : 0.15
% 3.20/1.48  Reduction            : 0.16
% 3.20/1.48  Demodulation         : 0.13
% 3.20/1.48  BG Simplification    : 0.02
% 3.20/1.48  Subsumption          : 0.06
% 3.20/1.48  Abstraction          : 0.02
% 3.20/1.48  MUC search           : 0.00
% 3.20/1.48  Cooper               : 0.00
% 3.20/1.48  Total                : 0.74
% 3.20/1.48  Index Insertion      : 0.00
% 3.20/1.48  Index Deletion       : 0.00
% 3.20/1.48  Index Matching       : 0.00
% 3.20/1.48  BG Taut test         : 0.00
%------------------------------------------------------------------------------
