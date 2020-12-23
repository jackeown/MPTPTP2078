%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:52:45 EST 2020

% Result     : Theorem 3.01s
% Output     : CNFRefutation 3.15s
% Verified   : 
% Statistics : Number of formulae       :   57 (  63 expanded)
%              Number of leaves         :   30 (  34 expanded)
%              Depth                    :   11
%              Number of atoms          :   50 (  62 expanded)
%              Number of equality atoms :   31 (  43 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

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

tff(f_82,negated_conjecture,(
    ~ ! [A,B] :
        ~ ( k4_xboole_0(A,k1_tarski(B)) = k1_xboole_0
          & A != k1_xboole_0
          & A != k1_tarski(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_zfmisc_1)).

tff(f_72,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,k1_tarski(B)) = A
    <=> ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_zfmisc_1)).

tff(f_65,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_43,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_37,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k5_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

tff(f_47,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_45,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_41,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(c_50,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_327,plain,(
    ! [A_80,B_81] :
      ( k4_xboole_0(A_80,k1_tarski(B_81)) = A_80
      | r2_hidden(B_81,A_80) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_52,plain,(
    k4_xboole_0('#skF_1',k1_tarski('#skF_2')) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_337,plain,
    ( k1_xboole_0 = '#skF_1'
    | r2_hidden('#skF_2','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_327,c_52])).

tff(c_349,plain,(
    r2_hidden('#skF_2','#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_337])).

tff(c_40,plain,(
    ! [A_47,B_48] :
      ( r1_tarski(k1_tarski(A_47),B_48)
      | ~ r2_hidden(A_47,B_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_48,plain,(
    k1_tarski('#skF_2') != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_18,plain,(
    ! [A_14] : k5_xboole_0(A_14,k1_xboole_0) = A_14 ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_262,plain,(
    ! [A_73,B_74] : k5_xboole_0(A_73,k3_xboole_0(A_73,B_74)) = k4_xboole_0(A_73,B_74) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_279,plain,(
    ! [A_1,B_2] : k5_xboole_0(A_1,k3_xboole_0(B_2,A_1)) = k4_xboole_0(A_1,B_2) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_262])).

tff(c_134,plain,(
    ! [B_61,A_62] : k5_xboole_0(B_61,A_62) = k5_xboole_0(A_62,B_61) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_150,plain,(
    ! [A_62] : k5_xboole_0(k1_xboole_0,A_62) = A_62 ),
    inference(superposition,[status(thm),theory(equality)],[c_134,c_18])).

tff(c_22,plain,(
    ! [A_18] : k5_xboole_0(A_18,A_18) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_656,plain,(
    ! [A_108,B_109,C_110] : k5_xboole_0(k5_xboole_0(A_108,B_109),C_110) = k5_xboole_0(A_108,k5_xboole_0(B_109,C_110)) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_724,plain,(
    ! [A_18,C_110] : k5_xboole_0(A_18,k5_xboole_0(A_18,C_110)) = k5_xboole_0(k1_xboole_0,C_110) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_656])).

tff(c_745,plain,(
    ! [A_111,C_112] : k5_xboole_0(A_111,k5_xboole_0(A_111,C_112)) = C_112 ),
    inference(demodulation,[status(thm),theory(equality)],[c_150,c_724])).

tff(c_1146,plain,(
    ! [A_134,B_135] : k5_xboole_0(A_134,k4_xboole_0(A_134,B_135)) = k3_xboole_0(B_135,A_134) ),
    inference(superposition,[status(thm),theory(equality)],[c_279,c_745])).

tff(c_1201,plain,(
    k3_xboole_0(k1_tarski('#skF_2'),'#skF_1') = k5_xboole_0('#skF_1',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_52,c_1146])).

tff(c_1211,plain,(
    k3_xboole_0(k1_tarski('#skF_2'),'#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_1201])).

tff(c_16,plain,(
    ! [A_12,B_13] : r1_tarski(k3_xboole_0(A_12,B_13),A_12) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_1239,plain,(
    r1_tarski('#skF_1',k1_tarski('#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1211,c_16])).

tff(c_6,plain,(
    ! [B_6,A_5] :
      ( B_6 = A_5
      | ~ r1_tarski(B_6,A_5)
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_1253,plain,
    ( k1_tarski('#skF_2') = '#skF_1'
    | ~ r1_tarski(k1_tarski('#skF_2'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_1239,c_6])).

tff(c_1256,plain,(
    ~ r1_tarski(k1_tarski('#skF_2'),'#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_1253])).

tff(c_1259,plain,(
    ~ r2_hidden('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_40,c_1256])).

tff(c_1263,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_349,c_1259])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:50:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.01/1.46  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.01/1.46  
% 3.01/1.46  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.01/1.46  %$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1
% 3.01/1.46  
% 3.01/1.46  %Foreground sorts:
% 3.01/1.46  
% 3.01/1.46  
% 3.01/1.46  %Background operators:
% 3.01/1.46  
% 3.01/1.46  
% 3.01/1.46  %Foreground operators:
% 3.01/1.46  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.01/1.46  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.01/1.46  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.01/1.46  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.01/1.46  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.01/1.46  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.01/1.46  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.01/1.46  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.01/1.46  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.01/1.46  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.01/1.46  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.01/1.46  tff('#skF_2', type, '#skF_2': $i).
% 3.01/1.46  tff('#skF_1', type, '#skF_1': $i).
% 3.01/1.46  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.01/1.46  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.01/1.46  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.01/1.46  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.01/1.46  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.01/1.46  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.01/1.46  
% 3.15/1.47  tff(f_82, negated_conjecture, ~(![A, B]: ~(((k4_xboole_0(A, k1_tarski(B)) = k1_xboole_0) & ~(A = k1_xboole_0)) & ~(A = k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t66_zfmisc_1)).
% 3.15/1.47  tff(f_72, axiom, (![A, B]: ((k4_xboole_0(A, k1_tarski(B)) = A) <=> ~r2_hidden(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_zfmisc_1)).
% 3.15/1.47  tff(f_65, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 3.15/1.47  tff(f_43, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 3.15/1.47  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 3.15/1.47  tff(f_37, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 3.15/1.47  tff(f_29, axiom, (![A, B]: (k5_xboole_0(A, B) = k5_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 3.15/1.47  tff(f_47, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t92_xboole_1)).
% 3.15/1.47  tff(f_45, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_xboole_1)).
% 3.15/1.47  tff(f_41, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 3.15/1.47  tff(f_35, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.15/1.47  tff(c_50, plain, (k1_xboole_0!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_82])).
% 3.15/1.47  tff(c_327, plain, (![A_80, B_81]: (k4_xboole_0(A_80, k1_tarski(B_81))=A_80 | r2_hidden(B_81, A_80))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.15/1.47  tff(c_52, plain, (k4_xboole_0('#skF_1', k1_tarski('#skF_2'))=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_82])).
% 3.15/1.47  tff(c_337, plain, (k1_xboole_0='#skF_1' | r2_hidden('#skF_2', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_327, c_52])).
% 3.15/1.47  tff(c_349, plain, (r2_hidden('#skF_2', '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_50, c_337])).
% 3.15/1.47  tff(c_40, plain, (![A_47, B_48]: (r1_tarski(k1_tarski(A_47), B_48) | ~r2_hidden(A_47, B_48))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.15/1.47  tff(c_48, plain, (k1_tarski('#skF_2')!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_82])).
% 3.15/1.47  tff(c_18, plain, (![A_14]: (k5_xboole_0(A_14, k1_xboole_0)=A_14)), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.15/1.47  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.15/1.47  tff(c_262, plain, (![A_73, B_74]: (k5_xboole_0(A_73, k3_xboole_0(A_73, B_74))=k4_xboole_0(A_73, B_74))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.15/1.47  tff(c_279, plain, (![A_1, B_2]: (k5_xboole_0(A_1, k3_xboole_0(B_2, A_1))=k4_xboole_0(A_1, B_2))), inference(superposition, [status(thm), theory('equality')], [c_2, c_262])).
% 3.15/1.47  tff(c_134, plain, (![B_61, A_62]: (k5_xboole_0(B_61, A_62)=k5_xboole_0(A_62, B_61))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.15/1.47  tff(c_150, plain, (![A_62]: (k5_xboole_0(k1_xboole_0, A_62)=A_62)), inference(superposition, [status(thm), theory('equality')], [c_134, c_18])).
% 3.15/1.47  tff(c_22, plain, (![A_18]: (k5_xboole_0(A_18, A_18)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.15/1.47  tff(c_656, plain, (![A_108, B_109, C_110]: (k5_xboole_0(k5_xboole_0(A_108, B_109), C_110)=k5_xboole_0(A_108, k5_xboole_0(B_109, C_110)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.15/1.47  tff(c_724, plain, (![A_18, C_110]: (k5_xboole_0(A_18, k5_xboole_0(A_18, C_110))=k5_xboole_0(k1_xboole_0, C_110))), inference(superposition, [status(thm), theory('equality')], [c_22, c_656])).
% 3.15/1.47  tff(c_745, plain, (![A_111, C_112]: (k5_xboole_0(A_111, k5_xboole_0(A_111, C_112))=C_112)), inference(demodulation, [status(thm), theory('equality')], [c_150, c_724])).
% 3.15/1.47  tff(c_1146, plain, (![A_134, B_135]: (k5_xboole_0(A_134, k4_xboole_0(A_134, B_135))=k3_xboole_0(B_135, A_134))), inference(superposition, [status(thm), theory('equality')], [c_279, c_745])).
% 3.15/1.47  tff(c_1201, plain, (k3_xboole_0(k1_tarski('#skF_2'), '#skF_1')=k5_xboole_0('#skF_1', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_52, c_1146])).
% 3.15/1.47  tff(c_1211, plain, (k3_xboole_0(k1_tarski('#skF_2'), '#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_18, c_1201])).
% 3.15/1.47  tff(c_16, plain, (![A_12, B_13]: (r1_tarski(k3_xboole_0(A_12, B_13), A_12))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.15/1.47  tff(c_1239, plain, (r1_tarski('#skF_1', k1_tarski('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_1211, c_16])).
% 3.15/1.47  tff(c_6, plain, (![B_6, A_5]: (B_6=A_5 | ~r1_tarski(B_6, A_5) | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.15/1.47  tff(c_1253, plain, (k1_tarski('#skF_2')='#skF_1' | ~r1_tarski(k1_tarski('#skF_2'), '#skF_1')), inference(resolution, [status(thm)], [c_1239, c_6])).
% 3.15/1.47  tff(c_1256, plain, (~r1_tarski(k1_tarski('#skF_2'), '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_48, c_1253])).
% 3.15/1.47  tff(c_1259, plain, (~r2_hidden('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_40, c_1256])).
% 3.15/1.47  tff(c_1263, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_349, c_1259])).
% 3.15/1.47  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.15/1.47  
% 3.15/1.47  Inference rules
% 3.15/1.47  ----------------------
% 3.15/1.47  #Ref     : 0
% 3.15/1.47  #Sup     : 298
% 3.15/1.47  #Fact    : 0
% 3.15/1.47  #Define  : 0
% 3.15/1.47  #Split   : 0
% 3.15/1.47  #Chain   : 0
% 3.15/1.47  #Close   : 0
% 3.15/1.47  
% 3.15/1.47  Ordering : KBO
% 3.15/1.47  
% 3.15/1.47  Simplification rules
% 3.15/1.47  ----------------------
% 3.15/1.47  #Subsume      : 7
% 3.15/1.47  #Demod        : 138
% 3.15/1.47  #Tautology    : 193
% 3.15/1.47  #SimpNegUnit  : 3
% 3.15/1.47  #BackRed      : 0
% 3.15/1.47  
% 3.15/1.47  #Partial instantiations: 0
% 3.15/1.47  #Strategies tried      : 1
% 3.15/1.47  
% 3.15/1.47  Timing (in seconds)
% 3.15/1.47  ----------------------
% 3.15/1.48  Preprocessing        : 0.32
% 3.15/1.48  Parsing              : 0.17
% 3.15/1.48  CNF conversion       : 0.02
% 3.15/1.48  Main loop            : 0.40
% 3.15/1.48  Inferencing          : 0.14
% 3.15/1.48  Reduction            : 0.16
% 3.15/1.48  Demodulation         : 0.13
% 3.15/1.48  BG Simplification    : 0.02
% 3.15/1.48  Subsumption          : 0.06
% 3.15/1.48  Abstraction          : 0.02
% 3.15/1.48  MUC search           : 0.00
% 3.15/1.48  Cooper               : 0.00
% 3.15/1.48  Total                : 0.75
% 3.15/1.48  Index Insertion      : 0.00
% 3.15/1.48  Index Deletion       : 0.00
% 3.15/1.48  Index Matching       : 0.00
% 3.15/1.48  BG Taut test         : 0.00
%------------------------------------------------------------------------------
