%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:57:24 EST 2020

% Result     : Theorem 2.29s
% Output     : CNFRefutation 2.29s
% Verified   : 
% Statistics : Number of formulae       :   52 (  74 expanded)
%              Number of leaves         :   29 (  37 expanded)
%              Depth                    :   10
%              Number of atoms          :   50 (  79 expanded)
%              Number of equality atoms :   42 (  64 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i ) > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_50,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_52,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_46,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

tff(f_27,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

tff(f_29,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_31,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_61,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,k1_tarski(B)) = A
    <=> ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_zfmisc_1)).

tff(f_73,axiom,(
    ! [A] : k1_setfam_1(k1_tarski(A)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_setfam_1)).

tff(f_48,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_xboole_0(k1_tarski(A),k1_tarski(B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_enumset1)).

tff(f_71,axiom,(
    ! [A,B] :
      ~ ( A != k1_xboole_0
        & B != k1_xboole_0
        & k1_setfam_1(k2_xboole_0(A,B)) != k3_xboole_0(k1_setfam_1(A),k1_setfam_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_setfam_1)).

tff(f_76,negated_conjecture,(
    ~ ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

tff(c_34,plain,(
    ! [A_14] : k2_tarski(A_14,A_14) = k1_tarski(A_14) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_117,plain,(
    ! [A_43,B_44] : k1_enumset1(A_43,A_43,B_44) = k2_tarski(A_43,B_44) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_10,plain,(
    ! [E_11,A_5,B_6] : r2_hidden(E_11,k1_enumset1(A_5,B_6,E_11)) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_135,plain,(
    ! [B_45,A_46] : r2_hidden(B_45,k2_tarski(A_46,B_45)) ),
    inference(superposition,[status(thm),theory(equality)],[c_117,c_10])).

tff(c_138,plain,(
    ! [A_14] : r2_hidden(A_14,k1_tarski(A_14)) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_135])).

tff(c_2,plain,(
    ! [A_1] : k3_xboole_0(A_1,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_4,plain,(
    ! [A_2] : k4_xboole_0(A_2,k1_xboole_0) = A_2 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_188,plain,(
    ! [A_57,B_58] : k4_xboole_0(A_57,k4_xboole_0(A_57,B_58)) = k3_xboole_0(A_57,B_58) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_206,plain,(
    ! [A_2] : k4_xboole_0(A_2,A_2) = k3_xboole_0(A_2,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_188])).

tff(c_210,plain,(
    ! [A_59] : k4_xboole_0(A_59,A_59) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_206])).

tff(c_42,plain,(
    ! [B_23,A_22] :
      ( ~ r2_hidden(B_23,A_22)
      | k4_xboole_0(A_22,k1_tarski(B_23)) != A_22 ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_223,plain,(
    ! [B_23] :
      ( ~ r2_hidden(B_23,k1_tarski(B_23))
      | k1_tarski(B_23) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_210,c_42])).

tff(c_242,plain,(
    ! [B_23] : k1_tarski(B_23) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_138,c_223])).

tff(c_48,plain,(
    ! [A_26] : k1_setfam_1(k1_tarski(A_26)) = A_26 ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_32,plain,(
    ! [A_12,B_13] : k2_xboole_0(k1_tarski(A_12),k1_tarski(B_13)) = k2_tarski(A_12,B_13) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_343,plain,(
    ! [A_73,B_74] :
      ( k3_xboole_0(k1_setfam_1(A_73),k1_setfam_1(B_74)) = k1_setfam_1(k2_xboole_0(A_73,B_74))
      | k1_xboole_0 = B_74
      | k1_xboole_0 = A_73 ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_363,plain,(
    ! [A_26,B_74] :
      ( k1_setfam_1(k2_xboole_0(k1_tarski(A_26),B_74)) = k3_xboole_0(A_26,k1_setfam_1(B_74))
      | k1_xboole_0 = B_74
      | k1_tarski(A_26) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_343])).

tff(c_485,plain,(
    ! [A_90,B_91] :
      ( k1_setfam_1(k2_xboole_0(k1_tarski(A_90),B_91)) = k3_xboole_0(A_90,k1_setfam_1(B_91))
      | k1_xboole_0 = B_91 ) ),
    inference(negUnitSimplification,[status(thm)],[c_242,c_363])).

tff(c_508,plain,(
    ! [A_12,B_13] :
      ( k3_xboole_0(A_12,k1_setfam_1(k1_tarski(B_13))) = k1_setfam_1(k2_tarski(A_12,B_13))
      | k1_tarski(B_13) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_485])).

tff(c_519,plain,(
    ! [A_12,B_13] :
      ( k1_setfam_1(k2_tarski(A_12,B_13)) = k3_xboole_0(A_12,B_13)
      | k1_tarski(B_13) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_508])).

tff(c_520,plain,(
    ! [A_12,B_13] : k1_setfam_1(k2_tarski(A_12,B_13)) = k3_xboole_0(A_12,B_13) ),
    inference(negUnitSimplification,[status(thm)],[c_242,c_519])).

tff(c_50,plain,(
    k1_setfam_1(k2_tarski('#skF_3','#skF_4')) != k3_xboole_0('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_526,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_520,c_50])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n016.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 15:35:49 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.29/1.30  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.29/1.31  
% 2.29/1.31  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.29/1.31  %$ r2_hidden > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 2.29/1.31  
% 2.29/1.31  %Foreground sorts:
% 2.29/1.31  
% 2.29/1.31  
% 2.29/1.31  %Background operators:
% 2.29/1.31  
% 2.29/1.31  
% 2.29/1.31  %Foreground operators:
% 2.29/1.31  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.29/1.31  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.29/1.31  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.29/1.31  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.29/1.31  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.29/1.31  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.29/1.31  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.29/1.31  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 2.29/1.31  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.29/1.31  tff('#skF_3', type, '#skF_3': $i).
% 2.29/1.31  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.29/1.31  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.29/1.31  tff('#skF_4', type, '#skF_4': $i).
% 2.29/1.31  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.29/1.31  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.29/1.31  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.29/1.31  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 2.29/1.31  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.29/1.31  
% 2.29/1.32  tff(f_50, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 2.29/1.32  tff(f_52, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 2.29/1.32  tff(f_46, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_enumset1)).
% 2.29/1.32  tff(f_27, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 2.29/1.32  tff(f_29, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 2.29/1.32  tff(f_31, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 2.29/1.32  tff(f_61, axiom, (![A, B]: ((k4_xboole_0(A, k1_tarski(B)) = A) <=> ~r2_hidden(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_zfmisc_1)).
% 2.29/1.32  tff(f_73, axiom, (![A]: (k1_setfam_1(k1_tarski(A)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_setfam_1)).
% 2.29/1.32  tff(f_48, axiom, (![A, B]: (k2_tarski(A, B) = k2_xboole_0(k1_tarski(A), k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_enumset1)).
% 2.29/1.32  tff(f_71, axiom, (![A, B]: ~((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(k1_setfam_1(k2_xboole_0(A, B)) = k3_xboole_0(k1_setfam_1(A), k1_setfam_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_setfam_1)).
% 2.29/1.32  tff(f_76, negated_conjecture, ~(![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_setfam_1)).
% 2.29/1.32  tff(c_34, plain, (![A_14]: (k2_tarski(A_14, A_14)=k1_tarski(A_14))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.29/1.32  tff(c_117, plain, (![A_43, B_44]: (k1_enumset1(A_43, A_43, B_44)=k2_tarski(A_43, B_44))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.29/1.32  tff(c_10, plain, (![E_11, A_5, B_6]: (r2_hidden(E_11, k1_enumset1(A_5, B_6, E_11)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.29/1.32  tff(c_135, plain, (![B_45, A_46]: (r2_hidden(B_45, k2_tarski(A_46, B_45)))), inference(superposition, [status(thm), theory('equality')], [c_117, c_10])).
% 2.29/1.32  tff(c_138, plain, (![A_14]: (r2_hidden(A_14, k1_tarski(A_14)))), inference(superposition, [status(thm), theory('equality')], [c_34, c_135])).
% 2.29/1.32  tff(c_2, plain, (![A_1]: (k3_xboole_0(A_1, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.29/1.32  tff(c_4, plain, (![A_2]: (k4_xboole_0(A_2, k1_xboole_0)=A_2)), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.29/1.32  tff(c_188, plain, (![A_57, B_58]: (k4_xboole_0(A_57, k4_xboole_0(A_57, B_58))=k3_xboole_0(A_57, B_58))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.29/1.32  tff(c_206, plain, (![A_2]: (k4_xboole_0(A_2, A_2)=k3_xboole_0(A_2, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_4, c_188])).
% 2.29/1.32  tff(c_210, plain, (![A_59]: (k4_xboole_0(A_59, A_59)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_2, c_206])).
% 2.29/1.32  tff(c_42, plain, (![B_23, A_22]: (~r2_hidden(B_23, A_22) | k4_xboole_0(A_22, k1_tarski(B_23))!=A_22)), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.29/1.32  tff(c_223, plain, (![B_23]: (~r2_hidden(B_23, k1_tarski(B_23)) | k1_tarski(B_23)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_210, c_42])).
% 2.29/1.32  tff(c_242, plain, (![B_23]: (k1_tarski(B_23)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_138, c_223])).
% 2.29/1.32  tff(c_48, plain, (![A_26]: (k1_setfam_1(k1_tarski(A_26))=A_26)), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.29/1.32  tff(c_32, plain, (![A_12, B_13]: (k2_xboole_0(k1_tarski(A_12), k1_tarski(B_13))=k2_tarski(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.29/1.32  tff(c_343, plain, (![A_73, B_74]: (k3_xboole_0(k1_setfam_1(A_73), k1_setfam_1(B_74))=k1_setfam_1(k2_xboole_0(A_73, B_74)) | k1_xboole_0=B_74 | k1_xboole_0=A_73)), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.29/1.32  tff(c_363, plain, (![A_26, B_74]: (k1_setfam_1(k2_xboole_0(k1_tarski(A_26), B_74))=k3_xboole_0(A_26, k1_setfam_1(B_74)) | k1_xboole_0=B_74 | k1_tarski(A_26)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_48, c_343])).
% 2.29/1.32  tff(c_485, plain, (![A_90, B_91]: (k1_setfam_1(k2_xboole_0(k1_tarski(A_90), B_91))=k3_xboole_0(A_90, k1_setfam_1(B_91)) | k1_xboole_0=B_91)), inference(negUnitSimplification, [status(thm)], [c_242, c_363])).
% 2.29/1.32  tff(c_508, plain, (![A_12, B_13]: (k3_xboole_0(A_12, k1_setfam_1(k1_tarski(B_13)))=k1_setfam_1(k2_tarski(A_12, B_13)) | k1_tarski(B_13)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_32, c_485])).
% 2.29/1.32  tff(c_519, plain, (![A_12, B_13]: (k1_setfam_1(k2_tarski(A_12, B_13))=k3_xboole_0(A_12, B_13) | k1_tarski(B_13)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_48, c_508])).
% 2.29/1.32  tff(c_520, plain, (![A_12, B_13]: (k1_setfam_1(k2_tarski(A_12, B_13))=k3_xboole_0(A_12, B_13))), inference(negUnitSimplification, [status(thm)], [c_242, c_519])).
% 2.29/1.32  tff(c_50, plain, (k1_setfam_1(k2_tarski('#skF_3', '#skF_4'))!=k3_xboole_0('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.29/1.32  tff(c_526, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_520, c_50])).
% 2.29/1.32  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.29/1.32  
% 2.29/1.32  Inference rules
% 2.29/1.32  ----------------------
% 2.29/1.32  #Ref     : 0
% 2.29/1.32  #Sup     : 106
% 2.29/1.32  #Fact    : 0
% 2.29/1.32  #Define  : 0
% 2.29/1.32  #Split   : 0
% 2.29/1.32  #Chain   : 0
% 2.29/1.32  #Close   : 0
% 2.29/1.32  
% 2.29/1.32  Ordering : KBO
% 2.29/1.32  
% 2.29/1.32  Simplification rules
% 2.29/1.32  ----------------------
% 2.29/1.32  #Subsume      : 2
% 2.29/1.32  #Demod        : 48
% 2.29/1.32  #Tautology    : 76
% 2.29/1.32  #SimpNegUnit  : 12
% 2.29/1.32  #BackRed      : 1
% 2.29/1.32  
% 2.29/1.32  #Partial instantiations: 0
% 2.29/1.32  #Strategies tried      : 1
% 2.29/1.32  
% 2.29/1.32  Timing (in seconds)
% 2.29/1.32  ----------------------
% 2.29/1.33  Preprocessing        : 0.31
% 2.29/1.33  Parsing              : 0.16
% 2.29/1.33  CNF conversion       : 0.02
% 2.29/1.33  Main loop            : 0.25
% 2.29/1.33  Inferencing          : 0.10
% 2.29/1.33  Reduction            : 0.08
% 2.29/1.33  Demodulation         : 0.06
% 2.29/1.33  BG Simplification    : 0.02
% 2.29/1.33  Subsumption          : 0.04
% 2.29/1.33  Abstraction          : 0.02
% 2.29/1.33  MUC search           : 0.00
% 2.29/1.33  Cooper               : 0.00
% 2.29/1.33  Total                : 0.59
% 2.29/1.33  Index Insertion      : 0.00
% 2.29/1.33  Index Deletion       : 0.00
% 2.29/1.33  Index Matching       : 0.00
% 2.29/1.33  BG Taut test         : 0.00
%------------------------------------------------------------------------------
