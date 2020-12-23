%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:57:23 EST 2020

% Result     : Theorem 2.12s
% Output     : CNFRefutation 2.12s
% Verified   : 
% Statistics : Number of formulae       :   56 (  80 expanded)
%              Number of leaves         :   29 (  39 expanded)
%              Depth                    :    9
%              Number of atoms          :   57 (  91 expanded)
%              Number of equality atoms :   44 (  66 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1

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

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

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

tff(f_31,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_59,axiom,(
    ! [A,B] :
      ~ ( r1_xboole_0(k1_tarski(A),B)
        & r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l24_zfmisc_1)).

tff(f_73,axiom,(
    ! [A] : k1_setfam_1(k1_tarski(A)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_setfam_1)).

tff(f_54,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_48,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k1_enumset1(A,B,C),k1_tarski(D)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_enumset1)).

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
    ! [A_16] : k2_tarski(A_16,A_16) = k1_tarski(A_16) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_120,plain,(
    ! [A_50,B_51] : k1_enumset1(A_50,A_50,B_51) = k2_tarski(A_50,B_51) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_10,plain,(
    ! [E_11,A_5,B_6] : r2_hidden(E_11,k1_enumset1(A_5,B_6,E_11)) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_138,plain,(
    ! [B_52,A_53] : r2_hidden(B_52,k2_tarski(A_53,B_52)) ),
    inference(superposition,[status(thm),theory(equality)],[c_120,c_10])).

tff(c_141,plain,(
    ! [A_16] : r2_hidden(A_16,k1_tarski(A_16)) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_138])).

tff(c_6,plain,(
    ! [A_3] : k3_xboole_0(A_3,A_3) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_110,plain,(
    ! [A_48,B_49] :
      ( r1_xboole_0(A_48,B_49)
      | k3_xboole_0(A_48,B_49) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_40,plain,(
    ! [A_22,B_23] :
      ( ~ r2_hidden(A_22,B_23)
      | ~ r1_xboole_0(k1_tarski(A_22),B_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_158,plain,(
    ! [A_60,B_61] :
      ( ~ r2_hidden(A_60,B_61)
      | k3_xboole_0(k1_tarski(A_60),B_61) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_110,c_40])).

tff(c_162,plain,(
    ! [A_60] :
      ( ~ r2_hidden(A_60,k1_tarski(A_60))
      | k1_tarski(A_60) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_158])).

tff(c_164,plain,(
    ! [A_60] : k1_tarski(A_60) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_141,c_162])).

tff(c_46,plain,(
    ! [A_28] : k1_setfam_1(k1_tarski(A_28)) = A_28 ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_36,plain,(
    ! [A_17,B_18] : k1_enumset1(A_17,A_17,B_18) = k2_tarski(A_17,B_18) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_38,plain,(
    ! [A_19,B_20,C_21] : k2_enumset1(A_19,A_19,B_20,C_21) = k1_enumset1(A_19,B_20,C_21) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_165,plain,(
    ! [A_62,B_63,C_64,D_65] : k2_xboole_0(k1_enumset1(A_62,B_63,C_64),k1_tarski(D_65)) = k2_enumset1(A_62,B_63,C_64,D_65) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_174,plain,(
    ! [A_17,B_18,D_65] : k2_xboole_0(k2_tarski(A_17,B_18),k1_tarski(D_65)) = k2_enumset1(A_17,A_17,B_18,D_65) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_165])).

tff(c_179,plain,(
    ! [A_67,B_68,D_69] : k2_xboole_0(k2_tarski(A_67,B_68),k1_tarski(D_69)) = k1_enumset1(A_67,B_68,D_69) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_174])).

tff(c_188,plain,(
    ! [A_16,D_69] : k2_xboole_0(k1_tarski(A_16),k1_tarski(D_69)) = k1_enumset1(A_16,A_16,D_69) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_179])).

tff(c_191,plain,(
    ! [A_16,D_69] : k2_xboole_0(k1_tarski(A_16),k1_tarski(D_69)) = k2_tarski(A_16,D_69) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_188])).

tff(c_260,plain,(
    ! [A_82,B_83] :
      ( k3_xboole_0(k1_setfam_1(A_82),k1_setfam_1(B_83)) = k1_setfam_1(k2_xboole_0(A_82,B_83))
      | k1_xboole_0 = B_83
      | k1_xboole_0 = A_82 ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_277,plain,(
    ! [A_28,B_83] :
      ( k1_setfam_1(k2_xboole_0(k1_tarski(A_28),B_83)) = k3_xboole_0(A_28,k1_setfam_1(B_83))
      | k1_xboole_0 = B_83
      | k1_tarski(A_28) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_260])).

tff(c_333,plain,(
    ! [A_90,B_91] :
      ( k1_setfam_1(k2_xboole_0(k1_tarski(A_90),B_91)) = k3_xboole_0(A_90,k1_setfam_1(B_91))
      | k1_xboole_0 = B_91 ) ),
    inference(negUnitSimplification,[status(thm)],[c_164,c_277])).

tff(c_356,plain,(
    ! [A_16,D_69] :
      ( k3_xboole_0(A_16,k1_setfam_1(k1_tarski(D_69))) = k1_setfam_1(k2_tarski(A_16,D_69))
      | k1_tarski(D_69) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_191,c_333])).

tff(c_367,plain,(
    ! [A_16,D_69] :
      ( k1_setfam_1(k2_tarski(A_16,D_69)) = k3_xboole_0(A_16,D_69)
      | k1_tarski(D_69) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_356])).

tff(c_368,plain,(
    ! [A_16,D_69] : k1_setfam_1(k2_tarski(A_16,D_69)) = k3_xboole_0(A_16,D_69) ),
    inference(negUnitSimplification,[status(thm)],[c_164,c_367])).

tff(c_48,plain,(
    k1_setfam_1(k2_tarski('#skF_3','#skF_4')) != k3_xboole_0('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_373,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_368,c_48])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n007.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 09:43:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.12/1.30  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.12/1.30  
% 2.12/1.30  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.12/1.30  %$ r2_hidden > r1_xboole_0 > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 2.12/1.30  
% 2.12/1.30  %Foreground sorts:
% 2.12/1.30  
% 2.12/1.30  
% 2.12/1.30  %Background operators:
% 2.12/1.30  
% 2.12/1.30  
% 2.12/1.30  %Foreground operators:
% 2.12/1.30  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.12/1.30  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.12/1.30  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.12/1.30  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.12/1.30  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.12/1.30  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.12/1.30  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 2.12/1.30  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.12/1.30  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.12/1.30  tff('#skF_3', type, '#skF_3': $i).
% 2.12/1.30  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.12/1.30  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.12/1.30  tff('#skF_4', type, '#skF_4': $i).
% 2.12/1.30  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.12/1.30  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.12/1.30  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.12/1.30  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 2.12/1.30  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.12/1.30  
% 2.12/1.32  tff(f_50, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 2.12/1.32  tff(f_52, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 2.12/1.32  tff(f_46, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_enumset1)).
% 2.12/1.32  tff(f_31, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 2.12/1.32  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 2.12/1.32  tff(f_59, axiom, (![A, B]: ~(r1_xboole_0(k1_tarski(A), B) & r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l24_zfmisc_1)).
% 2.12/1.32  tff(f_73, axiom, (![A]: (k1_setfam_1(k1_tarski(A)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_setfam_1)).
% 2.12/1.32  tff(f_54, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 2.12/1.32  tff(f_48, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k1_enumset1(A, B, C), k1_tarski(D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_enumset1)).
% 2.12/1.32  tff(f_71, axiom, (![A, B]: ~((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(k1_setfam_1(k2_xboole_0(A, B)) = k3_xboole_0(k1_setfam_1(A), k1_setfam_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_setfam_1)).
% 2.12/1.32  tff(f_76, negated_conjecture, ~(![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_setfam_1)).
% 2.12/1.32  tff(c_34, plain, (![A_16]: (k2_tarski(A_16, A_16)=k1_tarski(A_16))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.12/1.32  tff(c_120, plain, (![A_50, B_51]: (k1_enumset1(A_50, A_50, B_51)=k2_tarski(A_50, B_51))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.12/1.32  tff(c_10, plain, (![E_11, A_5, B_6]: (r2_hidden(E_11, k1_enumset1(A_5, B_6, E_11)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.12/1.32  tff(c_138, plain, (![B_52, A_53]: (r2_hidden(B_52, k2_tarski(A_53, B_52)))), inference(superposition, [status(thm), theory('equality')], [c_120, c_10])).
% 2.12/1.32  tff(c_141, plain, (![A_16]: (r2_hidden(A_16, k1_tarski(A_16)))), inference(superposition, [status(thm), theory('equality')], [c_34, c_138])).
% 2.12/1.32  tff(c_6, plain, (![A_3]: (k3_xboole_0(A_3, A_3)=A_3)), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.12/1.32  tff(c_110, plain, (![A_48, B_49]: (r1_xboole_0(A_48, B_49) | k3_xboole_0(A_48, B_49)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.12/1.32  tff(c_40, plain, (![A_22, B_23]: (~r2_hidden(A_22, B_23) | ~r1_xboole_0(k1_tarski(A_22), B_23))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.12/1.32  tff(c_158, plain, (![A_60, B_61]: (~r2_hidden(A_60, B_61) | k3_xboole_0(k1_tarski(A_60), B_61)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_110, c_40])).
% 2.12/1.32  tff(c_162, plain, (![A_60]: (~r2_hidden(A_60, k1_tarski(A_60)) | k1_tarski(A_60)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_6, c_158])).
% 2.12/1.32  tff(c_164, plain, (![A_60]: (k1_tarski(A_60)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_141, c_162])).
% 2.12/1.32  tff(c_46, plain, (![A_28]: (k1_setfam_1(k1_tarski(A_28))=A_28)), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.12/1.32  tff(c_36, plain, (![A_17, B_18]: (k1_enumset1(A_17, A_17, B_18)=k2_tarski(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.12/1.32  tff(c_38, plain, (![A_19, B_20, C_21]: (k2_enumset1(A_19, A_19, B_20, C_21)=k1_enumset1(A_19, B_20, C_21))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.12/1.32  tff(c_165, plain, (![A_62, B_63, C_64, D_65]: (k2_xboole_0(k1_enumset1(A_62, B_63, C_64), k1_tarski(D_65))=k2_enumset1(A_62, B_63, C_64, D_65))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.12/1.32  tff(c_174, plain, (![A_17, B_18, D_65]: (k2_xboole_0(k2_tarski(A_17, B_18), k1_tarski(D_65))=k2_enumset1(A_17, A_17, B_18, D_65))), inference(superposition, [status(thm), theory('equality')], [c_36, c_165])).
% 2.12/1.32  tff(c_179, plain, (![A_67, B_68, D_69]: (k2_xboole_0(k2_tarski(A_67, B_68), k1_tarski(D_69))=k1_enumset1(A_67, B_68, D_69))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_174])).
% 2.12/1.32  tff(c_188, plain, (![A_16, D_69]: (k2_xboole_0(k1_tarski(A_16), k1_tarski(D_69))=k1_enumset1(A_16, A_16, D_69))), inference(superposition, [status(thm), theory('equality')], [c_34, c_179])).
% 2.12/1.32  tff(c_191, plain, (![A_16, D_69]: (k2_xboole_0(k1_tarski(A_16), k1_tarski(D_69))=k2_tarski(A_16, D_69))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_188])).
% 2.12/1.32  tff(c_260, plain, (![A_82, B_83]: (k3_xboole_0(k1_setfam_1(A_82), k1_setfam_1(B_83))=k1_setfam_1(k2_xboole_0(A_82, B_83)) | k1_xboole_0=B_83 | k1_xboole_0=A_82)), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.12/1.32  tff(c_277, plain, (![A_28, B_83]: (k1_setfam_1(k2_xboole_0(k1_tarski(A_28), B_83))=k3_xboole_0(A_28, k1_setfam_1(B_83)) | k1_xboole_0=B_83 | k1_tarski(A_28)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_46, c_260])).
% 2.12/1.32  tff(c_333, plain, (![A_90, B_91]: (k1_setfam_1(k2_xboole_0(k1_tarski(A_90), B_91))=k3_xboole_0(A_90, k1_setfam_1(B_91)) | k1_xboole_0=B_91)), inference(negUnitSimplification, [status(thm)], [c_164, c_277])).
% 2.12/1.32  tff(c_356, plain, (![A_16, D_69]: (k3_xboole_0(A_16, k1_setfam_1(k1_tarski(D_69)))=k1_setfam_1(k2_tarski(A_16, D_69)) | k1_tarski(D_69)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_191, c_333])).
% 2.12/1.32  tff(c_367, plain, (![A_16, D_69]: (k1_setfam_1(k2_tarski(A_16, D_69))=k3_xboole_0(A_16, D_69) | k1_tarski(D_69)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_46, c_356])).
% 2.12/1.32  tff(c_368, plain, (![A_16, D_69]: (k1_setfam_1(k2_tarski(A_16, D_69))=k3_xboole_0(A_16, D_69))), inference(negUnitSimplification, [status(thm)], [c_164, c_367])).
% 2.12/1.32  tff(c_48, plain, (k1_setfam_1(k2_tarski('#skF_3', '#skF_4'))!=k3_xboole_0('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.12/1.32  tff(c_373, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_368, c_48])).
% 2.12/1.32  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.12/1.32  
% 2.12/1.32  Inference rules
% 2.12/1.32  ----------------------
% 2.12/1.32  #Ref     : 0
% 2.12/1.32  #Sup     : 71
% 2.12/1.32  #Fact    : 0
% 2.12/1.32  #Define  : 0
% 2.12/1.32  #Split   : 0
% 2.12/1.32  #Chain   : 0
% 2.12/1.32  #Close   : 0
% 2.12/1.32  
% 2.12/1.32  Ordering : KBO
% 2.12/1.32  
% 2.12/1.32  Simplification rules
% 2.12/1.32  ----------------------
% 2.12/1.32  #Subsume      : 2
% 2.12/1.32  #Demod        : 25
% 2.12/1.32  #Tautology    : 47
% 2.12/1.32  #SimpNegUnit  : 8
% 2.12/1.32  #BackRed      : 1
% 2.12/1.32  
% 2.12/1.32  #Partial instantiations: 0
% 2.12/1.32  #Strategies tried      : 1
% 2.12/1.32  
% 2.12/1.32  Timing (in seconds)
% 2.12/1.32  ----------------------
% 2.12/1.32  Preprocessing        : 0.32
% 2.12/1.32  Parsing              : 0.16
% 2.12/1.32  CNF conversion       : 0.02
% 2.12/1.32  Main loop            : 0.23
% 2.12/1.32  Inferencing          : 0.09
% 2.12/1.32  Reduction            : 0.07
% 2.12/1.32  Demodulation         : 0.05
% 2.12/1.32  BG Simplification    : 0.02
% 2.12/1.32  Subsumption          : 0.04
% 2.12/1.32  Abstraction          : 0.02
% 2.12/1.32  MUC search           : 0.00
% 2.12/1.32  Cooper               : 0.00
% 2.12/1.32  Total                : 0.58
% 2.12/1.32  Index Insertion      : 0.00
% 2.12/1.32  Index Deletion       : 0.00
% 2.12/1.32  Index Matching       : 0.00
% 2.12/1.32  BG Taut test         : 0.00
%------------------------------------------------------------------------------
