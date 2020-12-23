%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:53:09 EST 2020

% Result     : Theorem 6.25s
% Output     : CNFRefutation 6.25s
% Verified   : 
% Statistics : Number of formulae       :   46 (  51 expanded)
%              Number of leaves         :   24 (  27 expanded)
%              Depth                    :    9
%              Number of atoms          :   47 (  53 expanded)
%              Number of equality atoms :   42 (  48 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1

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

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_75,negated_conjecture,(
    ~ ! [A,B] :
        ( k4_xboole_0(k1_tarski(A),B) = k1_xboole_0
        | k4_xboole_0(k1_tarski(A),B) = k1_tarski(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_zfmisc_1)).

tff(f_35,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

tff(f_39,axiom,(
    ! [A,B] : k4_xboole_0(A,k2_xboole_0(A,B)) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).

tff(f_56,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
    <=> A != B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_zfmisc_1)).

tff(f_43,axiom,(
    ! [A] : k4_xboole_0(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).

tff(f_45,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_70,axiom,(
    ! [A,B,C] :
      ~ ( k1_tarski(A) = k2_xboole_0(B,C)
        & B != C
        & B != k1_xboole_0
        & C != k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_zfmisc_1)).

tff(c_38,plain,(
    k4_xboole_0(k1_tarski('#skF_1'),'#skF_2') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_10,plain,(
    ! [A_7] : k2_xboole_0(A_7,k1_xboole_0) = A_7 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_101,plain,(
    ! [A_37,B_38] : k4_xboole_0(A_37,k2_xboole_0(A_37,B_38)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_114,plain,(
    ! [A_7] : k4_xboole_0(A_7,A_7) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_101])).

tff(c_28,plain,(
    ! [B_24] : k4_xboole_0(k1_tarski(B_24),k1_tarski(B_24)) != k1_tarski(B_24) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_217,plain,(
    ! [B_24] : k1_tarski(B_24) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_114,c_28])).

tff(c_18,plain,(
    ! [A_14] : k4_xboole_0(k1_xboole_0,A_14) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_219,plain,(
    ! [A_52,B_53] : k5_xboole_0(A_52,k4_xboole_0(B_53,A_52)) = k2_xboole_0(A_52,B_53) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_240,plain,(
    ! [A_14] : k5_xboole_0(A_14,k1_xboole_0) = k2_xboole_0(A_14,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_219])).

tff(c_243,plain,(
    ! [A_14] : k5_xboole_0(A_14,k1_xboole_0) = A_14 ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_240])).

tff(c_12,plain,(
    ! [A_8,B_9] : r1_tarski(k4_xboole_0(A_8,B_9),A_8) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_153,plain,(
    ! [A_45,B_46] :
      ( k4_xboole_0(A_45,B_46) = k1_xboole_0
      | ~ r1_tarski(A_45,B_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_166,plain,(
    ! [A_8,B_9] : k4_xboole_0(k4_xboole_0(A_8,B_9),A_8) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_12,c_153])).

tff(c_231,plain,(
    ! [A_8,B_9] : k2_xboole_0(A_8,k4_xboole_0(A_8,B_9)) = k5_xboole_0(A_8,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_166,c_219])).

tff(c_1131,plain,(
    ! [A_97,B_98] : k2_xboole_0(A_97,k4_xboole_0(A_97,B_98)) = A_97 ),
    inference(demodulation,[status(thm),theory(equality)],[c_243,c_231])).

tff(c_34,plain,(
    ! [C_29,B_28,A_27] :
      ( k1_xboole_0 = C_29
      | k1_xboole_0 = B_28
      | C_29 = B_28
      | k2_xboole_0(B_28,C_29) != k1_tarski(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_1143,plain,(
    ! [A_97,B_98,A_27] :
      ( k4_xboole_0(A_97,B_98) = k1_xboole_0
      | k1_xboole_0 = A_97
      | k4_xboole_0(A_97,B_98) = A_97
      | k1_tarski(A_27) != A_97 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1131,c_34])).

tff(c_8985,plain,(
    ! [A_27,B_98] :
      ( k4_xboole_0(k1_tarski(A_27),B_98) = k1_xboole_0
      | k1_tarski(A_27) = k1_xboole_0
      | k4_xboole_0(k1_tarski(A_27),B_98) = k1_tarski(A_27) ) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_1143])).

tff(c_8992,plain,(
    ! [A_208,B_209] :
      ( k4_xboole_0(k1_tarski(A_208),B_209) = k1_xboole_0
      | k4_xboole_0(k1_tarski(A_208),B_209) = k1_tarski(A_208) ) ),
    inference(negUnitSimplification,[status(thm)],[c_217,c_8985])).

tff(c_36,plain,(
    k4_xboole_0(k1_tarski('#skF_1'),'#skF_2') != k1_tarski('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_9066,plain,(
    k4_xboole_0(k1_tarski('#skF_1'),'#skF_2') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_8992,c_36])).

tff(c_9134,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_9066])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n006.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 14:52:22 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.25/2.38  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.25/2.39  
% 6.25/2.39  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.25/2.39  %$ r1_tarski > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1
% 6.25/2.39  
% 6.25/2.39  %Foreground sorts:
% 6.25/2.39  
% 6.25/2.39  
% 6.25/2.39  %Background operators:
% 6.25/2.39  
% 6.25/2.39  
% 6.25/2.39  %Foreground operators:
% 6.25/2.39  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.25/2.39  tff(k1_tarski, type, k1_tarski: $i > $i).
% 6.25/2.39  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 6.25/2.39  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 6.25/2.39  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 6.25/2.39  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.25/2.39  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 6.25/2.39  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 6.25/2.39  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 6.25/2.39  tff('#skF_2', type, '#skF_2': $i).
% 6.25/2.39  tff('#skF_1', type, '#skF_1': $i).
% 6.25/2.39  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.25/2.39  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.25/2.39  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 6.25/2.39  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 6.25/2.39  
% 6.25/2.40  tff(f_75, negated_conjecture, ~(![A, B]: ((k4_xboole_0(k1_tarski(A), B) = k1_xboole_0) | (k4_xboole_0(k1_tarski(A), B) = k1_tarski(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_zfmisc_1)).
% 6.25/2.40  tff(f_35, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 6.25/2.40  tff(f_39, axiom, (![A, B]: (k4_xboole_0(A, k2_xboole_0(A, B)) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_xboole_1)).
% 6.25/2.40  tff(f_56, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) <=> ~(A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_zfmisc_1)).
% 6.25/2.40  tff(f_43, axiom, (![A]: (k4_xboole_0(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_boole)).
% 6.25/2.40  tff(f_45, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_xboole_1)).
% 6.25/2.40  tff(f_37, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 6.25/2.40  tff(f_31, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 6.25/2.40  tff(f_70, axiom, (![A, B, C]: ~((((k1_tarski(A) = k2_xboole_0(B, C)) & ~(B = C)) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_zfmisc_1)).
% 6.25/2.40  tff(c_38, plain, (k4_xboole_0(k1_tarski('#skF_1'), '#skF_2')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_75])).
% 6.25/2.40  tff(c_10, plain, (![A_7]: (k2_xboole_0(A_7, k1_xboole_0)=A_7)), inference(cnfTransformation, [status(thm)], [f_35])).
% 6.25/2.40  tff(c_101, plain, (![A_37, B_38]: (k4_xboole_0(A_37, k2_xboole_0(A_37, B_38))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 6.25/2.40  tff(c_114, plain, (![A_7]: (k4_xboole_0(A_7, A_7)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_10, c_101])).
% 6.25/2.40  tff(c_28, plain, (![B_24]: (k4_xboole_0(k1_tarski(B_24), k1_tarski(B_24))!=k1_tarski(B_24))), inference(cnfTransformation, [status(thm)], [f_56])).
% 6.25/2.40  tff(c_217, plain, (![B_24]: (k1_tarski(B_24)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_114, c_28])).
% 6.25/2.40  tff(c_18, plain, (![A_14]: (k4_xboole_0(k1_xboole_0, A_14)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_43])).
% 6.25/2.40  tff(c_219, plain, (![A_52, B_53]: (k5_xboole_0(A_52, k4_xboole_0(B_53, A_52))=k2_xboole_0(A_52, B_53))), inference(cnfTransformation, [status(thm)], [f_45])).
% 6.25/2.40  tff(c_240, plain, (![A_14]: (k5_xboole_0(A_14, k1_xboole_0)=k2_xboole_0(A_14, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_18, c_219])).
% 6.25/2.40  tff(c_243, plain, (![A_14]: (k5_xboole_0(A_14, k1_xboole_0)=A_14)), inference(demodulation, [status(thm), theory('equality')], [c_10, c_240])).
% 6.25/2.40  tff(c_12, plain, (![A_8, B_9]: (r1_tarski(k4_xboole_0(A_8, B_9), A_8))), inference(cnfTransformation, [status(thm)], [f_37])).
% 6.25/2.40  tff(c_153, plain, (![A_45, B_46]: (k4_xboole_0(A_45, B_46)=k1_xboole_0 | ~r1_tarski(A_45, B_46))), inference(cnfTransformation, [status(thm)], [f_31])).
% 6.25/2.40  tff(c_166, plain, (![A_8, B_9]: (k4_xboole_0(k4_xboole_0(A_8, B_9), A_8)=k1_xboole_0)), inference(resolution, [status(thm)], [c_12, c_153])).
% 6.25/2.40  tff(c_231, plain, (![A_8, B_9]: (k2_xboole_0(A_8, k4_xboole_0(A_8, B_9))=k5_xboole_0(A_8, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_166, c_219])).
% 6.25/2.40  tff(c_1131, plain, (![A_97, B_98]: (k2_xboole_0(A_97, k4_xboole_0(A_97, B_98))=A_97)), inference(demodulation, [status(thm), theory('equality')], [c_243, c_231])).
% 6.25/2.40  tff(c_34, plain, (![C_29, B_28, A_27]: (k1_xboole_0=C_29 | k1_xboole_0=B_28 | C_29=B_28 | k2_xboole_0(B_28, C_29)!=k1_tarski(A_27))), inference(cnfTransformation, [status(thm)], [f_70])).
% 6.25/2.40  tff(c_1143, plain, (![A_97, B_98, A_27]: (k4_xboole_0(A_97, B_98)=k1_xboole_0 | k1_xboole_0=A_97 | k4_xboole_0(A_97, B_98)=A_97 | k1_tarski(A_27)!=A_97)), inference(superposition, [status(thm), theory('equality')], [c_1131, c_34])).
% 6.25/2.40  tff(c_8985, plain, (![A_27, B_98]: (k4_xboole_0(k1_tarski(A_27), B_98)=k1_xboole_0 | k1_tarski(A_27)=k1_xboole_0 | k4_xboole_0(k1_tarski(A_27), B_98)=k1_tarski(A_27))), inference(reflexivity, [status(thm), theory('equality')], [c_1143])).
% 6.25/2.40  tff(c_8992, plain, (![A_208, B_209]: (k4_xboole_0(k1_tarski(A_208), B_209)=k1_xboole_0 | k4_xboole_0(k1_tarski(A_208), B_209)=k1_tarski(A_208))), inference(negUnitSimplification, [status(thm)], [c_217, c_8985])).
% 6.25/2.40  tff(c_36, plain, (k4_xboole_0(k1_tarski('#skF_1'), '#skF_2')!=k1_tarski('#skF_1')), inference(cnfTransformation, [status(thm)], [f_75])).
% 6.25/2.40  tff(c_9066, plain, (k4_xboole_0(k1_tarski('#skF_1'), '#skF_2')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_8992, c_36])).
% 6.25/2.40  tff(c_9134, plain, $false, inference(negUnitSimplification, [status(thm)], [c_38, c_9066])).
% 6.25/2.40  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.25/2.40  
% 6.25/2.40  Inference rules
% 6.25/2.40  ----------------------
% 6.25/2.40  #Ref     : 1
% 6.25/2.40  #Sup     : 2224
% 6.25/2.40  #Fact    : 1
% 6.25/2.40  #Define  : 0
% 6.25/2.40  #Split   : 0
% 6.25/2.40  #Chain   : 0
% 6.25/2.40  #Close   : 0
% 6.25/2.40  
% 6.25/2.40  Ordering : KBO
% 6.25/2.40  
% 6.25/2.40  Simplification rules
% 6.25/2.40  ----------------------
% 6.25/2.40  #Subsume      : 198
% 6.25/2.40  #Demod        : 3953
% 6.25/2.40  #Tautology    : 1856
% 6.25/2.40  #SimpNegUnit  : 14
% 6.25/2.40  #BackRed      : 1
% 6.25/2.40  
% 6.25/2.40  #Partial instantiations: 0
% 6.25/2.40  #Strategies tried      : 1
% 6.25/2.40  
% 6.25/2.40  Timing (in seconds)
% 6.25/2.40  ----------------------
% 6.25/2.40  Preprocessing        : 0.31
% 6.25/2.40  Parsing              : 0.17
% 6.25/2.40  CNF conversion       : 0.02
% 6.25/2.40  Main loop            : 1.29
% 6.25/2.40  Inferencing          : 0.33
% 6.25/2.40  Reduction            : 0.73
% 6.25/2.40  Demodulation         : 0.63
% 6.25/2.40  BG Simplification    : 0.03
% 6.25/2.40  Subsumption          : 0.15
% 6.25/2.40  Abstraction          : 0.07
% 6.25/2.40  MUC search           : 0.00
% 6.25/2.40  Cooper               : 0.00
% 6.25/2.40  Total                : 1.63
% 6.25/2.40  Index Insertion      : 0.00
% 6.25/2.40  Index Deletion       : 0.00
% 6.25/2.41  Index Matching       : 0.00
% 6.25/2.41  BG Taut test         : 0.00
%------------------------------------------------------------------------------
