%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:57:26 EST 2020

% Result     : Theorem 2.18s
% Output     : CNFRefutation 2.18s
% Verified   : 
% Statistics : Number of formulae       :   55 ( 144 expanded)
%              Number of leaves         :   25 (  59 expanded)
%              Depth                    :   16
%              Number of atoms          :   57 ( 179 expanded)
%              Number of equality atoms :   49 ( 146 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_1

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

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

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

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_31,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_37,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_52,axiom,(
    ! [A,B] :
      ~ ( r1_xboole_0(k1_tarski(A),k1_tarski(B))
        & A = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_zfmisc_1)).

tff(f_64,axiom,(
    ! [A] : k1_setfam_1(k1_tarski(A)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_setfam_1)).

tff(f_39,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_xboole_0(k1_tarski(A),k1_tarski(B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_enumset1)).

tff(f_62,axiom,(
    ! [A,B] :
      ~ ( A != k1_xboole_0
        & B != k1_xboole_0
        & k1_setfam_1(k2_xboole_0(A,B)) != k3_xboole_0(k1_setfam_1(A),k1_setfam_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_setfam_1)).

tff(f_67,negated_conjecture,(
    ~ ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

tff(c_6,plain,(
    ! [A_3] : k3_xboole_0(A_3,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_88,plain,(
    ! [A_35,B_36] :
      ( r1_xboole_0(A_35,B_36)
      | k3_xboole_0(A_35,B_36) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_10,plain,(
    ! [A_6,B_7] :
      ( k4_xboole_0(A_6,B_7) = A_6
      | ~ r1_xboole_0(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_95,plain,(
    ! [A_35,B_36] :
      ( k4_xboole_0(A_35,B_36) = A_35
      | k3_xboole_0(A_35,B_36) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_88,c_10])).

tff(c_125,plain,(
    ! [A_42,B_43] : k4_xboole_0(A_42,k4_xboole_0(A_42,B_43)) = k3_xboole_0(A_42,B_43) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_8,plain,(
    ! [A_4,B_5] : k4_xboole_0(A_4,k4_xboole_0(A_4,B_5)) = k3_xboole_0(A_4,B_5) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_209,plain,(
    ! [A_54,B_55] : k4_xboole_0(A_54,k3_xboole_0(A_54,B_55)) = k3_xboole_0(A_54,k4_xboole_0(A_54,B_55)) ),
    inference(superposition,[status(thm),theory(equality)],[c_125,c_8])).

tff(c_234,plain,(
    ! [A_56] : k3_xboole_0(A_56,k4_xboole_0(A_56,k1_xboole_0)) = k4_xboole_0(A_56,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_209])).

tff(c_247,plain,(
    ! [A_35] :
      ( k4_xboole_0(A_35,k1_xboole_0) = k3_xboole_0(A_35,A_35)
      | k3_xboole_0(A_35,k1_xboole_0) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_95,c_234])).

tff(c_254,plain,(
    ! [A_57] : k4_xboole_0(A_57,k1_xboole_0) = k3_xboole_0(A_57,A_57) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_247])).

tff(c_272,plain,(
    ! [A_57] :
      ( k3_xboole_0(A_57,A_57) = A_57
      | k3_xboole_0(A_57,k1_xboole_0) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_254,c_95])).

tff(c_291,plain,(
    ! [A_57] : k3_xboole_0(A_57,A_57) = A_57 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_272])).

tff(c_252,plain,(
    ! [A_35] : k4_xboole_0(A_35,k1_xboole_0) = k3_xboole_0(A_35,A_35) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_247])).

tff(c_349,plain,(
    ! [A_61] : k4_xboole_0(A_61,k1_xboole_0) = A_61 ),
    inference(demodulation,[status(thm),theory(equality)],[c_291,c_252])).

tff(c_361,plain,(
    ! [A_61] : k4_xboole_0(A_61,A_61) = k3_xboole_0(A_61,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_349,c_8])).

tff(c_375,plain,(
    ! [A_61] : k4_xboole_0(A_61,A_61) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_361])).

tff(c_67,plain,(
    ! [A_31,B_32] :
      ( r1_xboole_0(A_31,B_32)
      | k4_xboole_0(A_31,B_32) != A_31 ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_24,plain,(
    ! [B_19] : ~ r1_xboole_0(k1_tarski(B_19),k1_tarski(B_19)) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_75,plain,(
    ! [B_19] : k4_xboole_0(k1_tarski(B_19),k1_tarski(B_19)) != k1_tarski(B_19) ),
    inference(resolution,[status(thm)],[c_67,c_24])).

tff(c_380,plain,(
    ! [B_19] : k1_tarski(B_19) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_375,c_75])).

tff(c_28,plain,(
    ! [A_22] : k1_setfam_1(k1_tarski(A_22)) = A_22 ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_14,plain,(
    ! [A_8,B_9] : k2_xboole_0(k1_tarski(A_8),k1_tarski(B_9)) = k2_tarski(A_8,B_9) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_320,plain,(
    ! [A_59,B_60] :
      ( k3_xboole_0(k1_setfam_1(A_59),k1_setfam_1(B_60)) = k1_setfam_1(k2_xboole_0(A_59,B_60))
      | k1_xboole_0 = B_60
      | k1_xboole_0 = A_59 ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_340,plain,(
    ! [A_22,B_60] :
      ( k1_setfam_1(k2_xboole_0(k1_tarski(A_22),B_60)) = k3_xboole_0(A_22,k1_setfam_1(B_60))
      | k1_xboole_0 = B_60
      | k1_tarski(A_22) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_320])).

tff(c_422,plain,(
    ! [A_64,B_65] :
      ( k1_setfam_1(k2_xboole_0(k1_tarski(A_64),B_65)) = k3_xboole_0(A_64,k1_setfam_1(B_65))
      | k1_xboole_0 = B_65 ) ),
    inference(negUnitSimplification,[status(thm)],[c_380,c_340])).

tff(c_437,plain,(
    ! [A_8,B_9] :
      ( k3_xboole_0(A_8,k1_setfam_1(k1_tarski(B_9))) = k1_setfam_1(k2_tarski(A_8,B_9))
      | k1_tarski(B_9) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_422])).

tff(c_444,plain,(
    ! [A_8,B_9] :
      ( k1_setfam_1(k2_tarski(A_8,B_9)) = k3_xboole_0(A_8,B_9)
      | k1_tarski(B_9) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_437])).

tff(c_445,plain,(
    ! [A_8,B_9] : k1_setfam_1(k2_tarski(A_8,B_9)) = k3_xboole_0(A_8,B_9) ),
    inference(negUnitSimplification,[status(thm)],[c_380,c_444])).

tff(c_30,plain,(
    k1_setfam_1(k2_tarski('#skF_1','#skF_2')) != k3_xboole_0('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_450,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_445,c_30])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:41:45 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.18/1.27  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.18/1.28  
% 2.18/1.28  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.18/1.28  %$ r1_xboole_0 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_1
% 2.18/1.28  
% 2.18/1.28  %Foreground sorts:
% 2.18/1.28  
% 2.18/1.28  
% 2.18/1.28  %Background operators:
% 2.18/1.28  
% 2.18/1.28  
% 2.18/1.28  %Foreground operators:
% 2.18/1.28  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.18/1.28  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.18/1.28  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.18/1.28  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.18/1.28  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.18/1.28  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.18/1.28  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.18/1.28  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.18/1.28  tff('#skF_2', type, '#skF_2': $i).
% 2.18/1.28  tff('#skF_1', type, '#skF_1': $i).
% 2.18/1.28  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.18/1.28  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.18/1.28  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.18/1.28  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.18/1.28  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.18/1.28  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.18/1.28  
% 2.18/1.29  tff(f_31, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 2.18/1.29  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 2.18/1.29  tff(f_37, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_xboole_1)).
% 2.18/1.29  tff(f_33, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 2.18/1.29  tff(f_52, axiom, (![A, B]: ~(r1_xboole_0(k1_tarski(A), k1_tarski(B)) & (A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t16_zfmisc_1)).
% 2.18/1.29  tff(f_64, axiom, (![A]: (k1_setfam_1(k1_tarski(A)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_setfam_1)).
% 2.18/1.29  tff(f_39, axiom, (![A, B]: (k2_tarski(A, B) = k2_xboole_0(k1_tarski(A), k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_enumset1)).
% 2.18/1.29  tff(f_62, axiom, (![A, B]: ~((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(k1_setfam_1(k2_xboole_0(A, B)) = k3_xboole_0(k1_setfam_1(A), k1_setfam_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_setfam_1)).
% 2.18/1.29  tff(f_67, negated_conjecture, ~(![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 2.18/1.29  tff(c_6, plain, (![A_3]: (k3_xboole_0(A_3, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.18/1.29  tff(c_88, plain, (![A_35, B_36]: (r1_xboole_0(A_35, B_36) | k3_xboole_0(A_35, B_36)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.18/1.29  tff(c_10, plain, (![A_6, B_7]: (k4_xboole_0(A_6, B_7)=A_6 | ~r1_xboole_0(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.18/1.29  tff(c_95, plain, (![A_35, B_36]: (k4_xboole_0(A_35, B_36)=A_35 | k3_xboole_0(A_35, B_36)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_88, c_10])).
% 2.18/1.29  tff(c_125, plain, (![A_42, B_43]: (k4_xboole_0(A_42, k4_xboole_0(A_42, B_43))=k3_xboole_0(A_42, B_43))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.18/1.29  tff(c_8, plain, (![A_4, B_5]: (k4_xboole_0(A_4, k4_xboole_0(A_4, B_5))=k3_xboole_0(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.18/1.29  tff(c_209, plain, (![A_54, B_55]: (k4_xboole_0(A_54, k3_xboole_0(A_54, B_55))=k3_xboole_0(A_54, k4_xboole_0(A_54, B_55)))), inference(superposition, [status(thm), theory('equality')], [c_125, c_8])).
% 2.18/1.29  tff(c_234, plain, (![A_56]: (k3_xboole_0(A_56, k4_xboole_0(A_56, k1_xboole_0))=k4_xboole_0(A_56, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_6, c_209])).
% 2.18/1.29  tff(c_247, plain, (![A_35]: (k4_xboole_0(A_35, k1_xboole_0)=k3_xboole_0(A_35, A_35) | k3_xboole_0(A_35, k1_xboole_0)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_95, c_234])).
% 2.18/1.29  tff(c_254, plain, (![A_57]: (k4_xboole_0(A_57, k1_xboole_0)=k3_xboole_0(A_57, A_57))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_247])).
% 2.18/1.29  tff(c_272, plain, (![A_57]: (k3_xboole_0(A_57, A_57)=A_57 | k3_xboole_0(A_57, k1_xboole_0)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_254, c_95])).
% 2.18/1.29  tff(c_291, plain, (![A_57]: (k3_xboole_0(A_57, A_57)=A_57)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_272])).
% 2.18/1.29  tff(c_252, plain, (![A_35]: (k4_xboole_0(A_35, k1_xboole_0)=k3_xboole_0(A_35, A_35))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_247])).
% 2.18/1.29  tff(c_349, plain, (![A_61]: (k4_xboole_0(A_61, k1_xboole_0)=A_61)), inference(demodulation, [status(thm), theory('equality')], [c_291, c_252])).
% 2.18/1.29  tff(c_361, plain, (![A_61]: (k4_xboole_0(A_61, A_61)=k3_xboole_0(A_61, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_349, c_8])).
% 2.18/1.29  tff(c_375, plain, (![A_61]: (k4_xboole_0(A_61, A_61)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_361])).
% 2.18/1.29  tff(c_67, plain, (![A_31, B_32]: (r1_xboole_0(A_31, B_32) | k4_xboole_0(A_31, B_32)!=A_31)), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.18/1.29  tff(c_24, plain, (![B_19]: (~r1_xboole_0(k1_tarski(B_19), k1_tarski(B_19)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.18/1.29  tff(c_75, plain, (![B_19]: (k4_xboole_0(k1_tarski(B_19), k1_tarski(B_19))!=k1_tarski(B_19))), inference(resolution, [status(thm)], [c_67, c_24])).
% 2.18/1.29  tff(c_380, plain, (![B_19]: (k1_tarski(B_19)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_375, c_75])).
% 2.18/1.29  tff(c_28, plain, (![A_22]: (k1_setfam_1(k1_tarski(A_22))=A_22)), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.18/1.29  tff(c_14, plain, (![A_8, B_9]: (k2_xboole_0(k1_tarski(A_8), k1_tarski(B_9))=k2_tarski(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.18/1.29  tff(c_320, plain, (![A_59, B_60]: (k3_xboole_0(k1_setfam_1(A_59), k1_setfam_1(B_60))=k1_setfam_1(k2_xboole_0(A_59, B_60)) | k1_xboole_0=B_60 | k1_xboole_0=A_59)), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.18/1.29  tff(c_340, plain, (![A_22, B_60]: (k1_setfam_1(k2_xboole_0(k1_tarski(A_22), B_60))=k3_xboole_0(A_22, k1_setfam_1(B_60)) | k1_xboole_0=B_60 | k1_tarski(A_22)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_28, c_320])).
% 2.18/1.29  tff(c_422, plain, (![A_64, B_65]: (k1_setfam_1(k2_xboole_0(k1_tarski(A_64), B_65))=k3_xboole_0(A_64, k1_setfam_1(B_65)) | k1_xboole_0=B_65)), inference(negUnitSimplification, [status(thm)], [c_380, c_340])).
% 2.18/1.29  tff(c_437, plain, (![A_8, B_9]: (k3_xboole_0(A_8, k1_setfam_1(k1_tarski(B_9)))=k1_setfam_1(k2_tarski(A_8, B_9)) | k1_tarski(B_9)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_14, c_422])).
% 2.18/1.29  tff(c_444, plain, (![A_8, B_9]: (k1_setfam_1(k2_tarski(A_8, B_9))=k3_xboole_0(A_8, B_9) | k1_tarski(B_9)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_28, c_437])).
% 2.18/1.29  tff(c_445, plain, (![A_8, B_9]: (k1_setfam_1(k2_tarski(A_8, B_9))=k3_xboole_0(A_8, B_9))), inference(negUnitSimplification, [status(thm)], [c_380, c_444])).
% 2.18/1.29  tff(c_30, plain, (k1_setfam_1(k2_tarski('#skF_1', '#skF_2'))!=k3_xboole_0('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.18/1.29  tff(c_450, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_445, c_30])).
% 2.18/1.29  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.18/1.29  
% 2.18/1.29  Inference rules
% 2.18/1.29  ----------------------
% 2.18/1.29  #Ref     : 0
% 2.18/1.29  #Sup     : 94
% 2.18/1.29  #Fact    : 0
% 2.18/1.29  #Define  : 0
% 2.18/1.29  #Split   : 0
% 2.18/1.29  #Chain   : 0
% 2.18/1.29  #Close   : 0
% 2.18/1.29  
% 2.18/1.29  Ordering : KBO
% 2.18/1.29  
% 2.18/1.29  Simplification rules
% 2.18/1.29  ----------------------
% 2.18/1.29  #Subsume      : 2
% 2.18/1.29  #Demod        : 46
% 2.18/1.29  #Tautology    : 66
% 2.18/1.29  #SimpNegUnit  : 3
% 2.18/1.29  #BackRed      : 5
% 2.18/1.29  
% 2.18/1.29  #Partial instantiations: 0
% 2.18/1.29  #Strategies tried      : 1
% 2.18/1.29  
% 2.18/1.29  Timing (in seconds)
% 2.18/1.29  ----------------------
% 2.18/1.29  Preprocessing        : 0.30
% 2.18/1.29  Parsing              : 0.16
% 2.18/1.29  CNF conversion       : 0.02
% 2.18/1.29  Main loop            : 0.21
% 2.18/1.29  Inferencing          : 0.08
% 2.18/1.29  Reduction            : 0.07
% 2.18/1.29  Demodulation         : 0.05
% 2.18/1.29  BG Simplification    : 0.01
% 2.18/1.29  Subsumption          : 0.03
% 2.18/1.29  Abstraction          : 0.02
% 2.18/1.29  MUC search           : 0.00
% 2.18/1.29  Cooper               : 0.00
% 2.18/1.29  Total                : 0.54
% 2.18/1.29  Index Insertion      : 0.00
% 2.18/1.29  Index Deletion       : 0.00
% 2.18/1.29  Index Matching       : 0.00
% 2.18/1.29  BG Taut test         : 0.00
%------------------------------------------------------------------------------
