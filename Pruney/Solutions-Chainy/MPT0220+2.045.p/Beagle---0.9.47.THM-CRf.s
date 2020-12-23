%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:48:09 EST 2020

% Result     : Theorem 10.45s
% Output     : CNFRefutation 10.45s
% Verified   : 
% Statistics : Number of formulae       :   59 (  96 expanded)
%              Number of leaves         :   28 (  45 expanded)
%              Depth                    :   13
%              Number of atoms          :   42 (  79 expanded)
%              Number of equality atoms :   37 (  74 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1

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

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(f_35,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

tff(f_39,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_37,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_57,axiom,(
    ! [A,B] : r1_tarski(k1_tarski(A),k2_tarski(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_zfmisc_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_41,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_60,negated_conjecture,(
    ~ ! [A,B] : k2_xboole_0(k1_tarski(A),k2_tarski(A,B)) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_zfmisc_1)).

tff(c_8,plain,(
    ! [A_7] : k5_xboole_0(A_7,k1_xboole_0) = A_7 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_12,plain,(
    ! [A_11] : k5_xboole_0(A_11,A_11) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_257,plain,(
    ! [A_72,B_73,C_74] : k5_xboole_0(k5_xboole_0(A_72,B_73),C_74) = k5_xboole_0(A_72,k5_xboole_0(B_73,C_74)) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_447,plain,(
    ! [A_78,C_79] : k5_xboole_0(A_78,k5_xboole_0(A_78,C_79)) = k5_xboole_0(k1_xboole_0,C_79) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_257])).

tff(c_521,plain,(
    ! [A_11] : k5_xboole_0(k1_xboole_0,A_11) = k5_xboole_0(A_11,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_447])).

tff(c_537,plain,(
    ! [A_11] : k5_xboole_0(k1_xboole_0,A_11) = A_11 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_521])).

tff(c_30,plain,(
    ! [A_42,B_43] : r1_tarski(k1_tarski(A_42),k2_tarski(A_42,B_43)) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_115,plain,(
    ! [A_54,B_55] :
      ( k3_xboole_0(A_54,B_55) = A_54
      | ~ r1_tarski(A_54,B_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_221,plain,(
    ! [A_68,B_69] : k3_xboole_0(k1_tarski(A_68),k2_tarski(A_68,B_69)) = k1_tarski(A_68) ),
    inference(resolution,[status(thm)],[c_30,c_115])).

tff(c_4,plain,(
    ! [A_3,B_4] : k5_xboole_0(A_3,k3_xboole_0(A_3,B_4)) = k4_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_230,plain,(
    ! [A_68,B_69] : k5_xboole_0(k1_tarski(A_68),k1_tarski(A_68)) = k4_xboole_0(k1_tarski(A_68),k2_tarski(A_68,B_69)) ),
    inference(superposition,[status(thm),theory(equality)],[c_221,c_4])).

tff(c_238,plain,(
    ! [A_68,B_69] : k4_xboole_0(k1_tarski(A_68),k2_tarski(A_68,B_69)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_230])).

tff(c_14,plain,(
    ! [A_12,B_13] : k5_xboole_0(A_12,k4_xboole_0(B_13,A_12)) = k2_xboole_0(A_12,B_13) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_1886,plain,(
    ! [A_133,B_134,C_135] : k5_xboole_0(A_133,k5_xboole_0(k3_xboole_0(A_133,B_134),C_135)) = k5_xboole_0(k4_xboole_0(A_133,B_134),C_135) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_257])).

tff(c_2017,plain,(
    ! [A_133,B_134] : k5_xboole_0(k4_xboole_0(A_133,B_134),k3_xboole_0(A_133,B_134)) = k5_xboole_0(A_133,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_1886])).

tff(c_2139,plain,(
    ! [A_139,B_140] : k5_xboole_0(k4_xboole_0(A_139,B_140),k3_xboole_0(A_139,B_140)) = A_139 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_2017])).

tff(c_2303,plain,(
    ! [A_143,B_144] : k5_xboole_0(k4_xboole_0(A_143,B_144),k3_xboole_0(B_144,A_143)) = A_143 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_2139])).

tff(c_283,plain,(
    ! [A_72,B_73] : k5_xboole_0(A_72,k5_xboole_0(B_73,k5_xboole_0(A_72,B_73))) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_257,c_12])).

tff(c_320,plain,(
    ! [A_11,C_74] : k5_xboole_0(A_11,k5_xboole_0(A_11,C_74)) = k5_xboole_0(k1_xboole_0,C_74) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_257])).

tff(c_617,plain,(
    ! [A_81,C_82] : k5_xboole_0(A_81,k5_xboole_0(A_81,C_82)) = C_82 ),
    inference(demodulation,[status(thm),theory(equality)],[c_537,c_320])).

tff(c_661,plain,(
    ! [B_73,A_72] : k5_xboole_0(B_73,k5_xboole_0(A_72,B_73)) = k5_xboole_0(A_72,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_283,c_617])).

tff(c_700,plain,(
    ! [B_73,A_72] : k5_xboole_0(B_73,k5_xboole_0(A_72,B_73)) = A_72 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_661])).

tff(c_3502,plain,(
    ! [B_163,A_164] : k5_xboole_0(k3_xboole_0(B_163,A_164),A_164) = k4_xboole_0(A_164,B_163) ),
    inference(superposition,[status(thm),theory(equality)],[c_2303,c_700])).

tff(c_299,plain,(
    ! [A_3,B_4,C_74] : k5_xboole_0(A_3,k5_xboole_0(k3_xboole_0(A_3,B_4),C_74)) = k5_xboole_0(k4_xboole_0(A_3,B_4),C_74) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_257])).

tff(c_3519,plain,(
    ! [B_163,A_164] : k5_xboole_0(k4_xboole_0(B_163,A_164),A_164) = k5_xboole_0(B_163,k4_xboole_0(A_164,B_163)) ),
    inference(superposition,[status(thm),theory(equality)],[c_3502,c_299])).

tff(c_7125,plain,(
    ! [B_203,A_204] : k5_xboole_0(k4_xboole_0(B_203,A_204),A_204) = k2_xboole_0(B_203,A_204) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_3519])).

tff(c_7220,plain,(
    ! [A_68,B_69] : k2_xboole_0(k1_tarski(A_68),k2_tarski(A_68,B_69)) = k5_xboole_0(k1_xboole_0,k2_tarski(A_68,B_69)) ),
    inference(superposition,[status(thm),theory(equality)],[c_238,c_7125])).

tff(c_7246,plain,(
    ! [A_68,B_69] : k2_xboole_0(k1_tarski(A_68),k2_tarski(A_68,B_69)) = k2_tarski(A_68,B_69) ),
    inference(demodulation,[status(thm),theory(equality)],[c_537,c_7220])).

tff(c_32,plain,(
    k2_xboole_0(k1_tarski('#skF_1'),k2_tarski('#skF_1','#skF_2')) != k2_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_20864,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_7246,c_32])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:13:45 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 10.45/4.47  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.45/4.48  
% 10.45/4.48  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.45/4.48  %$ r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1
% 10.45/4.48  
% 10.45/4.48  %Foreground sorts:
% 10.45/4.48  
% 10.45/4.48  
% 10.45/4.48  %Background operators:
% 10.45/4.48  
% 10.45/4.48  
% 10.45/4.48  %Foreground operators:
% 10.45/4.48  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 10.45/4.48  tff(k1_tarski, type, k1_tarski: $i > $i).
% 10.45/4.48  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 10.45/4.48  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 10.45/4.48  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 10.45/4.48  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 10.45/4.48  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 10.45/4.48  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 10.45/4.48  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 10.45/4.48  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 10.45/4.48  tff('#skF_2', type, '#skF_2': $i).
% 10.45/4.48  tff('#skF_1', type, '#skF_1': $i).
% 10.45/4.48  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 10.45/4.48  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 10.45/4.48  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 10.45/4.48  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 10.45/4.48  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 10.45/4.48  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 10.45/4.48  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 10.45/4.48  
% 10.45/4.49  tff(f_35, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 10.45/4.49  tff(f_39, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t92_xboole_1)).
% 10.45/4.49  tff(f_37, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_xboole_1)).
% 10.45/4.49  tff(f_57, axiom, (![A, B]: r1_tarski(k1_tarski(A), k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_zfmisc_1)).
% 10.45/4.49  tff(f_33, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 10.45/4.49  tff(f_29, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 10.45/4.49  tff(f_41, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_xboole_1)).
% 10.45/4.49  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 10.45/4.49  tff(f_60, negated_conjecture, ~(![A, B]: (k2_xboole_0(k1_tarski(A), k2_tarski(A, B)) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t14_zfmisc_1)).
% 10.45/4.49  tff(c_8, plain, (![A_7]: (k5_xboole_0(A_7, k1_xboole_0)=A_7)), inference(cnfTransformation, [status(thm)], [f_35])).
% 10.45/4.49  tff(c_12, plain, (![A_11]: (k5_xboole_0(A_11, A_11)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 10.45/4.49  tff(c_257, plain, (![A_72, B_73, C_74]: (k5_xboole_0(k5_xboole_0(A_72, B_73), C_74)=k5_xboole_0(A_72, k5_xboole_0(B_73, C_74)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 10.45/4.49  tff(c_447, plain, (![A_78, C_79]: (k5_xboole_0(A_78, k5_xboole_0(A_78, C_79))=k5_xboole_0(k1_xboole_0, C_79))), inference(superposition, [status(thm), theory('equality')], [c_12, c_257])).
% 10.45/4.49  tff(c_521, plain, (![A_11]: (k5_xboole_0(k1_xboole_0, A_11)=k5_xboole_0(A_11, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_12, c_447])).
% 10.45/4.49  tff(c_537, plain, (![A_11]: (k5_xboole_0(k1_xboole_0, A_11)=A_11)), inference(demodulation, [status(thm), theory('equality')], [c_8, c_521])).
% 10.45/4.49  tff(c_30, plain, (![A_42, B_43]: (r1_tarski(k1_tarski(A_42), k2_tarski(A_42, B_43)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 10.45/4.49  tff(c_115, plain, (![A_54, B_55]: (k3_xboole_0(A_54, B_55)=A_54 | ~r1_tarski(A_54, B_55))), inference(cnfTransformation, [status(thm)], [f_33])).
% 10.45/4.49  tff(c_221, plain, (![A_68, B_69]: (k3_xboole_0(k1_tarski(A_68), k2_tarski(A_68, B_69))=k1_tarski(A_68))), inference(resolution, [status(thm)], [c_30, c_115])).
% 10.45/4.49  tff(c_4, plain, (![A_3, B_4]: (k5_xboole_0(A_3, k3_xboole_0(A_3, B_4))=k4_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 10.45/4.49  tff(c_230, plain, (![A_68, B_69]: (k5_xboole_0(k1_tarski(A_68), k1_tarski(A_68))=k4_xboole_0(k1_tarski(A_68), k2_tarski(A_68, B_69)))), inference(superposition, [status(thm), theory('equality')], [c_221, c_4])).
% 10.45/4.49  tff(c_238, plain, (![A_68, B_69]: (k4_xboole_0(k1_tarski(A_68), k2_tarski(A_68, B_69))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_12, c_230])).
% 10.45/4.49  tff(c_14, plain, (![A_12, B_13]: (k5_xboole_0(A_12, k4_xboole_0(B_13, A_12))=k2_xboole_0(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_41])).
% 10.45/4.49  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 10.45/4.49  tff(c_1886, plain, (![A_133, B_134, C_135]: (k5_xboole_0(A_133, k5_xboole_0(k3_xboole_0(A_133, B_134), C_135))=k5_xboole_0(k4_xboole_0(A_133, B_134), C_135))), inference(superposition, [status(thm), theory('equality')], [c_4, c_257])).
% 10.45/4.49  tff(c_2017, plain, (![A_133, B_134]: (k5_xboole_0(k4_xboole_0(A_133, B_134), k3_xboole_0(A_133, B_134))=k5_xboole_0(A_133, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_12, c_1886])).
% 10.45/4.49  tff(c_2139, plain, (![A_139, B_140]: (k5_xboole_0(k4_xboole_0(A_139, B_140), k3_xboole_0(A_139, B_140))=A_139)), inference(demodulation, [status(thm), theory('equality')], [c_8, c_2017])).
% 10.45/4.49  tff(c_2303, plain, (![A_143, B_144]: (k5_xboole_0(k4_xboole_0(A_143, B_144), k3_xboole_0(B_144, A_143))=A_143)), inference(superposition, [status(thm), theory('equality')], [c_2, c_2139])).
% 10.45/4.49  tff(c_283, plain, (![A_72, B_73]: (k5_xboole_0(A_72, k5_xboole_0(B_73, k5_xboole_0(A_72, B_73)))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_257, c_12])).
% 10.45/4.49  tff(c_320, plain, (![A_11, C_74]: (k5_xboole_0(A_11, k5_xboole_0(A_11, C_74))=k5_xboole_0(k1_xboole_0, C_74))), inference(superposition, [status(thm), theory('equality')], [c_12, c_257])).
% 10.45/4.49  tff(c_617, plain, (![A_81, C_82]: (k5_xboole_0(A_81, k5_xboole_0(A_81, C_82))=C_82)), inference(demodulation, [status(thm), theory('equality')], [c_537, c_320])).
% 10.45/4.49  tff(c_661, plain, (![B_73, A_72]: (k5_xboole_0(B_73, k5_xboole_0(A_72, B_73))=k5_xboole_0(A_72, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_283, c_617])).
% 10.45/4.49  tff(c_700, plain, (![B_73, A_72]: (k5_xboole_0(B_73, k5_xboole_0(A_72, B_73))=A_72)), inference(demodulation, [status(thm), theory('equality')], [c_8, c_661])).
% 10.45/4.49  tff(c_3502, plain, (![B_163, A_164]: (k5_xboole_0(k3_xboole_0(B_163, A_164), A_164)=k4_xboole_0(A_164, B_163))), inference(superposition, [status(thm), theory('equality')], [c_2303, c_700])).
% 10.45/4.49  tff(c_299, plain, (![A_3, B_4, C_74]: (k5_xboole_0(A_3, k5_xboole_0(k3_xboole_0(A_3, B_4), C_74))=k5_xboole_0(k4_xboole_0(A_3, B_4), C_74))), inference(superposition, [status(thm), theory('equality')], [c_4, c_257])).
% 10.45/4.49  tff(c_3519, plain, (![B_163, A_164]: (k5_xboole_0(k4_xboole_0(B_163, A_164), A_164)=k5_xboole_0(B_163, k4_xboole_0(A_164, B_163)))), inference(superposition, [status(thm), theory('equality')], [c_3502, c_299])).
% 10.45/4.49  tff(c_7125, plain, (![B_203, A_204]: (k5_xboole_0(k4_xboole_0(B_203, A_204), A_204)=k2_xboole_0(B_203, A_204))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_3519])).
% 10.45/4.49  tff(c_7220, plain, (![A_68, B_69]: (k2_xboole_0(k1_tarski(A_68), k2_tarski(A_68, B_69))=k5_xboole_0(k1_xboole_0, k2_tarski(A_68, B_69)))), inference(superposition, [status(thm), theory('equality')], [c_238, c_7125])).
% 10.45/4.49  tff(c_7246, plain, (![A_68, B_69]: (k2_xboole_0(k1_tarski(A_68), k2_tarski(A_68, B_69))=k2_tarski(A_68, B_69))), inference(demodulation, [status(thm), theory('equality')], [c_537, c_7220])).
% 10.45/4.49  tff(c_32, plain, (k2_xboole_0(k1_tarski('#skF_1'), k2_tarski('#skF_1', '#skF_2'))!=k2_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_60])).
% 10.45/4.49  tff(c_20864, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_7246, c_32])).
% 10.45/4.49  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.45/4.49  
% 10.45/4.49  Inference rules
% 10.45/4.49  ----------------------
% 10.45/4.49  #Ref     : 0
% 10.45/4.49  #Sup     : 5229
% 10.45/4.49  #Fact    : 0
% 10.45/4.49  #Define  : 0
% 10.45/4.49  #Split   : 0
% 10.45/4.49  #Chain   : 0
% 10.45/4.49  #Close   : 0
% 10.45/4.49  
% 10.45/4.49  Ordering : KBO
% 10.45/4.49  
% 10.45/4.49  Simplification rules
% 10.45/4.49  ----------------------
% 10.45/4.49  #Subsume      : 230
% 10.45/4.49  #Demod        : 6345
% 10.45/4.49  #Tautology    : 2552
% 10.45/4.49  #SimpNegUnit  : 0
% 10.45/4.49  #BackRed      : 7
% 10.45/4.49  
% 10.45/4.49  #Partial instantiations: 0
% 10.45/4.49  #Strategies tried      : 1
% 10.45/4.49  
% 10.45/4.49  Timing (in seconds)
% 10.45/4.49  ----------------------
% 10.55/4.50  Preprocessing        : 0.30
% 10.55/4.50  Parsing              : 0.16
% 10.55/4.50  CNF conversion       : 0.02
% 10.55/4.50  Main loop            : 3.43
% 10.55/4.50  Inferencing          : 0.64
% 10.55/4.50  Reduction            : 2.18
% 10.55/4.50  Demodulation         : 2.02
% 10.55/4.50  BG Simplification    : 0.09
% 10.55/4.50  Subsumption          : 0.39
% 10.55/4.50  Abstraction          : 0.14
% 10.55/4.50  MUC search           : 0.00
% 10.55/4.50  Cooper               : 0.00
% 10.55/4.50  Total                : 3.76
% 10.55/4.50  Index Insertion      : 0.00
% 10.55/4.50  Index Deletion       : 0.00
% 10.55/4.50  Index Matching       : 0.00
% 10.55/4.50  BG Taut test         : 0.00
%------------------------------------------------------------------------------
