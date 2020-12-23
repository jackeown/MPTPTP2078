%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:49:49 EST 2020

% Result     : Theorem 2.70s
% Output     : CNFRefutation 2.70s
% Verified   : 
% Statistics : Number of formulae       :   55 (  88 expanded)
%              Number of leaves         :   30 (  44 expanded)
%              Depth                    :    7
%              Number of atoms          :   47 (  90 expanded)
%              Number of equality atoms :   37 (  76 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1

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

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

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

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(f_35,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

tff(f_43,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_57,axiom,(
    ! [A,B] : r1_tarski(k1_tarski(A),k2_tarski(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_zfmisc_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_41,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_55,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_62,axiom,(
    ! [A,B] :
      ( A != B
     => r1_xboole_0(k1_tarski(A),k1_tarski(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_zfmisc_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_67,axiom,(
    ! [A,B] :
      ( A != B
     => k5_xboole_0(k1_tarski(A),k1_tarski(B)) = k2_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_zfmisc_1)).

tff(f_70,negated_conjecture,(
    ~ ! [A,B] : k3_tarski(k2_tarski(k1_tarski(A),k1_tarski(B))) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_zfmisc_1)).

tff(c_10,plain,(
    ! [A_7] : k5_xboole_0(A_7,k1_xboole_0) = A_7 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_18,plain,(
    ! [A_12] : k2_tarski(A_12,A_12) = k1_tarski(A_12) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_58,plain,(
    ! [A_43,B_44] : r1_tarski(k1_tarski(A_43),k2_tarski(A_43,B_44)) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_61,plain,(
    ! [A_12] : r1_tarski(k1_tarski(A_12),k1_tarski(A_12)) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_58])).

tff(c_96,plain,(
    ! [A_48,B_49] :
      ( k4_xboole_0(A_48,B_49) = k1_xboole_0
      | ~ r1_tarski(A_48,B_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_103,plain,(
    ! [A_12] : k4_xboole_0(k1_tarski(A_12),k1_tarski(A_12)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_61,c_96])).

tff(c_192,plain,(
    ! [A_68,B_69] : k5_xboole_0(A_68,k4_xboole_0(B_69,A_68)) = k2_xboole_0(A_68,B_69) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_204,plain,(
    ! [A_12] : k2_xboole_0(k1_tarski(A_12),k1_tarski(A_12)) = k5_xboole_0(k1_tarski(A_12),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_103,c_192])).

tff(c_209,plain,(
    ! [A_70] : k2_xboole_0(k1_tarski(A_70),k1_tarski(A_70)) = k1_tarski(A_70) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_204])).

tff(c_132,plain,(
    ! [A_59,B_60] : k3_tarski(k2_tarski(A_59,B_60)) = k2_xboole_0(A_59,B_60) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_141,plain,(
    ! [A_12] : k3_tarski(k1_tarski(A_12)) = k2_xboole_0(A_12,A_12) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_132])).

tff(c_215,plain,(
    ! [A_70] : k3_tarski(k1_tarski(k1_tarski(A_70))) = k1_tarski(A_70) ),
    inference(superposition,[status(thm),theory(equality)],[c_209,c_141])).

tff(c_127,plain,(
    ! [A_57,B_58] :
      ( r1_xboole_0(k1_tarski(A_57),k1_tarski(B_58))
      | B_58 = A_57 ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_12,plain,(
    ! [A_8,B_9] :
      ( k4_xboole_0(A_8,B_9) = A_8
      | ~ r1_xboole_0(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_272,plain,(
    ! [A_77,B_78] :
      ( k4_xboole_0(k1_tarski(A_77),k1_tarski(B_78)) = k1_tarski(A_77)
      | B_78 = A_77 ) ),
    inference(resolution,[status(thm)],[c_127,c_12])).

tff(c_16,plain,(
    ! [A_10,B_11] : k5_xboole_0(A_10,k4_xboole_0(B_11,A_10)) = k2_xboole_0(A_10,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_324,plain,(
    ! [B_87,A_88] :
      ( k5_xboole_0(k1_tarski(B_87),k1_tarski(A_88)) = k2_xboole_0(k1_tarski(B_87),k1_tarski(A_88))
      | B_87 = A_88 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_272,c_16])).

tff(c_36,plain,(
    ! [A_39,B_40] :
      ( k5_xboole_0(k1_tarski(A_39),k1_tarski(B_40)) = k2_tarski(A_39,B_40)
      | B_40 = A_39 ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_348,plain,(
    ! [B_94,A_95] :
      ( k2_xboole_0(k1_tarski(B_94),k1_tarski(A_95)) = k2_tarski(B_94,A_95)
      | B_94 = A_95
      | B_94 = A_95 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_324,c_36])).

tff(c_30,plain,(
    ! [A_33,B_34] : k3_tarski(k2_tarski(A_33,B_34)) = k2_xboole_0(A_33,B_34) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_38,plain,(
    k3_tarski(k2_tarski(k1_tarski('#skF_1'),k1_tarski('#skF_2'))) != k2_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_39,plain,(
    k2_xboole_0(k1_tarski('#skF_1'),k1_tarski('#skF_2')) != k2_tarski('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_38])).

tff(c_378,plain,(
    '#skF_2' = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_348,c_39])).

tff(c_384,plain,(
    k2_xboole_0(k1_tarski('#skF_1'),k1_tarski('#skF_1')) != k2_tarski('#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_378,c_378,c_39])).

tff(c_387,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_215,c_141,c_18,c_384])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n023.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 10:26:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.70/1.71  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.70/1.71  
% 2.70/1.71  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.70/1.72  %$ r1_xboole_0 > r1_tarski > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1
% 2.70/1.72  
% 2.70/1.72  %Foreground sorts:
% 2.70/1.72  
% 2.70/1.72  
% 2.70/1.72  %Background operators:
% 2.70/1.72  
% 2.70/1.72  
% 2.70/1.72  %Foreground operators:
% 2.70/1.72  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.70/1.72  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.70/1.72  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.70/1.72  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.70/1.72  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.70/1.72  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.70/1.72  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.70/1.72  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.70/1.72  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.70/1.72  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.70/1.72  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.70/1.72  tff('#skF_2', type, '#skF_2': $i).
% 2.70/1.72  tff('#skF_1', type, '#skF_1': $i).
% 2.70/1.72  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.70/1.72  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.70/1.72  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.70/1.72  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.70/1.72  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.70/1.72  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.70/1.72  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.70/1.72  
% 2.70/1.74  tff(f_35, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 2.70/1.74  tff(f_43, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 2.70/1.74  tff(f_57, axiom, (![A, B]: r1_tarski(k1_tarski(A), k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_zfmisc_1)).
% 2.70/1.74  tff(f_31, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 2.70/1.74  tff(f_41, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_xboole_1)).
% 2.70/1.74  tff(f_55, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 2.70/1.74  tff(f_62, axiom, (![A, B]: (~(A = B) => r1_xboole_0(k1_tarski(A), k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_zfmisc_1)).
% 2.70/1.74  tff(f_39, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 2.70/1.74  tff(f_67, axiom, (![A, B]: (~(A = B) => (k5_xboole_0(k1_tarski(A), k1_tarski(B)) = k2_tarski(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_zfmisc_1)).
% 2.70/1.74  tff(f_70, negated_conjecture, ~(![A, B]: (k3_tarski(k2_tarski(k1_tarski(A), k1_tarski(B))) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t32_zfmisc_1)).
% 2.70/1.74  tff(c_10, plain, (![A_7]: (k5_xboole_0(A_7, k1_xboole_0)=A_7)), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.70/1.74  tff(c_18, plain, (![A_12]: (k2_tarski(A_12, A_12)=k1_tarski(A_12))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.70/1.74  tff(c_58, plain, (![A_43, B_44]: (r1_tarski(k1_tarski(A_43), k2_tarski(A_43, B_44)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.70/1.74  tff(c_61, plain, (![A_12]: (r1_tarski(k1_tarski(A_12), k1_tarski(A_12)))), inference(superposition, [status(thm), theory('equality')], [c_18, c_58])).
% 2.70/1.74  tff(c_96, plain, (![A_48, B_49]: (k4_xboole_0(A_48, B_49)=k1_xboole_0 | ~r1_tarski(A_48, B_49))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.70/1.74  tff(c_103, plain, (![A_12]: (k4_xboole_0(k1_tarski(A_12), k1_tarski(A_12))=k1_xboole_0)), inference(resolution, [status(thm)], [c_61, c_96])).
% 2.70/1.74  tff(c_192, plain, (![A_68, B_69]: (k5_xboole_0(A_68, k4_xboole_0(B_69, A_68))=k2_xboole_0(A_68, B_69))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.70/1.74  tff(c_204, plain, (![A_12]: (k2_xboole_0(k1_tarski(A_12), k1_tarski(A_12))=k5_xboole_0(k1_tarski(A_12), k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_103, c_192])).
% 2.70/1.74  tff(c_209, plain, (![A_70]: (k2_xboole_0(k1_tarski(A_70), k1_tarski(A_70))=k1_tarski(A_70))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_204])).
% 2.70/1.74  tff(c_132, plain, (![A_59, B_60]: (k3_tarski(k2_tarski(A_59, B_60))=k2_xboole_0(A_59, B_60))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.70/1.74  tff(c_141, plain, (![A_12]: (k3_tarski(k1_tarski(A_12))=k2_xboole_0(A_12, A_12))), inference(superposition, [status(thm), theory('equality')], [c_18, c_132])).
% 2.70/1.74  tff(c_215, plain, (![A_70]: (k3_tarski(k1_tarski(k1_tarski(A_70)))=k1_tarski(A_70))), inference(superposition, [status(thm), theory('equality')], [c_209, c_141])).
% 2.70/1.74  tff(c_127, plain, (![A_57, B_58]: (r1_xboole_0(k1_tarski(A_57), k1_tarski(B_58)) | B_58=A_57)), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.70/1.74  tff(c_12, plain, (![A_8, B_9]: (k4_xboole_0(A_8, B_9)=A_8 | ~r1_xboole_0(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.70/1.74  tff(c_272, plain, (![A_77, B_78]: (k4_xboole_0(k1_tarski(A_77), k1_tarski(B_78))=k1_tarski(A_77) | B_78=A_77)), inference(resolution, [status(thm)], [c_127, c_12])).
% 2.70/1.74  tff(c_16, plain, (![A_10, B_11]: (k5_xboole_0(A_10, k4_xboole_0(B_11, A_10))=k2_xboole_0(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.70/1.74  tff(c_324, plain, (![B_87, A_88]: (k5_xboole_0(k1_tarski(B_87), k1_tarski(A_88))=k2_xboole_0(k1_tarski(B_87), k1_tarski(A_88)) | B_87=A_88)), inference(superposition, [status(thm), theory('equality')], [c_272, c_16])).
% 2.70/1.74  tff(c_36, plain, (![A_39, B_40]: (k5_xboole_0(k1_tarski(A_39), k1_tarski(B_40))=k2_tarski(A_39, B_40) | B_40=A_39)), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.70/1.74  tff(c_348, plain, (![B_94, A_95]: (k2_xboole_0(k1_tarski(B_94), k1_tarski(A_95))=k2_tarski(B_94, A_95) | B_94=A_95 | B_94=A_95)), inference(superposition, [status(thm), theory('equality')], [c_324, c_36])).
% 2.70/1.74  tff(c_30, plain, (![A_33, B_34]: (k3_tarski(k2_tarski(A_33, B_34))=k2_xboole_0(A_33, B_34))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.70/1.74  tff(c_38, plain, (k3_tarski(k2_tarski(k1_tarski('#skF_1'), k1_tarski('#skF_2')))!=k2_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.70/1.74  tff(c_39, plain, (k2_xboole_0(k1_tarski('#skF_1'), k1_tarski('#skF_2'))!=k2_tarski('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_38])).
% 2.70/1.74  tff(c_378, plain, ('#skF_2'='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_348, c_39])).
% 2.70/1.74  tff(c_384, plain, (k2_xboole_0(k1_tarski('#skF_1'), k1_tarski('#skF_1'))!=k2_tarski('#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_378, c_378, c_39])).
% 2.70/1.74  tff(c_387, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_215, c_141, c_18, c_384])).
% 2.70/1.74  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.70/1.74  
% 2.70/1.74  Inference rules
% 2.70/1.74  ----------------------
% 2.70/1.74  #Ref     : 0
% 2.70/1.74  #Sup     : 79
% 2.70/1.74  #Fact    : 0
% 2.70/1.74  #Define  : 0
% 2.70/1.74  #Split   : 0
% 2.70/1.74  #Chain   : 0
% 2.70/1.74  #Close   : 0
% 2.70/1.74  
% 2.70/1.74  Ordering : KBO
% 2.70/1.74  
% 2.70/1.74  Simplification rules
% 2.70/1.74  ----------------------
% 2.70/1.74  #Subsume      : 0
% 2.70/1.74  #Demod        : 21
% 2.70/1.74  #Tautology    : 66
% 2.70/1.74  #SimpNegUnit  : 0
% 2.70/1.74  #BackRed      : 1
% 2.70/1.74  
% 2.70/1.74  #Partial instantiations: 0
% 2.70/1.74  #Strategies tried      : 1
% 2.70/1.74  
% 2.70/1.74  Timing (in seconds)
% 2.70/1.74  ----------------------
% 2.70/1.74  Preprocessing        : 0.51
% 2.70/1.74  Parsing              : 0.27
% 2.70/1.74  CNF conversion       : 0.03
% 2.70/1.74  Main loop            : 0.32
% 2.70/1.74  Inferencing          : 0.14
% 2.70/1.74  Reduction            : 0.10
% 2.70/1.74  Demodulation         : 0.08
% 2.70/1.74  BG Simplification    : 0.02
% 2.70/1.74  Subsumption          : 0.04
% 2.70/1.74  Abstraction          : 0.02
% 2.70/1.74  MUC search           : 0.00
% 2.70/1.74  Cooper               : 0.00
% 2.70/1.74  Total                : 0.88
% 2.70/1.75  Index Insertion      : 0.00
% 2.70/1.75  Index Deletion       : 0.00
% 2.70/1.75  Index Matching       : 0.00
% 2.70/1.75  BG Taut test         : 0.00
%------------------------------------------------------------------------------
