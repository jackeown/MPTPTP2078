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
% DateTime   : Thu Dec  3 09:54:08 EST 2020

% Result     : Theorem 1.84s
% Output     : CNFRefutation 1.84s
% Verified   : 
% Statistics : Number of formulae       :   48 (  57 expanded)
%              Number of leaves         :   25 (  31 expanded)
%              Depth                    :    6
%              Number of atoms          :   42 (  65 expanded)
%              Number of equality atoms :   40 (  63 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1

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

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(f_49,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_66,negated_conjecture,(
    ~ ! [A,B] :
        ( A != k1_xboole_0
       => ( k2_zfmisc_1(k1_tarski(B),A) != k1_xboole_0
          & k2_zfmisc_1(A,k1_tarski(B)) != k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t130_zfmisc_1)).

tff(f_29,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_31,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_51,axiom,(
    ! [A,B] : k3_xboole_0(k1_tarski(A),k2_tarski(A,B)) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_zfmisc_1)).

tff(f_27,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_56,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
    <=> A != B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_zfmisc_1)).

tff(c_24,plain,(
    ! [B_33] : k2_zfmisc_1(k1_xboole_0,B_33) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_34,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_4,plain,(
    ! [A_3] : k5_xboole_0(A_3,A_3) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_6,plain,(
    ! [A_4] : k2_tarski(A_4,A_4) = k1_tarski(A_4) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_92,plain,(
    ! [A_47,B_48] : k3_xboole_0(k1_tarski(A_47),k2_tarski(A_47,B_48)) = k1_tarski(A_47) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_113,plain,(
    ! [A_49] : k3_xboole_0(k1_tarski(A_49),k1_tarski(A_49)) = k1_tarski(A_49) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_92])).

tff(c_2,plain,(
    ! [A_1,B_2] : k5_xboole_0(A_1,k3_xboole_0(A_1,B_2)) = k4_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_119,plain,(
    ! [A_49] : k5_xboole_0(k1_tarski(A_49),k1_tarski(A_49)) = k4_xboole_0(k1_tarski(A_49),k1_tarski(A_49)) ),
    inference(superposition,[status(thm),theory(equality)],[c_113,c_2])).

tff(c_124,plain,(
    ! [A_49] : k4_xboole_0(k1_tarski(A_49),k1_tarski(A_49)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_119])).

tff(c_28,plain,(
    ! [B_37] : k4_xboole_0(k1_tarski(B_37),k1_tarski(B_37)) != k1_tarski(B_37) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_126,plain,(
    ! [B_37] : k1_tarski(B_37) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_124,c_28])).

tff(c_32,plain,
    ( k2_zfmisc_1('#skF_1',k1_tarski('#skF_2')) = k1_xboole_0
    | k2_zfmisc_1(k1_tarski('#skF_2'),'#skF_1') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_108,plain,(
    k2_zfmisc_1(k1_tarski('#skF_2'),'#skF_1') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_32])).

tff(c_146,plain,(
    ! [B_54,A_55] :
      ( k1_xboole_0 = B_54
      | k1_xboole_0 = A_55
      | k2_zfmisc_1(A_55,B_54) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_149,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_tarski('#skF_2') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_108,c_146])).

tff(c_159,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_126,c_34,c_149])).

tff(c_160,plain,(
    k2_zfmisc_1('#skF_1',k1_tarski('#skF_2')) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_32])).

tff(c_176,plain,(
    ! [B_58,A_59] :
      ( k1_xboole_0 = B_58
      | k1_xboole_0 = A_59
      | k2_zfmisc_1(A_59,B_58) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_179,plain,
    ( k1_tarski('#skF_2') = k1_xboole_0
    | k1_xboole_0 = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_160,c_176])).

tff(c_188,plain,(
    k1_tarski('#skF_2') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_179])).

tff(c_161,plain,(
    k2_zfmisc_1(k1_tarski('#skF_2'),'#skF_1') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_32])).

tff(c_193,plain,(
    k2_zfmisc_1(k1_xboole_0,'#skF_1') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_188,c_161])).

tff(c_197,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_193])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n020.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 09:20:37 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.84/1.15  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.84/1.15  
% 1.84/1.15  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.84/1.15  %$ k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1
% 1.84/1.15  
% 1.84/1.15  %Foreground sorts:
% 1.84/1.15  
% 1.84/1.15  
% 1.84/1.15  %Background operators:
% 1.84/1.15  
% 1.84/1.15  
% 1.84/1.15  %Foreground operators:
% 1.84/1.15  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.84/1.15  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.84/1.15  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.84/1.15  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.84/1.15  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 1.84/1.15  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 1.84/1.15  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.84/1.15  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.84/1.15  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.84/1.15  tff('#skF_2', type, '#skF_2': $i).
% 1.84/1.15  tff('#skF_1', type, '#skF_1': $i).
% 1.84/1.15  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 1.84/1.15  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 1.84/1.15  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.84/1.15  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.84/1.15  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.84/1.15  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.84/1.15  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 1.84/1.15  
% 1.84/1.16  tff(f_49, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 1.84/1.16  tff(f_66, negated_conjecture, ~(![A, B]: (~(A = k1_xboole_0) => (~(k2_zfmisc_1(k1_tarski(B), A) = k1_xboole_0) & ~(k2_zfmisc_1(A, k1_tarski(B)) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t130_zfmisc_1)).
% 1.84/1.16  tff(f_29, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t92_xboole_1)).
% 1.84/1.16  tff(f_31, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 1.84/1.16  tff(f_51, axiom, (![A, B]: (k3_xboole_0(k1_tarski(A), k2_tarski(A, B)) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t19_zfmisc_1)).
% 1.84/1.16  tff(f_27, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 1.84/1.16  tff(f_56, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) <=> ~(A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_zfmisc_1)).
% 1.84/1.16  tff(c_24, plain, (![B_33]: (k2_zfmisc_1(k1_xboole_0, B_33)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_49])).
% 1.84/1.16  tff(c_34, plain, (k1_xboole_0!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_66])).
% 1.84/1.16  tff(c_4, plain, (![A_3]: (k5_xboole_0(A_3, A_3)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.84/1.16  tff(c_6, plain, (![A_4]: (k2_tarski(A_4, A_4)=k1_tarski(A_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.84/1.16  tff(c_92, plain, (![A_47, B_48]: (k3_xboole_0(k1_tarski(A_47), k2_tarski(A_47, B_48))=k1_tarski(A_47))), inference(cnfTransformation, [status(thm)], [f_51])).
% 1.84/1.16  tff(c_113, plain, (![A_49]: (k3_xboole_0(k1_tarski(A_49), k1_tarski(A_49))=k1_tarski(A_49))), inference(superposition, [status(thm), theory('equality')], [c_6, c_92])).
% 1.84/1.16  tff(c_2, plain, (![A_1, B_2]: (k5_xboole_0(A_1, k3_xboole_0(A_1, B_2))=k4_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.84/1.16  tff(c_119, plain, (![A_49]: (k5_xboole_0(k1_tarski(A_49), k1_tarski(A_49))=k4_xboole_0(k1_tarski(A_49), k1_tarski(A_49)))), inference(superposition, [status(thm), theory('equality')], [c_113, c_2])).
% 1.84/1.16  tff(c_124, plain, (![A_49]: (k4_xboole_0(k1_tarski(A_49), k1_tarski(A_49))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_4, c_119])).
% 1.84/1.16  tff(c_28, plain, (![B_37]: (k4_xboole_0(k1_tarski(B_37), k1_tarski(B_37))!=k1_tarski(B_37))), inference(cnfTransformation, [status(thm)], [f_56])).
% 1.84/1.16  tff(c_126, plain, (![B_37]: (k1_tarski(B_37)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_124, c_28])).
% 1.84/1.16  tff(c_32, plain, (k2_zfmisc_1('#skF_1', k1_tarski('#skF_2'))=k1_xboole_0 | k2_zfmisc_1(k1_tarski('#skF_2'), '#skF_1')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_66])).
% 1.84/1.16  tff(c_108, plain, (k2_zfmisc_1(k1_tarski('#skF_2'), '#skF_1')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_32])).
% 1.84/1.16  tff(c_146, plain, (![B_54, A_55]: (k1_xboole_0=B_54 | k1_xboole_0=A_55 | k2_zfmisc_1(A_55, B_54)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_49])).
% 1.84/1.16  tff(c_149, plain, (k1_xboole_0='#skF_1' | k1_tarski('#skF_2')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_108, c_146])).
% 1.84/1.16  tff(c_159, plain, $false, inference(negUnitSimplification, [status(thm)], [c_126, c_34, c_149])).
% 1.84/1.16  tff(c_160, plain, (k2_zfmisc_1('#skF_1', k1_tarski('#skF_2'))=k1_xboole_0), inference(splitRight, [status(thm)], [c_32])).
% 1.84/1.16  tff(c_176, plain, (![B_58, A_59]: (k1_xboole_0=B_58 | k1_xboole_0=A_59 | k2_zfmisc_1(A_59, B_58)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_49])).
% 1.84/1.16  tff(c_179, plain, (k1_tarski('#skF_2')=k1_xboole_0 | k1_xboole_0='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_160, c_176])).
% 1.84/1.16  tff(c_188, plain, (k1_tarski('#skF_2')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_34, c_179])).
% 1.84/1.16  tff(c_161, plain, (k2_zfmisc_1(k1_tarski('#skF_2'), '#skF_1')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_32])).
% 1.84/1.16  tff(c_193, plain, (k2_zfmisc_1(k1_xboole_0, '#skF_1')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_188, c_161])).
% 1.84/1.16  tff(c_197, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_24, c_193])).
% 1.84/1.16  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.84/1.16  
% 1.84/1.16  Inference rules
% 1.84/1.16  ----------------------
% 1.84/1.16  #Ref     : 0
% 1.84/1.16  #Sup     : 39
% 1.84/1.16  #Fact    : 0
% 1.84/1.16  #Define  : 0
% 1.84/1.16  #Split   : 1
% 1.84/1.16  #Chain   : 0
% 1.84/1.16  #Close   : 0
% 1.84/1.16  
% 1.84/1.16  Ordering : KBO
% 1.84/1.16  
% 1.84/1.16  Simplification rules
% 1.84/1.16  ----------------------
% 1.84/1.16  #Subsume      : 0
% 1.84/1.16  #Demod        : 7
% 1.84/1.16  #Tautology    : 31
% 1.84/1.16  #SimpNegUnit  : 2
% 1.84/1.16  #BackRed      : 3
% 1.84/1.16  
% 1.84/1.16  #Partial instantiations: 0
% 1.84/1.16  #Strategies tried      : 1
% 1.84/1.16  
% 1.84/1.16  Timing (in seconds)
% 1.84/1.16  ----------------------
% 1.84/1.16  Preprocessing        : 0.30
% 1.84/1.16  Parsing              : 0.16
% 1.84/1.16  CNF conversion       : 0.02
% 1.84/1.16  Main loop            : 0.12
% 1.84/1.17  Inferencing          : 0.04
% 1.84/1.17  Reduction            : 0.04
% 1.84/1.17  Demodulation         : 0.03
% 1.84/1.17  BG Simplification    : 0.01
% 1.84/1.17  Subsumption          : 0.02
% 1.84/1.17  Abstraction          : 0.01
% 1.84/1.17  MUC search           : 0.00
% 1.84/1.17  Cooper               : 0.00
% 1.84/1.17  Total                : 0.44
% 1.84/1.17  Index Insertion      : 0.00
% 1.84/1.17  Index Deletion       : 0.00
% 1.84/1.17  Index Matching       : 0.00
% 1.84/1.17  BG Taut test         : 0.00
%------------------------------------------------------------------------------
