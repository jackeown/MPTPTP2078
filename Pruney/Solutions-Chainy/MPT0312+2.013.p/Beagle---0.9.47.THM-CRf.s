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
% DateTime   : Thu Dec  3 09:53:54 EST 2020

% Result     : Theorem 2.44s
% Output     : CNFRefutation 2.80s
% Verified   : 
% Statistics : Number of formulae       :   61 ( 100 expanded)
%              Number of leaves         :   29 (  48 expanded)
%              Depth                    :   10
%              Number of atoms          :   44 (  89 expanded)
%              Number of equality atoms :   37 (  76 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k3_xboole_0 > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

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

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(f_33,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

tff(f_37,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_35,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_62,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( r1_tarski(A,B)
          & r1_tarski(C,D) )
       => k3_xboole_0(k2_zfmisc_1(A,D),k2_zfmisc_1(B,C)) = k2_zfmisc_1(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t124_zfmisc_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k5_xboole_0(k5_xboole_0(A,B),k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_xboole_1)).

tff(f_55,axiom,(
    ! [A,B,C,D] : k2_zfmisc_1(k3_xboole_0(A,B),k3_xboole_0(C,D)) = k3_xboole_0(k2_zfmisc_1(A,C),k2_zfmisc_1(B,D)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_zfmisc_1)).

tff(c_6,plain,(
    ! [A_5] : k5_xboole_0(A_5,k1_xboole_0) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_10,plain,(
    ! [A_9] : k5_xboole_0(A_9,A_9) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_199,plain,(
    ! [A_62,B_63,C_64] : k5_xboole_0(k5_xboole_0(A_62,B_63),C_64) = k5_xboole_0(A_62,k5_xboole_0(B_63,C_64)) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_631,plain,(
    ! [A_75,C_76] : k5_xboole_0(A_75,k5_xboole_0(A_75,C_76)) = k5_xboole_0(k1_xboole_0,C_76) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_199])).

tff(c_733,plain,(
    ! [A_9] : k5_xboole_0(k1_xboole_0,A_9) = k5_xboole_0(A_9,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_631])).

tff(c_758,plain,(
    ! [A_9] : k5_xboole_0(k1_xboole_0,A_9) = A_9 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_733])).

tff(c_256,plain,(
    ! [A_9,C_64] : k5_xboole_0(A_9,k5_xboole_0(A_9,C_64)) = k5_xboole_0(k1_xboole_0,C_64) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_199])).

tff(c_759,plain,(
    ! [A_9,C_64] : k5_xboole_0(A_9,k5_xboole_0(A_9,C_64)) = C_64 ),
    inference(demodulation,[status(thm),theory(equality)],[c_758,c_256])).

tff(c_224,plain,(
    ! [A_62,B_63] : k5_xboole_0(A_62,k5_xboole_0(B_63,k5_xboole_0(A_62,B_63))) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_199,c_10])).

tff(c_829,plain,(
    ! [A_78,C_79] : k5_xboole_0(A_78,k5_xboole_0(A_78,C_79)) = C_79 ),
    inference(demodulation,[status(thm),theory(equality)],[c_758,c_256])).

tff(c_879,plain,(
    ! [B_63,A_62] : k5_xboole_0(B_63,k5_xboole_0(A_62,B_63)) = k5_xboole_0(A_62,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_224,c_829])).

tff(c_931,plain,(
    ! [B_81,A_82] : k5_xboole_0(B_81,k5_xboole_0(A_82,B_81)) = A_82 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_879])).

tff(c_967,plain,(
    ! [A_9,C_64] : k5_xboole_0(k5_xboole_0(A_9,C_64),C_64) = A_9 ),
    inference(superposition,[status(thm),theory(equality)],[c_759,c_931])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_32,plain,(
    r1_tarski('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_95,plain,(
    ! [A_49,B_50] :
      ( k2_xboole_0(A_49,B_50) = B_50
      | ~ r1_tarski(A_49,B_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_102,plain,(
    k2_xboole_0('#skF_3','#skF_4') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_32,c_95])).

tff(c_139,plain,(
    ! [A_58,B_59] : k5_xboole_0(k5_xboole_0(A_58,B_59),k2_xboole_0(A_58,B_59)) = k3_xboole_0(A_58,B_59) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_157,plain,(
    k5_xboole_0(k5_xboole_0('#skF_3','#skF_4'),'#skF_4') = k3_xboole_0('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_102,c_139])).

tff(c_168,plain,(
    k5_xboole_0(k5_xboole_0('#skF_3','#skF_4'),'#skF_4') = k3_xboole_0('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_157])).

tff(c_1125,plain,(
    k3_xboole_0('#skF_4','#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_967,c_168])).

tff(c_34,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_103,plain,(
    k2_xboole_0('#skF_1','#skF_2') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_34,c_95])).

tff(c_154,plain,(
    k5_xboole_0(k5_xboole_0('#skF_1','#skF_2'),'#skF_2') = k3_xboole_0('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_103,c_139])).

tff(c_8,plain,(
    ! [A_6,B_7,C_8] : k5_xboole_0(k5_xboole_0(A_6,B_7),C_8) = k5_xboole_0(A_6,k5_xboole_0(B_7,C_8)) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_499,plain,(
    k5_xboole_0('#skF_1',k5_xboole_0('#skF_2','#skF_2')) = k3_xboole_0('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_154,c_8])).

tff(c_508,plain,(
    k3_xboole_0('#skF_1','#skF_2') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_10,c_499])).

tff(c_28,plain,(
    ! [A_41,C_43,B_42,D_44] : k3_xboole_0(k2_zfmisc_1(A_41,C_43),k2_zfmisc_1(B_42,D_44)) = k2_zfmisc_1(k3_xboole_0(A_41,B_42),k3_xboole_0(C_43,D_44)) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_30,plain,(
    k3_xboole_0(k2_zfmisc_1('#skF_1','#skF_4'),k2_zfmisc_1('#skF_2','#skF_3')) != k2_zfmisc_1('#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_35,plain,(
    k2_zfmisc_1(k3_xboole_0('#skF_1','#skF_2'),k3_xboole_0('#skF_4','#skF_3')) != k2_zfmisc_1('#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_30])).

tff(c_513,plain,(
    k2_zfmisc_1('#skF_1',k3_xboole_0('#skF_4','#skF_3')) != k2_zfmisc_1('#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_508,c_35])).

tff(c_1128,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1125,c_513])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n020.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 15:04:52 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.44/1.45  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.44/1.45  
% 2.44/1.45  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.44/1.45  %$ r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k3_xboole_0 > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.44/1.45  
% 2.44/1.45  %Foreground sorts:
% 2.44/1.45  
% 2.44/1.45  
% 2.44/1.45  %Background operators:
% 2.44/1.45  
% 2.44/1.45  
% 2.44/1.45  %Foreground operators:
% 2.44/1.45  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.44/1.45  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.44/1.45  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.44/1.45  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.44/1.45  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.44/1.45  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.44/1.45  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.44/1.45  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.44/1.45  tff('#skF_2', type, '#skF_2': $i).
% 2.44/1.45  tff('#skF_3', type, '#skF_3': $i).
% 2.44/1.45  tff('#skF_1', type, '#skF_1': $i).
% 2.44/1.45  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.44/1.45  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.44/1.45  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.44/1.45  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.44/1.45  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.44/1.45  tff('#skF_4', type, '#skF_4': $i).
% 2.44/1.45  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.44/1.45  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.44/1.45  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.44/1.45  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.44/1.45  
% 2.80/1.46  tff(f_33, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 2.80/1.46  tff(f_37, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t92_xboole_1)).
% 2.80/1.46  tff(f_35, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_xboole_1)).
% 2.80/1.46  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 2.80/1.46  tff(f_62, negated_conjecture, ~(![A, B, C, D]: ((r1_tarski(A, B) & r1_tarski(C, D)) => (k3_xboole_0(k2_zfmisc_1(A, D), k2_zfmisc_1(B, C)) = k2_zfmisc_1(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t124_zfmisc_1)).
% 2.80/1.46  tff(f_31, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 2.80/1.46  tff(f_39, axiom, (![A, B]: (k3_xboole_0(A, B) = k5_xboole_0(k5_xboole_0(A, B), k2_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t95_xboole_1)).
% 2.80/1.46  tff(f_55, axiom, (![A, B, C, D]: (k2_zfmisc_1(k3_xboole_0(A, B), k3_xboole_0(C, D)) = k3_xboole_0(k2_zfmisc_1(A, C), k2_zfmisc_1(B, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t123_zfmisc_1)).
% 2.80/1.46  tff(c_6, plain, (![A_5]: (k5_xboole_0(A_5, k1_xboole_0)=A_5)), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.80/1.46  tff(c_10, plain, (![A_9]: (k5_xboole_0(A_9, A_9)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.80/1.46  tff(c_199, plain, (![A_62, B_63, C_64]: (k5_xboole_0(k5_xboole_0(A_62, B_63), C_64)=k5_xboole_0(A_62, k5_xboole_0(B_63, C_64)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.80/1.46  tff(c_631, plain, (![A_75, C_76]: (k5_xboole_0(A_75, k5_xboole_0(A_75, C_76))=k5_xboole_0(k1_xboole_0, C_76))), inference(superposition, [status(thm), theory('equality')], [c_10, c_199])).
% 2.80/1.46  tff(c_733, plain, (![A_9]: (k5_xboole_0(k1_xboole_0, A_9)=k5_xboole_0(A_9, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_10, c_631])).
% 2.80/1.46  tff(c_758, plain, (![A_9]: (k5_xboole_0(k1_xboole_0, A_9)=A_9)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_733])).
% 2.80/1.46  tff(c_256, plain, (![A_9, C_64]: (k5_xboole_0(A_9, k5_xboole_0(A_9, C_64))=k5_xboole_0(k1_xboole_0, C_64))), inference(superposition, [status(thm), theory('equality')], [c_10, c_199])).
% 2.80/1.46  tff(c_759, plain, (![A_9, C_64]: (k5_xboole_0(A_9, k5_xboole_0(A_9, C_64))=C_64)), inference(demodulation, [status(thm), theory('equality')], [c_758, c_256])).
% 2.80/1.46  tff(c_224, plain, (![A_62, B_63]: (k5_xboole_0(A_62, k5_xboole_0(B_63, k5_xboole_0(A_62, B_63)))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_199, c_10])).
% 2.80/1.46  tff(c_829, plain, (![A_78, C_79]: (k5_xboole_0(A_78, k5_xboole_0(A_78, C_79))=C_79)), inference(demodulation, [status(thm), theory('equality')], [c_758, c_256])).
% 2.80/1.46  tff(c_879, plain, (![B_63, A_62]: (k5_xboole_0(B_63, k5_xboole_0(A_62, B_63))=k5_xboole_0(A_62, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_224, c_829])).
% 2.80/1.46  tff(c_931, plain, (![B_81, A_82]: (k5_xboole_0(B_81, k5_xboole_0(A_82, B_81))=A_82)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_879])).
% 2.80/1.46  tff(c_967, plain, (![A_9, C_64]: (k5_xboole_0(k5_xboole_0(A_9, C_64), C_64)=A_9)), inference(superposition, [status(thm), theory('equality')], [c_759, c_931])).
% 2.80/1.46  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.80/1.46  tff(c_32, plain, (r1_tarski('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.80/1.46  tff(c_95, plain, (![A_49, B_50]: (k2_xboole_0(A_49, B_50)=B_50 | ~r1_tarski(A_49, B_50))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.80/1.46  tff(c_102, plain, (k2_xboole_0('#skF_3', '#skF_4')='#skF_4'), inference(resolution, [status(thm)], [c_32, c_95])).
% 2.80/1.46  tff(c_139, plain, (![A_58, B_59]: (k5_xboole_0(k5_xboole_0(A_58, B_59), k2_xboole_0(A_58, B_59))=k3_xboole_0(A_58, B_59))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.80/1.46  tff(c_157, plain, (k5_xboole_0(k5_xboole_0('#skF_3', '#skF_4'), '#skF_4')=k3_xboole_0('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_102, c_139])).
% 2.80/1.46  tff(c_168, plain, (k5_xboole_0(k5_xboole_0('#skF_3', '#skF_4'), '#skF_4')=k3_xboole_0('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_157])).
% 2.80/1.46  tff(c_1125, plain, (k3_xboole_0('#skF_4', '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_967, c_168])).
% 2.80/1.46  tff(c_34, plain, (r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.80/1.46  tff(c_103, plain, (k2_xboole_0('#skF_1', '#skF_2')='#skF_2'), inference(resolution, [status(thm)], [c_34, c_95])).
% 2.80/1.46  tff(c_154, plain, (k5_xboole_0(k5_xboole_0('#skF_1', '#skF_2'), '#skF_2')=k3_xboole_0('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_103, c_139])).
% 2.80/1.46  tff(c_8, plain, (![A_6, B_7, C_8]: (k5_xboole_0(k5_xboole_0(A_6, B_7), C_8)=k5_xboole_0(A_6, k5_xboole_0(B_7, C_8)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.80/1.46  tff(c_499, plain, (k5_xboole_0('#skF_1', k5_xboole_0('#skF_2', '#skF_2'))=k3_xboole_0('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_154, c_8])).
% 2.80/1.46  tff(c_508, plain, (k3_xboole_0('#skF_1', '#skF_2')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_6, c_10, c_499])).
% 2.80/1.46  tff(c_28, plain, (![A_41, C_43, B_42, D_44]: (k3_xboole_0(k2_zfmisc_1(A_41, C_43), k2_zfmisc_1(B_42, D_44))=k2_zfmisc_1(k3_xboole_0(A_41, B_42), k3_xboole_0(C_43, D_44)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.80/1.46  tff(c_30, plain, (k3_xboole_0(k2_zfmisc_1('#skF_1', '#skF_4'), k2_zfmisc_1('#skF_2', '#skF_3'))!=k2_zfmisc_1('#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.80/1.46  tff(c_35, plain, (k2_zfmisc_1(k3_xboole_0('#skF_1', '#skF_2'), k3_xboole_0('#skF_4', '#skF_3'))!=k2_zfmisc_1('#skF_1', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_30])).
% 2.80/1.46  tff(c_513, plain, (k2_zfmisc_1('#skF_1', k3_xboole_0('#skF_4', '#skF_3'))!=k2_zfmisc_1('#skF_1', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_508, c_35])).
% 2.80/1.46  tff(c_1128, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1125, c_513])).
% 2.80/1.46  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.80/1.46  
% 2.80/1.46  Inference rules
% 2.80/1.46  ----------------------
% 2.80/1.46  #Ref     : 0
% 2.80/1.46  #Sup     : 267
% 2.80/1.46  #Fact    : 0
% 2.80/1.46  #Define  : 0
% 2.80/1.46  #Split   : 0
% 2.80/1.46  #Chain   : 0
% 2.80/1.46  #Close   : 0
% 2.80/1.46  
% 2.80/1.46  Ordering : KBO
% 2.80/1.46  
% 2.80/1.46  Simplification rules
% 2.80/1.46  ----------------------
% 2.80/1.46  #Subsume      : 4
% 2.80/1.46  #Demod        : 203
% 2.80/1.46  #Tautology    : 173
% 2.80/1.46  #SimpNegUnit  : 0
% 2.80/1.46  #BackRed      : 8
% 2.80/1.46  
% 2.80/1.46  #Partial instantiations: 0
% 2.80/1.46  #Strategies tried      : 1
% 2.80/1.46  
% 2.80/1.46  Timing (in seconds)
% 2.80/1.46  ----------------------
% 2.80/1.47  Preprocessing        : 0.30
% 2.80/1.47  Parsing              : 0.16
% 2.80/1.47  CNF conversion       : 0.02
% 2.80/1.47  Main loop            : 0.32
% 2.80/1.47  Inferencing          : 0.11
% 2.80/1.47  Reduction            : 0.13
% 2.80/1.47  Demodulation         : 0.11
% 2.80/1.47  BG Simplification    : 0.02
% 2.80/1.47  Subsumption          : 0.04
% 2.80/1.47  Abstraction          : 0.02
% 2.80/1.47  MUC search           : 0.00
% 2.80/1.47  Cooper               : 0.00
% 2.80/1.47  Total                : 0.65
% 2.80/1.47  Index Insertion      : 0.00
% 2.80/1.47  Index Deletion       : 0.00
% 2.80/1.47  Index Matching       : 0.00
% 2.80/1.47  BG Taut test         : 0.00
%------------------------------------------------------------------------------
