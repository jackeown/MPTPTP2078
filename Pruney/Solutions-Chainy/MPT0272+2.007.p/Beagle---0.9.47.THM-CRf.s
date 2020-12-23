%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:53:07 EST 2020

% Result     : Theorem 3.37s
% Output     : CNFRefutation 3.37s
% Verified   : 
% Statistics : Number of formulae       :   55 (  77 expanded)
%              Number of leaves         :   28 (  39 expanded)
%              Depth                    :    9
%              Number of atoms          :   46 (  69 expanded)
%              Number of equality atoms :   30 (  53 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1

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

tff(f_64,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),B) = k1_tarski(A)
    <=> ~ r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l33_zfmisc_1)).

tff(f_69,negated_conjecture,(
    ~ ! [A,B] :
        ( k4_xboole_0(k1_tarski(A),B) = k1_xboole_0
        | k4_xboole_0(k1_tarski(A),B) = k1_tarski(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_zfmisc_1)).

tff(f_35,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_39,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] : r1_xboole_0(k3_xboole_0(A,B),k5_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l97_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_41,axiom,(
    ! [A,B,C] : k5_xboole_0(k3_xboole_0(A,B),k3_xboole_0(C,B)) = k3_xboole_0(k5_xboole_0(A,C),B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t112_xboole_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => k3_xboole_0(B,k1_tarski(A)) = k1_tarski(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l31_zfmisc_1)).

tff(c_259,plain,(
    ! [A_70,B_71] :
      ( k4_xboole_0(k1_tarski(A_70),B_71) = k1_tarski(A_70)
      | r2_hidden(A_70,B_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_38,plain,(
    k4_xboole_0(k1_tarski('#skF_1'),'#skF_2') != k1_tarski('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_277,plain,(
    r2_hidden('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_259,c_38])).

tff(c_10,plain,(
    ! [A_7] : k3_xboole_0(A_7,A_7) = A_7 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_206,plain,(
    ! [A_66,B_67] : k5_xboole_0(A_66,k3_xboole_0(A_66,B_67)) = k4_xboole_0(A_66,B_67) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_230,plain,(
    ! [A_7] : k5_xboole_0(A_7,A_7) = k4_xboole_0(A_7,A_7) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_206])).

tff(c_125,plain,(
    ! [A_54,B_55] : r1_xboole_0(k3_xboole_0(A_54,B_55),k5_xboole_0(A_54,B_55)) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_140,plain,(
    ! [A_7] : r1_xboole_0(A_7,k5_xboole_0(A_7,A_7)) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_125])).

tff(c_253,plain,(
    ! [A_69] : r1_xboole_0(A_69,k4_xboole_0(A_69,A_69)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_230,c_140])).

tff(c_6,plain,(
    ! [A_5,B_6] :
      ( k3_xboole_0(A_5,B_6) = k1_xboole_0
      | ~ r1_xboole_0(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_257,plain,(
    ! [A_69] : k3_xboole_0(A_69,k4_xboole_0(A_69,A_69)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_253,c_6])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_227,plain,(
    ! [B_2,A_1] : k5_xboole_0(B_2,k3_xboole_0(A_1,B_2)) = k4_xboole_0(B_2,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_206])).

tff(c_641,plain,(
    ! [A_94,B_95,C_96] : k5_xboole_0(k3_xboole_0(A_94,B_95),k3_xboole_0(C_96,B_95)) = k3_xboole_0(k5_xboole_0(A_94,C_96),B_95) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_732,plain,(
    ! [A_7,C_96] : k5_xboole_0(A_7,k3_xboole_0(C_96,A_7)) = k3_xboole_0(k5_xboole_0(A_7,C_96),A_7) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_641])).

tff(c_748,plain,(
    ! [A_97,C_98] : k3_xboole_0(A_97,k5_xboole_0(A_97,C_98)) = k4_xboole_0(A_97,C_98) ),
    inference(demodulation,[status(thm),theory(equality)],[c_227,c_2,c_732])).

tff(c_795,plain,(
    ! [A_7] : k3_xboole_0(A_7,k4_xboole_0(A_7,A_7)) = k4_xboole_0(A_7,A_7) ),
    inference(superposition,[status(thm),theory(equality)],[c_230,c_748])).

tff(c_809,plain,(
    ! [A_7] : k4_xboole_0(A_7,A_7) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_257,c_795])).

tff(c_815,plain,(
    ! [A_7] : k5_xboole_0(A_7,A_7) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_809,c_230])).

tff(c_431,plain,(
    ! [B_84,A_85] :
      ( k3_xboole_0(B_84,k1_tarski(A_85)) = k1_tarski(A_85)
      | ~ r2_hidden(A_85,B_84) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_1196,plain,(
    ! [A_128,A_129] :
      ( k3_xboole_0(k1_tarski(A_128),A_129) = k1_tarski(A_128)
      | ~ r2_hidden(A_128,A_129) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_431])).

tff(c_14,plain,(
    ! [A_11,B_12] : k5_xboole_0(A_11,k3_xboole_0(A_11,B_12)) = k4_xboole_0(A_11,B_12) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_1236,plain,(
    ! [A_128,A_129] :
      ( k5_xboole_0(k1_tarski(A_128),k1_tarski(A_128)) = k4_xboole_0(k1_tarski(A_128),A_129)
      | ~ r2_hidden(A_128,A_129) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1196,c_14])).

tff(c_1458,plain,(
    ! [A_135,A_136] :
      ( k4_xboole_0(k1_tarski(A_135),A_136) = k1_xboole_0
      | ~ r2_hidden(A_135,A_136) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_815,c_1236])).

tff(c_40,plain,(
    k4_xboole_0(k1_tarski('#skF_1'),'#skF_2') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_1484,plain,(
    ~ r2_hidden('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_1458,c_40])).

tff(c_1504,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_277,c_1484])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:29:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.37/1.58  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.37/1.59  
% 3.37/1.59  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.37/1.59  %$ r2_hidden > r1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1
% 3.37/1.59  
% 3.37/1.59  %Foreground sorts:
% 3.37/1.59  
% 3.37/1.59  
% 3.37/1.59  %Background operators:
% 3.37/1.59  
% 3.37/1.59  
% 3.37/1.59  %Foreground operators:
% 3.37/1.59  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.37/1.59  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.37/1.59  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.37/1.59  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.37/1.59  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.37/1.59  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.37/1.59  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.37/1.59  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.37/1.59  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.37/1.59  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.37/1.59  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.37/1.59  tff('#skF_2', type, '#skF_2': $i).
% 3.37/1.59  tff('#skF_1', type, '#skF_1': $i).
% 3.37/1.59  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.37/1.59  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.37/1.59  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.37/1.59  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.37/1.59  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.37/1.59  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.37/1.59  
% 3.37/1.60  tff(f_64, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), B) = k1_tarski(A)) <=> ~r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l33_zfmisc_1)).
% 3.37/1.60  tff(f_69, negated_conjecture, ~(![A, B]: ((k4_xboole_0(k1_tarski(A), B) = k1_xboole_0) | (k4_xboole_0(k1_tarski(A), B) = k1_tarski(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_zfmisc_1)).
% 3.37/1.60  tff(f_35, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 3.37/1.60  tff(f_39, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 3.37/1.60  tff(f_37, axiom, (![A, B]: r1_xboole_0(k3_xboole_0(A, B), k5_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l97_xboole_1)).
% 3.37/1.60  tff(f_33, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 3.37/1.60  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 3.37/1.60  tff(f_41, axiom, (![A, B, C]: (k5_xboole_0(k3_xboole_0(A, B), k3_xboole_0(C, B)) = k3_xboole_0(k5_xboole_0(A, C), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t112_xboole_1)).
% 3.37/1.60  tff(f_59, axiom, (![A, B]: (r2_hidden(A, B) => (k3_xboole_0(B, k1_tarski(A)) = k1_tarski(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l31_zfmisc_1)).
% 3.37/1.60  tff(c_259, plain, (![A_70, B_71]: (k4_xboole_0(k1_tarski(A_70), B_71)=k1_tarski(A_70) | r2_hidden(A_70, B_71))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.37/1.60  tff(c_38, plain, (k4_xboole_0(k1_tarski('#skF_1'), '#skF_2')!=k1_tarski('#skF_1')), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.37/1.60  tff(c_277, plain, (r2_hidden('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_259, c_38])).
% 3.37/1.60  tff(c_10, plain, (![A_7]: (k3_xboole_0(A_7, A_7)=A_7)), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.37/1.60  tff(c_206, plain, (![A_66, B_67]: (k5_xboole_0(A_66, k3_xboole_0(A_66, B_67))=k4_xboole_0(A_66, B_67))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.37/1.60  tff(c_230, plain, (![A_7]: (k5_xboole_0(A_7, A_7)=k4_xboole_0(A_7, A_7))), inference(superposition, [status(thm), theory('equality')], [c_10, c_206])).
% 3.37/1.60  tff(c_125, plain, (![A_54, B_55]: (r1_xboole_0(k3_xboole_0(A_54, B_55), k5_xboole_0(A_54, B_55)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.37/1.60  tff(c_140, plain, (![A_7]: (r1_xboole_0(A_7, k5_xboole_0(A_7, A_7)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_125])).
% 3.37/1.60  tff(c_253, plain, (![A_69]: (r1_xboole_0(A_69, k4_xboole_0(A_69, A_69)))), inference(demodulation, [status(thm), theory('equality')], [c_230, c_140])).
% 3.37/1.60  tff(c_6, plain, (![A_5, B_6]: (k3_xboole_0(A_5, B_6)=k1_xboole_0 | ~r1_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.37/1.60  tff(c_257, plain, (![A_69]: (k3_xboole_0(A_69, k4_xboole_0(A_69, A_69))=k1_xboole_0)), inference(resolution, [status(thm)], [c_253, c_6])).
% 3.37/1.60  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.37/1.60  tff(c_227, plain, (![B_2, A_1]: (k5_xboole_0(B_2, k3_xboole_0(A_1, B_2))=k4_xboole_0(B_2, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_206])).
% 3.37/1.60  tff(c_641, plain, (![A_94, B_95, C_96]: (k5_xboole_0(k3_xboole_0(A_94, B_95), k3_xboole_0(C_96, B_95))=k3_xboole_0(k5_xboole_0(A_94, C_96), B_95))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.37/1.60  tff(c_732, plain, (![A_7, C_96]: (k5_xboole_0(A_7, k3_xboole_0(C_96, A_7))=k3_xboole_0(k5_xboole_0(A_7, C_96), A_7))), inference(superposition, [status(thm), theory('equality')], [c_10, c_641])).
% 3.37/1.60  tff(c_748, plain, (![A_97, C_98]: (k3_xboole_0(A_97, k5_xboole_0(A_97, C_98))=k4_xboole_0(A_97, C_98))), inference(demodulation, [status(thm), theory('equality')], [c_227, c_2, c_732])).
% 3.37/1.60  tff(c_795, plain, (![A_7]: (k3_xboole_0(A_7, k4_xboole_0(A_7, A_7))=k4_xboole_0(A_7, A_7))), inference(superposition, [status(thm), theory('equality')], [c_230, c_748])).
% 3.37/1.60  tff(c_809, plain, (![A_7]: (k4_xboole_0(A_7, A_7)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_257, c_795])).
% 3.37/1.60  tff(c_815, plain, (![A_7]: (k5_xboole_0(A_7, A_7)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_809, c_230])).
% 3.37/1.60  tff(c_431, plain, (![B_84, A_85]: (k3_xboole_0(B_84, k1_tarski(A_85))=k1_tarski(A_85) | ~r2_hidden(A_85, B_84))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.37/1.60  tff(c_1196, plain, (![A_128, A_129]: (k3_xboole_0(k1_tarski(A_128), A_129)=k1_tarski(A_128) | ~r2_hidden(A_128, A_129))), inference(superposition, [status(thm), theory('equality')], [c_2, c_431])).
% 3.37/1.60  tff(c_14, plain, (![A_11, B_12]: (k5_xboole_0(A_11, k3_xboole_0(A_11, B_12))=k4_xboole_0(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.37/1.60  tff(c_1236, plain, (![A_128, A_129]: (k5_xboole_0(k1_tarski(A_128), k1_tarski(A_128))=k4_xboole_0(k1_tarski(A_128), A_129) | ~r2_hidden(A_128, A_129))), inference(superposition, [status(thm), theory('equality')], [c_1196, c_14])).
% 3.37/1.60  tff(c_1458, plain, (![A_135, A_136]: (k4_xboole_0(k1_tarski(A_135), A_136)=k1_xboole_0 | ~r2_hidden(A_135, A_136))), inference(demodulation, [status(thm), theory('equality')], [c_815, c_1236])).
% 3.37/1.60  tff(c_40, plain, (k4_xboole_0(k1_tarski('#skF_1'), '#skF_2')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.37/1.60  tff(c_1484, plain, (~r2_hidden('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_1458, c_40])).
% 3.37/1.60  tff(c_1504, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_277, c_1484])).
% 3.37/1.60  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.37/1.60  
% 3.37/1.60  Inference rules
% 3.37/1.60  ----------------------
% 3.37/1.60  #Ref     : 0
% 3.37/1.60  #Sup     : 357
% 3.37/1.60  #Fact    : 0
% 3.37/1.60  #Define  : 0
% 3.37/1.60  #Split   : 0
% 3.37/1.60  #Chain   : 0
% 3.37/1.60  #Close   : 0
% 3.37/1.60  
% 3.37/1.60  Ordering : KBO
% 3.37/1.60  
% 3.37/1.60  Simplification rules
% 3.37/1.60  ----------------------
% 3.37/1.60  #Subsume      : 11
% 3.37/1.60  #Demod        : 232
% 3.37/1.60  #Tautology    : 209
% 3.37/1.60  #SimpNegUnit  : 0
% 3.37/1.60  #BackRed      : 10
% 3.37/1.60  
% 3.37/1.60  #Partial instantiations: 0
% 3.37/1.60  #Strategies tried      : 1
% 3.37/1.60  
% 3.37/1.60  Timing (in seconds)
% 3.37/1.60  ----------------------
% 3.37/1.61  Preprocessing        : 0.34
% 3.37/1.61  Parsing              : 0.19
% 3.37/1.61  CNF conversion       : 0.02
% 3.37/1.61  Main loop            : 0.44
% 3.37/1.61  Inferencing          : 0.15
% 3.37/1.61  Reduction            : 0.18
% 3.37/1.61  Demodulation         : 0.14
% 3.37/1.61  BG Simplification    : 0.03
% 3.37/1.61  Subsumption          : 0.06
% 3.37/1.61  Abstraction          : 0.03
% 3.37/1.61  MUC search           : 0.00
% 3.37/1.61  Cooper               : 0.00
% 3.37/1.61  Total                : 0.81
% 3.37/1.61  Index Insertion      : 0.00
% 3.37/1.61  Index Deletion       : 0.00
% 3.37/1.61  Index Matching       : 0.00
% 3.37/1.61  BG Taut test         : 0.00
%------------------------------------------------------------------------------
