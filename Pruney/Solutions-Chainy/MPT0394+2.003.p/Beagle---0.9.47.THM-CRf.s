%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:57:21 EST 2020

% Result     : Theorem 2.80s
% Output     : CNFRefutation 2.80s
% Verified   : 
% Statistics : Number of formulae       :   49 (  74 expanded)
%              Number of leaves         :   27 (  37 expanded)
%              Depth                    :   11
%              Number of atoms          :   51 (  87 expanded)
%              Number of equality atoms :   35 (  56 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_33,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_67,axiom,(
    ! [A,B] :
      ( k3_xboole_0(A,k1_tarski(B)) = k1_tarski(B)
     => r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l29_zfmisc_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_47,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_81,axiom,(
    ! [A] : k1_setfam_1(k1_tarski(A)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_setfam_1)).

tff(f_57,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_xboole_0(k1_tarski(A),k1_tarski(B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_enumset1)).

tff(f_79,axiom,(
    ! [A,B] :
      ~ ( A != k1_xboole_0
        & B != k1_xboole_0
        & k1_setfam_1(k2_xboole_0(A,B)) != k3_xboole_0(k1_setfam_1(A),k1_setfam_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_setfam_1)).

tff(f_84,negated_conjecture,(
    ~ ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_8,plain,(
    ! [A_5] : k3_xboole_0(A_5,A_5) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_348,plain,(
    ! [B_83,A_84] :
      ( r2_hidden(B_83,A_84)
      | k3_xboole_0(A_84,k1_tarski(B_83)) != k1_tarski(B_83) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_362,plain,(
    ! [B_85] : r2_hidden(B_85,k1_tarski(B_85)) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_348])).

tff(c_6,plain,(
    ! [A_3,B_4] :
      ( r1_xboole_0(A_3,B_4)
      | k3_xboole_0(A_3,B_4) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_205,plain,(
    ! [A_56,B_57,C_58] :
      ( ~ r1_xboole_0(A_56,B_57)
      | ~ r2_hidden(C_58,k3_xboole_0(A_56,B_57)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_221,plain,(
    ! [A_59,C_60] :
      ( ~ r1_xboole_0(A_59,A_59)
      | ~ r2_hidden(C_60,A_59) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_205])).

tff(c_227,plain,(
    ! [C_60,B_4] :
      ( ~ r2_hidden(C_60,B_4)
      | k3_xboole_0(B_4,B_4) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_6,c_221])).

tff(c_230,plain,(
    ! [C_60,B_4] :
      ( ~ r2_hidden(C_60,B_4)
      | k1_xboole_0 != B_4 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_227])).

tff(c_369,plain,(
    ! [B_85] : k1_tarski(B_85) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_362,c_230])).

tff(c_36,plain,(
    ! [A_32] : k1_setfam_1(k1_tarski(A_32)) = A_32 ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_22,plain,(
    ! [A_18,B_19] : k2_xboole_0(k1_tarski(A_18),k1_tarski(B_19)) = k2_tarski(A_18,B_19) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_506,plain,(
    ! [A_101,B_102] :
      ( k3_xboole_0(k1_setfam_1(A_101),k1_setfam_1(B_102)) = k1_setfam_1(k2_xboole_0(A_101,B_102))
      | k1_xboole_0 = B_102
      | k1_xboole_0 = A_101 ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_547,plain,(
    ! [A_101,A_32] :
      ( k1_setfam_1(k2_xboole_0(A_101,k1_tarski(A_32))) = k3_xboole_0(k1_setfam_1(A_101),A_32)
      | k1_tarski(A_32) = k1_xboole_0
      | k1_xboole_0 = A_101 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_506])).

tff(c_1110,plain,(
    ! [A_147,A_148] :
      ( k1_setfam_1(k2_xboole_0(A_147,k1_tarski(A_148))) = k3_xboole_0(k1_setfam_1(A_147),A_148)
      | k1_xboole_0 = A_147 ) ),
    inference(negUnitSimplification,[status(thm)],[c_369,c_547])).

tff(c_1133,plain,(
    ! [A_18,B_19] :
      ( k3_xboole_0(k1_setfam_1(k1_tarski(A_18)),B_19) = k1_setfam_1(k2_tarski(A_18,B_19))
      | k1_tarski(A_18) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_1110])).

tff(c_1144,plain,(
    ! [A_18,B_19] :
      ( k1_setfam_1(k2_tarski(A_18,B_19)) = k3_xboole_0(A_18,B_19)
      | k1_tarski(A_18) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_1133])).

tff(c_1145,plain,(
    ! [A_18,B_19] : k1_setfam_1(k2_tarski(A_18,B_19)) = k3_xboole_0(A_18,B_19) ),
    inference(negUnitSimplification,[status(thm)],[c_369,c_1144])).

tff(c_38,plain,(
    k1_setfam_1(k2_tarski('#skF_2','#skF_3')) != k3_xboole_0('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_39,plain,(
    k1_setfam_1(k2_tarski('#skF_2','#skF_3')) != k3_xboole_0('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_38])).

tff(c_1148,plain,(
    k3_xboole_0('#skF_2','#skF_3') != k3_xboole_0('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1145,c_39])).

tff(c_1151,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_1148])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n016.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 18:38:04 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.19/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.80/1.42  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.80/1.43  
% 2.80/1.43  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.80/1.43  %$ r2_hidden > r1_xboole_0 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.80/1.43  
% 2.80/1.43  %Foreground sorts:
% 2.80/1.43  
% 2.80/1.43  
% 2.80/1.43  %Background operators:
% 2.80/1.43  
% 2.80/1.43  
% 2.80/1.43  %Foreground operators:
% 2.80/1.43  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.80/1.43  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.80/1.43  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.80/1.43  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.80/1.43  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.80/1.43  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.80/1.43  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.80/1.43  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.80/1.43  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.80/1.43  tff('#skF_2', type, '#skF_2': $i).
% 2.80/1.43  tff('#skF_3', type, '#skF_3': $i).
% 2.80/1.43  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.80/1.43  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.80/1.43  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.80/1.43  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.80/1.43  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.80/1.43  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.80/1.43  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.80/1.43  
% 2.80/1.44  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 2.80/1.44  tff(f_33, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 2.80/1.44  tff(f_67, axiom, (![A, B]: ((k3_xboole_0(A, k1_tarski(B)) = k1_tarski(B)) => r2_hidden(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l29_zfmisc_1)).
% 2.80/1.44  tff(f_31, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 2.80/1.44  tff(f_47, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 2.80/1.44  tff(f_81, axiom, (![A]: (k1_setfam_1(k1_tarski(A)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_setfam_1)).
% 2.80/1.44  tff(f_57, axiom, (![A, B]: (k2_tarski(A, B) = k2_xboole_0(k1_tarski(A), k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_enumset1)).
% 2.80/1.44  tff(f_79, axiom, (![A, B]: ~((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(k1_setfam_1(k2_xboole_0(A, B)) = k3_xboole_0(k1_setfam_1(A), k1_setfam_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_setfam_1)).
% 2.80/1.44  tff(f_84, negated_conjecture, ~(![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 2.80/1.44  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.80/1.44  tff(c_8, plain, (![A_5]: (k3_xboole_0(A_5, A_5)=A_5)), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.80/1.44  tff(c_348, plain, (![B_83, A_84]: (r2_hidden(B_83, A_84) | k3_xboole_0(A_84, k1_tarski(B_83))!=k1_tarski(B_83))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.80/1.44  tff(c_362, plain, (![B_85]: (r2_hidden(B_85, k1_tarski(B_85)))), inference(superposition, [status(thm), theory('equality')], [c_8, c_348])).
% 2.80/1.44  tff(c_6, plain, (![A_3, B_4]: (r1_xboole_0(A_3, B_4) | k3_xboole_0(A_3, B_4)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.80/1.44  tff(c_205, plain, (![A_56, B_57, C_58]: (~r1_xboole_0(A_56, B_57) | ~r2_hidden(C_58, k3_xboole_0(A_56, B_57)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.80/1.44  tff(c_221, plain, (![A_59, C_60]: (~r1_xboole_0(A_59, A_59) | ~r2_hidden(C_60, A_59))), inference(superposition, [status(thm), theory('equality')], [c_8, c_205])).
% 2.80/1.44  tff(c_227, plain, (![C_60, B_4]: (~r2_hidden(C_60, B_4) | k3_xboole_0(B_4, B_4)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_221])).
% 2.80/1.44  tff(c_230, plain, (![C_60, B_4]: (~r2_hidden(C_60, B_4) | k1_xboole_0!=B_4)), inference(demodulation, [status(thm), theory('equality')], [c_8, c_227])).
% 2.80/1.44  tff(c_369, plain, (![B_85]: (k1_tarski(B_85)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_362, c_230])).
% 2.80/1.44  tff(c_36, plain, (![A_32]: (k1_setfam_1(k1_tarski(A_32))=A_32)), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.80/1.44  tff(c_22, plain, (![A_18, B_19]: (k2_xboole_0(k1_tarski(A_18), k1_tarski(B_19))=k2_tarski(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.80/1.44  tff(c_506, plain, (![A_101, B_102]: (k3_xboole_0(k1_setfam_1(A_101), k1_setfam_1(B_102))=k1_setfam_1(k2_xboole_0(A_101, B_102)) | k1_xboole_0=B_102 | k1_xboole_0=A_101)), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.80/1.44  tff(c_547, plain, (![A_101, A_32]: (k1_setfam_1(k2_xboole_0(A_101, k1_tarski(A_32)))=k3_xboole_0(k1_setfam_1(A_101), A_32) | k1_tarski(A_32)=k1_xboole_0 | k1_xboole_0=A_101)), inference(superposition, [status(thm), theory('equality')], [c_36, c_506])).
% 2.80/1.44  tff(c_1110, plain, (![A_147, A_148]: (k1_setfam_1(k2_xboole_0(A_147, k1_tarski(A_148)))=k3_xboole_0(k1_setfam_1(A_147), A_148) | k1_xboole_0=A_147)), inference(negUnitSimplification, [status(thm)], [c_369, c_547])).
% 2.80/1.44  tff(c_1133, plain, (![A_18, B_19]: (k3_xboole_0(k1_setfam_1(k1_tarski(A_18)), B_19)=k1_setfam_1(k2_tarski(A_18, B_19)) | k1_tarski(A_18)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_22, c_1110])).
% 2.80/1.44  tff(c_1144, plain, (![A_18, B_19]: (k1_setfam_1(k2_tarski(A_18, B_19))=k3_xboole_0(A_18, B_19) | k1_tarski(A_18)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_36, c_1133])).
% 2.80/1.44  tff(c_1145, plain, (![A_18, B_19]: (k1_setfam_1(k2_tarski(A_18, B_19))=k3_xboole_0(A_18, B_19))), inference(negUnitSimplification, [status(thm)], [c_369, c_1144])).
% 2.80/1.44  tff(c_38, plain, (k1_setfam_1(k2_tarski('#skF_2', '#skF_3'))!=k3_xboole_0('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.80/1.44  tff(c_39, plain, (k1_setfam_1(k2_tarski('#skF_2', '#skF_3'))!=k3_xboole_0('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_38])).
% 2.80/1.44  tff(c_1148, plain, (k3_xboole_0('#skF_2', '#skF_3')!=k3_xboole_0('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1145, c_39])).
% 2.80/1.44  tff(c_1151, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2, c_1148])).
% 2.80/1.44  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.80/1.44  
% 2.80/1.44  Inference rules
% 2.80/1.44  ----------------------
% 2.80/1.44  #Ref     : 0
% 2.80/1.44  #Sup     : 277
% 2.80/1.44  #Fact    : 0
% 2.80/1.44  #Define  : 0
% 2.80/1.44  #Split   : 0
% 2.80/1.44  #Chain   : 0
% 2.80/1.44  #Close   : 0
% 2.80/1.44  
% 2.80/1.44  Ordering : KBO
% 2.80/1.44  
% 2.80/1.44  Simplification rules
% 2.80/1.44  ----------------------
% 2.80/1.44  #Subsume      : 74
% 2.80/1.44  #Demod        : 98
% 2.80/1.44  #Tautology    : 88
% 2.80/1.44  #SimpNegUnit  : 8
% 2.80/1.44  #BackRed      : 1
% 2.80/1.44  
% 2.80/1.44  #Partial instantiations: 0
% 2.80/1.44  #Strategies tried      : 1
% 2.80/1.44  
% 2.80/1.44  Timing (in seconds)
% 2.80/1.44  ----------------------
% 2.80/1.44  Preprocessing        : 0.30
% 2.80/1.44  Parsing              : 0.17
% 2.80/1.44  CNF conversion       : 0.02
% 2.80/1.44  Main loop            : 0.39
% 2.80/1.44  Inferencing          : 0.15
% 2.80/1.44  Reduction            : 0.13
% 2.80/1.44  Demodulation         : 0.10
% 2.80/1.44  BG Simplification    : 0.02
% 2.80/1.44  Subsumption          : 0.07
% 2.80/1.44  Abstraction          : 0.02
% 2.80/1.44  MUC search           : 0.00
% 2.80/1.44  Cooper               : 0.00
% 2.80/1.44  Total                : 0.72
% 2.80/1.44  Index Insertion      : 0.00
% 2.80/1.44  Index Deletion       : 0.00
% 2.80/1.44  Index Matching       : 0.00
% 2.80/1.44  BG Taut test         : 0.00
%------------------------------------------------------------------------------
