%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:57:21 EST 2020

% Result     : Theorem 3.61s
% Output     : CNFRefutation 3.89s
% Verified   : 
% Statistics : Number of formulae       :   53 (  89 expanded)
%              Number of leaves         :   26 (  40 expanded)
%              Depth                    :   12
%              Number of atoms          :   57 ( 103 expanded)
%              Number of equality atoms :   38 (  62 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

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

tff(f_53,axiom,(
    ! [A] : k4_xboole_0(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).

tff(f_63,axiom,(
    ! [A,B] : r1_xboole_0(k3_xboole_0(A,B),k4_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t89_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_45,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_51,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_79,axiom,(
    ! [A,B] :
      ( k3_xboole_0(A,k1_tarski(B)) = k1_tarski(B)
     => r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_zfmisc_1)).

tff(f_91,axiom,(
    ! [A] : k1_setfam_1(k1_tarski(A)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_setfam_1)).

tff(f_65,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_xboole_0(k1_tarski(A),k1_tarski(B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_enumset1)).

tff(f_89,axiom,(
    ! [A,B] :
      ~ ( A != k1_xboole_0
        & B != k1_xboole_0
        & k1_setfam_1(k2_xboole_0(A,B)) != k3_xboole_0(k1_setfam_1(A),k1_setfam_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_setfam_1)).

tff(f_94,negated_conjecture,(
    ~ ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_18,plain,(
    ! [A_15] : k4_xboole_0(k1_xboole_0,A_15) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_153,plain,(
    ! [A_49,B_50] : r1_xboole_0(k3_xboole_0(A_49,B_50),k4_xboole_0(A_49,B_50)) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_165,plain,(
    ! [A_15] : r1_xboole_0(k3_xboole_0(k1_xboole_0,A_15),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_153])).

tff(c_167,plain,(
    ! [A_51] : r1_xboole_0(k3_xboole_0(k1_xboole_0,A_51),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_153])).

tff(c_4,plain,(
    ! [A_3,B_4] :
      ( k3_xboole_0(A_3,B_4) = k1_xboole_0
      | ~ r1_xboole_0(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_179,plain,(
    ! [A_51] : k3_xboole_0(k3_xboole_0(k1_xboole_0,A_51),k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_167,c_4])).

tff(c_249,plain,(
    ! [A_56,B_57,C_58] :
      ( ~ r1_xboole_0(A_56,B_57)
      | ~ r2_hidden(C_58,k3_xboole_0(A_56,B_57)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_252,plain,(
    ! [A_51,C_58] :
      ( ~ r1_xboole_0(k3_xboole_0(k1_xboole_0,A_51),k1_xboole_0)
      | ~ r2_hidden(C_58,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_179,c_249])).

tff(c_260,plain,(
    ! [C_58] : ~ r2_hidden(C_58,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_165,c_252])).

tff(c_406,plain,(
    ! [A_62,B_63] : k4_xboole_0(A_62,k4_xboole_0(A_62,B_63)) = k3_xboole_0(A_62,B_63) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_419,plain,(
    ! [B_63] : k3_xboole_0(k1_xboole_0,B_63) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_406,c_18])).

tff(c_572,plain,(
    ! [B_69,A_70] :
      ( r2_hidden(B_69,A_70)
      | k3_xboole_0(A_70,k1_tarski(B_69)) != k1_tarski(B_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_576,plain,(
    ! [B_69] :
      ( r2_hidden(B_69,k1_xboole_0)
      | k1_tarski(B_69) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_419,c_572])).

tff(c_585,plain,(
    ! [B_69] : k1_tarski(B_69) != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_260,c_576])).

tff(c_36,plain,(
    ! [A_32] : k1_setfam_1(k1_tarski(A_32)) = A_32 ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_24,plain,(
    ! [A_22,B_23] : k2_xboole_0(k1_tarski(A_22),k1_tarski(B_23)) = k2_tarski(A_22,B_23) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_625,plain,(
    ! [A_76,B_77] :
      ( k3_xboole_0(k1_setfam_1(A_76),k1_setfam_1(B_77)) = k1_setfam_1(k2_xboole_0(A_76,B_77))
      | k1_xboole_0 = B_77
      | k1_xboole_0 = A_76 ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_664,plain,(
    ! [A_76,A_32] :
      ( k1_setfam_1(k2_xboole_0(A_76,k1_tarski(A_32))) = k3_xboole_0(k1_setfam_1(A_76),A_32)
      | k1_tarski(A_32) = k1_xboole_0
      | k1_xboole_0 = A_76 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_625])).

tff(c_3162,plain,(
    ! [A_169,A_170] :
      ( k1_setfam_1(k2_xboole_0(A_169,k1_tarski(A_170))) = k3_xboole_0(k1_setfam_1(A_169),A_170)
      | k1_xboole_0 = A_169 ) ),
    inference(negUnitSimplification,[status(thm)],[c_585,c_664])).

tff(c_3185,plain,(
    ! [A_22,B_23] :
      ( k3_xboole_0(k1_setfam_1(k1_tarski(A_22)),B_23) = k1_setfam_1(k2_tarski(A_22,B_23))
      | k1_tarski(A_22) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_3162])).

tff(c_3189,plain,(
    ! [A_22,B_23] :
      ( k1_setfam_1(k2_tarski(A_22,B_23)) = k3_xboole_0(A_22,B_23)
      | k1_tarski(A_22) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_3185])).

tff(c_3190,plain,(
    ! [A_22,B_23] : k1_setfam_1(k2_tarski(A_22,B_23)) = k3_xboole_0(A_22,B_23) ),
    inference(negUnitSimplification,[status(thm)],[c_585,c_3189])).

tff(c_38,plain,(
    k1_setfam_1(k2_tarski('#skF_2','#skF_3')) != k3_xboole_0('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_39,plain,(
    k1_setfam_1(k2_tarski('#skF_2','#skF_3')) != k3_xboole_0('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_38])).

tff(c_3191,plain,(
    k3_xboole_0('#skF_2','#skF_3') != k3_xboole_0('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3190,c_39])).

tff(c_3194,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_3191])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:53:30 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.61/1.63  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.61/1.63  
% 3.61/1.63  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.61/1.64  %$ r2_hidden > r1_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 3.61/1.64  
% 3.61/1.64  %Foreground sorts:
% 3.61/1.64  
% 3.61/1.64  
% 3.61/1.64  %Background operators:
% 3.61/1.64  
% 3.61/1.64  
% 3.61/1.64  %Foreground operators:
% 3.61/1.64  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.61/1.64  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.61/1.64  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.61/1.64  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.61/1.64  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.61/1.64  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.61/1.64  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.61/1.64  tff('#skF_2', type, '#skF_2': $i).
% 3.61/1.64  tff('#skF_3', type, '#skF_3': $i).
% 3.61/1.64  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.61/1.64  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.61/1.64  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.61/1.64  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.61/1.64  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.61/1.64  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 3.61/1.64  
% 3.89/1.65  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 3.89/1.65  tff(f_53, axiom, (![A]: (k4_xboole_0(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_boole)).
% 3.89/1.65  tff(f_63, axiom, (![A, B]: r1_xboole_0(k3_xboole_0(A, B), k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t89_xboole_1)).
% 3.89/1.65  tff(f_31, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 3.89/1.65  tff(f_45, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 3.89/1.65  tff(f_51, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 3.89/1.65  tff(f_79, axiom, (![A, B]: ((k3_xboole_0(A, k1_tarski(B)) = k1_tarski(B)) => r2_hidden(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t51_zfmisc_1)).
% 3.89/1.65  tff(f_91, axiom, (![A]: (k1_setfam_1(k1_tarski(A)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_setfam_1)).
% 3.89/1.65  tff(f_65, axiom, (![A, B]: (k2_tarski(A, B) = k2_xboole_0(k1_tarski(A), k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_enumset1)).
% 3.89/1.65  tff(f_89, axiom, (![A, B]: ~((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(k1_setfam_1(k2_xboole_0(A, B)) = k3_xboole_0(k1_setfam_1(A), k1_setfam_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_setfam_1)).
% 3.89/1.65  tff(f_94, negated_conjecture, ~(![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 3.89/1.65  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.89/1.65  tff(c_18, plain, (![A_15]: (k4_xboole_0(k1_xboole_0, A_15)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.89/1.65  tff(c_153, plain, (![A_49, B_50]: (r1_xboole_0(k3_xboole_0(A_49, B_50), k4_xboole_0(A_49, B_50)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.89/1.65  tff(c_165, plain, (![A_15]: (r1_xboole_0(k3_xboole_0(k1_xboole_0, A_15), k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_18, c_153])).
% 3.89/1.65  tff(c_167, plain, (![A_51]: (r1_xboole_0(k3_xboole_0(k1_xboole_0, A_51), k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_18, c_153])).
% 3.89/1.65  tff(c_4, plain, (![A_3, B_4]: (k3_xboole_0(A_3, B_4)=k1_xboole_0 | ~r1_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.89/1.65  tff(c_179, plain, (![A_51]: (k3_xboole_0(k3_xboole_0(k1_xboole_0, A_51), k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_167, c_4])).
% 3.89/1.65  tff(c_249, plain, (![A_56, B_57, C_58]: (~r1_xboole_0(A_56, B_57) | ~r2_hidden(C_58, k3_xboole_0(A_56, B_57)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.89/1.65  tff(c_252, plain, (![A_51, C_58]: (~r1_xboole_0(k3_xboole_0(k1_xboole_0, A_51), k1_xboole_0) | ~r2_hidden(C_58, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_179, c_249])).
% 3.89/1.65  tff(c_260, plain, (![C_58]: (~r2_hidden(C_58, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_165, c_252])).
% 3.89/1.65  tff(c_406, plain, (![A_62, B_63]: (k4_xboole_0(A_62, k4_xboole_0(A_62, B_63))=k3_xboole_0(A_62, B_63))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.89/1.65  tff(c_419, plain, (![B_63]: (k3_xboole_0(k1_xboole_0, B_63)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_406, c_18])).
% 3.89/1.65  tff(c_572, plain, (![B_69, A_70]: (r2_hidden(B_69, A_70) | k3_xboole_0(A_70, k1_tarski(B_69))!=k1_tarski(B_69))), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.89/1.65  tff(c_576, plain, (![B_69]: (r2_hidden(B_69, k1_xboole_0) | k1_tarski(B_69)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_419, c_572])).
% 3.89/1.65  tff(c_585, plain, (![B_69]: (k1_tarski(B_69)!=k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_260, c_576])).
% 3.89/1.65  tff(c_36, plain, (![A_32]: (k1_setfam_1(k1_tarski(A_32))=A_32)), inference(cnfTransformation, [status(thm)], [f_91])).
% 3.89/1.65  tff(c_24, plain, (![A_22, B_23]: (k2_xboole_0(k1_tarski(A_22), k1_tarski(B_23))=k2_tarski(A_22, B_23))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.89/1.65  tff(c_625, plain, (![A_76, B_77]: (k3_xboole_0(k1_setfam_1(A_76), k1_setfam_1(B_77))=k1_setfam_1(k2_xboole_0(A_76, B_77)) | k1_xboole_0=B_77 | k1_xboole_0=A_76)), inference(cnfTransformation, [status(thm)], [f_89])).
% 3.89/1.65  tff(c_664, plain, (![A_76, A_32]: (k1_setfam_1(k2_xboole_0(A_76, k1_tarski(A_32)))=k3_xboole_0(k1_setfam_1(A_76), A_32) | k1_tarski(A_32)=k1_xboole_0 | k1_xboole_0=A_76)), inference(superposition, [status(thm), theory('equality')], [c_36, c_625])).
% 3.89/1.65  tff(c_3162, plain, (![A_169, A_170]: (k1_setfam_1(k2_xboole_0(A_169, k1_tarski(A_170)))=k3_xboole_0(k1_setfam_1(A_169), A_170) | k1_xboole_0=A_169)), inference(negUnitSimplification, [status(thm)], [c_585, c_664])).
% 3.89/1.65  tff(c_3185, plain, (![A_22, B_23]: (k3_xboole_0(k1_setfam_1(k1_tarski(A_22)), B_23)=k1_setfam_1(k2_tarski(A_22, B_23)) | k1_tarski(A_22)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_24, c_3162])).
% 3.89/1.65  tff(c_3189, plain, (![A_22, B_23]: (k1_setfam_1(k2_tarski(A_22, B_23))=k3_xboole_0(A_22, B_23) | k1_tarski(A_22)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_36, c_3185])).
% 3.89/1.65  tff(c_3190, plain, (![A_22, B_23]: (k1_setfam_1(k2_tarski(A_22, B_23))=k3_xboole_0(A_22, B_23))), inference(negUnitSimplification, [status(thm)], [c_585, c_3189])).
% 3.89/1.65  tff(c_38, plain, (k1_setfam_1(k2_tarski('#skF_2', '#skF_3'))!=k3_xboole_0('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_94])).
% 3.89/1.65  tff(c_39, plain, (k1_setfam_1(k2_tarski('#skF_2', '#skF_3'))!=k3_xboole_0('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_38])).
% 3.89/1.65  tff(c_3191, plain, (k3_xboole_0('#skF_2', '#skF_3')!=k3_xboole_0('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_3190, c_39])).
% 3.89/1.65  tff(c_3194, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2, c_3191])).
% 3.89/1.65  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.89/1.65  
% 3.89/1.65  Inference rules
% 3.89/1.65  ----------------------
% 3.89/1.65  #Ref     : 5
% 3.89/1.65  #Sup     : 806
% 3.89/1.65  #Fact    : 0
% 3.89/1.65  #Define  : 0
% 3.89/1.65  #Split   : 0
% 3.89/1.65  #Chain   : 0
% 3.89/1.65  #Close   : 0
% 3.89/1.65  
% 3.89/1.65  Ordering : KBO
% 3.89/1.65  
% 3.89/1.65  Simplification rules
% 3.89/1.65  ----------------------
% 3.89/1.65  #Subsume      : 167
% 3.89/1.65  #Demod        : 437
% 3.89/1.65  #Tautology    : 467
% 3.89/1.65  #SimpNegUnit  : 28
% 3.89/1.65  #BackRed      : 3
% 3.89/1.65  
% 3.89/1.65  #Partial instantiations: 0
% 3.89/1.65  #Strategies tried      : 1
% 3.89/1.65  
% 3.89/1.65  Timing (in seconds)
% 3.89/1.65  ----------------------
% 3.89/1.65  Preprocessing        : 0.29
% 3.89/1.65  Parsing              : 0.16
% 3.89/1.65  CNF conversion       : 0.02
% 3.89/1.65  Main loop            : 0.59
% 3.89/1.65  Inferencing          : 0.19
% 3.89/1.65  Reduction            : 0.25
% 3.89/1.65  Demodulation         : 0.20
% 3.89/1.65  BG Simplification    : 0.03
% 3.89/1.65  Subsumption          : 0.09
% 3.89/1.65  Abstraction          : 0.03
% 3.89/1.65  MUC search           : 0.00
% 3.89/1.65  Cooper               : 0.00
% 3.89/1.65  Total                : 0.90
% 3.89/1.65  Index Insertion      : 0.00
% 3.89/1.65  Index Deletion       : 0.00
% 3.89/1.65  Index Matching       : 0.00
% 3.89/1.65  BG Taut test         : 0.00
%------------------------------------------------------------------------------
