%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:53:08 EST 2020

% Result     : Theorem 2.24s
% Output     : CNFRefutation 2.24s
% Verified   : 
% Statistics : Number of formulae       :   59 ( 128 expanded)
%              Number of leaves         :   25 (  53 expanded)
%              Depth                    :   14
%              Number of atoms          :   54 ( 124 expanded)
%              Number of equality atoms :   40 ( 110 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k2_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1

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

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

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

tff(f_33,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_35,axiom,(
    ! [A] : k4_xboole_0(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_31,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

tff(f_41,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_54,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => k3_xboole_0(B,k1_tarski(A)) = k1_tarski(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l31_zfmisc_1)).

tff(f_59,negated_conjecture,(
    ~ ! [A,B] :
        ( k4_xboole_0(k1_tarski(A),B) = k1_xboole_0
        | k4_xboole_0(k1_tarski(A),B) = k1_tarski(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_zfmisc_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( ~ r2_hidden(A,B)
     => r1_xboole_0(k1_tarski(A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l27_zfmisc_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

tff(c_98,plain,(
    ! [A_31,B_32] : k4_xboole_0(A_31,k4_xboole_0(A_31,B_32)) = k3_xboole_0(A_31,B_32) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_10,plain,(
    ! [A_8] : k4_xboole_0(k1_xboole_0,A_8) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_125,plain,(
    ! [B_33] : k3_xboole_0(k1_xboole_0,B_33) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_98,c_10])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_130,plain,(
    ! [B_33] : k3_xboole_0(B_33,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_125,c_2])).

tff(c_6,plain,(
    ! [A_5] : k2_xboole_0(A_5,k1_xboole_0) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_193,plain,(
    ! [A_37,B_38] : k5_xboole_0(A_37,k4_xboole_0(B_38,A_37)) = k2_xboole_0(A_37,B_38) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_205,plain,(
    ! [A_8] : k5_xboole_0(A_8,k1_xboole_0) = k2_xboole_0(A_8,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_193])).

tff(c_208,plain,(
    ! [A_8] : k5_xboole_0(A_8,k1_xboole_0) = A_8 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_205])).

tff(c_209,plain,(
    ! [A_39,B_40] : k5_xboole_0(A_39,k3_xboole_0(A_39,B_40)) = k4_xboole_0(A_39,B_40) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_218,plain,(
    ! [B_33] : k5_xboole_0(B_33,k1_xboole_0) = k4_xboole_0(B_33,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_130,c_209])).

tff(c_242,plain,(
    ! [B_42] : k4_xboole_0(B_42,k1_xboole_0) = B_42 ),
    inference(demodulation,[status(thm),theory(equality)],[c_208,c_218])).

tff(c_8,plain,(
    ! [A_6,B_7] : k4_xboole_0(A_6,k4_xboole_0(A_6,B_7)) = k3_xboole_0(A_6,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_251,plain,(
    ! [B_42] : k4_xboole_0(B_42,B_42) = k3_xboole_0(B_42,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_242,c_8])).

tff(c_264,plain,(
    ! [B_42] : k4_xboole_0(B_42,B_42) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_130,c_251])).

tff(c_241,plain,(
    ! [B_33] : k4_xboole_0(B_33,k1_xboole_0) = B_33 ),
    inference(demodulation,[status(thm),theory(equality)],[c_208,c_218])).

tff(c_268,plain,(
    ! [B_43] : k4_xboole_0(B_43,B_43) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_130,c_251])).

tff(c_280,plain,(
    ! [B_43] : k4_xboole_0(B_43,k1_xboole_0) = k3_xboole_0(B_43,B_43) ),
    inference(superposition,[status(thm),theory(equality)],[c_268,c_8])).

tff(c_354,plain,(
    ! [B_47] : k3_xboole_0(B_47,B_47) = B_47 ),
    inference(demodulation,[status(thm),theory(equality)],[c_241,c_280])).

tff(c_4,plain,(
    ! [A_3,B_4] : k5_xboole_0(A_3,k3_xboole_0(A_3,B_4)) = k4_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_364,plain,(
    ! [B_47] : k5_xboole_0(B_47,B_47) = k4_xboole_0(B_47,B_47) ),
    inference(superposition,[status(thm),theory(equality)],[c_354,c_4])).

tff(c_390,plain,(
    ! [B_47] : k5_xboole_0(B_47,B_47) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_264,c_364])).

tff(c_24,plain,(
    ! [B_19,A_18] :
      ( k3_xboole_0(B_19,k1_tarski(A_18)) = k1_tarski(A_18)
      | ~ r2_hidden(A_18,B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_464,plain,(
    ! [A_51,B_52] : k5_xboole_0(A_51,k3_xboole_0(B_52,A_51)) = k4_xboole_0(A_51,B_52) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_209])).

tff(c_488,plain,(
    ! [A_18,B_19] :
      ( k5_xboole_0(k1_tarski(A_18),k1_tarski(A_18)) = k4_xboole_0(k1_tarski(A_18),B_19)
      | ~ r2_hidden(A_18,B_19) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_464])).

tff(c_518,plain,(
    ! [A_53,B_54] :
      ( k4_xboole_0(k1_tarski(A_53),B_54) = k1_xboole_0
      | ~ r2_hidden(A_53,B_54) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_390,c_488])).

tff(c_28,plain,(
    k4_xboole_0(k1_tarski('#skF_1'),'#skF_2') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_565,plain,(
    ~ r2_hidden('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_518,c_28])).

tff(c_93,plain,(
    ! [A_29,B_30] :
      ( r1_xboole_0(k1_tarski(A_29),B_30)
      | r2_hidden(A_29,B_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_12,plain,(
    ! [A_9,B_10] :
      ( k4_xboole_0(A_9,B_10) = A_9
      | ~ r1_xboole_0(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_643,plain,(
    ! [A_59,B_60] :
      ( k4_xboole_0(k1_tarski(A_59),B_60) = k1_tarski(A_59)
      | r2_hidden(A_59,B_60) ) ),
    inference(resolution,[status(thm)],[c_93,c_12])).

tff(c_26,plain,(
    k4_xboole_0(k1_tarski('#skF_1'),'#skF_2') != k1_tarski('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_670,plain,(
    r2_hidden('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_643,c_26])).

tff(c_698,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_565,c_670])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n003.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 12:09:27 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.24/1.25  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.24/1.26  
% 2.24/1.26  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.24/1.26  %$ r2_hidden > r1_xboole_0 > k2_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1
% 2.24/1.26  
% 2.24/1.26  %Foreground sorts:
% 2.24/1.26  
% 2.24/1.26  
% 2.24/1.26  %Background operators:
% 2.24/1.26  
% 2.24/1.26  
% 2.24/1.26  %Foreground operators:
% 2.24/1.26  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.24/1.26  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.24/1.26  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.24/1.26  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.24/1.26  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.24/1.26  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.24/1.26  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.24/1.26  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.24/1.26  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.24/1.26  tff('#skF_2', type, '#skF_2': $i).
% 2.24/1.26  tff('#skF_1', type, '#skF_1': $i).
% 2.24/1.26  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.24/1.26  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.24/1.26  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.24/1.26  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.24/1.26  
% 2.24/1.27  tff(f_33, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 2.24/1.27  tff(f_35, axiom, (![A]: (k4_xboole_0(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_boole)).
% 2.24/1.27  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 2.24/1.27  tff(f_31, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 2.24/1.27  tff(f_41, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_xboole_1)).
% 2.24/1.27  tff(f_29, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 2.24/1.27  tff(f_54, axiom, (![A, B]: (r2_hidden(A, B) => (k3_xboole_0(B, k1_tarski(A)) = k1_tarski(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l31_zfmisc_1)).
% 2.24/1.27  tff(f_59, negated_conjecture, ~(![A, B]: ((k4_xboole_0(k1_tarski(A), B) = k1_xboole_0) | (k4_xboole_0(k1_tarski(A), B) = k1_tarski(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_zfmisc_1)).
% 2.24/1.27  tff(f_50, axiom, (![A, B]: (~r2_hidden(A, B) => r1_xboole_0(k1_tarski(A), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 2.24/1.27  tff(f_39, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_xboole_1)).
% 2.24/1.27  tff(c_98, plain, (![A_31, B_32]: (k4_xboole_0(A_31, k4_xboole_0(A_31, B_32))=k3_xboole_0(A_31, B_32))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.24/1.27  tff(c_10, plain, (![A_8]: (k4_xboole_0(k1_xboole_0, A_8)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.24/1.27  tff(c_125, plain, (![B_33]: (k3_xboole_0(k1_xboole_0, B_33)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_98, c_10])).
% 2.24/1.27  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.24/1.27  tff(c_130, plain, (![B_33]: (k3_xboole_0(B_33, k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_125, c_2])).
% 2.24/1.27  tff(c_6, plain, (![A_5]: (k2_xboole_0(A_5, k1_xboole_0)=A_5)), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.24/1.27  tff(c_193, plain, (![A_37, B_38]: (k5_xboole_0(A_37, k4_xboole_0(B_38, A_37))=k2_xboole_0(A_37, B_38))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.24/1.27  tff(c_205, plain, (![A_8]: (k5_xboole_0(A_8, k1_xboole_0)=k2_xboole_0(A_8, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_10, c_193])).
% 2.24/1.27  tff(c_208, plain, (![A_8]: (k5_xboole_0(A_8, k1_xboole_0)=A_8)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_205])).
% 2.24/1.27  tff(c_209, plain, (![A_39, B_40]: (k5_xboole_0(A_39, k3_xboole_0(A_39, B_40))=k4_xboole_0(A_39, B_40))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.24/1.27  tff(c_218, plain, (![B_33]: (k5_xboole_0(B_33, k1_xboole_0)=k4_xboole_0(B_33, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_130, c_209])).
% 2.24/1.27  tff(c_242, plain, (![B_42]: (k4_xboole_0(B_42, k1_xboole_0)=B_42)), inference(demodulation, [status(thm), theory('equality')], [c_208, c_218])).
% 2.24/1.27  tff(c_8, plain, (![A_6, B_7]: (k4_xboole_0(A_6, k4_xboole_0(A_6, B_7))=k3_xboole_0(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.24/1.27  tff(c_251, plain, (![B_42]: (k4_xboole_0(B_42, B_42)=k3_xboole_0(B_42, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_242, c_8])).
% 2.24/1.27  tff(c_264, plain, (![B_42]: (k4_xboole_0(B_42, B_42)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_130, c_251])).
% 2.24/1.27  tff(c_241, plain, (![B_33]: (k4_xboole_0(B_33, k1_xboole_0)=B_33)), inference(demodulation, [status(thm), theory('equality')], [c_208, c_218])).
% 2.24/1.27  tff(c_268, plain, (![B_43]: (k4_xboole_0(B_43, B_43)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_130, c_251])).
% 2.24/1.27  tff(c_280, plain, (![B_43]: (k4_xboole_0(B_43, k1_xboole_0)=k3_xboole_0(B_43, B_43))), inference(superposition, [status(thm), theory('equality')], [c_268, c_8])).
% 2.24/1.27  tff(c_354, plain, (![B_47]: (k3_xboole_0(B_47, B_47)=B_47)), inference(demodulation, [status(thm), theory('equality')], [c_241, c_280])).
% 2.24/1.27  tff(c_4, plain, (![A_3, B_4]: (k5_xboole_0(A_3, k3_xboole_0(A_3, B_4))=k4_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.24/1.27  tff(c_364, plain, (![B_47]: (k5_xboole_0(B_47, B_47)=k4_xboole_0(B_47, B_47))), inference(superposition, [status(thm), theory('equality')], [c_354, c_4])).
% 2.24/1.27  tff(c_390, plain, (![B_47]: (k5_xboole_0(B_47, B_47)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_264, c_364])).
% 2.24/1.27  tff(c_24, plain, (![B_19, A_18]: (k3_xboole_0(B_19, k1_tarski(A_18))=k1_tarski(A_18) | ~r2_hidden(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.24/1.27  tff(c_464, plain, (![A_51, B_52]: (k5_xboole_0(A_51, k3_xboole_0(B_52, A_51))=k4_xboole_0(A_51, B_52))), inference(superposition, [status(thm), theory('equality')], [c_2, c_209])).
% 2.24/1.27  tff(c_488, plain, (![A_18, B_19]: (k5_xboole_0(k1_tarski(A_18), k1_tarski(A_18))=k4_xboole_0(k1_tarski(A_18), B_19) | ~r2_hidden(A_18, B_19))), inference(superposition, [status(thm), theory('equality')], [c_24, c_464])).
% 2.24/1.27  tff(c_518, plain, (![A_53, B_54]: (k4_xboole_0(k1_tarski(A_53), B_54)=k1_xboole_0 | ~r2_hidden(A_53, B_54))), inference(demodulation, [status(thm), theory('equality')], [c_390, c_488])).
% 2.24/1.27  tff(c_28, plain, (k4_xboole_0(k1_tarski('#skF_1'), '#skF_2')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.24/1.27  tff(c_565, plain, (~r2_hidden('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_518, c_28])).
% 2.24/1.27  tff(c_93, plain, (![A_29, B_30]: (r1_xboole_0(k1_tarski(A_29), B_30) | r2_hidden(A_29, B_30))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.24/1.27  tff(c_12, plain, (![A_9, B_10]: (k4_xboole_0(A_9, B_10)=A_9 | ~r1_xboole_0(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.24/1.27  tff(c_643, plain, (![A_59, B_60]: (k4_xboole_0(k1_tarski(A_59), B_60)=k1_tarski(A_59) | r2_hidden(A_59, B_60))), inference(resolution, [status(thm)], [c_93, c_12])).
% 2.24/1.27  tff(c_26, plain, (k4_xboole_0(k1_tarski('#skF_1'), '#skF_2')!=k1_tarski('#skF_1')), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.24/1.27  tff(c_670, plain, (r2_hidden('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_643, c_26])).
% 2.24/1.27  tff(c_698, plain, $false, inference(negUnitSimplification, [status(thm)], [c_565, c_670])).
% 2.24/1.27  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.24/1.27  
% 2.24/1.27  Inference rules
% 2.24/1.27  ----------------------
% 2.24/1.27  #Ref     : 0
% 2.24/1.27  #Sup     : 157
% 2.24/1.27  #Fact    : 0
% 2.24/1.27  #Define  : 0
% 2.24/1.27  #Split   : 0
% 2.24/1.27  #Chain   : 0
% 2.24/1.27  #Close   : 0
% 2.24/1.27  
% 2.24/1.27  Ordering : KBO
% 2.24/1.27  
% 2.24/1.27  Simplification rules
% 2.24/1.27  ----------------------
% 2.24/1.27  #Subsume      : 12
% 2.24/1.27  #Demod        : 54
% 2.24/1.27  #Tautology    : 106
% 2.24/1.27  #SimpNegUnit  : 1
% 2.24/1.27  #BackRed      : 0
% 2.24/1.27  
% 2.24/1.27  #Partial instantiations: 0
% 2.24/1.27  #Strategies tried      : 1
% 2.24/1.27  
% 2.24/1.27  Timing (in seconds)
% 2.24/1.27  ----------------------
% 2.24/1.27  Preprocessing        : 0.28
% 2.24/1.27  Parsing              : 0.15
% 2.24/1.27  CNF conversion       : 0.01
% 2.24/1.27  Main loop            : 0.23
% 2.24/1.27  Inferencing          : 0.09
% 2.24/1.28  Reduction            : 0.08
% 2.24/1.28  Demodulation         : 0.06
% 2.24/1.28  BG Simplification    : 0.01
% 2.24/1.28  Subsumption          : 0.03
% 2.24/1.28  Abstraction          : 0.02
% 2.24/1.28  MUC search           : 0.00
% 2.24/1.28  Cooper               : 0.00
% 2.24/1.28  Total                : 0.54
% 2.24/1.28  Index Insertion      : 0.00
% 2.24/1.28  Index Deletion       : 0.00
% 2.24/1.28  Index Matching       : 0.00
% 2.24/1.28  BG Taut test         : 0.00
%------------------------------------------------------------------------------
