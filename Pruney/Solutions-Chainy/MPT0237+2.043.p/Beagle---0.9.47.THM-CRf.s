%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:49:50 EST 2020

% Result     : Theorem 2.94s
% Output     : CNFRefutation 2.94s
% Verified   : 
% Statistics : Number of formulae       :   62 (  95 expanded)
%              Number of leaves         :   33 (  46 expanded)
%              Depth                    :    7
%              Number of atoms          :   54 (  99 expanded)
%              Number of equality atoms :   45 (  82 expanded)
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

tff(f_37,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_35,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_29,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_45,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_47,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_69,axiom,(
    ! [A,B] :
      ( A != B
     => k5_xboole_0(k1_tarski(A),k1_tarski(B)) = k2_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_zfmisc_1)).

tff(f_64,axiom,(
    ! [A,B] :
      ( A != B
     => r1_xboole_0(k1_tarski(A),k1_tarski(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_zfmisc_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_59,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_72,negated_conjecture,(
    ~ ! [A,B] : k3_tarski(k2_tarski(k1_tarski(A),k1_tarski(B))) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_zfmisc_1)).

tff(c_10,plain,(
    ! [A_8] : k4_xboole_0(A_8,k1_xboole_0) = A_8 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_8,plain,(
    ! [A_7] : r1_tarski(k1_xboole_0,A_7) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_92,plain,(
    ! [A_47,B_48] :
      ( k3_xboole_0(A_47,B_48) = A_47
      | ~ r1_tarski(A_47,B_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_109,plain,(
    ! [A_51] : k3_xboole_0(k1_xboole_0,A_51) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_8,c_92])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_114,plain,(
    ! [A_51] : k3_xboole_0(A_51,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_109,c_2])).

tff(c_243,plain,(
    ! [A_65,B_66] : k5_xboole_0(A_65,k3_xboole_0(A_65,B_66)) = k4_xboole_0(A_65,B_66) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_252,plain,(
    ! [A_51] : k5_xboole_0(A_51,k1_xboole_0) = k4_xboole_0(A_51,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_114,c_243])).

tff(c_264,plain,(
    ! [A_51] : k5_xboole_0(A_51,k1_xboole_0) = A_51 ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_252])).

tff(c_203,plain,(
    ! [A_62,B_63] : k4_xboole_0(A_62,k4_xboole_0(A_62,B_63)) = k3_xboole_0(A_62,B_63) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_218,plain,(
    ! [A_8] : k4_xboole_0(A_8,A_8) = k3_xboole_0(A_8,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_203])).

tff(c_221,plain,(
    ! [A_8] : k4_xboole_0(A_8,A_8) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_114,c_218])).

tff(c_364,plain,(
    ! [A_71,B_72] : k5_xboole_0(A_71,k4_xboole_0(B_72,A_71)) = k2_xboole_0(A_71,B_72) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_376,plain,(
    ! [A_8] : k5_xboole_0(A_8,k1_xboole_0) = k2_xboole_0(A_8,A_8) ),
    inference(superposition,[status(thm),theory(equality)],[c_221,c_364])).

tff(c_386,plain,(
    ! [A_8] : k2_xboole_0(A_8,A_8) = A_8 ),
    inference(demodulation,[status(thm),theory(equality)],[c_264,c_376])).

tff(c_20,plain,(
    ! [A_15] : k2_tarski(A_15,A_15) = k1_tarski(A_15) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_36,plain,(
    ! [A_40,B_41] :
      ( k5_xboole_0(k1_tarski(A_40),k1_tarski(B_41)) = k2_tarski(A_40,B_41)
      | B_41 = A_40 ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_34,plain,(
    ! [A_38,B_39] :
      ( r1_xboole_0(k1_tarski(A_38),k1_tarski(B_39))
      | B_39 = A_38 ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_194,plain,(
    ! [A_60,B_61] :
      ( k4_xboole_0(A_60,B_61) = A_60
      | ~ r1_xboole_0(A_60,B_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_555,plain,(
    ! [A_84,B_85] :
      ( k4_xboole_0(k1_tarski(A_84),k1_tarski(B_85)) = k1_tarski(A_84)
      | B_85 = A_84 ) ),
    inference(resolution,[status(thm)],[c_34,c_194])).

tff(c_18,plain,(
    ! [A_13,B_14] : k5_xboole_0(A_13,k4_xboole_0(B_14,A_13)) = k2_xboole_0(A_13,B_14) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_807,plain,(
    ! [B_103,A_104] :
      ( k5_xboole_0(k1_tarski(B_103),k1_tarski(A_104)) = k2_xboole_0(k1_tarski(B_103),k1_tarski(A_104))
      | B_103 = A_104 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_555,c_18])).

tff(c_1150,plain,(
    ! [A_121,B_122] :
      ( k2_xboole_0(k1_tarski(A_121),k1_tarski(B_122)) = k2_tarski(A_121,B_122)
      | B_122 = A_121
      | B_122 = A_121 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_807])).

tff(c_32,plain,(
    ! [A_36,B_37] : k3_tarski(k2_tarski(A_36,B_37)) = k2_xboole_0(A_36,B_37) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_38,plain,(
    k3_tarski(k2_tarski(k1_tarski('#skF_1'),k1_tarski('#skF_2'))) != k2_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_39,plain,(
    k2_xboole_0(k1_tarski('#skF_1'),k1_tarski('#skF_2')) != k2_tarski('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_38])).

tff(c_1171,plain,(
    '#skF_2' = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_1150,c_39])).

tff(c_1175,plain,(
    k2_xboole_0(k1_tarski('#skF_1'),k1_tarski('#skF_1')) != k2_tarski('#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1171,c_1171,c_39])).

tff(c_1178,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_386,c_20,c_1175])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:48:34 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.94/1.45  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.94/1.45  
% 2.94/1.45  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.94/1.46  %$ r1_xboole_0 > r1_tarski > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1
% 2.94/1.46  
% 2.94/1.46  %Foreground sorts:
% 2.94/1.46  
% 2.94/1.46  
% 2.94/1.46  %Background operators:
% 2.94/1.46  
% 2.94/1.46  
% 2.94/1.46  %Foreground operators:
% 2.94/1.46  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.94/1.46  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.94/1.46  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.94/1.46  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.94/1.46  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.94/1.46  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.94/1.46  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.94/1.46  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.94/1.46  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.94/1.46  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.94/1.46  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.94/1.46  tff('#skF_2', type, '#skF_2': $i).
% 2.94/1.46  tff('#skF_1', type, '#skF_1': $i).
% 2.94/1.46  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.94/1.46  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.94/1.46  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.94/1.46  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.94/1.46  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.94/1.46  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.94/1.46  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.94/1.46  
% 2.94/1.47  tff(f_37, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 2.94/1.47  tff(f_35, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.94/1.47  tff(f_33, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 2.94/1.47  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 2.94/1.47  tff(f_29, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 2.94/1.47  tff(f_39, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 2.94/1.47  tff(f_45, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_xboole_1)).
% 2.94/1.47  tff(f_47, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 2.94/1.47  tff(f_69, axiom, (![A, B]: (~(A = B) => (k5_xboole_0(k1_tarski(A), k1_tarski(B)) = k2_tarski(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_zfmisc_1)).
% 2.94/1.47  tff(f_64, axiom, (![A, B]: (~(A = B) => r1_xboole_0(k1_tarski(A), k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_zfmisc_1)).
% 2.94/1.47  tff(f_43, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_xboole_1)).
% 2.94/1.47  tff(f_59, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 2.94/1.47  tff(f_72, negated_conjecture, ~(![A, B]: (k3_tarski(k2_tarski(k1_tarski(A), k1_tarski(B))) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t32_zfmisc_1)).
% 2.94/1.47  tff(c_10, plain, (![A_8]: (k4_xboole_0(A_8, k1_xboole_0)=A_8)), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.94/1.47  tff(c_8, plain, (![A_7]: (r1_tarski(k1_xboole_0, A_7))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.94/1.47  tff(c_92, plain, (![A_47, B_48]: (k3_xboole_0(A_47, B_48)=A_47 | ~r1_tarski(A_47, B_48))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.94/1.47  tff(c_109, plain, (![A_51]: (k3_xboole_0(k1_xboole_0, A_51)=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_92])).
% 2.94/1.47  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.94/1.47  tff(c_114, plain, (![A_51]: (k3_xboole_0(A_51, k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_109, c_2])).
% 2.94/1.47  tff(c_243, plain, (![A_65, B_66]: (k5_xboole_0(A_65, k3_xboole_0(A_65, B_66))=k4_xboole_0(A_65, B_66))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.94/1.47  tff(c_252, plain, (![A_51]: (k5_xboole_0(A_51, k1_xboole_0)=k4_xboole_0(A_51, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_114, c_243])).
% 2.94/1.47  tff(c_264, plain, (![A_51]: (k5_xboole_0(A_51, k1_xboole_0)=A_51)), inference(demodulation, [status(thm), theory('equality')], [c_10, c_252])).
% 2.94/1.47  tff(c_203, plain, (![A_62, B_63]: (k4_xboole_0(A_62, k4_xboole_0(A_62, B_63))=k3_xboole_0(A_62, B_63))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.94/1.47  tff(c_218, plain, (![A_8]: (k4_xboole_0(A_8, A_8)=k3_xboole_0(A_8, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_10, c_203])).
% 2.94/1.47  tff(c_221, plain, (![A_8]: (k4_xboole_0(A_8, A_8)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_114, c_218])).
% 2.94/1.47  tff(c_364, plain, (![A_71, B_72]: (k5_xboole_0(A_71, k4_xboole_0(B_72, A_71))=k2_xboole_0(A_71, B_72))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.94/1.47  tff(c_376, plain, (![A_8]: (k5_xboole_0(A_8, k1_xboole_0)=k2_xboole_0(A_8, A_8))), inference(superposition, [status(thm), theory('equality')], [c_221, c_364])).
% 2.94/1.47  tff(c_386, plain, (![A_8]: (k2_xboole_0(A_8, A_8)=A_8)), inference(demodulation, [status(thm), theory('equality')], [c_264, c_376])).
% 2.94/1.47  tff(c_20, plain, (![A_15]: (k2_tarski(A_15, A_15)=k1_tarski(A_15))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.94/1.47  tff(c_36, plain, (![A_40, B_41]: (k5_xboole_0(k1_tarski(A_40), k1_tarski(B_41))=k2_tarski(A_40, B_41) | B_41=A_40)), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.94/1.47  tff(c_34, plain, (![A_38, B_39]: (r1_xboole_0(k1_tarski(A_38), k1_tarski(B_39)) | B_39=A_38)), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.94/1.47  tff(c_194, plain, (![A_60, B_61]: (k4_xboole_0(A_60, B_61)=A_60 | ~r1_xboole_0(A_60, B_61))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.94/1.47  tff(c_555, plain, (![A_84, B_85]: (k4_xboole_0(k1_tarski(A_84), k1_tarski(B_85))=k1_tarski(A_84) | B_85=A_84)), inference(resolution, [status(thm)], [c_34, c_194])).
% 2.94/1.47  tff(c_18, plain, (![A_13, B_14]: (k5_xboole_0(A_13, k4_xboole_0(B_14, A_13))=k2_xboole_0(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.94/1.47  tff(c_807, plain, (![B_103, A_104]: (k5_xboole_0(k1_tarski(B_103), k1_tarski(A_104))=k2_xboole_0(k1_tarski(B_103), k1_tarski(A_104)) | B_103=A_104)), inference(superposition, [status(thm), theory('equality')], [c_555, c_18])).
% 2.94/1.47  tff(c_1150, plain, (![A_121, B_122]: (k2_xboole_0(k1_tarski(A_121), k1_tarski(B_122))=k2_tarski(A_121, B_122) | B_122=A_121 | B_122=A_121)), inference(superposition, [status(thm), theory('equality')], [c_36, c_807])).
% 2.94/1.47  tff(c_32, plain, (![A_36, B_37]: (k3_tarski(k2_tarski(A_36, B_37))=k2_xboole_0(A_36, B_37))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.94/1.47  tff(c_38, plain, (k3_tarski(k2_tarski(k1_tarski('#skF_1'), k1_tarski('#skF_2')))!=k2_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.94/1.47  tff(c_39, plain, (k2_xboole_0(k1_tarski('#skF_1'), k1_tarski('#skF_2'))!=k2_tarski('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_38])).
% 2.94/1.47  tff(c_1171, plain, ('#skF_2'='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_1150, c_39])).
% 2.94/1.47  tff(c_1175, plain, (k2_xboole_0(k1_tarski('#skF_1'), k1_tarski('#skF_1'))!=k2_tarski('#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1171, c_1171, c_39])).
% 2.94/1.47  tff(c_1178, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_386, c_20, c_1175])).
% 2.94/1.47  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.94/1.47  
% 2.94/1.47  Inference rules
% 2.94/1.47  ----------------------
% 2.94/1.47  #Ref     : 0
% 2.94/1.47  #Sup     : 265
% 2.94/1.47  #Fact    : 0
% 2.94/1.47  #Define  : 0
% 2.94/1.47  #Split   : 0
% 2.94/1.47  #Chain   : 0
% 2.94/1.47  #Close   : 0
% 2.94/1.47  
% 2.94/1.47  Ordering : KBO
% 2.94/1.47  
% 2.94/1.47  Simplification rules
% 2.94/1.47  ----------------------
% 2.94/1.47  #Subsume      : 12
% 2.94/1.47  #Demod        : 226
% 2.94/1.47  #Tautology    : 188
% 2.94/1.47  #SimpNegUnit  : 0
% 2.94/1.47  #BackRed      : 2
% 2.94/1.47  
% 2.94/1.47  #Partial instantiations: 0
% 2.94/1.47  #Strategies tried      : 1
% 2.94/1.47  
% 2.94/1.47  Timing (in seconds)
% 2.94/1.47  ----------------------
% 2.94/1.47  Preprocessing        : 0.31
% 2.94/1.47  Parsing              : 0.17
% 2.94/1.47  CNF conversion       : 0.02
% 2.94/1.47  Main loop            : 0.39
% 2.94/1.47  Inferencing          : 0.15
% 2.94/1.47  Reduction            : 0.15
% 2.94/1.47  Demodulation         : 0.12
% 2.94/1.47  BG Simplification    : 0.02
% 2.94/1.47  Subsumption          : 0.05
% 2.94/1.47  Abstraction          : 0.03
% 2.94/1.47  MUC search           : 0.00
% 2.94/1.47  Cooper               : 0.00
% 2.94/1.47  Total                : 0.73
% 2.94/1.47  Index Insertion      : 0.00
% 2.94/1.47  Index Deletion       : 0.00
% 2.94/1.47  Index Matching       : 0.00
% 2.94/1.47  BG Taut test         : 0.00
%------------------------------------------------------------------------------
