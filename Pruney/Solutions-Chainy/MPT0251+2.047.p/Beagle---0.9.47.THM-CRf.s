%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:50:52 EST 2020

% Result     : Theorem 2.26s
% Output     : CNFRefutation 2.26s
% Verified   : 
% Statistics : Number of formulae       :   65 (  78 expanded)
%              Number of leaves         :   31 (  39 expanded)
%              Depth                    :   12
%              Number of atoms          :   64 (  79 expanded)
%              Number of equality atoms :   35 (  48 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1

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

tff(f_72,negated_conjecture,(
    ~ ! [A,B] :
        ( r2_hidden(A,B)
       => k2_xboole_0(k1_tarski(A),B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_zfmisc_1)).

tff(f_39,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

tff(f_47,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_53,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_67,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => k4_xboole_0(k2_xboole_0(A,B),B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_43,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_65,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_45,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

tff(c_40,plain,(
    r2_hidden('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_12,plain,(
    ! [A_7] : k2_xboole_0(A_7,k1_xboole_0) = A_7 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_18,plain,(
    ! [A_12] : r1_xboole_0(A_12,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_95,plain,(
    ! [B_37,A_38] :
      ( r1_xboole_0(B_37,A_38)
      | ~ r1_xboole_0(A_38,B_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_98,plain,(
    ! [A_12] : r1_xboole_0(k1_xboole_0,A_12) ),
    inference(resolution,[status(thm)],[c_18,c_95])).

tff(c_22,plain,(
    ! [B_16,A_15] : k2_tarski(B_16,A_15) = k2_tarski(A_15,B_16) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_134,plain,(
    ! [A_48,B_49] : k3_tarski(k2_tarski(A_48,B_49)) = k2_xboole_0(A_48,B_49) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_178,plain,(
    ! [B_53,A_54] : k3_tarski(k2_tarski(B_53,A_54)) = k2_xboole_0(A_54,B_53) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_134])).

tff(c_36,plain,(
    ! [A_29,B_30] : k3_tarski(k2_tarski(A_29,B_30)) = k2_xboole_0(A_29,B_30) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_205,plain,(
    ! [B_55,A_56] : k2_xboole_0(B_55,A_56) = k2_xboole_0(A_56,B_55) ),
    inference(superposition,[status(thm),theory(equality)],[c_178,c_36])).

tff(c_221,plain,(
    ! [A_56] : k2_xboole_0(k1_xboole_0,A_56) = A_56 ),
    inference(superposition,[status(thm),theory(equality)],[c_205,c_12])).

tff(c_366,plain,(
    ! [A_69,B_70] :
      ( k4_xboole_0(k2_xboole_0(A_69,B_70),B_70) = A_69
      | ~ r1_xboole_0(A_69,B_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_389,plain,(
    ! [A_56] :
      ( k4_xboole_0(A_56,A_56) = k1_xboole_0
      | ~ r1_xboole_0(k1_xboole_0,A_56) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_221,c_366])).

tff(c_409,plain,(
    ! [A_56] : k4_xboole_0(A_56,A_56) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_389])).

tff(c_8,plain,(
    ! [B_4] : r1_tarski(B_4,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_113,plain,(
    ! [A_42,B_43] :
      ( k3_xboole_0(A_42,B_43) = A_42
      | ~ r1_tarski(A_42,B_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_117,plain,(
    ! [B_4] : k3_xboole_0(B_4,B_4) = B_4 ),
    inference(resolution,[status(thm)],[c_8,c_113])).

tff(c_335,plain,(
    ! [A_63,B_64] : k5_xboole_0(A_63,k3_xboole_0(A_63,B_64)) = k4_xboole_0(A_63,B_64) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_344,plain,(
    ! [B_4] : k5_xboole_0(B_4,B_4) = k4_xboole_0(B_4,B_4) ),
    inference(superposition,[status(thm),theory(equality)],[c_117,c_335])).

tff(c_412,plain,(
    ! [B_4] : k5_xboole_0(B_4,B_4) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_409,c_344])).

tff(c_152,plain,(
    ! [A_50,B_51] :
      ( r1_tarski(k1_tarski(A_50),B_51)
      | ~ r2_hidden(A_50,B_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_14,plain,(
    ! [A_8,B_9] :
      ( k3_xboole_0(A_8,B_9) = A_8
      | ~ r1_tarski(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_493,plain,(
    ! [A_79,B_80] :
      ( k3_xboole_0(k1_tarski(A_79),B_80) = k1_tarski(A_79)
      | ~ r2_hidden(A_79,B_80) ) ),
    inference(resolution,[status(thm)],[c_152,c_14])).

tff(c_10,plain,(
    ! [A_5,B_6] : k5_xboole_0(A_5,k3_xboole_0(A_5,B_6)) = k4_xboole_0(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_499,plain,(
    ! [A_79,B_80] :
      ( k5_xboole_0(k1_tarski(A_79),k1_tarski(A_79)) = k4_xboole_0(k1_tarski(A_79),B_80)
      | ~ r2_hidden(A_79,B_80) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_493,c_10])).

tff(c_533,plain,(
    ! [A_82,B_83] :
      ( k4_xboole_0(k1_tarski(A_82),B_83) = k1_xboole_0
      | ~ r2_hidden(A_82,B_83) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_412,c_499])).

tff(c_16,plain,(
    ! [A_10,B_11] : k2_xboole_0(A_10,k4_xboole_0(B_11,A_10)) = k2_xboole_0(A_10,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_547,plain,(
    ! [B_83,A_82] :
      ( k2_xboole_0(B_83,k1_tarski(A_82)) = k2_xboole_0(B_83,k1_xboole_0)
      | ~ r2_hidden(A_82,B_83) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_533,c_16])).

tff(c_569,plain,(
    ! [B_85,A_86] :
      ( k2_xboole_0(B_85,k1_tarski(A_86)) = B_85
      | ~ r2_hidden(A_86,B_85) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_547])).

tff(c_184,plain,(
    ! [B_53,A_54] : k2_xboole_0(B_53,A_54) = k2_xboole_0(A_54,B_53) ),
    inference(superposition,[status(thm),theory(equality)],[c_178,c_36])).

tff(c_38,plain,(
    k2_xboole_0(k1_tarski('#skF_1'),'#skF_2') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_204,plain,(
    k2_xboole_0('#skF_2',k1_tarski('#skF_1')) != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_184,c_38])).

tff(c_586,plain,(
    ~ r2_hidden('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_569,c_204])).

tff(c_619,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_586])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n022.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 17:03:40 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.26/1.31  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.26/1.31  
% 2.26/1.31  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.26/1.32  %$ r2_hidden > r1_xboole_0 > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1
% 2.26/1.32  
% 2.26/1.32  %Foreground sorts:
% 2.26/1.32  
% 2.26/1.32  
% 2.26/1.32  %Background operators:
% 2.26/1.32  
% 2.26/1.32  
% 2.26/1.32  %Foreground operators:
% 2.26/1.32  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.26/1.32  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.26/1.32  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.26/1.32  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.26/1.32  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.26/1.32  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.26/1.32  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.26/1.32  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.26/1.32  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.26/1.32  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.26/1.32  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.26/1.32  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.26/1.32  tff('#skF_2', type, '#skF_2': $i).
% 2.26/1.32  tff('#skF_1', type, '#skF_1': $i).
% 2.26/1.32  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.26/1.32  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.26/1.32  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.26/1.32  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.26/1.32  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.26/1.32  
% 2.26/1.33  tff(f_72, negated_conjecture, ~(![A, B]: (r2_hidden(A, B) => (k2_xboole_0(k1_tarski(A), B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_zfmisc_1)).
% 2.26/1.33  tff(f_39, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 2.26/1.33  tff(f_47, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 2.26/1.33  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 2.26/1.33  tff(f_53, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 2.26/1.33  tff(f_67, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 2.26/1.33  tff(f_51, axiom, (![A, B]: (r1_xboole_0(A, B) => (k4_xboole_0(k2_xboole_0(A, B), B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t88_xboole_1)).
% 2.26/1.33  tff(f_35, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.26/1.33  tff(f_43, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 2.26/1.33  tff(f_37, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 2.26/1.33  tff(f_65, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 2.26/1.33  tff(f_45, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_xboole_1)).
% 2.26/1.33  tff(c_40, plain, (r2_hidden('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.26/1.33  tff(c_12, plain, (![A_7]: (k2_xboole_0(A_7, k1_xboole_0)=A_7)), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.26/1.33  tff(c_18, plain, (![A_12]: (r1_xboole_0(A_12, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.26/1.33  tff(c_95, plain, (![B_37, A_38]: (r1_xboole_0(B_37, A_38) | ~r1_xboole_0(A_38, B_37))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.26/1.33  tff(c_98, plain, (![A_12]: (r1_xboole_0(k1_xboole_0, A_12))), inference(resolution, [status(thm)], [c_18, c_95])).
% 2.26/1.33  tff(c_22, plain, (![B_16, A_15]: (k2_tarski(B_16, A_15)=k2_tarski(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.26/1.33  tff(c_134, plain, (![A_48, B_49]: (k3_tarski(k2_tarski(A_48, B_49))=k2_xboole_0(A_48, B_49))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.26/1.33  tff(c_178, plain, (![B_53, A_54]: (k3_tarski(k2_tarski(B_53, A_54))=k2_xboole_0(A_54, B_53))), inference(superposition, [status(thm), theory('equality')], [c_22, c_134])).
% 2.26/1.33  tff(c_36, plain, (![A_29, B_30]: (k3_tarski(k2_tarski(A_29, B_30))=k2_xboole_0(A_29, B_30))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.26/1.33  tff(c_205, plain, (![B_55, A_56]: (k2_xboole_0(B_55, A_56)=k2_xboole_0(A_56, B_55))), inference(superposition, [status(thm), theory('equality')], [c_178, c_36])).
% 2.26/1.33  tff(c_221, plain, (![A_56]: (k2_xboole_0(k1_xboole_0, A_56)=A_56)), inference(superposition, [status(thm), theory('equality')], [c_205, c_12])).
% 2.26/1.33  tff(c_366, plain, (![A_69, B_70]: (k4_xboole_0(k2_xboole_0(A_69, B_70), B_70)=A_69 | ~r1_xboole_0(A_69, B_70))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.26/1.33  tff(c_389, plain, (![A_56]: (k4_xboole_0(A_56, A_56)=k1_xboole_0 | ~r1_xboole_0(k1_xboole_0, A_56))), inference(superposition, [status(thm), theory('equality')], [c_221, c_366])).
% 2.26/1.33  tff(c_409, plain, (![A_56]: (k4_xboole_0(A_56, A_56)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_98, c_389])).
% 2.26/1.33  tff(c_8, plain, (![B_4]: (r1_tarski(B_4, B_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.26/1.33  tff(c_113, plain, (![A_42, B_43]: (k3_xboole_0(A_42, B_43)=A_42 | ~r1_tarski(A_42, B_43))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.26/1.33  tff(c_117, plain, (![B_4]: (k3_xboole_0(B_4, B_4)=B_4)), inference(resolution, [status(thm)], [c_8, c_113])).
% 2.26/1.33  tff(c_335, plain, (![A_63, B_64]: (k5_xboole_0(A_63, k3_xboole_0(A_63, B_64))=k4_xboole_0(A_63, B_64))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.26/1.33  tff(c_344, plain, (![B_4]: (k5_xboole_0(B_4, B_4)=k4_xboole_0(B_4, B_4))), inference(superposition, [status(thm), theory('equality')], [c_117, c_335])).
% 2.26/1.33  tff(c_412, plain, (![B_4]: (k5_xboole_0(B_4, B_4)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_409, c_344])).
% 2.26/1.33  tff(c_152, plain, (![A_50, B_51]: (r1_tarski(k1_tarski(A_50), B_51) | ~r2_hidden(A_50, B_51))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.26/1.33  tff(c_14, plain, (![A_8, B_9]: (k3_xboole_0(A_8, B_9)=A_8 | ~r1_tarski(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.26/1.33  tff(c_493, plain, (![A_79, B_80]: (k3_xboole_0(k1_tarski(A_79), B_80)=k1_tarski(A_79) | ~r2_hidden(A_79, B_80))), inference(resolution, [status(thm)], [c_152, c_14])).
% 2.26/1.33  tff(c_10, plain, (![A_5, B_6]: (k5_xboole_0(A_5, k3_xboole_0(A_5, B_6))=k4_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.26/1.33  tff(c_499, plain, (![A_79, B_80]: (k5_xboole_0(k1_tarski(A_79), k1_tarski(A_79))=k4_xboole_0(k1_tarski(A_79), B_80) | ~r2_hidden(A_79, B_80))), inference(superposition, [status(thm), theory('equality')], [c_493, c_10])).
% 2.26/1.33  tff(c_533, plain, (![A_82, B_83]: (k4_xboole_0(k1_tarski(A_82), B_83)=k1_xboole_0 | ~r2_hidden(A_82, B_83))), inference(demodulation, [status(thm), theory('equality')], [c_412, c_499])).
% 2.26/1.33  tff(c_16, plain, (![A_10, B_11]: (k2_xboole_0(A_10, k4_xboole_0(B_11, A_10))=k2_xboole_0(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.26/1.33  tff(c_547, plain, (![B_83, A_82]: (k2_xboole_0(B_83, k1_tarski(A_82))=k2_xboole_0(B_83, k1_xboole_0) | ~r2_hidden(A_82, B_83))), inference(superposition, [status(thm), theory('equality')], [c_533, c_16])).
% 2.26/1.33  tff(c_569, plain, (![B_85, A_86]: (k2_xboole_0(B_85, k1_tarski(A_86))=B_85 | ~r2_hidden(A_86, B_85))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_547])).
% 2.26/1.33  tff(c_184, plain, (![B_53, A_54]: (k2_xboole_0(B_53, A_54)=k2_xboole_0(A_54, B_53))), inference(superposition, [status(thm), theory('equality')], [c_178, c_36])).
% 2.26/1.33  tff(c_38, plain, (k2_xboole_0(k1_tarski('#skF_1'), '#skF_2')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.26/1.33  tff(c_204, plain, (k2_xboole_0('#skF_2', k1_tarski('#skF_1'))!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_184, c_38])).
% 2.26/1.33  tff(c_586, plain, (~r2_hidden('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_569, c_204])).
% 2.26/1.33  tff(c_619, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_40, c_586])).
% 2.26/1.33  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.26/1.33  
% 2.26/1.33  Inference rules
% 2.26/1.33  ----------------------
% 2.26/1.33  #Ref     : 0
% 2.26/1.33  #Sup     : 129
% 2.26/1.33  #Fact    : 0
% 2.26/1.33  #Define  : 0
% 2.26/1.33  #Split   : 0
% 2.26/1.33  #Chain   : 0
% 2.26/1.33  #Close   : 0
% 2.26/1.33  
% 2.26/1.33  Ordering : KBO
% 2.26/1.33  
% 2.26/1.33  Simplification rules
% 2.26/1.33  ----------------------
% 2.26/1.33  #Subsume      : 4
% 2.26/1.33  #Demod        : 38
% 2.26/1.33  #Tautology    : 95
% 2.26/1.33  #SimpNegUnit  : 0
% 2.26/1.33  #BackRed      : 3
% 2.26/1.33  
% 2.26/1.33  #Partial instantiations: 0
% 2.26/1.33  #Strategies tried      : 1
% 2.26/1.33  
% 2.26/1.33  Timing (in seconds)
% 2.26/1.33  ----------------------
% 2.26/1.33  Preprocessing        : 0.32
% 2.26/1.33  Parsing              : 0.17
% 2.26/1.33  CNF conversion       : 0.02
% 2.26/1.33  Main loop            : 0.25
% 2.26/1.33  Inferencing          : 0.10
% 2.26/1.33  Reduction            : 0.08
% 2.26/1.33  Demodulation         : 0.07
% 2.26/1.34  BG Simplification    : 0.02
% 2.26/1.34  Subsumption          : 0.03
% 2.26/1.34  Abstraction          : 0.02
% 2.26/1.34  MUC search           : 0.00
% 2.26/1.34  Cooper               : 0.00
% 2.26/1.34  Total                : 0.59
% 2.26/1.34  Index Insertion      : 0.00
% 2.26/1.34  Index Deletion       : 0.00
% 2.26/1.34  Index Matching       : 0.00
% 2.26/1.34  BG Taut test         : 0.00
%------------------------------------------------------------------------------
