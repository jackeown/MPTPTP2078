%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:50:48 EST 2020

% Result     : Theorem 3.32s
% Output     : CNFRefutation 3.32s
% Verified   : 
% Statistics : Number of formulae       :   69 ( 128 expanded)
%              Number of leaves         :   29 (  55 expanded)
%              Depth                    :   15
%              Number of atoms          :   63 ( 131 expanded)
%              Number of equality atoms :   43 ( 101 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1

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

tff(f_68,negated_conjecture,(
    ~ ! [A,B] :
        ( r2_hidden(A,B)
       => k2_xboole_0(k1_tarski(A),B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_zfmisc_1)).

tff(f_37,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

tff(f_49,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_63,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_43,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_47,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_45,axiom,(
    ! [A,B] : k4_xboole_0(k2_xboole_0(A,B),B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_xboole_1)).

tff(f_61,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(c_40,plain,(
    r2_hidden('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_12,plain,(
    ! [A_7] : k2_xboole_0(A_7,k1_xboole_0) = A_7 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_22,plain,(
    ! [B_17,A_16] : k2_tarski(B_17,A_16) = k2_tarski(A_16,B_17) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_132,plain,(
    ! [A_41,B_42] : k3_tarski(k2_tarski(A_41,B_42)) = k2_xboole_0(A_41,B_42) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_274,plain,(
    ! [A_61,B_62] : k3_tarski(k2_tarski(A_61,B_62)) = k2_xboole_0(B_62,A_61) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_132])).

tff(c_36,plain,(
    ! [A_30,B_31] : k3_tarski(k2_tarski(A_30,B_31)) = k2_xboole_0(A_30,B_31) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_301,plain,(
    ! [B_63,A_64] : k2_xboole_0(B_63,A_64) = k2_xboole_0(A_64,B_63) ),
    inference(superposition,[status(thm),theory(equality)],[c_274,c_36])).

tff(c_337,plain,(
    ! [A_64] : k2_xboole_0(k1_xboole_0,A_64) = A_64 ),
    inference(superposition,[status(thm),theory(equality)],[c_301,c_12])).

tff(c_652,plain,(
    ! [A_79,B_80] : k2_xboole_0(A_79,k4_xboole_0(B_80,A_79)) = k2_xboole_0(A_79,B_80) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_662,plain,(
    ! [B_80] : k4_xboole_0(B_80,k1_xboole_0) = k2_xboole_0(k1_xboole_0,B_80) ),
    inference(superposition,[status(thm),theory(equality)],[c_652,c_337])).

tff(c_687,plain,(
    ! [B_80] : k4_xboole_0(B_80,k1_xboole_0) = B_80 ),
    inference(demodulation,[status(thm),theory(equality)],[c_337,c_662])).

tff(c_390,plain,(
    ! [A_67] : k2_xboole_0(k1_xboole_0,A_67) = A_67 ),
    inference(superposition,[status(thm),theory(equality)],[c_301,c_12])).

tff(c_20,plain,(
    ! [A_14,B_15] : r1_tarski(A_14,k2_xboole_0(A_14,B_15)) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_209,plain,(
    ! [A_53,B_54] :
      ( k3_xboole_0(A_53,B_54) = A_53
      | ~ r1_tarski(A_53,B_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_224,plain,(
    ! [A_14,B_15] : k3_xboole_0(A_14,k2_xboole_0(A_14,B_15)) = A_14 ),
    inference(resolution,[status(thm)],[c_20,c_209])).

tff(c_405,plain,(
    ! [A_67] : k3_xboole_0(k1_xboole_0,A_67) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_390,c_224])).

tff(c_539,plain,(
    ! [A_71,B_72] : k5_xboole_0(A_71,k3_xboole_0(A_71,B_72)) = k4_xboole_0(A_71,B_72) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_1019,plain,(
    ! [A_99] : k5_xboole_0(k1_xboole_0,k1_xboole_0) = k4_xboole_0(k1_xboole_0,A_99) ),
    inference(superposition,[status(thm),theory(equality)],[c_405,c_539])).

tff(c_8,plain,(
    ! [B_4] : r1_tarski(B_4,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_225,plain,(
    ! [B_4] : k3_xboole_0(B_4,B_4) = B_4 ),
    inference(resolution,[status(thm)],[c_8,c_209])).

tff(c_560,plain,(
    ! [B_4] : k5_xboole_0(B_4,B_4) = k4_xboole_0(B_4,B_4) ),
    inference(superposition,[status(thm),theory(equality)],[c_225,c_539])).

tff(c_1034,plain,(
    ! [A_99] : k4_xboole_0(k1_xboole_0,k1_xboole_0) = k4_xboole_0(k1_xboole_0,A_99) ),
    inference(superposition,[status(thm),theory(equality)],[c_1019,c_560])).

tff(c_1046,plain,(
    ! [A_99] : k4_xboole_0(k1_xboole_0,A_99) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_687,c_1034])).

tff(c_18,plain,(
    ! [A_12,B_13] : k4_xboole_0(k2_xboole_0(A_12,B_13),B_13) = k4_xboole_0(A_12,B_13) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_396,plain,(
    ! [A_67] : k4_xboole_0(k1_xboole_0,A_67) = k4_xboole_0(A_67,A_67) ),
    inference(superposition,[status(thm),theory(equality)],[c_390,c_18])).

tff(c_1051,plain,(
    ! [A_67] : k4_xboole_0(A_67,A_67) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1046,c_396])).

tff(c_1088,plain,(
    ! [B_4] : k5_xboole_0(B_4,B_4) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1051,c_560])).

tff(c_34,plain,(
    ! [A_28,B_29] :
      ( r1_tarski(k1_tarski(A_28),B_29)
      | ~ r2_hidden(A_28,B_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_1443,plain,(
    ! [A_115,B_116] :
      ( k3_xboole_0(k1_tarski(A_115),B_116) = k1_tarski(A_115)
      | ~ r2_hidden(A_115,B_116) ) ),
    inference(resolution,[status(thm)],[c_34,c_209])).

tff(c_10,plain,(
    ! [A_5,B_6] : k5_xboole_0(A_5,k3_xboole_0(A_5,B_6)) = k4_xboole_0(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_1456,plain,(
    ! [A_115,B_116] :
      ( k5_xboole_0(k1_tarski(A_115),k1_tarski(A_115)) = k4_xboole_0(k1_tarski(A_115),B_116)
      | ~ r2_hidden(A_115,B_116) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1443,c_10])).

tff(c_2045,plain,(
    ! [A_133,B_134] :
      ( k4_xboole_0(k1_tarski(A_133),B_134) = k1_xboole_0
      | ~ r2_hidden(A_133,B_134) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1088,c_1456])).

tff(c_16,plain,(
    ! [A_10,B_11] : k2_xboole_0(A_10,k4_xboole_0(B_11,A_10)) = k2_xboole_0(A_10,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_2076,plain,(
    ! [B_134,A_133] :
      ( k2_xboole_0(B_134,k1_tarski(A_133)) = k2_xboole_0(B_134,k1_xboole_0)
      | ~ r2_hidden(A_133,B_134) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2045,c_16])).

tff(c_2220,plain,(
    ! [B_139,A_140] :
      ( k2_xboole_0(B_139,k1_tarski(A_140)) = B_139
      | ~ r2_hidden(A_140,B_139) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_2076])).

tff(c_280,plain,(
    ! [B_62,A_61] : k2_xboole_0(B_62,A_61) = k2_xboole_0(A_61,B_62) ),
    inference(superposition,[status(thm),theory(equality)],[c_274,c_36])).

tff(c_38,plain,(
    k2_xboole_0(k1_tarski('#skF_1'),'#skF_2') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_300,plain,(
    k2_xboole_0('#skF_2',k1_tarski('#skF_1')) != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_280,c_38])).

tff(c_2281,plain,(
    ~ r2_hidden('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_2220,c_300])).

tff(c_2340,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_2281])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n015.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 19:27:23 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.32/1.56  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.32/1.57  
% 3.32/1.57  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.32/1.57  %$ r2_hidden > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1
% 3.32/1.57  
% 3.32/1.57  %Foreground sorts:
% 3.32/1.57  
% 3.32/1.57  
% 3.32/1.57  %Background operators:
% 3.32/1.57  
% 3.32/1.57  
% 3.32/1.57  %Foreground operators:
% 3.32/1.57  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.32/1.57  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.32/1.57  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.32/1.57  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.32/1.57  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.32/1.57  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.32/1.57  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.32/1.57  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.32/1.57  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.32/1.57  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.32/1.57  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.32/1.57  tff('#skF_2', type, '#skF_2': $i).
% 3.32/1.57  tff('#skF_1', type, '#skF_1': $i).
% 3.32/1.57  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.32/1.57  tff(k3_tarski, type, k3_tarski: $i > $i).
% 3.32/1.57  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.32/1.57  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.32/1.57  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.32/1.57  
% 3.32/1.58  tff(f_68, negated_conjecture, ~(![A, B]: (r2_hidden(A, B) => (k2_xboole_0(k1_tarski(A), B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_zfmisc_1)).
% 3.32/1.58  tff(f_37, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 3.32/1.58  tff(f_49, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 3.32/1.58  tff(f_63, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 3.32/1.58  tff(f_43, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_xboole_1)).
% 3.32/1.58  tff(f_47, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 3.32/1.58  tff(f_41, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 3.32/1.58  tff(f_35, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 3.32/1.58  tff(f_33, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.32/1.58  tff(f_45, axiom, (![A, B]: (k4_xboole_0(k2_xboole_0(A, B), B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t40_xboole_1)).
% 3.32/1.58  tff(f_61, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 3.32/1.58  tff(c_40, plain, (r2_hidden('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.32/1.58  tff(c_12, plain, (![A_7]: (k2_xboole_0(A_7, k1_xboole_0)=A_7)), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.32/1.58  tff(c_22, plain, (![B_17, A_16]: (k2_tarski(B_17, A_16)=k2_tarski(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.32/1.58  tff(c_132, plain, (![A_41, B_42]: (k3_tarski(k2_tarski(A_41, B_42))=k2_xboole_0(A_41, B_42))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.32/1.58  tff(c_274, plain, (![A_61, B_62]: (k3_tarski(k2_tarski(A_61, B_62))=k2_xboole_0(B_62, A_61))), inference(superposition, [status(thm), theory('equality')], [c_22, c_132])).
% 3.32/1.58  tff(c_36, plain, (![A_30, B_31]: (k3_tarski(k2_tarski(A_30, B_31))=k2_xboole_0(A_30, B_31))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.32/1.58  tff(c_301, plain, (![B_63, A_64]: (k2_xboole_0(B_63, A_64)=k2_xboole_0(A_64, B_63))), inference(superposition, [status(thm), theory('equality')], [c_274, c_36])).
% 3.32/1.58  tff(c_337, plain, (![A_64]: (k2_xboole_0(k1_xboole_0, A_64)=A_64)), inference(superposition, [status(thm), theory('equality')], [c_301, c_12])).
% 3.32/1.58  tff(c_652, plain, (![A_79, B_80]: (k2_xboole_0(A_79, k4_xboole_0(B_80, A_79))=k2_xboole_0(A_79, B_80))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.32/1.58  tff(c_662, plain, (![B_80]: (k4_xboole_0(B_80, k1_xboole_0)=k2_xboole_0(k1_xboole_0, B_80))), inference(superposition, [status(thm), theory('equality')], [c_652, c_337])).
% 3.32/1.58  tff(c_687, plain, (![B_80]: (k4_xboole_0(B_80, k1_xboole_0)=B_80)), inference(demodulation, [status(thm), theory('equality')], [c_337, c_662])).
% 3.32/1.58  tff(c_390, plain, (![A_67]: (k2_xboole_0(k1_xboole_0, A_67)=A_67)), inference(superposition, [status(thm), theory('equality')], [c_301, c_12])).
% 3.32/1.58  tff(c_20, plain, (![A_14, B_15]: (r1_tarski(A_14, k2_xboole_0(A_14, B_15)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.32/1.58  tff(c_209, plain, (![A_53, B_54]: (k3_xboole_0(A_53, B_54)=A_53 | ~r1_tarski(A_53, B_54))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.32/1.58  tff(c_224, plain, (![A_14, B_15]: (k3_xboole_0(A_14, k2_xboole_0(A_14, B_15))=A_14)), inference(resolution, [status(thm)], [c_20, c_209])).
% 3.32/1.58  tff(c_405, plain, (![A_67]: (k3_xboole_0(k1_xboole_0, A_67)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_390, c_224])).
% 3.32/1.58  tff(c_539, plain, (![A_71, B_72]: (k5_xboole_0(A_71, k3_xboole_0(A_71, B_72))=k4_xboole_0(A_71, B_72))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.32/1.58  tff(c_1019, plain, (![A_99]: (k5_xboole_0(k1_xboole_0, k1_xboole_0)=k4_xboole_0(k1_xboole_0, A_99))), inference(superposition, [status(thm), theory('equality')], [c_405, c_539])).
% 3.32/1.58  tff(c_8, plain, (![B_4]: (r1_tarski(B_4, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.32/1.58  tff(c_225, plain, (![B_4]: (k3_xboole_0(B_4, B_4)=B_4)), inference(resolution, [status(thm)], [c_8, c_209])).
% 3.32/1.58  tff(c_560, plain, (![B_4]: (k5_xboole_0(B_4, B_4)=k4_xboole_0(B_4, B_4))), inference(superposition, [status(thm), theory('equality')], [c_225, c_539])).
% 3.32/1.58  tff(c_1034, plain, (![A_99]: (k4_xboole_0(k1_xboole_0, k1_xboole_0)=k4_xboole_0(k1_xboole_0, A_99))), inference(superposition, [status(thm), theory('equality')], [c_1019, c_560])).
% 3.32/1.58  tff(c_1046, plain, (![A_99]: (k4_xboole_0(k1_xboole_0, A_99)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_687, c_1034])).
% 3.32/1.58  tff(c_18, plain, (![A_12, B_13]: (k4_xboole_0(k2_xboole_0(A_12, B_13), B_13)=k4_xboole_0(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.32/1.58  tff(c_396, plain, (![A_67]: (k4_xboole_0(k1_xboole_0, A_67)=k4_xboole_0(A_67, A_67))), inference(superposition, [status(thm), theory('equality')], [c_390, c_18])).
% 3.32/1.58  tff(c_1051, plain, (![A_67]: (k4_xboole_0(A_67, A_67)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_1046, c_396])).
% 3.32/1.58  tff(c_1088, plain, (![B_4]: (k5_xboole_0(B_4, B_4)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_1051, c_560])).
% 3.32/1.58  tff(c_34, plain, (![A_28, B_29]: (r1_tarski(k1_tarski(A_28), B_29) | ~r2_hidden(A_28, B_29))), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.32/1.58  tff(c_1443, plain, (![A_115, B_116]: (k3_xboole_0(k1_tarski(A_115), B_116)=k1_tarski(A_115) | ~r2_hidden(A_115, B_116))), inference(resolution, [status(thm)], [c_34, c_209])).
% 3.32/1.58  tff(c_10, plain, (![A_5, B_6]: (k5_xboole_0(A_5, k3_xboole_0(A_5, B_6))=k4_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.32/1.58  tff(c_1456, plain, (![A_115, B_116]: (k5_xboole_0(k1_tarski(A_115), k1_tarski(A_115))=k4_xboole_0(k1_tarski(A_115), B_116) | ~r2_hidden(A_115, B_116))), inference(superposition, [status(thm), theory('equality')], [c_1443, c_10])).
% 3.32/1.58  tff(c_2045, plain, (![A_133, B_134]: (k4_xboole_0(k1_tarski(A_133), B_134)=k1_xboole_0 | ~r2_hidden(A_133, B_134))), inference(demodulation, [status(thm), theory('equality')], [c_1088, c_1456])).
% 3.32/1.58  tff(c_16, plain, (![A_10, B_11]: (k2_xboole_0(A_10, k4_xboole_0(B_11, A_10))=k2_xboole_0(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.32/1.58  tff(c_2076, plain, (![B_134, A_133]: (k2_xboole_0(B_134, k1_tarski(A_133))=k2_xboole_0(B_134, k1_xboole_0) | ~r2_hidden(A_133, B_134))), inference(superposition, [status(thm), theory('equality')], [c_2045, c_16])).
% 3.32/1.58  tff(c_2220, plain, (![B_139, A_140]: (k2_xboole_0(B_139, k1_tarski(A_140))=B_139 | ~r2_hidden(A_140, B_139))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_2076])).
% 3.32/1.58  tff(c_280, plain, (![B_62, A_61]: (k2_xboole_0(B_62, A_61)=k2_xboole_0(A_61, B_62))), inference(superposition, [status(thm), theory('equality')], [c_274, c_36])).
% 3.32/1.58  tff(c_38, plain, (k2_xboole_0(k1_tarski('#skF_1'), '#skF_2')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.32/1.58  tff(c_300, plain, (k2_xboole_0('#skF_2', k1_tarski('#skF_1'))!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_280, c_38])).
% 3.32/1.58  tff(c_2281, plain, (~r2_hidden('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_2220, c_300])).
% 3.32/1.58  tff(c_2340, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_40, c_2281])).
% 3.32/1.58  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.32/1.58  
% 3.32/1.58  Inference rules
% 3.32/1.58  ----------------------
% 3.32/1.58  #Ref     : 0
% 3.32/1.58  #Sup     : 539
% 3.32/1.58  #Fact    : 0
% 3.32/1.58  #Define  : 0
% 3.32/1.58  #Split   : 0
% 3.32/1.58  #Chain   : 0
% 3.32/1.58  #Close   : 0
% 3.32/1.58  
% 3.32/1.58  Ordering : KBO
% 3.32/1.58  
% 3.32/1.58  Simplification rules
% 3.32/1.58  ----------------------
% 3.32/1.58  #Subsume      : 21
% 3.32/1.58  #Demod        : 456
% 3.32/1.58  #Tautology    : 425
% 3.32/1.58  #SimpNegUnit  : 0
% 3.32/1.58  #BackRed      : 11
% 3.32/1.58  
% 3.32/1.58  #Partial instantiations: 0
% 3.32/1.58  #Strategies tried      : 1
% 3.32/1.58  
% 3.32/1.58  Timing (in seconds)
% 3.32/1.58  ----------------------
% 3.32/1.59  Preprocessing        : 0.30
% 3.32/1.59  Parsing              : 0.16
% 3.32/1.59  CNF conversion       : 0.02
% 3.32/1.59  Main loop            : 0.47
% 3.32/1.59  Inferencing          : 0.17
% 3.32/1.59  Reduction            : 0.19
% 3.32/1.59  Demodulation         : 0.15
% 3.32/1.59  BG Simplification    : 0.02
% 3.32/1.59  Subsumption          : 0.06
% 3.32/1.59  Abstraction          : 0.03
% 3.32/1.59  MUC search           : 0.00
% 3.32/1.59  Cooper               : 0.00
% 3.32/1.59  Total                : 0.80
% 3.32/1.59  Index Insertion      : 0.00
% 3.32/1.59  Index Deletion       : 0.00
% 3.32/1.59  Index Matching       : 0.00
% 3.32/1.59  BG Taut test         : 0.00
%------------------------------------------------------------------------------
