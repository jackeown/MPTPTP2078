%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:50:52 EST 2020

% Result     : Theorem 2.98s
% Output     : CNFRefutation 3.09s
% Verified   : 
% Statistics : Number of formulae       :   73 ( 164 expanded)
%              Number of leaves         :   30 (  67 expanded)
%              Depth                    :   14
%              Number of atoms          :   67 ( 169 expanded)
%              Number of equality atoms :   47 ( 132 expanded)
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_zfmisc_1)).

tff(f_35,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

tff(f_41,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_49,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_63,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_43,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_47,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_45,axiom,(
    ! [A,B] : k4_xboole_0(k2_xboole_0(A,B),B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_61,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(c_40,plain,(
    r2_hidden('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_10,plain,(
    ! [A_5] : k2_xboole_0(A_5,k1_xboole_0) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_14,plain,(
    ! [A_8] : r1_tarski(k1_xboole_0,A_8) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_106,plain,(
    ! [A_41,B_42] :
      ( k3_xboole_0(A_41,B_42) = A_41
      | ~ r1_tarski(A_41,B_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_117,plain,(
    ! [A_8] : k3_xboole_0(k1_xboole_0,A_8) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_14,c_106])).

tff(c_173,plain,(
    ! [A_50,B_51] : k5_xboole_0(A_50,k3_xboole_0(A_50,B_51)) = k4_xboole_0(A_50,B_51) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_214,plain,(
    ! [A_54] : k5_xboole_0(k1_xboole_0,k1_xboole_0) = k4_xboole_0(k1_xboole_0,A_54) ),
    inference(superposition,[status(thm),theory(equality)],[c_117,c_173])).

tff(c_185,plain,(
    ! [A_8] : k5_xboole_0(k1_xboole_0,k1_xboole_0) = k4_xboole_0(k1_xboole_0,A_8) ),
    inference(superposition,[status(thm),theory(equality)],[c_117,c_173])).

tff(c_217,plain,(
    ! [A_8,A_54] : k4_xboole_0(k1_xboole_0,A_8) = k4_xboole_0(k1_xboole_0,A_54) ),
    inference(superposition,[status(thm),theory(equality)],[c_214,c_185])).

tff(c_22,plain,(
    ! [B_16,A_15] : k2_tarski(B_16,A_15) = k2_tarski(A_15,B_16) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_155,plain,(
    ! [A_48,B_49] : k3_tarski(k2_tarski(A_48,B_49)) = k2_xboole_0(A_48,B_49) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_405,plain,(
    ! [A_68,B_69] : k3_tarski(k2_tarski(A_68,B_69)) = k2_xboole_0(B_69,A_68) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_155])).

tff(c_36,plain,(
    ! [A_29,B_30] : k3_tarski(k2_tarski(A_29,B_30)) = k2_xboole_0(A_29,B_30) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_432,plain,(
    ! [B_70,A_71] : k2_xboole_0(B_70,A_71) = k2_xboole_0(A_71,B_70) ),
    inference(superposition,[status(thm),theory(equality)],[c_405,c_36])).

tff(c_462,plain,(
    ! [A_71] : k2_xboole_0(k1_xboole_0,A_71) = A_71 ),
    inference(superposition,[status(thm),theory(equality)],[c_432,c_10])).

tff(c_524,plain,(
    ! [A_74] : k2_xboole_0(k1_xboole_0,A_74) = A_74 ),
    inference(superposition,[status(thm),theory(equality)],[c_432,c_10])).

tff(c_16,plain,(
    ! [A_9,B_10] : k2_xboole_0(A_9,k4_xboole_0(B_10,A_9)) = k2_xboole_0(A_9,B_10) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_544,plain,(
    ! [B_10] : k4_xboole_0(B_10,k1_xboole_0) = k2_xboole_0(k1_xboole_0,B_10) ),
    inference(superposition,[status(thm),theory(equality)],[c_524,c_16])).

tff(c_585,plain,(
    ! [B_75] : k4_xboole_0(B_75,k1_xboole_0) = B_75 ),
    inference(demodulation,[status(thm),theory(equality)],[c_462,c_544])).

tff(c_638,plain,(
    ! [A_76] : k4_xboole_0(k1_xboole_0,A_76) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_217,c_585])).

tff(c_20,plain,(
    ! [A_13,B_14] : k5_xboole_0(A_13,k4_xboole_0(B_14,A_13)) = k2_xboole_0(A_13,B_14) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_647,plain,(
    ! [A_76] : k5_xboole_0(A_76,k1_xboole_0) = k2_xboole_0(A_76,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_638,c_20])).

tff(c_659,plain,(
    ! [A_76] : k5_xboole_0(A_76,k1_xboole_0) = A_76 ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_647])).

tff(c_625,plain,(
    ! [A_54] : k4_xboole_0(k1_xboole_0,A_54) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_217,c_585])).

tff(c_18,plain,(
    ! [A_11,B_12] : k4_xboole_0(k2_xboole_0(A_11,B_12),B_12) = k4_xboole_0(A_11,B_12) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_536,plain,(
    ! [A_74] : k4_xboole_0(k1_xboole_0,A_74) = k4_xboole_0(A_74,A_74) ),
    inference(superposition,[status(thm),theory(equality)],[c_524,c_18])).

tff(c_758,plain,(
    ! [A_74] : k4_xboole_0(A_74,A_74) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_625,c_536])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_118,plain,(
    ! [B_2] : k3_xboole_0(B_2,B_2) = B_2 ),
    inference(resolution,[status(thm)],[c_6,c_106])).

tff(c_182,plain,(
    ! [B_2] : k5_xboole_0(B_2,B_2) = k4_xboole_0(B_2,B_2) ),
    inference(superposition,[status(thm),theory(equality)],[c_118,c_173])).

tff(c_759,plain,(
    ! [B_2] : k5_xboole_0(B_2,B_2) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_758,c_182])).

tff(c_34,plain,(
    ! [A_27,B_28] :
      ( r1_tarski(k1_tarski(A_27),B_28)
      | ~ r2_hidden(A_27,B_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_1225,plain,(
    ! [A_101,B_102] :
      ( k3_xboole_0(k1_tarski(A_101),B_102) = k1_tarski(A_101)
      | ~ r2_hidden(A_101,B_102) ) ),
    inference(resolution,[status(thm)],[c_34,c_106])).

tff(c_8,plain,(
    ! [A_3,B_4] : k5_xboole_0(A_3,k3_xboole_0(A_3,B_4)) = k4_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_1231,plain,(
    ! [A_101,B_102] :
      ( k5_xboole_0(k1_tarski(A_101),k1_tarski(A_101)) = k4_xboole_0(k1_tarski(A_101),B_102)
      | ~ r2_hidden(A_101,B_102) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1225,c_8])).

tff(c_1406,plain,(
    ! [A_107,B_108] :
      ( k4_xboole_0(k1_tarski(A_107),B_108) = k1_xboole_0
      | ~ r2_hidden(A_107,B_108) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_759,c_1231])).

tff(c_1434,plain,(
    ! [B_108,A_107] :
      ( k2_xboole_0(B_108,k1_tarski(A_107)) = k5_xboole_0(B_108,k1_xboole_0)
      | ~ r2_hidden(A_107,B_108) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1406,c_20])).

tff(c_1578,plain,(
    ! [B_111,A_112] :
      ( k2_xboole_0(B_111,k1_tarski(A_112)) = B_111
      | ~ r2_hidden(A_112,B_111) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_659,c_1434])).

tff(c_411,plain,(
    ! [B_69,A_68] : k2_xboole_0(B_69,A_68) = k2_xboole_0(A_68,B_69) ),
    inference(superposition,[status(thm),theory(equality)],[c_405,c_36])).

tff(c_38,plain,(
    k2_xboole_0(k1_tarski('#skF_1'),'#skF_2') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_431,plain,(
    k2_xboole_0('#skF_2',k1_tarski('#skF_1')) != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_411,c_38])).

tff(c_1613,plain,(
    ~ r2_hidden('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_1578,c_431])).

tff(c_1664,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_1613])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n014.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 12:05:37 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.98/1.53  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.98/1.54  
% 2.98/1.54  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.98/1.54  %$ r2_hidden > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1
% 2.98/1.54  
% 2.98/1.54  %Foreground sorts:
% 2.98/1.54  
% 2.98/1.54  
% 2.98/1.54  %Background operators:
% 2.98/1.54  
% 2.98/1.54  
% 2.98/1.54  %Foreground operators:
% 2.98/1.54  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.98/1.54  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.98/1.54  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.98/1.54  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.98/1.54  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.98/1.54  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.98/1.54  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.98/1.54  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.98/1.54  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.98/1.54  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.98/1.54  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.98/1.54  tff('#skF_2', type, '#skF_2': $i).
% 2.98/1.54  tff('#skF_1', type, '#skF_1': $i).
% 2.98/1.54  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.98/1.54  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.98/1.54  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.98/1.54  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.98/1.54  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.98/1.54  
% 3.09/1.56  tff(f_68, negated_conjecture, ~(![A, B]: (r2_hidden(A, B) => (k2_xboole_0(k1_tarski(A), B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_zfmisc_1)).
% 3.09/1.56  tff(f_35, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 3.09/1.56  tff(f_41, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 3.09/1.56  tff(f_39, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 3.09/1.56  tff(f_33, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 3.09/1.56  tff(f_49, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 3.09/1.56  tff(f_63, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 3.09/1.56  tff(f_43, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 3.09/1.56  tff(f_47, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_xboole_1)).
% 3.09/1.56  tff(f_45, axiom, (![A, B]: (k4_xboole_0(k2_xboole_0(A, B), B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t40_xboole_1)).
% 3.09/1.56  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.09/1.56  tff(f_61, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 3.09/1.56  tff(c_40, plain, (r2_hidden('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.09/1.56  tff(c_10, plain, (![A_5]: (k2_xboole_0(A_5, k1_xboole_0)=A_5)), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.09/1.56  tff(c_14, plain, (![A_8]: (r1_tarski(k1_xboole_0, A_8))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.09/1.56  tff(c_106, plain, (![A_41, B_42]: (k3_xboole_0(A_41, B_42)=A_41 | ~r1_tarski(A_41, B_42))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.09/1.56  tff(c_117, plain, (![A_8]: (k3_xboole_0(k1_xboole_0, A_8)=k1_xboole_0)), inference(resolution, [status(thm)], [c_14, c_106])).
% 3.09/1.56  tff(c_173, plain, (![A_50, B_51]: (k5_xboole_0(A_50, k3_xboole_0(A_50, B_51))=k4_xboole_0(A_50, B_51))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.09/1.56  tff(c_214, plain, (![A_54]: (k5_xboole_0(k1_xboole_0, k1_xboole_0)=k4_xboole_0(k1_xboole_0, A_54))), inference(superposition, [status(thm), theory('equality')], [c_117, c_173])).
% 3.09/1.56  tff(c_185, plain, (![A_8]: (k5_xboole_0(k1_xboole_0, k1_xboole_0)=k4_xboole_0(k1_xboole_0, A_8))), inference(superposition, [status(thm), theory('equality')], [c_117, c_173])).
% 3.09/1.56  tff(c_217, plain, (![A_8, A_54]: (k4_xboole_0(k1_xboole_0, A_8)=k4_xboole_0(k1_xboole_0, A_54))), inference(superposition, [status(thm), theory('equality')], [c_214, c_185])).
% 3.09/1.56  tff(c_22, plain, (![B_16, A_15]: (k2_tarski(B_16, A_15)=k2_tarski(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.09/1.56  tff(c_155, plain, (![A_48, B_49]: (k3_tarski(k2_tarski(A_48, B_49))=k2_xboole_0(A_48, B_49))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.09/1.56  tff(c_405, plain, (![A_68, B_69]: (k3_tarski(k2_tarski(A_68, B_69))=k2_xboole_0(B_69, A_68))), inference(superposition, [status(thm), theory('equality')], [c_22, c_155])).
% 3.09/1.56  tff(c_36, plain, (![A_29, B_30]: (k3_tarski(k2_tarski(A_29, B_30))=k2_xboole_0(A_29, B_30))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.09/1.56  tff(c_432, plain, (![B_70, A_71]: (k2_xboole_0(B_70, A_71)=k2_xboole_0(A_71, B_70))), inference(superposition, [status(thm), theory('equality')], [c_405, c_36])).
% 3.09/1.56  tff(c_462, plain, (![A_71]: (k2_xboole_0(k1_xboole_0, A_71)=A_71)), inference(superposition, [status(thm), theory('equality')], [c_432, c_10])).
% 3.09/1.56  tff(c_524, plain, (![A_74]: (k2_xboole_0(k1_xboole_0, A_74)=A_74)), inference(superposition, [status(thm), theory('equality')], [c_432, c_10])).
% 3.09/1.56  tff(c_16, plain, (![A_9, B_10]: (k2_xboole_0(A_9, k4_xboole_0(B_10, A_9))=k2_xboole_0(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.09/1.56  tff(c_544, plain, (![B_10]: (k4_xboole_0(B_10, k1_xboole_0)=k2_xboole_0(k1_xboole_0, B_10))), inference(superposition, [status(thm), theory('equality')], [c_524, c_16])).
% 3.09/1.56  tff(c_585, plain, (![B_75]: (k4_xboole_0(B_75, k1_xboole_0)=B_75)), inference(demodulation, [status(thm), theory('equality')], [c_462, c_544])).
% 3.09/1.56  tff(c_638, plain, (![A_76]: (k4_xboole_0(k1_xboole_0, A_76)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_217, c_585])).
% 3.09/1.56  tff(c_20, plain, (![A_13, B_14]: (k5_xboole_0(A_13, k4_xboole_0(B_14, A_13))=k2_xboole_0(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.09/1.56  tff(c_647, plain, (![A_76]: (k5_xboole_0(A_76, k1_xboole_0)=k2_xboole_0(A_76, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_638, c_20])).
% 3.09/1.56  tff(c_659, plain, (![A_76]: (k5_xboole_0(A_76, k1_xboole_0)=A_76)), inference(demodulation, [status(thm), theory('equality')], [c_10, c_647])).
% 3.09/1.56  tff(c_625, plain, (![A_54]: (k4_xboole_0(k1_xboole_0, A_54)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_217, c_585])).
% 3.09/1.56  tff(c_18, plain, (![A_11, B_12]: (k4_xboole_0(k2_xboole_0(A_11, B_12), B_12)=k4_xboole_0(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.09/1.56  tff(c_536, plain, (![A_74]: (k4_xboole_0(k1_xboole_0, A_74)=k4_xboole_0(A_74, A_74))), inference(superposition, [status(thm), theory('equality')], [c_524, c_18])).
% 3.09/1.56  tff(c_758, plain, (![A_74]: (k4_xboole_0(A_74, A_74)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_625, c_536])).
% 3.09/1.56  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.09/1.56  tff(c_118, plain, (![B_2]: (k3_xboole_0(B_2, B_2)=B_2)), inference(resolution, [status(thm)], [c_6, c_106])).
% 3.09/1.56  tff(c_182, plain, (![B_2]: (k5_xboole_0(B_2, B_2)=k4_xboole_0(B_2, B_2))), inference(superposition, [status(thm), theory('equality')], [c_118, c_173])).
% 3.09/1.56  tff(c_759, plain, (![B_2]: (k5_xboole_0(B_2, B_2)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_758, c_182])).
% 3.09/1.56  tff(c_34, plain, (![A_27, B_28]: (r1_tarski(k1_tarski(A_27), B_28) | ~r2_hidden(A_27, B_28))), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.09/1.56  tff(c_1225, plain, (![A_101, B_102]: (k3_xboole_0(k1_tarski(A_101), B_102)=k1_tarski(A_101) | ~r2_hidden(A_101, B_102))), inference(resolution, [status(thm)], [c_34, c_106])).
% 3.09/1.56  tff(c_8, plain, (![A_3, B_4]: (k5_xboole_0(A_3, k3_xboole_0(A_3, B_4))=k4_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.09/1.56  tff(c_1231, plain, (![A_101, B_102]: (k5_xboole_0(k1_tarski(A_101), k1_tarski(A_101))=k4_xboole_0(k1_tarski(A_101), B_102) | ~r2_hidden(A_101, B_102))), inference(superposition, [status(thm), theory('equality')], [c_1225, c_8])).
% 3.09/1.56  tff(c_1406, plain, (![A_107, B_108]: (k4_xboole_0(k1_tarski(A_107), B_108)=k1_xboole_0 | ~r2_hidden(A_107, B_108))), inference(demodulation, [status(thm), theory('equality')], [c_759, c_1231])).
% 3.09/1.56  tff(c_1434, plain, (![B_108, A_107]: (k2_xboole_0(B_108, k1_tarski(A_107))=k5_xboole_0(B_108, k1_xboole_0) | ~r2_hidden(A_107, B_108))), inference(superposition, [status(thm), theory('equality')], [c_1406, c_20])).
% 3.09/1.56  tff(c_1578, plain, (![B_111, A_112]: (k2_xboole_0(B_111, k1_tarski(A_112))=B_111 | ~r2_hidden(A_112, B_111))), inference(demodulation, [status(thm), theory('equality')], [c_659, c_1434])).
% 3.09/1.56  tff(c_411, plain, (![B_69, A_68]: (k2_xboole_0(B_69, A_68)=k2_xboole_0(A_68, B_69))), inference(superposition, [status(thm), theory('equality')], [c_405, c_36])).
% 3.09/1.56  tff(c_38, plain, (k2_xboole_0(k1_tarski('#skF_1'), '#skF_2')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.09/1.56  tff(c_431, plain, (k2_xboole_0('#skF_2', k1_tarski('#skF_1'))!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_411, c_38])).
% 3.09/1.56  tff(c_1613, plain, (~r2_hidden('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_1578, c_431])).
% 3.09/1.56  tff(c_1664, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_40, c_1613])).
% 3.09/1.56  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.09/1.56  
% 3.09/1.56  Inference rules
% 3.09/1.56  ----------------------
% 3.09/1.56  #Ref     : 0
% 3.09/1.56  #Sup     : 384
% 3.09/1.56  #Fact    : 0
% 3.09/1.56  #Define  : 0
% 3.09/1.56  #Split   : 0
% 3.09/1.56  #Chain   : 0
% 3.09/1.56  #Close   : 0
% 3.09/1.56  
% 3.09/1.56  Ordering : KBO
% 3.09/1.56  
% 3.09/1.56  Simplification rules
% 3.09/1.56  ----------------------
% 3.09/1.56  #Subsume      : 25
% 3.09/1.56  #Demod        : 327
% 3.09/1.56  #Tautology    : 305
% 3.09/1.56  #SimpNegUnit  : 0
% 3.09/1.56  #BackRed      : 6
% 3.09/1.56  
% 3.09/1.56  #Partial instantiations: 0
% 3.09/1.56  #Strategies tried      : 1
% 3.09/1.56  
% 3.09/1.56  Timing (in seconds)
% 3.09/1.56  ----------------------
% 3.09/1.56  Preprocessing        : 0.30
% 3.09/1.56  Parsing              : 0.16
% 3.09/1.56  CNF conversion       : 0.02
% 3.09/1.56  Main loop            : 0.40
% 3.09/1.56  Inferencing          : 0.14
% 3.09/1.56  Reduction            : 0.16
% 3.09/1.56  Demodulation         : 0.13
% 3.09/1.56  BG Simplification    : 0.02
% 3.09/1.56  Subsumption          : 0.05
% 3.09/1.56  Abstraction          : 0.03
% 3.09/1.56  MUC search           : 0.00
% 3.09/1.56  Cooper               : 0.00
% 3.09/1.56  Total                : 0.74
% 3.09/1.56  Index Insertion      : 0.00
% 3.09/1.56  Index Deletion       : 0.00
% 3.09/1.56  Index Matching       : 0.00
% 3.09/1.56  BG Taut test         : 0.00
%------------------------------------------------------------------------------
