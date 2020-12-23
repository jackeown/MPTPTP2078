%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:52:38 EST 2020

% Result     : Theorem 2.58s
% Output     : CNFRefutation 2.91s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 137 expanded)
%              Number of leaves         :   33 (  59 expanded)
%              Depth                    :   11
%              Number of atoms          :   79 ( 157 expanded)
%              Number of equality atoms :   33 (  76 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_75,negated_conjecture,(
    ~ ! [A,B] :
        ( k4_xboole_0(A,k1_tarski(B)) = A
      <=> ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_zfmisc_1)).

tff(f_67,axiom,(
    ! [A,B] :
      ( ~ r2_hidden(A,B)
     => r1_xboole_0(k1_tarski(A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l27_zfmisc_1)).

tff(f_43,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

tff(f_39,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_33,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_41,axiom,(
    ! [A,B] : k2_xboole_0(k3_xboole_0(A,B),k4_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_xboole_1)).

tff(f_49,axiom,(
    ! [A,B,C] :
      ( r1_xboole_0(A,B)
     => k2_xboole_0(k4_xboole_0(C,A),B) = k4_xboole_0(k2_xboole_0(C,B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_xboole_1)).

tff(f_45,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_62,axiom,(
    ! [A,B] :
      ~ ( r1_xboole_0(k1_tarski(A),B)
        & r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l24_zfmisc_1)).

tff(c_36,plain,
    ( ~ r2_hidden('#skF_2','#skF_1')
    | r2_hidden('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_61,plain,(
    ~ r2_hidden('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_36])).

tff(c_30,plain,(
    ! [A_30,B_31] :
      ( r1_xboole_0(k1_tarski(A_30),B_31)
      | r2_hidden(A_30,B_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_14,plain,(
    ! [A_12] : k5_xboole_0(A_12,k1_xboole_0) = A_12 ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_10,plain,(
    ! [A_9] : r1_tarski(k1_xboole_0,A_9) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_147,plain,(
    ! [A_52,B_53] :
      ( k3_xboole_0(A_52,B_53) = A_52
      | ~ r1_tarski(A_52,B_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_152,plain,(
    ! [A_54] : k3_xboole_0(k1_xboole_0,A_54) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_10,c_147])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_157,plain,(
    ! [A_54] : k3_xboole_0(A_54,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_152,c_2])).

tff(c_229,plain,(
    ! [A_62,B_63] : k5_xboole_0(A_62,k3_xboole_0(A_62,B_63)) = k4_xboole_0(A_62,B_63) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_238,plain,(
    ! [A_54] : k5_xboole_0(A_54,k1_xboole_0) = k4_xboole_0(A_54,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_157,c_229])).

tff(c_250,plain,(
    ! [A_54] : k4_xboole_0(A_54,k1_xboole_0) = A_54 ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_238])).

tff(c_311,plain,(
    ! [A_69,B_70] : k2_xboole_0(k3_xboole_0(A_69,B_70),k4_xboole_0(A_69,B_70)) = A_69 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_326,plain,(
    ! [A_54] : k2_xboole_0(k1_xboole_0,k4_xboole_0(A_54,k1_xboole_0)) = A_54 ),
    inference(superposition,[status(thm),theory(equality)],[c_157,c_311])).

tff(c_340,plain,(
    ! [A_54] : k2_xboole_0(k1_xboole_0,A_54) = A_54 ),
    inference(demodulation,[status(thm),theory(equality)],[c_250,c_326])).

tff(c_151,plain,(
    ! [A_9] : k3_xboole_0(k1_xboole_0,A_9) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_10,c_147])).

tff(c_241,plain,(
    ! [A_9] : k5_xboole_0(k1_xboole_0,k1_xboole_0) = k4_xboole_0(k1_xboole_0,A_9) ),
    inference(superposition,[status(thm),theory(equality)],[c_151,c_229])).

tff(c_251,plain,(
    ! [A_9] : k4_xboole_0(k1_xboole_0,A_9) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_241])).

tff(c_457,plain,(
    ! [C_85,B_86,A_87] :
      ( k4_xboole_0(k2_xboole_0(C_85,B_86),A_87) = k2_xboole_0(k4_xboole_0(C_85,A_87),B_86)
      | ~ r1_xboole_0(A_87,B_86) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_489,plain,(
    ! [A_87,A_54] :
      ( k2_xboole_0(k4_xboole_0(k1_xboole_0,A_87),A_54) = k4_xboole_0(A_54,A_87)
      | ~ r1_xboole_0(A_87,A_54) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_340,c_457])).

tff(c_507,plain,(
    ! [A_88,A_89] :
      ( k4_xboole_0(A_88,A_89) = A_88
      | ~ r1_xboole_0(A_89,A_88) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_340,c_251,c_489])).

tff(c_658,plain,(
    ! [B_94,A_95] :
      ( k4_xboole_0(B_94,k1_tarski(A_95)) = B_94
      | r2_hidden(A_95,B_94) ) ),
    inference(resolution,[status(thm)],[c_30,c_507])).

tff(c_34,plain,
    ( k4_xboole_0('#skF_1',k1_tarski('#skF_2')) != '#skF_1'
    | r2_hidden('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_104,plain,(
    k4_xboole_0('#skF_1',k1_tarski('#skF_2')) != '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_34])).

tff(c_691,plain,(
    r2_hidden('#skF_2','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_658,c_104])).

tff(c_722,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_61,c_691])).

tff(c_723,plain,(
    r2_hidden('#skF_4','#skF_3') ),
    inference(splitRight,[status(thm)],[c_34])).

tff(c_724,plain,(
    k4_xboole_0('#skF_1',k1_tarski('#skF_2')) = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_34])).

tff(c_38,plain,
    ( k4_xboole_0('#skF_1',k1_tarski('#skF_2')) != '#skF_1'
    | k4_xboole_0('#skF_3',k1_tarski('#skF_4')) = '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_875,plain,(
    k4_xboole_0('#skF_3',k1_tarski('#skF_4')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_724,c_38])).

tff(c_16,plain,(
    ! [A_13,B_14] : r1_xboole_0(k4_xboole_0(A_13,B_14),B_14) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_95,plain,(
    ! [B_41,A_42] :
      ( r1_xboole_0(B_41,A_42)
      | ~ r1_xboole_0(A_42,B_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_98,plain,(
    ! [B_14,A_13] : r1_xboole_0(B_14,k4_xboole_0(A_13,B_14)) ),
    inference(resolution,[status(thm)],[c_16,c_95])).

tff(c_838,plain,(
    ! [A_105,B_106] :
      ( ~ r2_hidden(A_105,B_106)
      | ~ r1_xboole_0(k1_tarski(A_105),B_106) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_851,plain,(
    ! [A_105,A_13] : ~ r2_hidden(A_105,k4_xboole_0(A_13,k1_tarski(A_105))) ),
    inference(resolution,[status(thm)],[c_98,c_838])).

tff(c_879,plain,(
    ~ r2_hidden('#skF_4','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_875,c_851])).

tff(c_890,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_723,c_879])).

tff(c_891,plain,(
    r2_hidden('#skF_4','#skF_3') ),
    inference(splitRight,[status(thm)],[c_36])).

tff(c_892,plain,(
    r2_hidden('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_36])).

tff(c_40,plain,
    ( ~ r2_hidden('#skF_2','#skF_1')
    | k4_xboole_0('#skF_3',k1_tarski('#skF_4')) = '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_1061,plain,(
    k4_xboole_0('#skF_3',k1_tarski('#skF_4')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_892,c_40])).

tff(c_893,plain,(
    ! [B_113,A_114] :
      ( r1_xboole_0(B_113,A_114)
      | ~ r1_xboole_0(A_114,B_113) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_896,plain,(
    ! [B_14,A_13] : r1_xboole_0(B_14,k4_xboole_0(A_13,B_14)) ),
    inference(resolution,[status(thm)],[c_16,c_893])).

tff(c_998,plain,(
    ! [A_123,B_124] :
      ( ~ r2_hidden(A_123,B_124)
      | ~ r1_xboole_0(k1_tarski(A_123),B_124) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_1003,plain,(
    ! [A_123,A_13] : ~ r2_hidden(A_123,k4_xboole_0(A_13,k1_tarski(A_123))) ),
    inference(resolution,[status(thm)],[c_896,c_998])).

tff(c_1065,plain,(
    ~ r2_hidden('#skF_4','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1061,c_1003])).

tff(c_1076,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_891,c_1065])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n018.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 18:58:12 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.58/1.41  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.58/1.41  
% 2.58/1.41  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.58/1.42  %$ r2_hidden > r1_xboole_0 > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.58/1.42  
% 2.58/1.42  %Foreground sorts:
% 2.58/1.42  
% 2.58/1.42  
% 2.58/1.42  %Background operators:
% 2.58/1.42  
% 2.58/1.42  
% 2.58/1.42  %Foreground operators:
% 2.58/1.42  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.58/1.42  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.58/1.42  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.58/1.42  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.58/1.42  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.58/1.42  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.58/1.42  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.58/1.42  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.58/1.42  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.58/1.42  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.58/1.42  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.58/1.42  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.58/1.42  tff('#skF_2', type, '#skF_2': $i).
% 2.58/1.42  tff('#skF_3', type, '#skF_3': $i).
% 2.58/1.42  tff('#skF_1', type, '#skF_1': $i).
% 2.58/1.42  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.58/1.42  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.58/1.42  tff('#skF_4', type, '#skF_4': $i).
% 2.58/1.42  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.58/1.42  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.58/1.42  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.58/1.42  
% 2.91/1.43  tff(f_75, negated_conjecture, ~(![A, B]: ((k4_xboole_0(A, k1_tarski(B)) = A) <=> ~r2_hidden(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_zfmisc_1)).
% 2.91/1.43  tff(f_67, axiom, (![A, B]: (~r2_hidden(A, B) => r1_xboole_0(k1_tarski(A), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 2.91/1.43  tff(f_43, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 2.91/1.43  tff(f_39, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.91/1.43  tff(f_37, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 2.91/1.43  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 2.91/1.43  tff(f_33, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 2.91/1.43  tff(f_41, axiom, (![A, B]: (k2_xboole_0(k3_xboole_0(A, B), k4_xboole_0(A, B)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t51_xboole_1)).
% 2.91/1.43  tff(f_49, axiom, (![A, B, C]: (r1_xboole_0(A, B) => (k2_xboole_0(k4_xboole_0(C, A), B) = k4_xboole_0(k2_xboole_0(C, B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t87_xboole_1)).
% 2.91/1.43  tff(f_45, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_xboole_1)).
% 2.91/1.43  tff(f_31, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 2.91/1.43  tff(f_62, axiom, (![A, B]: ~(r1_xboole_0(k1_tarski(A), B) & r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l24_zfmisc_1)).
% 2.91/1.43  tff(c_36, plain, (~r2_hidden('#skF_2', '#skF_1') | r2_hidden('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.91/1.43  tff(c_61, plain, (~r2_hidden('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_36])).
% 2.91/1.43  tff(c_30, plain, (![A_30, B_31]: (r1_xboole_0(k1_tarski(A_30), B_31) | r2_hidden(A_30, B_31))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.91/1.43  tff(c_14, plain, (![A_12]: (k5_xboole_0(A_12, k1_xboole_0)=A_12)), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.91/1.43  tff(c_10, plain, (![A_9]: (r1_tarski(k1_xboole_0, A_9))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.91/1.43  tff(c_147, plain, (![A_52, B_53]: (k3_xboole_0(A_52, B_53)=A_52 | ~r1_tarski(A_52, B_53))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.91/1.43  tff(c_152, plain, (![A_54]: (k3_xboole_0(k1_xboole_0, A_54)=k1_xboole_0)), inference(resolution, [status(thm)], [c_10, c_147])).
% 2.91/1.43  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.91/1.43  tff(c_157, plain, (![A_54]: (k3_xboole_0(A_54, k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_152, c_2])).
% 2.91/1.43  tff(c_229, plain, (![A_62, B_63]: (k5_xboole_0(A_62, k3_xboole_0(A_62, B_63))=k4_xboole_0(A_62, B_63))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.91/1.43  tff(c_238, plain, (![A_54]: (k5_xboole_0(A_54, k1_xboole_0)=k4_xboole_0(A_54, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_157, c_229])).
% 2.91/1.43  tff(c_250, plain, (![A_54]: (k4_xboole_0(A_54, k1_xboole_0)=A_54)), inference(demodulation, [status(thm), theory('equality')], [c_14, c_238])).
% 2.91/1.43  tff(c_311, plain, (![A_69, B_70]: (k2_xboole_0(k3_xboole_0(A_69, B_70), k4_xboole_0(A_69, B_70))=A_69)), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.91/1.43  tff(c_326, plain, (![A_54]: (k2_xboole_0(k1_xboole_0, k4_xboole_0(A_54, k1_xboole_0))=A_54)), inference(superposition, [status(thm), theory('equality')], [c_157, c_311])).
% 2.91/1.43  tff(c_340, plain, (![A_54]: (k2_xboole_0(k1_xboole_0, A_54)=A_54)), inference(demodulation, [status(thm), theory('equality')], [c_250, c_326])).
% 2.91/1.43  tff(c_151, plain, (![A_9]: (k3_xboole_0(k1_xboole_0, A_9)=k1_xboole_0)), inference(resolution, [status(thm)], [c_10, c_147])).
% 2.91/1.43  tff(c_241, plain, (![A_9]: (k5_xboole_0(k1_xboole_0, k1_xboole_0)=k4_xboole_0(k1_xboole_0, A_9))), inference(superposition, [status(thm), theory('equality')], [c_151, c_229])).
% 2.91/1.43  tff(c_251, plain, (![A_9]: (k4_xboole_0(k1_xboole_0, A_9)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_14, c_241])).
% 2.91/1.43  tff(c_457, plain, (![C_85, B_86, A_87]: (k4_xboole_0(k2_xboole_0(C_85, B_86), A_87)=k2_xboole_0(k4_xboole_0(C_85, A_87), B_86) | ~r1_xboole_0(A_87, B_86))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.91/1.43  tff(c_489, plain, (![A_87, A_54]: (k2_xboole_0(k4_xboole_0(k1_xboole_0, A_87), A_54)=k4_xboole_0(A_54, A_87) | ~r1_xboole_0(A_87, A_54))), inference(superposition, [status(thm), theory('equality')], [c_340, c_457])).
% 2.91/1.43  tff(c_507, plain, (![A_88, A_89]: (k4_xboole_0(A_88, A_89)=A_88 | ~r1_xboole_0(A_89, A_88))), inference(demodulation, [status(thm), theory('equality')], [c_340, c_251, c_489])).
% 2.91/1.43  tff(c_658, plain, (![B_94, A_95]: (k4_xboole_0(B_94, k1_tarski(A_95))=B_94 | r2_hidden(A_95, B_94))), inference(resolution, [status(thm)], [c_30, c_507])).
% 2.91/1.43  tff(c_34, plain, (k4_xboole_0('#skF_1', k1_tarski('#skF_2'))!='#skF_1' | r2_hidden('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.91/1.43  tff(c_104, plain, (k4_xboole_0('#skF_1', k1_tarski('#skF_2'))!='#skF_1'), inference(splitLeft, [status(thm)], [c_34])).
% 2.91/1.43  tff(c_691, plain, (r2_hidden('#skF_2', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_658, c_104])).
% 2.91/1.43  tff(c_722, plain, $false, inference(negUnitSimplification, [status(thm)], [c_61, c_691])).
% 2.91/1.43  tff(c_723, plain, (r2_hidden('#skF_4', '#skF_3')), inference(splitRight, [status(thm)], [c_34])).
% 2.91/1.43  tff(c_724, plain, (k4_xboole_0('#skF_1', k1_tarski('#skF_2'))='#skF_1'), inference(splitRight, [status(thm)], [c_34])).
% 2.91/1.43  tff(c_38, plain, (k4_xboole_0('#skF_1', k1_tarski('#skF_2'))!='#skF_1' | k4_xboole_0('#skF_3', k1_tarski('#skF_4'))='#skF_3'), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.91/1.43  tff(c_875, plain, (k4_xboole_0('#skF_3', k1_tarski('#skF_4'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_724, c_38])).
% 2.91/1.43  tff(c_16, plain, (![A_13, B_14]: (r1_xboole_0(k4_xboole_0(A_13, B_14), B_14))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.91/1.43  tff(c_95, plain, (![B_41, A_42]: (r1_xboole_0(B_41, A_42) | ~r1_xboole_0(A_42, B_41))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.91/1.43  tff(c_98, plain, (![B_14, A_13]: (r1_xboole_0(B_14, k4_xboole_0(A_13, B_14)))), inference(resolution, [status(thm)], [c_16, c_95])).
% 2.91/1.43  tff(c_838, plain, (![A_105, B_106]: (~r2_hidden(A_105, B_106) | ~r1_xboole_0(k1_tarski(A_105), B_106))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.91/1.43  tff(c_851, plain, (![A_105, A_13]: (~r2_hidden(A_105, k4_xboole_0(A_13, k1_tarski(A_105))))), inference(resolution, [status(thm)], [c_98, c_838])).
% 2.91/1.43  tff(c_879, plain, (~r2_hidden('#skF_4', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_875, c_851])).
% 2.91/1.43  tff(c_890, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_723, c_879])).
% 2.91/1.43  tff(c_891, plain, (r2_hidden('#skF_4', '#skF_3')), inference(splitRight, [status(thm)], [c_36])).
% 2.91/1.43  tff(c_892, plain, (r2_hidden('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_36])).
% 2.91/1.43  tff(c_40, plain, (~r2_hidden('#skF_2', '#skF_1') | k4_xboole_0('#skF_3', k1_tarski('#skF_4'))='#skF_3'), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.91/1.43  tff(c_1061, plain, (k4_xboole_0('#skF_3', k1_tarski('#skF_4'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_892, c_40])).
% 2.91/1.43  tff(c_893, plain, (![B_113, A_114]: (r1_xboole_0(B_113, A_114) | ~r1_xboole_0(A_114, B_113))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.91/1.43  tff(c_896, plain, (![B_14, A_13]: (r1_xboole_0(B_14, k4_xboole_0(A_13, B_14)))), inference(resolution, [status(thm)], [c_16, c_893])).
% 2.91/1.43  tff(c_998, plain, (![A_123, B_124]: (~r2_hidden(A_123, B_124) | ~r1_xboole_0(k1_tarski(A_123), B_124))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.91/1.43  tff(c_1003, plain, (![A_123, A_13]: (~r2_hidden(A_123, k4_xboole_0(A_13, k1_tarski(A_123))))), inference(resolution, [status(thm)], [c_896, c_998])).
% 2.91/1.43  tff(c_1065, plain, (~r2_hidden('#skF_4', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1061, c_1003])).
% 2.91/1.43  tff(c_1076, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_891, c_1065])).
% 2.91/1.43  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.91/1.43  
% 2.91/1.43  Inference rules
% 2.91/1.43  ----------------------
% 2.91/1.43  #Ref     : 0
% 2.91/1.43  #Sup     : 249
% 2.91/1.43  #Fact    : 0
% 2.91/1.43  #Define  : 0
% 2.91/1.43  #Split   : 2
% 2.91/1.43  #Chain   : 0
% 2.91/1.43  #Close   : 0
% 2.91/1.43  
% 2.91/1.43  Ordering : KBO
% 2.91/1.43  
% 2.91/1.43  Simplification rules
% 2.91/1.43  ----------------------
% 2.91/1.43  #Subsume      : 10
% 2.91/1.43  #Demod        : 92
% 2.91/1.43  #Tautology    : 171
% 2.91/1.43  #SimpNegUnit  : 3
% 2.91/1.43  #BackRed      : 0
% 2.91/1.43  
% 2.91/1.43  #Partial instantiations: 0
% 2.91/1.43  #Strategies tried      : 1
% 2.91/1.43  
% 2.91/1.43  Timing (in seconds)
% 2.91/1.43  ----------------------
% 2.91/1.44  Preprocessing        : 0.30
% 2.91/1.44  Parsing              : 0.15
% 2.91/1.44  CNF conversion       : 0.02
% 2.91/1.44  Main loop            : 0.32
% 2.91/1.44  Inferencing          : 0.13
% 2.91/1.44  Reduction            : 0.10
% 2.91/1.44  Demodulation         : 0.08
% 2.91/1.44  BG Simplification    : 0.02
% 2.91/1.44  Subsumption          : 0.04
% 2.91/1.44  Abstraction          : 0.02
% 2.91/1.44  MUC search           : 0.00
% 2.91/1.44  Cooper               : 0.00
% 2.91/1.44  Total                : 0.65
% 2.91/1.44  Index Insertion      : 0.00
% 2.91/1.44  Index Deletion       : 0.00
% 2.91/1.44  Index Matching       : 0.00
% 2.91/1.44  BG Taut test         : 0.00
%------------------------------------------------------------------------------
