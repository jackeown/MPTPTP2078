%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:53:03 EST 2020

% Result     : Theorem 3.27s
% Output     : CNFRefutation 3.27s
% Verified   : 
% Statistics : Number of formulae       :   76 ( 100 expanded)
%              Number of leaves         :   31 (  46 expanded)
%              Depth                    :    9
%              Number of atoms          :   72 ( 108 expanded)
%              Number of equality atoms :   40 (  62 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(f_66,negated_conjecture,(
    ~ ! [A,B] :
        ( k4_xboole_0(k1_tarski(A),B) = k1_xboole_0
      <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t68_zfmisc_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_35,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

tff(f_31,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k5_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

tff(f_39,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_37,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_41,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_61,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_tarski(A,B),C)
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_zfmisc_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => k3_xboole_0(B,k1_tarski(A)) = k1_tarski(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l31_zfmisc_1)).

tff(c_38,plain,
    ( r2_hidden('#skF_1','#skF_2')
    | ~ r2_hidden('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_214,plain,(
    ~ r2_hidden('#skF_3','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_38])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_10,plain,(
    ! [A_9] : k5_xboole_0(A_9,k1_xboole_0) = A_9 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_42,plain,
    ( r2_hidden('#skF_1','#skF_2')
    | k4_xboole_0(k1_tarski('#skF_3'),'#skF_4') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_268,plain,(
    k4_xboole_0(k1_tarski('#skF_3'),'#skF_4') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_42])).

tff(c_6,plain,(
    ! [A_5,B_6] : k5_xboole_0(A_5,k3_xboole_0(A_5,B_6)) = k4_xboole_0(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_79,plain,(
    ! [B_45,A_46] : k5_xboole_0(B_45,A_46) = k5_xboole_0(A_46,B_45) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_95,plain,(
    ! [A_46] : k5_xboole_0(k1_xboole_0,A_46) = A_46 ),
    inference(superposition,[status(thm),theory(equality)],[c_79,c_10])).

tff(c_14,plain,(
    ! [A_13] : k5_xboole_0(A_13,A_13) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_445,plain,(
    ! [A_81,B_82,C_83] : k5_xboole_0(k5_xboole_0(A_81,B_82),C_83) = k5_xboole_0(A_81,k5_xboole_0(B_82,C_83)) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_520,plain,(
    ! [A_13,C_83] : k5_xboole_0(A_13,k5_xboole_0(A_13,C_83)) = k5_xboole_0(k1_xboole_0,C_83) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_445])).

tff(c_534,plain,(
    ! [A_84,C_85] : k5_xboole_0(A_84,k5_xboole_0(A_84,C_85)) = C_85 ),
    inference(demodulation,[status(thm),theory(equality)],[c_95,c_520])).

tff(c_937,plain,(
    ! [A_104,B_105] : k5_xboole_0(A_104,k4_xboole_0(A_104,B_105)) = k3_xboole_0(A_104,B_105) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_534])).

tff(c_979,plain,(
    k5_xboole_0(k1_tarski('#skF_3'),k1_xboole_0) = k3_xboole_0(k1_tarski('#skF_3'),'#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_268,c_937])).

tff(c_992,plain,(
    k3_xboole_0('#skF_4',k1_tarski('#skF_3')) = k1_tarski('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_10,c_979])).

tff(c_8,plain,(
    ! [A_7,B_8] : r1_tarski(k3_xboole_0(A_7,B_8),A_7) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_1010,plain,(
    r1_tarski(k1_tarski('#skF_3'),'#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_992,c_8])).

tff(c_16,plain,(
    ! [A_14] : k2_tarski(A_14,A_14) = k1_tarski(A_14) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_273,plain,(
    ! [A_57,C_58,B_59] :
      ( r2_hidden(A_57,C_58)
      | ~ r1_tarski(k2_tarski(A_57,B_59),C_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_276,plain,(
    ! [A_14,C_58] :
      ( r2_hidden(A_14,C_58)
      | ~ r1_tarski(k1_tarski(A_14),C_58) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_273])).

tff(c_1020,plain,(
    r2_hidden('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_1010,c_276])).

tff(c_1024,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_214,c_1020])).

tff(c_1025,plain,(
    r2_hidden('#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_1098,plain,(
    ! [B_120,A_121] :
      ( k3_xboole_0(B_120,k1_tarski(A_121)) = k1_tarski(A_121)
      | ~ r2_hidden(A_121,B_120) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_235,plain,(
    ! [A_54,B_55] : k5_xboole_0(A_54,k3_xboole_0(A_54,B_55)) = k4_xboole_0(A_54,B_55) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_255,plain,(
    ! [B_2,A_1] : k5_xboole_0(B_2,k3_xboole_0(A_1,B_2)) = k4_xboole_0(B_2,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_235])).

tff(c_1104,plain,(
    ! [A_121,B_120] :
      ( k5_xboole_0(k1_tarski(A_121),k1_tarski(A_121)) = k4_xboole_0(k1_tarski(A_121),B_120)
      | ~ r2_hidden(A_121,B_120) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1098,c_255])).

tff(c_1631,plain,(
    ! [A_147,B_148] :
      ( k4_xboole_0(k1_tarski(A_147),B_148) = k1_xboole_0
      | ~ r2_hidden(A_147,B_148) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_1104])).

tff(c_1026,plain,(
    k4_xboole_0(k1_tarski('#skF_3'),'#skF_4') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_40,plain,
    ( k4_xboole_0(k1_tarski('#skF_1'),'#skF_2') != k1_xboole_0
    | k4_xboole_0(k1_tarski('#skF_3'),'#skF_4') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_1071,plain,(
    k4_xboole_0(k1_tarski('#skF_1'),'#skF_2') != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_1026,c_40])).

tff(c_1637,plain,(
    ~ r2_hidden('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_1631,c_1071])).

tff(c_1648,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1025,c_1637])).

tff(c_1649,plain,(
    r2_hidden('#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_38])).

tff(c_1777,plain,(
    ! [B_170,A_171] :
      ( k3_xboole_0(B_170,k1_tarski(A_171)) = k1_tarski(A_171)
      | ~ r2_hidden(A_171,B_170) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_1683,plain,(
    ! [A_161,B_162] : k5_xboole_0(A_161,k3_xboole_0(A_161,B_162)) = k4_xboole_0(A_161,B_162) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_1700,plain,(
    ! [A_1,B_2] : k5_xboole_0(A_1,k3_xboole_0(B_2,A_1)) = k4_xboole_0(A_1,B_2) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_1683])).

tff(c_1783,plain,(
    ! [A_171,B_170] :
      ( k5_xboole_0(k1_tarski(A_171),k1_tarski(A_171)) = k4_xboole_0(k1_tarski(A_171),B_170)
      | ~ r2_hidden(A_171,B_170) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1777,c_1700])).

tff(c_1818,plain,(
    ! [A_174,B_175] :
      ( k4_xboole_0(k1_tarski(A_174),B_175) = k1_xboole_0
      | ~ r2_hidden(A_174,B_175) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_1783])).

tff(c_1650,plain,(
    r2_hidden('#skF_3','#skF_4') ),
    inference(splitRight,[status(thm)],[c_38])).

tff(c_36,plain,
    ( k4_xboole_0(k1_tarski('#skF_1'),'#skF_2') != k1_xboole_0
    | ~ r2_hidden('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_1676,plain,(
    k4_xboole_0(k1_tarski('#skF_1'),'#skF_2') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1650,c_36])).

tff(c_1824,plain,(
    ~ r2_hidden('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_1818,c_1676])).

tff(c_1832,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1649,c_1824])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n016.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 17:32:04 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.27/1.51  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.27/1.51  
% 3.27/1.51  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.27/1.52  %$ r2_hidden > r1_tarski > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 3.27/1.52  
% 3.27/1.52  %Foreground sorts:
% 3.27/1.52  
% 3.27/1.52  
% 3.27/1.52  %Background operators:
% 3.27/1.52  
% 3.27/1.52  
% 3.27/1.52  %Foreground operators:
% 3.27/1.52  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.27/1.52  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.27/1.52  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.27/1.52  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.27/1.52  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.27/1.52  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.27/1.52  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.27/1.52  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.27/1.52  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.27/1.52  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.27/1.52  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.27/1.52  tff('#skF_2', type, '#skF_2': $i).
% 3.27/1.52  tff('#skF_3', type, '#skF_3': $i).
% 3.27/1.52  tff('#skF_1', type, '#skF_1': $i).
% 3.27/1.52  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.27/1.52  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.27/1.52  tff('#skF_4', type, '#skF_4': $i).
% 3.27/1.52  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.27/1.52  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.27/1.52  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.27/1.52  
% 3.27/1.53  tff(f_66, negated_conjecture, ~(![A, B]: ((k4_xboole_0(k1_tarski(A), B) = k1_xboole_0) <=> r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t68_zfmisc_1)).
% 3.27/1.53  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 3.27/1.53  tff(f_35, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 3.27/1.53  tff(f_31, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 3.27/1.53  tff(f_29, axiom, (![A, B]: (k5_xboole_0(A, B) = k5_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 3.27/1.53  tff(f_39, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t92_xboole_1)).
% 3.27/1.53  tff(f_37, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_xboole_1)).
% 3.27/1.53  tff(f_33, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 3.27/1.53  tff(f_41, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 3.27/1.53  tff(f_61, axiom, (![A, B, C]: (r1_tarski(k2_tarski(A, B), C) <=> (r2_hidden(A, C) & r2_hidden(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 3.27/1.53  tff(f_55, axiom, (![A, B]: (r2_hidden(A, B) => (k3_xboole_0(B, k1_tarski(A)) = k1_tarski(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l31_zfmisc_1)).
% 3.27/1.53  tff(c_38, plain, (r2_hidden('#skF_1', '#skF_2') | ~r2_hidden('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.27/1.53  tff(c_214, plain, (~r2_hidden('#skF_3', '#skF_4')), inference(splitLeft, [status(thm)], [c_38])).
% 3.27/1.53  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.27/1.53  tff(c_10, plain, (![A_9]: (k5_xboole_0(A_9, k1_xboole_0)=A_9)), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.27/1.53  tff(c_42, plain, (r2_hidden('#skF_1', '#skF_2') | k4_xboole_0(k1_tarski('#skF_3'), '#skF_4')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.27/1.53  tff(c_268, plain, (k4_xboole_0(k1_tarski('#skF_3'), '#skF_4')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_42])).
% 3.27/1.53  tff(c_6, plain, (![A_5, B_6]: (k5_xboole_0(A_5, k3_xboole_0(A_5, B_6))=k4_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.27/1.53  tff(c_79, plain, (![B_45, A_46]: (k5_xboole_0(B_45, A_46)=k5_xboole_0(A_46, B_45))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.27/1.53  tff(c_95, plain, (![A_46]: (k5_xboole_0(k1_xboole_0, A_46)=A_46)), inference(superposition, [status(thm), theory('equality')], [c_79, c_10])).
% 3.27/1.53  tff(c_14, plain, (![A_13]: (k5_xboole_0(A_13, A_13)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.27/1.53  tff(c_445, plain, (![A_81, B_82, C_83]: (k5_xboole_0(k5_xboole_0(A_81, B_82), C_83)=k5_xboole_0(A_81, k5_xboole_0(B_82, C_83)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.27/1.53  tff(c_520, plain, (![A_13, C_83]: (k5_xboole_0(A_13, k5_xboole_0(A_13, C_83))=k5_xboole_0(k1_xboole_0, C_83))), inference(superposition, [status(thm), theory('equality')], [c_14, c_445])).
% 3.27/1.53  tff(c_534, plain, (![A_84, C_85]: (k5_xboole_0(A_84, k5_xboole_0(A_84, C_85))=C_85)), inference(demodulation, [status(thm), theory('equality')], [c_95, c_520])).
% 3.27/1.53  tff(c_937, plain, (![A_104, B_105]: (k5_xboole_0(A_104, k4_xboole_0(A_104, B_105))=k3_xboole_0(A_104, B_105))), inference(superposition, [status(thm), theory('equality')], [c_6, c_534])).
% 3.27/1.53  tff(c_979, plain, (k5_xboole_0(k1_tarski('#skF_3'), k1_xboole_0)=k3_xboole_0(k1_tarski('#skF_3'), '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_268, c_937])).
% 3.27/1.53  tff(c_992, plain, (k3_xboole_0('#skF_4', k1_tarski('#skF_3'))=k1_tarski('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_10, c_979])).
% 3.27/1.53  tff(c_8, plain, (![A_7, B_8]: (r1_tarski(k3_xboole_0(A_7, B_8), A_7))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.27/1.53  tff(c_1010, plain, (r1_tarski(k1_tarski('#skF_3'), '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_992, c_8])).
% 3.27/1.53  tff(c_16, plain, (![A_14]: (k2_tarski(A_14, A_14)=k1_tarski(A_14))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.27/1.53  tff(c_273, plain, (![A_57, C_58, B_59]: (r2_hidden(A_57, C_58) | ~r1_tarski(k2_tarski(A_57, B_59), C_58))), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.27/1.53  tff(c_276, plain, (![A_14, C_58]: (r2_hidden(A_14, C_58) | ~r1_tarski(k1_tarski(A_14), C_58))), inference(superposition, [status(thm), theory('equality')], [c_16, c_273])).
% 3.27/1.53  tff(c_1020, plain, (r2_hidden('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_1010, c_276])).
% 3.27/1.53  tff(c_1024, plain, $false, inference(negUnitSimplification, [status(thm)], [c_214, c_1020])).
% 3.27/1.53  tff(c_1025, plain, (r2_hidden('#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_42])).
% 3.27/1.53  tff(c_1098, plain, (![B_120, A_121]: (k3_xboole_0(B_120, k1_tarski(A_121))=k1_tarski(A_121) | ~r2_hidden(A_121, B_120))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.27/1.53  tff(c_235, plain, (![A_54, B_55]: (k5_xboole_0(A_54, k3_xboole_0(A_54, B_55))=k4_xboole_0(A_54, B_55))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.27/1.53  tff(c_255, plain, (![B_2, A_1]: (k5_xboole_0(B_2, k3_xboole_0(A_1, B_2))=k4_xboole_0(B_2, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_235])).
% 3.27/1.53  tff(c_1104, plain, (![A_121, B_120]: (k5_xboole_0(k1_tarski(A_121), k1_tarski(A_121))=k4_xboole_0(k1_tarski(A_121), B_120) | ~r2_hidden(A_121, B_120))), inference(superposition, [status(thm), theory('equality')], [c_1098, c_255])).
% 3.27/1.53  tff(c_1631, plain, (![A_147, B_148]: (k4_xboole_0(k1_tarski(A_147), B_148)=k1_xboole_0 | ~r2_hidden(A_147, B_148))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_1104])).
% 3.27/1.53  tff(c_1026, plain, (k4_xboole_0(k1_tarski('#skF_3'), '#skF_4')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_42])).
% 3.27/1.53  tff(c_40, plain, (k4_xboole_0(k1_tarski('#skF_1'), '#skF_2')!=k1_xboole_0 | k4_xboole_0(k1_tarski('#skF_3'), '#skF_4')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.27/1.53  tff(c_1071, plain, (k4_xboole_0(k1_tarski('#skF_1'), '#skF_2')!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_1026, c_40])).
% 3.27/1.53  tff(c_1637, plain, (~r2_hidden('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_1631, c_1071])).
% 3.27/1.53  tff(c_1648, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1025, c_1637])).
% 3.27/1.53  tff(c_1649, plain, (r2_hidden('#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_38])).
% 3.27/1.53  tff(c_1777, plain, (![B_170, A_171]: (k3_xboole_0(B_170, k1_tarski(A_171))=k1_tarski(A_171) | ~r2_hidden(A_171, B_170))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.27/1.53  tff(c_1683, plain, (![A_161, B_162]: (k5_xboole_0(A_161, k3_xboole_0(A_161, B_162))=k4_xboole_0(A_161, B_162))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.27/1.53  tff(c_1700, plain, (![A_1, B_2]: (k5_xboole_0(A_1, k3_xboole_0(B_2, A_1))=k4_xboole_0(A_1, B_2))), inference(superposition, [status(thm), theory('equality')], [c_2, c_1683])).
% 3.27/1.53  tff(c_1783, plain, (![A_171, B_170]: (k5_xboole_0(k1_tarski(A_171), k1_tarski(A_171))=k4_xboole_0(k1_tarski(A_171), B_170) | ~r2_hidden(A_171, B_170))), inference(superposition, [status(thm), theory('equality')], [c_1777, c_1700])).
% 3.27/1.53  tff(c_1818, plain, (![A_174, B_175]: (k4_xboole_0(k1_tarski(A_174), B_175)=k1_xboole_0 | ~r2_hidden(A_174, B_175))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_1783])).
% 3.27/1.53  tff(c_1650, plain, (r2_hidden('#skF_3', '#skF_4')), inference(splitRight, [status(thm)], [c_38])).
% 3.27/1.53  tff(c_36, plain, (k4_xboole_0(k1_tarski('#skF_1'), '#skF_2')!=k1_xboole_0 | ~r2_hidden('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.27/1.53  tff(c_1676, plain, (k4_xboole_0(k1_tarski('#skF_1'), '#skF_2')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_1650, c_36])).
% 3.27/1.53  tff(c_1824, plain, (~r2_hidden('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_1818, c_1676])).
% 3.27/1.53  tff(c_1832, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1649, c_1824])).
% 3.27/1.53  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.27/1.53  
% 3.27/1.53  Inference rules
% 3.27/1.53  ----------------------
% 3.27/1.53  #Ref     : 0
% 3.27/1.53  #Sup     : 438
% 3.27/1.53  #Fact    : 0
% 3.27/1.53  #Define  : 0
% 3.27/1.53  #Split   : 2
% 3.27/1.53  #Chain   : 0
% 3.27/1.53  #Close   : 0
% 3.27/1.53  
% 3.27/1.53  Ordering : KBO
% 3.27/1.53  
% 3.27/1.53  Simplification rules
% 3.27/1.53  ----------------------
% 3.27/1.53  #Subsume      : 32
% 3.27/1.53  #Demod        : 184
% 3.27/1.53  #Tautology    : 286
% 3.27/1.53  #SimpNegUnit  : 2
% 3.27/1.53  #BackRed      : 0
% 3.27/1.53  
% 3.27/1.53  #Partial instantiations: 0
% 3.27/1.53  #Strategies tried      : 1
% 3.27/1.53  
% 3.27/1.53  Timing (in seconds)
% 3.27/1.53  ----------------------
% 3.42/1.53  Preprocessing        : 0.31
% 3.42/1.53  Parsing              : 0.17
% 3.42/1.53  CNF conversion       : 0.02
% 3.42/1.53  Main loop            : 0.45
% 3.42/1.53  Inferencing          : 0.17
% 3.42/1.53  Reduction            : 0.17
% 3.42/1.53  Demodulation         : 0.14
% 3.42/1.53  BG Simplification    : 0.02
% 3.42/1.53  Subsumption          : 0.06
% 3.42/1.53  Abstraction          : 0.03
% 3.42/1.53  MUC search           : 0.00
% 3.42/1.53  Cooper               : 0.00
% 3.42/1.53  Total                : 0.79
% 3.42/1.53  Index Insertion      : 0.00
% 3.42/1.53  Index Deletion       : 0.00
% 3.42/1.53  Index Matching       : 0.00
% 3.42/1.53  BG Taut test         : 0.00
%------------------------------------------------------------------------------
