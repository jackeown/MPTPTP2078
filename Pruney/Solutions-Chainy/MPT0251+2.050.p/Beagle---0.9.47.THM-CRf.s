%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:50:53 EST 2020

% Result     : Theorem 2.88s
% Output     : CNFRefutation 3.04s
% Verified   : 
% Statistics : Number of formulae       :   76 ( 200 expanded)
%              Number of leaves         :   30 (  79 expanded)
%              Depth                    :   16
%              Number of atoms          :   71 ( 201 expanded)
%              Number of equality atoms :   50 ( 172 expanded)
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

tff(f_49,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_63,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_41,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_47,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_45,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_43,axiom,(
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

tff(c_22,plain,(
    ! [B_17,A_16] : k2_tarski(B_17,A_16) = k2_tarski(A_16,B_17) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_99,plain,(
    ! [A_39,B_40] : k3_tarski(k2_tarski(A_39,B_40)) = k2_xboole_0(A_39,B_40) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_241,plain,(
    ! [B_59,A_60] : k3_tarski(k2_tarski(B_59,A_60)) = k2_xboole_0(A_60,B_59) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_99])).

tff(c_36,plain,(
    ! [A_30,B_31] : k3_tarski(k2_tarski(A_30,B_31)) = k2_xboole_0(A_30,B_31) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_268,plain,(
    ! [B_61,A_62] : k2_xboole_0(B_61,A_62) = k2_xboole_0(A_62,B_61) ),
    inference(superposition,[status(thm),theory(equality)],[c_241,c_36])).

tff(c_304,plain,(
    ! [A_62] : k2_xboole_0(k1_xboole_0,A_62) = A_62 ),
    inference(superposition,[status(thm),theory(equality)],[c_268,c_10])).

tff(c_378,plain,(
    ! [A_64,B_65] : k2_xboole_0(A_64,k4_xboole_0(B_65,A_64)) = k2_xboole_0(A_64,B_65) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_385,plain,(
    ! [B_65] : k4_xboole_0(B_65,k1_xboole_0) = k2_xboole_0(k1_xboole_0,B_65) ),
    inference(superposition,[status(thm),theory(equality)],[c_378,c_304])).

tff(c_404,plain,(
    ! [B_65] : k4_xboole_0(B_65,k1_xboole_0) = B_65 ),
    inference(demodulation,[status(thm),theory(equality)],[c_304,c_385])).

tff(c_470,plain,(
    ! [A_69,B_70] : k5_xboole_0(A_69,k4_xboole_0(B_70,A_69)) = k2_xboole_0(A_69,B_70) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_479,plain,(
    ! [B_65] : k5_xboole_0(k1_xboole_0,B_65) = k2_xboole_0(k1_xboole_0,B_65) ),
    inference(superposition,[status(thm),theory(equality)],[c_404,c_470])).

tff(c_482,plain,(
    ! [B_65] : k5_xboole_0(k1_xboole_0,B_65) = B_65 ),
    inference(demodulation,[status(thm),theory(equality)],[c_304,c_479])).

tff(c_335,plain,(
    ! [A_63] : k2_xboole_0(k1_xboole_0,A_63) = A_63 ),
    inference(superposition,[status(thm),theory(equality)],[c_268,c_10])).

tff(c_18,plain,(
    ! [A_12,B_13] : r1_tarski(A_12,k2_xboole_0(A_12,B_13)) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_137,plain,(
    ! [A_42,B_43] :
      ( k3_xboole_0(A_42,B_43) = A_42
      | ~ r1_tarski(A_42,B_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_144,plain,(
    ! [A_12,B_13] : k3_xboole_0(A_12,k2_xboole_0(A_12,B_13)) = A_12 ),
    inference(resolution,[status(thm)],[c_18,c_137])).

tff(c_347,plain,(
    ! [A_63] : k3_xboole_0(k1_xboole_0,A_63) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_335,c_144])).

tff(c_650,plain,(
    ! [A_81,B_82] : k5_xboole_0(A_81,k3_xboole_0(A_81,B_82)) = k4_xboole_0(A_81,B_82) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_670,plain,(
    ! [A_63] : k5_xboole_0(k1_xboole_0,k1_xboole_0) = k4_xboole_0(k1_xboole_0,A_63) ),
    inference(superposition,[status(thm),theory(equality)],[c_347,c_650])).

tff(c_685,plain,(
    ! [A_83] : k4_xboole_0(k1_xboole_0,A_83) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_482,c_670])).

tff(c_20,plain,(
    ! [A_14,B_15] : k5_xboole_0(A_14,k4_xboole_0(B_15,A_14)) = k2_xboole_0(A_14,B_15) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_690,plain,(
    ! [A_83] : k5_xboole_0(A_83,k1_xboole_0) = k2_xboole_0(A_83,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_685,c_20])).

tff(c_705,plain,(
    ! [A_83] : k5_xboole_0(A_83,k1_xboole_0) = A_83 ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_690])).

tff(c_684,plain,(
    ! [A_63] : k4_xboole_0(k1_xboole_0,A_63) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_482,c_670])).

tff(c_712,plain,(
    ! [A_84,B_85] : k4_xboole_0(k2_xboole_0(A_84,B_85),B_85) = k4_xboole_0(A_84,B_85) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_738,plain,(
    ! [A_62] : k4_xboole_0(k1_xboole_0,A_62) = k4_xboole_0(A_62,A_62) ),
    inference(superposition,[status(thm),theory(equality)],[c_304,c_712])).

tff(c_757,plain,(
    ! [A_62] : k4_xboole_0(A_62,A_62) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_684,c_738])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_145,plain,(
    ! [B_2] : k3_xboole_0(B_2,B_2) = B_2 ),
    inference(resolution,[status(thm)],[c_6,c_137])).

tff(c_679,plain,(
    ! [B_2] : k5_xboole_0(B_2,B_2) = k4_xboole_0(B_2,B_2) ),
    inference(superposition,[status(thm),theory(equality)],[c_145,c_650])).

tff(c_885,plain,(
    ! [B_2] : k5_xboole_0(B_2,B_2) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_757,c_679])).

tff(c_230,plain,(
    ! [A_56,B_57] :
      ( r1_tarski(k1_tarski(A_56),B_57)
      | ~ r2_hidden(A_56,B_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_12,plain,(
    ! [A_6,B_7] :
      ( k3_xboole_0(A_6,B_7) = A_6
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_1493,plain,(
    ! [A_115,B_116] :
      ( k3_xboole_0(k1_tarski(A_115),B_116) = k1_tarski(A_115)
      | ~ r2_hidden(A_115,B_116) ) ),
    inference(resolution,[status(thm)],[c_230,c_12])).

tff(c_8,plain,(
    ! [A_3,B_4] : k5_xboole_0(A_3,k3_xboole_0(A_3,B_4)) = k4_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_1499,plain,(
    ! [A_115,B_116] :
      ( k5_xboole_0(k1_tarski(A_115),k1_tarski(A_115)) = k4_xboole_0(k1_tarski(A_115),B_116)
      | ~ r2_hidden(A_115,B_116) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1493,c_8])).

tff(c_1623,plain,(
    ! [A_119,B_120] :
      ( k4_xboole_0(k1_tarski(A_119),B_120) = k1_xboole_0
      | ~ r2_hidden(A_119,B_120) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_885,c_1499])).

tff(c_1650,plain,(
    ! [B_120,A_119] :
      ( k2_xboole_0(B_120,k1_tarski(A_119)) = k5_xboole_0(B_120,k1_xboole_0)
      | ~ r2_hidden(A_119,B_120) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1623,c_20])).

tff(c_1839,plain,(
    ! [B_123,A_124] :
      ( k2_xboole_0(B_123,k1_tarski(A_124)) = B_123
      | ~ r2_hidden(A_124,B_123) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_705,c_1650])).

tff(c_247,plain,(
    ! [B_59,A_60] : k2_xboole_0(B_59,A_60) = k2_xboole_0(A_60,B_59) ),
    inference(superposition,[status(thm),theory(equality)],[c_241,c_36])).

tff(c_38,plain,(
    k2_xboole_0(k1_tarski('#skF_1'),'#skF_2') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_267,plain,(
    k2_xboole_0('#skF_2',k1_tarski('#skF_1')) != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_247,c_38])).

tff(c_1895,plain,(
    ~ r2_hidden('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_1839,c_267])).

tff(c_1956,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_1895])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:51:21 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.88/1.43  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.88/1.44  
% 2.88/1.44  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.88/1.44  %$ r2_hidden > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1
% 2.88/1.44  
% 2.88/1.44  %Foreground sorts:
% 2.88/1.44  
% 2.88/1.44  
% 2.88/1.44  %Background operators:
% 2.88/1.44  
% 2.88/1.44  
% 2.88/1.44  %Foreground operators:
% 2.88/1.44  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.88/1.44  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.88/1.44  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.88/1.44  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.88/1.44  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.88/1.44  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.88/1.44  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.88/1.44  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.88/1.44  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.88/1.44  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.88/1.44  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.88/1.44  tff('#skF_2', type, '#skF_2': $i).
% 2.88/1.44  tff('#skF_1', type, '#skF_1': $i).
% 2.88/1.44  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.88/1.44  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.88/1.44  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.88/1.44  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.88/1.44  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.88/1.44  
% 3.04/1.45  tff(f_68, negated_conjecture, ~(![A, B]: (r2_hidden(A, B) => (k2_xboole_0(k1_tarski(A), B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_zfmisc_1)).
% 3.04/1.45  tff(f_35, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 3.04/1.45  tff(f_49, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 3.04/1.45  tff(f_63, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 3.04/1.45  tff(f_41, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 3.04/1.45  tff(f_47, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_xboole_1)).
% 3.04/1.45  tff(f_45, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 3.04/1.45  tff(f_39, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 3.04/1.45  tff(f_33, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 3.04/1.45  tff(f_43, axiom, (![A, B]: (k4_xboole_0(k2_xboole_0(A, B), B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t40_xboole_1)).
% 3.04/1.45  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.04/1.45  tff(f_61, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 3.04/1.45  tff(c_40, plain, (r2_hidden('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.04/1.45  tff(c_10, plain, (![A_5]: (k2_xboole_0(A_5, k1_xboole_0)=A_5)), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.04/1.45  tff(c_22, plain, (![B_17, A_16]: (k2_tarski(B_17, A_16)=k2_tarski(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.04/1.45  tff(c_99, plain, (![A_39, B_40]: (k3_tarski(k2_tarski(A_39, B_40))=k2_xboole_0(A_39, B_40))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.04/1.45  tff(c_241, plain, (![B_59, A_60]: (k3_tarski(k2_tarski(B_59, A_60))=k2_xboole_0(A_60, B_59))), inference(superposition, [status(thm), theory('equality')], [c_22, c_99])).
% 3.04/1.45  tff(c_36, plain, (![A_30, B_31]: (k3_tarski(k2_tarski(A_30, B_31))=k2_xboole_0(A_30, B_31))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.04/1.45  tff(c_268, plain, (![B_61, A_62]: (k2_xboole_0(B_61, A_62)=k2_xboole_0(A_62, B_61))), inference(superposition, [status(thm), theory('equality')], [c_241, c_36])).
% 3.04/1.45  tff(c_304, plain, (![A_62]: (k2_xboole_0(k1_xboole_0, A_62)=A_62)), inference(superposition, [status(thm), theory('equality')], [c_268, c_10])).
% 3.04/1.45  tff(c_378, plain, (![A_64, B_65]: (k2_xboole_0(A_64, k4_xboole_0(B_65, A_64))=k2_xboole_0(A_64, B_65))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.04/1.45  tff(c_385, plain, (![B_65]: (k4_xboole_0(B_65, k1_xboole_0)=k2_xboole_0(k1_xboole_0, B_65))), inference(superposition, [status(thm), theory('equality')], [c_378, c_304])).
% 3.04/1.45  tff(c_404, plain, (![B_65]: (k4_xboole_0(B_65, k1_xboole_0)=B_65)), inference(demodulation, [status(thm), theory('equality')], [c_304, c_385])).
% 3.04/1.45  tff(c_470, plain, (![A_69, B_70]: (k5_xboole_0(A_69, k4_xboole_0(B_70, A_69))=k2_xboole_0(A_69, B_70))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.04/1.45  tff(c_479, plain, (![B_65]: (k5_xboole_0(k1_xboole_0, B_65)=k2_xboole_0(k1_xboole_0, B_65))), inference(superposition, [status(thm), theory('equality')], [c_404, c_470])).
% 3.04/1.45  tff(c_482, plain, (![B_65]: (k5_xboole_0(k1_xboole_0, B_65)=B_65)), inference(demodulation, [status(thm), theory('equality')], [c_304, c_479])).
% 3.04/1.45  tff(c_335, plain, (![A_63]: (k2_xboole_0(k1_xboole_0, A_63)=A_63)), inference(superposition, [status(thm), theory('equality')], [c_268, c_10])).
% 3.04/1.45  tff(c_18, plain, (![A_12, B_13]: (r1_tarski(A_12, k2_xboole_0(A_12, B_13)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.04/1.45  tff(c_137, plain, (![A_42, B_43]: (k3_xboole_0(A_42, B_43)=A_42 | ~r1_tarski(A_42, B_43))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.04/1.45  tff(c_144, plain, (![A_12, B_13]: (k3_xboole_0(A_12, k2_xboole_0(A_12, B_13))=A_12)), inference(resolution, [status(thm)], [c_18, c_137])).
% 3.04/1.45  tff(c_347, plain, (![A_63]: (k3_xboole_0(k1_xboole_0, A_63)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_335, c_144])).
% 3.04/1.45  tff(c_650, plain, (![A_81, B_82]: (k5_xboole_0(A_81, k3_xboole_0(A_81, B_82))=k4_xboole_0(A_81, B_82))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.04/1.45  tff(c_670, plain, (![A_63]: (k5_xboole_0(k1_xboole_0, k1_xboole_0)=k4_xboole_0(k1_xboole_0, A_63))), inference(superposition, [status(thm), theory('equality')], [c_347, c_650])).
% 3.04/1.45  tff(c_685, plain, (![A_83]: (k4_xboole_0(k1_xboole_0, A_83)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_482, c_670])).
% 3.04/1.45  tff(c_20, plain, (![A_14, B_15]: (k5_xboole_0(A_14, k4_xboole_0(B_15, A_14))=k2_xboole_0(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.04/1.45  tff(c_690, plain, (![A_83]: (k5_xboole_0(A_83, k1_xboole_0)=k2_xboole_0(A_83, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_685, c_20])).
% 3.04/1.45  tff(c_705, plain, (![A_83]: (k5_xboole_0(A_83, k1_xboole_0)=A_83)), inference(demodulation, [status(thm), theory('equality')], [c_10, c_690])).
% 3.04/1.45  tff(c_684, plain, (![A_63]: (k4_xboole_0(k1_xboole_0, A_63)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_482, c_670])).
% 3.04/1.45  tff(c_712, plain, (![A_84, B_85]: (k4_xboole_0(k2_xboole_0(A_84, B_85), B_85)=k4_xboole_0(A_84, B_85))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.04/1.45  tff(c_738, plain, (![A_62]: (k4_xboole_0(k1_xboole_0, A_62)=k4_xboole_0(A_62, A_62))), inference(superposition, [status(thm), theory('equality')], [c_304, c_712])).
% 3.04/1.45  tff(c_757, plain, (![A_62]: (k4_xboole_0(A_62, A_62)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_684, c_738])).
% 3.04/1.45  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.04/1.45  tff(c_145, plain, (![B_2]: (k3_xboole_0(B_2, B_2)=B_2)), inference(resolution, [status(thm)], [c_6, c_137])).
% 3.04/1.45  tff(c_679, plain, (![B_2]: (k5_xboole_0(B_2, B_2)=k4_xboole_0(B_2, B_2))), inference(superposition, [status(thm), theory('equality')], [c_145, c_650])).
% 3.04/1.45  tff(c_885, plain, (![B_2]: (k5_xboole_0(B_2, B_2)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_757, c_679])).
% 3.04/1.45  tff(c_230, plain, (![A_56, B_57]: (r1_tarski(k1_tarski(A_56), B_57) | ~r2_hidden(A_56, B_57))), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.04/1.45  tff(c_12, plain, (![A_6, B_7]: (k3_xboole_0(A_6, B_7)=A_6 | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.04/1.45  tff(c_1493, plain, (![A_115, B_116]: (k3_xboole_0(k1_tarski(A_115), B_116)=k1_tarski(A_115) | ~r2_hidden(A_115, B_116))), inference(resolution, [status(thm)], [c_230, c_12])).
% 3.04/1.45  tff(c_8, plain, (![A_3, B_4]: (k5_xboole_0(A_3, k3_xboole_0(A_3, B_4))=k4_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.04/1.45  tff(c_1499, plain, (![A_115, B_116]: (k5_xboole_0(k1_tarski(A_115), k1_tarski(A_115))=k4_xboole_0(k1_tarski(A_115), B_116) | ~r2_hidden(A_115, B_116))), inference(superposition, [status(thm), theory('equality')], [c_1493, c_8])).
% 3.04/1.45  tff(c_1623, plain, (![A_119, B_120]: (k4_xboole_0(k1_tarski(A_119), B_120)=k1_xboole_0 | ~r2_hidden(A_119, B_120))), inference(demodulation, [status(thm), theory('equality')], [c_885, c_1499])).
% 3.04/1.45  tff(c_1650, plain, (![B_120, A_119]: (k2_xboole_0(B_120, k1_tarski(A_119))=k5_xboole_0(B_120, k1_xboole_0) | ~r2_hidden(A_119, B_120))), inference(superposition, [status(thm), theory('equality')], [c_1623, c_20])).
% 3.04/1.45  tff(c_1839, plain, (![B_123, A_124]: (k2_xboole_0(B_123, k1_tarski(A_124))=B_123 | ~r2_hidden(A_124, B_123))), inference(demodulation, [status(thm), theory('equality')], [c_705, c_1650])).
% 3.04/1.45  tff(c_247, plain, (![B_59, A_60]: (k2_xboole_0(B_59, A_60)=k2_xboole_0(A_60, B_59))), inference(superposition, [status(thm), theory('equality')], [c_241, c_36])).
% 3.04/1.45  tff(c_38, plain, (k2_xboole_0(k1_tarski('#skF_1'), '#skF_2')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.04/1.45  tff(c_267, plain, (k2_xboole_0('#skF_2', k1_tarski('#skF_1'))!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_247, c_38])).
% 3.04/1.45  tff(c_1895, plain, (~r2_hidden('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_1839, c_267])).
% 3.04/1.45  tff(c_1956, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_40, c_1895])).
% 3.04/1.45  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.04/1.45  
% 3.04/1.45  Inference rules
% 3.04/1.45  ----------------------
% 3.04/1.45  #Ref     : 0
% 3.04/1.45  #Sup     : 445
% 3.04/1.45  #Fact    : 0
% 3.04/1.45  #Define  : 0
% 3.04/1.45  #Split   : 0
% 3.04/1.45  #Chain   : 0
% 3.04/1.45  #Close   : 0
% 3.04/1.45  
% 3.04/1.45  Ordering : KBO
% 3.04/1.45  
% 3.04/1.45  Simplification rules
% 3.04/1.45  ----------------------
% 3.04/1.45  #Subsume      : 12
% 3.04/1.45  #Demod        : 373
% 3.04/1.45  #Tautology    : 354
% 3.04/1.45  #SimpNegUnit  : 0
% 3.04/1.45  #BackRed      : 5
% 3.04/1.45  
% 3.04/1.45  #Partial instantiations: 0
% 3.04/1.45  #Strategies tried      : 1
% 3.04/1.45  
% 3.04/1.45  Timing (in seconds)
% 3.04/1.45  ----------------------
% 3.04/1.46  Preprocessing        : 0.30
% 3.04/1.46  Parsing              : 0.16
% 3.04/1.46  CNF conversion       : 0.02
% 3.04/1.46  Main loop            : 0.40
% 3.04/1.46  Inferencing          : 0.14
% 3.04/1.46  Reduction            : 0.17
% 3.04/1.46  Demodulation         : 0.14
% 3.04/1.46  BG Simplification    : 0.02
% 3.04/1.46  Subsumption          : 0.05
% 3.04/1.46  Abstraction          : 0.02
% 3.04/1.46  MUC search           : 0.00
% 3.04/1.46  Cooper               : 0.00
% 3.04/1.46  Total                : 0.73
% 3.04/1.46  Index Insertion      : 0.00
% 3.04/1.46  Index Deletion       : 0.00
% 3.04/1.46  Index Matching       : 0.00
% 3.04/1.46  BG Taut test         : 0.00
%------------------------------------------------------------------------------
