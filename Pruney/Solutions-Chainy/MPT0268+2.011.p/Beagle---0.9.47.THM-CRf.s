%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:52:35 EST 2020

% Result     : Theorem 9.13s
% Output     : CNFRefutation 9.29s
% Verified   : 
% Statistics : Number of formulae       :   77 (  93 expanded)
%              Number of leaves         :   33 (  44 expanded)
%              Depth                    :    9
%              Number of atoms          :   79 ( 109 expanded)
%              Number of equality atoms :   28 (  37 expanded)
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

tff(f_85,negated_conjecture,(
    ~ ! [A,B] :
        ( k4_xboole_0(A,k1_tarski(B)) = A
      <=> ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_zfmisc_1)).

tff(f_53,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

tff(f_77,axiom,(
    ! [A,B] :
      ( ~ r2_hidden(A,B)
     => r1_xboole_0(k1_tarski(A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l27_zfmisc_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_59,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => k4_xboole_0(k2_xboole_0(A,B),B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_xboole_1)).

tff(f_45,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_51,axiom,(
    ! [A,B,C] : k3_xboole_0(A,k4_xboole_0(B,C)) = k4_xboole_0(k3_xboole_0(A,B),C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_43,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_55,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).

tff(f_72,axiom,(
    ! [A,B] :
      ~ ( r1_xboole_0(k1_tarski(A),B)
        & r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l24_zfmisc_1)).

tff(c_46,plain,
    ( ~ r2_hidden('#skF_2','#skF_1')
    | r2_hidden('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_73,plain,(
    ~ r2_hidden('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_46])).

tff(c_24,plain,(
    ! [A_18] : k5_xboole_0(A_18,k1_xboole_0) = A_18 ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_257,plain,(
    ! [A_68,B_69] :
      ( r1_xboole_0(k1_tarski(A_68),B_69)
      | r2_hidden(A_68,B_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_4,plain,(
    ! [B_4,A_3] :
      ( r1_xboole_0(B_4,A_3)
      | ~ r1_xboole_0(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_260,plain,(
    ! [B_69,A_68] :
      ( r1_xboole_0(B_69,k1_tarski(A_68))
      | r2_hidden(A_68,B_69) ) ),
    inference(resolution,[status(thm)],[c_257,c_4])).

tff(c_28,plain,(
    ! [A_21,B_22] :
      ( k4_xboole_0(k2_xboole_0(A_21,B_22),B_22) = A_21
      | ~ r1_xboole_0(A_21,B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_18,plain,(
    ! [A_11,B_12] : r1_tarski(k3_xboole_0(A_11,B_12),A_11) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_161,plain,(
    ! [A_57,B_58] :
      ( k4_xboole_0(A_57,B_58) = k1_xboole_0
      | ~ r1_tarski(A_57,B_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_172,plain,(
    ! [A_11,B_12] : k4_xboole_0(k3_xboole_0(A_11,B_12),A_11) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_18,c_161])).

tff(c_716,plain,(
    ! [A_104,B_105,C_106] : k4_xboole_0(k3_xboole_0(A_104,B_105),C_106) = k3_xboole_0(A_104,k4_xboole_0(B_105,C_106)) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_1217,plain,(
    ! [A_121,B_122] : k3_xboole_0(A_121,k4_xboole_0(B_122,A_121)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_172,c_716])).

tff(c_1784,plain,(
    ! [B_140,A_141] :
      ( k3_xboole_0(B_140,A_141) = k1_xboole_0
      | ~ r1_xboole_0(A_141,B_140) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_1217])).

tff(c_8868,plain,(
    ! [A_262,B_263] :
      ( k3_xboole_0(k1_tarski(A_262),B_263) = k1_xboole_0
      | r2_hidden(A_262,B_263) ) ),
    inference(resolution,[status(thm)],[c_260,c_1784])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_363,plain,(
    ! [A_84,B_85] : k5_xboole_0(A_84,k3_xboole_0(A_84,B_85)) = k4_xboole_0(A_84,B_85) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_378,plain,(
    ! [B_2,A_1] : k5_xboole_0(B_2,k3_xboole_0(A_1,B_2)) = k4_xboole_0(B_2,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_363])).

tff(c_9038,plain,(
    ! [B_263,A_262] :
      ( k4_xboole_0(B_263,k1_tarski(A_262)) = k5_xboole_0(B_263,k1_xboole_0)
      | r2_hidden(A_262,B_263) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8868,c_378])).

tff(c_20652,plain,(
    ! [B_369,A_370] :
      ( k4_xboole_0(B_369,k1_tarski(A_370)) = B_369
      | r2_hidden(A_370,B_369) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_9038])).

tff(c_44,plain,
    ( k4_xboole_0('#skF_1',k1_tarski('#skF_2')) != '#skF_1'
    | r2_hidden('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_196,plain,(
    k4_xboole_0('#skF_1',k1_tarski('#skF_2')) != '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_44])).

tff(c_20921,plain,(
    r2_hidden('#skF_2','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_20652,c_196])).

tff(c_21015,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_73,c_20921])).

tff(c_21016,plain,(
    r2_hidden('#skF_4','#skF_3') ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_21017,plain,(
    k4_xboole_0('#skF_1',k1_tarski('#skF_2')) = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_48,plain,
    ( k4_xboole_0('#skF_1',k1_tarski('#skF_2')) != '#skF_1'
    | k4_xboole_0('#skF_3',k1_tarski('#skF_4')) = '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_21064,plain,(
    k4_xboole_0('#skF_3',k1_tarski('#skF_4')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_21017,c_48])).

tff(c_26,plain,(
    ! [A_19,B_20] : r1_xboole_0(k4_xboole_0(A_19,B_20),B_20) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_123,plain,(
    ! [B_50,A_51] :
      ( r1_xboole_0(B_50,A_51)
      | ~ r1_xboole_0(A_51,B_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_126,plain,(
    ! [B_20,A_19] : r1_xboole_0(B_20,k4_xboole_0(A_19,B_20)) ),
    inference(resolution,[status(thm)],[c_26,c_123])).

tff(c_21068,plain,(
    r1_xboole_0(k1_tarski('#skF_4'),'#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_21064,c_126])).

tff(c_21146,plain,(
    ! [A_383,B_384] :
      ( ~ r2_hidden(A_383,B_384)
      | ~ r1_xboole_0(k1_tarski(A_383),B_384) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_21152,plain,(
    ~ r2_hidden('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_21068,c_21146])).

tff(c_21168,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_21016,c_21152])).

tff(c_21169,plain,(
    r2_hidden('#skF_4','#skF_3') ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_21170,plain,(
    r2_hidden('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_50,plain,
    ( ~ r2_hidden('#skF_2','#skF_1')
    | k4_xboole_0('#skF_3',k1_tarski('#skF_4')) = '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_21349,plain,(
    k4_xboole_0('#skF_3',k1_tarski('#skF_4')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_21170,c_50])).

tff(c_21171,plain,(
    ! [B_385,A_386] :
      ( r1_xboole_0(B_385,A_386)
      | ~ r1_xboole_0(A_386,B_385) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_21174,plain,(
    ! [B_20,A_19] : r1_xboole_0(B_20,k4_xboole_0(A_19,B_20)) ),
    inference(resolution,[status(thm)],[c_26,c_21171])).

tff(c_21298,plain,(
    ! [A_401,B_402] :
      ( ~ r2_hidden(A_401,B_402)
      | ~ r1_xboole_0(k1_tarski(A_401),B_402) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_21303,plain,(
    ! [A_401,A_19] : ~ r2_hidden(A_401,k4_xboole_0(A_19,k1_tarski(A_401))) ),
    inference(resolution,[status(thm)],[c_21174,c_21298])).

tff(c_21353,plain,(
    ~ r2_hidden('#skF_4','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_21349,c_21303])).

tff(c_21364,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_21169,c_21353])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n019.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 17:06:22 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 9.13/3.40  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.13/3.41  
% 9.13/3.41  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.13/3.41  %$ r2_hidden > r1_xboole_0 > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 9.13/3.41  
% 9.13/3.41  %Foreground sorts:
% 9.13/3.41  
% 9.13/3.41  
% 9.13/3.41  %Background operators:
% 9.13/3.41  
% 9.13/3.41  
% 9.13/3.41  %Foreground operators:
% 9.13/3.41  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 9.13/3.41  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 9.13/3.41  tff(k1_tarski, type, k1_tarski: $i > $i).
% 9.13/3.41  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 9.13/3.41  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 9.13/3.41  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 9.13/3.41  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 9.13/3.41  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 9.13/3.41  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 9.13/3.41  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 9.13/3.41  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 9.13/3.41  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 9.13/3.41  tff('#skF_2', type, '#skF_2': $i).
% 9.13/3.41  tff('#skF_3', type, '#skF_3': $i).
% 9.13/3.41  tff('#skF_1', type, '#skF_1': $i).
% 9.13/3.41  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 9.13/3.41  tff(k3_tarski, type, k3_tarski: $i > $i).
% 9.13/3.41  tff('#skF_4', type, '#skF_4': $i).
% 9.13/3.41  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 9.13/3.41  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 9.13/3.41  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 9.13/3.41  
% 9.29/3.43  tff(f_85, negated_conjecture, ~(![A, B]: ((k4_xboole_0(A, k1_tarski(B)) = A) <=> ~r2_hidden(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_zfmisc_1)).
% 9.29/3.43  tff(f_53, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 9.29/3.43  tff(f_77, axiom, (![A, B]: (~r2_hidden(A, B) => r1_xboole_0(k1_tarski(A), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 9.29/3.43  tff(f_31, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 9.29/3.43  tff(f_59, axiom, (![A, B]: (r1_xboole_0(A, B) => (k4_xboole_0(k2_xboole_0(A, B), B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t88_xboole_1)).
% 9.29/3.43  tff(f_45, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 9.29/3.43  tff(f_41, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 9.29/3.43  tff(f_51, axiom, (![A, B, C]: (k3_xboole_0(A, k4_xboole_0(B, C)) = k4_xboole_0(k3_xboole_0(A, B), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_xboole_1)).
% 9.29/3.43  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 9.29/3.43  tff(f_43, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 9.29/3.43  tff(f_55, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_xboole_1)).
% 9.29/3.43  tff(f_72, axiom, (![A, B]: ~(r1_xboole_0(k1_tarski(A), B) & r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l24_zfmisc_1)).
% 9.29/3.43  tff(c_46, plain, (~r2_hidden('#skF_2', '#skF_1') | r2_hidden('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_85])).
% 9.29/3.43  tff(c_73, plain, (~r2_hidden('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_46])).
% 9.29/3.43  tff(c_24, plain, (![A_18]: (k5_xboole_0(A_18, k1_xboole_0)=A_18)), inference(cnfTransformation, [status(thm)], [f_53])).
% 9.29/3.43  tff(c_257, plain, (![A_68, B_69]: (r1_xboole_0(k1_tarski(A_68), B_69) | r2_hidden(A_68, B_69))), inference(cnfTransformation, [status(thm)], [f_77])).
% 9.29/3.43  tff(c_4, plain, (![B_4, A_3]: (r1_xboole_0(B_4, A_3) | ~r1_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 9.29/3.43  tff(c_260, plain, (![B_69, A_68]: (r1_xboole_0(B_69, k1_tarski(A_68)) | r2_hidden(A_68, B_69))), inference(resolution, [status(thm)], [c_257, c_4])).
% 9.29/3.43  tff(c_28, plain, (![A_21, B_22]: (k4_xboole_0(k2_xboole_0(A_21, B_22), B_22)=A_21 | ~r1_xboole_0(A_21, B_22))), inference(cnfTransformation, [status(thm)], [f_59])).
% 9.29/3.43  tff(c_18, plain, (![A_11, B_12]: (r1_tarski(k3_xboole_0(A_11, B_12), A_11))), inference(cnfTransformation, [status(thm)], [f_45])).
% 9.29/3.43  tff(c_161, plain, (![A_57, B_58]: (k4_xboole_0(A_57, B_58)=k1_xboole_0 | ~r1_tarski(A_57, B_58))), inference(cnfTransformation, [status(thm)], [f_41])).
% 9.29/3.43  tff(c_172, plain, (![A_11, B_12]: (k4_xboole_0(k3_xboole_0(A_11, B_12), A_11)=k1_xboole_0)), inference(resolution, [status(thm)], [c_18, c_161])).
% 9.29/3.43  tff(c_716, plain, (![A_104, B_105, C_106]: (k4_xboole_0(k3_xboole_0(A_104, B_105), C_106)=k3_xboole_0(A_104, k4_xboole_0(B_105, C_106)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 9.29/3.43  tff(c_1217, plain, (![A_121, B_122]: (k3_xboole_0(A_121, k4_xboole_0(B_122, A_121))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_172, c_716])).
% 9.29/3.43  tff(c_1784, plain, (![B_140, A_141]: (k3_xboole_0(B_140, A_141)=k1_xboole_0 | ~r1_xboole_0(A_141, B_140))), inference(superposition, [status(thm), theory('equality')], [c_28, c_1217])).
% 9.29/3.43  tff(c_8868, plain, (![A_262, B_263]: (k3_xboole_0(k1_tarski(A_262), B_263)=k1_xboole_0 | r2_hidden(A_262, B_263))), inference(resolution, [status(thm)], [c_260, c_1784])).
% 9.29/3.43  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 9.29/3.43  tff(c_363, plain, (![A_84, B_85]: (k5_xboole_0(A_84, k3_xboole_0(A_84, B_85))=k4_xboole_0(A_84, B_85))), inference(cnfTransformation, [status(thm)], [f_43])).
% 9.29/3.43  tff(c_378, plain, (![B_2, A_1]: (k5_xboole_0(B_2, k3_xboole_0(A_1, B_2))=k4_xboole_0(B_2, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_363])).
% 9.29/3.43  tff(c_9038, plain, (![B_263, A_262]: (k4_xboole_0(B_263, k1_tarski(A_262))=k5_xboole_0(B_263, k1_xboole_0) | r2_hidden(A_262, B_263))), inference(superposition, [status(thm), theory('equality')], [c_8868, c_378])).
% 9.29/3.43  tff(c_20652, plain, (![B_369, A_370]: (k4_xboole_0(B_369, k1_tarski(A_370))=B_369 | r2_hidden(A_370, B_369))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_9038])).
% 9.29/3.43  tff(c_44, plain, (k4_xboole_0('#skF_1', k1_tarski('#skF_2'))!='#skF_1' | r2_hidden('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_85])).
% 9.29/3.43  tff(c_196, plain, (k4_xboole_0('#skF_1', k1_tarski('#skF_2'))!='#skF_1'), inference(splitLeft, [status(thm)], [c_44])).
% 9.29/3.43  tff(c_20921, plain, (r2_hidden('#skF_2', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_20652, c_196])).
% 9.29/3.43  tff(c_21015, plain, $false, inference(negUnitSimplification, [status(thm)], [c_73, c_20921])).
% 9.29/3.43  tff(c_21016, plain, (r2_hidden('#skF_4', '#skF_3')), inference(splitRight, [status(thm)], [c_44])).
% 9.29/3.43  tff(c_21017, plain, (k4_xboole_0('#skF_1', k1_tarski('#skF_2'))='#skF_1'), inference(splitRight, [status(thm)], [c_44])).
% 9.29/3.43  tff(c_48, plain, (k4_xboole_0('#skF_1', k1_tarski('#skF_2'))!='#skF_1' | k4_xboole_0('#skF_3', k1_tarski('#skF_4'))='#skF_3'), inference(cnfTransformation, [status(thm)], [f_85])).
% 9.29/3.43  tff(c_21064, plain, (k4_xboole_0('#skF_3', k1_tarski('#skF_4'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_21017, c_48])).
% 9.29/3.43  tff(c_26, plain, (![A_19, B_20]: (r1_xboole_0(k4_xboole_0(A_19, B_20), B_20))), inference(cnfTransformation, [status(thm)], [f_55])).
% 9.29/3.43  tff(c_123, plain, (![B_50, A_51]: (r1_xboole_0(B_50, A_51) | ~r1_xboole_0(A_51, B_50))), inference(cnfTransformation, [status(thm)], [f_31])).
% 9.29/3.43  tff(c_126, plain, (![B_20, A_19]: (r1_xboole_0(B_20, k4_xboole_0(A_19, B_20)))), inference(resolution, [status(thm)], [c_26, c_123])).
% 9.29/3.43  tff(c_21068, plain, (r1_xboole_0(k1_tarski('#skF_4'), '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_21064, c_126])).
% 9.29/3.43  tff(c_21146, plain, (![A_383, B_384]: (~r2_hidden(A_383, B_384) | ~r1_xboole_0(k1_tarski(A_383), B_384))), inference(cnfTransformation, [status(thm)], [f_72])).
% 9.29/3.43  tff(c_21152, plain, (~r2_hidden('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_21068, c_21146])).
% 9.29/3.43  tff(c_21168, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_21016, c_21152])).
% 9.29/3.43  tff(c_21169, plain, (r2_hidden('#skF_4', '#skF_3')), inference(splitRight, [status(thm)], [c_46])).
% 9.29/3.43  tff(c_21170, plain, (r2_hidden('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_46])).
% 9.29/3.43  tff(c_50, plain, (~r2_hidden('#skF_2', '#skF_1') | k4_xboole_0('#skF_3', k1_tarski('#skF_4'))='#skF_3'), inference(cnfTransformation, [status(thm)], [f_85])).
% 9.29/3.43  tff(c_21349, plain, (k4_xboole_0('#skF_3', k1_tarski('#skF_4'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_21170, c_50])).
% 9.29/3.43  tff(c_21171, plain, (![B_385, A_386]: (r1_xboole_0(B_385, A_386) | ~r1_xboole_0(A_386, B_385))), inference(cnfTransformation, [status(thm)], [f_31])).
% 9.29/3.43  tff(c_21174, plain, (![B_20, A_19]: (r1_xboole_0(B_20, k4_xboole_0(A_19, B_20)))), inference(resolution, [status(thm)], [c_26, c_21171])).
% 9.29/3.43  tff(c_21298, plain, (![A_401, B_402]: (~r2_hidden(A_401, B_402) | ~r1_xboole_0(k1_tarski(A_401), B_402))), inference(cnfTransformation, [status(thm)], [f_72])).
% 9.29/3.43  tff(c_21303, plain, (![A_401, A_19]: (~r2_hidden(A_401, k4_xboole_0(A_19, k1_tarski(A_401))))), inference(resolution, [status(thm)], [c_21174, c_21298])).
% 9.29/3.43  tff(c_21353, plain, (~r2_hidden('#skF_4', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_21349, c_21303])).
% 9.29/3.43  tff(c_21364, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_21169, c_21353])).
% 9.29/3.43  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.29/3.43  
% 9.29/3.43  Inference rules
% 9.29/3.43  ----------------------
% 9.29/3.43  #Ref     : 0
% 9.29/3.43  #Sup     : 5319
% 9.29/3.43  #Fact    : 0
% 9.29/3.43  #Define  : 0
% 9.29/3.43  #Split   : 2
% 9.29/3.43  #Chain   : 0
% 9.29/3.43  #Close   : 0
% 9.29/3.43  
% 9.29/3.43  Ordering : KBO
% 9.29/3.43  
% 9.29/3.43  Simplification rules
% 9.29/3.43  ----------------------
% 9.29/3.43  #Subsume      : 386
% 9.29/3.43  #Demod        : 5233
% 9.29/3.43  #Tautology    : 3355
% 9.29/3.43  #SimpNegUnit  : 21
% 9.29/3.43  #BackRed      : 2
% 9.29/3.43  
% 9.29/3.43  #Partial instantiations: 0
% 9.29/3.43  #Strategies tried      : 1
% 9.29/3.43  
% 9.29/3.43  Timing (in seconds)
% 9.29/3.43  ----------------------
% 9.29/3.43  Preprocessing        : 0.30
% 9.29/3.43  Parsing              : 0.16
% 9.29/3.43  CNF conversion       : 0.02
% 9.29/3.43  Main loop            : 2.33
% 9.29/3.43  Inferencing          : 0.51
% 9.29/3.43  Reduction            : 1.21
% 9.29/3.43  Demodulation         : 1.05
% 9.29/3.43  BG Simplification    : 0.06
% 9.29/3.43  Subsumption          : 0.42
% 9.29/3.43  Abstraction          : 0.09
% 9.29/3.43  MUC search           : 0.00
% 9.29/3.43  Cooper               : 0.00
% 9.29/3.43  Total                : 2.66
% 9.29/3.43  Index Insertion      : 0.00
% 9.29/3.43  Index Deletion       : 0.00
% 9.29/3.43  Index Matching       : 0.00
% 9.29/3.43  BG Taut test         : 0.00
%------------------------------------------------------------------------------
