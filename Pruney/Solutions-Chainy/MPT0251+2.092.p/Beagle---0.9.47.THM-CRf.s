%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:50:58 EST 2020

% Result     : Theorem 4.46s
% Output     : CNFRefutation 4.46s
% Verified   : 
% Statistics : Number of formulae       :   73 ( 116 expanded)
%              Number of leaves         :   35 (  53 expanded)
%              Depth                    :   15
%              Number of atoms          :   75 ( 128 expanded)
%              Number of equality atoms :   39 (  75 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_2',type,(
    '#skF_2': $i > $i )).

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

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_90,negated_conjecture,(
    ~ ! [A,B] :
        ( r2_hidden(A,B)
       => k2_xboole_0(k1_tarski(A),B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_zfmisc_1)).

tff(f_57,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_69,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_53,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_45,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_67,axiom,(
    ! [A,B] : k2_xboole_0(k3_xboole_0(A,B),k4_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_xboole_1)).

tff(f_65,axiom,(
    ! [A,B] : k4_xboole_0(k2_xboole_0(A,B),B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_xboole_1)).

tff(f_55,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_71,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_85,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_tarski(A,B),C)
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_zfmisc_1)).

tff(f_61,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_63,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

tff(c_44,plain,(
    r2_hidden('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_14,plain,(
    ! [A_14] : k2_xboole_0(A_14,k1_xboole_0) = A_14 ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_66,plain,(
    ! [B_43,A_44] : k2_xboole_0(B_43,A_44) = k2_xboole_0(A_44,B_43) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_82,plain,(
    ! [A_44] : k2_xboole_0(k1_xboole_0,A_44) = A_44 ),
    inference(superposition,[status(thm),theory(equality)],[c_66,c_14])).

tff(c_24,plain,(
    ! [A_23] : r1_xboole_0(A_23,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_151,plain,(
    ! [B_46,A_47] :
      ( r1_xboole_0(B_46,A_47)
      | ~ r1_xboole_0(A_47,B_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_154,plain,(
    ! [A_23] : r1_xboole_0(k1_xboole_0,A_23) ),
    inference(resolution,[status(thm)],[c_24,c_151])).

tff(c_10,plain,(
    ! [A_10] :
      ( r2_hidden('#skF_2'(A_10),A_10)
      | k1_xboole_0 = A_10 ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_208,plain,(
    ! [A_58,B_59,C_60] :
      ( ~ r1_xboole_0(A_58,B_59)
      | ~ r2_hidden(C_60,k3_xboole_0(A_58,B_59)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_218,plain,(
    ! [A_64,B_65] :
      ( ~ r1_xboole_0(A_64,B_65)
      | k3_xboole_0(A_64,B_65) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_10,c_208])).

tff(c_227,plain,(
    ! [A_66] : k3_xboole_0(k1_xboole_0,A_66) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_154,c_218])).

tff(c_22,plain,(
    ! [A_21,B_22] : k2_xboole_0(k3_xboole_0(A_21,B_22),k4_xboole_0(A_21,B_22)) = A_21 ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_272,plain,(
    ! [A_69] : k2_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,A_69)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_227,c_22])).

tff(c_282,plain,(
    ! [A_69] : k4_xboole_0(k1_xboole_0,A_69) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_82,c_272])).

tff(c_398,plain,(
    ! [A_82,B_83] : k4_xboole_0(k2_xboole_0(A_82,B_83),B_83) = k4_xboole_0(A_82,B_83) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_430,plain,(
    ! [A_44] : k4_xboole_0(k1_xboole_0,A_44) = k4_xboole_0(A_44,A_44) ),
    inference(superposition,[status(thm),theory(equality)],[c_82,c_398])).

tff(c_445,plain,(
    ! [A_44] : k4_xboole_0(A_44,A_44) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_282,c_430])).

tff(c_447,plain,(
    ! [A_84] : k4_xboole_0(A_84,A_84) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_282,c_430])).

tff(c_531,plain,(
    ! [A_90] : k2_xboole_0(k3_xboole_0(A_90,A_90),k1_xboole_0) = A_90 ),
    inference(superposition,[status(thm),theory(equality)],[c_447,c_22])).

tff(c_574,plain,(
    ! [A_91] : k3_xboole_0(A_91,A_91) = A_91 ),
    inference(superposition,[status(thm),theory(equality)],[c_531,c_14])).

tff(c_12,plain,(
    ! [A_12,B_13] : k5_xboole_0(A_12,k3_xboole_0(A_12,B_13)) = k4_xboole_0(A_12,B_13) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_580,plain,(
    ! [A_91] : k5_xboole_0(A_91,A_91) = k4_xboole_0(A_91,A_91) ),
    inference(superposition,[status(thm),theory(equality)],[c_574,c_12])).

tff(c_607,plain,(
    ! [A_91] : k5_xboole_0(A_91,A_91) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_445,c_580])).

tff(c_26,plain,(
    ! [A_24] : k2_tarski(A_24,A_24) = k1_tarski(A_24) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_737,plain,(
    ! [A_103,B_104,C_105] :
      ( r1_tarski(k2_tarski(A_103,B_104),C_105)
      | ~ r2_hidden(B_104,C_105)
      | ~ r2_hidden(A_103,C_105) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_1171,plain,(
    ! [A_120,C_121] :
      ( r1_tarski(k1_tarski(A_120),C_121)
      | ~ r2_hidden(A_120,C_121)
      | ~ r2_hidden(A_120,C_121) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_737])).

tff(c_16,plain,(
    ! [A_15,B_16] :
      ( k3_xboole_0(A_15,B_16) = A_15
      | ~ r1_tarski(A_15,B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_4026,plain,(
    ! [A_169,C_170] :
      ( k3_xboole_0(k1_tarski(A_169),C_170) = k1_tarski(A_169)
      | ~ r2_hidden(A_169,C_170) ) ),
    inference(resolution,[status(thm)],[c_1171,c_16])).

tff(c_4065,plain,(
    ! [A_169,C_170] :
      ( k5_xboole_0(k1_tarski(A_169),k1_tarski(A_169)) = k4_xboole_0(k1_tarski(A_169),C_170)
      | ~ r2_hidden(A_169,C_170) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4026,c_12])).

tff(c_4440,plain,(
    ! [A_175,C_176] :
      ( k4_xboole_0(k1_tarski(A_175),C_176) = k1_xboole_0
      | ~ r2_hidden(A_175,C_176) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_607,c_4065])).

tff(c_18,plain,(
    ! [A_17,B_18] : k2_xboole_0(A_17,k4_xboole_0(B_18,A_17)) = k2_xboole_0(A_17,B_18) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_4495,plain,(
    ! [C_176,A_175] :
      ( k2_xboole_0(C_176,k1_tarski(A_175)) = k2_xboole_0(C_176,k1_xboole_0)
      | ~ r2_hidden(A_175,C_176) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4440,c_18])).

tff(c_4848,plain,(
    ! [C_182,A_183] :
      ( k2_xboole_0(C_182,k1_tarski(A_183)) = C_182
      | ~ r2_hidden(A_183,C_182) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_4495])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_42,plain,(
    k2_xboole_0(k1_tarski('#skF_3'),'#skF_4') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_45,plain,(
    k2_xboole_0('#skF_4',k1_tarski('#skF_3')) != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_42])).

tff(c_4959,plain,(
    ~ r2_hidden('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_4848,c_45])).

tff(c_5027,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_4959])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n011.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 16:04:57 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.46/1.89  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.46/1.90  
% 4.46/1.90  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.46/1.90  %$ r2_hidden > r1_xboole_0 > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 4.46/1.90  
% 4.46/1.90  %Foreground sorts:
% 4.46/1.90  
% 4.46/1.90  
% 4.46/1.90  %Background operators:
% 4.46/1.90  
% 4.46/1.90  
% 4.46/1.90  %Foreground operators:
% 4.46/1.90  tff('#skF_2', type, '#skF_2': $i > $i).
% 4.46/1.90  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.46/1.90  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.46/1.90  tff(k1_tarski, type, k1_tarski: $i > $i).
% 4.46/1.90  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.46/1.90  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.46/1.90  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 4.46/1.90  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 4.46/1.90  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.46/1.90  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 4.46/1.90  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.46/1.90  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 4.46/1.90  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 4.46/1.90  tff('#skF_3', type, '#skF_3': $i).
% 4.46/1.90  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.46/1.90  tff(k3_tarski, type, k3_tarski: $i > $i).
% 4.46/1.90  tff('#skF_4', type, '#skF_4': $i).
% 4.46/1.90  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.46/1.90  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.46/1.90  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.46/1.90  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 4.46/1.90  
% 4.46/1.91  tff(f_90, negated_conjecture, ~(![A, B]: (r2_hidden(A, B) => (k2_xboole_0(k1_tarski(A), B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_zfmisc_1)).
% 4.46/1.91  tff(f_57, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 4.46/1.91  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 4.46/1.91  tff(f_69, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 4.46/1.91  tff(f_31, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 4.46/1.91  tff(f_53, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 4.46/1.91  tff(f_45, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 4.46/1.91  tff(f_67, axiom, (![A, B]: (k2_xboole_0(k3_xboole_0(A, B), k4_xboole_0(A, B)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t51_xboole_1)).
% 4.46/1.91  tff(f_65, axiom, (![A, B]: (k4_xboole_0(k2_xboole_0(A, B), B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t40_xboole_1)).
% 4.46/1.91  tff(f_55, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 4.46/1.91  tff(f_71, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 4.46/1.91  tff(f_85, axiom, (![A, B, C]: (r1_tarski(k2_tarski(A, B), C) <=> (r2_hidden(A, C) & r2_hidden(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 4.46/1.91  tff(f_61, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 4.46/1.91  tff(f_63, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_xboole_1)).
% 4.46/1.91  tff(c_44, plain, (r2_hidden('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_90])).
% 4.46/1.91  tff(c_14, plain, (![A_14]: (k2_xboole_0(A_14, k1_xboole_0)=A_14)), inference(cnfTransformation, [status(thm)], [f_57])).
% 4.46/1.91  tff(c_66, plain, (![B_43, A_44]: (k2_xboole_0(B_43, A_44)=k2_xboole_0(A_44, B_43))), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.46/1.91  tff(c_82, plain, (![A_44]: (k2_xboole_0(k1_xboole_0, A_44)=A_44)), inference(superposition, [status(thm), theory('equality')], [c_66, c_14])).
% 4.46/1.91  tff(c_24, plain, (![A_23]: (r1_xboole_0(A_23, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_69])).
% 4.46/1.91  tff(c_151, plain, (![B_46, A_47]: (r1_xboole_0(B_46, A_47) | ~r1_xboole_0(A_47, B_46))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.46/1.91  tff(c_154, plain, (![A_23]: (r1_xboole_0(k1_xboole_0, A_23))), inference(resolution, [status(thm)], [c_24, c_151])).
% 4.46/1.91  tff(c_10, plain, (![A_10]: (r2_hidden('#skF_2'(A_10), A_10) | k1_xboole_0=A_10)), inference(cnfTransformation, [status(thm)], [f_53])).
% 4.46/1.91  tff(c_208, plain, (![A_58, B_59, C_60]: (~r1_xboole_0(A_58, B_59) | ~r2_hidden(C_60, k3_xboole_0(A_58, B_59)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 4.46/1.91  tff(c_218, plain, (![A_64, B_65]: (~r1_xboole_0(A_64, B_65) | k3_xboole_0(A_64, B_65)=k1_xboole_0)), inference(resolution, [status(thm)], [c_10, c_208])).
% 4.46/1.91  tff(c_227, plain, (![A_66]: (k3_xboole_0(k1_xboole_0, A_66)=k1_xboole_0)), inference(resolution, [status(thm)], [c_154, c_218])).
% 4.46/1.91  tff(c_22, plain, (![A_21, B_22]: (k2_xboole_0(k3_xboole_0(A_21, B_22), k4_xboole_0(A_21, B_22))=A_21)), inference(cnfTransformation, [status(thm)], [f_67])).
% 4.46/1.91  tff(c_272, plain, (![A_69]: (k2_xboole_0(k1_xboole_0, k4_xboole_0(k1_xboole_0, A_69))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_227, c_22])).
% 4.46/1.91  tff(c_282, plain, (![A_69]: (k4_xboole_0(k1_xboole_0, A_69)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_82, c_272])).
% 4.46/1.91  tff(c_398, plain, (![A_82, B_83]: (k4_xboole_0(k2_xboole_0(A_82, B_83), B_83)=k4_xboole_0(A_82, B_83))), inference(cnfTransformation, [status(thm)], [f_65])).
% 4.46/1.91  tff(c_430, plain, (![A_44]: (k4_xboole_0(k1_xboole_0, A_44)=k4_xboole_0(A_44, A_44))), inference(superposition, [status(thm), theory('equality')], [c_82, c_398])).
% 4.46/1.91  tff(c_445, plain, (![A_44]: (k4_xboole_0(A_44, A_44)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_282, c_430])).
% 4.46/1.91  tff(c_447, plain, (![A_84]: (k4_xboole_0(A_84, A_84)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_282, c_430])).
% 4.46/1.91  tff(c_531, plain, (![A_90]: (k2_xboole_0(k3_xboole_0(A_90, A_90), k1_xboole_0)=A_90)), inference(superposition, [status(thm), theory('equality')], [c_447, c_22])).
% 4.46/1.91  tff(c_574, plain, (![A_91]: (k3_xboole_0(A_91, A_91)=A_91)), inference(superposition, [status(thm), theory('equality')], [c_531, c_14])).
% 4.46/1.91  tff(c_12, plain, (![A_12, B_13]: (k5_xboole_0(A_12, k3_xboole_0(A_12, B_13))=k4_xboole_0(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_55])).
% 4.46/1.91  tff(c_580, plain, (![A_91]: (k5_xboole_0(A_91, A_91)=k4_xboole_0(A_91, A_91))), inference(superposition, [status(thm), theory('equality')], [c_574, c_12])).
% 4.46/1.91  tff(c_607, plain, (![A_91]: (k5_xboole_0(A_91, A_91)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_445, c_580])).
% 4.46/1.91  tff(c_26, plain, (![A_24]: (k2_tarski(A_24, A_24)=k1_tarski(A_24))), inference(cnfTransformation, [status(thm)], [f_71])).
% 4.46/1.91  tff(c_737, plain, (![A_103, B_104, C_105]: (r1_tarski(k2_tarski(A_103, B_104), C_105) | ~r2_hidden(B_104, C_105) | ~r2_hidden(A_103, C_105))), inference(cnfTransformation, [status(thm)], [f_85])).
% 4.46/1.91  tff(c_1171, plain, (![A_120, C_121]: (r1_tarski(k1_tarski(A_120), C_121) | ~r2_hidden(A_120, C_121) | ~r2_hidden(A_120, C_121))), inference(superposition, [status(thm), theory('equality')], [c_26, c_737])).
% 4.46/1.91  tff(c_16, plain, (![A_15, B_16]: (k3_xboole_0(A_15, B_16)=A_15 | ~r1_tarski(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_61])).
% 4.46/1.91  tff(c_4026, plain, (![A_169, C_170]: (k3_xboole_0(k1_tarski(A_169), C_170)=k1_tarski(A_169) | ~r2_hidden(A_169, C_170))), inference(resolution, [status(thm)], [c_1171, c_16])).
% 4.46/1.91  tff(c_4065, plain, (![A_169, C_170]: (k5_xboole_0(k1_tarski(A_169), k1_tarski(A_169))=k4_xboole_0(k1_tarski(A_169), C_170) | ~r2_hidden(A_169, C_170))), inference(superposition, [status(thm), theory('equality')], [c_4026, c_12])).
% 4.46/1.91  tff(c_4440, plain, (![A_175, C_176]: (k4_xboole_0(k1_tarski(A_175), C_176)=k1_xboole_0 | ~r2_hidden(A_175, C_176))), inference(demodulation, [status(thm), theory('equality')], [c_607, c_4065])).
% 4.46/1.91  tff(c_18, plain, (![A_17, B_18]: (k2_xboole_0(A_17, k4_xboole_0(B_18, A_17))=k2_xboole_0(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_63])).
% 4.46/1.91  tff(c_4495, plain, (![C_176, A_175]: (k2_xboole_0(C_176, k1_tarski(A_175))=k2_xboole_0(C_176, k1_xboole_0) | ~r2_hidden(A_175, C_176))), inference(superposition, [status(thm), theory('equality')], [c_4440, c_18])).
% 4.46/1.91  tff(c_4848, plain, (![C_182, A_183]: (k2_xboole_0(C_182, k1_tarski(A_183))=C_182 | ~r2_hidden(A_183, C_182))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_4495])).
% 4.46/1.91  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.46/1.91  tff(c_42, plain, (k2_xboole_0(k1_tarski('#skF_3'), '#skF_4')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_90])).
% 4.46/1.91  tff(c_45, plain, (k2_xboole_0('#skF_4', k1_tarski('#skF_3'))!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_2, c_42])).
% 4.46/1.91  tff(c_4959, plain, (~r2_hidden('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_4848, c_45])).
% 4.46/1.91  tff(c_5027, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_44, c_4959])).
% 4.46/1.91  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.46/1.91  
% 4.46/1.91  Inference rules
% 4.46/1.91  ----------------------
% 4.46/1.91  #Ref     : 0
% 4.46/1.91  #Sup     : 1250
% 4.46/1.91  #Fact    : 0
% 4.46/1.91  #Define  : 0
% 4.46/1.91  #Split   : 0
% 4.46/1.91  #Chain   : 0
% 4.46/1.91  #Close   : 0
% 4.46/1.91  
% 4.46/1.91  Ordering : KBO
% 4.46/1.91  
% 4.46/1.91  Simplification rules
% 4.46/1.91  ----------------------
% 4.46/1.91  #Subsume      : 82
% 4.46/1.91  #Demod        : 1538
% 4.46/1.91  #Tautology    : 892
% 4.46/1.91  #SimpNegUnit  : 2
% 4.46/1.91  #BackRed      : 4
% 4.46/1.91  
% 4.46/1.91  #Partial instantiations: 0
% 4.46/1.91  #Strategies tried      : 1
% 4.46/1.91  
% 4.46/1.91  Timing (in seconds)
% 4.46/1.91  ----------------------
% 4.46/1.92  Preprocessing        : 0.32
% 4.46/1.92  Parsing              : 0.17
% 4.46/1.92  CNF conversion       : 0.02
% 4.46/1.92  Main loop            : 0.84
% 4.46/1.92  Inferencing          : 0.24
% 4.46/1.92  Reduction            : 0.42
% 4.46/1.92  Demodulation         : 0.36
% 4.46/1.92  BG Simplification    : 0.03
% 4.46/1.92  Subsumption          : 0.10
% 4.46/1.92  Abstraction          : 0.05
% 4.46/1.92  MUC search           : 0.00
% 4.46/1.92  Cooper               : 0.00
% 4.46/1.92  Total                : 1.19
% 4.46/1.92  Index Insertion      : 0.00
% 4.46/1.92  Index Deletion       : 0.00
% 4.46/1.92  Index Matching       : 0.00
% 4.46/1.92  BG Taut test         : 0.00
%------------------------------------------------------------------------------
