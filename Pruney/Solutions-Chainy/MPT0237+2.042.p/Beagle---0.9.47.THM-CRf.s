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
% DateTime   : Thu Dec  3 09:49:50 EST 2020

% Result     : Theorem 2.55s
% Output     : CNFRefutation 2.78s
% Verified   : 
% Statistics : Number of formulae       :   71 ( 148 expanded)
%              Number of leaves         :   36 (  66 expanded)
%              Depth                    :   11
%              Number of atoms          :   65 ( 180 expanded)
%              Number of equality atoms :   51 ( 124 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1

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

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

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

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_53,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_55,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_49,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_41,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_51,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_59,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_82,axiom,(
    ! [A,B] : k4_xboole_0(k1_tarski(A),k2_tarski(A,B)) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_zfmisc_1)).

tff(f_57,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_73,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_78,axiom,(
    ! [A,B] :
      ( A != B
     => r1_xboole_0(k1_tarski(A),k1_tarski(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_zfmisc_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_87,axiom,(
    ! [A,B] :
      ( A != B
     => k5_xboole_0(k1_tarski(A),k1_tarski(B)) = k2_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_zfmisc_1)).

tff(f_90,negated_conjecture,(
    ~ ! [A,B] : k3_tarski(k2_tarski(k1_tarski(A),k1_tarski(B))) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_zfmisc_1)).

tff(c_12,plain,(
    ! [A_12] : k4_xboole_0(A_12,k1_xboole_0) = A_12 ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_14,plain,(
    ! [A_13] : r1_xboole_0(A_13,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_8,plain,(
    ! [A_8] :
      ( r2_hidden('#skF_2'(A_8),A_8)
      | k1_xboole_0 = A_8 ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_168,plain,(
    ! [A_72,B_73,C_74] :
      ( ~ r1_xboole_0(A_72,B_73)
      | ~ r2_hidden(C_74,k3_xboole_0(A_72,B_73)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_180,plain,(
    ! [A_75,B_76] :
      ( ~ r1_xboole_0(A_75,B_76)
      | k3_xboole_0(A_75,B_76) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_8,c_168])).

tff(c_208,plain,(
    ! [A_79] : k3_xboole_0(A_79,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_14,c_180])).

tff(c_10,plain,(
    ! [A_10,B_11] : k5_xboole_0(A_10,k3_xboole_0(A_10,B_11)) = k4_xboole_0(A_10,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_216,plain,(
    ! [A_79] : k5_xboole_0(A_79,k1_xboole_0) = k4_xboole_0(A_79,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_208,c_10])).

tff(c_236,plain,(
    ! [A_79] : k5_xboole_0(A_79,k1_xboole_0) = A_79 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_216])).

tff(c_18,plain,(
    ! [A_16] : k2_tarski(A_16,A_16) = k1_tarski(A_16) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_98,plain,(
    ! [A_62,B_63] : k4_xboole_0(k1_tarski(A_62),k2_tarski(A_62,B_63)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_105,plain,(
    ! [A_16] : k4_xboole_0(k1_tarski(A_16),k1_tarski(A_16)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_98])).

tff(c_254,plain,(
    ! [A_82,B_83] : k5_xboole_0(A_82,k4_xboole_0(B_83,A_82)) = k2_xboole_0(A_82,B_83) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_263,plain,(
    ! [A_16] : k2_xboole_0(k1_tarski(A_16),k1_tarski(A_16)) = k5_xboole_0(k1_tarski(A_16),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_105,c_254])).

tff(c_438,plain,(
    ! [A_95] : k2_xboole_0(k1_tarski(A_95),k1_tarski(A_95)) = k1_tarski(A_95) ),
    inference(demodulation,[status(thm),theory(equality)],[c_236,c_263])).

tff(c_124,plain,(
    ! [A_67,B_68] : k3_tarski(k2_tarski(A_67,B_68)) = k2_xboole_0(A_67,B_68) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_133,plain,(
    ! [A_16] : k3_tarski(k1_tarski(A_16)) = k2_xboole_0(A_16,A_16) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_124])).

tff(c_444,plain,(
    ! [A_95] : k3_tarski(k1_tarski(k1_tarski(A_95))) = k1_tarski(A_95) ),
    inference(superposition,[status(thm),theory(equality)],[c_438,c_133])).

tff(c_34,plain,(
    ! [A_46,B_47] :
      ( r1_xboole_0(k1_tarski(A_46),k1_tarski(B_47))
      | B_47 = A_46 ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_618,plain,(
    ! [A_113,B_114] :
      ( k3_xboole_0(k1_tarski(A_113),k1_tarski(B_114)) = k1_xboole_0
      | B_114 = A_113 ) ),
    inference(resolution,[status(thm)],[c_34,c_180])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_153,plain,(
    ! [A_70,B_71] : k5_xboole_0(A_70,k3_xboole_0(A_70,B_71)) = k4_xboole_0(A_70,B_71) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_162,plain,(
    ! [A_1,B_2] : k5_xboole_0(A_1,k3_xboole_0(B_2,A_1)) = k4_xboole_0(A_1,B_2) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_153])).

tff(c_630,plain,(
    ! [B_114,A_113] :
      ( k4_xboole_0(k1_tarski(B_114),k1_tarski(A_113)) = k5_xboole_0(k1_tarski(B_114),k1_xboole_0)
      | B_114 = A_113 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_618,c_162])).

tff(c_682,plain,(
    ! [B_122,A_123] :
      ( k4_xboole_0(k1_tarski(B_122),k1_tarski(A_123)) = k1_tarski(B_122)
      | B_122 = A_123 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_236,c_630])).

tff(c_16,plain,(
    ! [A_14,B_15] : k5_xboole_0(A_14,k4_xboole_0(B_15,A_14)) = k2_xboole_0(A_14,B_15) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_788,plain,(
    ! [A_149,B_150] :
      ( k5_xboole_0(k1_tarski(A_149),k1_tarski(B_150)) = k2_xboole_0(k1_tarski(A_149),k1_tarski(B_150))
      | B_150 = A_149 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_682,c_16])).

tff(c_40,plain,(
    ! [A_52,B_53] :
      ( k5_xboole_0(k1_tarski(A_52),k1_tarski(B_53)) = k2_tarski(A_52,B_53)
      | B_53 = A_52 ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_814,plain,(
    ! [A_151,B_152] :
      ( k2_xboole_0(k1_tarski(A_151),k1_tarski(B_152)) = k2_tarski(A_151,B_152)
      | B_152 = A_151
      | B_152 = A_151 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_788,c_40])).

tff(c_32,plain,(
    ! [A_44,B_45] : k3_tarski(k2_tarski(A_44,B_45)) = k2_xboole_0(A_44,B_45) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_42,plain,(
    k3_tarski(k2_tarski(k1_tarski('#skF_3'),k1_tarski('#skF_4'))) != k2_tarski('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_43,plain,(
    k2_xboole_0(k1_tarski('#skF_3'),k1_tarski('#skF_4')) != k2_tarski('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_42])).

tff(c_844,plain,(
    '#skF_3' = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_814,c_43])).

tff(c_850,plain,(
    k2_xboole_0(k1_tarski('#skF_4'),k1_tarski('#skF_4')) != k2_tarski('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_844,c_844,c_43])).

tff(c_853,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_444,c_133,c_18,c_850])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.05/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.05/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n019.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 13:33:52 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.55/1.36  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.55/1.36  
% 2.55/1.36  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.78/1.36  %$ r2_hidden > r1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 2.78/1.36  
% 2.78/1.36  %Foreground sorts:
% 2.78/1.36  
% 2.78/1.36  
% 2.78/1.36  %Background operators:
% 2.78/1.36  
% 2.78/1.36  
% 2.78/1.36  %Foreground operators:
% 2.78/1.36  tff('#skF_2', type, '#skF_2': $i > $i).
% 2.78/1.36  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.78/1.36  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.78/1.36  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.78/1.36  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.78/1.36  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.78/1.36  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.78/1.36  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.78/1.36  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.78/1.36  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.78/1.36  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.78/1.36  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.78/1.36  tff('#skF_3', type, '#skF_3': $i).
% 2.78/1.36  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.78/1.36  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.78/1.36  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.78/1.36  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.78/1.36  tff('#skF_4', type, '#skF_4': $i).
% 2.78/1.36  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.78/1.36  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.78/1.36  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.78/1.36  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.78/1.36  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.78/1.36  
% 2.78/1.38  tff(f_53, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 2.78/1.38  tff(f_55, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 2.78/1.38  tff(f_49, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 2.78/1.38  tff(f_41, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 2.78/1.38  tff(f_51, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 2.78/1.38  tff(f_59, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 2.78/1.38  tff(f_82, axiom, (![A, B]: (k4_xboole_0(k1_tarski(A), k2_tarski(A, B)) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t22_zfmisc_1)).
% 2.78/1.38  tff(f_57, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_xboole_1)).
% 2.78/1.38  tff(f_73, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 2.78/1.38  tff(f_78, axiom, (![A, B]: (~(A = B) => r1_xboole_0(k1_tarski(A), k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_zfmisc_1)).
% 2.78/1.38  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 2.78/1.38  tff(f_87, axiom, (![A, B]: (~(A = B) => (k5_xboole_0(k1_tarski(A), k1_tarski(B)) = k2_tarski(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_zfmisc_1)).
% 2.78/1.38  tff(f_90, negated_conjecture, ~(![A, B]: (k3_tarski(k2_tarski(k1_tarski(A), k1_tarski(B))) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t32_zfmisc_1)).
% 2.78/1.38  tff(c_12, plain, (![A_12]: (k4_xboole_0(A_12, k1_xboole_0)=A_12)), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.78/1.38  tff(c_14, plain, (![A_13]: (r1_xboole_0(A_13, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.78/1.38  tff(c_8, plain, (![A_8]: (r2_hidden('#skF_2'(A_8), A_8) | k1_xboole_0=A_8)), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.78/1.38  tff(c_168, plain, (![A_72, B_73, C_74]: (~r1_xboole_0(A_72, B_73) | ~r2_hidden(C_74, k3_xboole_0(A_72, B_73)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.78/1.38  tff(c_180, plain, (![A_75, B_76]: (~r1_xboole_0(A_75, B_76) | k3_xboole_0(A_75, B_76)=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_168])).
% 2.78/1.38  tff(c_208, plain, (![A_79]: (k3_xboole_0(A_79, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_14, c_180])).
% 2.78/1.38  tff(c_10, plain, (![A_10, B_11]: (k5_xboole_0(A_10, k3_xboole_0(A_10, B_11))=k4_xboole_0(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.78/1.38  tff(c_216, plain, (![A_79]: (k5_xboole_0(A_79, k1_xboole_0)=k4_xboole_0(A_79, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_208, c_10])).
% 2.78/1.38  tff(c_236, plain, (![A_79]: (k5_xboole_0(A_79, k1_xboole_0)=A_79)), inference(demodulation, [status(thm), theory('equality')], [c_12, c_216])).
% 2.78/1.38  tff(c_18, plain, (![A_16]: (k2_tarski(A_16, A_16)=k1_tarski(A_16))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.78/1.38  tff(c_98, plain, (![A_62, B_63]: (k4_xboole_0(k1_tarski(A_62), k2_tarski(A_62, B_63))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.78/1.38  tff(c_105, plain, (![A_16]: (k4_xboole_0(k1_tarski(A_16), k1_tarski(A_16))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_18, c_98])).
% 2.78/1.38  tff(c_254, plain, (![A_82, B_83]: (k5_xboole_0(A_82, k4_xboole_0(B_83, A_82))=k2_xboole_0(A_82, B_83))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.78/1.38  tff(c_263, plain, (![A_16]: (k2_xboole_0(k1_tarski(A_16), k1_tarski(A_16))=k5_xboole_0(k1_tarski(A_16), k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_105, c_254])).
% 2.78/1.38  tff(c_438, plain, (![A_95]: (k2_xboole_0(k1_tarski(A_95), k1_tarski(A_95))=k1_tarski(A_95))), inference(demodulation, [status(thm), theory('equality')], [c_236, c_263])).
% 2.78/1.38  tff(c_124, plain, (![A_67, B_68]: (k3_tarski(k2_tarski(A_67, B_68))=k2_xboole_0(A_67, B_68))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.78/1.38  tff(c_133, plain, (![A_16]: (k3_tarski(k1_tarski(A_16))=k2_xboole_0(A_16, A_16))), inference(superposition, [status(thm), theory('equality')], [c_18, c_124])).
% 2.78/1.38  tff(c_444, plain, (![A_95]: (k3_tarski(k1_tarski(k1_tarski(A_95)))=k1_tarski(A_95))), inference(superposition, [status(thm), theory('equality')], [c_438, c_133])).
% 2.78/1.38  tff(c_34, plain, (![A_46, B_47]: (r1_xboole_0(k1_tarski(A_46), k1_tarski(B_47)) | B_47=A_46)), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.78/1.38  tff(c_618, plain, (![A_113, B_114]: (k3_xboole_0(k1_tarski(A_113), k1_tarski(B_114))=k1_xboole_0 | B_114=A_113)), inference(resolution, [status(thm)], [c_34, c_180])).
% 2.78/1.38  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.78/1.38  tff(c_153, plain, (![A_70, B_71]: (k5_xboole_0(A_70, k3_xboole_0(A_70, B_71))=k4_xboole_0(A_70, B_71))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.78/1.38  tff(c_162, plain, (![A_1, B_2]: (k5_xboole_0(A_1, k3_xboole_0(B_2, A_1))=k4_xboole_0(A_1, B_2))), inference(superposition, [status(thm), theory('equality')], [c_2, c_153])).
% 2.78/1.38  tff(c_630, plain, (![B_114, A_113]: (k4_xboole_0(k1_tarski(B_114), k1_tarski(A_113))=k5_xboole_0(k1_tarski(B_114), k1_xboole_0) | B_114=A_113)), inference(superposition, [status(thm), theory('equality')], [c_618, c_162])).
% 2.78/1.38  tff(c_682, plain, (![B_122, A_123]: (k4_xboole_0(k1_tarski(B_122), k1_tarski(A_123))=k1_tarski(B_122) | B_122=A_123)), inference(demodulation, [status(thm), theory('equality')], [c_236, c_630])).
% 2.78/1.38  tff(c_16, plain, (![A_14, B_15]: (k5_xboole_0(A_14, k4_xboole_0(B_15, A_14))=k2_xboole_0(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.78/1.38  tff(c_788, plain, (![A_149, B_150]: (k5_xboole_0(k1_tarski(A_149), k1_tarski(B_150))=k2_xboole_0(k1_tarski(A_149), k1_tarski(B_150)) | B_150=A_149)), inference(superposition, [status(thm), theory('equality')], [c_682, c_16])).
% 2.78/1.38  tff(c_40, plain, (![A_52, B_53]: (k5_xboole_0(k1_tarski(A_52), k1_tarski(B_53))=k2_tarski(A_52, B_53) | B_53=A_52)), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.78/1.38  tff(c_814, plain, (![A_151, B_152]: (k2_xboole_0(k1_tarski(A_151), k1_tarski(B_152))=k2_tarski(A_151, B_152) | B_152=A_151 | B_152=A_151)), inference(superposition, [status(thm), theory('equality')], [c_788, c_40])).
% 2.78/1.38  tff(c_32, plain, (![A_44, B_45]: (k3_tarski(k2_tarski(A_44, B_45))=k2_xboole_0(A_44, B_45))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.78/1.38  tff(c_42, plain, (k3_tarski(k2_tarski(k1_tarski('#skF_3'), k1_tarski('#skF_4')))!=k2_tarski('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.78/1.38  tff(c_43, plain, (k2_xboole_0(k1_tarski('#skF_3'), k1_tarski('#skF_4'))!=k2_tarski('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_42])).
% 2.78/1.38  tff(c_844, plain, ('#skF_3'='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_814, c_43])).
% 2.78/1.38  tff(c_850, plain, (k2_xboole_0(k1_tarski('#skF_4'), k1_tarski('#skF_4'))!=k2_tarski('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_844, c_844, c_43])).
% 2.78/1.38  tff(c_853, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_444, c_133, c_18, c_850])).
% 2.78/1.38  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.78/1.38  
% 2.78/1.38  Inference rules
% 2.78/1.38  ----------------------
% 2.78/1.38  #Ref     : 0
% 2.78/1.38  #Sup     : 190
% 2.78/1.38  #Fact    : 0
% 2.78/1.38  #Define  : 0
% 2.78/1.38  #Split   : 0
% 2.78/1.38  #Chain   : 0
% 2.78/1.38  #Close   : 0
% 2.78/1.38  
% 2.78/1.38  Ordering : KBO
% 2.78/1.38  
% 2.78/1.38  Simplification rules
% 2.78/1.38  ----------------------
% 2.78/1.38  #Subsume      : 24
% 2.78/1.38  #Demod        : 77
% 2.78/1.38  #Tautology    : 131
% 2.78/1.38  #SimpNegUnit  : 6
% 2.78/1.38  #BackRed      : 1
% 2.78/1.38  
% 2.78/1.38  #Partial instantiations: 0
% 2.78/1.38  #Strategies tried      : 1
% 2.78/1.38  
% 2.78/1.38  Timing (in seconds)
% 2.78/1.38  ----------------------
% 2.78/1.38  Preprocessing        : 0.32
% 2.78/1.38  Parsing              : 0.17
% 2.78/1.38  CNF conversion       : 0.02
% 2.78/1.38  Main loop            : 0.30
% 2.78/1.38  Inferencing          : 0.12
% 2.78/1.38  Reduction            : 0.10
% 2.78/1.38  Demodulation         : 0.08
% 2.78/1.38  BG Simplification    : 0.02
% 2.78/1.38  Subsumption          : 0.04
% 2.78/1.38  Abstraction          : 0.02
% 2.78/1.38  MUC search           : 0.00
% 2.78/1.38  Cooper               : 0.00
% 2.78/1.38  Total                : 0.65
% 2.78/1.38  Index Insertion      : 0.00
% 2.78/1.38  Index Deletion       : 0.00
% 2.78/1.38  Index Matching       : 0.00
% 2.78/1.38  BG Taut test         : 0.00
%------------------------------------------------------------------------------
