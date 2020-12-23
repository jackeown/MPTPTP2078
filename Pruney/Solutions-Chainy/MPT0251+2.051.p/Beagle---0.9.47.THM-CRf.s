%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:50:53 EST 2020

% Result     : Theorem 3.16s
% Output     : CNFRefutation 3.48s
% Verified   : 
% Statistics : Number of formulae       :   71 (  84 expanded)
%              Number of leaves         :   33 (  41 expanded)
%              Depth                    :   12
%              Number of atoms          :   73 (  88 expanded)
%              Number of equality atoms :   40 (  53 expanded)
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

tff(f_76,negated_conjecture,(
    ~ ! [A,B] :
        ( r2_hidden(A,B)
       => k2_xboole_0(k1_tarski(A),B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_zfmisc_1)).

tff(f_39,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

tff(f_49,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_53,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_55,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_65,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_47,axiom,(
    ! [A,B] : k4_xboole_0(k2_xboole_0(A,B),B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_xboole_1)).

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

tff(f_57,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_71,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_tarski(A,B),C)
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_zfmisc_1)).

tff(f_45,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

tff(c_46,plain,(
    r2_hidden('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_12,plain,(
    ! [A_7] : k2_xboole_0(A_7,k1_xboole_0) = A_7 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_20,plain,(
    ! [A_14] : r1_xboole_0(A_14,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_101,plain,(
    ! [B_40,A_41] :
      ( r1_xboole_0(B_40,A_41)
      | ~ r1_xboole_0(A_41,B_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_104,plain,(
    ! [A_14] : r1_xboole_0(k1_xboole_0,A_14) ),
    inference(resolution,[status(thm)],[c_20,c_101])).

tff(c_172,plain,(
    ! [A_53,B_54] :
      ( k4_xboole_0(A_53,B_54) = A_53
      | ~ r1_xboole_0(A_53,B_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_183,plain,(
    ! [A_14] : k4_xboole_0(k1_xboole_0,A_14) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_104,c_172])).

tff(c_26,plain,(
    ! [B_18,A_17] : k2_tarski(B_18,A_17) = k2_tarski(A_17,B_18) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_114,plain,(
    ! [A_45,B_46] : k3_tarski(k2_tarski(A_45,B_46)) = k2_xboole_0(A_45,B_46) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_211,plain,(
    ! [A_57,B_58] : k3_tarski(k2_tarski(A_57,B_58)) = k2_xboole_0(B_58,A_57) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_114])).

tff(c_36,plain,(
    ! [A_29,B_30] : k3_tarski(k2_tarski(A_29,B_30)) = k2_xboole_0(A_29,B_30) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_245,plain,(
    ! [B_61,A_62] : k2_xboole_0(B_61,A_62) = k2_xboole_0(A_62,B_61) ),
    inference(superposition,[status(thm),theory(equality)],[c_211,c_36])).

tff(c_261,plain,(
    ! [A_62] : k2_xboole_0(k1_xboole_0,A_62) = A_62 ),
    inference(superposition,[status(thm),theory(equality)],[c_245,c_12])).

tff(c_400,plain,(
    ! [A_77,B_78] : k4_xboole_0(k2_xboole_0(A_77,B_78),B_78) = k4_xboole_0(A_77,B_78) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_413,plain,(
    ! [A_62] : k4_xboole_0(k1_xboole_0,A_62) = k4_xboole_0(A_62,A_62) ),
    inference(superposition,[status(thm),theory(equality)],[c_261,c_400])).

tff(c_433,plain,(
    ! [A_62] : k4_xboole_0(A_62,A_62) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_183,c_413])).

tff(c_8,plain,(
    ! [B_4] : r1_tarski(B_4,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_158,plain,(
    ! [A_50,B_51] :
      ( k3_xboole_0(A_50,B_51) = A_50
      | ~ r1_tarski(A_50,B_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_162,plain,(
    ! [B_4] : k3_xboole_0(B_4,B_4) = B_4 ),
    inference(resolution,[status(thm)],[c_8,c_158])).

tff(c_332,plain,(
    ! [A_64,B_65] : k5_xboole_0(A_64,k3_xboole_0(A_64,B_65)) = k4_xboole_0(A_64,B_65) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_341,plain,(
    ! [B_4] : k5_xboole_0(B_4,B_4) = k4_xboole_0(B_4,B_4) ),
    inference(superposition,[status(thm),theory(equality)],[c_162,c_332])).

tff(c_436,plain,(
    ! [B_4] : k5_xboole_0(B_4,B_4) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_433,c_341])).

tff(c_28,plain,(
    ! [A_19] : k2_tarski(A_19,A_19) = k1_tarski(A_19) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_650,plain,(
    ! [A_97,B_98,C_99] :
      ( r1_tarski(k2_tarski(A_97,B_98),C_99)
      | ~ r2_hidden(B_98,C_99)
      | ~ r2_hidden(A_97,C_99) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_1388,plain,(
    ! [A_122,C_123] :
      ( r1_tarski(k1_tarski(A_122),C_123)
      | ~ r2_hidden(A_122,C_123)
      | ~ r2_hidden(A_122,C_123) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_650])).

tff(c_14,plain,(
    ! [A_8,B_9] :
      ( k3_xboole_0(A_8,B_9) = A_8
      | ~ r1_tarski(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_1691,plain,(
    ! [A_130,C_131] :
      ( k3_xboole_0(k1_tarski(A_130),C_131) = k1_tarski(A_130)
      | ~ r2_hidden(A_130,C_131) ) ),
    inference(resolution,[status(thm)],[c_1388,c_14])).

tff(c_10,plain,(
    ! [A_5,B_6] : k5_xboole_0(A_5,k3_xboole_0(A_5,B_6)) = k4_xboole_0(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_1697,plain,(
    ! [A_130,C_131] :
      ( k5_xboole_0(k1_tarski(A_130),k1_tarski(A_130)) = k4_xboole_0(k1_tarski(A_130),C_131)
      | ~ r2_hidden(A_130,C_131) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1691,c_10])).

tff(c_1718,plain,(
    ! [A_132,C_133] :
      ( k4_xboole_0(k1_tarski(A_132),C_133) = k1_xboole_0
      | ~ r2_hidden(A_132,C_133) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_436,c_1697])).

tff(c_16,plain,(
    ! [A_10,B_11] : k2_xboole_0(A_10,k4_xboole_0(B_11,A_10)) = k2_xboole_0(A_10,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_1756,plain,(
    ! [C_133,A_132] :
      ( k2_xboole_0(C_133,k1_tarski(A_132)) = k2_xboole_0(C_133,k1_xboole_0)
      | ~ r2_hidden(A_132,C_133) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1718,c_16])).

tff(c_1814,plain,(
    ! [C_135,A_136] :
      ( k2_xboole_0(C_135,k1_tarski(A_136)) = C_135
      | ~ r2_hidden(A_136,C_135) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_1756])).

tff(c_217,plain,(
    ! [B_58,A_57] : k2_xboole_0(B_58,A_57) = k2_xboole_0(A_57,B_58) ),
    inference(superposition,[status(thm),theory(equality)],[c_211,c_36])).

tff(c_44,plain,(
    k2_xboole_0(k1_tarski('#skF_1'),'#skF_2') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_244,plain,(
    k2_xboole_0('#skF_2',k1_tarski('#skF_1')) != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_217,c_44])).

tff(c_1859,plain,(
    ~ r2_hidden('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_1814,c_244])).

tff(c_1914,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_1859])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n021.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 19:39:04 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.16/1.68  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.16/1.69  
% 3.16/1.69  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.16/1.69  %$ r2_hidden > r1_xboole_0 > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1
% 3.16/1.69  
% 3.16/1.69  %Foreground sorts:
% 3.16/1.69  
% 3.16/1.69  
% 3.16/1.69  %Background operators:
% 3.16/1.69  
% 3.16/1.69  
% 3.16/1.69  %Foreground operators:
% 3.16/1.69  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.16/1.69  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.16/1.69  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.16/1.69  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.16/1.69  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.16/1.69  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.16/1.69  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.16/1.69  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.16/1.69  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.16/1.69  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.16/1.69  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.16/1.69  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.16/1.69  tff('#skF_2', type, '#skF_2': $i).
% 3.16/1.69  tff('#skF_1', type, '#skF_1': $i).
% 3.16/1.69  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.16/1.69  tff(k3_tarski, type, k3_tarski: $i > $i).
% 3.16/1.69  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.16/1.69  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.16/1.69  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.16/1.69  
% 3.48/1.70  tff(f_76, negated_conjecture, ~(![A, B]: (r2_hidden(A, B) => (k2_xboole_0(k1_tarski(A), B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_zfmisc_1)).
% 3.48/1.70  tff(f_39, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 3.48/1.70  tff(f_49, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 3.48/1.70  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 3.48/1.70  tff(f_53, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 3.48/1.70  tff(f_55, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 3.48/1.70  tff(f_65, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 3.48/1.70  tff(f_47, axiom, (![A, B]: (k4_xboole_0(k2_xboole_0(A, B), B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t40_xboole_1)).
% 3.48/1.70  tff(f_35, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.48/1.70  tff(f_43, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 3.48/1.70  tff(f_37, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 3.48/1.70  tff(f_57, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 3.48/1.70  tff(f_71, axiom, (![A, B, C]: (r1_tarski(k2_tarski(A, B), C) <=> (r2_hidden(A, C) & r2_hidden(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 3.48/1.70  tff(f_45, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_xboole_1)).
% 3.48/1.70  tff(c_46, plain, (r2_hidden('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.48/1.70  tff(c_12, plain, (![A_7]: (k2_xboole_0(A_7, k1_xboole_0)=A_7)), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.48/1.70  tff(c_20, plain, (![A_14]: (r1_xboole_0(A_14, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.48/1.70  tff(c_101, plain, (![B_40, A_41]: (r1_xboole_0(B_40, A_41) | ~r1_xboole_0(A_41, B_40))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.48/1.70  tff(c_104, plain, (![A_14]: (r1_xboole_0(k1_xboole_0, A_14))), inference(resolution, [status(thm)], [c_20, c_101])).
% 3.48/1.70  tff(c_172, plain, (![A_53, B_54]: (k4_xboole_0(A_53, B_54)=A_53 | ~r1_xboole_0(A_53, B_54))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.48/1.70  tff(c_183, plain, (![A_14]: (k4_xboole_0(k1_xboole_0, A_14)=k1_xboole_0)), inference(resolution, [status(thm)], [c_104, c_172])).
% 3.48/1.70  tff(c_26, plain, (![B_18, A_17]: (k2_tarski(B_18, A_17)=k2_tarski(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.48/1.70  tff(c_114, plain, (![A_45, B_46]: (k3_tarski(k2_tarski(A_45, B_46))=k2_xboole_0(A_45, B_46))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.48/1.70  tff(c_211, plain, (![A_57, B_58]: (k3_tarski(k2_tarski(A_57, B_58))=k2_xboole_0(B_58, A_57))), inference(superposition, [status(thm), theory('equality')], [c_26, c_114])).
% 3.48/1.70  tff(c_36, plain, (![A_29, B_30]: (k3_tarski(k2_tarski(A_29, B_30))=k2_xboole_0(A_29, B_30))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.48/1.70  tff(c_245, plain, (![B_61, A_62]: (k2_xboole_0(B_61, A_62)=k2_xboole_0(A_62, B_61))), inference(superposition, [status(thm), theory('equality')], [c_211, c_36])).
% 3.48/1.70  tff(c_261, plain, (![A_62]: (k2_xboole_0(k1_xboole_0, A_62)=A_62)), inference(superposition, [status(thm), theory('equality')], [c_245, c_12])).
% 3.48/1.70  tff(c_400, plain, (![A_77, B_78]: (k4_xboole_0(k2_xboole_0(A_77, B_78), B_78)=k4_xboole_0(A_77, B_78))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.48/1.70  tff(c_413, plain, (![A_62]: (k4_xboole_0(k1_xboole_0, A_62)=k4_xboole_0(A_62, A_62))), inference(superposition, [status(thm), theory('equality')], [c_261, c_400])).
% 3.48/1.70  tff(c_433, plain, (![A_62]: (k4_xboole_0(A_62, A_62)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_183, c_413])).
% 3.48/1.70  tff(c_8, plain, (![B_4]: (r1_tarski(B_4, B_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.48/1.70  tff(c_158, plain, (![A_50, B_51]: (k3_xboole_0(A_50, B_51)=A_50 | ~r1_tarski(A_50, B_51))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.48/1.70  tff(c_162, plain, (![B_4]: (k3_xboole_0(B_4, B_4)=B_4)), inference(resolution, [status(thm)], [c_8, c_158])).
% 3.48/1.70  tff(c_332, plain, (![A_64, B_65]: (k5_xboole_0(A_64, k3_xboole_0(A_64, B_65))=k4_xboole_0(A_64, B_65))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.48/1.70  tff(c_341, plain, (![B_4]: (k5_xboole_0(B_4, B_4)=k4_xboole_0(B_4, B_4))), inference(superposition, [status(thm), theory('equality')], [c_162, c_332])).
% 3.48/1.70  tff(c_436, plain, (![B_4]: (k5_xboole_0(B_4, B_4)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_433, c_341])).
% 3.48/1.70  tff(c_28, plain, (![A_19]: (k2_tarski(A_19, A_19)=k1_tarski(A_19))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.48/1.70  tff(c_650, plain, (![A_97, B_98, C_99]: (r1_tarski(k2_tarski(A_97, B_98), C_99) | ~r2_hidden(B_98, C_99) | ~r2_hidden(A_97, C_99))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.48/1.70  tff(c_1388, plain, (![A_122, C_123]: (r1_tarski(k1_tarski(A_122), C_123) | ~r2_hidden(A_122, C_123) | ~r2_hidden(A_122, C_123))), inference(superposition, [status(thm), theory('equality')], [c_28, c_650])).
% 3.48/1.70  tff(c_14, plain, (![A_8, B_9]: (k3_xboole_0(A_8, B_9)=A_8 | ~r1_tarski(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.48/1.70  tff(c_1691, plain, (![A_130, C_131]: (k3_xboole_0(k1_tarski(A_130), C_131)=k1_tarski(A_130) | ~r2_hidden(A_130, C_131))), inference(resolution, [status(thm)], [c_1388, c_14])).
% 3.48/1.70  tff(c_10, plain, (![A_5, B_6]: (k5_xboole_0(A_5, k3_xboole_0(A_5, B_6))=k4_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.48/1.70  tff(c_1697, plain, (![A_130, C_131]: (k5_xboole_0(k1_tarski(A_130), k1_tarski(A_130))=k4_xboole_0(k1_tarski(A_130), C_131) | ~r2_hidden(A_130, C_131))), inference(superposition, [status(thm), theory('equality')], [c_1691, c_10])).
% 3.48/1.70  tff(c_1718, plain, (![A_132, C_133]: (k4_xboole_0(k1_tarski(A_132), C_133)=k1_xboole_0 | ~r2_hidden(A_132, C_133))), inference(demodulation, [status(thm), theory('equality')], [c_436, c_1697])).
% 3.48/1.70  tff(c_16, plain, (![A_10, B_11]: (k2_xboole_0(A_10, k4_xboole_0(B_11, A_10))=k2_xboole_0(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.48/1.70  tff(c_1756, plain, (![C_133, A_132]: (k2_xboole_0(C_133, k1_tarski(A_132))=k2_xboole_0(C_133, k1_xboole_0) | ~r2_hidden(A_132, C_133))), inference(superposition, [status(thm), theory('equality')], [c_1718, c_16])).
% 3.48/1.70  tff(c_1814, plain, (![C_135, A_136]: (k2_xboole_0(C_135, k1_tarski(A_136))=C_135 | ~r2_hidden(A_136, C_135))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_1756])).
% 3.48/1.70  tff(c_217, plain, (![B_58, A_57]: (k2_xboole_0(B_58, A_57)=k2_xboole_0(A_57, B_58))), inference(superposition, [status(thm), theory('equality')], [c_211, c_36])).
% 3.48/1.70  tff(c_44, plain, (k2_xboole_0(k1_tarski('#skF_1'), '#skF_2')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.48/1.70  tff(c_244, plain, (k2_xboole_0('#skF_2', k1_tarski('#skF_1'))!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_217, c_44])).
% 3.48/1.70  tff(c_1859, plain, (~r2_hidden('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_1814, c_244])).
% 3.48/1.70  tff(c_1914, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_46, c_1859])).
% 3.48/1.70  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.48/1.70  
% 3.48/1.70  Inference rules
% 3.48/1.70  ----------------------
% 3.48/1.70  #Ref     : 0
% 3.48/1.70  #Sup     : 447
% 3.48/1.70  #Fact    : 0
% 3.48/1.70  #Define  : 0
% 3.48/1.70  #Split   : 0
% 3.48/1.70  #Chain   : 0
% 3.48/1.70  #Close   : 0
% 3.48/1.70  
% 3.48/1.70  Ordering : KBO
% 3.48/1.70  
% 3.48/1.70  Simplification rules
% 3.48/1.70  ----------------------
% 3.48/1.70  #Subsume      : 39
% 3.48/1.70  #Demod        : 365
% 3.48/1.70  #Tautology    : 313
% 3.48/1.70  #SimpNegUnit  : 0
% 3.48/1.70  #BackRed      : 3
% 3.48/1.70  
% 3.48/1.70  #Partial instantiations: 0
% 3.48/1.70  #Strategies tried      : 1
% 3.48/1.70  
% 3.48/1.70  Timing (in seconds)
% 3.48/1.70  ----------------------
% 3.48/1.71  Preprocessing        : 0.38
% 3.48/1.71  Parsing              : 0.21
% 3.48/1.71  CNF conversion       : 0.02
% 3.48/1.71  Main loop            : 0.45
% 3.48/1.71  Inferencing          : 0.16
% 3.48/1.71  Reduction            : 0.18
% 3.48/1.71  Demodulation         : 0.15
% 3.48/1.71  BG Simplification    : 0.02
% 3.48/1.71  Subsumption          : 0.06
% 3.48/1.71  Abstraction          : 0.03
% 3.48/1.71  MUC search           : 0.00
% 3.48/1.71  Cooper               : 0.00
% 3.48/1.71  Total                : 0.86
% 3.48/1.71  Index Insertion      : 0.00
% 3.48/1.71  Index Deletion       : 0.00
% 3.48/1.71  Index Matching       : 0.00
% 3.48/1.71  BG Taut test         : 0.00
%------------------------------------------------------------------------------
