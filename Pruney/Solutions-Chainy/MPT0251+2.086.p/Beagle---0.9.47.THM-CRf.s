%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:50:58 EST 2020

% Result     : Theorem 3.75s
% Output     : CNFRefutation 3.75s
% Verified   : 
% Statistics : Number of formulae       :   73 ( 152 expanded)
%              Number of leaves         :   30 (  63 expanded)
%              Depth                    :   13
%              Number of atoms          :   72 ( 165 expanded)
%              Number of equality atoms :   48 ( 124 expanded)
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

tff(f_70,negated_conjecture,(
    ~ ! [A,B] :
        ( r2_hidden(A,B)
       => k2_xboole_0(k1_tarski(A),B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_zfmisc_1)).

tff(f_33,axiom,(
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

tff(f_39,axiom,(
    ! [A,B] : k2_xboole_0(A,k3_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_37,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

tff(f_45,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_47,axiom,(
    ! [A,B] : k4_xboole_0(k2_xboole_0(A,B),B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_xboole_1)).

tff(f_49,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_51,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_65,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_tarski(A,B),C)
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_zfmisc_1)).

tff(c_42,plain,(
    r2_hidden('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_8,plain,(
    ! [B_4] : r1_tarski(B_4,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_201,plain,(
    ! [A_46,B_47] :
      ( k3_xboole_0(A_46,B_47) = A_46
      | ~ r1_tarski(A_46,B_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_206,plain,(
    ! [B_48] : k3_xboole_0(B_48,B_48) = B_48 ),
    inference(resolution,[status(thm)],[c_8,c_201])).

tff(c_14,plain,(
    ! [A_8,B_9] : k2_xboole_0(A_8,k3_xboole_0(A_8,B_9)) = A_8 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_216,plain,(
    ! [B_48] : k2_xboole_0(B_48,B_48) = B_48 ),
    inference(superposition,[status(thm),theory(equality)],[c_206,c_14])).

tff(c_64,plain,(
    ! [B_36,A_37] : k2_xboole_0(B_36,A_37) = k2_xboole_0(A_37,B_36) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_12,plain,(
    ! [A_7] : k2_xboole_0(A_7,k1_xboole_0) = A_7 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_80,plain,(
    ! [A_37] : k2_xboole_0(k1_xboole_0,A_37) = A_37 ),
    inference(superposition,[status(thm),theory(equality)],[c_64,c_12])).

tff(c_321,plain,(
    ! [A_56,B_57] : k2_xboole_0(A_56,k4_xboole_0(B_57,A_56)) = k2_xboole_0(A_56,B_57) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_331,plain,(
    ! [B_57] : k4_xboole_0(B_57,k1_xboole_0) = k2_xboole_0(k1_xboole_0,B_57) ),
    inference(superposition,[status(thm),theory(equality)],[c_321,c_80])).

tff(c_349,plain,(
    ! [B_57] : k4_xboole_0(B_57,k1_xboole_0) = B_57 ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_331])).

tff(c_150,plain,(
    ! [A_39,B_40] : k2_xboole_0(A_39,k3_xboole_0(A_39,B_40)) = A_39 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_164,plain,(
    ! [B_40] : k3_xboole_0(k1_xboole_0,B_40) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_80,c_150])).

tff(c_379,plain,(
    ! [A_59,B_60] : k5_xboole_0(A_59,k3_xboole_0(A_59,B_60)) = k4_xboole_0(A_59,B_60) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_508,plain,(
    ! [B_70] : k5_xboole_0(k1_xboole_0,k1_xboole_0) = k4_xboole_0(k1_xboole_0,B_70) ),
    inference(superposition,[status(thm),theory(equality)],[c_164,c_379])).

tff(c_205,plain,(
    ! [B_4] : k3_xboole_0(B_4,B_4) = B_4 ),
    inference(resolution,[status(thm)],[c_8,c_201])).

tff(c_388,plain,(
    ! [B_4] : k5_xboole_0(B_4,B_4) = k4_xboole_0(B_4,B_4) ),
    inference(superposition,[status(thm),theory(equality)],[c_205,c_379])).

tff(c_517,plain,(
    ! [B_70] : k4_xboole_0(k1_xboole_0,k1_xboole_0) = k4_xboole_0(k1_xboole_0,B_70) ),
    inference(superposition,[status(thm),theory(equality)],[c_508,c_388])).

tff(c_534,plain,(
    ! [B_70] : k4_xboole_0(k1_xboole_0,B_70) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_349,c_517])).

tff(c_267,plain,(
    ! [A_51,B_52] : k4_xboole_0(k2_xboole_0(A_51,B_52),B_52) = k4_xboole_0(A_51,B_52) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_282,plain,(
    ! [A_37] : k4_xboole_0(k1_xboole_0,A_37) = k4_xboole_0(A_37,A_37) ),
    inference(superposition,[status(thm),theory(equality)],[c_80,c_267])).

tff(c_540,plain,(
    ! [A_37] : k4_xboole_0(A_37,A_37) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_534,c_282])).

tff(c_630,plain,(
    ! [A_77,B_78] : k5_xboole_0(A_77,k4_xboole_0(B_78,A_77)) = k2_xboole_0(A_77,B_78) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_639,plain,(
    ! [A_37] : k5_xboole_0(A_37,k1_xboole_0) = k2_xboole_0(A_37,A_37) ),
    inference(superposition,[status(thm),theory(equality)],[c_540,c_630])).

tff(c_651,plain,(
    ! [A_37] : k5_xboole_0(A_37,k1_xboole_0) = A_37 ),
    inference(demodulation,[status(thm),theory(equality)],[c_216,c_639])).

tff(c_591,plain,(
    ! [B_4] : k5_xboole_0(B_4,B_4) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_540,c_388])).

tff(c_24,plain,(
    ! [A_18] : k2_tarski(A_18,A_18) = k1_tarski(A_18) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_857,plain,(
    ! [A_96,B_97,C_98] :
      ( r1_tarski(k2_tarski(A_96,B_97),C_98)
      | ~ r2_hidden(B_97,C_98)
      | ~ r2_hidden(A_96,C_98) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_1210,plain,(
    ! [A_109,C_110] :
      ( r1_tarski(k1_tarski(A_109),C_110)
      | ~ r2_hidden(A_109,C_110)
      | ~ r2_hidden(A_109,C_110) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_857])).

tff(c_16,plain,(
    ! [A_10,B_11] :
      ( k3_xboole_0(A_10,B_11) = A_10
      | ~ r1_tarski(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_2982,plain,(
    ! [A_143,C_144] :
      ( k3_xboole_0(k1_tarski(A_143),C_144) = k1_tarski(A_143)
      | ~ r2_hidden(A_143,C_144) ) ),
    inference(resolution,[status(thm)],[c_1210,c_16])).

tff(c_10,plain,(
    ! [A_5,B_6] : k5_xboole_0(A_5,k3_xboole_0(A_5,B_6)) = k4_xboole_0(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_2997,plain,(
    ! [A_143,C_144] :
      ( k5_xboole_0(k1_tarski(A_143),k1_tarski(A_143)) = k4_xboole_0(k1_tarski(A_143),C_144)
      | ~ r2_hidden(A_143,C_144) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2982,c_10])).

tff(c_3025,plain,(
    ! [A_145,C_146] :
      ( k4_xboole_0(k1_tarski(A_145),C_146) = k1_xboole_0
      | ~ r2_hidden(A_145,C_146) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_591,c_2997])).

tff(c_22,plain,(
    ! [A_16,B_17] : k5_xboole_0(A_16,k4_xboole_0(B_17,A_16)) = k2_xboole_0(A_16,B_17) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_3058,plain,(
    ! [C_146,A_145] :
      ( k2_xboole_0(C_146,k1_tarski(A_145)) = k5_xboole_0(C_146,k1_xboole_0)
      | ~ r2_hidden(A_145,C_146) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3025,c_22])).

tff(c_3110,plain,(
    ! [C_148,A_149] :
      ( k2_xboole_0(C_148,k1_tarski(A_149)) = C_148
      | ~ r2_hidden(A_149,C_148) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_651,c_3058])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_40,plain,(
    k2_xboole_0(k1_tarski('#skF_1'),'#skF_2') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_44,plain,(
    k2_xboole_0('#skF_2',k1_tarski('#skF_1')) != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_40])).

tff(c_3205,plain,(
    ~ r2_hidden('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_3110,c_44])).

tff(c_3271,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_3205])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n014.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 12:15:07 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.75/1.70  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.75/1.70  
% 3.75/1.70  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.75/1.71  %$ r2_hidden > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1
% 3.75/1.71  
% 3.75/1.71  %Foreground sorts:
% 3.75/1.71  
% 3.75/1.71  
% 3.75/1.71  %Background operators:
% 3.75/1.71  
% 3.75/1.71  
% 3.75/1.71  %Foreground operators:
% 3.75/1.71  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.75/1.71  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.75/1.71  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.75/1.71  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.75/1.71  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.75/1.71  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.75/1.71  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.75/1.71  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.75/1.71  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.75/1.71  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.75/1.71  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.75/1.71  tff('#skF_2', type, '#skF_2': $i).
% 3.75/1.71  tff('#skF_1', type, '#skF_1': $i).
% 3.75/1.71  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.75/1.71  tff(k3_tarski, type, k3_tarski: $i > $i).
% 3.75/1.71  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.75/1.71  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.75/1.71  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.75/1.71  
% 3.75/1.73  tff(f_70, negated_conjecture, ~(![A, B]: (r2_hidden(A, B) => (k2_xboole_0(k1_tarski(A), B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_zfmisc_1)).
% 3.75/1.73  tff(f_33, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.75/1.73  tff(f_43, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 3.75/1.73  tff(f_39, axiom, (![A, B]: (k2_xboole_0(A, k3_xboole_0(A, B)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t22_xboole_1)).
% 3.75/1.73  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 3.75/1.73  tff(f_37, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 3.75/1.73  tff(f_45, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_xboole_1)).
% 3.75/1.73  tff(f_35, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 3.75/1.73  tff(f_47, axiom, (![A, B]: (k4_xboole_0(k2_xboole_0(A, B), B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t40_xboole_1)).
% 3.75/1.73  tff(f_49, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_xboole_1)).
% 3.75/1.73  tff(f_51, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 3.75/1.73  tff(f_65, axiom, (![A, B, C]: (r1_tarski(k2_tarski(A, B), C) <=> (r2_hidden(A, C) & r2_hidden(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 3.75/1.73  tff(c_42, plain, (r2_hidden('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.75/1.73  tff(c_8, plain, (![B_4]: (r1_tarski(B_4, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.75/1.73  tff(c_201, plain, (![A_46, B_47]: (k3_xboole_0(A_46, B_47)=A_46 | ~r1_tarski(A_46, B_47))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.75/1.73  tff(c_206, plain, (![B_48]: (k3_xboole_0(B_48, B_48)=B_48)), inference(resolution, [status(thm)], [c_8, c_201])).
% 3.75/1.73  tff(c_14, plain, (![A_8, B_9]: (k2_xboole_0(A_8, k3_xboole_0(A_8, B_9))=A_8)), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.75/1.73  tff(c_216, plain, (![B_48]: (k2_xboole_0(B_48, B_48)=B_48)), inference(superposition, [status(thm), theory('equality')], [c_206, c_14])).
% 3.75/1.73  tff(c_64, plain, (![B_36, A_37]: (k2_xboole_0(B_36, A_37)=k2_xboole_0(A_37, B_36))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.75/1.73  tff(c_12, plain, (![A_7]: (k2_xboole_0(A_7, k1_xboole_0)=A_7)), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.75/1.73  tff(c_80, plain, (![A_37]: (k2_xboole_0(k1_xboole_0, A_37)=A_37)), inference(superposition, [status(thm), theory('equality')], [c_64, c_12])).
% 3.75/1.73  tff(c_321, plain, (![A_56, B_57]: (k2_xboole_0(A_56, k4_xboole_0(B_57, A_56))=k2_xboole_0(A_56, B_57))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.75/1.73  tff(c_331, plain, (![B_57]: (k4_xboole_0(B_57, k1_xboole_0)=k2_xboole_0(k1_xboole_0, B_57))), inference(superposition, [status(thm), theory('equality')], [c_321, c_80])).
% 3.75/1.73  tff(c_349, plain, (![B_57]: (k4_xboole_0(B_57, k1_xboole_0)=B_57)), inference(demodulation, [status(thm), theory('equality')], [c_80, c_331])).
% 3.75/1.73  tff(c_150, plain, (![A_39, B_40]: (k2_xboole_0(A_39, k3_xboole_0(A_39, B_40))=A_39)), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.75/1.73  tff(c_164, plain, (![B_40]: (k3_xboole_0(k1_xboole_0, B_40)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_80, c_150])).
% 3.75/1.73  tff(c_379, plain, (![A_59, B_60]: (k5_xboole_0(A_59, k3_xboole_0(A_59, B_60))=k4_xboole_0(A_59, B_60))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.75/1.73  tff(c_508, plain, (![B_70]: (k5_xboole_0(k1_xboole_0, k1_xboole_0)=k4_xboole_0(k1_xboole_0, B_70))), inference(superposition, [status(thm), theory('equality')], [c_164, c_379])).
% 3.75/1.73  tff(c_205, plain, (![B_4]: (k3_xboole_0(B_4, B_4)=B_4)), inference(resolution, [status(thm)], [c_8, c_201])).
% 3.75/1.73  tff(c_388, plain, (![B_4]: (k5_xboole_0(B_4, B_4)=k4_xboole_0(B_4, B_4))), inference(superposition, [status(thm), theory('equality')], [c_205, c_379])).
% 3.75/1.73  tff(c_517, plain, (![B_70]: (k4_xboole_0(k1_xboole_0, k1_xboole_0)=k4_xboole_0(k1_xboole_0, B_70))), inference(superposition, [status(thm), theory('equality')], [c_508, c_388])).
% 3.75/1.73  tff(c_534, plain, (![B_70]: (k4_xboole_0(k1_xboole_0, B_70)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_349, c_517])).
% 3.75/1.73  tff(c_267, plain, (![A_51, B_52]: (k4_xboole_0(k2_xboole_0(A_51, B_52), B_52)=k4_xboole_0(A_51, B_52))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.75/1.73  tff(c_282, plain, (![A_37]: (k4_xboole_0(k1_xboole_0, A_37)=k4_xboole_0(A_37, A_37))), inference(superposition, [status(thm), theory('equality')], [c_80, c_267])).
% 3.75/1.73  tff(c_540, plain, (![A_37]: (k4_xboole_0(A_37, A_37)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_534, c_282])).
% 3.75/1.73  tff(c_630, plain, (![A_77, B_78]: (k5_xboole_0(A_77, k4_xboole_0(B_78, A_77))=k2_xboole_0(A_77, B_78))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.75/1.73  tff(c_639, plain, (![A_37]: (k5_xboole_0(A_37, k1_xboole_0)=k2_xboole_0(A_37, A_37))), inference(superposition, [status(thm), theory('equality')], [c_540, c_630])).
% 3.75/1.73  tff(c_651, plain, (![A_37]: (k5_xboole_0(A_37, k1_xboole_0)=A_37)), inference(demodulation, [status(thm), theory('equality')], [c_216, c_639])).
% 3.75/1.73  tff(c_591, plain, (![B_4]: (k5_xboole_0(B_4, B_4)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_540, c_388])).
% 3.75/1.73  tff(c_24, plain, (![A_18]: (k2_tarski(A_18, A_18)=k1_tarski(A_18))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.75/1.73  tff(c_857, plain, (![A_96, B_97, C_98]: (r1_tarski(k2_tarski(A_96, B_97), C_98) | ~r2_hidden(B_97, C_98) | ~r2_hidden(A_96, C_98))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.75/1.73  tff(c_1210, plain, (![A_109, C_110]: (r1_tarski(k1_tarski(A_109), C_110) | ~r2_hidden(A_109, C_110) | ~r2_hidden(A_109, C_110))), inference(superposition, [status(thm), theory('equality')], [c_24, c_857])).
% 3.75/1.73  tff(c_16, plain, (![A_10, B_11]: (k3_xboole_0(A_10, B_11)=A_10 | ~r1_tarski(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.75/1.73  tff(c_2982, plain, (![A_143, C_144]: (k3_xboole_0(k1_tarski(A_143), C_144)=k1_tarski(A_143) | ~r2_hidden(A_143, C_144))), inference(resolution, [status(thm)], [c_1210, c_16])).
% 3.75/1.73  tff(c_10, plain, (![A_5, B_6]: (k5_xboole_0(A_5, k3_xboole_0(A_5, B_6))=k4_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.75/1.73  tff(c_2997, plain, (![A_143, C_144]: (k5_xboole_0(k1_tarski(A_143), k1_tarski(A_143))=k4_xboole_0(k1_tarski(A_143), C_144) | ~r2_hidden(A_143, C_144))), inference(superposition, [status(thm), theory('equality')], [c_2982, c_10])).
% 3.75/1.73  tff(c_3025, plain, (![A_145, C_146]: (k4_xboole_0(k1_tarski(A_145), C_146)=k1_xboole_0 | ~r2_hidden(A_145, C_146))), inference(demodulation, [status(thm), theory('equality')], [c_591, c_2997])).
% 3.75/1.73  tff(c_22, plain, (![A_16, B_17]: (k5_xboole_0(A_16, k4_xboole_0(B_17, A_16))=k2_xboole_0(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.75/1.73  tff(c_3058, plain, (![C_146, A_145]: (k2_xboole_0(C_146, k1_tarski(A_145))=k5_xboole_0(C_146, k1_xboole_0) | ~r2_hidden(A_145, C_146))), inference(superposition, [status(thm), theory('equality')], [c_3025, c_22])).
% 3.75/1.73  tff(c_3110, plain, (![C_148, A_149]: (k2_xboole_0(C_148, k1_tarski(A_149))=C_148 | ~r2_hidden(A_149, C_148))), inference(demodulation, [status(thm), theory('equality')], [c_651, c_3058])).
% 3.75/1.73  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.75/1.73  tff(c_40, plain, (k2_xboole_0(k1_tarski('#skF_1'), '#skF_2')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.75/1.73  tff(c_44, plain, (k2_xboole_0('#skF_2', k1_tarski('#skF_1'))!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_2, c_40])).
% 3.75/1.73  tff(c_3205, plain, (~r2_hidden('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_3110, c_44])).
% 3.75/1.73  tff(c_3271, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_42, c_3205])).
% 3.75/1.73  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.75/1.73  
% 3.75/1.73  Inference rules
% 3.75/1.73  ----------------------
% 3.75/1.73  #Ref     : 0
% 3.75/1.73  #Sup     : 770
% 3.75/1.73  #Fact    : 0
% 3.75/1.73  #Define  : 0
% 3.75/1.73  #Split   : 0
% 3.75/1.73  #Chain   : 0
% 3.75/1.73  #Close   : 0
% 3.75/1.73  
% 3.75/1.73  Ordering : KBO
% 3.75/1.73  
% 3.75/1.73  Simplification rules
% 3.75/1.73  ----------------------
% 3.75/1.73  #Subsume      : 35
% 3.75/1.73  #Demod        : 966
% 3.75/1.73  #Tautology    : 607
% 3.75/1.73  #SimpNegUnit  : 0
% 3.75/1.73  #BackRed      : 5
% 3.75/1.73  
% 3.75/1.73  #Partial instantiations: 0
% 3.75/1.73  #Strategies tried      : 1
% 3.75/1.73  
% 3.75/1.73  Timing (in seconds)
% 3.75/1.73  ----------------------
% 3.75/1.73  Preprocessing        : 0.30
% 3.75/1.73  Parsing              : 0.16
% 3.75/1.73  CNF conversion       : 0.02
% 3.75/1.73  Main loop            : 0.62
% 3.75/1.73  Inferencing          : 0.20
% 3.75/1.73  Reduction            : 0.29
% 3.75/1.73  Demodulation         : 0.24
% 3.75/1.73  BG Simplification    : 0.02
% 3.75/1.73  Subsumption          : 0.07
% 3.75/1.73  Abstraction          : 0.04
% 3.75/1.73  MUC search           : 0.00
% 3.75/1.74  Cooper               : 0.00
% 3.75/1.74  Total                : 0.96
% 3.75/1.74  Index Insertion      : 0.00
% 3.75/1.74  Index Deletion       : 0.00
% 3.75/1.74  Index Matching       : 0.00
% 3.75/1.74  BG Taut test         : 0.00
%------------------------------------------------------------------------------
