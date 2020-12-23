%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:50:56 EST 2020

% Result     : Theorem 3.02s
% Output     : CNFRefutation 3.02s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 125 expanded)
%              Number of leaves         :   34 (  56 expanded)
%              Depth                    :   16
%              Number of atoms          :   79 ( 151 expanded)
%              Number of equality atoms :   38 (  72 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_3 > #skF_4 > #skF_2 > #skF_1

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_91,negated_conjecture,(
    ~ ! [A,B] :
        ( r2_hidden(A,B)
       => k2_xboole_0(k1_tarski(A),B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_zfmisc_1)).

tff(f_62,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_68,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_34,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_72,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_58,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_66,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_52,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_60,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_70,axiom,(
    ! [A,B] : k4_xboole_0(k2_xboole_0(A,B),B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_xboole_1)).

tff(f_84,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(c_50,plain,(
    r2_hidden('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_24,plain,(
    ! [A_19] : k2_xboole_0(A_19,k1_xboole_0) = A_19 ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_73,plain,(
    ! [B_45,A_46] : k2_xboole_0(B_45,A_46) = k2_xboole_0(A_46,B_45) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_89,plain,(
    ! [A_46] : k2_xboole_0(k1_xboole_0,A_46) = A_46 ),
    inference(superposition,[status(thm),theory(equality)],[c_73,c_24])).

tff(c_444,plain,(
    ! [A_88,B_89] : k2_xboole_0(A_88,k4_xboole_0(B_89,A_88)) = k2_xboole_0(A_88,B_89) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_454,plain,(
    ! [B_89] : k4_xboole_0(B_89,k1_xboole_0) = k2_xboole_0(k1_xboole_0,B_89) ),
    inference(superposition,[status(thm),theory(equality)],[c_444,c_89])).

tff(c_489,plain,(
    ! [B_90] : k4_xboole_0(B_90,k1_xboole_0) = B_90 ),
    inference(demodulation,[status(thm),theory(equality)],[c_89,c_454])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( r2_hidden('#skF_1'(A_3,B_4),A_3)
      | r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_32,plain,(
    ! [A_26] : r1_xboole_0(A_26,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_158,plain,(
    ! [B_48,A_49] :
      ( r1_xboole_0(B_48,A_49)
      | ~ r1_xboole_0(A_49,B_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_161,plain,(
    ! [A_26] : r1_xboole_0(k1_xboole_0,A_26) ),
    inference(resolution,[status(thm)],[c_32,c_158])).

tff(c_20,plain,(
    ! [B_16] : r1_tarski(B_16,B_16) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_170,plain,(
    ! [A_53,B_54] :
      ( k3_xboole_0(A_53,B_54) = A_53
      | ~ r1_tarski(A_53,B_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_178,plain,(
    ! [B_16] : k3_xboole_0(B_16,B_16) = B_16 ),
    inference(resolution,[status(thm)],[c_20,c_170])).

tff(c_264,plain,(
    ! [A_71,B_72,C_73] :
      ( ~ r1_xboole_0(A_71,B_72)
      | ~ r2_hidden(C_73,k3_xboole_0(A_71,B_72)) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_273,plain,(
    ! [B_74,C_75] :
      ( ~ r1_xboole_0(B_74,B_74)
      | ~ r2_hidden(C_75,B_74) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_178,c_264])).

tff(c_282,plain,(
    ! [C_76] : ~ r2_hidden(C_76,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_161,c_273])).

tff(c_298,plain,(
    ! [B_79] : r1_tarski(k1_xboole_0,B_79) ),
    inference(resolution,[status(thm)],[c_8,c_282])).

tff(c_26,plain,(
    ! [A_20,B_21] :
      ( k3_xboole_0(A_20,B_21) = A_20
      | ~ r1_tarski(A_20,B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_306,plain,(
    ! [B_80] : k3_xboole_0(k1_xboole_0,B_80) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_298,c_26])).

tff(c_22,plain,(
    ! [A_17,B_18] : k5_xboole_0(A_17,k3_xboole_0(A_17,B_18)) = k4_xboole_0(A_17,B_18) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_349,plain,(
    ! [B_82] : k5_xboole_0(k1_xboole_0,k1_xboole_0) = k4_xboole_0(k1_xboole_0,B_82) ),
    inference(superposition,[status(thm),theory(equality)],[c_306,c_22])).

tff(c_314,plain,(
    ! [B_80] : k5_xboole_0(k1_xboole_0,k1_xboole_0) = k4_xboole_0(k1_xboole_0,B_80) ),
    inference(superposition,[status(thm),theory(equality)],[c_306,c_22])).

tff(c_352,plain,(
    ! [B_82,B_80] : k4_xboole_0(k1_xboole_0,B_82) = k4_xboole_0(k1_xboole_0,B_80) ),
    inference(superposition,[status(thm),theory(equality)],[c_349,c_314])).

tff(c_503,plain,(
    ! [B_80] : k4_xboole_0(k1_xboole_0,B_80) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_489,c_352])).

tff(c_389,plain,(
    ! [A_85,B_86] : k4_xboole_0(k2_xboole_0(A_85,B_86),B_86) = k4_xboole_0(A_85,B_86) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_401,plain,(
    ! [A_46] : k4_xboole_0(k1_xboole_0,A_46) = k4_xboole_0(A_46,A_46) ),
    inference(superposition,[status(thm),theory(equality)],[c_89,c_389])).

tff(c_529,plain,(
    ! [A_46] : k4_xboole_0(A_46,A_46) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_503,c_401])).

tff(c_236,plain,(
    ! [A_66,B_67] : k5_xboole_0(A_66,k3_xboole_0(A_66,B_67)) = k4_xboole_0(A_66,B_67) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_245,plain,(
    ! [B_16] : k5_xboole_0(B_16,B_16) = k4_xboole_0(B_16,B_16) ),
    inference(superposition,[status(thm),theory(equality)],[c_178,c_236])).

tff(c_576,plain,(
    ! [B_16] : k5_xboole_0(B_16,B_16) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_529,c_245])).

tff(c_44,plain,(
    ! [A_37,B_38] :
      ( r1_tarski(k1_tarski(A_37),B_38)
      | ~ r2_hidden(A_37,B_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_1161,plain,(
    ! [A_135,B_136] :
      ( k3_xboole_0(k1_tarski(A_135),B_136) = k1_tarski(A_135)
      | ~ r2_hidden(A_135,B_136) ) ),
    inference(resolution,[status(thm)],[c_44,c_170])).

tff(c_1183,plain,(
    ! [A_135,B_136] :
      ( k5_xboole_0(k1_tarski(A_135),k1_tarski(A_135)) = k4_xboole_0(k1_tarski(A_135),B_136)
      | ~ r2_hidden(A_135,B_136) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1161,c_22])).

tff(c_1291,plain,(
    ! [A_142,B_143] :
      ( k4_xboole_0(k1_tarski(A_142),B_143) = k1_xboole_0
      | ~ r2_hidden(A_142,B_143) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_576,c_1183])).

tff(c_28,plain,(
    ! [A_22,B_23] : k2_xboole_0(A_22,k4_xboole_0(B_23,A_22)) = k2_xboole_0(A_22,B_23) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_1316,plain,(
    ! [B_143,A_142] :
      ( k2_xboole_0(B_143,k1_tarski(A_142)) = k2_xboole_0(B_143,k1_xboole_0)
      | ~ r2_hidden(A_142,B_143) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1291,c_28])).

tff(c_1449,plain,(
    ! [B_146,A_147] :
      ( k2_xboole_0(B_146,k1_tarski(A_147)) = B_146
      | ~ r2_hidden(A_147,B_146) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_1316])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_48,plain,(
    k2_xboole_0(k1_tarski('#skF_3'),'#skF_4') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_52,plain,(
    k2_xboole_0('#skF_4',k1_tarski('#skF_3')) != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_48])).

tff(c_1494,plain,(
    ~ r2_hidden('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1449,c_52])).

tff(c_1532,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_1494])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 09:45:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.02/1.50  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.02/1.51  
% 3.02/1.51  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.02/1.51  %$ r2_hidden > r1_xboole_0 > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 3.02/1.51  
% 3.02/1.51  %Foreground sorts:
% 3.02/1.51  
% 3.02/1.51  
% 3.02/1.51  %Background operators:
% 3.02/1.51  
% 3.02/1.51  
% 3.02/1.51  %Foreground operators:
% 3.02/1.51  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.02/1.51  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.02/1.51  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.02/1.51  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.02/1.51  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.02/1.51  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.02/1.51  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.02/1.51  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.02/1.51  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.02/1.51  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.02/1.51  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.02/1.51  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.02/1.51  tff('#skF_3', type, '#skF_3': $i).
% 3.02/1.51  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.02/1.51  tff(k3_tarski, type, k3_tarski: $i > $i).
% 3.02/1.51  tff('#skF_4', type, '#skF_4': $i).
% 3.02/1.51  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.02/1.51  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.02/1.51  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.02/1.51  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.02/1.51  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.02/1.51  
% 3.02/1.52  tff(f_91, negated_conjecture, ~(![A, B]: (r2_hidden(A, B) => (k2_xboole_0(k1_tarski(A), B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_zfmisc_1)).
% 3.02/1.52  tff(f_62, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 3.02/1.52  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 3.02/1.52  tff(f_68, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_xboole_1)).
% 3.02/1.52  tff(f_34, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 3.02/1.52  tff(f_72, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 3.02/1.52  tff(f_38, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 3.02/1.52  tff(f_58, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.02/1.52  tff(f_66, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 3.02/1.52  tff(f_52, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 3.02/1.52  tff(f_60, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 3.02/1.52  tff(f_70, axiom, (![A, B]: (k4_xboole_0(k2_xboole_0(A, B), B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t40_xboole_1)).
% 3.02/1.52  tff(f_84, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 3.02/1.52  tff(c_50, plain, (r2_hidden('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_91])).
% 3.02/1.52  tff(c_24, plain, (![A_19]: (k2_xboole_0(A_19, k1_xboole_0)=A_19)), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.02/1.52  tff(c_73, plain, (![B_45, A_46]: (k2_xboole_0(B_45, A_46)=k2_xboole_0(A_46, B_45))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.02/1.52  tff(c_89, plain, (![A_46]: (k2_xboole_0(k1_xboole_0, A_46)=A_46)), inference(superposition, [status(thm), theory('equality')], [c_73, c_24])).
% 3.02/1.52  tff(c_444, plain, (![A_88, B_89]: (k2_xboole_0(A_88, k4_xboole_0(B_89, A_88))=k2_xboole_0(A_88, B_89))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.02/1.52  tff(c_454, plain, (![B_89]: (k4_xboole_0(B_89, k1_xboole_0)=k2_xboole_0(k1_xboole_0, B_89))), inference(superposition, [status(thm), theory('equality')], [c_444, c_89])).
% 3.02/1.52  tff(c_489, plain, (![B_90]: (k4_xboole_0(B_90, k1_xboole_0)=B_90)), inference(demodulation, [status(thm), theory('equality')], [c_89, c_454])).
% 3.02/1.52  tff(c_8, plain, (![A_3, B_4]: (r2_hidden('#skF_1'(A_3, B_4), A_3) | r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.02/1.52  tff(c_32, plain, (![A_26]: (r1_xboole_0(A_26, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.02/1.52  tff(c_158, plain, (![B_48, A_49]: (r1_xboole_0(B_48, A_49) | ~r1_xboole_0(A_49, B_48))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.02/1.52  tff(c_161, plain, (![A_26]: (r1_xboole_0(k1_xboole_0, A_26))), inference(resolution, [status(thm)], [c_32, c_158])).
% 3.02/1.52  tff(c_20, plain, (![B_16]: (r1_tarski(B_16, B_16))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.02/1.52  tff(c_170, plain, (![A_53, B_54]: (k3_xboole_0(A_53, B_54)=A_53 | ~r1_tarski(A_53, B_54))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.02/1.52  tff(c_178, plain, (![B_16]: (k3_xboole_0(B_16, B_16)=B_16)), inference(resolution, [status(thm)], [c_20, c_170])).
% 3.02/1.52  tff(c_264, plain, (![A_71, B_72, C_73]: (~r1_xboole_0(A_71, B_72) | ~r2_hidden(C_73, k3_xboole_0(A_71, B_72)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.02/1.52  tff(c_273, plain, (![B_74, C_75]: (~r1_xboole_0(B_74, B_74) | ~r2_hidden(C_75, B_74))), inference(superposition, [status(thm), theory('equality')], [c_178, c_264])).
% 3.02/1.52  tff(c_282, plain, (![C_76]: (~r2_hidden(C_76, k1_xboole_0))), inference(resolution, [status(thm)], [c_161, c_273])).
% 3.02/1.52  tff(c_298, plain, (![B_79]: (r1_tarski(k1_xboole_0, B_79))), inference(resolution, [status(thm)], [c_8, c_282])).
% 3.02/1.52  tff(c_26, plain, (![A_20, B_21]: (k3_xboole_0(A_20, B_21)=A_20 | ~r1_tarski(A_20, B_21))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.02/1.52  tff(c_306, plain, (![B_80]: (k3_xboole_0(k1_xboole_0, B_80)=k1_xboole_0)), inference(resolution, [status(thm)], [c_298, c_26])).
% 3.02/1.52  tff(c_22, plain, (![A_17, B_18]: (k5_xboole_0(A_17, k3_xboole_0(A_17, B_18))=k4_xboole_0(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.02/1.52  tff(c_349, plain, (![B_82]: (k5_xboole_0(k1_xboole_0, k1_xboole_0)=k4_xboole_0(k1_xboole_0, B_82))), inference(superposition, [status(thm), theory('equality')], [c_306, c_22])).
% 3.02/1.52  tff(c_314, plain, (![B_80]: (k5_xboole_0(k1_xboole_0, k1_xboole_0)=k4_xboole_0(k1_xboole_0, B_80))), inference(superposition, [status(thm), theory('equality')], [c_306, c_22])).
% 3.02/1.52  tff(c_352, plain, (![B_82, B_80]: (k4_xboole_0(k1_xboole_0, B_82)=k4_xboole_0(k1_xboole_0, B_80))), inference(superposition, [status(thm), theory('equality')], [c_349, c_314])).
% 3.02/1.52  tff(c_503, plain, (![B_80]: (k4_xboole_0(k1_xboole_0, B_80)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_489, c_352])).
% 3.02/1.52  tff(c_389, plain, (![A_85, B_86]: (k4_xboole_0(k2_xboole_0(A_85, B_86), B_86)=k4_xboole_0(A_85, B_86))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.02/1.52  tff(c_401, plain, (![A_46]: (k4_xboole_0(k1_xboole_0, A_46)=k4_xboole_0(A_46, A_46))), inference(superposition, [status(thm), theory('equality')], [c_89, c_389])).
% 3.02/1.52  tff(c_529, plain, (![A_46]: (k4_xboole_0(A_46, A_46)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_503, c_401])).
% 3.02/1.52  tff(c_236, plain, (![A_66, B_67]: (k5_xboole_0(A_66, k3_xboole_0(A_66, B_67))=k4_xboole_0(A_66, B_67))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.02/1.52  tff(c_245, plain, (![B_16]: (k5_xboole_0(B_16, B_16)=k4_xboole_0(B_16, B_16))), inference(superposition, [status(thm), theory('equality')], [c_178, c_236])).
% 3.02/1.52  tff(c_576, plain, (![B_16]: (k5_xboole_0(B_16, B_16)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_529, c_245])).
% 3.02/1.52  tff(c_44, plain, (![A_37, B_38]: (r1_tarski(k1_tarski(A_37), B_38) | ~r2_hidden(A_37, B_38))), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.02/1.52  tff(c_1161, plain, (![A_135, B_136]: (k3_xboole_0(k1_tarski(A_135), B_136)=k1_tarski(A_135) | ~r2_hidden(A_135, B_136))), inference(resolution, [status(thm)], [c_44, c_170])).
% 3.02/1.52  tff(c_1183, plain, (![A_135, B_136]: (k5_xboole_0(k1_tarski(A_135), k1_tarski(A_135))=k4_xboole_0(k1_tarski(A_135), B_136) | ~r2_hidden(A_135, B_136))), inference(superposition, [status(thm), theory('equality')], [c_1161, c_22])).
% 3.02/1.52  tff(c_1291, plain, (![A_142, B_143]: (k4_xboole_0(k1_tarski(A_142), B_143)=k1_xboole_0 | ~r2_hidden(A_142, B_143))), inference(demodulation, [status(thm), theory('equality')], [c_576, c_1183])).
% 3.02/1.52  tff(c_28, plain, (![A_22, B_23]: (k2_xboole_0(A_22, k4_xboole_0(B_23, A_22))=k2_xboole_0(A_22, B_23))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.02/1.52  tff(c_1316, plain, (![B_143, A_142]: (k2_xboole_0(B_143, k1_tarski(A_142))=k2_xboole_0(B_143, k1_xboole_0) | ~r2_hidden(A_142, B_143))), inference(superposition, [status(thm), theory('equality')], [c_1291, c_28])).
% 3.02/1.52  tff(c_1449, plain, (![B_146, A_147]: (k2_xboole_0(B_146, k1_tarski(A_147))=B_146 | ~r2_hidden(A_147, B_146))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_1316])).
% 3.02/1.52  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.02/1.52  tff(c_48, plain, (k2_xboole_0(k1_tarski('#skF_3'), '#skF_4')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_91])).
% 3.02/1.52  tff(c_52, plain, (k2_xboole_0('#skF_4', k1_tarski('#skF_3'))!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_2, c_48])).
% 3.02/1.52  tff(c_1494, plain, (~r2_hidden('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1449, c_52])).
% 3.02/1.52  tff(c_1532, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_50, c_1494])).
% 3.02/1.52  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.02/1.52  
% 3.02/1.52  Inference rules
% 3.02/1.52  ----------------------
% 3.02/1.52  #Ref     : 0
% 3.02/1.52  #Sup     : 351
% 3.02/1.52  #Fact    : 0
% 3.02/1.52  #Define  : 0
% 3.02/1.52  #Split   : 0
% 3.02/1.52  #Chain   : 0
% 3.02/1.52  #Close   : 0
% 3.02/1.52  
% 3.02/1.52  Ordering : KBO
% 3.02/1.52  
% 3.02/1.52  Simplification rules
% 3.02/1.52  ----------------------
% 3.02/1.52  #Subsume      : 41
% 3.02/1.52  #Demod        : 249
% 3.02/1.52  #Tautology    : 244
% 3.02/1.52  #SimpNegUnit  : 2
% 3.02/1.52  #BackRed      : 4
% 3.02/1.52  
% 3.02/1.52  #Partial instantiations: 0
% 3.02/1.52  #Strategies tried      : 1
% 3.02/1.52  
% 3.02/1.52  Timing (in seconds)
% 3.02/1.52  ----------------------
% 3.02/1.53  Preprocessing        : 0.33
% 3.02/1.53  Parsing              : 0.17
% 3.02/1.53  CNF conversion       : 0.02
% 3.02/1.53  Main loop            : 0.41
% 3.02/1.53  Inferencing          : 0.15
% 3.02/1.53  Reduction            : 0.16
% 3.02/1.53  Demodulation         : 0.12
% 3.02/1.53  BG Simplification    : 0.02
% 3.02/1.53  Subsumption          : 0.06
% 3.02/1.53  Abstraction          : 0.02
% 3.02/1.53  MUC search           : 0.00
% 3.02/1.53  Cooper               : 0.00
% 3.02/1.53  Total                : 0.77
% 3.02/1.53  Index Insertion      : 0.00
% 3.02/1.53  Index Deletion       : 0.00
% 3.02/1.53  Index Matching       : 0.00
% 3.02/1.53  BG Taut test         : 0.00
%------------------------------------------------------------------------------
