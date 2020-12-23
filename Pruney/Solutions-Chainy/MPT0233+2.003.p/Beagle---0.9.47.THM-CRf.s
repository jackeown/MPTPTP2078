%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:49:24 EST 2020

% Result     : Theorem 4.06s
% Output     : CNFRefutation 4.43s
% Verified   : 
% Statistics : Number of formulae       :   87 ( 130 expanded)
%              Number of leaves         :   43 (  62 expanded)
%              Depth                    :   12
%              Number of atoms          :   91 ( 160 expanded)
%              Number of equality atoms :   53 (  84 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_4 > #skF_7 > #skF_5 > #skF_6 > #skF_8 > #skF_3 > #skF_1

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

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

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

tff(f_132,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ~ ( r1_tarski(k2_tarski(A,B),k2_tarski(C,D))
          & A != C
          & A != D ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_zfmisc_1)).

tff(f_79,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

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

tff(f_77,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

tff(f_61,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_75,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_122,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
    <=> A != B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_zfmisc_1)).

tff(f_117,axiom,(
    ! [A,B] : k3_xboole_0(k1_tarski(A),k2_tarski(A,B)) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_zfmisc_1)).

tff(f_29,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_63,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_69,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_73,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_94,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_115,axiom,(
    ! [A,B,C] :
      ( k4_xboole_0(k2_tarski(A,B),C) = k1_tarski(A)
    <=> ( ~ r2_hidden(A,C)
        & ( r2_hidden(B,C)
          | A = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l38_zfmisc_1)).

tff(f_90,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

tff(c_86,plain,(
    '#skF_7' != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_84,plain,(
    '#skF_5' != '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_32,plain,(
    ! [A_28] : r1_xboole_0(A_28,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_12,plain,(
    ! [A_12] :
      ( r2_hidden('#skF_2'(A_12),A_12)
      | k1_xboole_0 = A_12 ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_266,plain,(
    ! [A_102,B_103,C_104] :
      ( ~ r1_xboole_0(A_102,B_103)
      | ~ r2_hidden(C_104,k3_xboole_0(A_102,B_103)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_308,plain,(
    ! [A_110,B_111] :
      ( ~ r1_xboole_0(A_110,B_111)
      | k3_xboole_0(A_110,B_111) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_12,c_266])).

tff(c_312,plain,(
    ! [A_28] : k3_xboole_0(A_28,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_32,c_308])).

tff(c_30,plain,(
    ! [A_27] : k5_xboole_0(A_27,k1_xboole_0) = A_27 ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_512,plain,(
    ! [A_122,B_123] : k5_xboole_0(A_122,k3_xboole_0(A_122,B_123)) = k4_xboole_0(A_122,B_123) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_530,plain,(
    ! [A_28] : k5_xboole_0(A_28,k1_xboole_0) = k4_xboole_0(A_28,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_312,c_512])).

tff(c_544,plain,(
    ! [A_124] : k4_xboole_0(A_124,k1_xboole_0) = A_124 ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_530])).

tff(c_28,plain,(
    ! [A_25,B_26] : k4_xboole_0(A_25,k4_xboole_0(A_25,B_26)) = k3_xboole_0(A_25,B_26) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_553,plain,(
    ! [A_124] : k4_xboole_0(A_124,A_124) = k3_xboole_0(A_124,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_544,c_28])).

tff(c_558,plain,(
    ! [A_124] : k4_xboole_0(A_124,A_124) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_312,c_553])).

tff(c_80,plain,(
    ! [B_75] : k4_xboole_0(k1_tarski(B_75),k1_tarski(B_75)) != k1_tarski(B_75) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_595,plain,(
    ! [B_75] : k1_tarski(B_75) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_558,c_80])).

tff(c_475,plain,(
    ! [A_118,B_119] : k3_xboole_0(k1_tarski(A_118),k2_tarski(A_118,B_119)) = k1_tarski(A_118) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_136,plain,(
    ! [B_89,A_90] : k3_xboole_0(B_89,A_90) = k3_xboole_0(A_90,B_89) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_22,plain,(
    ! [A_18,B_19] : r1_tarski(k3_xboole_0(A_18,B_19),A_18) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_151,plain,(
    ! [B_89,A_90] : r1_tarski(k3_xboole_0(B_89,A_90),A_90) ),
    inference(superposition,[status(thm),theory(equality)],[c_136,c_22])).

tff(c_484,plain,(
    ! [A_118,B_119] : r1_tarski(k1_tarski(A_118),k2_tarski(A_118,B_119)) ),
    inference(superposition,[status(thm),theory(equality)],[c_475,c_151])).

tff(c_88,plain,(
    r1_tarski(k2_tarski('#skF_5','#skF_6'),k2_tarski('#skF_7','#skF_8')) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_1013,plain,(
    ! [A_147,C_148,B_149] :
      ( r1_tarski(A_147,C_148)
      | ~ r1_tarski(B_149,C_148)
      | ~ r1_tarski(A_147,B_149) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_1157,plain,(
    ! [A_156] :
      ( r1_tarski(A_156,k2_tarski('#skF_7','#skF_8'))
      | ~ r1_tarski(A_156,k2_tarski('#skF_5','#skF_6')) ) ),
    inference(resolution,[status(thm)],[c_88,c_1013])).

tff(c_26,plain,(
    ! [A_23,B_24] :
      ( k3_xboole_0(A_23,B_24) = A_23
      | ~ r1_tarski(A_23,B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_2804,plain,(
    ! [A_214] :
      ( k3_xboole_0(A_214,k2_tarski('#skF_7','#skF_8')) = A_214
      | ~ r1_tarski(A_214,k2_tarski('#skF_5','#skF_6')) ) ),
    inference(resolution,[status(thm)],[c_1157,c_26])).

tff(c_2845,plain,(
    k3_xboole_0(k1_tarski('#skF_5'),k2_tarski('#skF_7','#skF_8')) = k1_tarski('#skF_5') ),
    inference(resolution,[status(thm)],[c_484,c_2804])).

tff(c_20,plain,(
    ! [A_16,B_17] : k5_xboole_0(A_16,k3_xboole_0(A_16,B_17)) = k4_xboole_0(A_16,B_17) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_231,plain,(
    ! [A_97,B_98] :
      ( k3_xboole_0(A_97,B_98) = A_97
      | ~ r1_tarski(A_97,B_98) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_924,plain,(
    ! [A_145,B_146] : k3_xboole_0(k3_xboole_0(A_145,B_146),A_145) = k3_xboole_0(A_145,B_146) ),
    inference(resolution,[status(thm)],[c_22,c_231])).

tff(c_4,plain,(
    ! [B_4,A_3] : k3_xboole_0(B_4,A_3) = k3_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_536,plain,(
    ! [B_4,A_3] : k5_xboole_0(B_4,k3_xboole_0(A_3,B_4)) = k4_xboole_0(B_4,A_3) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_512])).

tff(c_936,plain,(
    ! [A_145,B_146] : k5_xboole_0(A_145,k3_xboole_0(A_145,B_146)) = k4_xboole_0(A_145,k3_xboole_0(A_145,B_146)) ),
    inference(superposition,[status(thm),theory(equality)],[c_924,c_536])).

tff(c_1000,plain,(
    ! [A_145,B_146] : k4_xboole_0(A_145,k3_xboole_0(A_145,B_146)) = k4_xboole_0(A_145,B_146) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_936])).

tff(c_3539,plain,(
    k4_xboole_0(k1_tarski('#skF_5'),k2_tarski('#skF_7','#skF_8')) = k4_xboole_0(k1_tarski('#skF_5'),k1_tarski('#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_2845,c_1000])).

tff(c_3612,plain,(
    k4_xboole_0(k1_tarski('#skF_5'),k2_tarski('#skF_7','#skF_8')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_558,c_3539])).

tff(c_56,plain,(
    ! [A_41] : k2_tarski(A_41,A_41) = k1_tarski(A_41) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_74,plain,(
    ! [B_70,C_71] :
      ( k4_xboole_0(k2_tarski(B_70,B_70),C_71) = k1_tarski(B_70)
      | r2_hidden(B_70,C_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_89,plain,(
    ! [B_70,C_71] :
      ( k4_xboole_0(k1_tarski(B_70),C_71) = k1_tarski(B_70)
      | r2_hidden(B_70,C_71) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_74])).

tff(c_3629,plain,
    ( k1_tarski('#skF_5') = k1_xboole_0
    | r2_hidden('#skF_5',k2_tarski('#skF_7','#skF_8')) ),
    inference(superposition,[status(thm),theory(equality)],[c_3612,c_89])).

tff(c_3641,plain,(
    r2_hidden('#skF_5',k2_tarski('#skF_7','#skF_8')) ),
    inference(negUnitSimplification,[status(thm)],[c_595,c_3629])).

tff(c_36,plain,(
    ! [D_36,B_32,A_31] :
      ( D_36 = B_32
      | D_36 = A_31
      | ~ r2_hidden(D_36,k2_tarski(A_31,B_32)) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_3648,plain,
    ( '#skF_5' = '#skF_8'
    | '#skF_7' = '#skF_5' ),
    inference(resolution,[status(thm)],[c_3641,c_36])).

tff(c_3652,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_84,c_3648])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.34  % Computer   : n004.cluster.edu
% 0.15/0.34  % Model      : x86_64 x86_64
% 0.15/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.34  % Memory     : 8042.1875MB
% 0.15/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.34  % CPULimit   : 60
% 0.15/0.34  % DateTime   : Tue Dec  1 19:41:53 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.06/1.77  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.06/1.78  
% 4.06/1.78  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.06/1.78  %$ r2_hidden > r1_xboole_0 > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_4 > #skF_7 > #skF_5 > #skF_6 > #skF_8 > #skF_3 > #skF_1
% 4.06/1.78  
% 4.06/1.78  %Foreground sorts:
% 4.06/1.78  
% 4.06/1.78  
% 4.06/1.78  %Background operators:
% 4.06/1.78  
% 4.06/1.78  
% 4.06/1.78  %Foreground operators:
% 4.06/1.78  tff('#skF_2', type, '#skF_2': $i > $i).
% 4.06/1.78  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.06/1.78  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.06/1.78  tff(k1_tarski, type, k1_tarski: $i > $i).
% 4.06/1.78  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.06/1.78  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.06/1.78  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 4.06/1.78  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 4.06/1.78  tff('#skF_7', type, '#skF_7': $i).
% 4.06/1.78  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 4.06/1.78  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.06/1.78  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 4.06/1.78  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.06/1.78  tff('#skF_5', type, '#skF_5': $i).
% 4.06/1.78  tff('#skF_6', type, '#skF_6': $i).
% 4.06/1.78  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 4.06/1.78  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 4.06/1.78  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 4.06/1.78  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 4.06/1.78  tff('#skF_8', type, '#skF_8': $i).
% 4.06/1.78  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.06/1.78  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 4.06/1.78  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.06/1.78  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.06/1.78  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.06/1.78  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 4.06/1.78  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 4.06/1.78  
% 4.43/1.79  tff(f_132, negated_conjecture, ~(![A, B, C, D]: ~((r1_tarski(k2_tarski(A, B), k2_tarski(C, D)) & ~(A = C)) & ~(A = D))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_zfmisc_1)).
% 4.43/1.79  tff(f_79, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 4.43/1.79  tff(f_53, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 4.43/1.79  tff(f_45, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 4.43/1.79  tff(f_77, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 4.43/1.79  tff(f_61, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 4.43/1.79  tff(f_75, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 4.43/1.79  tff(f_122, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) <=> ~(A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_zfmisc_1)).
% 4.43/1.79  tff(f_117, axiom, (![A, B]: (k3_xboole_0(k1_tarski(A), k2_tarski(A, B)) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t19_zfmisc_1)).
% 4.43/1.79  tff(f_29, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 4.43/1.79  tff(f_63, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 4.43/1.79  tff(f_69, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 4.43/1.79  tff(f_73, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 4.43/1.79  tff(f_94, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 4.43/1.79  tff(f_115, axiom, (![A, B, C]: ((k4_xboole_0(k2_tarski(A, B), C) = k1_tarski(A)) <=> (~r2_hidden(A, C) & (r2_hidden(B, C) | (A = B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l38_zfmisc_1)).
% 4.43/1.79  tff(f_90, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_tarski)).
% 4.43/1.79  tff(c_86, plain, ('#skF_7'!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_132])).
% 4.43/1.79  tff(c_84, plain, ('#skF_5'!='#skF_8'), inference(cnfTransformation, [status(thm)], [f_132])).
% 4.43/1.79  tff(c_32, plain, (![A_28]: (r1_xboole_0(A_28, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_79])).
% 4.43/1.79  tff(c_12, plain, (![A_12]: (r2_hidden('#skF_2'(A_12), A_12) | k1_xboole_0=A_12)), inference(cnfTransformation, [status(thm)], [f_53])).
% 4.43/1.79  tff(c_266, plain, (![A_102, B_103, C_104]: (~r1_xboole_0(A_102, B_103) | ~r2_hidden(C_104, k3_xboole_0(A_102, B_103)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 4.43/1.79  tff(c_308, plain, (![A_110, B_111]: (~r1_xboole_0(A_110, B_111) | k3_xboole_0(A_110, B_111)=k1_xboole_0)), inference(resolution, [status(thm)], [c_12, c_266])).
% 4.43/1.79  tff(c_312, plain, (![A_28]: (k3_xboole_0(A_28, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_32, c_308])).
% 4.43/1.79  tff(c_30, plain, (![A_27]: (k5_xboole_0(A_27, k1_xboole_0)=A_27)), inference(cnfTransformation, [status(thm)], [f_77])).
% 4.43/1.79  tff(c_512, plain, (![A_122, B_123]: (k5_xboole_0(A_122, k3_xboole_0(A_122, B_123))=k4_xboole_0(A_122, B_123))), inference(cnfTransformation, [status(thm)], [f_61])).
% 4.43/1.79  tff(c_530, plain, (![A_28]: (k5_xboole_0(A_28, k1_xboole_0)=k4_xboole_0(A_28, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_312, c_512])).
% 4.43/1.79  tff(c_544, plain, (![A_124]: (k4_xboole_0(A_124, k1_xboole_0)=A_124)), inference(demodulation, [status(thm), theory('equality')], [c_30, c_530])).
% 4.43/1.79  tff(c_28, plain, (![A_25, B_26]: (k4_xboole_0(A_25, k4_xboole_0(A_25, B_26))=k3_xboole_0(A_25, B_26))), inference(cnfTransformation, [status(thm)], [f_75])).
% 4.43/1.79  tff(c_553, plain, (![A_124]: (k4_xboole_0(A_124, A_124)=k3_xboole_0(A_124, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_544, c_28])).
% 4.43/1.79  tff(c_558, plain, (![A_124]: (k4_xboole_0(A_124, A_124)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_312, c_553])).
% 4.43/1.79  tff(c_80, plain, (![B_75]: (k4_xboole_0(k1_tarski(B_75), k1_tarski(B_75))!=k1_tarski(B_75))), inference(cnfTransformation, [status(thm)], [f_122])).
% 4.43/1.79  tff(c_595, plain, (![B_75]: (k1_tarski(B_75)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_558, c_80])).
% 4.43/1.79  tff(c_475, plain, (![A_118, B_119]: (k3_xboole_0(k1_tarski(A_118), k2_tarski(A_118, B_119))=k1_tarski(A_118))), inference(cnfTransformation, [status(thm)], [f_117])).
% 4.43/1.79  tff(c_136, plain, (![B_89, A_90]: (k3_xboole_0(B_89, A_90)=k3_xboole_0(A_90, B_89))), inference(cnfTransformation, [status(thm)], [f_29])).
% 4.43/1.79  tff(c_22, plain, (![A_18, B_19]: (r1_tarski(k3_xboole_0(A_18, B_19), A_18))), inference(cnfTransformation, [status(thm)], [f_63])).
% 4.43/1.79  tff(c_151, plain, (![B_89, A_90]: (r1_tarski(k3_xboole_0(B_89, A_90), A_90))), inference(superposition, [status(thm), theory('equality')], [c_136, c_22])).
% 4.43/1.79  tff(c_484, plain, (![A_118, B_119]: (r1_tarski(k1_tarski(A_118), k2_tarski(A_118, B_119)))), inference(superposition, [status(thm), theory('equality')], [c_475, c_151])).
% 4.43/1.79  tff(c_88, plain, (r1_tarski(k2_tarski('#skF_5', '#skF_6'), k2_tarski('#skF_7', '#skF_8'))), inference(cnfTransformation, [status(thm)], [f_132])).
% 4.43/1.79  tff(c_1013, plain, (![A_147, C_148, B_149]: (r1_tarski(A_147, C_148) | ~r1_tarski(B_149, C_148) | ~r1_tarski(A_147, B_149))), inference(cnfTransformation, [status(thm)], [f_69])).
% 4.43/1.79  tff(c_1157, plain, (![A_156]: (r1_tarski(A_156, k2_tarski('#skF_7', '#skF_8')) | ~r1_tarski(A_156, k2_tarski('#skF_5', '#skF_6')))), inference(resolution, [status(thm)], [c_88, c_1013])).
% 4.43/1.79  tff(c_26, plain, (![A_23, B_24]: (k3_xboole_0(A_23, B_24)=A_23 | ~r1_tarski(A_23, B_24))), inference(cnfTransformation, [status(thm)], [f_73])).
% 4.43/1.79  tff(c_2804, plain, (![A_214]: (k3_xboole_0(A_214, k2_tarski('#skF_7', '#skF_8'))=A_214 | ~r1_tarski(A_214, k2_tarski('#skF_5', '#skF_6')))), inference(resolution, [status(thm)], [c_1157, c_26])).
% 4.43/1.79  tff(c_2845, plain, (k3_xboole_0(k1_tarski('#skF_5'), k2_tarski('#skF_7', '#skF_8'))=k1_tarski('#skF_5')), inference(resolution, [status(thm)], [c_484, c_2804])).
% 4.43/1.79  tff(c_20, plain, (![A_16, B_17]: (k5_xboole_0(A_16, k3_xboole_0(A_16, B_17))=k4_xboole_0(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_61])).
% 4.43/1.79  tff(c_231, plain, (![A_97, B_98]: (k3_xboole_0(A_97, B_98)=A_97 | ~r1_tarski(A_97, B_98))), inference(cnfTransformation, [status(thm)], [f_73])).
% 4.43/1.79  tff(c_924, plain, (![A_145, B_146]: (k3_xboole_0(k3_xboole_0(A_145, B_146), A_145)=k3_xboole_0(A_145, B_146))), inference(resolution, [status(thm)], [c_22, c_231])).
% 4.43/1.79  tff(c_4, plain, (![B_4, A_3]: (k3_xboole_0(B_4, A_3)=k3_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 4.43/1.79  tff(c_536, plain, (![B_4, A_3]: (k5_xboole_0(B_4, k3_xboole_0(A_3, B_4))=k4_xboole_0(B_4, A_3))), inference(superposition, [status(thm), theory('equality')], [c_4, c_512])).
% 4.43/1.79  tff(c_936, plain, (![A_145, B_146]: (k5_xboole_0(A_145, k3_xboole_0(A_145, B_146))=k4_xboole_0(A_145, k3_xboole_0(A_145, B_146)))), inference(superposition, [status(thm), theory('equality')], [c_924, c_536])).
% 4.43/1.79  tff(c_1000, plain, (![A_145, B_146]: (k4_xboole_0(A_145, k3_xboole_0(A_145, B_146))=k4_xboole_0(A_145, B_146))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_936])).
% 4.43/1.79  tff(c_3539, plain, (k4_xboole_0(k1_tarski('#skF_5'), k2_tarski('#skF_7', '#skF_8'))=k4_xboole_0(k1_tarski('#skF_5'), k1_tarski('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_2845, c_1000])).
% 4.43/1.79  tff(c_3612, plain, (k4_xboole_0(k1_tarski('#skF_5'), k2_tarski('#skF_7', '#skF_8'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_558, c_3539])).
% 4.43/1.79  tff(c_56, plain, (![A_41]: (k2_tarski(A_41, A_41)=k1_tarski(A_41))), inference(cnfTransformation, [status(thm)], [f_94])).
% 4.43/1.79  tff(c_74, plain, (![B_70, C_71]: (k4_xboole_0(k2_tarski(B_70, B_70), C_71)=k1_tarski(B_70) | r2_hidden(B_70, C_71))), inference(cnfTransformation, [status(thm)], [f_115])).
% 4.43/1.79  tff(c_89, plain, (![B_70, C_71]: (k4_xboole_0(k1_tarski(B_70), C_71)=k1_tarski(B_70) | r2_hidden(B_70, C_71))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_74])).
% 4.43/1.79  tff(c_3629, plain, (k1_tarski('#skF_5')=k1_xboole_0 | r2_hidden('#skF_5', k2_tarski('#skF_7', '#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_3612, c_89])).
% 4.43/1.79  tff(c_3641, plain, (r2_hidden('#skF_5', k2_tarski('#skF_7', '#skF_8'))), inference(negUnitSimplification, [status(thm)], [c_595, c_3629])).
% 4.43/1.79  tff(c_36, plain, (![D_36, B_32, A_31]: (D_36=B_32 | D_36=A_31 | ~r2_hidden(D_36, k2_tarski(A_31, B_32)))), inference(cnfTransformation, [status(thm)], [f_90])).
% 4.43/1.79  tff(c_3648, plain, ('#skF_5'='#skF_8' | '#skF_7'='#skF_5'), inference(resolution, [status(thm)], [c_3641, c_36])).
% 4.43/1.79  tff(c_3652, plain, $false, inference(negUnitSimplification, [status(thm)], [c_86, c_84, c_3648])).
% 4.43/1.79  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.43/1.79  
% 4.43/1.79  Inference rules
% 4.43/1.79  ----------------------
% 4.43/1.79  #Ref     : 0
% 4.43/1.79  #Sup     : 864
% 4.43/1.79  #Fact    : 0
% 4.43/1.79  #Define  : 0
% 4.43/1.79  #Split   : 3
% 4.43/1.79  #Chain   : 0
% 4.43/1.79  #Close   : 0
% 4.43/1.79  
% 4.43/1.79  Ordering : KBO
% 4.43/1.79  
% 4.43/1.79  Simplification rules
% 4.43/1.79  ----------------------
% 4.43/1.79  #Subsume      : 44
% 4.43/1.79  #Demod        : 656
% 4.43/1.79  #Tautology    : 576
% 4.43/1.79  #SimpNegUnit  : 17
% 4.43/1.79  #BackRed      : 1
% 4.43/1.79  
% 4.43/1.79  #Partial instantiations: 0
% 4.43/1.79  #Strategies tried      : 1
% 4.43/1.79  
% 4.43/1.79  Timing (in seconds)
% 4.43/1.79  ----------------------
% 4.43/1.80  Preprocessing        : 0.36
% 4.43/1.80  Parsing              : 0.18
% 4.43/1.80  CNF conversion       : 0.03
% 4.43/1.80  Main loop            : 0.66
% 4.43/1.80  Inferencing          : 0.20
% 4.43/1.80  Reduction            : 0.29
% 4.43/1.80  Demodulation         : 0.23
% 4.43/1.80  BG Simplification    : 0.03
% 4.43/1.80  Subsumption          : 0.10
% 4.43/1.80  Abstraction          : 0.03
% 4.43/1.80  MUC search           : 0.00
% 4.43/1.80  Cooper               : 0.00
% 4.43/1.80  Total                : 1.05
% 4.43/1.80  Index Insertion      : 0.00
% 4.43/1.80  Index Deletion       : 0.00
% 4.43/1.80  Index Matching       : 0.00
% 4.43/1.80  BG Taut test         : 0.00
%------------------------------------------------------------------------------
