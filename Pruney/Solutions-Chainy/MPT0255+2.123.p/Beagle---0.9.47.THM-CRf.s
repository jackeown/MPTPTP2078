%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:51:54 EST 2020

% Result     : Theorem 2.89s
% Output     : CNFRefutation 3.13s
% Verified   : 
% Statistics : Number of formulae       :   73 ( 104 expanded)
%              Number of leaves         :   37 (  51 expanded)
%              Depth                    :   10
%              Number of atoms          :   67 ( 132 expanded)
%              Number of equality atoms :   32 (  42 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2

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

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

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

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(f_32,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_50,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & r2_hidden(C,B) ) )
      & ~ ( ? [C] :
              ( r2_hidden(C,A)
              & r2_hidden(C,B) )
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_62,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_85,negated_conjecture,(
    ~ ! [A,B,C] : k2_xboole_0(k2_tarski(A,B),C) != k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_zfmisc_1)).

tff(f_58,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_54,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_68,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_70,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_66,axiom,(
    ! [A,B,C] : k2_xboole_0(k2_tarski(B,A),k2_tarski(C,A)) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t137_enumset1)).

tff(f_81,axiom,(
    ! [A,B] : k2_xboole_0(k1_tarski(A),B) != k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_zfmisc_1)).

tff(f_64,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_56,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(c_6,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_193,plain,(
    ! [A_74,B_75] :
      ( r2_hidden('#skF_2'(A_74,B_75),B_75)
      | r1_xboole_0(A_74,B_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_198,plain,(
    ! [B_76,A_77] :
      ( ~ v1_xboole_0(B_76)
      | r1_xboole_0(A_77,B_76) ) ),
    inference(resolution,[status(thm)],[c_193,c_2])).

tff(c_22,plain,(
    ! [A_16,B_17] :
      ( k4_xboole_0(A_16,B_17) = A_16
      | ~ r1_xboole_0(A_16,B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_251,plain,(
    ! [A_83,B_84] :
      ( k4_xboole_0(A_83,B_84) = A_83
      | ~ v1_xboole_0(B_84) ) ),
    inference(resolution,[status(thm)],[c_198,c_22])).

tff(c_255,plain,(
    ! [A_85] : k4_xboole_0(A_85,k1_xboole_0) = A_85 ),
    inference(resolution,[status(thm)],[c_6,c_251])).

tff(c_44,plain,(
    k2_xboole_0(k2_tarski('#skF_3','#skF_4'),'#skF_5') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_20,plain,(
    ! [A_14,B_15] : r1_tarski(A_14,k2_xboole_0(A_14,B_15)) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_60,plain,(
    r1_tarski(k2_tarski('#skF_3','#skF_4'),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_20])).

tff(c_79,plain,(
    ! [A_54,B_55] :
      ( k4_xboole_0(A_54,B_55) = k1_xboole_0
      | ~ r1_tarski(A_54,B_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_90,plain,(
    k4_xboole_0(k2_tarski('#skF_3','#skF_4'),k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_60,c_79])).

tff(c_268,plain,(
    k2_tarski('#skF_3','#skF_4') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_255,c_90])).

tff(c_30,plain,(
    ! [A_23] : k2_tarski(A_23,A_23) = k1_tarski(A_23) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_32,plain,(
    ! [A_24,B_25] : k1_enumset1(A_24,A_24,B_25) = k2_tarski(A_24,B_25) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_652,plain,(
    ! [B_110,A_111,C_112] : k2_xboole_0(k2_tarski(B_110,A_111),k2_tarski(C_112,A_111)) = k1_enumset1(A_111,B_110,C_112) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_700,plain,(
    ! [B_113,A_114,C_115] : r1_tarski(k2_tarski(B_113,A_114),k1_enumset1(A_114,B_113,C_115)) ),
    inference(superposition,[status(thm),theory(equality)],[c_652,c_20])).

tff(c_709,plain,(
    ! [A_24,B_25] : r1_tarski(k2_tarski(A_24,A_24),k2_tarski(A_24,B_25)) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_700])).

tff(c_716,plain,(
    ! [A_116,B_117] : r1_tarski(k1_tarski(A_116),k2_tarski(A_116,B_117)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_709])).

tff(c_722,plain,(
    r1_tarski(k1_tarski('#skF_3'),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_268,c_716])).

tff(c_16,plain,(
    ! [A_10,B_11] :
      ( k4_xboole_0(A_10,B_11) = k1_xboole_0
      | ~ r1_tarski(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_730,plain,(
    k4_xboole_0(k1_tarski('#skF_3'),k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_722,c_16])).

tff(c_254,plain,(
    ! [A_83] : k4_xboole_0(A_83,k1_xboole_0) = A_83 ),
    inference(resolution,[status(thm)],[c_6,c_251])).

tff(c_739,plain,(
    k1_tarski('#skF_3') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_730,c_254])).

tff(c_42,plain,(
    ! [A_40,B_41] : k2_xboole_0(k1_tarski(A_40),B_41) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_794,plain,(
    ! [B_41] : k2_xboole_0(k1_xboole_0,B_41) != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_739,c_42])).

tff(c_183,plain,(
    ! [A_70,B_71] :
      ( r2_hidden('#skF_2'(A_70,B_71),A_70)
      | r1_xboole_0(A_70,B_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_188,plain,(
    ! [A_72,B_73] :
      ( ~ v1_xboole_0(A_72)
      | r1_xboole_0(A_72,B_73) ) ),
    inference(resolution,[status(thm)],[c_183,c_2])).

tff(c_203,plain,(
    ! [A_78,B_79] :
      ( k4_xboole_0(A_78,B_79) = A_78
      | ~ v1_xboole_0(A_78) ) ),
    inference(resolution,[status(thm)],[c_188,c_22])).

tff(c_206,plain,(
    ! [B_79] : k4_xboole_0(k1_xboole_0,B_79) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_6,c_203])).

tff(c_26,plain,(
    ! [A_18,B_19] : k5_xboole_0(A_18,k4_xboole_0(B_19,A_18)) = k2_xboole_0(A_18,B_19) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_358,plain,(
    ! [A_90] : k5_xboole_0(k1_xboole_0,A_90) = k2_xboole_0(k1_xboole_0,A_90) ),
    inference(superposition,[status(thm),theory(equality)],[c_255,c_26])).

tff(c_18,plain,(
    ! [A_12,B_13] : k5_xboole_0(A_12,k3_xboole_0(A_12,B_13)) = k4_xboole_0(A_12,B_13) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_373,plain,(
    ! [B_13] : k2_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,B_13)) = k4_xboole_0(k1_xboole_0,B_13) ),
    inference(superposition,[status(thm),theory(equality)],[c_358,c_18])).

tff(c_392,plain,(
    ! [B_13] : k2_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,B_13)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_206,c_373])).

tff(c_815,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_794,c_392])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:29:02 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.89/1.52  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.89/1.52  
% 2.89/1.52  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.89/1.53  %$ r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2
% 2.89/1.53  
% 2.89/1.53  %Foreground sorts:
% 2.89/1.53  
% 2.89/1.53  
% 2.89/1.53  %Background operators:
% 2.89/1.53  
% 2.89/1.53  
% 2.89/1.53  %Foreground operators:
% 2.89/1.53  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.89/1.53  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.89/1.53  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.89/1.53  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.89/1.53  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.89/1.53  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.89/1.53  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.89/1.53  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.89/1.53  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.89/1.53  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.89/1.53  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.89/1.53  tff('#skF_5', type, '#skF_5': $i).
% 2.89/1.53  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.89/1.53  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.89/1.53  tff('#skF_3', type, '#skF_3': $i).
% 2.89/1.53  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.89/1.53  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.89/1.53  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.89/1.53  tff('#skF_4', type, '#skF_4': $i).
% 2.89/1.53  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.89/1.53  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.89/1.53  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.89/1.53  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.89/1.53  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.89/1.53  
% 3.13/1.54  tff(f_32, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 3.13/1.54  tff(f_50, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 3.13/1.54  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 3.13/1.54  tff(f_62, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 3.13/1.54  tff(f_85, negated_conjecture, ~(![A, B, C]: ~(k2_xboole_0(k2_tarski(A, B), C) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t50_zfmisc_1)).
% 3.13/1.54  tff(f_58, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 3.13/1.54  tff(f_54, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 3.13/1.54  tff(f_68, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 3.13/1.54  tff(f_70, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 3.13/1.54  tff(f_66, axiom, (![A, B, C]: (k2_xboole_0(k2_tarski(B, A), k2_tarski(C, A)) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t137_enumset1)).
% 3.13/1.54  tff(f_81, axiom, (![A, B]: ~(k2_xboole_0(k1_tarski(A), B) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_zfmisc_1)).
% 3.13/1.54  tff(f_64, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_xboole_1)).
% 3.13/1.54  tff(f_56, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 3.13/1.54  tff(c_6, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.13/1.54  tff(c_193, plain, (![A_74, B_75]: (r2_hidden('#skF_2'(A_74, B_75), B_75) | r1_xboole_0(A_74, B_75))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.13/1.54  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.13/1.54  tff(c_198, plain, (![B_76, A_77]: (~v1_xboole_0(B_76) | r1_xboole_0(A_77, B_76))), inference(resolution, [status(thm)], [c_193, c_2])).
% 3.13/1.54  tff(c_22, plain, (![A_16, B_17]: (k4_xboole_0(A_16, B_17)=A_16 | ~r1_xboole_0(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.13/1.54  tff(c_251, plain, (![A_83, B_84]: (k4_xboole_0(A_83, B_84)=A_83 | ~v1_xboole_0(B_84))), inference(resolution, [status(thm)], [c_198, c_22])).
% 3.13/1.54  tff(c_255, plain, (![A_85]: (k4_xboole_0(A_85, k1_xboole_0)=A_85)), inference(resolution, [status(thm)], [c_6, c_251])).
% 3.13/1.54  tff(c_44, plain, (k2_xboole_0(k2_tarski('#skF_3', '#skF_4'), '#skF_5')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.13/1.54  tff(c_20, plain, (![A_14, B_15]: (r1_tarski(A_14, k2_xboole_0(A_14, B_15)))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.13/1.54  tff(c_60, plain, (r1_tarski(k2_tarski('#skF_3', '#skF_4'), k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_44, c_20])).
% 3.13/1.54  tff(c_79, plain, (![A_54, B_55]: (k4_xboole_0(A_54, B_55)=k1_xboole_0 | ~r1_tarski(A_54, B_55))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.13/1.54  tff(c_90, plain, (k4_xboole_0(k2_tarski('#skF_3', '#skF_4'), k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_60, c_79])).
% 3.13/1.54  tff(c_268, plain, (k2_tarski('#skF_3', '#skF_4')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_255, c_90])).
% 3.13/1.54  tff(c_30, plain, (![A_23]: (k2_tarski(A_23, A_23)=k1_tarski(A_23))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.13/1.54  tff(c_32, plain, (![A_24, B_25]: (k1_enumset1(A_24, A_24, B_25)=k2_tarski(A_24, B_25))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.13/1.54  tff(c_652, plain, (![B_110, A_111, C_112]: (k2_xboole_0(k2_tarski(B_110, A_111), k2_tarski(C_112, A_111))=k1_enumset1(A_111, B_110, C_112))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.13/1.54  tff(c_700, plain, (![B_113, A_114, C_115]: (r1_tarski(k2_tarski(B_113, A_114), k1_enumset1(A_114, B_113, C_115)))), inference(superposition, [status(thm), theory('equality')], [c_652, c_20])).
% 3.13/1.54  tff(c_709, plain, (![A_24, B_25]: (r1_tarski(k2_tarski(A_24, A_24), k2_tarski(A_24, B_25)))), inference(superposition, [status(thm), theory('equality')], [c_32, c_700])).
% 3.13/1.54  tff(c_716, plain, (![A_116, B_117]: (r1_tarski(k1_tarski(A_116), k2_tarski(A_116, B_117)))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_709])).
% 3.13/1.54  tff(c_722, plain, (r1_tarski(k1_tarski('#skF_3'), k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_268, c_716])).
% 3.13/1.54  tff(c_16, plain, (![A_10, B_11]: (k4_xboole_0(A_10, B_11)=k1_xboole_0 | ~r1_tarski(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.13/1.54  tff(c_730, plain, (k4_xboole_0(k1_tarski('#skF_3'), k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_722, c_16])).
% 3.13/1.54  tff(c_254, plain, (![A_83]: (k4_xboole_0(A_83, k1_xboole_0)=A_83)), inference(resolution, [status(thm)], [c_6, c_251])).
% 3.13/1.54  tff(c_739, plain, (k1_tarski('#skF_3')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_730, c_254])).
% 3.13/1.54  tff(c_42, plain, (![A_40, B_41]: (k2_xboole_0(k1_tarski(A_40), B_41)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.13/1.54  tff(c_794, plain, (![B_41]: (k2_xboole_0(k1_xboole_0, B_41)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_739, c_42])).
% 3.13/1.54  tff(c_183, plain, (![A_70, B_71]: (r2_hidden('#skF_2'(A_70, B_71), A_70) | r1_xboole_0(A_70, B_71))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.13/1.54  tff(c_188, plain, (![A_72, B_73]: (~v1_xboole_0(A_72) | r1_xboole_0(A_72, B_73))), inference(resolution, [status(thm)], [c_183, c_2])).
% 3.13/1.54  tff(c_203, plain, (![A_78, B_79]: (k4_xboole_0(A_78, B_79)=A_78 | ~v1_xboole_0(A_78))), inference(resolution, [status(thm)], [c_188, c_22])).
% 3.13/1.54  tff(c_206, plain, (![B_79]: (k4_xboole_0(k1_xboole_0, B_79)=k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_203])).
% 3.13/1.54  tff(c_26, plain, (![A_18, B_19]: (k5_xboole_0(A_18, k4_xboole_0(B_19, A_18))=k2_xboole_0(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.13/1.54  tff(c_358, plain, (![A_90]: (k5_xboole_0(k1_xboole_0, A_90)=k2_xboole_0(k1_xboole_0, A_90))), inference(superposition, [status(thm), theory('equality')], [c_255, c_26])).
% 3.13/1.54  tff(c_18, plain, (![A_12, B_13]: (k5_xboole_0(A_12, k3_xboole_0(A_12, B_13))=k4_xboole_0(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.13/1.54  tff(c_373, plain, (![B_13]: (k2_xboole_0(k1_xboole_0, k3_xboole_0(k1_xboole_0, B_13))=k4_xboole_0(k1_xboole_0, B_13))), inference(superposition, [status(thm), theory('equality')], [c_358, c_18])).
% 3.13/1.54  tff(c_392, plain, (![B_13]: (k2_xboole_0(k1_xboole_0, k3_xboole_0(k1_xboole_0, B_13))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_206, c_373])).
% 3.13/1.54  tff(c_815, plain, $false, inference(negUnitSimplification, [status(thm)], [c_794, c_392])).
% 3.13/1.54  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.13/1.54  
% 3.13/1.54  Inference rules
% 3.13/1.54  ----------------------
% 3.13/1.54  #Ref     : 0
% 3.13/1.54  #Sup     : 200
% 3.13/1.54  #Fact    : 0
% 3.13/1.54  #Define  : 0
% 3.13/1.54  #Split   : 0
% 3.13/1.54  #Chain   : 0
% 3.13/1.54  #Close   : 0
% 3.13/1.54  
% 3.13/1.54  Ordering : KBO
% 3.13/1.54  
% 3.13/1.54  Simplification rules
% 3.13/1.54  ----------------------
% 3.13/1.54  #Subsume      : 6
% 3.13/1.54  #Demod        : 103
% 3.13/1.54  #Tautology    : 120
% 3.13/1.54  #SimpNegUnit  : 2
% 3.13/1.54  #BackRed      : 7
% 3.13/1.54  
% 3.13/1.54  #Partial instantiations: 0
% 3.13/1.54  #Strategies tried      : 1
% 3.13/1.54  
% 3.13/1.54  Timing (in seconds)
% 3.13/1.54  ----------------------
% 3.13/1.54  Preprocessing        : 0.36
% 3.13/1.54  Parsing              : 0.18
% 3.13/1.54  CNF conversion       : 0.03
% 3.13/1.54  Main loop            : 0.35
% 3.13/1.54  Inferencing          : 0.14
% 3.13/1.54  Reduction            : 0.12
% 3.13/1.54  Demodulation         : 0.09
% 3.13/1.54  BG Simplification    : 0.02
% 3.13/1.54  Subsumption          : 0.04
% 3.13/1.54  Abstraction          : 0.02
% 3.13/1.54  MUC search           : 0.00
% 3.13/1.54  Cooper               : 0.00
% 3.13/1.54  Total                : 0.74
% 3.13/1.54  Index Insertion      : 0.00
% 3.13/1.54  Index Deletion       : 0.00
% 3.13/1.54  Index Matching       : 0.00
% 3.13/1.54  BG Taut test         : 0.00
%------------------------------------------------------------------------------
