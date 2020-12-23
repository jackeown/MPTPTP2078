%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:50:53 EST 2020

% Result     : Theorem 3.25s
% Output     : CNFRefutation 3.58s
% Verified   : 
% Statistics : Number of formulae       :   76 ( 137 expanded)
%              Number of leaves         :   31 (  58 expanded)
%              Depth                    :   16
%              Number of atoms          :   75 ( 140 expanded)
%              Number of equality atoms :   49 ( 110 expanded)
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_zfmisc_1)).

tff(f_35,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

tff(f_49,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_59,axiom,(
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

tff(f_51,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_65,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_tarski(A,B),C)
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).

tff(c_42,plain,(
    r2_hidden('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_10,plain,(
    ! [A_5] : k2_xboole_0(A_5,k1_xboole_0) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_22,plain,(
    ! [B_17,A_16] : k2_tarski(B_17,A_16) = k2_tarski(A_16,B_17) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_101,plain,(
    ! [A_40,B_41] : k3_tarski(k2_tarski(A_40,B_41)) = k2_xboole_0(A_40,B_41) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_314,plain,(
    ! [B_70,A_71] : k3_tarski(k2_tarski(B_70,A_71)) = k2_xboole_0(A_71,B_70) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_101])).

tff(c_32,plain,(
    ! [A_28,B_29] : k3_tarski(k2_tarski(A_28,B_29)) = k2_xboole_0(A_28,B_29) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_341,plain,(
    ! [B_72,A_73] : k2_xboole_0(B_72,A_73) = k2_xboole_0(A_73,B_72) ),
    inference(superposition,[status(thm),theory(equality)],[c_314,c_32])).

tff(c_391,plain,(
    ! [A_73] : k2_xboole_0(k1_xboole_0,A_73) = A_73 ),
    inference(superposition,[status(thm),theory(equality)],[c_341,c_10])).

tff(c_679,plain,(
    ! [A_89,B_90] : k2_xboole_0(A_89,k4_xboole_0(B_90,A_89)) = k2_xboole_0(A_89,B_90) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_692,plain,(
    ! [B_90] : k4_xboole_0(B_90,k1_xboole_0) = k2_xboole_0(k1_xboole_0,B_90) ),
    inference(superposition,[status(thm),theory(equality)],[c_679,c_391])).

tff(c_729,plain,(
    ! [B_91] : k4_xboole_0(B_91,k1_xboole_0) = B_91 ),
    inference(demodulation,[status(thm),theory(equality)],[c_391,c_692])).

tff(c_20,plain,(
    ! [A_14,B_15] : k5_xboole_0(A_14,k4_xboole_0(B_15,A_14)) = k2_xboole_0(A_14,B_15) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_738,plain,(
    ! [B_91] : k5_xboole_0(k1_xboole_0,B_91) = k2_xboole_0(k1_xboole_0,B_91) ),
    inference(superposition,[status(thm),theory(equality)],[c_729,c_20])).

tff(c_752,plain,(
    ! [B_91] : k5_xboole_0(k1_xboole_0,B_91) = B_91 ),
    inference(demodulation,[status(thm),theory(equality)],[c_391,c_738])).

tff(c_422,plain,(
    ! [A_74] : k2_xboole_0(k1_xboole_0,A_74) = A_74 ),
    inference(superposition,[status(thm),theory(equality)],[c_341,c_10])).

tff(c_18,plain,(
    ! [A_12,B_13] : r1_tarski(A_12,k2_xboole_0(A_12,B_13)) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_153,plain,(
    ! [A_46,B_47] :
      ( k3_xboole_0(A_46,B_47) = A_46
      | ~ r1_tarski(A_46,B_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_164,plain,(
    ! [A_12,B_13] : k3_xboole_0(A_12,k2_xboole_0(A_12,B_13)) = A_12 ),
    inference(resolution,[status(thm)],[c_18,c_153])).

tff(c_437,plain,(
    ! [A_74] : k3_xboole_0(k1_xboole_0,A_74) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_422,c_164])).

tff(c_776,plain,(
    ! [A_93,B_94] : k5_xboole_0(A_93,k3_xboole_0(A_93,B_94)) = k4_xboole_0(A_93,B_94) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_796,plain,(
    ! [A_74] : k5_xboole_0(k1_xboole_0,k1_xboole_0) = k4_xboole_0(k1_xboole_0,A_74) ),
    inference(superposition,[status(thm),theory(equality)],[c_437,c_776])).

tff(c_810,plain,(
    ! [A_74] : k4_xboole_0(k1_xboole_0,A_74) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_752,c_796])).

tff(c_16,plain,(
    ! [A_10,B_11] : k4_xboole_0(k2_xboole_0(A_10,B_11),B_11) = k4_xboole_0(A_10,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_434,plain,(
    ! [A_74] : k4_xboole_0(k1_xboole_0,A_74) = k4_xboole_0(A_74,A_74) ),
    inference(superposition,[status(thm),theory(equality)],[c_422,c_16])).

tff(c_896,plain,(
    ! [A_74] : k4_xboole_0(A_74,A_74) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_810,c_434])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_165,plain,(
    ! [B_2] : k3_xboole_0(B_2,B_2) = B_2 ),
    inference(resolution,[status(thm)],[c_6,c_153])).

tff(c_805,plain,(
    ! [B_2] : k5_xboole_0(B_2,B_2) = k4_xboole_0(B_2,B_2) ),
    inference(superposition,[status(thm),theory(equality)],[c_165,c_776])).

tff(c_897,plain,(
    ! [B_2] : k5_xboole_0(B_2,B_2) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_896,c_805])).

tff(c_24,plain,(
    ! [A_18] : k2_tarski(A_18,A_18) = k1_tarski(A_18) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_958,plain,(
    ! [A_103,B_104,C_105] :
      ( r1_tarski(k2_tarski(A_103,B_104),C_105)
      | ~ r2_hidden(B_104,C_105)
      | ~ r2_hidden(A_103,C_105) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_2216,plain,(
    ! [A_147,C_148] :
      ( r1_tarski(k1_tarski(A_147),C_148)
      | ~ r2_hidden(A_147,C_148)
      | ~ r2_hidden(A_147,C_148) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_958])).

tff(c_12,plain,(
    ! [A_6,B_7] :
      ( k3_xboole_0(A_6,B_7) = A_6
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_2340,plain,(
    ! [A_152,C_153] :
      ( k3_xboole_0(k1_tarski(A_152),C_153) = k1_tarski(A_152)
      | ~ r2_hidden(A_152,C_153) ) ),
    inference(resolution,[status(thm)],[c_2216,c_12])).

tff(c_8,plain,(
    ! [A_3,B_4] : k5_xboole_0(A_3,k3_xboole_0(A_3,B_4)) = k4_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_2346,plain,(
    ! [A_152,C_153] :
      ( k5_xboole_0(k1_tarski(A_152),k1_tarski(A_152)) = k4_xboole_0(k1_tarski(A_152),C_153)
      | ~ r2_hidden(A_152,C_153) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2340,c_8])).

tff(c_2395,plain,(
    ! [A_154,C_155] :
      ( k4_xboole_0(k1_tarski(A_154),C_155) = k1_xboole_0
      | ~ r2_hidden(A_154,C_155) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_897,c_2346])).

tff(c_14,plain,(
    ! [A_8,B_9] : k2_xboole_0(A_8,k4_xboole_0(B_9,A_8)) = k2_xboole_0(A_8,B_9) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_2429,plain,(
    ! [C_155,A_154] :
      ( k2_xboole_0(C_155,k1_tarski(A_154)) = k2_xboole_0(C_155,k1_xboole_0)
      | ~ r2_hidden(A_154,C_155) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2395,c_14])).

tff(c_2478,plain,(
    ! [C_156,A_157] :
      ( k2_xboole_0(C_156,k1_tarski(A_157)) = C_156
      | ~ r2_hidden(A_157,C_156) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_2429])).

tff(c_320,plain,(
    ! [B_70,A_71] : k2_xboole_0(B_70,A_71) = k2_xboole_0(A_71,B_70) ),
    inference(superposition,[status(thm),theory(equality)],[c_314,c_32])).

tff(c_40,plain,(
    k2_xboole_0(k1_tarski('#skF_1'),'#skF_2') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_340,plain,(
    k2_xboole_0('#skF_2',k1_tarski('#skF_1')) != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_320,c_40])).

tff(c_2548,plain,(
    ~ r2_hidden('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_2478,c_340])).

tff(c_2625,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_2548])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n010.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 10:18:44 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.25/1.61  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.58/1.62  
% 3.58/1.62  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.58/1.62  %$ r2_hidden > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1
% 3.58/1.62  
% 3.58/1.62  %Foreground sorts:
% 3.58/1.62  
% 3.58/1.62  
% 3.58/1.62  %Background operators:
% 3.58/1.62  
% 3.58/1.62  
% 3.58/1.62  %Foreground operators:
% 3.58/1.62  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.58/1.62  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.58/1.62  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.58/1.62  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.58/1.62  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.58/1.62  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.58/1.62  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.58/1.62  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.58/1.62  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.58/1.62  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.58/1.62  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.58/1.62  tff('#skF_2', type, '#skF_2': $i).
% 3.58/1.62  tff('#skF_1', type, '#skF_1': $i).
% 3.58/1.62  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.58/1.62  tff(k3_tarski, type, k3_tarski: $i > $i).
% 3.58/1.62  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.58/1.62  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.58/1.62  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.58/1.62  
% 3.58/1.64  tff(f_70, negated_conjecture, ~(![A, B]: (r2_hidden(A, B) => (k2_xboole_0(k1_tarski(A), B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_zfmisc_1)).
% 3.58/1.64  tff(f_35, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 3.58/1.64  tff(f_49, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 3.58/1.64  tff(f_59, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 3.58/1.64  tff(f_41, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 3.58/1.64  tff(f_47, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_xboole_1)).
% 3.58/1.64  tff(f_45, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 3.58/1.64  tff(f_39, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 3.58/1.64  tff(f_33, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 3.58/1.64  tff(f_43, axiom, (![A, B]: (k4_xboole_0(k2_xboole_0(A, B), B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t40_xboole_1)).
% 3.58/1.64  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.58/1.64  tff(f_51, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 3.58/1.64  tff(f_65, axiom, (![A, B, C]: (r1_tarski(k2_tarski(A, B), C) <=> (r2_hidden(A, C) & r2_hidden(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 3.58/1.64  tff(c_42, plain, (r2_hidden('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.58/1.64  tff(c_10, plain, (![A_5]: (k2_xboole_0(A_5, k1_xboole_0)=A_5)), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.58/1.64  tff(c_22, plain, (![B_17, A_16]: (k2_tarski(B_17, A_16)=k2_tarski(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.58/1.64  tff(c_101, plain, (![A_40, B_41]: (k3_tarski(k2_tarski(A_40, B_41))=k2_xboole_0(A_40, B_41))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.58/1.64  tff(c_314, plain, (![B_70, A_71]: (k3_tarski(k2_tarski(B_70, A_71))=k2_xboole_0(A_71, B_70))), inference(superposition, [status(thm), theory('equality')], [c_22, c_101])).
% 3.58/1.64  tff(c_32, plain, (![A_28, B_29]: (k3_tarski(k2_tarski(A_28, B_29))=k2_xboole_0(A_28, B_29))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.58/1.64  tff(c_341, plain, (![B_72, A_73]: (k2_xboole_0(B_72, A_73)=k2_xboole_0(A_73, B_72))), inference(superposition, [status(thm), theory('equality')], [c_314, c_32])).
% 3.58/1.64  tff(c_391, plain, (![A_73]: (k2_xboole_0(k1_xboole_0, A_73)=A_73)), inference(superposition, [status(thm), theory('equality')], [c_341, c_10])).
% 3.58/1.64  tff(c_679, plain, (![A_89, B_90]: (k2_xboole_0(A_89, k4_xboole_0(B_90, A_89))=k2_xboole_0(A_89, B_90))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.58/1.64  tff(c_692, plain, (![B_90]: (k4_xboole_0(B_90, k1_xboole_0)=k2_xboole_0(k1_xboole_0, B_90))), inference(superposition, [status(thm), theory('equality')], [c_679, c_391])).
% 3.58/1.64  tff(c_729, plain, (![B_91]: (k4_xboole_0(B_91, k1_xboole_0)=B_91)), inference(demodulation, [status(thm), theory('equality')], [c_391, c_692])).
% 3.58/1.64  tff(c_20, plain, (![A_14, B_15]: (k5_xboole_0(A_14, k4_xboole_0(B_15, A_14))=k2_xboole_0(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.58/1.64  tff(c_738, plain, (![B_91]: (k5_xboole_0(k1_xboole_0, B_91)=k2_xboole_0(k1_xboole_0, B_91))), inference(superposition, [status(thm), theory('equality')], [c_729, c_20])).
% 3.58/1.64  tff(c_752, plain, (![B_91]: (k5_xboole_0(k1_xboole_0, B_91)=B_91)), inference(demodulation, [status(thm), theory('equality')], [c_391, c_738])).
% 3.58/1.64  tff(c_422, plain, (![A_74]: (k2_xboole_0(k1_xboole_0, A_74)=A_74)), inference(superposition, [status(thm), theory('equality')], [c_341, c_10])).
% 3.58/1.64  tff(c_18, plain, (![A_12, B_13]: (r1_tarski(A_12, k2_xboole_0(A_12, B_13)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.58/1.64  tff(c_153, plain, (![A_46, B_47]: (k3_xboole_0(A_46, B_47)=A_46 | ~r1_tarski(A_46, B_47))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.58/1.64  tff(c_164, plain, (![A_12, B_13]: (k3_xboole_0(A_12, k2_xboole_0(A_12, B_13))=A_12)), inference(resolution, [status(thm)], [c_18, c_153])).
% 3.58/1.64  tff(c_437, plain, (![A_74]: (k3_xboole_0(k1_xboole_0, A_74)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_422, c_164])).
% 3.58/1.64  tff(c_776, plain, (![A_93, B_94]: (k5_xboole_0(A_93, k3_xboole_0(A_93, B_94))=k4_xboole_0(A_93, B_94))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.58/1.64  tff(c_796, plain, (![A_74]: (k5_xboole_0(k1_xboole_0, k1_xboole_0)=k4_xboole_0(k1_xboole_0, A_74))), inference(superposition, [status(thm), theory('equality')], [c_437, c_776])).
% 3.58/1.64  tff(c_810, plain, (![A_74]: (k4_xboole_0(k1_xboole_0, A_74)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_752, c_796])).
% 3.58/1.64  tff(c_16, plain, (![A_10, B_11]: (k4_xboole_0(k2_xboole_0(A_10, B_11), B_11)=k4_xboole_0(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.58/1.64  tff(c_434, plain, (![A_74]: (k4_xboole_0(k1_xboole_0, A_74)=k4_xboole_0(A_74, A_74))), inference(superposition, [status(thm), theory('equality')], [c_422, c_16])).
% 3.58/1.64  tff(c_896, plain, (![A_74]: (k4_xboole_0(A_74, A_74)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_810, c_434])).
% 3.58/1.64  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.58/1.64  tff(c_165, plain, (![B_2]: (k3_xboole_0(B_2, B_2)=B_2)), inference(resolution, [status(thm)], [c_6, c_153])).
% 3.58/1.64  tff(c_805, plain, (![B_2]: (k5_xboole_0(B_2, B_2)=k4_xboole_0(B_2, B_2))), inference(superposition, [status(thm), theory('equality')], [c_165, c_776])).
% 3.58/1.64  tff(c_897, plain, (![B_2]: (k5_xboole_0(B_2, B_2)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_896, c_805])).
% 3.58/1.64  tff(c_24, plain, (![A_18]: (k2_tarski(A_18, A_18)=k1_tarski(A_18))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.58/1.64  tff(c_958, plain, (![A_103, B_104, C_105]: (r1_tarski(k2_tarski(A_103, B_104), C_105) | ~r2_hidden(B_104, C_105) | ~r2_hidden(A_103, C_105))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.58/1.64  tff(c_2216, plain, (![A_147, C_148]: (r1_tarski(k1_tarski(A_147), C_148) | ~r2_hidden(A_147, C_148) | ~r2_hidden(A_147, C_148))), inference(superposition, [status(thm), theory('equality')], [c_24, c_958])).
% 3.58/1.64  tff(c_12, plain, (![A_6, B_7]: (k3_xboole_0(A_6, B_7)=A_6 | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.58/1.64  tff(c_2340, plain, (![A_152, C_153]: (k3_xboole_0(k1_tarski(A_152), C_153)=k1_tarski(A_152) | ~r2_hidden(A_152, C_153))), inference(resolution, [status(thm)], [c_2216, c_12])).
% 3.58/1.64  tff(c_8, plain, (![A_3, B_4]: (k5_xboole_0(A_3, k3_xboole_0(A_3, B_4))=k4_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.58/1.64  tff(c_2346, plain, (![A_152, C_153]: (k5_xboole_0(k1_tarski(A_152), k1_tarski(A_152))=k4_xboole_0(k1_tarski(A_152), C_153) | ~r2_hidden(A_152, C_153))), inference(superposition, [status(thm), theory('equality')], [c_2340, c_8])).
% 3.58/1.64  tff(c_2395, plain, (![A_154, C_155]: (k4_xboole_0(k1_tarski(A_154), C_155)=k1_xboole_0 | ~r2_hidden(A_154, C_155))), inference(demodulation, [status(thm), theory('equality')], [c_897, c_2346])).
% 3.58/1.64  tff(c_14, plain, (![A_8, B_9]: (k2_xboole_0(A_8, k4_xboole_0(B_9, A_8))=k2_xboole_0(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.58/1.64  tff(c_2429, plain, (![C_155, A_154]: (k2_xboole_0(C_155, k1_tarski(A_154))=k2_xboole_0(C_155, k1_xboole_0) | ~r2_hidden(A_154, C_155))), inference(superposition, [status(thm), theory('equality')], [c_2395, c_14])).
% 3.58/1.64  tff(c_2478, plain, (![C_156, A_157]: (k2_xboole_0(C_156, k1_tarski(A_157))=C_156 | ~r2_hidden(A_157, C_156))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_2429])).
% 3.58/1.64  tff(c_320, plain, (![B_70, A_71]: (k2_xboole_0(B_70, A_71)=k2_xboole_0(A_71, B_70))), inference(superposition, [status(thm), theory('equality')], [c_314, c_32])).
% 3.58/1.64  tff(c_40, plain, (k2_xboole_0(k1_tarski('#skF_1'), '#skF_2')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.58/1.64  tff(c_340, plain, (k2_xboole_0('#skF_2', k1_tarski('#skF_1'))!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_320, c_40])).
% 3.58/1.64  tff(c_2548, plain, (~r2_hidden('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_2478, c_340])).
% 3.58/1.64  tff(c_2625, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_42, c_2548])).
% 3.58/1.64  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.58/1.64  
% 3.58/1.64  Inference rules
% 3.58/1.64  ----------------------
% 3.58/1.64  #Ref     : 0
% 3.58/1.64  #Sup     : 599
% 3.58/1.64  #Fact    : 0
% 3.58/1.64  #Define  : 0
% 3.58/1.64  #Split   : 0
% 3.58/1.64  #Chain   : 0
% 3.58/1.64  #Close   : 0
% 3.58/1.64  
% 3.58/1.64  Ordering : KBO
% 3.58/1.64  
% 3.58/1.64  Simplification rules
% 3.58/1.64  ----------------------
% 3.58/1.64  #Subsume      : 27
% 3.58/1.64  #Demod        : 541
% 3.58/1.64  #Tautology    : 468
% 3.58/1.64  #SimpNegUnit  : 0
% 3.58/1.64  #BackRed      : 6
% 3.58/1.64  
% 3.58/1.64  #Partial instantiations: 0
% 3.58/1.64  #Strategies tried      : 1
% 3.58/1.64  
% 3.58/1.64  Timing (in seconds)
% 3.58/1.64  ----------------------
% 3.58/1.64  Preprocessing        : 0.31
% 3.58/1.64  Parsing              : 0.17
% 3.58/1.64  CNF conversion       : 0.02
% 3.58/1.64  Main loop            : 0.50
% 3.58/1.64  Inferencing          : 0.17
% 3.58/1.64  Reduction            : 0.22
% 3.58/1.64  Demodulation         : 0.18
% 3.58/1.64  BG Simplification    : 0.02
% 3.58/1.64  Subsumption          : 0.07
% 3.58/1.64  Abstraction          : 0.03
% 3.58/1.64  MUC search           : 0.00
% 3.58/1.64  Cooper               : 0.00
% 3.58/1.64  Total                : 0.84
% 3.58/1.64  Index Insertion      : 0.00
% 3.58/1.64  Index Deletion       : 0.00
% 3.58/1.64  Index Matching       : 0.00
% 3.58/1.64  BG Taut test         : 0.00
%------------------------------------------------------------------------------
