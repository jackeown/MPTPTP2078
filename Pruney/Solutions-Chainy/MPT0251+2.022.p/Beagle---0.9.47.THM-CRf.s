%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:50:49 EST 2020

% Result     : Theorem 8.46s
% Output     : CNFRefutation 8.46s
% Verified   : 
% Statistics : Number of formulae       :   71 (  82 expanded)
%              Number of leaves         :   35 (  43 expanded)
%              Depth                    :   11
%              Number of atoms          :   88 ( 113 expanded)
%              Number of equality atoms :   26 (  29 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_xboole_0 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_1 > #skF_4 > #skF_5 > #skF_6 > #skF_3 > #skF_2

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

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

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

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

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

tff(f_88,negated_conjecture,(
    ~ ! [A,B] :
        ( r2_hidden(A,B)
       => k2_xboole_0(k1_tarski(A),B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_zfmisc_1)).

tff(f_59,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

tff(f_69,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_83,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_tarski(A,B),C)
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_48,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_49,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_55,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_65,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_67,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_77,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(c_66,plain,(
    r2_hidden('#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_40,plain,(
    ! [A_20] : k2_xboole_0(A_20,k1_xboole_0) = A_20 ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_48,plain,(
    ! [A_27] : k2_tarski(A_27,A_27) = k1_tarski(A_27) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_870,plain,(
    ! [A_140,B_141,C_142] :
      ( r1_tarski(k2_tarski(A_140,B_141),C_142)
      | ~ r2_hidden(B_141,C_142)
      | ~ r2_hidden(A_140,C_142) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_902,plain,(
    ! [A_27,C_142] :
      ( r1_tarski(k1_tarski(A_27),C_142)
      | ~ r2_hidden(A_27,C_142)
      | ~ r2_hidden(A_27,C_142) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_870])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_188,plain,(
    ! [D_58,A_59,B_60] :
      ( r2_hidden(D_58,A_59)
      | ~ r2_hidden(D_58,k4_xboole_0(A_59,B_60)) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_1134,plain,(
    ! [A_167,B_168] :
      ( r2_hidden('#skF_1'(k4_xboole_0(A_167,B_168)),A_167)
      | v1_xboole_0(k4_xboole_0(A_167,B_168)) ) ),
    inference(resolution,[status(thm)],[c_4,c_188])).

tff(c_6,plain,(
    ! [C_9,B_6,A_5] :
      ( r2_hidden(C_9,B_6)
      | ~ r2_hidden(C_9,A_5)
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_12865,plain,(
    ! [A_654,B_655,B_656] :
      ( r2_hidden('#skF_1'(k4_xboole_0(A_654,B_655)),B_656)
      | ~ r1_tarski(A_654,B_656)
      | v1_xboole_0(k4_xboole_0(A_654,B_655)) ) ),
    inference(resolution,[status(thm)],[c_1134,c_6])).

tff(c_420,plain,(
    ! [D_86,B_87,A_88] :
      ( ~ r2_hidden(D_86,B_87)
      | ~ r2_hidden(D_86,k4_xboole_0(A_88,B_87)) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_428,plain,(
    ! [A_88,B_87] :
      ( ~ r2_hidden('#skF_1'(k4_xboole_0(A_88,B_87)),B_87)
      | v1_xboole_0(k4_xboole_0(A_88,B_87)) ) ),
    inference(resolution,[status(thm)],[c_4,c_420])).

tff(c_12991,plain,(
    ! [A_657,B_658] :
      ( ~ r1_tarski(A_657,B_658)
      | v1_xboole_0(k4_xboole_0(A_657,B_658)) ) ),
    inference(resolution,[status(thm)],[c_12865,c_428])).

tff(c_30,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_472,plain,(
    ! [A_97,B_98] :
      ( r2_hidden('#skF_2'(A_97,B_98),A_97)
      | r1_tarski(A_97,B_98) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_496,plain,(
    ! [A_97,B_98] :
      ( ~ v1_xboole_0(A_97)
      | r1_tarski(A_97,B_98) ) ),
    inference(resolution,[status(thm)],[c_472,c_2])).

tff(c_497,plain,(
    ! [A_99,B_100] :
      ( ~ v1_xboole_0(A_99)
      | r1_tarski(A_99,B_100) ) ),
    inference(resolution,[status(thm)],[c_472,c_2])).

tff(c_32,plain,(
    ! [B_17,A_16] :
      ( B_17 = A_16
      | ~ r1_tarski(B_17,A_16)
      | ~ r1_tarski(A_16,B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_698,plain,(
    ! [B_116,A_117] :
      ( B_116 = A_117
      | ~ r1_tarski(B_116,A_117)
      | ~ v1_xboole_0(A_117) ) ),
    inference(resolution,[status(thm)],[c_497,c_32])).

tff(c_708,plain,(
    ! [B_118,A_119] :
      ( B_118 = A_119
      | ~ v1_xboole_0(B_118)
      | ~ v1_xboole_0(A_119) ) ),
    inference(resolution,[status(thm)],[c_496,c_698])).

tff(c_711,plain,(
    ! [A_119] :
      ( k1_xboole_0 = A_119
      | ~ v1_xboole_0(A_119) ) ),
    inference(resolution,[status(thm)],[c_30,c_708])).

tff(c_13098,plain,(
    ! [A_659,B_660] :
      ( k4_xboole_0(A_659,B_660) = k1_xboole_0
      | ~ r1_tarski(A_659,B_660) ) ),
    inference(resolution,[status(thm)],[c_12991,c_711])).

tff(c_13396,plain,(
    ! [A_675,C_676] :
      ( k4_xboole_0(k1_tarski(A_675),C_676) = k1_xboole_0
      | ~ r2_hidden(A_675,C_676) ) ),
    inference(resolution,[status(thm)],[c_902,c_13098])).

tff(c_44,plain,(
    ! [A_23,B_24] : k2_xboole_0(A_23,k4_xboole_0(B_24,A_23)) = k2_xboole_0(A_23,B_24) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_13819,plain,(
    ! [C_676,A_675] :
      ( k2_xboole_0(C_676,k1_tarski(A_675)) = k2_xboole_0(C_676,k1_xboole_0)
      | ~ r2_hidden(A_675,C_676) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_13396,c_44])).

tff(c_14006,plain,(
    ! [C_682,A_683] :
      ( k2_xboole_0(C_682,k1_tarski(A_683)) = C_682
      | ~ r2_hidden(A_683,C_682) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_13819])).

tff(c_46,plain,(
    ! [B_26,A_25] : k2_tarski(B_26,A_25) = k2_tarski(A_25,B_26) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_130,plain,(
    ! [A_50,B_51] : k3_tarski(k2_tarski(A_50,B_51)) = k2_xboole_0(A_50,B_51) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_194,plain,(
    ! [B_61,A_62] : k3_tarski(k2_tarski(B_61,A_62)) = k2_xboole_0(A_62,B_61) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_130])).

tff(c_56,plain,(
    ! [A_37,B_38] : k3_tarski(k2_tarski(A_37,B_38)) = k2_xboole_0(A_37,B_38) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_200,plain,(
    ! [B_61,A_62] : k2_xboole_0(B_61,A_62) = k2_xboole_0(A_62,B_61) ),
    inference(superposition,[status(thm),theory(equality)],[c_194,c_56])).

tff(c_64,plain,(
    k2_xboole_0(k1_tarski('#skF_5'),'#skF_6') != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_220,plain,(
    k2_xboole_0('#skF_6',k1_tarski('#skF_5')) != '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_200,c_64])).

tff(c_14024,plain,(
    ~ r2_hidden('#skF_5','#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_14006,c_220])).

tff(c_14069,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_14024])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:44:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.46/3.02  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.46/3.02  
% 8.46/3.02  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.46/3.02  %$ r2_hidden > r1_tarski > v1_xboole_0 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_1 > #skF_4 > #skF_5 > #skF_6 > #skF_3 > #skF_2
% 8.46/3.02  
% 8.46/3.02  %Foreground sorts:
% 8.46/3.02  
% 8.46/3.02  
% 8.46/3.02  %Background operators:
% 8.46/3.02  
% 8.46/3.02  
% 8.46/3.02  %Foreground operators:
% 8.46/3.02  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.46/3.02  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 8.46/3.02  tff(k1_tarski, type, k1_tarski: $i > $i).
% 8.46/3.02  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 8.46/3.02  tff('#skF_1', type, '#skF_1': $i > $i).
% 8.46/3.02  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 8.46/3.02  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 8.46/3.02  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 8.46/3.02  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 8.46/3.02  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 8.46/3.02  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 8.46/3.02  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 8.46/3.02  tff('#skF_5', type, '#skF_5': $i).
% 8.46/3.02  tff('#skF_6', type, '#skF_6': $i).
% 8.46/3.02  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 8.46/3.02  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.46/3.02  tff(k3_tarski, type, k3_tarski: $i > $i).
% 8.46/3.02  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 8.46/3.02  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.46/3.02  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 8.46/3.02  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 8.46/3.02  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 8.46/3.02  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 8.46/3.02  
% 8.46/3.04  tff(f_88, negated_conjecture, ~(![A, B]: (r2_hidden(A, B) => (k2_xboole_0(k1_tarski(A), B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_zfmisc_1)).
% 8.46/3.04  tff(f_59, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 8.46/3.04  tff(f_69, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 8.46/3.04  tff(f_83, axiom, (![A, B, C]: (r1_tarski(k2_tarski(A, B), C) <=> (r2_hidden(A, C) & r2_hidden(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 8.46/3.04  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 8.46/3.04  tff(f_48, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 8.46/3.04  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 8.46/3.04  tff(f_49, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 8.46/3.04  tff(f_55, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 8.46/3.04  tff(f_65, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 8.46/3.04  tff(f_67, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 8.46/3.04  tff(f_77, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 8.46/3.04  tff(c_66, plain, (r2_hidden('#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_88])).
% 8.46/3.04  tff(c_40, plain, (![A_20]: (k2_xboole_0(A_20, k1_xboole_0)=A_20)), inference(cnfTransformation, [status(thm)], [f_59])).
% 8.46/3.04  tff(c_48, plain, (![A_27]: (k2_tarski(A_27, A_27)=k1_tarski(A_27))), inference(cnfTransformation, [status(thm)], [f_69])).
% 8.46/3.04  tff(c_870, plain, (![A_140, B_141, C_142]: (r1_tarski(k2_tarski(A_140, B_141), C_142) | ~r2_hidden(B_141, C_142) | ~r2_hidden(A_140, C_142))), inference(cnfTransformation, [status(thm)], [f_83])).
% 8.46/3.04  tff(c_902, plain, (![A_27, C_142]: (r1_tarski(k1_tarski(A_27), C_142) | ~r2_hidden(A_27, C_142) | ~r2_hidden(A_27, C_142))), inference(superposition, [status(thm), theory('equality')], [c_48, c_870])).
% 8.46/3.04  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 8.46/3.04  tff(c_188, plain, (![D_58, A_59, B_60]: (r2_hidden(D_58, A_59) | ~r2_hidden(D_58, k4_xboole_0(A_59, B_60)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 8.46/3.04  tff(c_1134, plain, (![A_167, B_168]: (r2_hidden('#skF_1'(k4_xboole_0(A_167, B_168)), A_167) | v1_xboole_0(k4_xboole_0(A_167, B_168)))), inference(resolution, [status(thm)], [c_4, c_188])).
% 8.46/3.04  tff(c_6, plain, (![C_9, B_6, A_5]: (r2_hidden(C_9, B_6) | ~r2_hidden(C_9, A_5) | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_38])).
% 8.46/3.04  tff(c_12865, plain, (![A_654, B_655, B_656]: (r2_hidden('#skF_1'(k4_xboole_0(A_654, B_655)), B_656) | ~r1_tarski(A_654, B_656) | v1_xboole_0(k4_xboole_0(A_654, B_655)))), inference(resolution, [status(thm)], [c_1134, c_6])).
% 8.46/3.04  tff(c_420, plain, (![D_86, B_87, A_88]: (~r2_hidden(D_86, B_87) | ~r2_hidden(D_86, k4_xboole_0(A_88, B_87)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 8.46/3.04  tff(c_428, plain, (![A_88, B_87]: (~r2_hidden('#skF_1'(k4_xboole_0(A_88, B_87)), B_87) | v1_xboole_0(k4_xboole_0(A_88, B_87)))), inference(resolution, [status(thm)], [c_4, c_420])).
% 8.46/3.04  tff(c_12991, plain, (![A_657, B_658]: (~r1_tarski(A_657, B_658) | v1_xboole_0(k4_xboole_0(A_657, B_658)))), inference(resolution, [status(thm)], [c_12865, c_428])).
% 8.46/3.04  tff(c_30, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_49])).
% 8.46/3.04  tff(c_472, plain, (![A_97, B_98]: (r2_hidden('#skF_2'(A_97, B_98), A_97) | r1_tarski(A_97, B_98))), inference(cnfTransformation, [status(thm)], [f_38])).
% 8.46/3.04  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 8.46/3.04  tff(c_496, plain, (![A_97, B_98]: (~v1_xboole_0(A_97) | r1_tarski(A_97, B_98))), inference(resolution, [status(thm)], [c_472, c_2])).
% 8.46/3.04  tff(c_497, plain, (![A_99, B_100]: (~v1_xboole_0(A_99) | r1_tarski(A_99, B_100))), inference(resolution, [status(thm)], [c_472, c_2])).
% 8.46/3.04  tff(c_32, plain, (![B_17, A_16]: (B_17=A_16 | ~r1_tarski(B_17, A_16) | ~r1_tarski(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_55])).
% 8.46/3.04  tff(c_698, plain, (![B_116, A_117]: (B_116=A_117 | ~r1_tarski(B_116, A_117) | ~v1_xboole_0(A_117))), inference(resolution, [status(thm)], [c_497, c_32])).
% 8.46/3.04  tff(c_708, plain, (![B_118, A_119]: (B_118=A_119 | ~v1_xboole_0(B_118) | ~v1_xboole_0(A_119))), inference(resolution, [status(thm)], [c_496, c_698])).
% 8.46/3.04  tff(c_711, plain, (![A_119]: (k1_xboole_0=A_119 | ~v1_xboole_0(A_119))), inference(resolution, [status(thm)], [c_30, c_708])).
% 8.46/3.04  tff(c_13098, plain, (![A_659, B_660]: (k4_xboole_0(A_659, B_660)=k1_xboole_0 | ~r1_tarski(A_659, B_660))), inference(resolution, [status(thm)], [c_12991, c_711])).
% 8.46/3.04  tff(c_13396, plain, (![A_675, C_676]: (k4_xboole_0(k1_tarski(A_675), C_676)=k1_xboole_0 | ~r2_hidden(A_675, C_676))), inference(resolution, [status(thm)], [c_902, c_13098])).
% 8.46/3.04  tff(c_44, plain, (![A_23, B_24]: (k2_xboole_0(A_23, k4_xboole_0(B_24, A_23))=k2_xboole_0(A_23, B_24))), inference(cnfTransformation, [status(thm)], [f_65])).
% 8.46/3.04  tff(c_13819, plain, (![C_676, A_675]: (k2_xboole_0(C_676, k1_tarski(A_675))=k2_xboole_0(C_676, k1_xboole_0) | ~r2_hidden(A_675, C_676))), inference(superposition, [status(thm), theory('equality')], [c_13396, c_44])).
% 8.46/3.04  tff(c_14006, plain, (![C_682, A_683]: (k2_xboole_0(C_682, k1_tarski(A_683))=C_682 | ~r2_hidden(A_683, C_682))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_13819])).
% 8.46/3.04  tff(c_46, plain, (![B_26, A_25]: (k2_tarski(B_26, A_25)=k2_tarski(A_25, B_26))), inference(cnfTransformation, [status(thm)], [f_67])).
% 8.46/3.04  tff(c_130, plain, (![A_50, B_51]: (k3_tarski(k2_tarski(A_50, B_51))=k2_xboole_0(A_50, B_51))), inference(cnfTransformation, [status(thm)], [f_77])).
% 8.46/3.04  tff(c_194, plain, (![B_61, A_62]: (k3_tarski(k2_tarski(B_61, A_62))=k2_xboole_0(A_62, B_61))), inference(superposition, [status(thm), theory('equality')], [c_46, c_130])).
% 8.46/3.04  tff(c_56, plain, (![A_37, B_38]: (k3_tarski(k2_tarski(A_37, B_38))=k2_xboole_0(A_37, B_38))), inference(cnfTransformation, [status(thm)], [f_77])).
% 8.46/3.04  tff(c_200, plain, (![B_61, A_62]: (k2_xboole_0(B_61, A_62)=k2_xboole_0(A_62, B_61))), inference(superposition, [status(thm), theory('equality')], [c_194, c_56])).
% 8.46/3.04  tff(c_64, plain, (k2_xboole_0(k1_tarski('#skF_5'), '#skF_6')!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_88])).
% 8.46/3.04  tff(c_220, plain, (k2_xboole_0('#skF_6', k1_tarski('#skF_5'))!='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_200, c_64])).
% 8.46/3.04  tff(c_14024, plain, (~r2_hidden('#skF_5', '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_14006, c_220])).
% 8.46/3.04  tff(c_14069, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_66, c_14024])).
% 8.46/3.04  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.46/3.04  
% 8.46/3.04  Inference rules
% 8.46/3.04  ----------------------
% 8.46/3.04  #Ref     : 0
% 8.46/3.04  #Sup     : 3440
% 8.46/3.04  #Fact    : 0
% 8.46/3.04  #Define  : 0
% 8.46/3.04  #Split   : 14
% 8.46/3.04  #Chain   : 0
% 8.46/3.04  #Close   : 0
% 8.46/3.04  
% 8.46/3.04  Ordering : KBO
% 8.46/3.04  
% 8.46/3.04  Simplification rules
% 8.46/3.04  ----------------------
% 8.46/3.04  #Subsume      : 1979
% 8.46/3.04  #Demod        : 1229
% 8.46/3.04  #Tautology    : 693
% 8.46/3.04  #SimpNegUnit  : 174
% 8.46/3.04  #BackRed      : 62
% 8.46/3.04  
% 8.46/3.04  #Partial instantiations: 0
% 8.46/3.04  #Strategies tried      : 1
% 8.46/3.04  
% 8.46/3.04  Timing (in seconds)
% 8.46/3.04  ----------------------
% 8.46/3.04  Preprocessing        : 0.34
% 8.46/3.04  Parsing              : 0.17
% 8.46/3.04  CNF conversion       : 0.03
% 8.46/3.04  Main loop            : 1.95
% 8.46/3.04  Inferencing          : 0.57
% 8.46/3.04  Reduction            : 0.69
% 8.46/3.04  Demodulation         : 0.50
% 8.46/3.04  BG Simplification    : 0.05
% 8.46/3.04  Subsumption          : 0.52
% 8.46/3.04  Abstraction          : 0.08
% 8.46/3.04  MUC search           : 0.00
% 8.46/3.04  Cooper               : 0.00
% 8.46/3.04  Total                : 2.31
% 8.46/3.04  Index Insertion      : 0.00
% 8.46/3.04  Index Deletion       : 0.00
% 8.46/3.04  Index Matching       : 0.00
% 8.46/3.04  BG Taut test         : 0.00
%------------------------------------------------------------------------------
