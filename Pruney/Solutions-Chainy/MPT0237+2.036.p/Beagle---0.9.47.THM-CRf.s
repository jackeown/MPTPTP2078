%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:49:49 EST 2020

% Result     : Theorem 2.80s
% Output     : CNFRefutation 2.80s
% Verified   : 
% Statistics : Number of formulae       :   71 ( 104 expanded)
%              Number of leaves         :   38 (  52 expanded)
%              Depth                    :    8
%              Number of atoms          :   66 ( 109 expanded)
%              Number of equality atoms :   45 (  84 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1

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

tff(f_57,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_59,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_49,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_41,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_55,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_67,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_83,axiom,(
    ! [A,B] : r1_tarski(k1_tarski(A),k2_tarski(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_zfmisc_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_65,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_81,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_93,axiom,(
    ! [A,B] :
      ( A != B
     => k5_xboole_0(k1_tarski(A),k1_tarski(B)) = k2_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_zfmisc_1)).

tff(f_88,axiom,(
    ! [A,B] :
      ( A != B
     => r1_xboole_0(k1_tarski(A),k1_tarski(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_zfmisc_1)).

tff(f_63,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_96,negated_conjecture,(
    ~ ! [A,B] : k3_tarski(k2_tarski(k1_tarski(A),k1_tarski(B))) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_zfmisc_1)).

tff(c_16,plain,(
    ! [A_14] : k4_xboole_0(A_14,k1_xboole_0) = A_14 ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_18,plain,(
    ! [A_15] : r1_xboole_0(A_15,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_8,plain,(
    ! [A_8] :
      ( r2_hidden('#skF_2'(A_8),A_8)
      | k1_xboole_0 = A_8 ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_194,plain,(
    ! [A_83,B_84,C_85] :
      ( ~ r1_xboole_0(A_83,B_84)
      | ~ r2_hidden(C_85,k3_xboole_0(A_83,B_84)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_221,plain,(
    ! [A_88,B_89] :
      ( ~ r1_xboole_0(A_88,B_89)
      | k3_xboole_0(A_88,B_89) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_8,c_194])).

tff(c_234,plain,(
    ! [A_90] : k3_xboole_0(A_90,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_18,c_221])).

tff(c_14,plain,(
    ! [A_12,B_13] : k5_xboole_0(A_12,k3_xboole_0(A_12,B_13)) = k4_xboole_0(A_12,B_13) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_239,plain,(
    ! [A_90] : k5_xboole_0(A_90,k1_xboole_0) = k4_xboole_0(A_90,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_234,c_14])).

tff(c_260,plain,(
    ! [A_90] : k5_xboole_0(A_90,k1_xboole_0) = A_90 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_239])).

tff(c_26,plain,(
    ! [A_20] : k2_tarski(A_20,A_20) = k1_tarski(A_20) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_70,plain,(
    ! [A_60,B_61] : r1_tarski(k1_tarski(A_60),k2_tarski(A_60,B_61)) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_73,plain,(
    ! [A_20] : r1_tarski(k1_tarski(A_20),k1_tarski(A_20)) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_70])).

tff(c_115,plain,(
    ! [A_69,B_70] :
      ( k4_xboole_0(A_69,B_70) = k1_xboole_0
      | ~ r1_tarski(A_69,B_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_126,plain,(
    ! [A_20] : k4_xboole_0(k1_tarski(A_20),k1_tarski(A_20)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_73,c_115])).

tff(c_320,plain,(
    ! [A_94,B_95] : k5_xboole_0(A_94,k4_xboole_0(B_95,A_94)) = k2_xboole_0(A_94,B_95) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_332,plain,(
    ! [A_20] : k2_xboole_0(k1_tarski(A_20),k1_tarski(A_20)) = k5_xboole_0(k1_tarski(A_20),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_126,c_320])).

tff(c_421,plain,(
    ! [A_102] : k2_xboole_0(k1_tarski(A_102),k1_tarski(A_102)) = k1_tarski(A_102) ),
    inference(demodulation,[status(thm),theory(equality)],[c_260,c_332])).

tff(c_135,plain,(
    ! [A_72,B_73] : k3_tarski(k2_tarski(A_72,B_73)) = k2_xboole_0(A_72,B_73) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_144,plain,(
    ! [A_20] : k3_tarski(k1_tarski(A_20)) = k2_xboole_0(A_20,A_20) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_135])).

tff(c_427,plain,(
    ! [A_102] : k3_tarski(k1_tarski(k1_tarski(A_102))) = k1_tarski(A_102) ),
    inference(superposition,[status(thm),theory(equality)],[c_421,c_144])).

tff(c_46,plain,(
    ! [A_54,B_55] :
      ( k5_xboole_0(k1_tarski(A_54),k1_tarski(B_55)) = k2_tarski(A_54,B_55)
      | B_55 = A_54 ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_173,plain,(
    ! [A_77,B_78] :
      ( r1_xboole_0(k1_tarski(A_77),k1_tarski(B_78))
      | B_78 = A_77 ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_20,plain,(
    ! [A_16,B_17] :
      ( k4_xboole_0(A_16,B_17) = A_16
      | ~ r1_xboole_0(A_16,B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_726,plain,(
    ! [A_143,B_144] :
      ( k4_xboole_0(k1_tarski(A_143),k1_tarski(B_144)) = k1_tarski(A_143)
      | B_144 = A_143 ) ),
    inference(resolution,[status(thm)],[c_173,c_20])).

tff(c_24,plain,(
    ! [A_18,B_19] : k5_xboole_0(A_18,k4_xboole_0(B_19,A_18)) = k2_xboole_0(A_18,B_19) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_941,plain,(
    ! [B_164,A_165] :
      ( k5_xboole_0(k1_tarski(B_164),k1_tarski(A_165)) = k2_xboole_0(k1_tarski(B_164),k1_tarski(A_165))
      | B_164 = A_165 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_726,c_24])).

tff(c_956,plain,(
    ! [A_166,B_167] :
      ( k2_xboole_0(k1_tarski(A_166),k1_tarski(B_167)) = k2_tarski(A_166,B_167)
      | B_167 = A_166
      | B_167 = A_166 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_941])).

tff(c_40,plain,(
    ! [A_48,B_49] : k3_tarski(k2_tarski(A_48,B_49)) = k2_xboole_0(A_48,B_49) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_48,plain,(
    k3_tarski(k2_tarski(k1_tarski('#skF_3'),k1_tarski('#skF_4'))) != k2_tarski('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_49,plain,(
    k2_xboole_0(k1_tarski('#skF_3'),k1_tarski('#skF_4')) != k2_tarski('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_48])).

tff(c_986,plain,(
    '#skF_3' = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_956,c_49])).

tff(c_992,plain,(
    k2_xboole_0(k1_tarski('#skF_4'),k1_tarski('#skF_4')) != k2_tarski('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_986,c_986,c_49])).

tff(c_995,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_427,c_144,c_26,c_992])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:41:49 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.80/1.59  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.80/1.59  
% 2.80/1.59  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.80/1.59  %$ r2_hidden > r1_xboole_0 > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 2.80/1.59  
% 2.80/1.59  %Foreground sorts:
% 2.80/1.59  
% 2.80/1.59  
% 2.80/1.59  %Background operators:
% 2.80/1.59  
% 2.80/1.59  
% 2.80/1.59  %Foreground operators:
% 2.80/1.59  tff('#skF_2', type, '#skF_2': $i > $i).
% 2.80/1.59  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.80/1.59  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.80/1.59  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.80/1.59  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.80/1.59  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.80/1.59  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.80/1.59  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.80/1.59  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.80/1.59  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.80/1.59  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.80/1.59  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.80/1.59  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.80/1.59  tff('#skF_3', type, '#skF_3': $i).
% 2.80/1.59  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.80/1.59  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.80/1.59  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.80/1.59  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.80/1.59  tff('#skF_4', type, '#skF_4': $i).
% 2.80/1.59  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.80/1.59  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.80/1.59  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.80/1.59  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.80/1.59  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.80/1.59  
% 2.80/1.61  tff(f_57, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 2.80/1.61  tff(f_59, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 2.80/1.61  tff(f_49, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 2.80/1.61  tff(f_41, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 2.80/1.61  tff(f_55, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 2.80/1.61  tff(f_67, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 2.80/1.61  tff(f_83, axiom, (![A, B]: r1_tarski(k1_tarski(A), k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_zfmisc_1)).
% 2.80/1.61  tff(f_53, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 2.80/1.61  tff(f_65, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_xboole_1)).
% 2.80/1.61  tff(f_81, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 2.80/1.61  tff(f_93, axiom, (![A, B]: (~(A = B) => (k5_xboole_0(k1_tarski(A), k1_tarski(B)) = k2_tarski(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_zfmisc_1)).
% 2.80/1.61  tff(f_88, axiom, (![A, B]: (~(A = B) => r1_xboole_0(k1_tarski(A), k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_zfmisc_1)).
% 2.80/1.61  tff(f_63, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_xboole_1)).
% 2.80/1.61  tff(f_96, negated_conjecture, ~(![A, B]: (k3_tarski(k2_tarski(k1_tarski(A), k1_tarski(B))) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t32_zfmisc_1)).
% 2.80/1.61  tff(c_16, plain, (![A_14]: (k4_xboole_0(A_14, k1_xboole_0)=A_14)), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.80/1.61  tff(c_18, plain, (![A_15]: (r1_xboole_0(A_15, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.80/1.61  tff(c_8, plain, (![A_8]: (r2_hidden('#skF_2'(A_8), A_8) | k1_xboole_0=A_8)), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.80/1.61  tff(c_194, plain, (![A_83, B_84, C_85]: (~r1_xboole_0(A_83, B_84) | ~r2_hidden(C_85, k3_xboole_0(A_83, B_84)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.80/1.61  tff(c_221, plain, (![A_88, B_89]: (~r1_xboole_0(A_88, B_89) | k3_xboole_0(A_88, B_89)=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_194])).
% 2.80/1.61  tff(c_234, plain, (![A_90]: (k3_xboole_0(A_90, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_18, c_221])).
% 2.80/1.61  tff(c_14, plain, (![A_12, B_13]: (k5_xboole_0(A_12, k3_xboole_0(A_12, B_13))=k4_xboole_0(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.80/1.61  tff(c_239, plain, (![A_90]: (k5_xboole_0(A_90, k1_xboole_0)=k4_xboole_0(A_90, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_234, c_14])).
% 2.80/1.61  tff(c_260, plain, (![A_90]: (k5_xboole_0(A_90, k1_xboole_0)=A_90)), inference(demodulation, [status(thm), theory('equality')], [c_16, c_239])).
% 2.80/1.61  tff(c_26, plain, (![A_20]: (k2_tarski(A_20, A_20)=k1_tarski(A_20))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.80/1.61  tff(c_70, plain, (![A_60, B_61]: (r1_tarski(k1_tarski(A_60), k2_tarski(A_60, B_61)))), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.80/1.61  tff(c_73, plain, (![A_20]: (r1_tarski(k1_tarski(A_20), k1_tarski(A_20)))), inference(superposition, [status(thm), theory('equality')], [c_26, c_70])).
% 2.80/1.61  tff(c_115, plain, (![A_69, B_70]: (k4_xboole_0(A_69, B_70)=k1_xboole_0 | ~r1_tarski(A_69, B_70))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.80/1.61  tff(c_126, plain, (![A_20]: (k4_xboole_0(k1_tarski(A_20), k1_tarski(A_20))=k1_xboole_0)), inference(resolution, [status(thm)], [c_73, c_115])).
% 2.80/1.61  tff(c_320, plain, (![A_94, B_95]: (k5_xboole_0(A_94, k4_xboole_0(B_95, A_94))=k2_xboole_0(A_94, B_95))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.80/1.61  tff(c_332, plain, (![A_20]: (k2_xboole_0(k1_tarski(A_20), k1_tarski(A_20))=k5_xboole_0(k1_tarski(A_20), k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_126, c_320])).
% 2.80/1.61  tff(c_421, plain, (![A_102]: (k2_xboole_0(k1_tarski(A_102), k1_tarski(A_102))=k1_tarski(A_102))), inference(demodulation, [status(thm), theory('equality')], [c_260, c_332])).
% 2.80/1.61  tff(c_135, plain, (![A_72, B_73]: (k3_tarski(k2_tarski(A_72, B_73))=k2_xboole_0(A_72, B_73))), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.80/1.61  tff(c_144, plain, (![A_20]: (k3_tarski(k1_tarski(A_20))=k2_xboole_0(A_20, A_20))), inference(superposition, [status(thm), theory('equality')], [c_26, c_135])).
% 2.80/1.61  tff(c_427, plain, (![A_102]: (k3_tarski(k1_tarski(k1_tarski(A_102)))=k1_tarski(A_102))), inference(superposition, [status(thm), theory('equality')], [c_421, c_144])).
% 2.80/1.61  tff(c_46, plain, (![A_54, B_55]: (k5_xboole_0(k1_tarski(A_54), k1_tarski(B_55))=k2_tarski(A_54, B_55) | B_55=A_54)), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.80/1.61  tff(c_173, plain, (![A_77, B_78]: (r1_xboole_0(k1_tarski(A_77), k1_tarski(B_78)) | B_78=A_77)), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.80/1.61  tff(c_20, plain, (![A_16, B_17]: (k4_xboole_0(A_16, B_17)=A_16 | ~r1_xboole_0(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.80/1.61  tff(c_726, plain, (![A_143, B_144]: (k4_xboole_0(k1_tarski(A_143), k1_tarski(B_144))=k1_tarski(A_143) | B_144=A_143)), inference(resolution, [status(thm)], [c_173, c_20])).
% 2.80/1.61  tff(c_24, plain, (![A_18, B_19]: (k5_xboole_0(A_18, k4_xboole_0(B_19, A_18))=k2_xboole_0(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.80/1.61  tff(c_941, plain, (![B_164, A_165]: (k5_xboole_0(k1_tarski(B_164), k1_tarski(A_165))=k2_xboole_0(k1_tarski(B_164), k1_tarski(A_165)) | B_164=A_165)), inference(superposition, [status(thm), theory('equality')], [c_726, c_24])).
% 2.80/1.61  tff(c_956, plain, (![A_166, B_167]: (k2_xboole_0(k1_tarski(A_166), k1_tarski(B_167))=k2_tarski(A_166, B_167) | B_167=A_166 | B_167=A_166)), inference(superposition, [status(thm), theory('equality')], [c_46, c_941])).
% 2.80/1.61  tff(c_40, plain, (![A_48, B_49]: (k3_tarski(k2_tarski(A_48, B_49))=k2_xboole_0(A_48, B_49))), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.80/1.61  tff(c_48, plain, (k3_tarski(k2_tarski(k1_tarski('#skF_3'), k1_tarski('#skF_4')))!=k2_tarski('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_96])).
% 2.80/1.61  tff(c_49, plain, (k2_xboole_0(k1_tarski('#skF_3'), k1_tarski('#skF_4'))!=k2_tarski('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_48])).
% 2.80/1.61  tff(c_986, plain, ('#skF_3'='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_956, c_49])).
% 2.80/1.61  tff(c_992, plain, (k2_xboole_0(k1_tarski('#skF_4'), k1_tarski('#skF_4'))!=k2_tarski('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_986, c_986, c_49])).
% 2.80/1.61  tff(c_995, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_427, c_144, c_26, c_992])).
% 2.80/1.61  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.80/1.61  
% 2.80/1.61  Inference rules
% 2.80/1.61  ----------------------
% 2.80/1.61  #Ref     : 0
% 2.80/1.61  #Sup     : 222
% 2.80/1.61  #Fact    : 0
% 2.80/1.61  #Define  : 0
% 2.80/1.61  #Split   : 0
% 2.80/1.61  #Chain   : 0
% 2.80/1.61  #Close   : 0
% 2.80/1.61  
% 2.80/1.61  Ordering : KBO
% 2.80/1.61  
% 2.80/1.61  Simplification rules
% 2.80/1.61  ----------------------
% 2.80/1.61  #Subsume      : 47
% 2.80/1.61  #Demod        : 85
% 2.80/1.61  #Tautology    : 136
% 2.80/1.61  #SimpNegUnit  : 10
% 2.80/1.61  #BackRed      : 1
% 2.80/1.61  
% 2.80/1.61  #Partial instantiations: 0
% 2.80/1.61  #Strategies tried      : 1
% 2.80/1.61  
% 2.80/1.61  Timing (in seconds)
% 2.80/1.61  ----------------------
% 2.80/1.61  Preprocessing        : 0.39
% 2.80/1.61  Parsing              : 0.21
% 2.80/1.61  CNF conversion       : 0.02
% 2.80/1.61  Main loop            : 0.35
% 2.80/1.61  Inferencing          : 0.14
% 2.80/1.61  Reduction            : 0.12
% 2.80/1.61  Demodulation         : 0.09
% 2.80/1.61  BG Simplification    : 0.02
% 2.80/1.61  Subsumption          : 0.05
% 2.80/1.61  Abstraction          : 0.02
% 2.80/1.61  MUC search           : 0.00
% 2.80/1.61  Cooper               : 0.00
% 2.80/1.61  Total                : 0.78
% 2.80/1.61  Index Insertion      : 0.00
% 2.80/1.61  Index Deletion       : 0.00
% 2.80/1.61  Index Matching       : 0.00
% 2.80/1.61  BG Taut test         : 0.00
%------------------------------------------------------------------------------
