%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:52:09 EST 2020

% Result     : Theorem 4.41s
% Output     : CNFRefutation 4.74s
% Verified   : 
% Statistics : Number of formulae       :   75 ( 139 expanded)
%              Number of leaves         :   34 (  60 expanded)
%              Depth                    :   11
%              Number of atoms          :   90 ( 191 expanded)
%              Number of equality atoms :   29 (  65 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k6_enumset1 > k5_enumset1 > k3_enumset1 > k2_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(f_99,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( r1_xboole_0(k2_tarski(A,B),C)
          & r2_hidden(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_zfmisc_1)).

tff(f_88,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => k3_xboole_0(B,k1_tarski(A)) = k1_tarski(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_zfmisc_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k3_xboole_0(B,C))
     => r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_xboole_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_xboole_1)).

tff(f_37,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

tff(f_59,axiom,(
    ! [A,B] : r1_xboole_0(k3_xboole_0(A,B),k4_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t89_xboole_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ~ ( ~ r1_xboole_0(A,B)
        & r1_xboole_0(k3_xboole_0(A,B),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_xboole_1)).

tff(f_93,axiom,(
    ! [A,B] :
      ~ ( r1_xboole_0(k1_tarski(A),B)
        & r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t54_zfmisc_1)).

tff(f_43,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_84,axiom,(
    ! [A,B] :
      ( k3_xboole_0(A,k1_tarski(B)) = k1_tarski(B)
     => r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_zfmisc_1)).

tff(f_76,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),B) = k1_tarski(A)
    <=> ~ r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l33_zfmisc_1)).

tff(f_80,axiom,(
    ! [A,B] : k3_xboole_0(k1_tarski(A),k2_tarski(A,B)) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_zfmisc_1)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(A,C)
        & r1_xboole_0(B,C) )
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_xboole_1)).

tff(c_50,plain,(
    r2_hidden('#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_541,plain,(
    ! [B_96,A_97] :
      ( k3_xboole_0(B_96,k1_tarski(A_97)) = k1_tarski(A_97)
      | ~ r2_hidden(A_97,B_96) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_284,plain,(
    ! [A_82,B_83,C_84] :
      ( r1_tarski(A_82,B_83)
      | ~ r1_tarski(A_82,k3_xboole_0(B_83,C_84)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_303,plain,(
    ! [B_83,C_84] : r1_tarski(k3_xboole_0(B_83,C_84),B_83) ),
    inference(resolution,[status(thm)],[c_6,c_284])).

tff(c_551,plain,(
    ! [A_97,B_96] :
      ( r1_tarski(k1_tarski(A_97),B_96)
      | ~ r2_hidden(A_97,B_96) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_541,c_303])).

tff(c_69,plain,(
    ! [A_63,B_64] :
      ( k4_xboole_0(A_63,B_64) = k1_xboole_0
      | ~ r1_tarski(A_63,B_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_90,plain,(
    ! [B_67] : k4_xboole_0(B_67,B_67) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_6,c_69])).

tff(c_10,plain,(
    ! [A_6] : k3_xboole_0(A_6,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_62,plain,(
    ! [A_56,B_57] : r1_xboole_0(k3_xboole_0(A_56,B_57),k4_xboole_0(A_56,B_57)) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_65,plain,(
    ! [A_6] : r1_xboole_0(k1_xboole_0,k4_xboole_0(A_6,k1_xboole_0)) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_62])).

tff(c_95,plain,(
    r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_90,c_65])).

tff(c_108,plain,(
    ! [A_69,B_70] :
      ( ~ r1_xboole_0(k3_xboole_0(A_69,B_70),B_70)
      | r1_xboole_0(A_69,B_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_118,plain,(
    ! [A_6] :
      ( ~ r1_xboole_0(k1_xboole_0,k1_xboole_0)
      | r1_xboole_0(A_6,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_108])).

tff(c_125,plain,(
    ! [A_71] : r1_xboole_0(A_71,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_95,c_118])).

tff(c_48,plain,(
    ! [A_52,B_53] :
      ( ~ r2_hidden(A_52,B_53)
      | ~ r1_xboole_0(k1_tarski(A_52),B_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_136,plain,(
    ! [A_52] : ~ r2_hidden(A_52,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_125,c_48])).

tff(c_16,plain,(
    ! [A_9,B_10] : k4_xboole_0(A_9,k4_xboole_0(A_9,B_10)) = k3_xboole_0(A_9,B_10) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_328,plain,(
    ! [B_87,C_88] : r1_tarski(k3_xboole_0(B_87,C_88),B_87) ),
    inference(resolution,[status(thm)],[c_6,c_284])).

tff(c_348,plain,(
    ! [A_89] : r1_tarski(k1_xboole_0,A_89) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_328])).

tff(c_14,plain,(
    ! [A_7,B_8] :
      ( k4_xboole_0(A_7,B_8) = k1_xboole_0
      | ~ r1_tarski(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_359,plain,(
    ! [A_90] : k4_xboole_0(k1_xboole_0,A_90) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_348,c_14])).

tff(c_410,plain,(
    ! [B_10] : k3_xboole_0(k1_xboole_0,B_10) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_359])).

tff(c_678,plain,(
    ! [B_103,A_104] :
      ( r2_hidden(B_103,A_104)
      | k3_xboole_0(A_104,k1_tarski(B_103)) != k1_tarski(B_103) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_685,plain,(
    ! [B_103] :
      ( r2_hidden(B_103,k1_xboole_0)
      | k1_tarski(B_103) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_410,c_678])).

tff(c_691,plain,(
    ! [B_103] : k1_tarski(B_103) != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_136,c_685])).

tff(c_77,plain,(
    ! [B_2] : k4_xboole_0(B_2,B_2) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_6,c_69])).

tff(c_852,plain,(
    ! [A_113,B_114] :
      ( k4_xboole_0(k1_tarski(A_113),B_114) = k1_tarski(A_113)
      | r2_hidden(A_113,B_114) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_885,plain,(
    ! [A_113,B_114] :
      ( k4_xboole_0(k1_tarski(A_113),k1_tarski(A_113)) = k3_xboole_0(k1_tarski(A_113),B_114)
      | r2_hidden(A_113,B_114) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_852,c_16])).

tff(c_1280,plain,(
    ! [A_140,B_141] :
      ( k3_xboole_0(k1_tarski(A_140),B_141) = k1_xboole_0
      | r2_hidden(A_140,B_141) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_77,c_885])).

tff(c_42,plain,(
    ! [A_46,B_47] : k3_xboole_0(k1_tarski(A_46),k2_tarski(A_46,B_47)) = k1_tarski(A_46) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_1329,plain,(
    ! [A_140,B_47] :
      ( k1_tarski(A_140) = k1_xboole_0
      | r2_hidden(A_140,k2_tarski(A_140,B_47)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1280,c_42])).

tff(c_1367,plain,(
    ! [A_140,B_47] : r2_hidden(A_140,k2_tarski(A_140,B_47)) ),
    inference(negUnitSimplification,[status(thm)],[c_691,c_1329])).

tff(c_52,plain,(
    r1_xboole_0(k2_tarski('#skF_1','#skF_2'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_1033,plain,(
    ! [A_123,B_124,C_125] :
      ( k1_xboole_0 = A_123
      | ~ r1_xboole_0(B_124,C_125)
      | ~ r1_tarski(A_123,C_125)
      | ~ r1_tarski(A_123,B_124) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_1376,plain,(
    ! [A_142] :
      ( k1_xboole_0 = A_142
      | ~ r1_tarski(A_142,'#skF_3')
      | ~ r1_tarski(A_142,k2_tarski('#skF_1','#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_52,c_1033])).

tff(c_1392,plain,(
    ! [A_97] :
      ( k1_tarski(A_97) = k1_xboole_0
      | ~ r1_tarski(k1_tarski(A_97),'#skF_3')
      | ~ r2_hidden(A_97,k2_tarski('#skF_1','#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_551,c_1376])).

tff(c_3880,plain,(
    ! [A_239] :
      ( ~ r1_tarski(k1_tarski(A_239),'#skF_3')
      | ~ r2_hidden(A_239,k2_tarski('#skF_1','#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_691,c_1392])).

tff(c_3885,plain,(
    ~ r1_tarski(k1_tarski('#skF_1'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_1367,c_3880])).

tff(c_3891,plain,(
    ~ r2_hidden('#skF_1','#skF_3') ),
    inference(resolution,[status(thm)],[c_551,c_3885])).

tff(c_3899,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_3891])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n006.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 19:36:52 EST 2020
% 0.12/0.35  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.41/1.83  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.64/1.83  
% 4.64/1.83  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.64/1.84  %$ r2_hidden > r1_xboole_0 > r1_tarski > k6_enumset1 > k5_enumset1 > k3_enumset1 > k2_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 4.64/1.84  
% 4.64/1.84  %Foreground sorts:
% 4.64/1.84  
% 4.64/1.84  
% 4.64/1.84  %Background operators:
% 4.64/1.84  
% 4.64/1.84  
% 4.64/1.84  %Foreground operators:
% 4.64/1.84  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.64/1.84  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.64/1.84  tff(k1_tarski, type, k1_tarski: $i > $i).
% 4.64/1.84  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.64/1.84  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.64/1.84  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 4.64/1.84  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 4.64/1.84  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.64/1.84  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 4.64/1.84  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.64/1.84  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 4.64/1.84  tff('#skF_2', type, '#skF_2': $i).
% 4.64/1.84  tff('#skF_3', type, '#skF_3': $i).
% 4.64/1.84  tff('#skF_1', type, '#skF_1': $i).
% 4.64/1.84  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 4.64/1.84  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.64/1.84  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.64/1.84  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.64/1.84  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.64/1.84  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 4.64/1.84  
% 4.64/1.85  tff(f_99, negated_conjecture, ~(![A, B, C]: ~(r1_xboole_0(k2_tarski(A, B), C) & r2_hidden(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_zfmisc_1)).
% 4.64/1.85  tff(f_88, axiom, (![A, B]: (r2_hidden(A, B) => (k3_xboole_0(B, k1_tarski(A)) = k1_tarski(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_zfmisc_1)).
% 4.64/1.85  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 4.64/1.85  tff(f_35, axiom, (![A, B, C]: (r1_tarski(A, k3_xboole_0(B, C)) => r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t18_xboole_1)).
% 4.64/1.85  tff(f_41, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t37_xboole_1)).
% 4.64/1.85  tff(f_37, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 4.64/1.85  tff(f_59, axiom, (![A, B]: r1_xboole_0(k3_xboole_0(A, B), k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t89_xboole_1)).
% 4.64/1.85  tff(f_57, axiom, (![A, B]: ~(~r1_xboole_0(A, B) & r1_xboole_0(k3_xboole_0(A, B), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t75_xboole_1)).
% 4.64/1.85  tff(f_93, axiom, (![A, B]: ~(r1_xboole_0(k1_tarski(A), B) & r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t54_zfmisc_1)).
% 4.64/1.85  tff(f_43, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 4.64/1.85  tff(f_84, axiom, (![A, B]: ((k3_xboole_0(A, k1_tarski(B)) = k1_tarski(B)) => r2_hidden(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t51_zfmisc_1)).
% 4.64/1.85  tff(f_76, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), B) = k1_tarski(A)) <=> ~r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l33_zfmisc_1)).
% 4.64/1.85  tff(f_80, axiom, (![A, B]: (k3_xboole_0(k1_tarski(A), k2_tarski(A, B)) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t19_zfmisc_1)).
% 4.64/1.85  tff(f_51, axiom, (![A, B, C]: (((r1_tarski(A, B) & r1_tarski(A, C)) & r1_xboole_0(B, C)) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t67_xboole_1)).
% 4.64/1.85  tff(c_50, plain, (r2_hidden('#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_99])).
% 4.64/1.85  tff(c_541, plain, (![B_96, A_97]: (k3_xboole_0(B_96, k1_tarski(A_97))=k1_tarski(A_97) | ~r2_hidden(A_97, B_96))), inference(cnfTransformation, [status(thm)], [f_88])).
% 4.64/1.85  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.64/1.85  tff(c_284, plain, (![A_82, B_83, C_84]: (r1_tarski(A_82, B_83) | ~r1_tarski(A_82, k3_xboole_0(B_83, C_84)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.64/1.85  tff(c_303, plain, (![B_83, C_84]: (r1_tarski(k3_xboole_0(B_83, C_84), B_83))), inference(resolution, [status(thm)], [c_6, c_284])).
% 4.64/1.85  tff(c_551, plain, (![A_97, B_96]: (r1_tarski(k1_tarski(A_97), B_96) | ~r2_hidden(A_97, B_96))), inference(superposition, [status(thm), theory('equality')], [c_541, c_303])).
% 4.64/1.85  tff(c_69, plain, (![A_63, B_64]: (k4_xboole_0(A_63, B_64)=k1_xboole_0 | ~r1_tarski(A_63, B_64))), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.64/1.85  tff(c_90, plain, (![B_67]: (k4_xboole_0(B_67, B_67)=k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_69])).
% 4.64/1.85  tff(c_10, plain, (![A_6]: (k3_xboole_0(A_6, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.64/1.85  tff(c_62, plain, (![A_56, B_57]: (r1_xboole_0(k3_xboole_0(A_56, B_57), k4_xboole_0(A_56, B_57)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 4.64/1.85  tff(c_65, plain, (![A_6]: (r1_xboole_0(k1_xboole_0, k4_xboole_0(A_6, k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_62])).
% 4.64/1.85  tff(c_95, plain, (r1_xboole_0(k1_xboole_0, k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_90, c_65])).
% 4.64/1.85  tff(c_108, plain, (![A_69, B_70]: (~r1_xboole_0(k3_xboole_0(A_69, B_70), B_70) | r1_xboole_0(A_69, B_70))), inference(cnfTransformation, [status(thm)], [f_57])).
% 4.64/1.85  tff(c_118, plain, (![A_6]: (~r1_xboole_0(k1_xboole_0, k1_xboole_0) | r1_xboole_0(A_6, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_10, c_108])).
% 4.64/1.85  tff(c_125, plain, (![A_71]: (r1_xboole_0(A_71, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_95, c_118])).
% 4.64/1.85  tff(c_48, plain, (![A_52, B_53]: (~r2_hidden(A_52, B_53) | ~r1_xboole_0(k1_tarski(A_52), B_53))), inference(cnfTransformation, [status(thm)], [f_93])).
% 4.64/1.85  tff(c_136, plain, (![A_52]: (~r2_hidden(A_52, k1_xboole_0))), inference(resolution, [status(thm)], [c_125, c_48])).
% 4.64/1.85  tff(c_16, plain, (![A_9, B_10]: (k4_xboole_0(A_9, k4_xboole_0(A_9, B_10))=k3_xboole_0(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.64/1.85  tff(c_328, plain, (![B_87, C_88]: (r1_tarski(k3_xboole_0(B_87, C_88), B_87))), inference(resolution, [status(thm)], [c_6, c_284])).
% 4.64/1.85  tff(c_348, plain, (![A_89]: (r1_tarski(k1_xboole_0, A_89))), inference(superposition, [status(thm), theory('equality')], [c_10, c_328])).
% 4.64/1.85  tff(c_14, plain, (![A_7, B_8]: (k4_xboole_0(A_7, B_8)=k1_xboole_0 | ~r1_tarski(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.64/1.85  tff(c_359, plain, (![A_90]: (k4_xboole_0(k1_xboole_0, A_90)=k1_xboole_0)), inference(resolution, [status(thm)], [c_348, c_14])).
% 4.64/1.85  tff(c_410, plain, (![B_10]: (k3_xboole_0(k1_xboole_0, B_10)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_16, c_359])).
% 4.64/1.85  tff(c_678, plain, (![B_103, A_104]: (r2_hidden(B_103, A_104) | k3_xboole_0(A_104, k1_tarski(B_103))!=k1_tarski(B_103))), inference(cnfTransformation, [status(thm)], [f_84])).
% 4.64/1.85  tff(c_685, plain, (![B_103]: (r2_hidden(B_103, k1_xboole_0) | k1_tarski(B_103)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_410, c_678])).
% 4.64/1.85  tff(c_691, plain, (![B_103]: (k1_tarski(B_103)!=k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_136, c_685])).
% 4.64/1.85  tff(c_77, plain, (![B_2]: (k4_xboole_0(B_2, B_2)=k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_69])).
% 4.64/1.85  tff(c_852, plain, (![A_113, B_114]: (k4_xboole_0(k1_tarski(A_113), B_114)=k1_tarski(A_113) | r2_hidden(A_113, B_114))), inference(cnfTransformation, [status(thm)], [f_76])).
% 4.64/1.85  tff(c_885, plain, (![A_113, B_114]: (k4_xboole_0(k1_tarski(A_113), k1_tarski(A_113))=k3_xboole_0(k1_tarski(A_113), B_114) | r2_hidden(A_113, B_114))), inference(superposition, [status(thm), theory('equality')], [c_852, c_16])).
% 4.64/1.85  tff(c_1280, plain, (![A_140, B_141]: (k3_xboole_0(k1_tarski(A_140), B_141)=k1_xboole_0 | r2_hidden(A_140, B_141))), inference(demodulation, [status(thm), theory('equality')], [c_77, c_885])).
% 4.64/1.85  tff(c_42, plain, (![A_46, B_47]: (k3_xboole_0(k1_tarski(A_46), k2_tarski(A_46, B_47))=k1_tarski(A_46))), inference(cnfTransformation, [status(thm)], [f_80])).
% 4.64/1.85  tff(c_1329, plain, (![A_140, B_47]: (k1_tarski(A_140)=k1_xboole_0 | r2_hidden(A_140, k2_tarski(A_140, B_47)))), inference(superposition, [status(thm), theory('equality')], [c_1280, c_42])).
% 4.64/1.85  tff(c_1367, plain, (![A_140, B_47]: (r2_hidden(A_140, k2_tarski(A_140, B_47)))), inference(negUnitSimplification, [status(thm)], [c_691, c_1329])).
% 4.64/1.85  tff(c_52, plain, (r1_xboole_0(k2_tarski('#skF_1', '#skF_2'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_99])).
% 4.64/1.85  tff(c_1033, plain, (![A_123, B_124, C_125]: (k1_xboole_0=A_123 | ~r1_xboole_0(B_124, C_125) | ~r1_tarski(A_123, C_125) | ~r1_tarski(A_123, B_124))), inference(cnfTransformation, [status(thm)], [f_51])).
% 4.64/1.85  tff(c_1376, plain, (![A_142]: (k1_xboole_0=A_142 | ~r1_tarski(A_142, '#skF_3') | ~r1_tarski(A_142, k2_tarski('#skF_1', '#skF_2')))), inference(resolution, [status(thm)], [c_52, c_1033])).
% 4.64/1.85  tff(c_1392, plain, (![A_97]: (k1_tarski(A_97)=k1_xboole_0 | ~r1_tarski(k1_tarski(A_97), '#skF_3') | ~r2_hidden(A_97, k2_tarski('#skF_1', '#skF_2')))), inference(resolution, [status(thm)], [c_551, c_1376])).
% 4.64/1.85  tff(c_3880, plain, (![A_239]: (~r1_tarski(k1_tarski(A_239), '#skF_3') | ~r2_hidden(A_239, k2_tarski('#skF_1', '#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_691, c_1392])).
% 4.64/1.85  tff(c_3885, plain, (~r1_tarski(k1_tarski('#skF_1'), '#skF_3')), inference(resolution, [status(thm)], [c_1367, c_3880])).
% 4.74/1.85  tff(c_3891, plain, (~r2_hidden('#skF_1', '#skF_3')), inference(resolution, [status(thm)], [c_551, c_3885])).
% 4.74/1.85  tff(c_3899, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_50, c_3891])).
% 4.74/1.85  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.74/1.85  
% 4.74/1.85  Inference rules
% 4.74/1.85  ----------------------
% 4.74/1.85  #Ref     : 2
% 4.74/1.85  #Sup     : 856
% 4.74/1.85  #Fact    : 0
% 4.74/1.85  #Define  : 0
% 4.74/1.85  #Split   : 1
% 4.74/1.85  #Chain   : 0
% 4.74/1.85  #Close   : 0
% 4.74/1.85  
% 4.74/1.85  Ordering : KBO
% 4.74/1.85  
% 4.74/1.85  Simplification rules
% 4.74/1.85  ----------------------
% 4.74/1.85  #Subsume      : 190
% 4.74/1.85  #Demod        : 594
% 4.74/1.85  #Tautology    : 487
% 4.74/1.85  #SimpNegUnit  : 53
% 4.74/1.85  #BackRed      : 19
% 4.74/1.85  
% 4.74/1.85  #Partial instantiations: 0
% 4.74/1.85  #Strategies tried      : 1
% 4.74/1.85  
% 4.74/1.85  Timing (in seconds)
% 4.74/1.85  ----------------------
% 4.74/1.85  Preprocessing        : 0.35
% 4.74/1.85  Parsing              : 0.18
% 4.74/1.85  CNF conversion       : 0.02
% 4.74/1.85  Main loop            : 0.74
% 4.74/1.85  Inferencing          : 0.26
% 4.74/1.85  Reduction            : 0.28
% 4.74/1.85  Demodulation         : 0.21
% 4.74/1.86  BG Simplification    : 0.03
% 4.74/1.86  Subsumption          : 0.12
% 4.74/1.86  Abstraction          : 0.04
% 4.74/1.86  MUC search           : 0.00
% 4.74/1.86  Cooper               : 0.00
% 4.74/1.86  Total                : 1.12
% 4.74/1.86  Index Insertion      : 0.00
% 4.74/1.86  Index Deletion       : 0.00
% 4.74/1.86  Index Matching       : 0.00
% 4.74/1.86  BG Taut test         : 0.00
%------------------------------------------------------------------------------
