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
% DateTime   : Thu Dec  3 09:51:14 EST 2020

% Result     : Theorem 25.83s
% Output     : CNFRefutation 25.97s
% Verified   : 
% Statistics : Number of formulae       :   91 ( 127 expanded)
%              Number of leaves         :   42 (  61 expanded)
%              Depth                    :   13
%              Number of atoms          :  109 ( 183 expanded)
%              Number of equality atoms :   38 (  53 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_xboole_0 > #skF_6 > #skF_11 > #skF_1 > #skF_4 > #skF_10 > #skF_5 > #skF_2 > #skF_8 > #skF_9 > #skF_3 > #skF_7

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_11',type,(
    '#skF_11': $i )).

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

tff('#skF_10',type,(
    '#skF_10': $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': ( $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(f_117,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( r2_hidden(A,B)
          & r2_hidden(C,B) )
       => k2_xboole_0(k2_tarski(A,C),B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_zfmisc_1)).

tff(f_86,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

tff(f_36,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_55,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_92,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_90,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ( C = k3_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

tff(f_64,axiom,(
    ! [A,B] :
      ( ! [C] :
          ( r2_hidden(C,A)
        <=> r2_hidden(C,B) )
     => A = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tarski)).

tff(f_57,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_84,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_110,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_tarski(A,B),C)
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).

tff(f_94,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_96,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_104,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(c_90,plain,(
    r2_hidden('#skF_9','#skF_10') ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_88,plain,(
    r2_hidden('#skF_11','#skF_10') ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_62,plain,(
    ! [A_31] : k2_xboole_0(A_31,k1_xboole_0) = A_31 ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_6,plain,(
    ! [A_3] :
      ( v1_xboole_0(A_3)
      | r2_hidden('#skF_1'(A_3),A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_434,plain,(
    ! [D_95,A_96,B_97] :
      ( r2_hidden(D_95,A_96)
      | ~ r2_hidden(D_95,k4_xboole_0(A_96,B_97)) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_2334,plain,(
    ! [A_242,B_243] :
      ( r2_hidden('#skF_1'(k4_xboole_0(A_242,B_243)),A_242)
      | v1_xboole_0(k4_xboole_0(A_242,B_243)) ) ),
    inference(resolution,[status(thm)],[c_6,c_434])).

tff(c_406,plain,(
    ! [D_89,B_90,A_91] :
      ( ~ r2_hidden(D_89,B_90)
      | ~ r2_hidden(D_89,k4_xboole_0(A_91,B_90)) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_426,plain,(
    ! [A_91,B_90] :
      ( ~ r2_hidden('#skF_1'(k4_xboole_0(A_91,B_90)),B_90)
      | v1_xboole_0(k4_xboole_0(A_91,B_90)) ) ),
    inference(resolution,[status(thm)],[c_6,c_406])).

tff(c_2397,plain,(
    ! [A_244] : v1_xboole_0(k4_xboole_0(A_244,A_244)) ),
    inference(resolution,[status(thm)],[c_2334,c_426])).

tff(c_66,plain,(
    ! [A_34] : r1_tarski(k1_xboole_0,A_34) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_168,plain,(
    ! [A_64,B_65] :
      ( k3_xboole_0(A_64,B_65) = A_64
      | ~ r1_tarski(A_64,B_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_172,plain,(
    ! [A_34] : k3_xboole_0(k1_xboole_0,A_34) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_66,c_168])).

tff(c_455,plain,(
    ! [D_98,B_99,A_100] :
      ( r2_hidden(D_98,B_99)
      | ~ r2_hidden(D_98,k3_xboole_0(A_100,B_99)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_472,plain,(
    ! [D_101,A_102] :
      ( r2_hidden(D_101,A_102)
      | ~ r2_hidden(D_101,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_172,c_455])).

tff(c_480,plain,(
    ! [A_102] :
      ( r2_hidden('#skF_1'(k1_xboole_0),A_102)
      | v1_xboole_0(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_6,c_472])).

tff(c_481,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_480])).

tff(c_890,plain,(
    ! [A_147,B_148] :
      ( r2_hidden('#skF_6'(A_147,B_148),B_148)
      | r2_hidden('#skF_7'(A_147,B_148),A_147)
      | B_148 = A_147 ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_4,plain,(
    ! [B_6,A_3] :
      ( ~ r2_hidden(B_6,A_3)
      | ~ v1_xboole_0(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_1101,plain,(
    ! [B_156,A_157] :
      ( ~ v1_xboole_0(B_156)
      | r2_hidden('#skF_7'(A_157,B_156),A_157)
      | B_156 = A_157 ) ),
    inference(resolution,[status(thm)],[c_890,c_4])).

tff(c_1137,plain,(
    ! [A_158,B_159] :
      ( ~ v1_xboole_0(A_158)
      | ~ v1_xboole_0(B_159)
      | B_159 = A_158 ) ),
    inference(resolution,[status(thm)],[c_1101,c_4])).

tff(c_1140,plain,(
    ! [B_159] :
      ( ~ v1_xboole_0(B_159)
      | k1_xboole_0 = B_159 ) ),
    inference(resolution,[status(thm)],[c_481,c_1137])).

tff(c_2439,plain,(
    ! [A_244] : k4_xboole_0(A_244,A_244) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2397,c_1140])).

tff(c_44,plain,(
    ! [A_19] : k3_xboole_0(A_19,A_19) = A_19 ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_214,plain,(
    ! [A_71,B_72] : k5_xboole_0(A_71,k3_xboole_0(A_71,B_72)) = k4_xboole_0(A_71,B_72) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_226,plain,(
    ! [A_19] : k5_xboole_0(A_19,A_19) = k4_xboole_0(A_19,A_19) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_214])).

tff(c_2444,plain,(
    ! [A_19] : k5_xboole_0(A_19,A_19) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2439,c_226])).

tff(c_699,plain,(
    ! [A_127,B_128,C_129] :
      ( r1_tarski(k2_tarski(A_127,B_128),C_129)
      | ~ r2_hidden(B_128,C_129)
      | ~ r2_hidden(A_127,C_129) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_64,plain,(
    ! [A_32,B_33] :
      ( k3_xboole_0(A_32,B_33) = A_32
      | ~ r1_tarski(A_32,B_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_14665,plain,(
    ! [A_694,B_695,C_696] :
      ( k3_xboole_0(k2_tarski(A_694,B_695),C_696) = k2_tarski(A_694,B_695)
      | ~ r2_hidden(B_695,C_696)
      | ~ r2_hidden(A_694,C_696) ) ),
    inference(resolution,[status(thm)],[c_699,c_64])).

tff(c_60,plain,(
    ! [A_29,B_30] : k5_xboole_0(A_29,k3_xboole_0(A_29,B_30)) = k4_xboole_0(A_29,B_30) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_14936,plain,(
    ! [A_694,B_695,C_696] :
      ( k5_xboole_0(k2_tarski(A_694,B_695),k2_tarski(A_694,B_695)) = k4_xboole_0(k2_tarski(A_694,B_695),C_696)
      | ~ r2_hidden(B_695,C_696)
      | ~ r2_hidden(A_694,C_696) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14665,c_60])).

tff(c_110696,plain,(
    ! [A_1872,B_1873,C_1874] :
      ( k4_xboole_0(k2_tarski(A_1872,B_1873),C_1874) = k1_xboole_0
      | ~ r2_hidden(B_1873,C_1874)
      | ~ r2_hidden(A_1872,C_1874) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2444,c_14936])).

tff(c_68,plain,(
    ! [A_35,B_36] : k2_xboole_0(A_35,k4_xboole_0(B_36,A_35)) = k2_xboole_0(A_35,B_36) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_111265,plain,(
    ! [C_1874,A_1872,B_1873] :
      ( k2_xboole_0(C_1874,k2_tarski(A_1872,B_1873)) = k2_xboole_0(C_1874,k1_xboole_0)
      | ~ r2_hidden(B_1873,C_1874)
      | ~ r2_hidden(A_1872,C_1874) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_110696,c_68])).

tff(c_116029,plain,(
    ! [C_1939,A_1940,B_1941] :
      ( k2_xboole_0(C_1939,k2_tarski(A_1940,B_1941)) = C_1939
      | ~ r2_hidden(B_1941,C_1939)
      | ~ r2_hidden(A_1940,C_1939) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_111265])).

tff(c_70,plain,(
    ! [B_38,A_37] : k2_tarski(B_38,A_37) = k2_tarski(A_37,B_38) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_190,plain,(
    ! [A_67,B_68] : k3_tarski(k2_tarski(A_67,B_68)) = k2_xboole_0(A_67,B_68) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_285,plain,(
    ! [A_80,B_81] : k3_tarski(k2_tarski(A_80,B_81)) = k2_xboole_0(B_81,A_80) ),
    inference(superposition,[status(thm),theory(equality)],[c_70,c_190])).

tff(c_78,plain,(
    ! [A_48,B_49] : k3_tarski(k2_tarski(A_48,B_49)) = k2_xboole_0(A_48,B_49) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_291,plain,(
    ! [B_81,A_80] : k2_xboole_0(B_81,A_80) = k2_xboole_0(A_80,B_81) ),
    inference(superposition,[status(thm),theory(equality)],[c_285,c_78])).

tff(c_86,plain,(
    k2_xboole_0(k2_tarski('#skF_9','#skF_11'),'#skF_10') != '#skF_10' ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_308,plain,(
    k2_xboole_0('#skF_10',k2_tarski('#skF_9','#skF_11')) != '#skF_10' ),
    inference(demodulation,[status(thm),theory(equality)],[c_291,c_86])).

tff(c_116091,plain,
    ( ~ r2_hidden('#skF_11','#skF_10')
    | ~ r2_hidden('#skF_9','#skF_10') ),
    inference(superposition,[status(thm),theory(equality)],[c_116029,c_308])).

tff(c_116176,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_88,c_116091])).

tff(c_116177,plain,(
    ! [A_102] : r2_hidden('#skF_1'(k1_xboole_0),A_102) ),
    inference(splitRight,[status(thm)],[c_480])).

tff(c_116179,plain,(
    ! [A_1942] : r2_hidden('#skF_1'(k1_xboole_0),A_1942) ),
    inference(splitRight,[status(thm)],[c_480])).

tff(c_28,plain,(
    ! [D_18,B_14,A_13] :
      ( ~ r2_hidden(D_18,B_14)
      | ~ r2_hidden(D_18,k4_xboole_0(A_13,B_14)) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_116194,plain,(
    ! [B_14] : ~ r2_hidden('#skF_1'(k1_xboole_0),B_14) ),
    inference(resolution,[status(thm)],[c_116179,c_28])).

tff(c_116213,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_116177,c_116194])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n010.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 18:01:14 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 25.83/17.06  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 25.83/17.07  
% 25.83/17.07  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 25.83/17.07  %$ r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_xboole_0 > #skF_6 > #skF_11 > #skF_1 > #skF_4 > #skF_10 > #skF_5 > #skF_2 > #skF_8 > #skF_9 > #skF_3 > #skF_7
% 25.83/17.07  
% 25.83/17.07  %Foreground sorts:
% 25.83/17.07  
% 25.83/17.07  
% 25.83/17.07  %Background operators:
% 25.83/17.07  
% 25.83/17.07  
% 25.83/17.07  %Foreground operators:
% 25.83/17.07  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 25.83/17.07  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 25.83/17.07  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 25.83/17.07  tff('#skF_11', type, '#skF_11': $i).
% 25.83/17.07  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 25.83/17.07  tff('#skF_1', type, '#skF_1': $i > $i).
% 25.83/17.07  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 25.83/17.07  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 25.83/17.07  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 25.83/17.07  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 25.83/17.07  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 25.83/17.07  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 25.83/17.07  tff('#skF_10', type, '#skF_10': $i).
% 25.83/17.07  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 25.83/17.07  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 25.83/17.07  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 25.83/17.07  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 25.83/17.07  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 25.83/17.07  tff('#skF_8', type, '#skF_8': ($i * $i) > $i).
% 25.83/17.07  tff('#skF_9', type, '#skF_9': $i).
% 25.83/17.07  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 25.83/17.07  tff(k3_tarski, type, k3_tarski: $i > $i).
% 25.83/17.07  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 25.83/17.07  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 25.83/17.07  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 25.83/17.07  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 25.83/17.07  tff('#skF_7', type, '#skF_7': ($i * $i) > $i).
% 25.83/17.07  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 25.83/17.07  
% 25.97/17.09  tff(f_117, negated_conjecture, ~(![A, B, C]: ((r2_hidden(A, B) & r2_hidden(C, B)) => (k2_xboole_0(k2_tarski(A, C), B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_zfmisc_1)).
% 25.97/17.09  tff(f_86, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 25.97/17.09  tff(f_36, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 25.97/17.09  tff(f_55, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 25.97/17.09  tff(f_92, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 25.97/17.09  tff(f_90, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 25.97/17.09  tff(f_45, axiom, (![A, B, C]: ((C = k3_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_xboole_0)).
% 25.97/17.09  tff(f_64, axiom, (![A, B]: ((![C]: (r2_hidden(C, A) <=> r2_hidden(C, B))) => (A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_tarski)).
% 25.97/17.09  tff(f_57, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 25.97/17.09  tff(f_84, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 25.97/17.09  tff(f_110, axiom, (![A, B, C]: (r1_tarski(k2_tarski(A, B), C) <=> (r2_hidden(A, C) & r2_hidden(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 25.97/17.09  tff(f_94, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 25.97/17.09  tff(f_96, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 25.97/17.09  tff(f_104, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 25.97/17.09  tff(c_90, plain, (r2_hidden('#skF_9', '#skF_10')), inference(cnfTransformation, [status(thm)], [f_117])).
% 25.97/17.09  tff(c_88, plain, (r2_hidden('#skF_11', '#skF_10')), inference(cnfTransformation, [status(thm)], [f_117])).
% 25.97/17.09  tff(c_62, plain, (![A_31]: (k2_xboole_0(A_31, k1_xboole_0)=A_31)), inference(cnfTransformation, [status(thm)], [f_86])).
% 25.97/17.09  tff(c_6, plain, (![A_3]: (v1_xboole_0(A_3) | r2_hidden('#skF_1'(A_3), A_3))), inference(cnfTransformation, [status(thm)], [f_36])).
% 25.97/17.09  tff(c_434, plain, (![D_95, A_96, B_97]: (r2_hidden(D_95, A_96) | ~r2_hidden(D_95, k4_xboole_0(A_96, B_97)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 25.97/17.09  tff(c_2334, plain, (![A_242, B_243]: (r2_hidden('#skF_1'(k4_xboole_0(A_242, B_243)), A_242) | v1_xboole_0(k4_xboole_0(A_242, B_243)))), inference(resolution, [status(thm)], [c_6, c_434])).
% 25.97/17.09  tff(c_406, plain, (![D_89, B_90, A_91]: (~r2_hidden(D_89, B_90) | ~r2_hidden(D_89, k4_xboole_0(A_91, B_90)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 25.97/17.09  tff(c_426, plain, (![A_91, B_90]: (~r2_hidden('#skF_1'(k4_xboole_0(A_91, B_90)), B_90) | v1_xboole_0(k4_xboole_0(A_91, B_90)))), inference(resolution, [status(thm)], [c_6, c_406])).
% 25.97/17.09  tff(c_2397, plain, (![A_244]: (v1_xboole_0(k4_xboole_0(A_244, A_244)))), inference(resolution, [status(thm)], [c_2334, c_426])).
% 25.97/17.09  tff(c_66, plain, (![A_34]: (r1_tarski(k1_xboole_0, A_34))), inference(cnfTransformation, [status(thm)], [f_92])).
% 25.97/17.09  tff(c_168, plain, (![A_64, B_65]: (k3_xboole_0(A_64, B_65)=A_64 | ~r1_tarski(A_64, B_65))), inference(cnfTransformation, [status(thm)], [f_90])).
% 25.97/17.09  tff(c_172, plain, (![A_34]: (k3_xboole_0(k1_xboole_0, A_34)=k1_xboole_0)), inference(resolution, [status(thm)], [c_66, c_168])).
% 25.97/17.09  tff(c_455, plain, (![D_98, B_99, A_100]: (r2_hidden(D_98, B_99) | ~r2_hidden(D_98, k3_xboole_0(A_100, B_99)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 25.97/17.09  tff(c_472, plain, (![D_101, A_102]: (r2_hidden(D_101, A_102) | ~r2_hidden(D_101, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_172, c_455])).
% 25.97/17.09  tff(c_480, plain, (![A_102]: (r2_hidden('#skF_1'(k1_xboole_0), A_102) | v1_xboole_0(k1_xboole_0))), inference(resolution, [status(thm)], [c_6, c_472])).
% 25.97/17.09  tff(c_481, plain, (v1_xboole_0(k1_xboole_0)), inference(splitLeft, [status(thm)], [c_480])).
% 25.97/17.09  tff(c_890, plain, (![A_147, B_148]: (r2_hidden('#skF_6'(A_147, B_148), B_148) | r2_hidden('#skF_7'(A_147, B_148), A_147) | B_148=A_147)), inference(cnfTransformation, [status(thm)], [f_64])).
% 25.97/17.09  tff(c_4, plain, (![B_6, A_3]: (~r2_hidden(B_6, A_3) | ~v1_xboole_0(A_3))), inference(cnfTransformation, [status(thm)], [f_36])).
% 25.97/17.09  tff(c_1101, plain, (![B_156, A_157]: (~v1_xboole_0(B_156) | r2_hidden('#skF_7'(A_157, B_156), A_157) | B_156=A_157)), inference(resolution, [status(thm)], [c_890, c_4])).
% 25.97/17.09  tff(c_1137, plain, (![A_158, B_159]: (~v1_xboole_0(A_158) | ~v1_xboole_0(B_159) | B_159=A_158)), inference(resolution, [status(thm)], [c_1101, c_4])).
% 25.97/17.09  tff(c_1140, plain, (![B_159]: (~v1_xboole_0(B_159) | k1_xboole_0=B_159)), inference(resolution, [status(thm)], [c_481, c_1137])).
% 25.97/17.09  tff(c_2439, plain, (![A_244]: (k4_xboole_0(A_244, A_244)=k1_xboole_0)), inference(resolution, [status(thm)], [c_2397, c_1140])).
% 25.97/17.09  tff(c_44, plain, (![A_19]: (k3_xboole_0(A_19, A_19)=A_19)), inference(cnfTransformation, [status(thm)], [f_57])).
% 25.97/17.09  tff(c_214, plain, (![A_71, B_72]: (k5_xboole_0(A_71, k3_xboole_0(A_71, B_72))=k4_xboole_0(A_71, B_72))), inference(cnfTransformation, [status(thm)], [f_84])).
% 25.97/17.09  tff(c_226, plain, (![A_19]: (k5_xboole_0(A_19, A_19)=k4_xboole_0(A_19, A_19))), inference(superposition, [status(thm), theory('equality')], [c_44, c_214])).
% 25.97/17.09  tff(c_2444, plain, (![A_19]: (k5_xboole_0(A_19, A_19)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_2439, c_226])).
% 25.97/17.09  tff(c_699, plain, (![A_127, B_128, C_129]: (r1_tarski(k2_tarski(A_127, B_128), C_129) | ~r2_hidden(B_128, C_129) | ~r2_hidden(A_127, C_129))), inference(cnfTransformation, [status(thm)], [f_110])).
% 25.97/17.09  tff(c_64, plain, (![A_32, B_33]: (k3_xboole_0(A_32, B_33)=A_32 | ~r1_tarski(A_32, B_33))), inference(cnfTransformation, [status(thm)], [f_90])).
% 25.97/17.09  tff(c_14665, plain, (![A_694, B_695, C_696]: (k3_xboole_0(k2_tarski(A_694, B_695), C_696)=k2_tarski(A_694, B_695) | ~r2_hidden(B_695, C_696) | ~r2_hidden(A_694, C_696))), inference(resolution, [status(thm)], [c_699, c_64])).
% 25.97/17.09  tff(c_60, plain, (![A_29, B_30]: (k5_xboole_0(A_29, k3_xboole_0(A_29, B_30))=k4_xboole_0(A_29, B_30))), inference(cnfTransformation, [status(thm)], [f_84])).
% 25.97/17.09  tff(c_14936, plain, (![A_694, B_695, C_696]: (k5_xboole_0(k2_tarski(A_694, B_695), k2_tarski(A_694, B_695))=k4_xboole_0(k2_tarski(A_694, B_695), C_696) | ~r2_hidden(B_695, C_696) | ~r2_hidden(A_694, C_696))), inference(superposition, [status(thm), theory('equality')], [c_14665, c_60])).
% 25.97/17.09  tff(c_110696, plain, (![A_1872, B_1873, C_1874]: (k4_xboole_0(k2_tarski(A_1872, B_1873), C_1874)=k1_xboole_0 | ~r2_hidden(B_1873, C_1874) | ~r2_hidden(A_1872, C_1874))), inference(demodulation, [status(thm), theory('equality')], [c_2444, c_14936])).
% 25.97/17.09  tff(c_68, plain, (![A_35, B_36]: (k2_xboole_0(A_35, k4_xboole_0(B_36, A_35))=k2_xboole_0(A_35, B_36))), inference(cnfTransformation, [status(thm)], [f_94])).
% 25.97/17.09  tff(c_111265, plain, (![C_1874, A_1872, B_1873]: (k2_xboole_0(C_1874, k2_tarski(A_1872, B_1873))=k2_xboole_0(C_1874, k1_xboole_0) | ~r2_hidden(B_1873, C_1874) | ~r2_hidden(A_1872, C_1874))), inference(superposition, [status(thm), theory('equality')], [c_110696, c_68])).
% 25.97/17.09  tff(c_116029, plain, (![C_1939, A_1940, B_1941]: (k2_xboole_0(C_1939, k2_tarski(A_1940, B_1941))=C_1939 | ~r2_hidden(B_1941, C_1939) | ~r2_hidden(A_1940, C_1939))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_111265])).
% 25.97/17.09  tff(c_70, plain, (![B_38, A_37]: (k2_tarski(B_38, A_37)=k2_tarski(A_37, B_38))), inference(cnfTransformation, [status(thm)], [f_96])).
% 25.97/17.09  tff(c_190, plain, (![A_67, B_68]: (k3_tarski(k2_tarski(A_67, B_68))=k2_xboole_0(A_67, B_68))), inference(cnfTransformation, [status(thm)], [f_104])).
% 25.97/17.09  tff(c_285, plain, (![A_80, B_81]: (k3_tarski(k2_tarski(A_80, B_81))=k2_xboole_0(B_81, A_80))), inference(superposition, [status(thm), theory('equality')], [c_70, c_190])).
% 25.97/17.09  tff(c_78, plain, (![A_48, B_49]: (k3_tarski(k2_tarski(A_48, B_49))=k2_xboole_0(A_48, B_49))), inference(cnfTransformation, [status(thm)], [f_104])).
% 25.97/17.09  tff(c_291, plain, (![B_81, A_80]: (k2_xboole_0(B_81, A_80)=k2_xboole_0(A_80, B_81))), inference(superposition, [status(thm), theory('equality')], [c_285, c_78])).
% 25.97/17.09  tff(c_86, plain, (k2_xboole_0(k2_tarski('#skF_9', '#skF_11'), '#skF_10')!='#skF_10'), inference(cnfTransformation, [status(thm)], [f_117])).
% 25.97/17.09  tff(c_308, plain, (k2_xboole_0('#skF_10', k2_tarski('#skF_9', '#skF_11'))!='#skF_10'), inference(demodulation, [status(thm), theory('equality')], [c_291, c_86])).
% 25.97/17.09  tff(c_116091, plain, (~r2_hidden('#skF_11', '#skF_10') | ~r2_hidden('#skF_9', '#skF_10')), inference(superposition, [status(thm), theory('equality')], [c_116029, c_308])).
% 25.97/17.09  tff(c_116176, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_90, c_88, c_116091])).
% 25.97/17.09  tff(c_116177, plain, (![A_102]: (r2_hidden('#skF_1'(k1_xboole_0), A_102))), inference(splitRight, [status(thm)], [c_480])).
% 25.97/17.09  tff(c_116179, plain, (![A_1942]: (r2_hidden('#skF_1'(k1_xboole_0), A_1942))), inference(splitRight, [status(thm)], [c_480])).
% 25.97/17.09  tff(c_28, plain, (![D_18, B_14, A_13]: (~r2_hidden(D_18, B_14) | ~r2_hidden(D_18, k4_xboole_0(A_13, B_14)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 25.97/17.09  tff(c_116194, plain, (![B_14]: (~r2_hidden('#skF_1'(k1_xboole_0), B_14))), inference(resolution, [status(thm)], [c_116179, c_28])).
% 25.97/17.09  tff(c_116213, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_116177, c_116194])).
% 25.97/17.09  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 25.97/17.09  
% 25.97/17.09  Inference rules
% 25.97/17.09  ----------------------
% 25.97/17.09  #Ref     : 0
% 25.97/17.09  #Sup     : 31615
% 25.97/17.09  #Fact    : 0
% 25.97/17.09  #Define  : 0
% 25.97/17.09  #Split   : 10
% 25.97/17.09  #Chain   : 0
% 25.97/17.09  #Close   : 0
% 25.97/17.09  
% 25.97/17.09  Ordering : KBO
% 25.97/17.09  
% 25.97/17.09  Simplification rules
% 25.97/17.09  ----------------------
% 25.97/17.09  #Subsume      : 10718
% 25.97/17.09  #Demod        : 20627
% 25.97/17.09  #Tautology    : 11651
% 25.97/17.09  #SimpNegUnit  : 75
% 25.97/17.09  #BackRed      : 46
% 25.97/17.09  
% 25.97/17.09  #Partial instantiations: 0
% 25.97/17.09  #Strategies tried      : 1
% 25.97/17.09  
% 25.97/17.09  Timing (in seconds)
% 25.97/17.09  ----------------------
% 25.97/17.09  Preprocessing        : 0.39
% 25.97/17.09  Parsing              : 0.19
% 25.97/17.09  CNF conversion       : 0.04
% 25.97/17.09  Main loop            : 15.90
% 25.97/17.09  Inferencing          : 2.45
% 25.97/17.09  Reduction            : 3.78
% 25.97/17.09  Demodulation         : 2.86
% 25.97/17.09  BG Simplification    : 0.27
% 25.97/17.09  Subsumption          : 8.67
% 25.97/17.09  Abstraction          : 0.41
% 25.97/17.09  MUC search           : 0.00
% 25.97/17.09  Cooper               : 0.00
% 25.97/17.09  Total                : 16.33
% 25.97/17.09  Index Insertion      : 0.00
% 25.97/17.09  Index Deletion       : 0.00
% 25.97/17.09  Index Matching       : 0.00
% 25.97/17.09  BG Taut test         : 0.00
%------------------------------------------------------------------------------
