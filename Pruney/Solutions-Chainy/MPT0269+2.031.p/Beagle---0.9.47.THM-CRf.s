%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:52:48 EST 2020

% Result     : Theorem 11.32s
% Output     : CNFRefutation 11.46s
% Verified   : 
% Statistics : Number of formulae       :   79 ( 131 expanded)
%              Number of leaves         :   31 (  57 expanded)
%              Depth                    :   13
%              Number of atoms          :   86 ( 166 expanded)
%              Number of equality atoms :   58 ( 108 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

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

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_82,negated_conjecture,(
    ~ ! [A,B] :
        ~ ( k4_xboole_0(A,k1_tarski(B)) = k1_xboole_0
          & A != k1_xboole_0
          & A != k1_tarski(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_zfmisc_1)).

tff(f_72,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,k1_tarski(B)) = A
    <=> ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_zfmisc_1)).

tff(f_53,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_55,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_43,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_61,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_51,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_49,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_57,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k2_xboole_0(k4_xboole_0(A,B),k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_xboole_0)).

tff(f_59,axiom,(
    ! [A,B,C] : k4_xboole_0(A,k4_xboole_0(B,C)) = k2_xboole_0(k4_xboole_0(A,B),k3_xboole_0(A,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_xboole_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

tff(c_58,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_484,plain,(
    ! [A_66,B_67] :
      ( k4_xboole_0(A_66,k1_tarski(B_67)) = A_66
      | r2_hidden(B_67,A_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_60,plain,(
    k4_xboole_0('#skF_3',k1_tarski('#skF_4')) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_514,plain,
    ( k1_xboole_0 = '#skF_3'
    | r2_hidden('#skF_4','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_484,c_60])).

tff(c_539,plain,(
    r2_hidden('#skF_4','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_514])).

tff(c_36,plain,(
    ! [A_16,B_17] : r1_tarski(k4_xboole_0(A_16,B_17),A_16) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_110,plain,(
    ! [A_44,B_45] :
      ( k4_xboole_0(A_44,B_45) = k1_xboole_0
      | ~ r1_tarski(A_44,B_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_125,plain,(
    ! [A_16,B_17] : k4_xboole_0(k4_xboole_0(A_16,B_17),A_16) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_36,c_110])).

tff(c_31818,plain,(
    ! [B_455,B_456] :
      ( k4_xboole_0(k1_tarski(B_455),B_456) = k1_xboole_0
      | r2_hidden(B_455,k4_xboole_0(k1_tarski(B_455),B_456)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_125,c_484])).

tff(c_38,plain,(
    ! [A_18] : k4_xboole_0(A_18,k1_xboole_0) = A_18 ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_26,plain,(
    ! [B_10] : r1_tarski(B_10,B_10) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_127,plain,(
    ! [B_46] : k4_xboole_0(B_46,B_46) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_26,c_110])).

tff(c_148,plain,(
    ! [B_47] : r1_tarski(k1_xboole_0,B_47) ),
    inference(superposition,[status(thm),theory(equality)],[c_127,c_36])).

tff(c_30,plain,(
    ! [A_11,B_12] :
      ( k4_xboole_0(A_11,B_12) = k1_xboole_0
      | ~ r1_tarski(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_183,plain,(
    ! [B_50] : k4_xboole_0(k1_xboole_0,B_50) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_148,c_30])).

tff(c_44,plain,(
    ! [A_24,B_25] : k5_xboole_0(A_24,k4_xboole_0(B_25,A_24)) = k2_xboole_0(A_24,B_25) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_188,plain,(
    ! [B_50] : k5_xboole_0(B_50,k1_xboole_0) = k2_xboole_0(B_50,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_183,c_44])).

tff(c_34,plain,(
    ! [A_15] : k3_xboole_0(A_15,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_375,plain,(
    ! [A_57,B_58] : k5_xboole_0(A_57,k3_xboole_0(A_57,B_58)) = k4_xboole_0(A_57,B_58) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_392,plain,(
    ! [A_15] : k5_xboole_0(A_15,k1_xboole_0) = k4_xboole_0(A_15,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_375])).

tff(c_397,plain,(
    ! [A_15] : k2_xboole_0(A_15,k1_xboole_0) = A_15 ),
    inference(demodulation,[status(thm),theory(equality)],[c_188,c_38,c_392])).

tff(c_32,plain,(
    ! [A_13,B_14] : k5_xboole_0(A_13,k3_xboole_0(A_13,B_14)) = k4_xboole_0(A_13,B_14) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_632,plain,(
    ! [A_79,B_80] : k4_xboole_0(A_79,k4_xboole_0(A_79,B_80)) = k3_xboole_0(A_79,B_80) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_647,plain,(
    ! [A_79,B_80] : k4_xboole_0(k3_xboole_0(A_79,B_80),A_79) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_632,c_125])).

tff(c_1194,plain,(
    ! [A_104,B_105] : k2_xboole_0(k4_xboole_0(A_104,B_105),k4_xboole_0(B_105,A_104)) = k5_xboole_0(A_104,B_105) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_1210,plain,(
    ! [A_79,B_80] : k2_xboole_0(k4_xboole_0(A_79,k3_xboole_0(A_79,B_80)),k1_xboole_0) = k5_xboole_0(A_79,k3_xboole_0(A_79,B_80)) ),
    inference(superposition,[status(thm),theory(equality)],[c_647,c_1194])).

tff(c_1260,plain,(
    ! [A_79,B_80] : k4_xboole_0(A_79,k3_xboole_0(A_79,B_80)) = k4_xboole_0(A_79,B_80) ),
    inference(demodulation,[status(thm),theory(equality)],[c_397,c_32,c_1210])).

tff(c_126,plain,(
    ! [B_10] : k4_xboole_0(B_10,B_10) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_26,c_110])).

tff(c_679,plain,(
    ! [B_10] : k4_xboole_0(B_10,k1_xboole_0) = k3_xboole_0(B_10,B_10) ),
    inference(superposition,[status(thm),theory(equality)],[c_126,c_632])).

tff(c_691,plain,(
    ! [B_10] : k3_xboole_0(B_10,B_10) = B_10 ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_679])).

tff(c_1678,plain,(
    ! [A_120,B_121,C_122] : k2_xboole_0(k4_xboole_0(A_120,B_121),k3_xboole_0(A_120,C_122)) = k4_xboole_0(A_120,k4_xboole_0(B_121,C_122)) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_9434,plain,(
    ! [B_255,B_256] : k4_xboole_0(B_255,k4_xboole_0(B_256,B_255)) = k2_xboole_0(k4_xboole_0(B_255,B_256),B_255) ),
    inference(superposition,[status(thm),theory(equality)],[c_691,c_1678])).

tff(c_9706,plain,(
    ! [A_79,B_80] : k2_xboole_0(k4_xboole_0(A_79,k3_xboole_0(A_79,B_80)),A_79) = k4_xboole_0(A_79,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_647,c_9434])).

tff(c_9785,plain,(
    ! [A_79,B_80] : k2_xboole_0(k4_xboole_0(A_79,B_80),A_79) = A_79 ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_1260,c_9706])).

tff(c_1714,plain,(
    ! [B_10,B_121] : k4_xboole_0(B_10,k4_xboole_0(B_121,B_10)) = k2_xboole_0(k4_xboole_0(B_10,B_121),B_10) ),
    inference(superposition,[status(thm),theory(equality)],[c_691,c_1678])).

tff(c_10017,plain,(
    ! [B_261,B_262] : k4_xboole_0(B_261,k4_xboole_0(B_262,B_261)) = B_261 ),
    inference(demodulation,[status(thm),theory(equality)],[c_9785,c_1714])).

tff(c_4,plain,(
    ! [D_6,B_2,A_1] :
      ( ~ r2_hidden(D_6,B_2)
      | ~ r2_hidden(D_6,k4_xboole_0(A_1,B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_10179,plain,(
    ! [D_6,B_262,B_261] :
      ( ~ r2_hidden(D_6,k4_xboole_0(B_262,B_261))
      | ~ r2_hidden(D_6,B_261) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10017,c_4])).

tff(c_31940,plain,(
    ! [B_457,B_458] :
      ( ~ r2_hidden(B_457,B_458)
      | k4_xboole_0(k1_tarski(B_457),B_458) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_31818,c_10179])).

tff(c_56,plain,(
    k1_tarski('#skF_4') != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_28,plain,(
    ! [A_11,B_12] :
      ( r1_tarski(A_11,B_12)
      | k4_xboole_0(A_11,B_12) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_552,plain,(
    ! [B_70,A_71] :
      ( B_70 = A_71
      | ~ r1_tarski(B_70,A_71)
      | ~ r1_tarski(A_71,B_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_1651,plain,(
    ! [B_118,A_119] :
      ( B_118 = A_119
      | ~ r1_tarski(B_118,A_119)
      | k4_xboole_0(A_119,B_118) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_28,c_552])).

tff(c_9253,plain,(
    ! [B_251,A_252] :
      ( B_251 = A_252
      | k4_xboole_0(B_251,A_252) != k1_xboole_0
      | k4_xboole_0(A_252,B_251) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_28,c_1651])).

tff(c_9297,plain,
    ( k1_tarski('#skF_4') = '#skF_3'
    | k4_xboole_0(k1_tarski('#skF_4'),'#skF_3') != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_60,c_9253])).

tff(c_9319,plain,(
    k4_xboole_0(k1_tarski('#skF_4'),'#skF_3') != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_9297])).

tff(c_32169,plain,(
    ~ r2_hidden('#skF_4','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_31940,c_9319])).

tff(c_32418,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_539,c_32169])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n018.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 11:21:56 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 11.32/4.68  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.32/4.68  
% 11.32/4.68  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.32/4.68  %$ r2_hidden > r1_tarski > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2 > #skF_4
% 11.32/4.68  
% 11.32/4.68  %Foreground sorts:
% 11.32/4.68  
% 11.32/4.68  
% 11.32/4.68  %Background operators:
% 11.32/4.68  
% 11.32/4.68  
% 11.32/4.68  %Foreground operators:
% 11.32/4.68  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 11.32/4.68  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 11.32/4.68  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 11.32/4.68  tff(k1_tarski, type, k1_tarski: $i > $i).
% 11.32/4.68  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 11.32/4.68  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 11.32/4.68  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 11.32/4.68  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 11.32/4.68  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 11.32/4.68  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 11.32/4.68  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 11.32/4.68  tff('#skF_3', type, '#skF_3': $i).
% 11.32/4.68  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 11.32/4.68  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 11.32/4.68  tff('#skF_4', type, '#skF_4': $i).
% 11.32/4.68  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 11.32/4.68  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 11.32/4.68  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 11.32/4.68  
% 11.46/4.70  tff(f_82, negated_conjecture, ~(![A, B]: ~(((k4_xboole_0(A, k1_tarski(B)) = k1_xboole_0) & ~(A = k1_xboole_0)) & ~(A = k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t66_zfmisc_1)).
% 11.46/4.70  tff(f_72, axiom, (![A, B]: ((k4_xboole_0(A, k1_tarski(B)) = A) <=> ~r2_hidden(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_zfmisc_1)).
% 11.46/4.70  tff(f_53, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 11.46/4.70  tff(f_47, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 11.46/4.70  tff(f_55, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 11.46/4.70  tff(f_43, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 11.46/4.70  tff(f_61, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_xboole_1)).
% 11.46/4.70  tff(f_51, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 11.46/4.70  tff(f_49, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 11.46/4.70  tff(f_57, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 11.46/4.70  tff(f_37, axiom, (![A, B]: (k5_xboole_0(A, B) = k2_xboole_0(k4_xboole_0(A, B), k4_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d6_xboole_0)).
% 11.46/4.70  tff(f_59, axiom, (![A, B, C]: (k4_xboole_0(A, k4_xboole_0(B, C)) = k2_xboole_0(k4_xboole_0(A, B), k3_xboole_0(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_xboole_1)).
% 11.46/4.70  tff(f_35, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 11.46/4.70  tff(c_58, plain, (k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_82])).
% 11.46/4.70  tff(c_484, plain, (![A_66, B_67]: (k4_xboole_0(A_66, k1_tarski(B_67))=A_66 | r2_hidden(B_67, A_66))), inference(cnfTransformation, [status(thm)], [f_72])).
% 11.46/4.70  tff(c_60, plain, (k4_xboole_0('#skF_3', k1_tarski('#skF_4'))=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_82])).
% 11.46/4.70  tff(c_514, plain, (k1_xboole_0='#skF_3' | r2_hidden('#skF_4', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_484, c_60])).
% 11.46/4.70  tff(c_539, plain, (r2_hidden('#skF_4', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_58, c_514])).
% 11.46/4.70  tff(c_36, plain, (![A_16, B_17]: (r1_tarski(k4_xboole_0(A_16, B_17), A_16))), inference(cnfTransformation, [status(thm)], [f_53])).
% 11.46/4.70  tff(c_110, plain, (![A_44, B_45]: (k4_xboole_0(A_44, B_45)=k1_xboole_0 | ~r1_tarski(A_44, B_45))), inference(cnfTransformation, [status(thm)], [f_47])).
% 11.46/4.70  tff(c_125, plain, (![A_16, B_17]: (k4_xboole_0(k4_xboole_0(A_16, B_17), A_16)=k1_xboole_0)), inference(resolution, [status(thm)], [c_36, c_110])).
% 11.46/4.70  tff(c_31818, plain, (![B_455, B_456]: (k4_xboole_0(k1_tarski(B_455), B_456)=k1_xboole_0 | r2_hidden(B_455, k4_xboole_0(k1_tarski(B_455), B_456)))), inference(superposition, [status(thm), theory('equality')], [c_125, c_484])).
% 11.46/4.70  tff(c_38, plain, (![A_18]: (k4_xboole_0(A_18, k1_xboole_0)=A_18)), inference(cnfTransformation, [status(thm)], [f_55])).
% 11.46/4.70  tff(c_26, plain, (![B_10]: (r1_tarski(B_10, B_10))), inference(cnfTransformation, [status(thm)], [f_43])).
% 11.46/4.70  tff(c_127, plain, (![B_46]: (k4_xboole_0(B_46, B_46)=k1_xboole_0)), inference(resolution, [status(thm)], [c_26, c_110])).
% 11.46/4.70  tff(c_148, plain, (![B_47]: (r1_tarski(k1_xboole_0, B_47))), inference(superposition, [status(thm), theory('equality')], [c_127, c_36])).
% 11.46/4.70  tff(c_30, plain, (![A_11, B_12]: (k4_xboole_0(A_11, B_12)=k1_xboole_0 | ~r1_tarski(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_47])).
% 11.46/4.70  tff(c_183, plain, (![B_50]: (k4_xboole_0(k1_xboole_0, B_50)=k1_xboole_0)), inference(resolution, [status(thm)], [c_148, c_30])).
% 11.46/4.70  tff(c_44, plain, (![A_24, B_25]: (k5_xboole_0(A_24, k4_xboole_0(B_25, A_24))=k2_xboole_0(A_24, B_25))), inference(cnfTransformation, [status(thm)], [f_61])).
% 11.46/4.70  tff(c_188, plain, (![B_50]: (k5_xboole_0(B_50, k1_xboole_0)=k2_xboole_0(B_50, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_183, c_44])).
% 11.46/4.70  tff(c_34, plain, (![A_15]: (k3_xboole_0(A_15, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_51])).
% 11.46/4.70  tff(c_375, plain, (![A_57, B_58]: (k5_xboole_0(A_57, k3_xboole_0(A_57, B_58))=k4_xboole_0(A_57, B_58))), inference(cnfTransformation, [status(thm)], [f_49])).
% 11.46/4.70  tff(c_392, plain, (![A_15]: (k5_xboole_0(A_15, k1_xboole_0)=k4_xboole_0(A_15, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_34, c_375])).
% 11.46/4.70  tff(c_397, plain, (![A_15]: (k2_xboole_0(A_15, k1_xboole_0)=A_15)), inference(demodulation, [status(thm), theory('equality')], [c_188, c_38, c_392])).
% 11.46/4.70  tff(c_32, plain, (![A_13, B_14]: (k5_xboole_0(A_13, k3_xboole_0(A_13, B_14))=k4_xboole_0(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_49])).
% 11.46/4.70  tff(c_632, plain, (![A_79, B_80]: (k4_xboole_0(A_79, k4_xboole_0(A_79, B_80))=k3_xboole_0(A_79, B_80))), inference(cnfTransformation, [status(thm)], [f_57])).
% 11.46/4.70  tff(c_647, plain, (![A_79, B_80]: (k4_xboole_0(k3_xboole_0(A_79, B_80), A_79)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_632, c_125])).
% 11.46/4.70  tff(c_1194, plain, (![A_104, B_105]: (k2_xboole_0(k4_xboole_0(A_104, B_105), k4_xboole_0(B_105, A_104))=k5_xboole_0(A_104, B_105))), inference(cnfTransformation, [status(thm)], [f_37])).
% 11.46/4.70  tff(c_1210, plain, (![A_79, B_80]: (k2_xboole_0(k4_xboole_0(A_79, k3_xboole_0(A_79, B_80)), k1_xboole_0)=k5_xboole_0(A_79, k3_xboole_0(A_79, B_80)))), inference(superposition, [status(thm), theory('equality')], [c_647, c_1194])).
% 11.46/4.70  tff(c_1260, plain, (![A_79, B_80]: (k4_xboole_0(A_79, k3_xboole_0(A_79, B_80))=k4_xboole_0(A_79, B_80))), inference(demodulation, [status(thm), theory('equality')], [c_397, c_32, c_1210])).
% 11.46/4.70  tff(c_126, plain, (![B_10]: (k4_xboole_0(B_10, B_10)=k1_xboole_0)), inference(resolution, [status(thm)], [c_26, c_110])).
% 11.46/4.70  tff(c_679, plain, (![B_10]: (k4_xboole_0(B_10, k1_xboole_0)=k3_xboole_0(B_10, B_10))), inference(superposition, [status(thm), theory('equality')], [c_126, c_632])).
% 11.46/4.70  tff(c_691, plain, (![B_10]: (k3_xboole_0(B_10, B_10)=B_10)), inference(demodulation, [status(thm), theory('equality')], [c_38, c_679])).
% 11.46/4.70  tff(c_1678, plain, (![A_120, B_121, C_122]: (k2_xboole_0(k4_xboole_0(A_120, B_121), k3_xboole_0(A_120, C_122))=k4_xboole_0(A_120, k4_xboole_0(B_121, C_122)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 11.46/4.70  tff(c_9434, plain, (![B_255, B_256]: (k4_xboole_0(B_255, k4_xboole_0(B_256, B_255))=k2_xboole_0(k4_xboole_0(B_255, B_256), B_255))), inference(superposition, [status(thm), theory('equality')], [c_691, c_1678])).
% 11.46/4.70  tff(c_9706, plain, (![A_79, B_80]: (k2_xboole_0(k4_xboole_0(A_79, k3_xboole_0(A_79, B_80)), A_79)=k4_xboole_0(A_79, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_647, c_9434])).
% 11.46/4.70  tff(c_9785, plain, (![A_79, B_80]: (k2_xboole_0(k4_xboole_0(A_79, B_80), A_79)=A_79)), inference(demodulation, [status(thm), theory('equality')], [c_38, c_1260, c_9706])).
% 11.46/4.70  tff(c_1714, plain, (![B_10, B_121]: (k4_xboole_0(B_10, k4_xboole_0(B_121, B_10))=k2_xboole_0(k4_xboole_0(B_10, B_121), B_10))), inference(superposition, [status(thm), theory('equality')], [c_691, c_1678])).
% 11.46/4.70  tff(c_10017, plain, (![B_261, B_262]: (k4_xboole_0(B_261, k4_xboole_0(B_262, B_261))=B_261)), inference(demodulation, [status(thm), theory('equality')], [c_9785, c_1714])).
% 11.46/4.70  tff(c_4, plain, (![D_6, B_2, A_1]: (~r2_hidden(D_6, B_2) | ~r2_hidden(D_6, k4_xboole_0(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 11.46/4.70  tff(c_10179, plain, (![D_6, B_262, B_261]: (~r2_hidden(D_6, k4_xboole_0(B_262, B_261)) | ~r2_hidden(D_6, B_261))), inference(superposition, [status(thm), theory('equality')], [c_10017, c_4])).
% 11.46/4.70  tff(c_31940, plain, (![B_457, B_458]: (~r2_hidden(B_457, B_458) | k4_xboole_0(k1_tarski(B_457), B_458)=k1_xboole_0)), inference(resolution, [status(thm)], [c_31818, c_10179])).
% 11.46/4.70  tff(c_56, plain, (k1_tarski('#skF_4')!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_82])).
% 11.46/4.70  tff(c_28, plain, (![A_11, B_12]: (r1_tarski(A_11, B_12) | k4_xboole_0(A_11, B_12)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_47])).
% 11.46/4.70  tff(c_552, plain, (![B_70, A_71]: (B_70=A_71 | ~r1_tarski(B_70, A_71) | ~r1_tarski(A_71, B_70))), inference(cnfTransformation, [status(thm)], [f_43])).
% 11.46/4.70  tff(c_1651, plain, (![B_118, A_119]: (B_118=A_119 | ~r1_tarski(B_118, A_119) | k4_xboole_0(A_119, B_118)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_28, c_552])).
% 11.46/4.70  tff(c_9253, plain, (![B_251, A_252]: (B_251=A_252 | k4_xboole_0(B_251, A_252)!=k1_xboole_0 | k4_xboole_0(A_252, B_251)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_28, c_1651])).
% 11.46/4.70  tff(c_9297, plain, (k1_tarski('#skF_4')='#skF_3' | k4_xboole_0(k1_tarski('#skF_4'), '#skF_3')!=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_60, c_9253])).
% 11.46/4.70  tff(c_9319, plain, (k4_xboole_0(k1_tarski('#skF_4'), '#skF_3')!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_56, c_9297])).
% 11.46/4.70  tff(c_32169, plain, (~r2_hidden('#skF_4', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_31940, c_9319])).
% 11.46/4.70  tff(c_32418, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_539, c_32169])).
% 11.46/4.70  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.46/4.70  
% 11.46/4.70  Inference rules
% 11.46/4.70  ----------------------
% 11.46/4.70  #Ref     : 0
% 11.46/4.70  #Sup     : 7934
% 11.46/4.70  #Fact    : 3
% 11.46/4.70  #Define  : 0
% 11.46/4.70  #Split   : 1
% 11.46/4.70  #Chain   : 0
% 11.46/4.70  #Close   : 0
% 11.46/4.70  
% 11.46/4.70  Ordering : KBO
% 11.46/4.70  
% 11.46/4.70  Simplification rules
% 11.46/4.70  ----------------------
% 11.46/4.70  #Subsume      : 1526
% 11.46/4.70  #Demod        : 7629
% 11.46/4.70  #Tautology    : 4307
% 11.46/4.70  #SimpNegUnit  : 578
% 11.46/4.70  #BackRed      : 14
% 11.46/4.70  
% 11.46/4.70  #Partial instantiations: 0
% 11.46/4.70  #Strategies tried      : 1
% 11.46/4.70  
% 11.46/4.70  Timing (in seconds)
% 11.46/4.70  ----------------------
% 11.46/4.70  Preprocessing        : 0.33
% 11.46/4.70  Parsing              : 0.17
% 11.46/4.70  CNF conversion       : 0.02
% 11.46/4.70  Main loop            : 3.59
% 11.46/4.70  Inferencing          : 0.76
% 11.46/4.70  Reduction            : 1.72
% 11.46/4.70  Demodulation         : 1.41
% 11.46/4.70  BG Simplification    : 0.09
% 11.46/4.70  Subsumption          : 0.84
% 11.46/4.70  Abstraction          : 0.14
% 11.46/4.70  MUC search           : 0.00
% 11.46/4.70  Cooper               : 0.00
% 11.46/4.70  Total                : 3.96
% 11.46/4.70  Index Insertion      : 0.00
% 11.46/4.71  Index Deletion       : 0.00
% 11.46/4.71  Index Matching       : 0.00
% 11.46/4.71  BG Taut test         : 0.00
%------------------------------------------------------------------------------
