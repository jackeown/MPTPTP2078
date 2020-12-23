%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:51:14 EST 2020

% Result     : Theorem 23.84s
% Output     : CNFRefutation 23.84s
% Verified   : 
% Statistics : Number of formulae       :   92 ( 130 expanded)
%              Number of leaves         :   42 (  62 expanded)
%              Depth                    :   13
%              Number of atoms          :  112 ( 190 expanded)
%              Number of equality atoms :   38 (  55 expanded)
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

tff(f_121,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( r2_hidden(A,B)
          & r2_hidden(C,B) )
       => k2_xboole_0(k2_tarski(A,C),B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_zfmisc_1)).

tff(f_90,axiom,(
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

tff(f_96,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_94,axiom,(
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

tff(f_62,axiom,(
    ! [A,B] :
      ( ! [C] :
          ( r2_hidden(C,A)
        <=> r2_hidden(C,B) )
     => A = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tarski)).

tff(f_86,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_88,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_114,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_tarski(A,B),C)
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).

tff(f_98,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_100,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_108,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(c_94,plain,(
    r2_hidden('#skF_9','#skF_10') ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_92,plain,(
    r2_hidden('#skF_11','#skF_10') ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_66,plain,(
    ! [A_31] : k2_xboole_0(A_31,k1_xboole_0) = A_31 ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_6,plain,(
    ! [A_3] :
      ( v1_xboole_0(A_3)
      | r2_hidden('#skF_1'(A_3),A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_334,plain,(
    ! [D_77,A_78,B_79] :
      ( r2_hidden(D_77,A_78)
      | ~ r2_hidden(D_77,k4_xboole_0(A_78,B_79)) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_339,plain,(
    ! [A_78,B_79] :
      ( r2_hidden('#skF_1'(k4_xboole_0(A_78,B_79)),A_78)
      | v1_xboole_0(k4_xboole_0(A_78,B_79)) ) ),
    inference(resolution,[status(thm)],[c_6,c_334])).

tff(c_415,plain,(
    ! [D_86,B_87,A_88] :
      ( ~ r2_hidden(D_86,B_87)
      | ~ r2_hidden(D_86,k4_xboole_0(A_88,B_87)) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_1257,plain,(
    ! [A_184,B_185] :
      ( ~ r2_hidden('#skF_1'(k4_xboole_0(A_184,B_185)),B_185)
      | v1_xboole_0(k4_xboole_0(A_184,B_185)) ) ),
    inference(resolution,[status(thm)],[c_6,c_415])).

tff(c_1276,plain,(
    ! [A_78] : v1_xboole_0(k4_xboole_0(A_78,A_78)) ),
    inference(resolution,[status(thm)],[c_339,c_1257])).

tff(c_70,plain,(
    ! [A_34] : r1_tarski(k1_xboole_0,A_34) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_180,plain,(
    ! [A_66,B_67] :
      ( k3_xboole_0(A_66,B_67) = A_66
      | ~ r1_tarski(A_66,B_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_187,plain,(
    ! [A_34] : k3_xboole_0(k1_xboole_0,A_34) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_70,c_180])).

tff(c_444,plain,(
    ! [D_92,B_93,A_94] :
      ( r2_hidden(D_92,B_93)
      | ~ r2_hidden(D_92,k3_xboole_0(A_94,B_93)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_681,plain,(
    ! [D_119,A_120] :
      ( r2_hidden(D_119,A_120)
      | ~ r2_hidden(D_119,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_187,c_444])).

tff(c_689,plain,(
    ! [A_120] :
      ( r2_hidden('#skF_1'(k1_xboole_0),A_120)
      | v1_xboole_0(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_6,c_681])).

tff(c_691,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_689])).

tff(c_1392,plain,(
    ! [A_195,B_196] :
      ( r2_hidden('#skF_6'(A_195,B_196),B_196)
      | r2_hidden('#skF_7'(A_195,B_196),A_195)
      | B_196 = A_195 ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_4,plain,(
    ! [B_6,A_3] :
      ( ~ r2_hidden(B_6,A_3)
      | ~ v1_xboole_0(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_1473,plain,(
    ! [B_197,A_198] :
      ( ~ v1_xboole_0(B_197)
      | r2_hidden('#skF_7'(A_198,B_197),A_198)
      | B_197 = A_198 ) ),
    inference(resolution,[status(thm)],[c_1392,c_4])).

tff(c_1513,plain,(
    ! [A_199,B_200] :
      ( ~ v1_xboole_0(A_199)
      | ~ v1_xboole_0(B_200)
      | B_200 = A_199 ) ),
    inference(resolution,[status(thm)],[c_1473,c_4])).

tff(c_1532,plain,(
    ! [B_201] :
      ( ~ v1_xboole_0(B_201)
      | k1_xboole_0 = B_201 ) ),
    inference(resolution,[status(thm)],[c_691,c_1513])).

tff(c_1552,plain,(
    ! [A_78] : k4_xboole_0(A_78,A_78) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1276,c_1532])).

tff(c_62,plain,(
    ! [B_28] : r1_tarski(B_28,B_28) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_188,plain,(
    ! [B_28] : k3_xboole_0(B_28,B_28) = B_28 ),
    inference(resolution,[status(thm)],[c_62,c_180])).

tff(c_341,plain,(
    ! [A_80,B_81] : k5_xboole_0(A_80,k3_xboole_0(A_80,B_81)) = k4_xboole_0(A_80,B_81) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_350,plain,(
    ! [B_28] : k5_xboole_0(B_28,B_28) = k4_xboole_0(B_28,B_28) ),
    inference(superposition,[status(thm),theory(equality)],[c_188,c_341])).

tff(c_1570,plain,(
    ! [B_28] : k5_xboole_0(B_28,B_28) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1552,c_350])).

tff(c_956,plain,(
    ! [A_156,B_157,C_158] :
      ( r1_tarski(k2_tarski(A_156,B_157),C_158)
      | ~ r2_hidden(B_157,C_158)
      | ~ r2_hidden(A_156,C_158) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_68,plain,(
    ! [A_32,B_33] :
      ( k3_xboole_0(A_32,B_33) = A_32
      | ~ r1_tarski(A_32,B_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_19798,plain,(
    ! [A_768,B_769,C_770] :
      ( k3_xboole_0(k2_tarski(A_768,B_769),C_770) = k2_tarski(A_768,B_769)
      | ~ r2_hidden(B_769,C_770)
      | ~ r2_hidden(A_768,C_770) ) ),
    inference(resolution,[status(thm)],[c_956,c_68])).

tff(c_64,plain,(
    ! [A_29,B_30] : k5_xboole_0(A_29,k3_xboole_0(A_29,B_30)) = k4_xboole_0(A_29,B_30) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_20067,plain,(
    ! [A_768,B_769,C_770] :
      ( k5_xboole_0(k2_tarski(A_768,B_769),k2_tarski(A_768,B_769)) = k4_xboole_0(k2_tarski(A_768,B_769),C_770)
      | ~ r2_hidden(B_769,C_770)
      | ~ r2_hidden(A_768,C_770) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_19798,c_64])).

tff(c_106530,plain,(
    ! [A_1850,B_1851,C_1852] :
      ( k4_xboole_0(k2_tarski(A_1850,B_1851),C_1852) = k1_xboole_0
      | ~ r2_hidden(B_1851,C_1852)
      | ~ r2_hidden(A_1850,C_1852) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1570,c_20067])).

tff(c_72,plain,(
    ! [A_35,B_36] : k2_xboole_0(A_35,k4_xboole_0(B_36,A_35)) = k2_xboole_0(A_35,B_36) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_107093,plain,(
    ! [C_1852,A_1850,B_1851] :
      ( k2_xboole_0(C_1852,k2_tarski(A_1850,B_1851)) = k2_xboole_0(C_1852,k1_xboole_0)
      | ~ r2_hidden(B_1851,C_1852)
      | ~ r2_hidden(A_1850,C_1852) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_106530,c_72])).

tff(c_109642,plain,(
    ! [C_1891,A_1892,B_1893] :
      ( k2_xboole_0(C_1891,k2_tarski(A_1892,B_1893)) = C_1891
      | ~ r2_hidden(B_1893,C_1891)
      | ~ r2_hidden(A_1892,C_1891) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_107093])).

tff(c_74,plain,(
    ! [B_38,A_37] : k2_tarski(B_38,A_37) = k2_tarski(A_37,B_38) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_165,plain,(
    ! [A_64,B_65] : k3_tarski(k2_tarski(A_64,B_65)) = k2_xboole_0(A_64,B_65) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_224,plain,(
    ! [A_72,B_73] : k3_tarski(k2_tarski(A_72,B_73)) = k2_xboole_0(B_73,A_72) ),
    inference(superposition,[status(thm),theory(equality)],[c_74,c_165])).

tff(c_82,plain,(
    ! [A_48,B_49] : k3_tarski(k2_tarski(A_48,B_49)) = k2_xboole_0(A_48,B_49) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_230,plain,(
    ! [B_73,A_72] : k2_xboole_0(B_73,A_72) = k2_xboole_0(A_72,B_73) ),
    inference(superposition,[status(thm),theory(equality)],[c_224,c_82])).

tff(c_90,plain,(
    k2_xboole_0(k2_tarski('#skF_9','#skF_11'),'#skF_10') != '#skF_10' ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_247,plain,(
    k2_xboole_0('#skF_10',k2_tarski('#skF_9','#skF_11')) != '#skF_10' ),
    inference(demodulation,[status(thm),theory(equality)],[c_230,c_90])).

tff(c_109700,plain,
    ( ~ r2_hidden('#skF_11','#skF_10')
    | ~ r2_hidden('#skF_9','#skF_10') ),
    inference(superposition,[status(thm),theory(equality)],[c_109642,c_247])).

tff(c_109791,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_92,c_109700])).

tff(c_109792,plain,(
    ! [A_120] : r2_hidden('#skF_1'(k1_xboole_0),A_120) ),
    inference(splitRight,[status(thm)],[c_689])).

tff(c_109794,plain,(
    ! [A_1894] : r2_hidden('#skF_1'(k1_xboole_0),A_1894) ),
    inference(splitRight,[status(thm)],[c_689])).

tff(c_28,plain,(
    ! [D_18,B_14,A_13] :
      ( ~ r2_hidden(D_18,B_14)
      | ~ r2_hidden(D_18,k4_xboole_0(A_13,B_14)) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_109809,plain,(
    ! [B_14] : ~ r2_hidden('#skF_1'(k1_xboole_0),B_14) ),
    inference(resolution,[status(thm)],[c_109794,c_28])).

tff(c_109832,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_109792,c_109809])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n019.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 13:54:37 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 23.84/15.92  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 23.84/15.93  
% 23.84/15.93  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 23.84/15.93  %$ r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_xboole_0 > #skF_6 > #skF_11 > #skF_1 > #skF_4 > #skF_10 > #skF_5 > #skF_2 > #skF_8 > #skF_9 > #skF_3 > #skF_7
% 23.84/15.93  
% 23.84/15.93  %Foreground sorts:
% 23.84/15.93  
% 23.84/15.93  
% 23.84/15.93  %Background operators:
% 23.84/15.93  
% 23.84/15.93  
% 23.84/15.93  %Foreground operators:
% 23.84/15.93  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 23.84/15.93  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 23.84/15.93  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 23.84/15.93  tff('#skF_11', type, '#skF_11': $i).
% 23.84/15.93  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 23.84/15.93  tff('#skF_1', type, '#skF_1': $i > $i).
% 23.84/15.93  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 23.84/15.93  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 23.84/15.93  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 23.84/15.93  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 23.84/15.93  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 23.84/15.93  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 23.84/15.93  tff('#skF_10', type, '#skF_10': $i).
% 23.84/15.93  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 23.84/15.93  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 23.84/15.93  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 23.84/15.93  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 23.84/15.93  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 23.84/15.93  tff('#skF_8', type, '#skF_8': ($i * $i) > $i).
% 23.84/15.93  tff('#skF_9', type, '#skF_9': $i).
% 23.84/15.93  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 23.84/15.93  tff(k3_tarski, type, k3_tarski: $i > $i).
% 23.84/15.93  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 23.84/15.93  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 23.84/15.93  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 23.84/15.93  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 23.84/15.93  tff('#skF_7', type, '#skF_7': ($i * $i) > $i).
% 23.84/15.93  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 23.84/15.93  
% 23.84/15.95  tff(f_121, negated_conjecture, ~(![A, B, C]: ((r2_hidden(A, B) & r2_hidden(C, B)) => (k2_xboole_0(k2_tarski(A, C), B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_zfmisc_1)).
% 23.84/15.95  tff(f_90, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 23.84/15.95  tff(f_36, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 23.84/15.95  tff(f_55, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 23.84/15.95  tff(f_96, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 23.84/15.95  tff(f_94, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 23.84/15.95  tff(f_45, axiom, (![A, B, C]: ((C = k3_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_xboole_0)).
% 23.84/15.95  tff(f_62, axiom, (![A, B]: ((![C]: (r2_hidden(C, A) <=> r2_hidden(C, B))) => (A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_tarski)).
% 23.84/15.95  tff(f_86, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 23.84/15.95  tff(f_88, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 23.84/15.95  tff(f_114, axiom, (![A, B, C]: (r1_tarski(k2_tarski(A, B), C) <=> (r2_hidden(A, C) & r2_hidden(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 23.84/15.95  tff(f_98, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 23.84/15.95  tff(f_100, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 23.84/15.95  tff(f_108, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 23.84/15.95  tff(c_94, plain, (r2_hidden('#skF_9', '#skF_10')), inference(cnfTransformation, [status(thm)], [f_121])).
% 23.84/15.95  tff(c_92, plain, (r2_hidden('#skF_11', '#skF_10')), inference(cnfTransformation, [status(thm)], [f_121])).
% 23.84/15.95  tff(c_66, plain, (![A_31]: (k2_xboole_0(A_31, k1_xboole_0)=A_31)), inference(cnfTransformation, [status(thm)], [f_90])).
% 23.84/15.95  tff(c_6, plain, (![A_3]: (v1_xboole_0(A_3) | r2_hidden('#skF_1'(A_3), A_3))), inference(cnfTransformation, [status(thm)], [f_36])).
% 23.84/15.95  tff(c_334, plain, (![D_77, A_78, B_79]: (r2_hidden(D_77, A_78) | ~r2_hidden(D_77, k4_xboole_0(A_78, B_79)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 23.84/15.95  tff(c_339, plain, (![A_78, B_79]: (r2_hidden('#skF_1'(k4_xboole_0(A_78, B_79)), A_78) | v1_xboole_0(k4_xboole_0(A_78, B_79)))), inference(resolution, [status(thm)], [c_6, c_334])).
% 23.84/15.95  tff(c_415, plain, (![D_86, B_87, A_88]: (~r2_hidden(D_86, B_87) | ~r2_hidden(D_86, k4_xboole_0(A_88, B_87)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 23.84/15.95  tff(c_1257, plain, (![A_184, B_185]: (~r2_hidden('#skF_1'(k4_xboole_0(A_184, B_185)), B_185) | v1_xboole_0(k4_xboole_0(A_184, B_185)))), inference(resolution, [status(thm)], [c_6, c_415])).
% 23.84/15.95  tff(c_1276, plain, (![A_78]: (v1_xboole_0(k4_xboole_0(A_78, A_78)))), inference(resolution, [status(thm)], [c_339, c_1257])).
% 23.84/15.95  tff(c_70, plain, (![A_34]: (r1_tarski(k1_xboole_0, A_34))), inference(cnfTransformation, [status(thm)], [f_96])).
% 23.84/15.95  tff(c_180, plain, (![A_66, B_67]: (k3_xboole_0(A_66, B_67)=A_66 | ~r1_tarski(A_66, B_67))), inference(cnfTransformation, [status(thm)], [f_94])).
% 23.84/15.95  tff(c_187, plain, (![A_34]: (k3_xboole_0(k1_xboole_0, A_34)=k1_xboole_0)), inference(resolution, [status(thm)], [c_70, c_180])).
% 23.84/15.95  tff(c_444, plain, (![D_92, B_93, A_94]: (r2_hidden(D_92, B_93) | ~r2_hidden(D_92, k3_xboole_0(A_94, B_93)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 23.84/15.95  tff(c_681, plain, (![D_119, A_120]: (r2_hidden(D_119, A_120) | ~r2_hidden(D_119, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_187, c_444])).
% 23.84/15.95  tff(c_689, plain, (![A_120]: (r2_hidden('#skF_1'(k1_xboole_0), A_120) | v1_xboole_0(k1_xboole_0))), inference(resolution, [status(thm)], [c_6, c_681])).
% 23.84/15.95  tff(c_691, plain, (v1_xboole_0(k1_xboole_0)), inference(splitLeft, [status(thm)], [c_689])).
% 23.84/15.95  tff(c_1392, plain, (![A_195, B_196]: (r2_hidden('#skF_6'(A_195, B_196), B_196) | r2_hidden('#skF_7'(A_195, B_196), A_195) | B_196=A_195)), inference(cnfTransformation, [status(thm)], [f_62])).
% 23.84/15.95  tff(c_4, plain, (![B_6, A_3]: (~r2_hidden(B_6, A_3) | ~v1_xboole_0(A_3))), inference(cnfTransformation, [status(thm)], [f_36])).
% 23.84/15.95  tff(c_1473, plain, (![B_197, A_198]: (~v1_xboole_0(B_197) | r2_hidden('#skF_7'(A_198, B_197), A_198) | B_197=A_198)), inference(resolution, [status(thm)], [c_1392, c_4])).
% 23.84/15.95  tff(c_1513, plain, (![A_199, B_200]: (~v1_xboole_0(A_199) | ~v1_xboole_0(B_200) | B_200=A_199)), inference(resolution, [status(thm)], [c_1473, c_4])).
% 23.84/15.95  tff(c_1532, plain, (![B_201]: (~v1_xboole_0(B_201) | k1_xboole_0=B_201)), inference(resolution, [status(thm)], [c_691, c_1513])).
% 23.84/15.95  tff(c_1552, plain, (![A_78]: (k4_xboole_0(A_78, A_78)=k1_xboole_0)), inference(resolution, [status(thm)], [c_1276, c_1532])).
% 23.84/15.95  tff(c_62, plain, (![B_28]: (r1_tarski(B_28, B_28))), inference(cnfTransformation, [status(thm)], [f_86])).
% 23.84/15.95  tff(c_188, plain, (![B_28]: (k3_xboole_0(B_28, B_28)=B_28)), inference(resolution, [status(thm)], [c_62, c_180])).
% 23.84/15.95  tff(c_341, plain, (![A_80, B_81]: (k5_xboole_0(A_80, k3_xboole_0(A_80, B_81))=k4_xboole_0(A_80, B_81))), inference(cnfTransformation, [status(thm)], [f_88])).
% 23.84/15.95  tff(c_350, plain, (![B_28]: (k5_xboole_0(B_28, B_28)=k4_xboole_0(B_28, B_28))), inference(superposition, [status(thm), theory('equality')], [c_188, c_341])).
% 23.84/15.95  tff(c_1570, plain, (![B_28]: (k5_xboole_0(B_28, B_28)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_1552, c_350])).
% 23.84/15.95  tff(c_956, plain, (![A_156, B_157, C_158]: (r1_tarski(k2_tarski(A_156, B_157), C_158) | ~r2_hidden(B_157, C_158) | ~r2_hidden(A_156, C_158))), inference(cnfTransformation, [status(thm)], [f_114])).
% 23.84/15.95  tff(c_68, plain, (![A_32, B_33]: (k3_xboole_0(A_32, B_33)=A_32 | ~r1_tarski(A_32, B_33))), inference(cnfTransformation, [status(thm)], [f_94])).
% 23.84/15.95  tff(c_19798, plain, (![A_768, B_769, C_770]: (k3_xboole_0(k2_tarski(A_768, B_769), C_770)=k2_tarski(A_768, B_769) | ~r2_hidden(B_769, C_770) | ~r2_hidden(A_768, C_770))), inference(resolution, [status(thm)], [c_956, c_68])).
% 23.84/15.95  tff(c_64, plain, (![A_29, B_30]: (k5_xboole_0(A_29, k3_xboole_0(A_29, B_30))=k4_xboole_0(A_29, B_30))), inference(cnfTransformation, [status(thm)], [f_88])).
% 23.84/15.95  tff(c_20067, plain, (![A_768, B_769, C_770]: (k5_xboole_0(k2_tarski(A_768, B_769), k2_tarski(A_768, B_769))=k4_xboole_0(k2_tarski(A_768, B_769), C_770) | ~r2_hidden(B_769, C_770) | ~r2_hidden(A_768, C_770))), inference(superposition, [status(thm), theory('equality')], [c_19798, c_64])).
% 23.84/15.95  tff(c_106530, plain, (![A_1850, B_1851, C_1852]: (k4_xboole_0(k2_tarski(A_1850, B_1851), C_1852)=k1_xboole_0 | ~r2_hidden(B_1851, C_1852) | ~r2_hidden(A_1850, C_1852))), inference(demodulation, [status(thm), theory('equality')], [c_1570, c_20067])).
% 23.84/15.95  tff(c_72, plain, (![A_35, B_36]: (k2_xboole_0(A_35, k4_xboole_0(B_36, A_35))=k2_xboole_0(A_35, B_36))), inference(cnfTransformation, [status(thm)], [f_98])).
% 23.84/15.95  tff(c_107093, plain, (![C_1852, A_1850, B_1851]: (k2_xboole_0(C_1852, k2_tarski(A_1850, B_1851))=k2_xboole_0(C_1852, k1_xboole_0) | ~r2_hidden(B_1851, C_1852) | ~r2_hidden(A_1850, C_1852))), inference(superposition, [status(thm), theory('equality')], [c_106530, c_72])).
% 23.84/15.95  tff(c_109642, plain, (![C_1891, A_1892, B_1893]: (k2_xboole_0(C_1891, k2_tarski(A_1892, B_1893))=C_1891 | ~r2_hidden(B_1893, C_1891) | ~r2_hidden(A_1892, C_1891))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_107093])).
% 23.84/15.95  tff(c_74, plain, (![B_38, A_37]: (k2_tarski(B_38, A_37)=k2_tarski(A_37, B_38))), inference(cnfTransformation, [status(thm)], [f_100])).
% 23.84/15.95  tff(c_165, plain, (![A_64, B_65]: (k3_tarski(k2_tarski(A_64, B_65))=k2_xboole_0(A_64, B_65))), inference(cnfTransformation, [status(thm)], [f_108])).
% 23.84/15.95  tff(c_224, plain, (![A_72, B_73]: (k3_tarski(k2_tarski(A_72, B_73))=k2_xboole_0(B_73, A_72))), inference(superposition, [status(thm), theory('equality')], [c_74, c_165])).
% 23.84/15.95  tff(c_82, plain, (![A_48, B_49]: (k3_tarski(k2_tarski(A_48, B_49))=k2_xboole_0(A_48, B_49))), inference(cnfTransformation, [status(thm)], [f_108])).
% 23.84/15.95  tff(c_230, plain, (![B_73, A_72]: (k2_xboole_0(B_73, A_72)=k2_xboole_0(A_72, B_73))), inference(superposition, [status(thm), theory('equality')], [c_224, c_82])).
% 23.84/15.95  tff(c_90, plain, (k2_xboole_0(k2_tarski('#skF_9', '#skF_11'), '#skF_10')!='#skF_10'), inference(cnfTransformation, [status(thm)], [f_121])).
% 23.84/15.95  tff(c_247, plain, (k2_xboole_0('#skF_10', k2_tarski('#skF_9', '#skF_11'))!='#skF_10'), inference(demodulation, [status(thm), theory('equality')], [c_230, c_90])).
% 23.84/15.95  tff(c_109700, plain, (~r2_hidden('#skF_11', '#skF_10') | ~r2_hidden('#skF_9', '#skF_10')), inference(superposition, [status(thm), theory('equality')], [c_109642, c_247])).
% 23.84/15.95  tff(c_109791, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_94, c_92, c_109700])).
% 23.84/15.95  tff(c_109792, plain, (![A_120]: (r2_hidden('#skF_1'(k1_xboole_0), A_120))), inference(splitRight, [status(thm)], [c_689])).
% 23.84/15.95  tff(c_109794, plain, (![A_1894]: (r2_hidden('#skF_1'(k1_xboole_0), A_1894))), inference(splitRight, [status(thm)], [c_689])).
% 23.84/15.95  tff(c_28, plain, (![D_18, B_14, A_13]: (~r2_hidden(D_18, B_14) | ~r2_hidden(D_18, k4_xboole_0(A_13, B_14)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 23.84/15.95  tff(c_109809, plain, (![B_14]: (~r2_hidden('#skF_1'(k1_xboole_0), B_14))), inference(resolution, [status(thm)], [c_109794, c_28])).
% 23.84/15.95  tff(c_109832, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_109792, c_109809])).
% 23.84/15.95  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 23.84/15.95  
% 23.84/15.95  Inference rules
% 23.84/15.95  ----------------------
% 23.84/15.95  #Ref     : 0
% 23.84/15.95  #Sup     : 29646
% 23.84/15.95  #Fact    : 0
% 23.84/15.95  #Define  : 0
% 23.84/15.95  #Split   : 5
% 23.84/15.95  #Chain   : 0
% 23.84/15.95  #Close   : 0
% 23.84/15.95  
% 23.84/15.95  Ordering : KBO
% 23.84/15.95  
% 23.84/15.95  Simplification rules
% 23.84/15.95  ----------------------
% 23.84/15.95  #Subsume      : 10425
% 23.84/15.95  #Demod        : 18414
% 23.84/15.95  #Tautology    : 10717
% 23.84/15.95  #SimpNegUnit  : 226
% 23.84/15.95  #BackRed      : 24
% 23.84/15.95  
% 23.84/15.95  #Partial instantiations: 0
% 23.84/15.95  #Strategies tried      : 1
% 23.84/15.95  
% 23.84/15.95  Timing (in seconds)
% 23.84/15.95  ----------------------
% 23.84/15.95  Preprocessing        : 0.34
% 23.84/15.95  Parsing              : 0.17
% 23.84/15.95  CNF conversion       : 0.03
% 23.84/15.95  Main loop            : 14.80
% 23.84/15.95  Inferencing          : 2.25
% 23.84/15.95  Reduction            : 3.66
% 23.84/15.95  Demodulation         : 2.73
% 23.84/15.95  BG Simplification    : 0.24
% 23.84/15.95  Subsumption          : 7.96
% 23.84/15.95  Abstraction          : 0.37
% 23.84/15.95  MUC search           : 0.00
% 23.84/15.95  Cooper               : 0.00
% 23.84/15.95  Total                : 15.18
% 23.84/15.95  Index Insertion      : 0.00
% 23.84/15.95  Index Deletion       : 0.00
% 23.84/15.95  Index Matching       : 0.00
% 23.84/15.95  BG Taut test         : 0.00
%------------------------------------------------------------------------------
