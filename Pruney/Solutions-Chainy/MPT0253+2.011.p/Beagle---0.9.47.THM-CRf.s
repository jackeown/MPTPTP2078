%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:51:15 EST 2020

% Result     : Theorem 6.10s
% Output     : CNFRefutation 6.10s
% Verified   : 
% Statistics : Number of formulae       :   91 ( 165 expanded)
%              Number of leaves         :   37 (  72 expanded)
%              Depth                    :   17
%              Number of atoms          :  111 ( 215 expanded)
%              Number of equality atoms :   42 ( 102 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_xboole_0 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_xboole_0 > #skF_1 > #skF_7 > #skF_6 > #skF_2 > #skF_8 > #skF_3 > #skF_5 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

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

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_91,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( r2_hidden(A,B)
          & r2_hidden(C,B) )
       => k2_xboole_0(k2_tarski(A,C),B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_zfmisc_1)).

tff(f_58,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_68,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_54,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_84,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_tarski(A,B),C)
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_zfmisc_1)).

tff(f_78,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_66,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_48,axiom,(
    ! [A,B] :
      ( ! [C] :
          ( r2_hidden(C,A)
        <=> r2_hidden(C,B) )
     => A = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tarski)).

tff(f_64,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_56,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(c_68,plain,(
    r2_hidden('#skF_8','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_70,plain,(
    r2_hidden('#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_40,plain,(
    ! [A_18] : k2_xboole_0(A_18,k1_xboole_0) = A_18 ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_493,plain,(
    ! [D_92,A_93,B_94] :
      ( r2_hidden(D_92,A_93)
      | ~ r2_hidden(D_92,k4_xboole_0(A_93,B_94)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_757,plain,(
    ! [A_122,B_123] :
      ( r2_hidden('#skF_1'(k4_xboole_0(A_122,B_123)),A_122)
      | v1_xboole_0(k4_xboole_0(A_122,B_123)) ) ),
    inference(resolution,[status(thm)],[c_4,c_493])).

tff(c_180,plain,(
    ! [D_62,B_63,A_64] :
      ( ~ r2_hidden(D_62,B_63)
      | ~ r2_hidden(D_62,k4_xboole_0(A_64,B_63)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_185,plain,(
    ! [A_64,B_63] :
      ( ~ r2_hidden('#skF_1'(k4_xboole_0(A_64,B_63)),B_63)
      | v1_xboole_0(k4_xboole_0(A_64,B_63)) ) ),
    inference(resolution,[status(thm)],[c_4,c_180])).

tff(c_788,plain,(
    ! [A_122] : v1_xboole_0(k4_xboole_0(A_122,A_122)) ),
    inference(resolution,[status(thm)],[c_757,c_185])).

tff(c_48,plain,(
    ! [B_26,A_25] : k2_tarski(B_26,A_25) = k2_tarski(A_25,B_26) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_36,plain,(
    ! [B_15] : r1_tarski(B_15,B_15) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_355,plain,(
    ! [A_72,C_73,B_74] :
      ( r2_hidden(A_72,C_73)
      | ~ r1_tarski(k2_tarski(A_72,B_74),C_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_368,plain,(
    ! [A_75,B_76] : r2_hidden(A_75,k2_tarski(A_75,B_76)) ),
    inference(resolution,[status(thm)],[c_36,c_355])).

tff(c_374,plain,(
    ! [A_25,B_26] : r2_hidden(A_25,k2_tarski(B_26,A_25)) ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_368])).

tff(c_148,plain,(
    ! [A_57,B_58] : k3_tarski(k2_tarski(A_57,B_58)) = k2_xboole_0(A_57,B_58) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_205,plain,(
    ! [A_66,B_67] : k3_tarski(k2_tarski(A_66,B_67)) = k2_xboole_0(B_67,A_66) ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_148])).

tff(c_58,plain,(
    ! [A_41,B_42] : k3_tarski(k2_tarski(A_41,B_42)) = k2_xboole_0(A_41,B_42) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_229,plain,(
    ! [B_68,A_69] : k2_xboole_0(B_68,A_69) = k2_xboole_0(A_69,B_68) ),
    inference(superposition,[status(thm),theory(equality)],[c_205,c_58])).

tff(c_245,plain,(
    ! [A_69] : k2_xboole_0(k1_xboole_0,A_69) = A_69 ),
    inference(superposition,[status(thm),theory(equality)],[c_229,c_40])).

tff(c_509,plain,(
    ! [A_95,B_96] : k2_xboole_0(A_95,k4_xboole_0(B_96,A_95)) = k2_xboole_0(A_95,B_96) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_516,plain,(
    ! [B_96] : k4_xboole_0(B_96,k1_xboole_0) = k2_xboole_0(k1_xboole_0,B_96) ),
    inference(superposition,[status(thm),theory(equality)],[c_509,c_245])).

tff(c_540,plain,(
    ! [B_97] : k4_xboole_0(B_97,k1_xboole_0) = B_97 ),
    inference(demodulation,[status(thm),theory(equality)],[c_245,c_516])).

tff(c_8,plain,(
    ! [D_10,B_6,A_5] :
      ( ~ r2_hidden(D_10,B_6)
      | ~ r2_hidden(D_10,k4_xboole_0(A_5,B_6)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_638,plain,(
    ! [D_106,B_107] :
      ( ~ r2_hidden(D_106,k1_xboole_0)
      | ~ r2_hidden(D_106,B_107) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_540,c_8])).

tff(c_642,plain,(
    ! [B_107] :
      ( ~ r2_hidden('#skF_1'(k1_xboole_0),B_107)
      | v1_xboole_0(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_4,c_638])).

tff(c_667,plain,(
    ! [B_111] : ~ r2_hidden('#skF_1'(k1_xboole_0),B_111) ),
    inference(splitLeft,[status(thm)],[c_642])).

tff(c_679,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_374,c_667])).

tff(c_680,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_642])).

tff(c_848,plain,(
    ! [A_134,B_135] :
      ( r2_hidden('#skF_4'(A_134,B_135),B_135)
      | r2_hidden('#skF_5'(A_134,B_135),A_134)
      | B_135 = A_134 ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_903,plain,(
    ! [B_141,A_142] :
      ( ~ v1_xboole_0(B_141)
      | r2_hidden('#skF_5'(A_142,B_141),A_142)
      | B_141 = A_142 ) ),
    inference(resolution,[status(thm)],[c_848,c_2])).

tff(c_932,plain,(
    ! [A_143,B_144] :
      ( ~ v1_xboole_0(A_143)
      | ~ v1_xboole_0(B_144)
      | B_144 = A_143 ) ),
    inference(resolution,[status(thm)],[c_903,c_2])).

tff(c_942,plain,(
    ! [B_145] :
      ( ~ v1_xboole_0(B_145)
      | k1_xboole_0 = B_145 ) ),
    inference(resolution,[status(thm)],[c_680,c_932])).

tff(c_953,plain,(
    ! [A_122] : k4_xboole_0(A_122,A_122) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_788,c_942])).

tff(c_163,plain,(
    ! [A_59,B_60] :
      ( k3_xboole_0(A_59,B_60) = A_59
      | ~ r1_tarski(A_59,B_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_167,plain,(
    ! [B_15] : k3_xboole_0(B_15,B_15) = B_15 ),
    inference(resolution,[status(thm)],[c_36,c_163])).

tff(c_419,plain,(
    ! [A_86,B_87] : k5_xboole_0(A_86,k3_xboole_0(A_86,B_87)) = k4_xboole_0(A_86,B_87) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_431,plain,(
    ! [B_15] : k5_xboole_0(B_15,B_15) = k4_xboole_0(B_15,B_15) ),
    inference(superposition,[status(thm),theory(equality)],[c_167,c_419])).

tff(c_957,plain,(
    ! [B_15] : k5_xboole_0(B_15,B_15) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_953,c_431])).

tff(c_644,plain,(
    ! [A_108,B_109,C_110] :
      ( r1_tarski(k2_tarski(A_108,B_109),C_110)
      | ~ r2_hidden(B_109,C_110)
      | ~ r2_hidden(A_108,C_110) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_44,plain,(
    ! [A_21,B_22] :
      ( k3_xboole_0(A_21,B_22) = A_21
      | ~ r1_tarski(A_21,B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_2222,plain,(
    ! [A_239,B_240,C_241] :
      ( k3_xboole_0(k2_tarski(A_239,B_240),C_241) = k2_tarski(A_239,B_240)
      | ~ r2_hidden(B_240,C_241)
      | ~ r2_hidden(A_239,C_241) ) ),
    inference(resolution,[status(thm)],[c_644,c_44])).

tff(c_38,plain,(
    ! [A_16,B_17] : k5_xboole_0(A_16,k3_xboole_0(A_16,B_17)) = k4_xboole_0(A_16,B_17) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_2228,plain,(
    ! [A_239,B_240,C_241] :
      ( k5_xboole_0(k2_tarski(A_239,B_240),k2_tarski(A_239,B_240)) = k4_xboole_0(k2_tarski(A_239,B_240),C_241)
      | ~ r2_hidden(B_240,C_241)
      | ~ r2_hidden(A_239,C_241) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2222,c_38])).

tff(c_5707,plain,(
    ! [A_352,B_353,C_354] :
      ( k4_xboole_0(k2_tarski(A_352,B_353),C_354) = k1_xboole_0
      | ~ r2_hidden(B_353,C_354)
      | ~ r2_hidden(A_352,C_354) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_957,c_2228])).

tff(c_46,plain,(
    ! [A_23,B_24] : k2_xboole_0(A_23,k4_xboole_0(B_24,A_23)) = k2_xboole_0(A_23,B_24) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_5851,plain,(
    ! [C_354,A_352,B_353] :
      ( k2_xboole_0(C_354,k2_tarski(A_352,B_353)) = k2_xboole_0(C_354,k1_xboole_0)
      | ~ r2_hidden(B_353,C_354)
      | ~ r2_hidden(A_352,C_354) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5707,c_46])).

tff(c_6396,plain,(
    ! [C_361,A_362,B_363] :
      ( k2_xboole_0(C_361,k2_tarski(A_362,B_363)) = C_361
      | ~ r2_hidden(B_363,C_361)
      | ~ r2_hidden(A_362,C_361) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_5851])).

tff(c_211,plain,(
    ! [B_67,A_66] : k2_xboole_0(B_67,A_66) = k2_xboole_0(A_66,B_67) ),
    inference(superposition,[status(thm),theory(equality)],[c_205,c_58])).

tff(c_66,plain,(
    k2_xboole_0(k2_tarski('#skF_6','#skF_8'),'#skF_7') != '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_71,plain,(
    k2_xboole_0(k2_tarski('#skF_8','#skF_6'),'#skF_7') != '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_66])).

tff(c_228,plain,(
    k2_xboole_0('#skF_7',k2_tarski('#skF_8','#skF_6')) != '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_211,c_71])).

tff(c_6414,plain,
    ( ~ r2_hidden('#skF_6','#skF_7')
    | ~ r2_hidden('#skF_8','#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_6396,c_228])).

tff(c_6462,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_70,c_6414])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n021.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 12:28:49 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.10/2.25  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.10/2.26  
% 6.10/2.26  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.10/2.26  %$ r2_hidden > r1_tarski > v1_xboole_0 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_xboole_0 > #skF_1 > #skF_7 > #skF_6 > #skF_2 > #skF_8 > #skF_3 > #skF_5 > #skF_4
% 6.10/2.26  
% 6.10/2.26  %Foreground sorts:
% 6.10/2.26  
% 6.10/2.26  
% 6.10/2.26  %Background operators:
% 6.10/2.26  
% 6.10/2.26  
% 6.10/2.26  %Foreground operators:
% 6.10/2.26  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.10/2.26  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 6.10/2.26  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 6.10/2.26  tff('#skF_1', type, '#skF_1': $i > $i).
% 6.10/2.26  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 6.10/2.26  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 6.10/2.26  tff('#skF_7', type, '#skF_7': $i).
% 6.10/2.26  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 6.10/2.26  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.10/2.26  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 6.10/2.26  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 6.10/2.26  tff('#skF_6', type, '#skF_6': $i).
% 6.10/2.26  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 6.10/2.26  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 6.10/2.26  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 6.10/2.26  tff('#skF_8', type, '#skF_8': $i).
% 6.10/2.26  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.10/2.26  tff(k3_tarski, type, k3_tarski: $i > $i).
% 6.10/2.26  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 6.10/2.26  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.10/2.26  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 6.10/2.26  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 6.10/2.26  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 6.10/2.26  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 6.10/2.26  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 6.10/2.26  
% 6.10/2.28  tff(f_91, negated_conjecture, ~(![A, B, C]: ((r2_hidden(A, B) & r2_hidden(C, B)) => (k2_xboole_0(k2_tarski(A, C), B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_zfmisc_1)).
% 6.10/2.28  tff(f_58, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 6.10/2.28  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 6.10/2.28  tff(f_41, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_xboole_0)).
% 6.10/2.28  tff(f_68, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 6.10/2.28  tff(f_54, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 6.10/2.28  tff(f_84, axiom, (![A, B, C]: (r1_tarski(k2_tarski(A, B), C) <=> (r2_hidden(A, C) & r2_hidden(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 6.10/2.28  tff(f_78, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 6.10/2.28  tff(f_66, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_xboole_1)).
% 6.10/2.28  tff(f_48, axiom, (![A, B]: ((![C]: (r2_hidden(C, A) <=> r2_hidden(C, B))) => (A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_tarski)).
% 6.10/2.28  tff(f_64, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 6.10/2.28  tff(f_56, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 6.10/2.28  tff(c_68, plain, (r2_hidden('#skF_8', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_91])).
% 6.10/2.28  tff(c_70, plain, (r2_hidden('#skF_6', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_91])).
% 6.10/2.28  tff(c_40, plain, (![A_18]: (k2_xboole_0(A_18, k1_xboole_0)=A_18)), inference(cnfTransformation, [status(thm)], [f_58])).
% 6.10/2.28  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 6.10/2.28  tff(c_493, plain, (![D_92, A_93, B_94]: (r2_hidden(D_92, A_93) | ~r2_hidden(D_92, k4_xboole_0(A_93, B_94)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 6.10/2.28  tff(c_757, plain, (![A_122, B_123]: (r2_hidden('#skF_1'(k4_xboole_0(A_122, B_123)), A_122) | v1_xboole_0(k4_xboole_0(A_122, B_123)))), inference(resolution, [status(thm)], [c_4, c_493])).
% 6.10/2.28  tff(c_180, plain, (![D_62, B_63, A_64]: (~r2_hidden(D_62, B_63) | ~r2_hidden(D_62, k4_xboole_0(A_64, B_63)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 6.10/2.28  tff(c_185, plain, (![A_64, B_63]: (~r2_hidden('#skF_1'(k4_xboole_0(A_64, B_63)), B_63) | v1_xboole_0(k4_xboole_0(A_64, B_63)))), inference(resolution, [status(thm)], [c_4, c_180])).
% 6.10/2.28  tff(c_788, plain, (![A_122]: (v1_xboole_0(k4_xboole_0(A_122, A_122)))), inference(resolution, [status(thm)], [c_757, c_185])).
% 6.10/2.28  tff(c_48, plain, (![B_26, A_25]: (k2_tarski(B_26, A_25)=k2_tarski(A_25, B_26))), inference(cnfTransformation, [status(thm)], [f_68])).
% 6.10/2.28  tff(c_36, plain, (![B_15]: (r1_tarski(B_15, B_15))), inference(cnfTransformation, [status(thm)], [f_54])).
% 6.10/2.28  tff(c_355, plain, (![A_72, C_73, B_74]: (r2_hidden(A_72, C_73) | ~r1_tarski(k2_tarski(A_72, B_74), C_73))), inference(cnfTransformation, [status(thm)], [f_84])).
% 6.10/2.28  tff(c_368, plain, (![A_75, B_76]: (r2_hidden(A_75, k2_tarski(A_75, B_76)))), inference(resolution, [status(thm)], [c_36, c_355])).
% 6.10/2.28  tff(c_374, plain, (![A_25, B_26]: (r2_hidden(A_25, k2_tarski(B_26, A_25)))), inference(superposition, [status(thm), theory('equality')], [c_48, c_368])).
% 6.10/2.28  tff(c_148, plain, (![A_57, B_58]: (k3_tarski(k2_tarski(A_57, B_58))=k2_xboole_0(A_57, B_58))), inference(cnfTransformation, [status(thm)], [f_78])).
% 6.10/2.28  tff(c_205, plain, (![A_66, B_67]: (k3_tarski(k2_tarski(A_66, B_67))=k2_xboole_0(B_67, A_66))), inference(superposition, [status(thm), theory('equality')], [c_48, c_148])).
% 6.10/2.28  tff(c_58, plain, (![A_41, B_42]: (k3_tarski(k2_tarski(A_41, B_42))=k2_xboole_0(A_41, B_42))), inference(cnfTransformation, [status(thm)], [f_78])).
% 6.10/2.28  tff(c_229, plain, (![B_68, A_69]: (k2_xboole_0(B_68, A_69)=k2_xboole_0(A_69, B_68))), inference(superposition, [status(thm), theory('equality')], [c_205, c_58])).
% 6.10/2.28  tff(c_245, plain, (![A_69]: (k2_xboole_0(k1_xboole_0, A_69)=A_69)), inference(superposition, [status(thm), theory('equality')], [c_229, c_40])).
% 6.10/2.28  tff(c_509, plain, (![A_95, B_96]: (k2_xboole_0(A_95, k4_xboole_0(B_96, A_95))=k2_xboole_0(A_95, B_96))), inference(cnfTransformation, [status(thm)], [f_66])).
% 6.10/2.28  tff(c_516, plain, (![B_96]: (k4_xboole_0(B_96, k1_xboole_0)=k2_xboole_0(k1_xboole_0, B_96))), inference(superposition, [status(thm), theory('equality')], [c_509, c_245])).
% 6.10/2.28  tff(c_540, plain, (![B_97]: (k4_xboole_0(B_97, k1_xboole_0)=B_97)), inference(demodulation, [status(thm), theory('equality')], [c_245, c_516])).
% 6.10/2.28  tff(c_8, plain, (![D_10, B_6, A_5]: (~r2_hidden(D_10, B_6) | ~r2_hidden(D_10, k4_xboole_0(A_5, B_6)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 6.10/2.28  tff(c_638, plain, (![D_106, B_107]: (~r2_hidden(D_106, k1_xboole_0) | ~r2_hidden(D_106, B_107))), inference(superposition, [status(thm), theory('equality')], [c_540, c_8])).
% 6.10/2.28  tff(c_642, plain, (![B_107]: (~r2_hidden('#skF_1'(k1_xboole_0), B_107) | v1_xboole_0(k1_xboole_0))), inference(resolution, [status(thm)], [c_4, c_638])).
% 6.10/2.28  tff(c_667, plain, (![B_111]: (~r2_hidden('#skF_1'(k1_xboole_0), B_111))), inference(splitLeft, [status(thm)], [c_642])).
% 6.10/2.28  tff(c_679, plain, $false, inference(resolution, [status(thm)], [c_374, c_667])).
% 6.10/2.28  tff(c_680, plain, (v1_xboole_0(k1_xboole_0)), inference(splitRight, [status(thm)], [c_642])).
% 6.10/2.28  tff(c_848, plain, (![A_134, B_135]: (r2_hidden('#skF_4'(A_134, B_135), B_135) | r2_hidden('#skF_5'(A_134, B_135), A_134) | B_135=A_134)), inference(cnfTransformation, [status(thm)], [f_48])).
% 6.10/2.28  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 6.10/2.28  tff(c_903, plain, (![B_141, A_142]: (~v1_xboole_0(B_141) | r2_hidden('#skF_5'(A_142, B_141), A_142) | B_141=A_142)), inference(resolution, [status(thm)], [c_848, c_2])).
% 6.10/2.28  tff(c_932, plain, (![A_143, B_144]: (~v1_xboole_0(A_143) | ~v1_xboole_0(B_144) | B_144=A_143)), inference(resolution, [status(thm)], [c_903, c_2])).
% 6.10/2.28  tff(c_942, plain, (![B_145]: (~v1_xboole_0(B_145) | k1_xboole_0=B_145)), inference(resolution, [status(thm)], [c_680, c_932])).
% 6.10/2.28  tff(c_953, plain, (![A_122]: (k4_xboole_0(A_122, A_122)=k1_xboole_0)), inference(resolution, [status(thm)], [c_788, c_942])).
% 6.10/2.28  tff(c_163, plain, (![A_59, B_60]: (k3_xboole_0(A_59, B_60)=A_59 | ~r1_tarski(A_59, B_60))), inference(cnfTransformation, [status(thm)], [f_64])).
% 6.10/2.28  tff(c_167, plain, (![B_15]: (k3_xboole_0(B_15, B_15)=B_15)), inference(resolution, [status(thm)], [c_36, c_163])).
% 6.10/2.28  tff(c_419, plain, (![A_86, B_87]: (k5_xboole_0(A_86, k3_xboole_0(A_86, B_87))=k4_xboole_0(A_86, B_87))), inference(cnfTransformation, [status(thm)], [f_56])).
% 6.10/2.28  tff(c_431, plain, (![B_15]: (k5_xboole_0(B_15, B_15)=k4_xboole_0(B_15, B_15))), inference(superposition, [status(thm), theory('equality')], [c_167, c_419])).
% 6.10/2.28  tff(c_957, plain, (![B_15]: (k5_xboole_0(B_15, B_15)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_953, c_431])).
% 6.10/2.28  tff(c_644, plain, (![A_108, B_109, C_110]: (r1_tarski(k2_tarski(A_108, B_109), C_110) | ~r2_hidden(B_109, C_110) | ~r2_hidden(A_108, C_110))), inference(cnfTransformation, [status(thm)], [f_84])).
% 6.10/2.28  tff(c_44, plain, (![A_21, B_22]: (k3_xboole_0(A_21, B_22)=A_21 | ~r1_tarski(A_21, B_22))), inference(cnfTransformation, [status(thm)], [f_64])).
% 6.10/2.28  tff(c_2222, plain, (![A_239, B_240, C_241]: (k3_xboole_0(k2_tarski(A_239, B_240), C_241)=k2_tarski(A_239, B_240) | ~r2_hidden(B_240, C_241) | ~r2_hidden(A_239, C_241))), inference(resolution, [status(thm)], [c_644, c_44])).
% 6.10/2.28  tff(c_38, plain, (![A_16, B_17]: (k5_xboole_0(A_16, k3_xboole_0(A_16, B_17))=k4_xboole_0(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_56])).
% 6.10/2.28  tff(c_2228, plain, (![A_239, B_240, C_241]: (k5_xboole_0(k2_tarski(A_239, B_240), k2_tarski(A_239, B_240))=k4_xboole_0(k2_tarski(A_239, B_240), C_241) | ~r2_hidden(B_240, C_241) | ~r2_hidden(A_239, C_241))), inference(superposition, [status(thm), theory('equality')], [c_2222, c_38])).
% 6.10/2.28  tff(c_5707, plain, (![A_352, B_353, C_354]: (k4_xboole_0(k2_tarski(A_352, B_353), C_354)=k1_xboole_0 | ~r2_hidden(B_353, C_354) | ~r2_hidden(A_352, C_354))), inference(demodulation, [status(thm), theory('equality')], [c_957, c_2228])).
% 6.10/2.28  tff(c_46, plain, (![A_23, B_24]: (k2_xboole_0(A_23, k4_xboole_0(B_24, A_23))=k2_xboole_0(A_23, B_24))), inference(cnfTransformation, [status(thm)], [f_66])).
% 6.10/2.28  tff(c_5851, plain, (![C_354, A_352, B_353]: (k2_xboole_0(C_354, k2_tarski(A_352, B_353))=k2_xboole_0(C_354, k1_xboole_0) | ~r2_hidden(B_353, C_354) | ~r2_hidden(A_352, C_354))), inference(superposition, [status(thm), theory('equality')], [c_5707, c_46])).
% 6.10/2.28  tff(c_6396, plain, (![C_361, A_362, B_363]: (k2_xboole_0(C_361, k2_tarski(A_362, B_363))=C_361 | ~r2_hidden(B_363, C_361) | ~r2_hidden(A_362, C_361))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_5851])).
% 6.10/2.28  tff(c_211, plain, (![B_67, A_66]: (k2_xboole_0(B_67, A_66)=k2_xboole_0(A_66, B_67))), inference(superposition, [status(thm), theory('equality')], [c_205, c_58])).
% 6.10/2.28  tff(c_66, plain, (k2_xboole_0(k2_tarski('#skF_6', '#skF_8'), '#skF_7')!='#skF_7'), inference(cnfTransformation, [status(thm)], [f_91])).
% 6.10/2.28  tff(c_71, plain, (k2_xboole_0(k2_tarski('#skF_8', '#skF_6'), '#skF_7')!='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_48, c_66])).
% 6.10/2.28  tff(c_228, plain, (k2_xboole_0('#skF_7', k2_tarski('#skF_8', '#skF_6'))!='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_211, c_71])).
% 6.10/2.28  tff(c_6414, plain, (~r2_hidden('#skF_6', '#skF_7') | ~r2_hidden('#skF_8', '#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_6396, c_228])).
% 6.10/2.28  tff(c_6462, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_68, c_70, c_6414])).
% 6.10/2.28  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.10/2.28  
% 6.10/2.28  Inference rules
% 6.10/2.28  ----------------------
% 6.10/2.28  #Ref     : 0
% 6.10/2.28  #Sup     : 1658
% 6.10/2.28  #Fact    : 0
% 6.10/2.28  #Define  : 0
% 6.10/2.28  #Split   : 2
% 6.10/2.28  #Chain   : 0
% 6.10/2.28  #Close   : 0
% 6.10/2.28  
% 6.10/2.28  Ordering : KBO
% 6.10/2.28  
% 6.10/2.28  Simplification rules
% 6.10/2.28  ----------------------
% 6.10/2.28  #Subsume      : 705
% 6.10/2.28  #Demod        : 501
% 6.10/2.28  #Tautology    : 435
% 6.10/2.28  #SimpNegUnit  : 25
% 6.10/2.28  #BackRed      : 5
% 6.10/2.28  
% 6.10/2.28  #Partial instantiations: 0
% 6.10/2.28  #Strategies tried      : 1
% 6.10/2.28  
% 6.10/2.28  Timing (in seconds)
% 6.10/2.28  ----------------------
% 6.10/2.28  Preprocessing        : 0.34
% 6.10/2.28  Parsing              : 0.18
% 6.10/2.28  CNF conversion       : 0.03
% 6.10/2.28  Main loop            : 1.13
% 6.10/2.28  Inferencing          : 0.37
% 6.10/2.28  Reduction            : 0.35
% 6.10/2.28  Demodulation         : 0.25
% 6.10/2.28  BG Simplification    : 0.04
% 6.10/2.28  Subsumption          : 0.30
% 6.10/2.28  Abstraction          : 0.06
% 6.10/2.28  MUC search           : 0.00
% 6.10/2.28  Cooper               : 0.00
% 6.10/2.28  Total                : 1.50
% 6.10/2.28  Index Insertion      : 0.00
% 6.10/2.28  Index Deletion       : 0.00
% 6.10/2.28  Index Matching       : 0.00
% 6.10/2.28  BG Taut test         : 0.00
%------------------------------------------------------------------------------
