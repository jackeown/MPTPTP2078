%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:55:03 EST 2020

% Result     : Theorem 7.94s
% Output     : CNFRefutation 7.94s
% Verified   : 
% Statistics : Number of formulae       :   83 ( 179 expanded)
%              Number of leaves         :   32 (  74 expanded)
%              Depth                    :   14
%              Number of atoms          :  116 ( 323 expanded)
%              Number of equality atoms :   27 (  77 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_1 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_4

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

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

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

tff(f_110,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( r1_tarski(k3_xboole_0(A,B),k1_tarski(D))
          & r2_hidden(D,C)
          & r1_xboole_0(C,B) )
       => r1_xboole_0(k2_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t149_zfmisc_1)).

tff(f_40,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_58,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_36,axiom,(
    ! [A,B,C] :
      ( C = k3_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

tff(f_64,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_70,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_99,axiom,(
    ! [A,B] :
      ( ~ r2_hidden(A,B)
     => r1_xboole_0(k1_tarski(A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l27_zfmisc_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_66,axiom,(
    ! [A,B,C] : k3_xboole_0(k3_xboole_0(A,B),C) = k3_xboole_0(A,k3_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_xboole_1)).

tff(f_88,axiom,(
    ! [A,B,C] :
      ( ~ ( ~ r1_xboole_0(A,k2_xboole_0(B,C))
          & r1_xboole_0(A,B)
          & r1_xboole_0(A,C) )
      & ~ ( ~ ( r1_xboole_0(A,B)
              & r1_xboole_0(A,C) )
          & r1_xboole_0(A,k2_xboole_0(B,C)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_xboole_1)).

tff(c_62,plain,(
    r1_xboole_0('#skF_6','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_213,plain,(
    ! [A_59,B_60] :
      ( k3_xboole_0(A_59,B_60) = k1_xboole_0
      | ~ r1_xboole_0(A_59,B_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_237,plain,(
    k3_xboole_0('#skF_6','#skF_5') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_62,c_213])).

tff(c_412,plain,(
    ! [A_76,B_77,C_78] :
      ( ~ r1_xboole_0(A_76,B_77)
      | ~ r2_hidden(C_78,k3_xboole_0(A_76,B_77)) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_421,plain,(
    ! [C_78] :
      ( ~ r1_xboole_0('#skF_6','#skF_5')
      | ~ r2_hidden(C_78,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_237,c_412])).

tff(c_442,plain,(
    ! [C_78] : ~ r2_hidden(C_78,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_421])).

tff(c_64,plain,(
    r2_hidden('#skF_7','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_761,plain,(
    ! [A_106,B_107] :
      ( r2_hidden('#skF_3'(A_106,B_107),k3_xboole_0(A_106,B_107))
      | r1_xboole_0(A_106,B_107) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_8,plain,(
    ! [D_8,A_3,B_4] :
      ( r2_hidden(D_8,A_3)
      | ~ r2_hidden(D_8,k3_xboole_0(A_3,B_4)) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_830,plain,(
    ! [A_108,B_109] :
      ( r2_hidden('#skF_3'(A_108,B_109),A_108)
      | r1_xboole_0(A_108,B_109) ) ),
    inference(resolution,[status(thm)],[c_761,c_8])).

tff(c_36,plain,(
    ! [B_19] : r1_tarski(B_19,B_19) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_179,plain,(
    ! [A_56,B_57] :
      ( k3_xboole_0(A_56,B_57) = A_56
      | ~ r1_tarski(A_56,B_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_187,plain,(
    ! [B_19] : k3_xboole_0(B_19,B_19) = B_19 ),
    inference(resolution,[status(thm)],[c_36,c_179])).

tff(c_170,plain,(
    ! [A_54,B_55] :
      ( r1_xboole_0(A_54,B_55)
      | k3_xboole_0(A_54,B_55) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_26,plain,(
    ! [B_12,A_11] :
      ( r1_xboole_0(B_12,A_11)
      | ~ r1_xboole_0(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_176,plain,(
    ! [B_55,A_54] :
      ( r1_xboole_0(B_55,A_54)
      | k3_xboole_0(A_54,B_55) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_170,c_26])).

tff(c_447,plain,(
    ! [B_81,C_82] :
      ( ~ r1_xboole_0(B_81,B_81)
      | ~ r2_hidden(C_82,B_81) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_187,c_412])).

tff(c_450,plain,(
    ! [C_82,A_54] :
      ( ~ r2_hidden(C_82,A_54)
      | k3_xboole_0(A_54,A_54) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_176,c_447])).

tff(c_467,plain,(
    ! [C_82,A_54] :
      ( ~ r2_hidden(C_82,A_54)
      | k1_xboole_0 != A_54 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_187,c_450])).

tff(c_868,plain,(
    ! [A_110,B_111] :
      ( k1_xboole_0 != A_110
      | r1_xboole_0(A_110,B_111) ) ),
    inference(resolution,[status(thm)],[c_830,c_467])).

tff(c_902,plain,(
    ! [B_112,A_113] :
      ( r1_xboole_0(B_112,A_113)
      | k1_xboole_0 != A_113 ) ),
    inference(resolution,[status(thm)],[c_868,c_26])).

tff(c_22,plain,(
    ! [A_9,B_10] :
      ( k3_xboole_0(A_9,B_10) = k1_xboole_0
      | ~ r1_xboole_0(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_1050,plain,(
    ! [B_112] : k3_xboole_0(B_112,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_902,c_22])).

tff(c_56,plain,(
    ! [A_35,B_36] :
      ( r1_xboole_0(k1_tarski(A_35),B_36)
      | r2_hidden(A_35,B_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_574,plain,(
    ! [A_96,B_97] :
      ( k3_xboole_0(k1_tarski(A_96),B_97) = k1_xboole_0
      | r2_hidden(A_96,B_97) ) ),
    inference(resolution,[status(thm)],[c_56,c_213])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_603,plain,(
    ! [B_97,A_96] :
      ( k3_xboole_0(B_97,k1_tarski(A_96)) = k1_xboole_0
      | r2_hidden(A_96,B_97) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_574,c_2])).

tff(c_66,plain,(
    r1_tarski(k3_xboole_0('#skF_4','#skF_5'),k1_tarski('#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_186,plain,(
    k3_xboole_0(k3_xboole_0('#skF_4','#skF_5'),k1_tarski('#skF_7')) = k3_xboole_0('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_66,c_179])).

tff(c_1167,plain,(
    ! [A_118,B_119,C_120] : k3_xboole_0(k3_xboole_0(A_118,B_119),C_120) = k3_xboole_0(A_118,k3_xboole_0(B_119,C_120)) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_1256,plain,(
    k3_xboole_0('#skF_4',k3_xboole_0('#skF_5',k1_tarski('#skF_7'))) = k3_xboole_0('#skF_4','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_186,c_1167])).

tff(c_2154,plain,
    ( k3_xboole_0('#skF_4',k1_xboole_0) = k3_xboole_0('#skF_4','#skF_5')
    | r2_hidden('#skF_7','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_603,c_1256])).

tff(c_2160,plain,
    ( k3_xboole_0('#skF_4','#skF_5') = k1_xboole_0
    | r2_hidden('#skF_7','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1050,c_2154])).

tff(c_2845,plain,(
    r2_hidden('#skF_7','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_2160])).

tff(c_1813,plain,(
    ! [D_134,A_135,B_136] :
      ( r2_hidden(D_134,k3_xboole_0(A_135,B_136))
      | ~ r2_hidden(D_134,B_136)
      | ~ r2_hidden(D_134,A_135) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_1862,plain,(
    ! [D_134] :
      ( r2_hidden(D_134,k1_xboole_0)
      | ~ r2_hidden(D_134,'#skF_5')
      | ~ r2_hidden(D_134,'#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_237,c_1813])).

tff(c_1888,plain,(
    ! [D_134] :
      ( ~ r2_hidden(D_134,'#skF_5')
      | ~ r2_hidden(D_134,'#skF_6') ) ),
    inference(negUnitSimplification,[status(thm)],[c_442,c_1862])).

tff(c_2849,plain,(
    ~ r2_hidden('#skF_7','#skF_6') ),
    inference(resolution,[status(thm)],[c_2845,c_1888])).

tff(c_2856,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_2849])).

tff(c_2857,plain,(
    k3_xboole_0('#skF_4','#skF_5') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_2160])).

tff(c_28,plain,(
    ! [A_13,B_14] :
      ( r2_hidden('#skF_3'(A_13,B_14),k3_xboole_0(A_13,B_14))
      | r1_xboole_0(A_13,B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_2890,plain,
    ( r2_hidden('#skF_3'('#skF_4','#skF_5'),k1_xboole_0)
    | r1_xboole_0('#skF_4','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_2857,c_28])).

tff(c_2917,plain,(
    r1_xboole_0('#skF_4','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_442,c_2890])).

tff(c_2926,plain,(
    r1_xboole_0('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_2917,c_26])).

tff(c_79,plain,(
    ! [B_42,A_43] :
      ( r1_xboole_0(B_42,A_43)
      | ~ r1_xboole_0(A_43,B_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_85,plain,(
    r1_xboole_0('#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_62,c_79])).

tff(c_1531,plain,(
    ! [A_126,C_127,B_128] :
      ( ~ r1_xboole_0(A_126,C_127)
      | ~ r1_xboole_0(A_126,B_128)
      | r1_xboole_0(A_126,k2_xboole_0(B_128,C_127)) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_14324,plain,(
    ! [B_312,C_313,A_314] :
      ( r1_xboole_0(k2_xboole_0(B_312,C_313),A_314)
      | ~ r1_xboole_0(A_314,C_313)
      | ~ r1_xboole_0(A_314,B_312) ) ),
    inference(resolution,[status(thm)],[c_1531,c_26])).

tff(c_60,plain,(
    ~ r1_xboole_0(k2_xboole_0('#skF_4','#skF_6'),'#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_14355,plain,
    ( ~ r1_xboole_0('#skF_5','#skF_6')
    | ~ r1_xboole_0('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_14324,c_60])).

tff(c_14371,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2926,c_85,c_14355])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.34  % Computer   : n002.cluster.edu
% 0.15/0.34  % Model      : x86_64 x86_64
% 0.15/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.34  % Memory     : 8042.1875MB
% 0.15/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.34  % CPULimit   : 60
% 0.15/0.34  % DateTime   : Tue Dec  1 12:30:22 EST 2020
% 0.15/0.34  % CPUTime    : 
% 0.21/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.94/3.07  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.94/3.08  
% 7.94/3.08  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.94/3.08  %$ r2_hidden > r1_xboole_0 > r1_tarski > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_1 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_4
% 7.94/3.08  
% 7.94/3.08  %Foreground sorts:
% 7.94/3.08  
% 7.94/3.08  
% 7.94/3.08  %Background operators:
% 7.94/3.08  
% 7.94/3.08  
% 7.94/3.08  %Foreground operators:
% 7.94/3.08  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 7.94/3.08  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.94/3.08  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 7.94/3.08  tff(k1_tarski, type, k1_tarski: $i > $i).
% 7.94/3.08  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 7.94/3.08  tff('#skF_7', type, '#skF_7': $i).
% 7.94/3.08  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 7.94/3.08  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.94/3.08  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 7.94/3.08  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 7.94/3.08  tff('#skF_5', type, '#skF_5': $i).
% 7.94/3.08  tff('#skF_6', type, '#skF_6': $i).
% 7.94/3.08  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 7.94/3.08  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 7.94/3.08  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 7.94/3.08  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.94/3.08  tff(k3_tarski, type, k3_tarski: $i > $i).
% 7.94/3.08  tff('#skF_4', type, '#skF_4': $i).
% 7.94/3.08  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.94/3.08  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 7.94/3.08  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 7.94/3.08  
% 7.94/3.09  tff(f_110, negated_conjecture, ~(![A, B, C, D]: (((r1_tarski(k3_xboole_0(A, B), k1_tarski(D)) & r2_hidden(D, C)) & r1_xboole_0(C, B)) => r1_xboole_0(k2_xboole_0(A, C), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t149_zfmisc_1)).
% 7.94/3.09  tff(f_40, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 7.94/3.09  tff(f_58, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 7.94/3.09  tff(f_36, axiom, (![A, B, C]: ((C = k3_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_xboole_0)).
% 7.94/3.09  tff(f_64, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 7.94/3.09  tff(f_70, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 7.94/3.09  tff(f_44, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 7.94/3.09  tff(f_99, axiom, (![A, B]: (~r2_hidden(A, B) => r1_xboole_0(k1_tarski(A), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 7.94/3.09  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 7.94/3.09  tff(f_66, axiom, (![A, B, C]: (k3_xboole_0(k3_xboole_0(A, B), C) = k3_xboole_0(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t16_xboole_1)).
% 7.94/3.09  tff(f_88, axiom, (![A, B, C]: (~((~r1_xboole_0(A, k2_xboole_0(B, C)) & r1_xboole_0(A, B)) & r1_xboole_0(A, C)) & ~(~(r1_xboole_0(A, B) & r1_xboole_0(A, C)) & r1_xboole_0(A, k2_xboole_0(B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_xboole_1)).
% 7.94/3.09  tff(c_62, plain, (r1_xboole_0('#skF_6', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_110])).
% 7.94/3.09  tff(c_213, plain, (![A_59, B_60]: (k3_xboole_0(A_59, B_60)=k1_xboole_0 | ~r1_xboole_0(A_59, B_60))), inference(cnfTransformation, [status(thm)], [f_40])).
% 7.94/3.09  tff(c_237, plain, (k3_xboole_0('#skF_6', '#skF_5')=k1_xboole_0), inference(resolution, [status(thm)], [c_62, c_213])).
% 7.94/3.09  tff(c_412, plain, (![A_76, B_77, C_78]: (~r1_xboole_0(A_76, B_77) | ~r2_hidden(C_78, k3_xboole_0(A_76, B_77)))), inference(cnfTransformation, [status(thm)], [f_58])).
% 7.94/3.09  tff(c_421, plain, (![C_78]: (~r1_xboole_0('#skF_6', '#skF_5') | ~r2_hidden(C_78, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_237, c_412])).
% 7.94/3.09  tff(c_442, plain, (![C_78]: (~r2_hidden(C_78, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_421])).
% 7.94/3.09  tff(c_64, plain, (r2_hidden('#skF_7', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_110])).
% 7.94/3.09  tff(c_761, plain, (![A_106, B_107]: (r2_hidden('#skF_3'(A_106, B_107), k3_xboole_0(A_106, B_107)) | r1_xboole_0(A_106, B_107))), inference(cnfTransformation, [status(thm)], [f_58])).
% 7.94/3.09  tff(c_8, plain, (![D_8, A_3, B_4]: (r2_hidden(D_8, A_3) | ~r2_hidden(D_8, k3_xboole_0(A_3, B_4)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 7.94/3.09  tff(c_830, plain, (![A_108, B_109]: (r2_hidden('#skF_3'(A_108, B_109), A_108) | r1_xboole_0(A_108, B_109))), inference(resolution, [status(thm)], [c_761, c_8])).
% 7.94/3.09  tff(c_36, plain, (![B_19]: (r1_tarski(B_19, B_19))), inference(cnfTransformation, [status(thm)], [f_64])).
% 7.94/3.09  tff(c_179, plain, (![A_56, B_57]: (k3_xboole_0(A_56, B_57)=A_56 | ~r1_tarski(A_56, B_57))), inference(cnfTransformation, [status(thm)], [f_70])).
% 7.94/3.09  tff(c_187, plain, (![B_19]: (k3_xboole_0(B_19, B_19)=B_19)), inference(resolution, [status(thm)], [c_36, c_179])).
% 7.94/3.09  tff(c_170, plain, (![A_54, B_55]: (r1_xboole_0(A_54, B_55) | k3_xboole_0(A_54, B_55)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_40])).
% 7.94/3.09  tff(c_26, plain, (![B_12, A_11]: (r1_xboole_0(B_12, A_11) | ~r1_xboole_0(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_44])).
% 7.94/3.09  tff(c_176, plain, (![B_55, A_54]: (r1_xboole_0(B_55, A_54) | k3_xboole_0(A_54, B_55)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_170, c_26])).
% 7.94/3.09  tff(c_447, plain, (![B_81, C_82]: (~r1_xboole_0(B_81, B_81) | ~r2_hidden(C_82, B_81))), inference(superposition, [status(thm), theory('equality')], [c_187, c_412])).
% 7.94/3.09  tff(c_450, plain, (![C_82, A_54]: (~r2_hidden(C_82, A_54) | k3_xboole_0(A_54, A_54)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_176, c_447])).
% 7.94/3.09  tff(c_467, plain, (![C_82, A_54]: (~r2_hidden(C_82, A_54) | k1_xboole_0!=A_54)), inference(demodulation, [status(thm), theory('equality')], [c_187, c_450])).
% 7.94/3.09  tff(c_868, plain, (![A_110, B_111]: (k1_xboole_0!=A_110 | r1_xboole_0(A_110, B_111))), inference(resolution, [status(thm)], [c_830, c_467])).
% 7.94/3.09  tff(c_902, plain, (![B_112, A_113]: (r1_xboole_0(B_112, A_113) | k1_xboole_0!=A_113)), inference(resolution, [status(thm)], [c_868, c_26])).
% 7.94/3.09  tff(c_22, plain, (![A_9, B_10]: (k3_xboole_0(A_9, B_10)=k1_xboole_0 | ~r1_xboole_0(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_40])).
% 7.94/3.09  tff(c_1050, plain, (![B_112]: (k3_xboole_0(B_112, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_902, c_22])).
% 7.94/3.09  tff(c_56, plain, (![A_35, B_36]: (r1_xboole_0(k1_tarski(A_35), B_36) | r2_hidden(A_35, B_36))), inference(cnfTransformation, [status(thm)], [f_99])).
% 7.94/3.09  tff(c_574, plain, (![A_96, B_97]: (k3_xboole_0(k1_tarski(A_96), B_97)=k1_xboole_0 | r2_hidden(A_96, B_97))), inference(resolution, [status(thm)], [c_56, c_213])).
% 7.94/3.09  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 7.94/3.09  tff(c_603, plain, (![B_97, A_96]: (k3_xboole_0(B_97, k1_tarski(A_96))=k1_xboole_0 | r2_hidden(A_96, B_97))), inference(superposition, [status(thm), theory('equality')], [c_574, c_2])).
% 7.94/3.09  tff(c_66, plain, (r1_tarski(k3_xboole_0('#skF_4', '#skF_5'), k1_tarski('#skF_7'))), inference(cnfTransformation, [status(thm)], [f_110])).
% 7.94/3.09  tff(c_186, plain, (k3_xboole_0(k3_xboole_0('#skF_4', '#skF_5'), k1_tarski('#skF_7'))=k3_xboole_0('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_66, c_179])).
% 7.94/3.09  tff(c_1167, plain, (![A_118, B_119, C_120]: (k3_xboole_0(k3_xboole_0(A_118, B_119), C_120)=k3_xboole_0(A_118, k3_xboole_0(B_119, C_120)))), inference(cnfTransformation, [status(thm)], [f_66])).
% 7.94/3.09  tff(c_1256, plain, (k3_xboole_0('#skF_4', k3_xboole_0('#skF_5', k1_tarski('#skF_7')))=k3_xboole_0('#skF_4', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_186, c_1167])).
% 7.94/3.09  tff(c_2154, plain, (k3_xboole_0('#skF_4', k1_xboole_0)=k3_xboole_0('#skF_4', '#skF_5') | r2_hidden('#skF_7', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_603, c_1256])).
% 7.94/3.09  tff(c_2160, plain, (k3_xboole_0('#skF_4', '#skF_5')=k1_xboole_0 | r2_hidden('#skF_7', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_1050, c_2154])).
% 7.94/3.09  tff(c_2845, plain, (r2_hidden('#skF_7', '#skF_5')), inference(splitLeft, [status(thm)], [c_2160])).
% 7.94/3.09  tff(c_1813, plain, (![D_134, A_135, B_136]: (r2_hidden(D_134, k3_xboole_0(A_135, B_136)) | ~r2_hidden(D_134, B_136) | ~r2_hidden(D_134, A_135))), inference(cnfTransformation, [status(thm)], [f_36])).
% 7.94/3.09  tff(c_1862, plain, (![D_134]: (r2_hidden(D_134, k1_xboole_0) | ~r2_hidden(D_134, '#skF_5') | ~r2_hidden(D_134, '#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_237, c_1813])).
% 7.94/3.09  tff(c_1888, plain, (![D_134]: (~r2_hidden(D_134, '#skF_5') | ~r2_hidden(D_134, '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_442, c_1862])).
% 7.94/3.09  tff(c_2849, plain, (~r2_hidden('#skF_7', '#skF_6')), inference(resolution, [status(thm)], [c_2845, c_1888])).
% 7.94/3.09  tff(c_2856, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_64, c_2849])).
% 7.94/3.09  tff(c_2857, plain, (k3_xboole_0('#skF_4', '#skF_5')=k1_xboole_0), inference(splitRight, [status(thm)], [c_2160])).
% 7.94/3.09  tff(c_28, plain, (![A_13, B_14]: (r2_hidden('#skF_3'(A_13, B_14), k3_xboole_0(A_13, B_14)) | r1_xboole_0(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_58])).
% 7.94/3.09  tff(c_2890, plain, (r2_hidden('#skF_3'('#skF_4', '#skF_5'), k1_xboole_0) | r1_xboole_0('#skF_4', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_2857, c_28])).
% 7.94/3.09  tff(c_2917, plain, (r1_xboole_0('#skF_4', '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_442, c_2890])).
% 7.94/3.09  tff(c_2926, plain, (r1_xboole_0('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_2917, c_26])).
% 7.94/3.09  tff(c_79, plain, (![B_42, A_43]: (r1_xboole_0(B_42, A_43) | ~r1_xboole_0(A_43, B_42))), inference(cnfTransformation, [status(thm)], [f_44])).
% 7.94/3.09  tff(c_85, plain, (r1_xboole_0('#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_62, c_79])).
% 7.94/3.09  tff(c_1531, plain, (![A_126, C_127, B_128]: (~r1_xboole_0(A_126, C_127) | ~r1_xboole_0(A_126, B_128) | r1_xboole_0(A_126, k2_xboole_0(B_128, C_127)))), inference(cnfTransformation, [status(thm)], [f_88])).
% 7.94/3.09  tff(c_14324, plain, (![B_312, C_313, A_314]: (r1_xboole_0(k2_xboole_0(B_312, C_313), A_314) | ~r1_xboole_0(A_314, C_313) | ~r1_xboole_0(A_314, B_312))), inference(resolution, [status(thm)], [c_1531, c_26])).
% 7.94/3.09  tff(c_60, plain, (~r1_xboole_0(k2_xboole_0('#skF_4', '#skF_6'), '#skF_5')), inference(cnfTransformation, [status(thm)], [f_110])).
% 7.94/3.09  tff(c_14355, plain, (~r1_xboole_0('#skF_5', '#skF_6') | ~r1_xboole_0('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_14324, c_60])).
% 7.94/3.09  tff(c_14371, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2926, c_85, c_14355])).
% 7.94/3.09  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.94/3.09  
% 7.94/3.09  Inference rules
% 7.94/3.09  ----------------------
% 7.94/3.09  #Ref     : 1
% 7.94/3.09  #Sup     : 3546
% 7.94/3.09  #Fact    : 0
% 7.94/3.09  #Define  : 0
% 7.94/3.09  #Split   : 4
% 7.94/3.09  #Chain   : 0
% 7.94/3.09  #Close   : 0
% 7.94/3.09  
% 7.94/3.09  Ordering : KBO
% 7.94/3.09  
% 7.94/3.09  Simplification rules
% 7.94/3.09  ----------------------
% 7.94/3.09  #Subsume      : 931
% 7.94/3.09  #Demod        : 2631
% 7.94/3.09  #Tautology    : 1797
% 7.94/3.09  #SimpNegUnit  : 132
% 7.94/3.09  #BackRed      : 6
% 7.94/3.09  
% 7.94/3.09  #Partial instantiations: 0
% 8.06/3.09  #Strategies tried      : 1
% 8.06/3.09  
% 8.06/3.09  Timing (in seconds)
% 8.06/3.09  ----------------------
% 8.06/3.10  Preprocessing        : 0.41
% 8.06/3.10  Parsing              : 0.19
% 8.06/3.10  CNF conversion       : 0.04
% 8.06/3.10  Main loop            : 1.92
% 8.06/3.10  Inferencing          : 0.45
% 8.06/3.10  Reduction            : 0.99
% 8.06/3.10  Demodulation         : 0.82
% 8.06/3.10  BG Simplification    : 0.05
% 8.06/3.10  Subsumption          : 0.34
% 8.06/3.10  Abstraction          : 0.07
% 8.06/3.10  MUC search           : 0.00
% 8.06/3.10  Cooper               : 0.00
% 8.06/3.10  Total                : 2.36
% 8.06/3.10  Index Insertion      : 0.00
% 8.06/3.10  Index Deletion       : 0.00
% 8.06/3.10  Index Matching       : 0.00
% 8.06/3.10  BG Taut test         : 0.00
%------------------------------------------------------------------------------
