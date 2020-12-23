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
% DateTime   : Thu Dec  3 09:49:01 EST 2020

% Result     : Theorem 3.54s
% Output     : CNFRefutation 3.54s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 105 expanded)
%              Number of leaves         :   40 (  53 expanded)
%              Depth                    :   12
%              Number of atoms          :   70 ( 109 expanded)
%              Number of equality atoms :   58 (  87 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_4 > #skF_7 > #skF_5 > #skF_2 > #skF_6 > #skF_3 > #skF_1

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

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

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

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i ) > $i )).

tff(f_97,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( r1_tarski(k1_tarski(A),k2_tarski(B,C))
          & A != B
          & A != C ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_zfmisc_1)).

tff(f_77,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_75,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_79,axiom,(
    ! [A,B,C,D] : k3_enumset1(A,A,B,C,D) = k2_enumset1(A,B,C,D) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

tff(f_71,axiom,(
    ! [A,B,C,D,E] : k3_enumset1(A,B,C,D,E) = k2_xboole_0(k2_enumset1(A,B,C,D),k1_tarski(E)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_enumset1)).

tff(f_41,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

tff(f_37,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_31,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_43,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_58,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

tff(f_69,axiom,(
    ! [A,B,C] : k1_enumset1(A,B,C) = k1_enumset1(C,B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t102_enumset1)).

tff(c_80,plain,(
    '#skF_7' != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_82,plain,(
    '#skF_5' != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_68,plain,(
    ! [A_39,B_40,C_41] : k2_enumset1(A_39,A_39,B_40,C_41) = k1_enumset1(A_39,B_40,C_41) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_66,plain,(
    ! [A_37,B_38] : k1_enumset1(A_37,A_37,B_38) = k2_tarski(A_37,B_38) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_70,plain,(
    ! [A_42,B_43,C_44,D_45] : k3_enumset1(A_42,A_42,B_43,C_44,D_45) = k2_enumset1(A_42,B_43,C_44,D_45) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_1685,plain,(
    ! [C_171,A_170,E_169,D_167,B_168] : k2_xboole_0(k2_enumset1(A_170,B_168,C_171,D_167),k1_tarski(E_169)) = k3_enumset1(A_170,B_168,C_171,D_167,E_169) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_1694,plain,(
    ! [A_39,B_40,C_41,E_169] : k3_enumset1(A_39,A_39,B_40,C_41,E_169) = k2_xboole_0(k1_enumset1(A_39,B_40,C_41),k1_tarski(E_169)) ),
    inference(superposition,[status(thm),theory(equality)],[c_68,c_1685])).

tff(c_1698,plain,(
    ! [A_172,B_173,C_174,E_175] : k2_xboole_0(k1_enumset1(A_172,B_173,C_174),k1_tarski(E_175)) = k2_enumset1(A_172,B_173,C_174,E_175) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_1694])).

tff(c_1737,plain,(
    ! [A_37,B_38,E_175] : k2_xboole_0(k2_tarski(A_37,B_38),k1_tarski(E_175)) = k2_enumset1(A_37,A_37,B_38,E_175) ),
    inference(superposition,[status(thm),theory(equality)],[c_66,c_1698])).

tff(c_1741,plain,(
    ! [A_176,B_177,E_178] : k2_xboole_0(k2_tarski(A_176,B_177),k1_tarski(E_178)) = k1_enumset1(A_176,B_177,E_178) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_1737])).

tff(c_14,plain,(
    ! [A_12] : k5_xboole_0(A_12,k1_xboole_0) = A_12 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_10,plain,(
    ! [A_9] : r1_tarski(k1_xboole_0,A_9) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_159,plain,(
    ! [A_87,B_88] :
      ( k3_xboole_0(A_87,B_88) = A_87
      | ~ r1_tarski(A_87,B_88) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_189,plain,(
    ! [A_91] : k3_xboole_0(k1_xboole_0,A_91) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_10,c_159])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_194,plain,(
    ! [A_91] : k3_xboole_0(A_91,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_189,c_2])).

tff(c_270,plain,(
    ! [A_93,B_94] : k5_xboole_0(A_93,k3_xboole_0(A_93,B_94)) = k4_xboole_0(A_93,B_94) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_282,plain,(
    ! [A_91] : k5_xboole_0(A_91,k1_xboole_0) = k4_xboole_0(A_91,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_194,c_270])).

tff(c_297,plain,(
    ! [A_91] : k4_xboole_0(A_91,k1_xboole_0) = A_91 ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_282])).

tff(c_426,plain,(
    ! [A_102,B_103] : k4_xboole_0(A_102,k4_xboole_0(A_102,B_103)) = k3_xboole_0(A_102,B_103) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_451,plain,(
    ! [A_91] : k4_xboole_0(A_91,A_91) = k3_xboole_0(A_91,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_297,c_426])).

tff(c_463,plain,(
    ! [A_91] : k4_xboole_0(A_91,A_91) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_194,c_451])).

tff(c_4,plain,(
    ! [A_3] : k3_xboole_0(A_3,A_3) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_294,plain,(
    ! [A_3] : k5_xboole_0(A_3,A_3) = k4_xboole_0(A_3,A_3) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_270])).

tff(c_84,plain,(
    r1_tarski(k1_tarski('#skF_5'),k2_tarski('#skF_6','#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_166,plain,(
    k3_xboole_0(k1_tarski('#skF_5'),k2_tarski('#skF_6','#skF_7')) = k1_tarski('#skF_5') ),
    inference(resolution,[status(thm)],[c_84,c_159])).

tff(c_279,plain,(
    k5_xboole_0(k1_tarski('#skF_5'),k1_tarski('#skF_5')) = k4_xboole_0(k1_tarski('#skF_5'),k2_tarski('#skF_6','#skF_7')) ),
    inference(superposition,[status(thm),theory(equality)],[c_166,c_270])).

tff(c_418,plain,(
    k4_xboole_0(k1_tarski('#skF_5'),k2_tarski('#skF_6','#skF_7')) = k4_xboole_0(k1_tarski('#skF_5'),k1_tarski('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_294,c_279])).

tff(c_16,plain,(
    ! [A_13,B_14] : k5_xboole_0(A_13,k4_xboole_0(B_14,A_13)) = k2_xboole_0(A_13,B_14) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_422,plain,(
    k5_xboole_0(k2_tarski('#skF_6','#skF_7'),k4_xboole_0(k1_tarski('#skF_5'),k1_tarski('#skF_5'))) = k2_xboole_0(k2_tarski('#skF_6','#skF_7'),k1_tarski('#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_418,c_16])).

tff(c_681,plain,(
    k2_xboole_0(k2_tarski('#skF_6','#skF_7'),k1_tarski('#skF_5')) = k2_tarski('#skF_6','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_463,c_422])).

tff(c_1747,plain,(
    k1_enumset1('#skF_6','#skF_7','#skF_5') = k2_tarski('#skF_6','#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_1741,c_681])).

tff(c_20,plain,(
    ! [E_21,A_15,B_16] : r2_hidden(E_21,k1_enumset1(A_15,B_16,E_21)) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_1787,plain,(
    r2_hidden('#skF_5',k2_tarski('#skF_6','#skF_7')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1747,c_20])).

tff(c_559,plain,(
    ! [C_107,B_108,A_109] : k1_enumset1(C_107,B_108,A_109) = k1_enumset1(A_109,B_108,C_107) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_575,plain,(
    ! [C_107,B_108] : k1_enumset1(C_107,B_108,B_108) = k2_tarski(B_108,C_107) ),
    inference(superposition,[status(thm),theory(equality)],[c_559,c_66])).

tff(c_1260,plain,(
    ! [E_137,C_138,B_139,A_140] :
      ( E_137 = C_138
      | E_137 = B_139
      | E_137 = A_140
      | ~ r2_hidden(E_137,k1_enumset1(A_140,B_139,C_138)) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_1284,plain,(
    ! [E_137,B_108,C_107] :
      ( E_137 = B_108
      | E_137 = B_108
      | E_137 = C_107
      | ~ r2_hidden(E_137,k2_tarski(B_108,C_107)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_575,c_1260])).

tff(c_1809,plain,
    ( '#skF_5' = '#skF_6'
    | '#skF_7' = '#skF_5' ),
    inference(resolution,[status(thm)],[c_1787,c_1284])).

tff(c_1816,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_82,c_82,c_1809])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:44:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.54/1.56  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.54/1.57  
% 3.54/1.57  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.54/1.57  %$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_4 > #skF_7 > #skF_5 > #skF_2 > #skF_6 > #skF_3 > #skF_1
% 3.54/1.57  
% 3.54/1.57  %Foreground sorts:
% 3.54/1.57  
% 3.54/1.57  
% 3.54/1.57  %Background operators:
% 3.54/1.57  
% 3.54/1.57  
% 3.54/1.57  %Foreground operators:
% 3.54/1.57  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.54/1.57  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.54/1.57  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.54/1.57  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.54/1.57  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.54/1.57  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.54/1.57  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 3.54/1.57  tff('#skF_7', type, '#skF_7': $i).
% 3.54/1.57  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.54/1.57  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.54/1.57  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.54/1.57  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.54/1.57  tff('#skF_5', type, '#skF_5': $i).
% 3.54/1.57  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 3.54/1.57  tff('#skF_6', type, '#skF_6': $i).
% 3.54/1.57  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.54/1.57  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.54/1.57  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.54/1.57  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.54/1.57  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 3.54/1.57  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.54/1.57  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.54/1.57  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.54/1.57  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.54/1.57  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 3.54/1.57  
% 3.54/1.58  tff(f_97, negated_conjecture, ~(![A, B, C]: ~((r1_tarski(k1_tarski(A), k2_tarski(B, C)) & ~(A = B)) & ~(A = C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t25_zfmisc_1)).
% 3.54/1.58  tff(f_77, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 3.54/1.58  tff(f_75, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 3.54/1.58  tff(f_79, axiom, (![A, B, C, D]: (k3_enumset1(A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_enumset1)).
% 3.54/1.58  tff(f_71, axiom, (![A, B, C, D, E]: (k3_enumset1(A, B, C, D, E) = k2_xboole_0(k2_enumset1(A, B, C, D), k1_tarski(E)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t50_enumset1)).
% 3.54/1.58  tff(f_41, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 3.54/1.58  tff(f_37, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 3.54/1.58  tff(f_35, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 3.54/1.58  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 3.54/1.58  tff(f_31, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 3.54/1.58  tff(f_39, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 3.54/1.58  tff(f_29, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 3.54/1.58  tff(f_43, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_xboole_1)).
% 3.54/1.58  tff(f_58, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_enumset1)).
% 3.54/1.58  tff(f_69, axiom, (![A, B, C]: (k1_enumset1(A, B, C) = k1_enumset1(C, B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t102_enumset1)).
% 3.54/1.58  tff(c_80, plain, ('#skF_7'!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_97])).
% 3.54/1.58  tff(c_82, plain, ('#skF_5'!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_97])).
% 3.54/1.58  tff(c_68, plain, (![A_39, B_40, C_41]: (k2_enumset1(A_39, A_39, B_40, C_41)=k1_enumset1(A_39, B_40, C_41))), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.54/1.58  tff(c_66, plain, (![A_37, B_38]: (k1_enumset1(A_37, A_37, B_38)=k2_tarski(A_37, B_38))), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.54/1.58  tff(c_70, plain, (![A_42, B_43, C_44, D_45]: (k3_enumset1(A_42, A_42, B_43, C_44, D_45)=k2_enumset1(A_42, B_43, C_44, D_45))), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.54/1.58  tff(c_1685, plain, (![C_171, A_170, E_169, D_167, B_168]: (k2_xboole_0(k2_enumset1(A_170, B_168, C_171, D_167), k1_tarski(E_169))=k3_enumset1(A_170, B_168, C_171, D_167, E_169))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.54/1.58  tff(c_1694, plain, (![A_39, B_40, C_41, E_169]: (k3_enumset1(A_39, A_39, B_40, C_41, E_169)=k2_xboole_0(k1_enumset1(A_39, B_40, C_41), k1_tarski(E_169)))), inference(superposition, [status(thm), theory('equality')], [c_68, c_1685])).
% 3.54/1.58  tff(c_1698, plain, (![A_172, B_173, C_174, E_175]: (k2_xboole_0(k1_enumset1(A_172, B_173, C_174), k1_tarski(E_175))=k2_enumset1(A_172, B_173, C_174, E_175))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_1694])).
% 3.54/1.58  tff(c_1737, plain, (![A_37, B_38, E_175]: (k2_xboole_0(k2_tarski(A_37, B_38), k1_tarski(E_175))=k2_enumset1(A_37, A_37, B_38, E_175))), inference(superposition, [status(thm), theory('equality')], [c_66, c_1698])).
% 3.54/1.58  tff(c_1741, plain, (![A_176, B_177, E_178]: (k2_xboole_0(k2_tarski(A_176, B_177), k1_tarski(E_178))=k1_enumset1(A_176, B_177, E_178))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_1737])).
% 3.54/1.58  tff(c_14, plain, (![A_12]: (k5_xboole_0(A_12, k1_xboole_0)=A_12)), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.54/1.58  tff(c_10, plain, (![A_9]: (r1_tarski(k1_xboole_0, A_9))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.54/1.58  tff(c_159, plain, (![A_87, B_88]: (k3_xboole_0(A_87, B_88)=A_87 | ~r1_tarski(A_87, B_88))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.54/1.58  tff(c_189, plain, (![A_91]: (k3_xboole_0(k1_xboole_0, A_91)=k1_xboole_0)), inference(resolution, [status(thm)], [c_10, c_159])).
% 3.54/1.58  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.54/1.58  tff(c_194, plain, (![A_91]: (k3_xboole_0(A_91, k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_189, c_2])).
% 3.54/1.58  tff(c_270, plain, (![A_93, B_94]: (k5_xboole_0(A_93, k3_xboole_0(A_93, B_94))=k4_xboole_0(A_93, B_94))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.54/1.58  tff(c_282, plain, (![A_91]: (k5_xboole_0(A_91, k1_xboole_0)=k4_xboole_0(A_91, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_194, c_270])).
% 3.54/1.58  tff(c_297, plain, (![A_91]: (k4_xboole_0(A_91, k1_xboole_0)=A_91)), inference(demodulation, [status(thm), theory('equality')], [c_14, c_282])).
% 3.54/1.58  tff(c_426, plain, (![A_102, B_103]: (k4_xboole_0(A_102, k4_xboole_0(A_102, B_103))=k3_xboole_0(A_102, B_103))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.54/1.58  tff(c_451, plain, (![A_91]: (k4_xboole_0(A_91, A_91)=k3_xboole_0(A_91, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_297, c_426])).
% 3.54/1.58  tff(c_463, plain, (![A_91]: (k4_xboole_0(A_91, A_91)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_194, c_451])).
% 3.54/1.58  tff(c_4, plain, (![A_3]: (k3_xboole_0(A_3, A_3)=A_3)), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.54/1.58  tff(c_294, plain, (![A_3]: (k5_xboole_0(A_3, A_3)=k4_xboole_0(A_3, A_3))), inference(superposition, [status(thm), theory('equality')], [c_4, c_270])).
% 3.54/1.58  tff(c_84, plain, (r1_tarski(k1_tarski('#skF_5'), k2_tarski('#skF_6', '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_97])).
% 3.54/1.58  tff(c_166, plain, (k3_xboole_0(k1_tarski('#skF_5'), k2_tarski('#skF_6', '#skF_7'))=k1_tarski('#skF_5')), inference(resolution, [status(thm)], [c_84, c_159])).
% 3.54/1.58  tff(c_279, plain, (k5_xboole_0(k1_tarski('#skF_5'), k1_tarski('#skF_5'))=k4_xboole_0(k1_tarski('#skF_5'), k2_tarski('#skF_6', '#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_166, c_270])).
% 3.54/1.58  tff(c_418, plain, (k4_xboole_0(k1_tarski('#skF_5'), k2_tarski('#skF_6', '#skF_7'))=k4_xboole_0(k1_tarski('#skF_5'), k1_tarski('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_294, c_279])).
% 3.54/1.58  tff(c_16, plain, (![A_13, B_14]: (k5_xboole_0(A_13, k4_xboole_0(B_14, A_13))=k2_xboole_0(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.54/1.58  tff(c_422, plain, (k5_xboole_0(k2_tarski('#skF_6', '#skF_7'), k4_xboole_0(k1_tarski('#skF_5'), k1_tarski('#skF_5')))=k2_xboole_0(k2_tarski('#skF_6', '#skF_7'), k1_tarski('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_418, c_16])).
% 3.54/1.58  tff(c_681, plain, (k2_xboole_0(k2_tarski('#skF_6', '#skF_7'), k1_tarski('#skF_5'))=k2_tarski('#skF_6', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_14, c_463, c_422])).
% 3.54/1.58  tff(c_1747, plain, (k1_enumset1('#skF_6', '#skF_7', '#skF_5')=k2_tarski('#skF_6', '#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_1741, c_681])).
% 3.54/1.58  tff(c_20, plain, (![E_21, A_15, B_16]: (r2_hidden(E_21, k1_enumset1(A_15, B_16, E_21)))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.54/1.58  tff(c_1787, plain, (r2_hidden('#skF_5', k2_tarski('#skF_6', '#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_1747, c_20])).
% 3.54/1.58  tff(c_559, plain, (![C_107, B_108, A_109]: (k1_enumset1(C_107, B_108, A_109)=k1_enumset1(A_109, B_108, C_107))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.54/1.58  tff(c_575, plain, (![C_107, B_108]: (k1_enumset1(C_107, B_108, B_108)=k2_tarski(B_108, C_107))), inference(superposition, [status(thm), theory('equality')], [c_559, c_66])).
% 3.54/1.58  tff(c_1260, plain, (![E_137, C_138, B_139, A_140]: (E_137=C_138 | E_137=B_139 | E_137=A_140 | ~r2_hidden(E_137, k1_enumset1(A_140, B_139, C_138)))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.54/1.58  tff(c_1284, plain, (![E_137, B_108, C_107]: (E_137=B_108 | E_137=B_108 | E_137=C_107 | ~r2_hidden(E_137, k2_tarski(B_108, C_107)))), inference(superposition, [status(thm), theory('equality')], [c_575, c_1260])).
% 3.54/1.58  tff(c_1809, plain, ('#skF_5'='#skF_6' | '#skF_7'='#skF_5'), inference(resolution, [status(thm)], [c_1787, c_1284])).
% 3.54/1.58  tff(c_1816, plain, $false, inference(negUnitSimplification, [status(thm)], [c_80, c_82, c_82, c_1809])).
% 3.54/1.58  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.54/1.58  
% 3.54/1.58  Inference rules
% 3.54/1.58  ----------------------
% 3.54/1.58  #Ref     : 0
% 3.54/1.58  #Sup     : 445
% 3.54/1.58  #Fact    : 0
% 3.54/1.58  #Define  : 0
% 3.54/1.58  #Split   : 0
% 3.54/1.58  #Chain   : 0
% 3.54/1.58  #Close   : 0
% 3.54/1.58  
% 3.54/1.58  Ordering : KBO
% 3.54/1.58  
% 3.54/1.58  Simplification rules
% 3.54/1.58  ----------------------
% 3.54/1.58  #Subsume      : 76
% 3.54/1.58  #Demod        : 246
% 3.54/1.58  #Tautology    : 285
% 3.54/1.58  #SimpNegUnit  : 1
% 3.54/1.58  #BackRed      : 2
% 3.54/1.58  
% 3.54/1.58  #Partial instantiations: 0
% 3.54/1.58  #Strategies tried      : 1
% 3.54/1.58  
% 3.54/1.58  Timing (in seconds)
% 3.54/1.58  ----------------------
% 3.54/1.59  Preprocessing        : 0.35
% 3.54/1.59  Parsing              : 0.18
% 3.54/1.59  CNF conversion       : 0.03
% 3.54/1.59  Main loop            : 0.46
% 3.54/1.59  Inferencing          : 0.15
% 3.54/1.59  Reduction            : 0.18
% 3.54/1.59  Demodulation         : 0.15
% 3.54/1.59  BG Simplification    : 0.03
% 3.54/1.59  Subsumption          : 0.08
% 3.54/1.59  Abstraction          : 0.02
% 3.54/1.59  MUC search           : 0.00
% 3.54/1.59  Cooper               : 0.00
% 3.54/1.59  Total                : 0.84
% 3.54/1.59  Index Insertion      : 0.00
% 3.54/1.59  Index Deletion       : 0.00
% 3.54/1.59  Index Matching       : 0.00
% 3.54/1.59  BG Taut test         : 0.00
%------------------------------------------------------------------------------
