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
% DateTime   : Thu Dec  3 09:43:00 EST 2020

% Result     : Theorem 8.73s
% Output     : CNFRefutation 8.73s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 197 expanded)
%              Number of leaves         :   27 (  77 expanded)
%              Depth                    :   18
%              Number of atoms          :   88 ( 225 expanded)
%              Number of equality atoms :   47 ( 157 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_1 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_75,axiom,(
    ! [A,B] : k2_xboole_0(A,k3_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_83,axiom,(
    ! [A,B] : k4_xboole_0(A,k3_xboole_0(A,B)) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).

tff(f_79,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_81,axiom,(
    ! [A,B] : k4_xboole_0(k2_xboole_0(A,B),B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_xboole_1)).

tff(f_77,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_73,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & r2_hidden(C,B) ) )
      & ~ ( ? [C] :
              ( r2_hidden(C,A)
              & r2_hidden(C,B) )
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_69,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_86,negated_conjecture,(
    ~ ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(c_36,plain,(
    ! [A_21,B_22] : k2_xboole_0(A_21,k3_xboole_0(A_21,B_22)) = A_21 ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_44,plain,(
    ! [A_29,B_30] : k4_xboole_0(A_29,k3_xboole_0(A_29,B_30)) = k4_xboole_0(A_29,B_30) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_40,plain,(
    ! [A_25,B_26] : k2_xboole_0(A_25,k4_xboole_0(B_26,A_25)) = k2_xboole_0(A_25,B_26) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_215,plain,(
    ! [A_60,B_61] : k4_xboole_0(k2_xboole_0(A_60,B_61),B_61) = k4_xboole_0(A_60,B_61) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_221,plain,(
    ! [B_61,A_60] : k2_xboole_0(B_61,k4_xboole_0(A_60,B_61)) = k2_xboole_0(B_61,k2_xboole_0(A_60,B_61)) ),
    inference(superposition,[status(thm),theory(equality)],[c_215,c_40])).

tff(c_814,plain,(
    ! [B_91,A_92] : k2_xboole_0(B_91,k2_xboole_0(A_92,B_91)) = k2_xboole_0(B_91,A_92) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_221])).

tff(c_1339,plain,(
    ! [A_112,B_113] : k2_xboole_0(A_112,k2_xboole_0(A_112,B_113)) = k2_xboole_0(A_112,B_113) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_814])).

tff(c_1403,plain,(
    ! [A_21,B_22] : k2_xboole_0(A_21,k3_xboole_0(A_21,B_22)) = k2_xboole_0(A_21,A_21) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_1339])).

tff(c_1424,plain,(
    ! [A_21] : k2_xboole_0(A_21,A_21) = A_21 ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_1403])).

tff(c_38,plain,(
    ! [A_23,B_24] : r1_tarski(k4_xboole_0(A_23,B_24),A_23) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_91,plain,(
    ! [A_39,B_40] :
      ( k4_xboole_0(A_39,B_40) = k1_xboole_0
      | ~ r1_tarski(A_39,B_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_99,plain,(
    ! [A_23,B_24] : k4_xboole_0(k4_xboole_0(A_23,B_24),A_23) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_38,c_91])).

tff(c_196,plain,(
    ! [A_58,B_59] : k2_xboole_0(A_58,k4_xboole_0(B_59,A_58)) = k2_xboole_0(A_58,B_59) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_1787,plain,(
    ! [A_133,B_134] : k2_xboole_0(A_133,k4_xboole_0(A_133,B_134)) = k2_xboole_0(A_133,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_99,c_196])).

tff(c_1815,plain,(
    ! [B_134] : k2_xboole_0(B_134,k1_xboole_0) = k2_xboole_0(B_134,B_134) ),
    inference(superposition,[status(thm),theory(equality)],[c_1787,c_40])).

tff(c_1860,plain,(
    ! [B_135] : k2_xboole_0(B_135,k1_xboole_0) = B_135 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1424,c_1815])).

tff(c_1894,plain,(
    ! [B_135] : k2_xboole_0(k1_xboole_0,B_135) = B_135 ),
    inference(superposition,[status(thm),theory(equality)],[c_1860,c_2])).

tff(c_1941,plain,(
    ! [B_139] : k2_xboole_0(k1_xboole_0,B_139) = B_139 ),
    inference(superposition,[status(thm),theory(equality)],[c_1860,c_2])).

tff(c_1985,plain,(
    ! [B_26] : k4_xboole_0(B_26,k1_xboole_0) = k2_xboole_0(k1_xboole_0,B_26) ),
    inference(superposition,[status(thm),theory(equality)],[c_1941,c_40])).

tff(c_2043,plain,(
    ! [B_26] : k4_xboole_0(B_26,k1_xboole_0) = B_26 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1894,c_1985])).

tff(c_26,plain,(
    ! [A_9,B_10] :
      ( r2_hidden('#skF_3'(A_9,B_10),A_9)
      | r1_xboole_0(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_574,plain,(
    ! [A_80,B_81] :
      ( r2_hidden('#skF_3'(A_80,B_81),B_81)
      | r1_xboole_0(A_80,B_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_6,plain,(
    ! [D_8,B_4,A_3] :
      ( ~ r2_hidden(D_8,B_4)
      | ~ r2_hidden(D_8,k4_xboole_0(A_3,B_4)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_3995,plain,(
    ! [A_200,A_201,B_202] :
      ( ~ r2_hidden('#skF_3'(A_200,k4_xboole_0(A_201,B_202)),B_202)
      | r1_xboole_0(A_200,k4_xboole_0(A_201,B_202)) ) ),
    inference(resolution,[status(thm)],[c_574,c_6])).

tff(c_4061,plain,(
    ! [A_203,A_204] : r1_xboole_0(A_203,k4_xboole_0(A_204,A_203)) ),
    inference(resolution,[status(thm)],[c_26,c_3995])).

tff(c_259,plain,(
    ! [A_62,B_63] : r1_tarski(k4_xboole_0(A_62,B_63),k2_xboole_0(A_62,B_63)) ),
    inference(superposition,[status(thm),theory(equality)],[c_215,c_38])).

tff(c_277,plain,(
    ! [A_23,B_24] : r1_tarski(k1_xboole_0,k2_xboole_0(k4_xboole_0(A_23,B_24),A_23)) ),
    inference(superposition,[status(thm),theory(equality)],[c_99,c_259])).

tff(c_326,plain,(
    ! [A_64,B_65] : r1_tarski(k1_xboole_0,k2_xboole_0(A_64,k4_xboole_0(A_64,B_65))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_277])).

tff(c_355,plain,(
    ! [B_66] : r1_tarski(k1_xboole_0,k2_xboole_0(B_66,B_66)) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_326])).

tff(c_34,plain,(
    ! [A_19,B_20] :
      ( k4_xboole_0(A_19,B_20) = k1_xboole_0
      | ~ r1_tarski(A_19,B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_359,plain,(
    ! [B_66] : k4_xboole_0(k1_xboole_0,k2_xboole_0(B_66,B_66)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_355,c_34])).

tff(c_1439,plain,(
    ! [B_66] : k4_xboole_0(k1_xboole_0,B_66) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1424,c_359])).

tff(c_252,plain,(
    ! [A_1,B_2] : k4_xboole_0(k2_xboole_0(A_1,B_2),A_1) = k4_xboole_0(B_2,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_215])).

tff(c_1882,plain,(
    ! [B_135] : k4_xboole_0(k1_xboole_0,B_135) = k4_xboole_0(B_135,B_135) ),
    inference(superposition,[status(thm),theory(equality)],[c_1860,c_252])).

tff(c_1921,plain,(
    ! [B_135] : k4_xboole_0(B_135,B_135) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1439,c_1882])).

tff(c_20,plain,(
    ! [A_3,B_4,C_5] :
      ( r2_hidden('#skF_1'(A_3,B_4,C_5),A_3)
      | r2_hidden('#skF_2'(A_3,B_4,C_5),C_5)
      | k4_xboole_0(A_3,B_4) = C_5 ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_1197,plain,(
    ! [A_104,B_105,C_106] :
      ( ~ r2_hidden('#skF_1'(A_104,B_105,C_106),B_105)
      | r2_hidden('#skF_2'(A_104,B_105,C_106),C_106)
      | k4_xboole_0(A_104,B_105) = C_106 ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_1204,plain,(
    ! [A_3,C_5] :
      ( r2_hidden('#skF_2'(A_3,A_3,C_5),C_5)
      | k4_xboole_0(A_3,A_3) = C_5 ) ),
    inference(resolution,[status(thm)],[c_20,c_1197])).

tff(c_2601,plain,(
    ! [A_157,C_158] :
      ( r2_hidden('#skF_2'(A_157,A_157,C_158),C_158)
      | k1_xboole_0 = C_158 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1921,c_1204])).

tff(c_30,plain,(
    ! [A_14,B_15,C_18] :
      ( ~ r1_xboole_0(A_14,B_15)
      | ~ r2_hidden(C_18,k3_xboole_0(A_14,B_15)) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_2627,plain,(
    ! [A_14,B_15] :
      ( ~ r1_xboole_0(A_14,B_15)
      | k3_xboole_0(A_14,B_15) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_2601,c_30])).

tff(c_4112,plain,(
    ! [A_205,A_206] : k3_xboole_0(A_205,k4_xboole_0(A_206,A_205)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_4061,c_2627])).

tff(c_4144,plain,(
    ! [A_205,A_206] : k4_xboole_0(A_205,k4_xboole_0(A_206,A_205)) = k4_xboole_0(A_205,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_4112,c_44])).

tff(c_4200,plain,(
    ! [A_205,A_206] : k4_xboole_0(A_205,k4_xboole_0(A_206,A_205)) = A_205 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2043,c_4144])).

tff(c_243,plain,(
    ! [A_25,B_26] : k4_xboole_0(k2_xboole_0(A_25,B_26),k4_xboole_0(B_26,A_25)) = k4_xboole_0(A_25,k4_xboole_0(B_26,A_25)) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_215])).

tff(c_4594,plain,(
    ! [A_217,B_218] : k4_xboole_0(k2_xboole_0(A_217,B_218),k4_xboole_0(B_218,A_217)) = A_217 ),
    inference(demodulation,[status(thm),theory(equality)],[c_4200,c_243])).

tff(c_4744,plain,(
    ! [A_29,B_30] : k4_xboole_0(k2_xboole_0(k3_xboole_0(A_29,B_30),A_29),k4_xboole_0(A_29,B_30)) = k3_xboole_0(A_29,B_30) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_4594])).

tff(c_4794,plain,(
    ! [A_29,B_30] : k4_xboole_0(A_29,k4_xboole_0(A_29,B_30)) = k3_xboole_0(A_29,B_30) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_2,c_4744])).

tff(c_46,plain,(
    k4_xboole_0('#skF_5',k4_xboole_0('#skF_5','#skF_6')) != k3_xboole_0('#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_9097,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4794,c_46])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:18:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.73/3.23  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.73/3.24  
% 8.73/3.24  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.73/3.24  %$ r2_hidden > r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_1 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_4
% 8.73/3.24  
% 8.73/3.24  %Foreground sorts:
% 8.73/3.24  
% 8.73/3.24  
% 8.73/3.24  %Background operators:
% 8.73/3.24  
% 8.73/3.24  
% 8.73/3.24  %Foreground operators:
% 8.73/3.24  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 8.73/3.24  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.73/3.24  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 8.73/3.24  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 8.73/3.24  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 8.73/3.24  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 8.73/3.24  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 8.73/3.24  tff('#skF_5', type, '#skF_5': $i).
% 8.73/3.24  tff('#skF_6', type, '#skF_6': $i).
% 8.73/3.24  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 8.73/3.24  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 8.73/3.24  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.73/3.24  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.73/3.24  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 8.73/3.24  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 8.73/3.24  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 8.73/3.24  
% 8.73/3.27  tff(f_75, axiom, (![A, B]: (k2_xboole_0(A, k3_xboole_0(A, B)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t22_xboole_1)).
% 8.73/3.27  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 8.73/3.27  tff(f_83, axiom, (![A, B]: (k4_xboole_0(A, k3_xboole_0(A, B)) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_xboole_1)).
% 8.73/3.27  tff(f_79, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_xboole_1)).
% 8.73/3.27  tff(f_81, axiom, (![A, B]: (k4_xboole_0(k2_xboole_0(A, B), B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t40_xboole_1)).
% 8.73/3.27  tff(f_77, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 8.73/3.27  tff(f_73, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 8.73/3.27  tff(f_55, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 8.73/3.27  tff(f_37, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_xboole_0)).
% 8.73/3.27  tff(f_69, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 8.73/3.27  tff(f_86, negated_conjecture, ~(![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 8.73/3.27  tff(c_36, plain, (![A_21, B_22]: (k2_xboole_0(A_21, k3_xboole_0(A_21, B_22))=A_21)), inference(cnfTransformation, [status(thm)], [f_75])).
% 8.73/3.27  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 8.73/3.27  tff(c_44, plain, (![A_29, B_30]: (k4_xboole_0(A_29, k3_xboole_0(A_29, B_30))=k4_xboole_0(A_29, B_30))), inference(cnfTransformation, [status(thm)], [f_83])).
% 8.73/3.27  tff(c_40, plain, (![A_25, B_26]: (k2_xboole_0(A_25, k4_xboole_0(B_26, A_25))=k2_xboole_0(A_25, B_26))), inference(cnfTransformation, [status(thm)], [f_79])).
% 8.73/3.27  tff(c_215, plain, (![A_60, B_61]: (k4_xboole_0(k2_xboole_0(A_60, B_61), B_61)=k4_xboole_0(A_60, B_61))), inference(cnfTransformation, [status(thm)], [f_81])).
% 8.73/3.27  tff(c_221, plain, (![B_61, A_60]: (k2_xboole_0(B_61, k4_xboole_0(A_60, B_61))=k2_xboole_0(B_61, k2_xboole_0(A_60, B_61)))), inference(superposition, [status(thm), theory('equality')], [c_215, c_40])).
% 8.73/3.27  tff(c_814, plain, (![B_91, A_92]: (k2_xboole_0(B_91, k2_xboole_0(A_92, B_91))=k2_xboole_0(B_91, A_92))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_221])).
% 8.73/3.27  tff(c_1339, plain, (![A_112, B_113]: (k2_xboole_0(A_112, k2_xboole_0(A_112, B_113))=k2_xboole_0(A_112, B_113))), inference(superposition, [status(thm), theory('equality')], [c_2, c_814])).
% 8.73/3.27  tff(c_1403, plain, (![A_21, B_22]: (k2_xboole_0(A_21, k3_xboole_0(A_21, B_22))=k2_xboole_0(A_21, A_21))), inference(superposition, [status(thm), theory('equality')], [c_36, c_1339])).
% 8.73/3.27  tff(c_1424, plain, (![A_21]: (k2_xboole_0(A_21, A_21)=A_21)), inference(demodulation, [status(thm), theory('equality')], [c_36, c_1403])).
% 8.73/3.27  tff(c_38, plain, (![A_23, B_24]: (r1_tarski(k4_xboole_0(A_23, B_24), A_23))), inference(cnfTransformation, [status(thm)], [f_77])).
% 8.73/3.27  tff(c_91, plain, (![A_39, B_40]: (k4_xboole_0(A_39, B_40)=k1_xboole_0 | ~r1_tarski(A_39, B_40))), inference(cnfTransformation, [status(thm)], [f_73])).
% 8.73/3.27  tff(c_99, plain, (![A_23, B_24]: (k4_xboole_0(k4_xboole_0(A_23, B_24), A_23)=k1_xboole_0)), inference(resolution, [status(thm)], [c_38, c_91])).
% 8.73/3.27  tff(c_196, plain, (![A_58, B_59]: (k2_xboole_0(A_58, k4_xboole_0(B_59, A_58))=k2_xboole_0(A_58, B_59))), inference(cnfTransformation, [status(thm)], [f_79])).
% 8.73/3.27  tff(c_1787, plain, (![A_133, B_134]: (k2_xboole_0(A_133, k4_xboole_0(A_133, B_134))=k2_xboole_0(A_133, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_99, c_196])).
% 8.73/3.27  tff(c_1815, plain, (![B_134]: (k2_xboole_0(B_134, k1_xboole_0)=k2_xboole_0(B_134, B_134))), inference(superposition, [status(thm), theory('equality')], [c_1787, c_40])).
% 8.73/3.27  tff(c_1860, plain, (![B_135]: (k2_xboole_0(B_135, k1_xboole_0)=B_135)), inference(demodulation, [status(thm), theory('equality')], [c_1424, c_1815])).
% 8.73/3.27  tff(c_1894, plain, (![B_135]: (k2_xboole_0(k1_xboole_0, B_135)=B_135)), inference(superposition, [status(thm), theory('equality')], [c_1860, c_2])).
% 8.73/3.27  tff(c_1941, plain, (![B_139]: (k2_xboole_0(k1_xboole_0, B_139)=B_139)), inference(superposition, [status(thm), theory('equality')], [c_1860, c_2])).
% 8.73/3.27  tff(c_1985, plain, (![B_26]: (k4_xboole_0(B_26, k1_xboole_0)=k2_xboole_0(k1_xboole_0, B_26))), inference(superposition, [status(thm), theory('equality')], [c_1941, c_40])).
% 8.73/3.27  tff(c_2043, plain, (![B_26]: (k4_xboole_0(B_26, k1_xboole_0)=B_26)), inference(demodulation, [status(thm), theory('equality')], [c_1894, c_1985])).
% 8.73/3.27  tff(c_26, plain, (![A_9, B_10]: (r2_hidden('#skF_3'(A_9, B_10), A_9) | r1_xboole_0(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_55])).
% 8.73/3.27  tff(c_574, plain, (![A_80, B_81]: (r2_hidden('#skF_3'(A_80, B_81), B_81) | r1_xboole_0(A_80, B_81))), inference(cnfTransformation, [status(thm)], [f_55])).
% 8.73/3.27  tff(c_6, plain, (![D_8, B_4, A_3]: (~r2_hidden(D_8, B_4) | ~r2_hidden(D_8, k4_xboole_0(A_3, B_4)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 8.73/3.27  tff(c_3995, plain, (![A_200, A_201, B_202]: (~r2_hidden('#skF_3'(A_200, k4_xboole_0(A_201, B_202)), B_202) | r1_xboole_0(A_200, k4_xboole_0(A_201, B_202)))), inference(resolution, [status(thm)], [c_574, c_6])).
% 8.73/3.27  tff(c_4061, plain, (![A_203, A_204]: (r1_xboole_0(A_203, k4_xboole_0(A_204, A_203)))), inference(resolution, [status(thm)], [c_26, c_3995])).
% 8.73/3.27  tff(c_259, plain, (![A_62, B_63]: (r1_tarski(k4_xboole_0(A_62, B_63), k2_xboole_0(A_62, B_63)))), inference(superposition, [status(thm), theory('equality')], [c_215, c_38])).
% 8.73/3.27  tff(c_277, plain, (![A_23, B_24]: (r1_tarski(k1_xboole_0, k2_xboole_0(k4_xboole_0(A_23, B_24), A_23)))), inference(superposition, [status(thm), theory('equality')], [c_99, c_259])).
% 8.73/3.27  tff(c_326, plain, (![A_64, B_65]: (r1_tarski(k1_xboole_0, k2_xboole_0(A_64, k4_xboole_0(A_64, B_65))))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_277])).
% 8.73/3.27  tff(c_355, plain, (![B_66]: (r1_tarski(k1_xboole_0, k2_xboole_0(B_66, B_66)))), inference(superposition, [status(thm), theory('equality')], [c_40, c_326])).
% 8.73/3.27  tff(c_34, plain, (![A_19, B_20]: (k4_xboole_0(A_19, B_20)=k1_xboole_0 | ~r1_tarski(A_19, B_20))), inference(cnfTransformation, [status(thm)], [f_73])).
% 8.73/3.27  tff(c_359, plain, (![B_66]: (k4_xboole_0(k1_xboole_0, k2_xboole_0(B_66, B_66))=k1_xboole_0)), inference(resolution, [status(thm)], [c_355, c_34])).
% 8.73/3.27  tff(c_1439, plain, (![B_66]: (k4_xboole_0(k1_xboole_0, B_66)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_1424, c_359])).
% 8.73/3.27  tff(c_252, plain, (![A_1, B_2]: (k4_xboole_0(k2_xboole_0(A_1, B_2), A_1)=k4_xboole_0(B_2, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_215])).
% 8.73/3.27  tff(c_1882, plain, (![B_135]: (k4_xboole_0(k1_xboole_0, B_135)=k4_xboole_0(B_135, B_135))), inference(superposition, [status(thm), theory('equality')], [c_1860, c_252])).
% 8.73/3.27  tff(c_1921, plain, (![B_135]: (k4_xboole_0(B_135, B_135)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_1439, c_1882])).
% 8.73/3.27  tff(c_20, plain, (![A_3, B_4, C_5]: (r2_hidden('#skF_1'(A_3, B_4, C_5), A_3) | r2_hidden('#skF_2'(A_3, B_4, C_5), C_5) | k4_xboole_0(A_3, B_4)=C_5)), inference(cnfTransformation, [status(thm)], [f_37])).
% 8.73/3.27  tff(c_1197, plain, (![A_104, B_105, C_106]: (~r2_hidden('#skF_1'(A_104, B_105, C_106), B_105) | r2_hidden('#skF_2'(A_104, B_105, C_106), C_106) | k4_xboole_0(A_104, B_105)=C_106)), inference(cnfTransformation, [status(thm)], [f_37])).
% 8.73/3.27  tff(c_1204, plain, (![A_3, C_5]: (r2_hidden('#skF_2'(A_3, A_3, C_5), C_5) | k4_xboole_0(A_3, A_3)=C_5)), inference(resolution, [status(thm)], [c_20, c_1197])).
% 8.73/3.27  tff(c_2601, plain, (![A_157, C_158]: (r2_hidden('#skF_2'(A_157, A_157, C_158), C_158) | k1_xboole_0=C_158)), inference(demodulation, [status(thm), theory('equality')], [c_1921, c_1204])).
% 8.73/3.27  tff(c_30, plain, (![A_14, B_15, C_18]: (~r1_xboole_0(A_14, B_15) | ~r2_hidden(C_18, k3_xboole_0(A_14, B_15)))), inference(cnfTransformation, [status(thm)], [f_69])).
% 8.73/3.27  tff(c_2627, plain, (![A_14, B_15]: (~r1_xboole_0(A_14, B_15) | k3_xboole_0(A_14, B_15)=k1_xboole_0)), inference(resolution, [status(thm)], [c_2601, c_30])).
% 8.73/3.27  tff(c_4112, plain, (![A_205, A_206]: (k3_xboole_0(A_205, k4_xboole_0(A_206, A_205))=k1_xboole_0)), inference(resolution, [status(thm)], [c_4061, c_2627])).
% 8.73/3.27  tff(c_4144, plain, (![A_205, A_206]: (k4_xboole_0(A_205, k4_xboole_0(A_206, A_205))=k4_xboole_0(A_205, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_4112, c_44])).
% 8.73/3.27  tff(c_4200, plain, (![A_205, A_206]: (k4_xboole_0(A_205, k4_xboole_0(A_206, A_205))=A_205)), inference(demodulation, [status(thm), theory('equality')], [c_2043, c_4144])).
% 8.73/3.27  tff(c_243, plain, (![A_25, B_26]: (k4_xboole_0(k2_xboole_0(A_25, B_26), k4_xboole_0(B_26, A_25))=k4_xboole_0(A_25, k4_xboole_0(B_26, A_25)))), inference(superposition, [status(thm), theory('equality')], [c_40, c_215])).
% 8.73/3.27  tff(c_4594, plain, (![A_217, B_218]: (k4_xboole_0(k2_xboole_0(A_217, B_218), k4_xboole_0(B_218, A_217))=A_217)), inference(demodulation, [status(thm), theory('equality')], [c_4200, c_243])).
% 8.73/3.27  tff(c_4744, plain, (![A_29, B_30]: (k4_xboole_0(k2_xboole_0(k3_xboole_0(A_29, B_30), A_29), k4_xboole_0(A_29, B_30))=k3_xboole_0(A_29, B_30))), inference(superposition, [status(thm), theory('equality')], [c_44, c_4594])).
% 8.73/3.27  tff(c_4794, plain, (![A_29, B_30]: (k4_xboole_0(A_29, k4_xboole_0(A_29, B_30))=k3_xboole_0(A_29, B_30))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_2, c_4744])).
% 8.73/3.27  tff(c_46, plain, (k4_xboole_0('#skF_5', k4_xboole_0('#skF_5', '#skF_6'))!=k3_xboole_0('#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_86])).
% 8.73/3.27  tff(c_9097, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4794, c_46])).
% 8.73/3.27  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.73/3.27  
% 8.73/3.27  Inference rules
% 8.73/3.27  ----------------------
% 8.73/3.27  #Ref     : 0
% 8.73/3.27  #Sup     : 2241
% 8.73/3.27  #Fact    : 0
% 8.73/3.27  #Define  : 0
% 8.73/3.27  #Split   : 1
% 8.73/3.27  #Chain   : 0
% 8.73/3.27  #Close   : 0
% 8.73/3.27  
% 8.73/3.27  Ordering : KBO
% 8.73/3.27  
% 8.73/3.27  Simplification rules
% 8.73/3.27  ----------------------
% 8.73/3.27  #Subsume      : 188
% 8.73/3.27  #Demod        : 2028
% 8.73/3.27  #Tautology    : 1558
% 8.73/3.27  #SimpNegUnit  : 42
% 8.73/3.27  #BackRed      : 9
% 8.73/3.27  
% 8.73/3.27  #Partial instantiations: 0
% 8.73/3.27  #Strategies tried      : 1
% 8.73/3.27  
% 8.73/3.27  Timing (in seconds)
% 8.73/3.27  ----------------------
% 8.73/3.27  Preprocessing        : 0.48
% 8.73/3.27  Parsing              : 0.25
% 8.73/3.27  CNF conversion       : 0.04
% 8.73/3.27  Main loop            : 1.94
% 8.73/3.27  Inferencing          : 0.59
% 8.73/3.27  Reduction            : 0.81
% 8.73/3.27  Demodulation         : 0.65
% 8.73/3.27  BG Simplification    : 0.06
% 8.73/3.27  Subsumption          : 0.33
% 8.73/3.27  Abstraction          : 0.08
% 8.73/3.27  MUC search           : 0.00
% 8.73/3.27  Cooper               : 0.00
% 8.73/3.27  Total                : 2.48
% 8.73/3.27  Index Insertion      : 0.00
% 8.73/3.27  Index Deletion       : 0.00
% 8.73/3.27  Index Matching       : 0.00
% 8.73/3.27  BG Taut test         : 0.00
%------------------------------------------------------------------------------
