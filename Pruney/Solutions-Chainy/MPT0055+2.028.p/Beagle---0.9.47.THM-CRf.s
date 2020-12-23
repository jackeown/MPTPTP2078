%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:43:01 EST 2020

% Result     : Theorem 5.55s
% Output     : CNFRefutation 5.55s
% Verified   : 
% Statistics : Number of formulae       :   60 (  91 expanded)
%              Number of leaves         :   25 (  41 expanded)
%              Depth                    :   17
%              Number of atoms          :   68 ( 110 expanded)
%              Number of equality atoms :   36 (  66 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_1 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_4

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

tff(f_71,axiom,(
    ! [A,B] : k2_xboole_0(A,k3_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_79,axiom,(
    ! [A,B] : k4_xboole_0(A,k3_xboole_0(A,B)) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).

tff(f_75,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_77,axiom,(
    ! [A,B] : k4_xboole_0(k2_xboole_0(A,B),B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_xboole_1)).

tff(f_69,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_73,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_82,negated_conjecture,(
    ~ ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(c_32,plain,(
    ! [A_19,B_20] : k2_xboole_0(A_19,k3_xboole_0(A_19,B_20)) = A_19 ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_40,plain,(
    ! [A_26,B_27] : k4_xboole_0(A_26,k3_xboole_0(A_26,B_27)) = k4_xboole_0(A_26,B_27) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_36,plain,(
    ! [A_23] : k4_xboole_0(A_23,k1_xboole_0) = A_23 ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_26,plain,(
    ! [A_9,B_10] :
      ( r2_hidden('#skF_3'(A_9,B_10),A_9)
      | r1_xboole_0(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_287,plain,(
    ! [A_51,B_52] :
      ( r2_hidden('#skF_3'(A_51,B_52),B_52)
      | r1_xboole_0(A_51,B_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_6,plain,(
    ! [D_8,B_4,A_3] :
      ( ~ r2_hidden(D_8,B_4)
      | ~ r2_hidden(D_8,k4_xboole_0(A_3,B_4)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_5625,plain,(
    ! [A_212,A_213,B_214] :
      ( ~ r2_hidden('#skF_3'(A_212,k4_xboole_0(A_213,B_214)),B_214)
      | r1_xboole_0(A_212,k4_xboole_0(A_213,B_214)) ) ),
    inference(resolution,[status(thm)],[c_287,c_6])).

tff(c_5711,plain,(
    ! [A_215,A_216] : r1_xboole_0(A_215,k4_xboole_0(A_216,A_215)) ),
    inference(resolution,[status(thm)],[c_26,c_5625])).

tff(c_115,plain,(
    ! [A_43,B_44] : k4_xboole_0(k2_xboole_0(A_43,B_44),B_44) = k4_xboole_0(A_43,B_44) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_125,plain,(
    ! [A_43] : k4_xboole_0(A_43,k1_xboole_0) = k2_xboole_0(A_43,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_115,c_36])).

tff(c_147,plain,(
    ! [A_45] : k2_xboole_0(A_45,k1_xboole_0) = A_45 ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_125])).

tff(c_175,plain,(
    ! [A_46] : k2_xboole_0(k1_xboole_0,A_46) = A_46 ),
    inference(superposition,[status(thm),theory(equality)],[c_147,c_2])).

tff(c_238,plain,(
    ! [B_49] : k3_xboole_0(k1_xboole_0,B_49) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_175,c_32])).

tff(c_243,plain,(
    ! [B_49] : k4_xboole_0(k1_xboole_0,k1_xboole_0) = k4_xboole_0(k1_xboole_0,B_49) ),
    inference(superposition,[status(thm),theory(equality)],[c_238,c_40])).

tff(c_253,plain,(
    ! [B_49] : k4_xboole_0(k1_xboole_0,B_49) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_243])).

tff(c_38,plain,(
    ! [A_24,B_25] : k4_xboole_0(k2_xboole_0(A_24,B_25),B_25) = k4_xboole_0(A_24,B_25) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_185,plain,(
    ! [A_46] : k4_xboole_0(k1_xboole_0,A_46) = k4_xboole_0(A_46,A_46) ),
    inference(superposition,[status(thm),theory(equality)],[c_175,c_38])).

tff(c_302,plain,(
    ! [A_46] : k4_xboole_0(A_46,A_46) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_253,c_185])).

tff(c_910,plain,(
    ! [A_92,B_93,C_94] :
      ( r2_hidden('#skF_1'(A_92,B_93,C_94),A_92)
      | r2_hidden('#skF_2'(A_92,B_93,C_94),C_94)
      | k4_xboole_0(A_92,B_93) = C_94 ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_18,plain,(
    ! [A_3,B_4,C_5] :
      ( ~ r2_hidden('#skF_1'(A_3,B_4,C_5),B_4)
      | r2_hidden('#skF_2'(A_3,B_4,C_5),C_5)
      | k4_xboole_0(A_3,B_4) = C_5 ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_913,plain,(
    ! [A_92,C_94] :
      ( r2_hidden('#skF_2'(A_92,A_92,C_94),C_94)
      | k4_xboole_0(A_92,A_92) = C_94 ) ),
    inference(resolution,[status(thm)],[c_910,c_18])).

tff(c_1541,plain,(
    ! [A_121,C_122] :
      ( r2_hidden('#skF_2'(A_121,A_121,C_122),C_122)
      | k1_xboole_0 = C_122 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_302,c_913])).

tff(c_30,plain,(
    ! [A_14,B_15,C_18] :
      ( ~ r1_xboole_0(A_14,B_15)
      | ~ r2_hidden(C_18,k3_xboole_0(A_14,B_15)) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_1561,plain,(
    ! [A_14,B_15] :
      ( ~ r1_xboole_0(A_14,B_15)
      | k3_xboole_0(A_14,B_15) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_1541,c_30])).

tff(c_5778,plain,(
    ! [A_217,A_218] : k3_xboole_0(A_217,k4_xboole_0(A_218,A_217)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_5711,c_1561])).

tff(c_5819,plain,(
    ! [A_217,A_218] : k4_xboole_0(A_217,k4_xboole_0(A_218,A_217)) = k4_xboole_0(A_217,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_5778,c_40])).

tff(c_5889,plain,(
    ! [A_217,A_218] : k4_xboole_0(A_217,k4_xboole_0(A_218,A_217)) = A_217 ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_5819])).

tff(c_372,plain,(
    ! [A_60,B_61] : k2_xboole_0(A_60,k4_xboole_0(B_61,A_60)) = k2_xboole_0(A_60,B_61) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_382,plain,(
    ! [A_60,B_61] : k4_xboole_0(k2_xboole_0(A_60,B_61),k4_xboole_0(B_61,A_60)) = k4_xboole_0(A_60,k4_xboole_0(B_61,A_60)) ),
    inference(superposition,[status(thm),theory(equality)],[c_372,c_38])).

tff(c_7506,plain,(
    ! [A_249,B_250] : k4_xboole_0(k2_xboole_0(A_249,B_250),k4_xboole_0(B_250,A_249)) = A_249 ),
    inference(demodulation,[status(thm),theory(equality)],[c_5889,c_382])).

tff(c_7716,plain,(
    ! [A_26,B_27] : k4_xboole_0(k2_xboole_0(k3_xboole_0(A_26,B_27),A_26),k4_xboole_0(A_26,B_27)) = k3_xboole_0(A_26,B_27) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_7506])).

tff(c_7783,plain,(
    ! [A_26,B_27] : k4_xboole_0(A_26,k4_xboole_0(A_26,B_27)) = k3_xboole_0(A_26,B_27) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_2,c_7716])).

tff(c_42,plain,(
    k4_xboole_0('#skF_5',k4_xboole_0('#skF_5','#skF_6')) != k3_xboole_0('#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_9073,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_7783,c_42])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.34  % Computer   : n023.cluster.edu
% 0.15/0.34  % Model      : x86_64 x86_64
% 0.15/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.34  % Memory     : 8042.1875MB
% 0.15/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.34  % CPULimit   : 60
% 0.15/0.34  % DateTime   : Tue Dec  1 16:54:36 EST 2020
% 0.15/0.34  % CPUTime    : 
% 0.15/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.55/2.18  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.55/2.18  
% 5.55/2.18  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.55/2.19  %$ r2_hidden > r1_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_1 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_4
% 5.55/2.19  
% 5.55/2.19  %Foreground sorts:
% 5.55/2.19  
% 5.55/2.19  
% 5.55/2.19  %Background operators:
% 5.55/2.19  
% 5.55/2.19  
% 5.55/2.19  %Foreground operators:
% 5.55/2.19  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 5.55/2.19  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.55/2.19  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.55/2.19  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 5.55/2.19  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.55/2.19  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 5.55/2.19  tff('#skF_5', type, '#skF_5': $i).
% 5.55/2.19  tff('#skF_6', type, '#skF_6': $i).
% 5.55/2.19  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 5.55/2.19  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 5.55/2.19  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.55/2.19  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.55/2.19  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 5.55/2.19  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 5.55/2.19  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 5.55/2.19  
% 5.55/2.20  tff(f_71, axiom, (![A, B]: (k2_xboole_0(A, k3_xboole_0(A, B)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_xboole_1)).
% 5.55/2.20  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 5.55/2.20  tff(f_79, axiom, (![A, B]: (k4_xboole_0(A, k3_xboole_0(A, B)) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_xboole_1)).
% 5.55/2.20  tff(f_75, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 5.55/2.20  tff(f_55, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 5.55/2.20  tff(f_37, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 5.55/2.20  tff(f_77, axiom, (![A, B]: (k4_xboole_0(k2_xboole_0(A, B), B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t40_xboole_1)).
% 5.55/2.20  tff(f_69, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 5.55/2.20  tff(f_73, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 5.55/2.20  tff(f_82, negated_conjecture, ~(![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 5.55/2.20  tff(c_32, plain, (![A_19, B_20]: (k2_xboole_0(A_19, k3_xboole_0(A_19, B_20))=A_19)), inference(cnfTransformation, [status(thm)], [f_71])).
% 5.55/2.20  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 5.55/2.20  tff(c_40, plain, (![A_26, B_27]: (k4_xboole_0(A_26, k3_xboole_0(A_26, B_27))=k4_xboole_0(A_26, B_27))), inference(cnfTransformation, [status(thm)], [f_79])).
% 5.55/2.20  tff(c_36, plain, (![A_23]: (k4_xboole_0(A_23, k1_xboole_0)=A_23)), inference(cnfTransformation, [status(thm)], [f_75])).
% 5.55/2.20  tff(c_26, plain, (![A_9, B_10]: (r2_hidden('#skF_3'(A_9, B_10), A_9) | r1_xboole_0(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_55])).
% 5.55/2.20  tff(c_287, plain, (![A_51, B_52]: (r2_hidden('#skF_3'(A_51, B_52), B_52) | r1_xboole_0(A_51, B_52))), inference(cnfTransformation, [status(thm)], [f_55])).
% 5.55/2.20  tff(c_6, plain, (![D_8, B_4, A_3]: (~r2_hidden(D_8, B_4) | ~r2_hidden(D_8, k4_xboole_0(A_3, B_4)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 5.55/2.20  tff(c_5625, plain, (![A_212, A_213, B_214]: (~r2_hidden('#skF_3'(A_212, k4_xboole_0(A_213, B_214)), B_214) | r1_xboole_0(A_212, k4_xboole_0(A_213, B_214)))), inference(resolution, [status(thm)], [c_287, c_6])).
% 5.55/2.20  tff(c_5711, plain, (![A_215, A_216]: (r1_xboole_0(A_215, k4_xboole_0(A_216, A_215)))), inference(resolution, [status(thm)], [c_26, c_5625])).
% 5.55/2.20  tff(c_115, plain, (![A_43, B_44]: (k4_xboole_0(k2_xboole_0(A_43, B_44), B_44)=k4_xboole_0(A_43, B_44))), inference(cnfTransformation, [status(thm)], [f_77])).
% 5.55/2.20  tff(c_125, plain, (![A_43]: (k4_xboole_0(A_43, k1_xboole_0)=k2_xboole_0(A_43, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_115, c_36])).
% 5.55/2.20  tff(c_147, plain, (![A_45]: (k2_xboole_0(A_45, k1_xboole_0)=A_45)), inference(demodulation, [status(thm), theory('equality')], [c_36, c_125])).
% 5.55/2.20  tff(c_175, plain, (![A_46]: (k2_xboole_0(k1_xboole_0, A_46)=A_46)), inference(superposition, [status(thm), theory('equality')], [c_147, c_2])).
% 5.55/2.20  tff(c_238, plain, (![B_49]: (k3_xboole_0(k1_xboole_0, B_49)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_175, c_32])).
% 5.55/2.20  tff(c_243, plain, (![B_49]: (k4_xboole_0(k1_xboole_0, k1_xboole_0)=k4_xboole_0(k1_xboole_0, B_49))), inference(superposition, [status(thm), theory('equality')], [c_238, c_40])).
% 5.55/2.20  tff(c_253, plain, (![B_49]: (k4_xboole_0(k1_xboole_0, B_49)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_36, c_243])).
% 5.55/2.20  tff(c_38, plain, (![A_24, B_25]: (k4_xboole_0(k2_xboole_0(A_24, B_25), B_25)=k4_xboole_0(A_24, B_25))), inference(cnfTransformation, [status(thm)], [f_77])).
% 5.55/2.20  tff(c_185, plain, (![A_46]: (k4_xboole_0(k1_xboole_0, A_46)=k4_xboole_0(A_46, A_46))), inference(superposition, [status(thm), theory('equality')], [c_175, c_38])).
% 5.55/2.20  tff(c_302, plain, (![A_46]: (k4_xboole_0(A_46, A_46)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_253, c_185])).
% 5.55/2.20  tff(c_910, plain, (![A_92, B_93, C_94]: (r2_hidden('#skF_1'(A_92, B_93, C_94), A_92) | r2_hidden('#skF_2'(A_92, B_93, C_94), C_94) | k4_xboole_0(A_92, B_93)=C_94)), inference(cnfTransformation, [status(thm)], [f_37])).
% 5.55/2.20  tff(c_18, plain, (![A_3, B_4, C_5]: (~r2_hidden('#skF_1'(A_3, B_4, C_5), B_4) | r2_hidden('#skF_2'(A_3, B_4, C_5), C_5) | k4_xboole_0(A_3, B_4)=C_5)), inference(cnfTransformation, [status(thm)], [f_37])).
% 5.55/2.20  tff(c_913, plain, (![A_92, C_94]: (r2_hidden('#skF_2'(A_92, A_92, C_94), C_94) | k4_xboole_0(A_92, A_92)=C_94)), inference(resolution, [status(thm)], [c_910, c_18])).
% 5.55/2.20  tff(c_1541, plain, (![A_121, C_122]: (r2_hidden('#skF_2'(A_121, A_121, C_122), C_122) | k1_xboole_0=C_122)), inference(demodulation, [status(thm), theory('equality')], [c_302, c_913])).
% 5.55/2.20  tff(c_30, plain, (![A_14, B_15, C_18]: (~r1_xboole_0(A_14, B_15) | ~r2_hidden(C_18, k3_xboole_0(A_14, B_15)))), inference(cnfTransformation, [status(thm)], [f_69])).
% 5.55/2.20  tff(c_1561, plain, (![A_14, B_15]: (~r1_xboole_0(A_14, B_15) | k3_xboole_0(A_14, B_15)=k1_xboole_0)), inference(resolution, [status(thm)], [c_1541, c_30])).
% 5.55/2.20  tff(c_5778, plain, (![A_217, A_218]: (k3_xboole_0(A_217, k4_xboole_0(A_218, A_217))=k1_xboole_0)), inference(resolution, [status(thm)], [c_5711, c_1561])).
% 5.55/2.20  tff(c_5819, plain, (![A_217, A_218]: (k4_xboole_0(A_217, k4_xboole_0(A_218, A_217))=k4_xboole_0(A_217, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_5778, c_40])).
% 5.55/2.20  tff(c_5889, plain, (![A_217, A_218]: (k4_xboole_0(A_217, k4_xboole_0(A_218, A_217))=A_217)), inference(demodulation, [status(thm), theory('equality')], [c_36, c_5819])).
% 5.55/2.20  tff(c_372, plain, (![A_60, B_61]: (k2_xboole_0(A_60, k4_xboole_0(B_61, A_60))=k2_xboole_0(A_60, B_61))), inference(cnfTransformation, [status(thm)], [f_73])).
% 5.55/2.20  tff(c_382, plain, (![A_60, B_61]: (k4_xboole_0(k2_xboole_0(A_60, B_61), k4_xboole_0(B_61, A_60))=k4_xboole_0(A_60, k4_xboole_0(B_61, A_60)))), inference(superposition, [status(thm), theory('equality')], [c_372, c_38])).
% 5.55/2.20  tff(c_7506, plain, (![A_249, B_250]: (k4_xboole_0(k2_xboole_0(A_249, B_250), k4_xboole_0(B_250, A_249))=A_249)), inference(demodulation, [status(thm), theory('equality')], [c_5889, c_382])).
% 5.55/2.20  tff(c_7716, plain, (![A_26, B_27]: (k4_xboole_0(k2_xboole_0(k3_xboole_0(A_26, B_27), A_26), k4_xboole_0(A_26, B_27))=k3_xboole_0(A_26, B_27))), inference(superposition, [status(thm), theory('equality')], [c_40, c_7506])).
% 5.55/2.20  tff(c_7783, plain, (![A_26, B_27]: (k4_xboole_0(A_26, k4_xboole_0(A_26, B_27))=k3_xboole_0(A_26, B_27))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_2, c_7716])).
% 5.55/2.20  tff(c_42, plain, (k4_xboole_0('#skF_5', k4_xboole_0('#skF_5', '#skF_6'))!=k3_xboole_0('#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_82])).
% 5.55/2.20  tff(c_9073, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_7783, c_42])).
% 5.55/2.20  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.55/2.20  
% 5.55/2.20  Inference rules
% 5.55/2.20  ----------------------
% 5.55/2.20  #Ref     : 0
% 5.55/2.20  #Sup     : 2268
% 5.55/2.20  #Fact    : 0
% 5.55/2.20  #Define  : 0
% 5.55/2.20  #Split   : 1
% 5.55/2.20  #Chain   : 0
% 5.55/2.20  #Close   : 0
% 5.55/2.20  
% 5.55/2.20  Ordering : KBO
% 5.55/2.20  
% 5.55/2.20  Simplification rules
% 5.55/2.20  ----------------------
% 5.55/2.20  #Subsume      : 224
% 5.55/2.20  #Demod        : 2224
% 5.55/2.20  #Tautology    : 1539
% 5.55/2.20  #SimpNegUnit  : 44
% 5.55/2.20  #BackRed      : 5
% 5.55/2.20  
% 5.55/2.20  #Partial instantiations: 0
% 5.55/2.20  #Strategies tried      : 1
% 5.55/2.20  
% 5.55/2.20  Timing (in seconds)
% 5.55/2.20  ----------------------
% 5.55/2.20  Preprocessing        : 0.29
% 5.55/2.20  Parsing              : 0.16
% 5.55/2.20  CNF conversion       : 0.02
% 5.55/2.20  Main loop            : 1.14
% 5.55/2.20  Inferencing          : 0.35
% 5.55/2.20  Reduction            : 0.50
% 5.55/2.20  Demodulation         : 0.41
% 5.55/2.21  BG Simplification    : 0.04
% 5.55/2.21  Subsumption          : 0.19
% 5.55/2.21  Abstraction          : 0.05
% 5.55/2.21  MUC search           : 0.00
% 5.55/2.21  Cooper               : 0.00
% 5.55/2.21  Total                : 1.47
% 5.55/2.21  Index Insertion      : 0.00
% 5.55/2.21  Index Deletion       : 0.00
% 5.55/2.21  Index Matching       : 0.00
% 5.55/2.21  BG Taut test         : 0.00
%------------------------------------------------------------------------------
