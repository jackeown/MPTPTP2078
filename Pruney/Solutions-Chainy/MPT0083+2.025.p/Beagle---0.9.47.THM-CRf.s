%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:44:04 EST 2020

% Result     : Theorem 5.02s
% Output     : CNFRefutation 5.02s
% Verified   : 
% Statistics : Number of formulae       :   67 (  89 expanded)
%              Number of leaves         :   28 (  40 expanded)
%              Depth                    :   13
%              Number of atoms          :   72 ( 103 expanded)
%              Number of equality atoms :   31 (  46 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > #nlpp > k1_xboole_0 > #skF_5 > #skF_6 > #skF_4 > #skF_3 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_77,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_67,axiom,(
    ! [A,B,C] : k3_xboole_0(k3_xboole_0(A,B),C) = k3_xboole_0(A,k3_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_xboole_1)).

tff(f_69,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_75,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_xboole_1)).

tff(f_94,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r1_xboole_0(A,B)
       => r1_xboole_0(k3_xboole_0(C,A),k3_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_xboole_1)).

tff(f_65,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_57,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_79,axiom,(
    ! [A,B] : k4_xboole_0(A,k3_xboole_0(A,B)) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).

tff(f_81,axiom,(
    ! [A,B,C] : k3_xboole_0(A,k4_xboole_0(B,C)) = k4_xboole_0(k3_xboole_0(A,B),C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_xboole_1)).

tff(f_43,axiom,(
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

tff(f_83,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_71,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_89,axiom,(
    ! [A,B] :
      ~ ( ~ r1_xboole_0(A,B)
        & r1_xboole_0(k3_xboole_0(A,B),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_xboole_1)).

tff(c_24,plain,(
    ! [A_21] : k4_xboole_0(A_21,k1_xboole_0) = A_21 ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_14,plain,(
    ! [A_13,B_14,C_15] : k3_xboole_0(k3_xboole_0(A_13,B_14),C_15) = k3_xboole_0(A_13,k3_xboole_0(B_14,C_15)) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_16,plain,(
    ! [A_16,B_17] : r1_tarski(k3_xboole_0(A_16,B_17),A_16) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_60,plain,(
    ! [A_37,B_38] :
      ( k4_xboole_0(A_37,B_38) = k1_xboole_0
      | ~ r1_tarski(A_37,B_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_86,plain,(
    ! [A_40,B_41] : k4_xboole_0(k3_xboole_0(A_40,B_41),A_40) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_16,c_60])).

tff(c_92,plain,(
    ! [B_41] : k3_xboole_0(k1_xboole_0,B_41) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_86,c_24])).

tff(c_36,plain,(
    r1_xboole_0('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_12,plain,(
    ! [A_11] :
      ( r2_hidden('#skF_3'(A_11),A_11)
      | k1_xboole_0 = A_11 ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_135,plain,(
    ! [A_47,B_48,C_49] :
      ( ~ r1_xboole_0(A_47,B_48)
      | ~ r2_hidden(C_49,k3_xboole_0(A_47,B_48)) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_167,plain,(
    ! [A_51,B_52] :
      ( ~ r1_xboole_0(A_51,B_52)
      | k3_xboole_0(A_51,B_52) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_12,c_135])).

tff(c_176,plain,(
    k3_xboole_0('#skF_4','#skF_5') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_36,c_167])).

tff(c_1171,plain,(
    ! [A_93,B_94,C_95] : k3_xboole_0(k3_xboole_0(A_93,B_94),C_95) = k3_xboole_0(A_93,k3_xboole_0(B_94,C_95)) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_1243,plain,(
    ! [C_95] : k3_xboole_0('#skF_4',k3_xboole_0('#skF_5',C_95)) = k3_xboole_0(k1_xboole_0,C_95) ),
    inference(superposition,[status(thm),theory(equality)],[c_176,c_1171])).

tff(c_1272,plain,(
    ! [C_96] : k3_xboole_0('#skF_4',k3_xboole_0('#skF_5',C_96)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_1243])).

tff(c_26,plain,(
    ! [A_22,B_23] : k4_xboole_0(A_22,k3_xboole_0(A_22,B_23)) = k4_xboole_0(A_22,B_23) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_1292,plain,(
    ! [C_96] : k4_xboole_0('#skF_4',k3_xboole_0('#skF_5',C_96)) = k4_xboole_0('#skF_4',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_1272,c_26])).

tff(c_1353,plain,(
    ! [C_98] : k4_xboole_0('#skF_4',k3_xboole_0('#skF_5',C_98)) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_1292])).

tff(c_372,plain,(
    ! [A_68,B_69,C_70] : k4_xboole_0(k3_xboole_0(A_68,B_69),C_70) = k3_xboole_0(A_68,k4_xboole_0(B_69,C_70)) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_68,plain,(
    ! [A_16,B_17] : k4_xboole_0(k3_xboole_0(A_16,B_17),A_16) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_16,c_60])).

tff(c_383,plain,(
    ! [C_70,B_69] : k3_xboole_0(C_70,k4_xboole_0(B_69,C_70)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_372,c_68])).

tff(c_1530,plain,(
    ! [C_102] : k3_xboole_0(k3_xboole_0('#skF_5',C_102),'#skF_4') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_1353,c_383])).

tff(c_1882,plain,(
    ! [B_110] : k3_xboole_0('#skF_5',k3_xboole_0(B_110,'#skF_4')) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_1530])).

tff(c_1918,plain,(
    ! [B_110] : k4_xboole_0('#skF_5',k3_xboole_0(B_110,'#skF_4')) = k4_xboole_0('#skF_5',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_1882,c_26])).

tff(c_1963,plain,(
    ! [B_110] : k4_xboole_0('#skF_5',k3_xboole_0(B_110,'#skF_4')) = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_1918])).

tff(c_28,plain,(
    ! [A_24,B_25,C_26] : k4_xboole_0(k3_xboole_0(A_24,B_25),C_26) = k3_xboole_0(A_24,k4_xboole_0(B_25,C_26)) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_248,plain,(
    ! [A_57,B_58] :
      ( r2_hidden('#skF_1'(A_57,B_58),A_57)
      | r1_xboole_0(A_57,B_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_30,plain,(
    ! [A_27] : r1_xboole_0(A_27,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_18,plain,(
    ! [A_18] : k3_xboole_0(A_18,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_149,plain,(
    ! [A_18,C_49] :
      ( ~ r1_xboole_0(A_18,k1_xboole_0)
      | ~ r2_hidden(C_49,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_135])).

tff(c_153,plain,(
    ! [C_49] : ~ r2_hidden(C_49,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_149])).

tff(c_257,plain,(
    ! [B_58] : r1_xboole_0(k1_xboole_0,B_58) ),
    inference(resolution,[status(thm)],[c_248,c_153])).

tff(c_424,plain,(
    ! [C_71,B_72] : k3_xboole_0(C_71,k4_xboole_0(B_72,C_71)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_372,c_68])).

tff(c_32,plain,(
    ! [A_28,B_29] :
      ( ~ r1_xboole_0(k3_xboole_0(A_28,B_29),B_29)
      | r1_xboole_0(A_28,B_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_435,plain,(
    ! [B_72,C_71] :
      ( ~ r1_xboole_0(k1_xboole_0,k4_xboole_0(B_72,C_71))
      | r1_xboole_0(C_71,k4_xboole_0(B_72,C_71)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_424,c_32])).

tff(c_493,plain,(
    ! [C_73,B_74] : r1_xboole_0(C_73,k4_xboole_0(B_74,C_73)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_257,c_435])).

tff(c_3709,plain,(
    ! [C_145,A_146,B_147] : r1_xboole_0(C_145,k3_xboole_0(A_146,k4_xboole_0(B_147,C_145))) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_493])).

tff(c_3720,plain,(
    ! [B_110,A_146] : r1_xboole_0(k3_xboole_0(B_110,'#skF_4'),k3_xboole_0(A_146,'#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1963,c_3709])).

tff(c_34,plain,(
    ~ r1_xboole_0(k3_xboole_0('#skF_6','#skF_4'),k3_xboole_0('#skF_6','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_6326,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3720,c_34])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n003.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 19:46:57 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.02/1.99  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.02/2.00  
% 5.02/2.00  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.02/2.00  %$ r2_hidden > r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > #nlpp > k1_xboole_0 > #skF_5 > #skF_6 > #skF_4 > #skF_3 > #skF_2 > #skF_1
% 5.02/2.00  
% 5.02/2.00  %Foreground sorts:
% 5.02/2.00  
% 5.02/2.00  
% 5.02/2.00  %Background operators:
% 5.02/2.00  
% 5.02/2.00  
% 5.02/2.00  %Foreground operators:
% 5.02/2.00  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.02/2.00  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.02/2.00  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 5.02/2.00  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.02/2.00  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.02/2.00  tff('#skF_5', type, '#skF_5': $i).
% 5.02/2.00  tff('#skF_6', type, '#skF_6': $i).
% 5.02/2.00  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 5.02/2.00  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.02/2.00  tff('#skF_4', type, '#skF_4': $i).
% 5.02/2.00  tff('#skF_3', type, '#skF_3': $i > $i).
% 5.02/2.00  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.02/2.00  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 5.02/2.00  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 5.02/2.00  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 5.02/2.00  
% 5.02/2.01  tff(f_77, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 5.02/2.01  tff(f_67, axiom, (![A, B, C]: (k3_xboole_0(k3_xboole_0(A, B), C) = k3_xboole_0(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t16_xboole_1)).
% 5.02/2.01  tff(f_69, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 5.02/2.01  tff(f_75, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t37_xboole_1)).
% 5.02/2.01  tff(f_94, negated_conjecture, ~(![A, B, C]: (r1_xboole_0(A, B) => r1_xboole_0(k3_xboole_0(C, A), k3_xboole_0(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t76_xboole_1)).
% 5.02/2.01  tff(f_65, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 5.02/2.01  tff(f_57, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 5.02/2.01  tff(f_79, axiom, (![A, B]: (k4_xboole_0(A, k3_xboole_0(A, B)) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_xboole_1)).
% 5.02/2.01  tff(f_81, axiom, (![A, B, C]: (k3_xboole_0(A, k4_xboole_0(B, C)) = k4_xboole_0(k3_xboole_0(A, B), C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_xboole_1)).
% 5.02/2.01  tff(f_43, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 5.02/2.01  tff(f_83, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 5.02/2.01  tff(f_71, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 5.02/2.01  tff(f_89, axiom, (![A, B]: ~(~r1_xboole_0(A, B) & r1_xboole_0(k3_xboole_0(A, B), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t75_xboole_1)).
% 5.02/2.01  tff(c_24, plain, (![A_21]: (k4_xboole_0(A_21, k1_xboole_0)=A_21)), inference(cnfTransformation, [status(thm)], [f_77])).
% 5.02/2.01  tff(c_14, plain, (![A_13, B_14, C_15]: (k3_xboole_0(k3_xboole_0(A_13, B_14), C_15)=k3_xboole_0(A_13, k3_xboole_0(B_14, C_15)))), inference(cnfTransformation, [status(thm)], [f_67])).
% 5.02/2.01  tff(c_16, plain, (![A_16, B_17]: (r1_tarski(k3_xboole_0(A_16, B_17), A_16))), inference(cnfTransformation, [status(thm)], [f_69])).
% 5.02/2.01  tff(c_60, plain, (![A_37, B_38]: (k4_xboole_0(A_37, B_38)=k1_xboole_0 | ~r1_tarski(A_37, B_38))), inference(cnfTransformation, [status(thm)], [f_75])).
% 5.02/2.01  tff(c_86, plain, (![A_40, B_41]: (k4_xboole_0(k3_xboole_0(A_40, B_41), A_40)=k1_xboole_0)), inference(resolution, [status(thm)], [c_16, c_60])).
% 5.02/2.01  tff(c_92, plain, (![B_41]: (k3_xboole_0(k1_xboole_0, B_41)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_86, c_24])).
% 5.02/2.01  tff(c_36, plain, (r1_xboole_0('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_94])).
% 5.02/2.01  tff(c_12, plain, (![A_11]: (r2_hidden('#skF_3'(A_11), A_11) | k1_xboole_0=A_11)), inference(cnfTransformation, [status(thm)], [f_65])).
% 5.02/2.01  tff(c_135, plain, (![A_47, B_48, C_49]: (~r1_xboole_0(A_47, B_48) | ~r2_hidden(C_49, k3_xboole_0(A_47, B_48)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 5.02/2.01  tff(c_167, plain, (![A_51, B_52]: (~r1_xboole_0(A_51, B_52) | k3_xboole_0(A_51, B_52)=k1_xboole_0)), inference(resolution, [status(thm)], [c_12, c_135])).
% 5.02/2.01  tff(c_176, plain, (k3_xboole_0('#skF_4', '#skF_5')=k1_xboole_0), inference(resolution, [status(thm)], [c_36, c_167])).
% 5.02/2.01  tff(c_1171, plain, (![A_93, B_94, C_95]: (k3_xboole_0(k3_xboole_0(A_93, B_94), C_95)=k3_xboole_0(A_93, k3_xboole_0(B_94, C_95)))), inference(cnfTransformation, [status(thm)], [f_67])).
% 5.02/2.01  tff(c_1243, plain, (![C_95]: (k3_xboole_0('#skF_4', k3_xboole_0('#skF_5', C_95))=k3_xboole_0(k1_xboole_0, C_95))), inference(superposition, [status(thm), theory('equality')], [c_176, c_1171])).
% 5.02/2.01  tff(c_1272, plain, (![C_96]: (k3_xboole_0('#skF_4', k3_xboole_0('#skF_5', C_96))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_92, c_1243])).
% 5.02/2.01  tff(c_26, plain, (![A_22, B_23]: (k4_xboole_0(A_22, k3_xboole_0(A_22, B_23))=k4_xboole_0(A_22, B_23))), inference(cnfTransformation, [status(thm)], [f_79])).
% 5.02/2.01  tff(c_1292, plain, (![C_96]: (k4_xboole_0('#skF_4', k3_xboole_0('#skF_5', C_96))=k4_xboole_0('#skF_4', k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_1272, c_26])).
% 5.02/2.01  tff(c_1353, plain, (![C_98]: (k4_xboole_0('#skF_4', k3_xboole_0('#skF_5', C_98))='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_24, c_1292])).
% 5.02/2.01  tff(c_372, plain, (![A_68, B_69, C_70]: (k4_xboole_0(k3_xboole_0(A_68, B_69), C_70)=k3_xboole_0(A_68, k4_xboole_0(B_69, C_70)))), inference(cnfTransformation, [status(thm)], [f_81])).
% 5.02/2.01  tff(c_68, plain, (![A_16, B_17]: (k4_xboole_0(k3_xboole_0(A_16, B_17), A_16)=k1_xboole_0)), inference(resolution, [status(thm)], [c_16, c_60])).
% 5.02/2.01  tff(c_383, plain, (![C_70, B_69]: (k3_xboole_0(C_70, k4_xboole_0(B_69, C_70))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_372, c_68])).
% 5.02/2.01  tff(c_1530, plain, (![C_102]: (k3_xboole_0(k3_xboole_0('#skF_5', C_102), '#skF_4')=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_1353, c_383])).
% 5.02/2.01  tff(c_1882, plain, (![B_110]: (k3_xboole_0('#skF_5', k3_xboole_0(B_110, '#skF_4'))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_14, c_1530])).
% 5.02/2.01  tff(c_1918, plain, (![B_110]: (k4_xboole_0('#skF_5', k3_xboole_0(B_110, '#skF_4'))=k4_xboole_0('#skF_5', k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_1882, c_26])).
% 5.02/2.01  tff(c_1963, plain, (![B_110]: (k4_xboole_0('#skF_5', k3_xboole_0(B_110, '#skF_4'))='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_24, c_1918])).
% 5.02/2.01  tff(c_28, plain, (![A_24, B_25, C_26]: (k4_xboole_0(k3_xboole_0(A_24, B_25), C_26)=k3_xboole_0(A_24, k4_xboole_0(B_25, C_26)))), inference(cnfTransformation, [status(thm)], [f_81])).
% 5.02/2.01  tff(c_248, plain, (![A_57, B_58]: (r2_hidden('#skF_1'(A_57, B_58), A_57) | r1_xboole_0(A_57, B_58))), inference(cnfTransformation, [status(thm)], [f_43])).
% 5.02/2.01  tff(c_30, plain, (![A_27]: (r1_xboole_0(A_27, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_83])).
% 5.02/2.01  tff(c_18, plain, (![A_18]: (k3_xboole_0(A_18, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_71])).
% 5.02/2.01  tff(c_149, plain, (![A_18, C_49]: (~r1_xboole_0(A_18, k1_xboole_0) | ~r2_hidden(C_49, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_18, c_135])).
% 5.02/2.01  tff(c_153, plain, (![C_49]: (~r2_hidden(C_49, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_149])).
% 5.02/2.01  tff(c_257, plain, (![B_58]: (r1_xboole_0(k1_xboole_0, B_58))), inference(resolution, [status(thm)], [c_248, c_153])).
% 5.02/2.01  tff(c_424, plain, (![C_71, B_72]: (k3_xboole_0(C_71, k4_xboole_0(B_72, C_71))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_372, c_68])).
% 5.02/2.01  tff(c_32, plain, (![A_28, B_29]: (~r1_xboole_0(k3_xboole_0(A_28, B_29), B_29) | r1_xboole_0(A_28, B_29))), inference(cnfTransformation, [status(thm)], [f_89])).
% 5.02/2.01  tff(c_435, plain, (![B_72, C_71]: (~r1_xboole_0(k1_xboole_0, k4_xboole_0(B_72, C_71)) | r1_xboole_0(C_71, k4_xboole_0(B_72, C_71)))), inference(superposition, [status(thm), theory('equality')], [c_424, c_32])).
% 5.02/2.01  tff(c_493, plain, (![C_73, B_74]: (r1_xboole_0(C_73, k4_xboole_0(B_74, C_73)))), inference(demodulation, [status(thm), theory('equality')], [c_257, c_435])).
% 5.02/2.01  tff(c_3709, plain, (![C_145, A_146, B_147]: (r1_xboole_0(C_145, k3_xboole_0(A_146, k4_xboole_0(B_147, C_145))))), inference(superposition, [status(thm), theory('equality')], [c_28, c_493])).
% 5.02/2.01  tff(c_3720, plain, (![B_110, A_146]: (r1_xboole_0(k3_xboole_0(B_110, '#skF_4'), k3_xboole_0(A_146, '#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_1963, c_3709])).
% 5.02/2.01  tff(c_34, plain, (~r1_xboole_0(k3_xboole_0('#skF_6', '#skF_4'), k3_xboole_0('#skF_6', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_94])).
% 5.02/2.01  tff(c_6326, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3720, c_34])).
% 5.02/2.01  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.02/2.01  
% 5.02/2.01  Inference rules
% 5.02/2.01  ----------------------
% 5.02/2.01  #Ref     : 0
% 5.02/2.01  #Sup     : 1580
% 5.02/2.01  #Fact    : 0
% 5.02/2.01  #Define  : 0
% 5.02/2.01  #Split   : 1
% 5.02/2.01  #Chain   : 0
% 5.02/2.01  #Close   : 0
% 5.02/2.01  
% 5.02/2.01  Ordering : KBO
% 5.02/2.01  
% 5.02/2.01  Simplification rules
% 5.02/2.01  ----------------------
% 5.02/2.01  #Subsume      : 63
% 5.02/2.01  #Demod        : 1680
% 5.02/2.01  #Tautology    : 1142
% 5.02/2.01  #SimpNegUnit  : 61
% 5.02/2.01  #BackRed      : 1
% 5.02/2.01  
% 5.02/2.01  #Partial instantiations: 0
% 5.02/2.01  #Strategies tried      : 1
% 5.02/2.01  
% 5.02/2.01  Timing (in seconds)
% 5.02/2.01  ----------------------
% 5.02/2.02  Preprocessing        : 0.32
% 5.02/2.02  Parsing              : 0.18
% 5.02/2.02  CNF conversion       : 0.02
% 5.02/2.02  Main loop            : 0.91
% 5.02/2.02  Inferencing          : 0.29
% 5.02/2.02  Reduction            : 0.40
% 5.02/2.02  Demodulation         : 0.32
% 5.02/2.02  BG Simplification    : 0.03
% 5.02/2.02  Subsumption          : 0.14
% 5.02/2.02  Abstraction          : 0.05
% 5.02/2.02  MUC search           : 0.00
% 5.02/2.02  Cooper               : 0.00
% 5.02/2.02  Total                : 1.26
% 5.02/2.02  Index Insertion      : 0.00
% 5.02/2.02  Index Deletion       : 0.00
% 5.02/2.02  Index Matching       : 0.00
% 5.02/2.02  BG Taut test         : 0.00
%------------------------------------------------------------------------------
