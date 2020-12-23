%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:55:02 EST 2020

% Result     : Theorem 4.28s
% Output     : CNFRefutation 4.28s
% Verified   : 
% Statistics : Number of formulae       :   73 ( 100 expanded)
%              Number of leaves         :   31 (  48 expanded)
%              Depth                    :    8
%              Number of atoms          :   88 ( 149 expanded)
%              Number of equality atoms :   27 (  41 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_2 > #skF_1

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

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_103,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( r1_tarski(k3_xboole_0(A,B),k1_tarski(D))
          & r2_hidden(D,C)
          & r1_xboole_0(C,B) )
       => r1_xboole_0(k2_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t149_zfmisc_1)).

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

tff(f_29,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_33,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_37,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_81,axiom,(
    ! [A,B,C] :
      ( r1_xboole_0(A,B)
     => k3_xboole_0(A,k2_xboole_0(B,C)) = k3_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t78_xboole_1)).

tff(f_69,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_94,axiom,(
    ! [A,B] :
      ( ~ r2_hidden(A,B)
     => r1_xboole_0(k1_tarski(A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l27_zfmisc_1)).

tff(f_77,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_73,axiom,(
    ! [A,B,C] : k3_xboole_0(k3_xboole_0(A,B),C) = k3_xboole_0(A,k3_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_xboole_1)).

tff(c_44,plain,(
    r2_hidden('#skF_6','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_42,plain,(
    r1_xboole_0('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_577,plain,(
    ! [A_83,B_84,C_85] :
      ( ~ r1_xboole_0(A_83,B_84)
      | ~ r2_hidden(C_85,B_84)
      | ~ r2_hidden(C_85,A_83) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_602,plain,(
    ! [C_86] :
      ( ~ r2_hidden(C_86,'#skF_4')
      | ~ r2_hidden(C_86,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_42,c_577])).

tff(c_616,plain,(
    ~ r2_hidden('#skF_6','#skF_4') ),
    inference(resolution,[status(thm)],[c_44,c_602])).

tff(c_4,plain,(
    ! [B_4,A_3] : k3_xboole_0(B_4,A_3) = k3_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_182,plain,(
    ! [A_54,B_55] :
      ( r1_xboole_0(A_54,B_55)
      | k3_xboole_0(A_54,B_55) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_10,plain,(
    ! [B_8,A_7] :
      ( r1_xboole_0(B_8,A_7)
      | ~ r1_xboole_0(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_192,plain,(
    ! [B_55,A_54] :
      ( r1_xboole_0(B_55,A_54)
      | k3_xboole_0(A_54,B_55) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_182,c_10])).

tff(c_57,plain,(
    ! [B_40,A_41] :
      ( r1_xboole_0(B_40,A_41)
      | ~ r1_xboole_0(A_41,B_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_60,plain,(
    r1_xboole_0('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_42,c_57])).

tff(c_149,plain,(
    ! [A_52,B_53] :
      ( k3_xboole_0(A_52,B_53) = k1_xboole_0
      | ~ r1_xboole_0(A_52,B_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_160,plain,(
    k3_xboole_0('#skF_4','#skF_5') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_60,c_149])).

tff(c_1589,plain,(
    ! [A_127,B_128,C_129] :
      ( k3_xboole_0(A_127,k2_xboole_0(B_128,C_129)) = k3_xboole_0(A_127,C_129)
      | ~ r1_xboole_0(A_127,B_128) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_40,plain,(
    ~ r1_xboole_0(k2_xboole_0('#skF_3','#skF_5'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_190,plain,(
    k3_xboole_0(k2_xboole_0('#skF_3','#skF_5'),'#skF_4') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_182,c_40])).

tff(c_194,plain,(
    k3_xboole_0('#skF_4',k2_xboole_0('#skF_3','#skF_5')) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_190])).

tff(c_1663,plain,
    ( k3_xboole_0('#skF_4','#skF_5') != k1_xboole_0
    | ~ r1_xboole_0('#skF_4','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1589,c_194])).

tff(c_1712,plain,(
    ~ r1_xboole_0('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_160,c_1663])).

tff(c_1719,plain,(
    k3_xboole_0('#skF_3','#skF_4') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_192,c_1712])).

tff(c_1724,plain,(
    k3_xboole_0('#skF_4','#skF_3') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_1719])).

tff(c_14,plain,(
    ! [A_9,B_10] :
      ( r2_hidden('#skF_1'(A_9,B_10),B_10)
      | r1_xboole_0(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_161,plain,(
    k3_xboole_0('#skF_5','#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_42,c_149])).

tff(c_241,plain,(
    ! [A_64,B_65,C_66] :
      ( ~ r1_xboole_0(A_64,B_65)
      | ~ r2_hidden(C_66,k3_xboole_0(A_64,B_65)) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_251,plain,(
    ! [C_66] :
      ( ~ r1_xboole_0('#skF_5','#skF_4')
      | ~ r2_hidden(C_66,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_161,c_241])).

tff(c_263,plain,(
    ! [C_67] : ~ r2_hidden(C_67,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_251])).

tff(c_269,plain,(
    ! [A_68] : r1_xboole_0(A_68,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_14,c_263])).

tff(c_6,plain,(
    ! [A_5,B_6] :
      ( k3_xboole_0(A_5,B_6) = k1_xboole_0
      | ~ r1_xboole_0(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_275,plain,(
    ! [A_68] : k3_xboole_0(A_68,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_269,c_6])).

tff(c_145,plain,(
    ! [A_50,B_51] :
      ( r1_xboole_0(k1_tarski(A_50),B_51)
      | r2_hidden(A_50,B_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_199,plain,(
    ! [B_56,A_57] :
      ( r1_xboole_0(B_56,k1_tarski(A_57))
      | r2_hidden(A_57,B_56) ) ),
    inference(resolution,[status(thm)],[c_145,c_10])).

tff(c_205,plain,(
    ! [B_56,A_57] :
      ( k3_xboole_0(B_56,k1_tarski(A_57)) = k1_xboole_0
      | r2_hidden(A_57,B_56) ) ),
    inference(resolution,[status(thm)],[c_199,c_6])).

tff(c_46,plain,(
    r1_tarski(k3_xboole_0('#skF_3','#skF_4'),k1_tarski('#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_47,plain,(
    r1_tarski(k3_xboole_0('#skF_4','#skF_3'),k1_tarski('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_46])).

tff(c_140,plain,(
    ! [A_48,B_49] :
      ( k3_xboole_0(A_48,B_49) = A_48
      | ~ r1_tarski(A_48,B_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_144,plain,(
    k3_xboole_0(k3_xboole_0('#skF_4','#skF_3'),k1_tarski('#skF_6')) = k3_xboole_0('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_47,c_140])).

tff(c_1112,plain,(
    ! [A_116,B_117,C_118] : k3_xboole_0(k3_xboole_0(A_116,B_117),C_118) = k3_xboole_0(A_116,k3_xboole_0(B_117,C_118)) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_2764,plain,(
    ! [A_139,B_140,C_141] : k3_xboole_0(k3_xboole_0(A_139,B_140),C_141) = k3_xboole_0(B_140,k3_xboole_0(A_139,C_141)) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_1112])).

tff(c_2959,plain,(
    k3_xboole_0('#skF_3',k3_xboole_0('#skF_4',k1_tarski('#skF_6'))) = k3_xboole_0('#skF_4','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_144,c_2764])).

tff(c_3246,plain,
    ( k3_xboole_0('#skF_3',k1_xboole_0) = k3_xboole_0('#skF_4','#skF_3')
    | r2_hidden('#skF_6','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_205,c_2959])).

tff(c_3257,plain,
    ( k3_xboole_0('#skF_4','#skF_3') = k1_xboole_0
    | r2_hidden('#skF_6','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_275,c_3246])).

tff(c_3259,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_616,c_1724,c_3257])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:00:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.28/1.88  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.28/1.89  
% 4.28/1.89  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.28/1.89  %$ r2_hidden > r1_xboole_0 > r1_tarski > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 4.28/1.89  
% 4.28/1.89  %Foreground sorts:
% 4.28/1.89  
% 4.28/1.89  
% 4.28/1.89  %Background operators:
% 4.28/1.89  
% 4.28/1.89  
% 4.28/1.89  %Foreground operators:
% 4.28/1.89  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.28/1.89  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.28/1.89  tff(k1_tarski, type, k1_tarski: $i > $i).
% 4.28/1.89  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.28/1.89  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.28/1.89  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 4.28/1.89  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.28/1.89  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 4.28/1.89  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.28/1.89  tff('#skF_5', type, '#skF_5': $i).
% 4.28/1.89  tff('#skF_6', type, '#skF_6': $i).
% 4.28/1.89  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 4.28/1.89  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 4.28/1.89  tff('#skF_3', type, '#skF_3': $i).
% 4.28/1.89  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.28/1.89  tff('#skF_4', type, '#skF_4': $i).
% 4.28/1.89  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.28/1.89  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 4.28/1.89  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.28/1.89  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.28/1.89  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 4.28/1.89  
% 4.28/1.90  tff(f_103, negated_conjecture, ~(![A, B, C, D]: (((r1_tarski(k3_xboole_0(A, B), k1_tarski(D)) & r2_hidden(D, C)) & r1_xboole_0(C, B)) => r1_xboole_0(k2_xboole_0(A, C), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t149_zfmisc_1)).
% 4.28/1.90  tff(f_55, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 4.28/1.90  tff(f_29, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 4.28/1.90  tff(f_33, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 4.28/1.90  tff(f_37, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 4.28/1.90  tff(f_81, axiom, (![A, B, C]: (r1_xboole_0(A, B) => (k3_xboole_0(A, k2_xboole_0(B, C)) = k3_xboole_0(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t78_xboole_1)).
% 4.28/1.90  tff(f_69, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 4.28/1.90  tff(f_94, axiom, (![A, B]: (~r2_hidden(A, B) => r1_xboole_0(k1_tarski(A), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 4.28/1.90  tff(f_77, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 4.28/1.90  tff(f_73, axiom, (![A, B, C]: (k3_xboole_0(k3_xboole_0(A, B), C) = k3_xboole_0(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t16_xboole_1)).
% 4.28/1.90  tff(c_44, plain, (r2_hidden('#skF_6', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_103])).
% 4.28/1.90  tff(c_42, plain, (r1_xboole_0('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_103])).
% 4.28/1.90  tff(c_577, plain, (![A_83, B_84, C_85]: (~r1_xboole_0(A_83, B_84) | ~r2_hidden(C_85, B_84) | ~r2_hidden(C_85, A_83))), inference(cnfTransformation, [status(thm)], [f_55])).
% 4.28/1.90  tff(c_602, plain, (![C_86]: (~r2_hidden(C_86, '#skF_4') | ~r2_hidden(C_86, '#skF_5'))), inference(resolution, [status(thm)], [c_42, c_577])).
% 4.28/1.90  tff(c_616, plain, (~r2_hidden('#skF_6', '#skF_4')), inference(resolution, [status(thm)], [c_44, c_602])).
% 4.28/1.90  tff(c_4, plain, (![B_4, A_3]: (k3_xboole_0(B_4, A_3)=k3_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 4.28/1.90  tff(c_182, plain, (![A_54, B_55]: (r1_xboole_0(A_54, B_55) | k3_xboole_0(A_54, B_55)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.28/1.90  tff(c_10, plain, (![B_8, A_7]: (r1_xboole_0(B_8, A_7) | ~r1_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.28/1.90  tff(c_192, plain, (![B_55, A_54]: (r1_xboole_0(B_55, A_54) | k3_xboole_0(A_54, B_55)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_182, c_10])).
% 4.28/1.90  tff(c_57, plain, (![B_40, A_41]: (r1_xboole_0(B_40, A_41) | ~r1_xboole_0(A_41, B_40))), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.28/1.90  tff(c_60, plain, (r1_xboole_0('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_42, c_57])).
% 4.28/1.90  tff(c_149, plain, (![A_52, B_53]: (k3_xboole_0(A_52, B_53)=k1_xboole_0 | ~r1_xboole_0(A_52, B_53))), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.28/1.90  tff(c_160, plain, (k3_xboole_0('#skF_4', '#skF_5')=k1_xboole_0), inference(resolution, [status(thm)], [c_60, c_149])).
% 4.28/1.90  tff(c_1589, plain, (![A_127, B_128, C_129]: (k3_xboole_0(A_127, k2_xboole_0(B_128, C_129))=k3_xboole_0(A_127, C_129) | ~r1_xboole_0(A_127, B_128))), inference(cnfTransformation, [status(thm)], [f_81])).
% 4.28/1.90  tff(c_40, plain, (~r1_xboole_0(k2_xboole_0('#skF_3', '#skF_5'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_103])).
% 4.28/1.90  tff(c_190, plain, (k3_xboole_0(k2_xboole_0('#skF_3', '#skF_5'), '#skF_4')!=k1_xboole_0), inference(resolution, [status(thm)], [c_182, c_40])).
% 4.28/1.90  tff(c_194, plain, (k3_xboole_0('#skF_4', k2_xboole_0('#skF_3', '#skF_5'))!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_4, c_190])).
% 4.28/1.90  tff(c_1663, plain, (k3_xboole_0('#skF_4', '#skF_5')!=k1_xboole_0 | ~r1_xboole_0('#skF_4', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1589, c_194])).
% 4.28/1.90  tff(c_1712, plain, (~r1_xboole_0('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_160, c_1663])).
% 4.28/1.90  tff(c_1719, plain, (k3_xboole_0('#skF_3', '#skF_4')!=k1_xboole_0), inference(resolution, [status(thm)], [c_192, c_1712])).
% 4.28/1.90  tff(c_1724, plain, (k3_xboole_0('#skF_4', '#skF_3')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_4, c_1719])).
% 4.28/1.90  tff(c_14, plain, (![A_9, B_10]: (r2_hidden('#skF_1'(A_9, B_10), B_10) | r1_xboole_0(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_55])).
% 4.28/1.90  tff(c_161, plain, (k3_xboole_0('#skF_5', '#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_42, c_149])).
% 4.28/1.90  tff(c_241, plain, (![A_64, B_65, C_66]: (~r1_xboole_0(A_64, B_65) | ~r2_hidden(C_66, k3_xboole_0(A_64, B_65)))), inference(cnfTransformation, [status(thm)], [f_69])).
% 4.28/1.90  tff(c_251, plain, (![C_66]: (~r1_xboole_0('#skF_5', '#skF_4') | ~r2_hidden(C_66, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_161, c_241])).
% 4.28/1.90  tff(c_263, plain, (![C_67]: (~r2_hidden(C_67, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_251])).
% 4.28/1.90  tff(c_269, plain, (![A_68]: (r1_xboole_0(A_68, k1_xboole_0))), inference(resolution, [status(thm)], [c_14, c_263])).
% 4.28/1.90  tff(c_6, plain, (![A_5, B_6]: (k3_xboole_0(A_5, B_6)=k1_xboole_0 | ~r1_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.28/1.90  tff(c_275, plain, (![A_68]: (k3_xboole_0(A_68, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_269, c_6])).
% 4.28/1.90  tff(c_145, plain, (![A_50, B_51]: (r1_xboole_0(k1_tarski(A_50), B_51) | r2_hidden(A_50, B_51))), inference(cnfTransformation, [status(thm)], [f_94])).
% 4.28/1.90  tff(c_199, plain, (![B_56, A_57]: (r1_xboole_0(B_56, k1_tarski(A_57)) | r2_hidden(A_57, B_56))), inference(resolution, [status(thm)], [c_145, c_10])).
% 4.28/1.90  tff(c_205, plain, (![B_56, A_57]: (k3_xboole_0(B_56, k1_tarski(A_57))=k1_xboole_0 | r2_hidden(A_57, B_56))), inference(resolution, [status(thm)], [c_199, c_6])).
% 4.28/1.90  tff(c_46, plain, (r1_tarski(k3_xboole_0('#skF_3', '#skF_4'), k1_tarski('#skF_6'))), inference(cnfTransformation, [status(thm)], [f_103])).
% 4.28/1.90  tff(c_47, plain, (r1_tarski(k3_xboole_0('#skF_4', '#skF_3'), k1_tarski('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_46])).
% 4.28/1.90  tff(c_140, plain, (![A_48, B_49]: (k3_xboole_0(A_48, B_49)=A_48 | ~r1_tarski(A_48, B_49))), inference(cnfTransformation, [status(thm)], [f_77])).
% 4.28/1.90  tff(c_144, plain, (k3_xboole_0(k3_xboole_0('#skF_4', '#skF_3'), k1_tarski('#skF_6'))=k3_xboole_0('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_47, c_140])).
% 4.28/1.90  tff(c_1112, plain, (![A_116, B_117, C_118]: (k3_xboole_0(k3_xboole_0(A_116, B_117), C_118)=k3_xboole_0(A_116, k3_xboole_0(B_117, C_118)))), inference(cnfTransformation, [status(thm)], [f_73])).
% 4.28/1.90  tff(c_2764, plain, (![A_139, B_140, C_141]: (k3_xboole_0(k3_xboole_0(A_139, B_140), C_141)=k3_xboole_0(B_140, k3_xboole_0(A_139, C_141)))), inference(superposition, [status(thm), theory('equality')], [c_4, c_1112])).
% 4.28/1.90  tff(c_2959, plain, (k3_xboole_0('#skF_3', k3_xboole_0('#skF_4', k1_tarski('#skF_6')))=k3_xboole_0('#skF_4', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_144, c_2764])).
% 4.28/1.90  tff(c_3246, plain, (k3_xboole_0('#skF_3', k1_xboole_0)=k3_xboole_0('#skF_4', '#skF_3') | r2_hidden('#skF_6', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_205, c_2959])).
% 4.28/1.90  tff(c_3257, plain, (k3_xboole_0('#skF_4', '#skF_3')=k1_xboole_0 | r2_hidden('#skF_6', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_275, c_3246])).
% 4.28/1.90  tff(c_3259, plain, $false, inference(negUnitSimplification, [status(thm)], [c_616, c_1724, c_3257])).
% 4.28/1.90  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.28/1.90  
% 4.28/1.90  Inference rules
% 4.28/1.90  ----------------------
% 4.28/1.90  #Ref     : 0
% 4.28/1.90  #Sup     : 838
% 4.28/1.90  #Fact    : 0
% 4.28/1.90  #Define  : 0
% 4.28/1.90  #Split   : 0
% 4.28/1.90  #Chain   : 0
% 4.28/1.90  #Close   : 0
% 4.28/1.90  
% 4.28/1.90  Ordering : KBO
% 4.28/1.90  
% 4.28/1.90  Simplification rules
% 4.28/1.90  ----------------------
% 4.28/1.90  #Subsume      : 92
% 4.28/1.90  #Demod        : 541
% 4.28/1.90  #Tautology    : 393
% 4.28/1.90  #SimpNegUnit  : 21
% 4.28/1.90  #BackRed      : 0
% 4.28/1.90  
% 4.28/1.90  #Partial instantiations: 0
% 4.28/1.90  #Strategies tried      : 1
% 4.28/1.90  
% 4.28/1.90  Timing (in seconds)
% 4.28/1.90  ----------------------
% 4.28/1.90  Preprocessing        : 0.33
% 4.28/1.90  Parsing              : 0.18
% 4.28/1.90  CNF conversion       : 0.02
% 4.28/1.90  Main loop            : 0.70
% 4.28/1.90  Inferencing          : 0.21
% 4.28/1.90  Reduction            : 0.33
% 4.28/1.90  Demodulation         : 0.27
% 4.28/1.90  BG Simplification    : 0.03
% 4.28/1.90  Subsumption          : 0.10
% 4.28/1.90  Abstraction          : 0.03
% 4.28/1.90  MUC search           : 0.00
% 4.28/1.90  Cooper               : 0.00
% 4.28/1.90  Total                : 1.07
% 4.28/1.90  Index Insertion      : 0.00
% 4.28/1.90  Index Deletion       : 0.00
% 4.28/1.90  Index Matching       : 0.00
% 4.28/1.90  BG Taut test         : 0.00
%------------------------------------------------------------------------------
