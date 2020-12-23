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
% DateTime   : Thu Dec  3 09:50:34 EST 2020

% Result     : Theorem 3.55s
% Output     : CNFRefutation 3.83s
% Verified   : 
% Statistics : Number of formulae       :   66 ( 123 expanded)
%              Number of leaves         :   33 (  57 expanded)
%              Depth                    :   13
%              Number of atoms          :   83 ( 190 expanded)
%              Number of equality atoms :   31 (  75 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > #skF_1 > #skF_7 > #skF_3 > #skF_6 > #skF_2 > #skF_4 > #skF_5

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

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

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

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_106,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_108,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_104,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

tff(f_87,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_89,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_114,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_119,negated_conjecture,(
    ~ ! [A,B] :
        ( r1_tarski(k2_xboole_0(k1_tarski(A),B),B)
       => r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_zfmisc_1)).

tff(f_65,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_83,axiom,(
    ! [A,B,C] :
      ( ~ ( ~ r1_xboole_0(A,k2_xboole_0(B,C))
          & r1_xboole_0(A,B)
          & r1_xboole_0(A,C) )
      & ~ ( ~ ( r1_xboole_0(A,B)
              & r1_xboole_0(A,C) )
          & r1_xboole_0(A,k2_xboole_0(B,C)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_xboole_1)).

tff(f_59,axiom,(
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

tff(c_82,plain,(
    ! [A_35] : k2_tarski(A_35,A_35) = k1_tarski(A_35) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_187,plain,(
    ! [A_68,B_69] : k1_enumset1(A_68,A_68,B_69) = k2_tarski(A_68,B_69) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_62,plain,(
    ! [E_34,A_28,C_30] : r2_hidden(E_34,k1_enumset1(A_28,E_34,C_30)) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_205,plain,(
    ! [A_70,B_71] : r2_hidden(A_70,k2_tarski(A_70,B_71)) ),
    inference(superposition,[status(thm),theory(equality)],[c_187,c_62])).

tff(c_214,plain,(
    ! [A_35] : r2_hidden(A_35,k1_tarski(A_35)) ),
    inference(superposition,[status(thm),theory(equality)],[c_82,c_205])).

tff(c_54,plain,(
    ! [A_24,B_25] : r1_tarski(A_24,k2_xboole_0(A_24,B_25)) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_56,plain,(
    ! [B_27,A_26] : k2_tarski(B_27,A_26) = k2_tarski(A_26,B_27) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_144,plain,(
    ! [A_64,B_65] : k3_tarski(k2_tarski(A_64,B_65)) = k2_xboole_0(A_64,B_65) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_251,plain,(
    ! [A_84,B_85] : k3_tarski(k2_tarski(A_84,B_85)) = k2_xboole_0(B_85,A_84) ),
    inference(superposition,[status(thm),theory(equality)],[c_56,c_144])).

tff(c_90,plain,(
    ! [A_45,B_46] : k3_tarski(k2_tarski(A_45,B_46)) = k2_xboole_0(A_45,B_46) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_257,plain,(
    ! [B_85,A_84] : k2_xboole_0(B_85,A_84) = k2_xboole_0(A_84,B_85) ),
    inference(superposition,[status(thm),theory(equality)],[c_251,c_90])).

tff(c_94,plain,(
    r1_tarski(k2_xboole_0(k1_tarski('#skF_6'),'#skF_7'),'#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_277,plain,(
    r1_tarski(k2_xboole_0('#skF_7',k1_tarski('#skF_6')),'#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_257,c_94])).

tff(c_436,plain,(
    ! [B_107,A_108] :
      ( B_107 = A_108
      | ~ r1_tarski(B_107,A_108)
      | ~ r1_tarski(A_108,B_107) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_438,plain,
    ( k2_xboole_0('#skF_7',k1_tarski('#skF_6')) = '#skF_7'
    | ~ r1_tarski('#skF_7',k2_xboole_0('#skF_7',k1_tarski('#skF_6'))) ),
    inference(resolution,[status(thm)],[c_277,c_436])).

tff(c_449,plain,(
    k2_xboole_0('#skF_7',k1_tarski('#skF_6')) = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_438])).

tff(c_48,plain,(
    ! [A_19,C_21,B_20] :
      ( r1_xboole_0(A_19,C_21)
      | ~ r1_xboole_0(A_19,k2_xboole_0(B_20,C_21)) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_462,plain,(
    ! [A_19] :
      ( r1_xboole_0(A_19,k1_tarski('#skF_6'))
      | ~ r1_xboole_0(A_19,'#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_449,c_48])).

tff(c_489,plain,(
    ! [A_111,B_112,C_113] :
      ( ~ r1_xboole_0(A_111,B_112)
      | ~ r2_hidden(C_113,B_112)
      | ~ r2_hidden(C_113,A_111) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_661,plain,(
    ! [C_137,A_138] :
      ( ~ r2_hidden(C_137,k1_tarski('#skF_6'))
      | ~ r2_hidden(C_137,A_138)
      | ~ r1_xboole_0(A_138,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_462,c_489])).

tff(c_674,plain,(
    ! [A_139] :
      ( ~ r2_hidden('#skF_6',A_139)
      | ~ r1_xboole_0(A_139,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_214,c_661])).

tff(c_705,plain,(
    ~ r1_xboole_0(k1_tarski('#skF_6'),'#skF_7') ),
    inference(resolution,[status(thm)],[c_214,c_674])).

tff(c_92,plain,(
    ~ r2_hidden('#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_36,plain,(
    ! [A_10,B_11] :
      ( r2_hidden('#skF_3'(A_10,B_11),A_10)
      | r1_xboole_0(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_84,plain,(
    ! [A_36,B_37] : k1_enumset1(A_36,A_36,B_37) = k2_tarski(A_36,B_37) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_1383,plain,(
    ! [E_218,C_219,B_220,A_221] :
      ( E_218 = C_219
      | E_218 = B_220
      | E_218 = A_221
      | ~ r2_hidden(E_218,k1_enumset1(A_221,B_220,C_219)) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_1498,plain,(
    ! [E_239,B_240,A_241] :
      ( E_239 = B_240
      | E_239 = A_241
      | E_239 = A_241
      | ~ r2_hidden(E_239,k2_tarski(A_241,B_240)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_84,c_1383])).

tff(c_1528,plain,(
    ! [E_242,A_243] :
      ( E_242 = A_243
      | E_242 = A_243
      | E_242 = A_243
      | ~ r2_hidden(E_242,k1_tarski(A_243)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_82,c_1498])).

tff(c_1604,plain,(
    ! [A_248,B_249] :
      ( '#skF_3'(k1_tarski(A_248),B_249) = A_248
      | r1_xboole_0(k1_tarski(A_248),B_249) ) ),
    inference(resolution,[status(thm)],[c_36,c_1528])).

tff(c_1622,plain,(
    '#skF_3'(k1_tarski('#skF_6'),'#skF_7') = '#skF_6' ),
    inference(resolution,[status(thm)],[c_1604,c_705])).

tff(c_34,plain,(
    ! [A_10,B_11] :
      ( r2_hidden('#skF_3'(A_10,B_11),B_11)
      | r1_xboole_0(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_1633,plain,
    ( r2_hidden('#skF_6','#skF_7')
    | r1_xboole_0(k1_tarski('#skF_6'),'#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_1622,c_34])).

tff(c_1641,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_705,c_92,c_1633])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n003.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 14:15:57 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.55/1.61  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.55/1.61  
% 3.55/1.61  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.55/1.61  %$ r2_hidden > r1_xboole_0 > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > #skF_1 > #skF_7 > #skF_3 > #skF_6 > #skF_2 > #skF_4 > #skF_5
% 3.55/1.61  
% 3.55/1.61  %Foreground sorts:
% 3.55/1.61  
% 3.55/1.61  
% 3.55/1.61  %Background operators:
% 3.55/1.61  
% 3.55/1.61  
% 3.55/1.61  %Foreground operators:
% 3.55/1.61  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 3.55/1.61  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.55/1.61  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.55/1.61  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.55/1.61  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.55/1.61  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.55/1.61  tff('#skF_7', type, '#skF_7': $i).
% 3.55/1.61  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.55/1.61  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 3.55/1.61  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.55/1.61  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.55/1.61  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.55/1.61  tff('#skF_6', type, '#skF_6': $i).
% 3.55/1.61  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.55/1.61  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.55/1.61  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 3.55/1.61  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i) > $i).
% 3.55/1.61  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.55/1.61  tff(k3_tarski, type, k3_tarski: $i > $i).
% 3.55/1.61  tff('#skF_5', type, '#skF_5': ($i * $i * $i * $i) > $i).
% 3.55/1.61  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.55/1.61  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.55/1.61  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.55/1.61  
% 3.83/1.63  tff(f_106, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 3.83/1.63  tff(f_108, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 3.83/1.63  tff(f_104, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_enumset1)).
% 3.83/1.63  tff(f_87, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 3.83/1.63  tff(f_89, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 3.83/1.63  tff(f_114, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 3.83/1.63  tff(f_119, negated_conjecture, ~(![A, B]: (r1_tarski(k2_xboole_0(k1_tarski(A), B), B) => r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t45_zfmisc_1)).
% 3.83/1.63  tff(f_65, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.83/1.63  tff(f_83, axiom, (![A, B, C]: (~((~r1_xboole_0(A, k2_xboole_0(B, C)) & r1_xboole_0(A, B)) & r1_xboole_0(A, C)) & ~(~(r1_xboole_0(A, B) & r1_xboole_0(A, C)) & r1_xboole_0(A, k2_xboole_0(B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_xboole_1)).
% 3.83/1.63  tff(f_59, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 3.83/1.63  tff(c_82, plain, (![A_35]: (k2_tarski(A_35, A_35)=k1_tarski(A_35))), inference(cnfTransformation, [status(thm)], [f_106])).
% 3.83/1.63  tff(c_187, plain, (![A_68, B_69]: (k1_enumset1(A_68, A_68, B_69)=k2_tarski(A_68, B_69))), inference(cnfTransformation, [status(thm)], [f_108])).
% 3.83/1.63  tff(c_62, plain, (![E_34, A_28, C_30]: (r2_hidden(E_34, k1_enumset1(A_28, E_34, C_30)))), inference(cnfTransformation, [status(thm)], [f_104])).
% 3.83/1.63  tff(c_205, plain, (![A_70, B_71]: (r2_hidden(A_70, k2_tarski(A_70, B_71)))), inference(superposition, [status(thm), theory('equality')], [c_187, c_62])).
% 3.83/1.63  tff(c_214, plain, (![A_35]: (r2_hidden(A_35, k1_tarski(A_35)))), inference(superposition, [status(thm), theory('equality')], [c_82, c_205])).
% 3.83/1.63  tff(c_54, plain, (![A_24, B_25]: (r1_tarski(A_24, k2_xboole_0(A_24, B_25)))), inference(cnfTransformation, [status(thm)], [f_87])).
% 3.83/1.63  tff(c_56, plain, (![B_27, A_26]: (k2_tarski(B_27, A_26)=k2_tarski(A_26, B_27))), inference(cnfTransformation, [status(thm)], [f_89])).
% 3.83/1.63  tff(c_144, plain, (![A_64, B_65]: (k3_tarski(k2_tarski(A_64, B_65))=k2_xboole_0(A_64, B_65))), inference(cnfTransformation, [status(thm)], [f_114])).
% 3.83/1.63  tff(c_251, plain, (![A_84, B_85]: (k3_tarski(k2_tarski(A_84, B_85))=k2_xboole_0(B_85, A_84))), inference(superposition, [status(thm), theory('equality')], [c_56, c_144])).
% 3.83/1.63  tff(c_90, plain, (![A_45, B_46]: (k3_tarski(k2_tarski(A_45, B_46))=k2_xboole_0(A_45, B_46))), inference(cnfTransformation, [status(thm)], [f_114])).
% 3.83/1.63  tff(c_257, plain, (![B_85, A_84]: (k2_xboole_0(B_85, A_84)=k2_xboole_0(A_84, B_85))), inference(superposition, [status(thm), theory('equality')], [c_251, c_90])).
% 3.83/1.63  tff(c_94, plain, (r1_tarski(k2_xboole_0(k1_tarski('#skF_6'), '#skF_7'), '#skF_7')), inference(cnfTransformation, [status(thm)], [f_119])).
% 3.83/1.63  tff(c_277, plain, (r1_tarski(k2_xboole_0('#skF_7', k1_tarski('#skF_6')), '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_257, c_94])).
% 3.83/1.63  tff(c_436, plain, (![B_107, A_108]: (B_107=A_108 | ~r1_tarski(B_107, A_108) | ~r1_tarski(A_108, B_107))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.83/1.63  tff(c_438, plain, (k2_xboole_0('#skF_7', k1_tarski('#skF_6'))='#skF_7' | ~r1_tarski('#skF_7', k2_xboole_0('#skF_7', k1_tarski('#skF_6')))), inference(resolution, [status(thm)], [c_277, c_436])).
% 3.83/1.63  tff(c_449, plain, (k2_xboole_0('#skF_7', k1_tarski('#skF_6'))='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_54, c_438])).
% 3.83/1.63  tff(c_48, plain, (![A_19, C_21, B_20]: (r1_xboole_0(A_19, C_21) | ~r1_xboole_0(A_19, k2_xboole_0(B_20, C_21)))), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.83/1.63  tff(c_462, plain, (![A_19]: (r1_xboole_0(A_19, k1_tarski('#skF_6')) | ~r1_xboole_0(A_19, '#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_449, c_48])).
% 3.83/1.63  tff(c_489, plain, (![A_111, B_112, C_113]: (~r1_xboole_0(A_111, B_112) | ~r2_hidden(C_113, B_112) | ~r2_hidden(C_113, A_111))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.83/1.63  tff(c_661, plain, (![C_137, A_138]: (~r2_hidden(C_137, k1_tarski('#skF_6')) | ~r2_hidden(C_137, A_138) | ~r1_xboole_0(A_138, '#skF_7'))), inference(resolution, [status(thm)], [c_462, c_489])).
% 3.83/1.63  tff(c_674, plain, (![A_139]: (~r2_hidden('#skF_6', A_139) | ~r1_xboole_0(A_139, '#skF_7'))), inference(resolution, [status(thm)], [c_214, c_661])).
% 3.83/1.63  tff(c_705, plain, (~r1_xboole_0(k1_tarski('#skF_6'), '#skF_7')), inference(resolution, [status(thm)], [c_214, c_674])).
% 3.83/1.63  tff(c_92, plain, (~r2_hidden('#skF_6', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_119])).
% 3.83/1.63  tff(c_36, plain, (![A_10, B_11]: (r2_hidden('#skF_3'(A_10, B_11), A_10) | r1_xboole_0(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.83/1.63  tff(c_84, plain, (![A_36, B_37]: (k1_enumset1(A_36, A_36, B_37)=k2_tarski(A_36, B_37))), inference(cnfTransformation, [status(thm)], [f_108])).
% 3.83/1.63  tff(c_1383, plain, (![E_218, C_219, B_220, A_221]: (E_218=C_219 | E_218=B_220 | E_218=A_221 | ~r2_hidden(E_218, k1_enumset1(A_221, B_220, C_219)))), inference(cnfTransformation, [status(thm)], [f_104])).
% 3.83/1.63  tff(c_1498, plain, (![E_239, B_240, A_241]: (E_239=B_240 | E_239=A_241 | E_239=A_241 | ~r2_hidden(E_239, k2_tarski(A_241, B_240)))), inference(superposition, [status(thm), theory('equality')], [c_84, c_1383])).
% 3.83/1.63  tff(c_1528, plain, (![E_242, A_243]: (E_242=A_243 | E_242=A_243 | E_242=A_243 | ~r2_hidden(E_242, k1_tarski(A_243)))), inference(superposition, [status(thm), theory('equality')], [c_82, c_1498])).
% 3.83/1.63  tff(c_1604, plain, (![A_248, B_249]: ('#skF_3'(k1_tarski(A_248), B_249)=A_248 | r1_xboole_0(k1_tarski(A_248), B_249))), inference(resolution, [status(thm)], [c_36, c_1528])).
% 3.83/1.63  tff(c_1622, plain, ('#skF_3'(k1_tarski('#skF_6'), '#skF_7')='#skF_6'), inference(resolution, [status(thm)], [c_1604, c_705])).
% 3.83/1.63  tff(c_34, plain, (![A_10, B_11]: (r2_hidden('#skF_3'(A_10, B_11), B_11) | r1_xboole_0(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.83/1.63  tff(c_1633, plain, (r2_hidden('#skF_6', '#skF_7') | r1_xboole_0(k1_tarski('#skF_6'), '#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_1622, c_34])).
% 3.83/1.63  tff(c_1641, plain, $false, inference(negUnitSimplification, [status(thm)], [c_705, c_92, c_1633])).
% 3.83/1.63  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.83/1.63  
% 3.83/1.63  Inference rules
% 3.83/1.63  ----------------------
% 3.83/1.63  #Ref     : 0
% 3.83/1.63  #Sup     : 354
% 3.83/1.63  #Fact    : 0
% 3.83/1.63  #Define  : 0
% 3.83/1.63  #Split   : 1
% 3.83/1.63  #Chain   : 0
% 3.83/1.63  #Close   : 0
% 3.83/1.63  
% 3.83/1.63  Ordering : KBO
% 3.83/1.63  
% 3.83/1.63  Simplification rules
% 3.83/1.63  ----------------------
% 3.83/1.63  #Subsume      : 60
% 3.83/1.63  #Demod        : 88
% 3.83/1.63  #Tautology    : 132
% 3.83/1.63  #SimpNegUnit  : 3
% 3.83/1.63  #BackRed      : 2
% 3.83/1.63  
% 3.83/1.63  #Partial instantiations: 0
% 3.83/1.63  #Strategies tried      : 1
% 3.83/1.63  
% 3.83/1.63  Timing (in seconds)
% 3.83/1.63  ----------------------
% 3.83/1.63  Preprocessing        : 0.35
% 3.83/1.63  Parsing              : 0.18
% 3.83/1.63  CNF conversion       : 0.03
% 3.83/1.63  Main loop            : 0.52
% 3.83/1.63  Inferencing          : 0.17
% 3.83/1.63  Reduction            : 0.20
% 3.83/1.63  Demodulation         : 0.15
% 3.83/1.63  BG Simplification    : 0.03
% 3.83/1.63  Subsumption          : 0.10
% 3.83/1.63  Abstraction          : 0.03
% 3.83/1.63  MUC search           : 0.00
% 3.83/1.63  Cooper               : 0.00
% 3.83/1.63  Total                : 0.91
% 3.83/1.63  Index Insertion      : 0.00
% 3.83/1.63  Index Deletion       : 0.00
% 3.83/1.63  Index Matching       : 0.00
% 3.83/1.63  BG Taut test         : 0.00
%------------------------------------------------------------------------------
