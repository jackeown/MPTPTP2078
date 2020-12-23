%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:50:34 EST 2020

% Result     : Theorem 3.03s
% Output     : CNFRefutation 3.14s
% Verified   : 
% Statistics : Number of formulae       :   66 (  76 expanded)
%              Number of leaves         :   34 (  39 expanded)
%              Depth                    :   12
%              Number of atoms          :   80 (  95 expanded)
%              Number of equality atoms :   27 (  36 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > #skF_2 > #skF_3 > #skF_4 > #skF_1

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

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i ) > $i )).

tff(f_83,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_85,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_81,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

tff(f_101,negated_conjecture,(
    ~ ! [A,B] :
        ( r1_tarski(k2_xboole_0(k1_tarski(A),B),B)
       => r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_zfmisc_1)).

tff(f_60,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_66,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_96,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_40,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_94,axiom,(
    ! [A,B] :
      ( ~ r2_hidden(A,B)
     => r1_xboole_0(k1_tarski(A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l27_zfmisc_1)).

tff(f_58,axiom,(
    ! [A,B,C] :
      ( ~ ( ~ r1_xboole_0(A,k2_xboole_0(B,C))
          & r1_xboole_0(A,B)
          & r1_xboole_0(A,C) )
      & ~ ( ~ ( r1_xboole_0(A,B)
              & r1_xboole_0(A,C) )
          & r1_xboole_0(A,k2_xboole_0(B,C)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_xboole_1)).

tff(f_64,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_42,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_34,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k5_xboole_0(B,C))
    <=> ~ ( r2_hidden(A,B)
        <=> r2_hidden(A,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_0)).

tff(c_62,plain,(
    ! [A_26] : k2_tarski(A_26,A_26) = k1_tarski(A_26) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_135,plain,(
    ! [A_58,B_59] : k1_enumset1(A_58,A_58,B_59) = k2_tarski(A_58,B_59) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_44,plain,(
    ! [E_25,B_20,C_21] : r2_hidden(E_25,k1_enumset1(E_25,B_20,C_21)) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_153,plain,(
    ! [A_60,B_61] : r2_hidden(A_60,k2_tarski(A_60,B_61)) ),
    inference(superposition,[status(thm),theory(equality)],[c_135,c_44])).

tff(c_162,plain,(
    ! [A_26] : r2_hidden(A_26,k1_tarski(A_26)) ),
    inference(superposition,[status(thm),theory(equality)],[c_62,c_153])).

tff(c_74,plain,(
    ~ r2_hidden('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_30,plain,(
    ! [A_13,B_14] : r1_tarski(A_13,k2_xboole_0(A_13,B_14)) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_36,plain,(
    ! [B_18,A_17] : k2_tarski(B_18,A_17) = k2_tarski(A_17,B_18) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_185,plain,(
    ! [A_67,B_68] : k3_tarski(k2_tarski(A_67,B_68)) = k2_xboole_0(A_67,B_68) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_233,plain,(
    ! [B_73,A_74] : k3_tarski(k2_tarski(B_73,A_74)) = k2_xboole_0(A_74,B_73) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_185])).

tff(c_72,plain,(
    ! [A_38,B_39] : k3_tarski(k2_tarski(A_38,B_39)) = k2_xboole_0(A_38,B_39) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_239,plain,(
    ! [B_73,A_74] : k2_xboole_0(B_73,A_74) = k2_xboole_0(A_74,B_73) ),
    inference(superposition,[status(thm),theory(equality)],[c_233,c_72])).

tff(c_76,plain,(
    r1_tarski(k2_xboole_0(k1_tarski('#skF_3'),'#skF_4'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_259,plain,(
    r1_tarski(k2_xboole_0('#skF_4',k1_tarski('#skF_3')),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_239,c_76])).

tff(c_16,plain,(
    ! [B_7,A_6] :
      ( B_7 = A_6
      | ~ r1_tarski(B_7,A_6)
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_330,plain,
    ( k2_xboole_0('#skF_4',k1_tarski('#skF_3')) = '#skF_4'
    | ~ r1_tarski('#skF_4',k2_xboole_0('#skF_4',k1_tarski('#skF_3'))) ),
    inference(resolution,[status(thm)],[c_259,c_16])).

tff(c_333,plain,(
    k2_xboole_0('#skF_4',k1_tarski('#skF_3')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_330])).

tff(c_70,plain,(
    ! [A_36,B_37] :
      ( r1_xboole_0(k1_tarski(A_36),B_37)
      | r2_hidden(A_36,B_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_352,plain,(
    ! [A_81,C_82,B_83] :
      ( r1_xboole_0(A_81,C_82)
      | ~ r1_xboole_0(A_81,k2_xboole_0(B_83,C_82)) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_553,plain,(
    ! [A_115,C_116,B_117] :
      ( r1_xboole_0(k1_tarski(A_115),C_116)
      | r2_hidden(A_115,k2_xboole_0(B_117,C_116)) ) ),
    inference(resolution,[status(thm)],[c_70,c_352])).

tff(c_566,plain,(
    ! [A_118] :
      ( r1_xboole_0(k1_tarski(A_118),k1_tarski('#skF_3'))
      | r2_hidden(A_118,'#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_333,c_553])).

tff(c_32,plain,(
    ! [A_15,B_16] :
      ( k4_xboole_0(A_15,B_16) = A_15
      | ~ r1_xboole_0(A_15,B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_570,plain,(
    ! [A_118] :
      ( k4_xboole_0(k1_tarski(A_118),k1_tarski('#skF_3')) = k1_tarski(A_118)
      | r2_hidden(A_118,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_566,c_32])).

tff(c_2,plain,(
    ! [A_1] : k3_xboole_0(A_1,A_1) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_403,plain,(
    ! [A_88,B_89] : k5_xboole_0(A_88,k3_xboole_0(A_88,B_89)) = k4_xboole_0(A_88,B_89) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_412,plain,(
    ! [A_1] : k5_xboole_0(A_1,A_1) = k4_xboole_0(A_1,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_403])).

tff(c_571,plain,(
    ! [A_119,C_120,B_121] :
      ( ~ r2_hidden(A_119,C_120)
      | ~ r2_hidden(A_119,B_121)
      | ~ r2_hidden(A_119,k5_xboole_0(B_121,C_120)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_955,plain,(
    ! [A_173,A_174] :
      ( ~ r2_hidden(A_173,A_174)
      | ~ r2_hidden(A_173,A_174)
      | ~ r2_hidden(A_173,k4_xboole_0(A_174,A_174)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_412,c_571])).

tff(c_967,plain,(
    ! [A_173] :
      ( ~ r2_hidden(A_173,k1_tarski('#skF_3'))
      | ~ r2_hidden(A_173,k1_tarski('#skF_3'))
      | ~ r2_hidden(A_173,k1_tarski('#skF_3'))
      | r2_hidden('#skF_3','#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_570,c_955])).

tff(c_1089,plain,(
    ! [A_185] :
      ( ~ r2_hidden(A_185,k1_tarski('#skF_3'))
      | ~ r2_hidden(A_185,k1_tarski('#skF_3'))
      | ~ r2_hidden(A_185,k1_tarski('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_967])).

tff(c_1092,plain,(
    ~ r2_hidden('#skF_3',k1_tarski('#skF_3')) ),
    inference(resolution,[status(thm)],[c_162,c_1089])).

tff(c_1096,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_162,c_1092])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.07  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.07  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.07/0.26  % Computer   : n017.cluster.edu
% 0.07/0.26  % Model      : x86_64 x86_64
% 0.07/0.26  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.07/0.26  % Memory     : 8042.1875MB
% 0.07/0.26  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.07/0.26  % CPULimit   : 60
% 0.07/0.26  % DateTime   : Tue Dec  1 19:44:46 EST 2020
% 0.07/0.26  % CPUTime    : 
% 0.07/0.26  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.03/1.44  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.03/1.45  
% 3.03/1.45  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.14/1.45  %$ r2_hidden > r1_xboole_0 > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 3.14/1.45  
% 3.14/1.45  %Foreground sorts:
% 3.14/1.45  
% 3.14/1.45  
% 3.14/1.45  %Background operators:
% 3.14/1.45  
% 3.14/1.45  
% 3.14/1.45  %Foreground operators:
% 3.14/1.45  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.14/1.45  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.14/1.45  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.14/1.45  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.14/1.45  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.14/1.45  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.14/1.45  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.14/1.45  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.14/1.45  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.14/1.45  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 3.14/1.45  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.14/1.45  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.14/1.45  tff('#skF_3', type, '#skF_3': $i).
% 3.14/1.45  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.14/1.45  tff(k3_tarski, type, k3_tarski: $i > $i).
% 3.14/1.45  tff('#skF_4', type, '#skF_4': $i).
% 3.14/1.45  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.14/1.45  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.14/1.45  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.14/1.45  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 3.14/1.45  
% 3.14/1.47  tff(f_83, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 3.14/1.47  tff(f_85, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 3.14/1.47  tff(f_81, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_enumset1)).
% 3.14/1.47  tff(f_101, negated_conjecture, ~(![A, B]: (r1_tarski(k2_xboole_0(k1_tarski(A), B), B) => r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t45_zfmisc_1)).
% 3.14/1.47  tff(f_60, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 3.14/1.47  tff(f_66, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 3.14/1.47  tff(f_96, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 3.14/1.47  tff(f_40, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.14/1.47  tff(f_94, axiom, (![A, B]: (~r2_hidden(A, B) => r1_xboole_0(k1_tarski(A), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 3.14/1.47  tff(f_58, axiom, (![A, B, C]: (~((~r1_xboole_0(A, k2_xboole_0(B, C)) & r1_xboole_0(A, B)) & r1_xboole_0(A, C)) & ~(~(r1_xboole_0(A, B) & r1_xboole_0(A, C)) & r1_xboole_0(A, k2_xboole_0(B, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_xboole_1)).
% 3.14/1.47  tff(f_64, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 3.14/1.47  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 3.14/1.47  tff(f_42, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 3.14/1.47  tff(f_34, axiom, (![A, B, C]: (r2_hidden(A, k5_xboole_0(B, C)) <=> ~(r2_hidden(A, B) <=> r2_hidden(A, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_0)).
% 3.14/1.47  tff(c_62, plain, (![A_26]: (k2_tarski(A_26, A_26)=k1_tarski(A_26))), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.14/1.47  tff(c_135, plain, (![A_58, B_59]: (k1_enumset1(A_58, A_58, B_59)=k2_tarski(A_58, B_59))), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.14/1.47  tff(c_44, plain, (![E_25, B_20, C_21]: (r2_hidden(E_25, k1_enumset1(E_25, B_20, C_21)))), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.14/1.47  tff(c_153, plain, (![A_60, B_61]: (r2_hidden(A_60, k2_tarski(A_60, B_61)))), inference(superposition, [status(thm), theory('equality')], [c_135, c_44])).
% 3.14/1.47  tff(c_162, plain, (![A_26]: (r2_hidden(A_26, k1_tarski(A_26)))), inference(superposition, [status(thm), theory('equality')], [c_62, c_153])).
% 3.14/1.47  tff(c_74, plain, (~r2_hidden('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_101])).
% 3.14/1.47  tff(c_30, plain, (![A_13, B_14]: (r1_tarski(A_13, k2_xboole_0(A_13, B_14)))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.14/1.47  tff(c_36, plain, (![B_18, A_17]: (k2_tarski(B_18, A_17)=k2_tarski(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.14/1.47  tff(c_185, plain, (![A_67, B_68]: (k3_tarski(k2_tarski(A_67, B_68))=k2_xboole_0(A_67, B_68))), inference(cnfTransformation, [status(thm)], [f_96])).
% 3.14/1.47  tff(c_233, plain, (![B_73, A_74]: (k3_tarski(k2_tarski(B_73, A_74))=k2_xboole_0(A_74, B_73))), inference(superposition, [status(thm), theory('equality')], [c_36, c_185])).
% 3.14/1.47  tff(c_72, plain, (![A_38, B_39]: (k3_tarski(k2_tarski(A_38, B_39))=k2_xboole_0(A_38, B_39))), inference(cnfTransformation, [status(thm)], [f_96])).
% 3.14/1.47  tff(c_239, plain, (![B_73, A_74]: (k2_xboole_0(B_73, A_74)=k2_xboole_0(A_74, B_73))), inference(superposition, [status(thm), theory('equality')], [c_233, c_72])).
% 3.14/1.47  tff(c_76, plain, (r1_tarski(k2_xboole_0(k1_tarski('#skF_3'), '#skF_4'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_101])).
% 3.14/1.47  tff(c_259, plain, (r1_tarski(k2_xboole_0('#skF_4', k1_tarski('#skF_3')), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_239, c_76])).
% 3.14/1.47  tff(c_16, plain, (![B_7, A_6]: (B_7=A_6 | ~r1_tarski(B_7, A_6) | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.14/1.47  tff(c_330, plain, (k2_xboole_0('#skF_4', k1_tarski('#skF_3'))='#skF_4' | ~r1_tarski('#skF_4', k2_xboole_0('#skF_4', k1_tarski('#skF_3')))), inference(resolution, [status(thm)], [c_259, c_16])).
% 3.14/1.47  tff(c_333, plain, (k2_xboole_0('#skF_4', k1_tarski('#skF_3'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_30, c_330])).
% 3.14/1.47  tff(c_70, plain, (![A_36, B_37]: (r1_xboole_0(k1_tarski(A_36), B_37) | r2_hidden(A_36, B_37))), inference(cnfTransformation, [status(thm)], [f_94])).
% 3.14/1.47  tff(c_352, plain, (![A_81, C_82, B_83]: (r1_xboole_0(A_81, C_82) | ~r1_xboole_0(A_81, k2_xboole_0(B_83, C_82)))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.14/1.47  tff(c_553, plain, (![A_115, C_116, B_117]: (r1_xboole_0(k1_tarski(A_115), C_116) | r2_hidden(A_115, k2_xboole_0(B_117, C_116)))), inference(resolution, [status(thm)], [c_70, c_352])).
% 3.14/1.47  tff(c_566, plain, (![A_118]: (r1_xboole_0(k1_tarski(A_118), k1_tarski('#skF_3')) | r2_hidden(A_118, '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_333, c_553])).
% 3.14/1.47  tff(c_32, plain, (![A_15, B_16]: (k4_xboole_0(A_15, B_16)=A_15 | ~r1_xboole_0(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.14/1.47  tff(c_570, plain, (![A_118]: (k4_xboole_0(k1_tarski(A_118), k1_tarski('#skF_3'))=k1_tarski(A_118) | r2_hidden(A_118, '#skF_4'))), inference(resolution, [status(thm)], [c_566, c_32])).
% 3.14/1.47  tff(c_2, plain, (![A_1]: (k3_xboole_0(A_1, A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.14/1.47  tff(c_403, plain, (![A_88, B_89]: (k5_xboole_0(A_88, k3_xboole_0(A_88, B_89))=k4_xboole_0(A_88, B_89))), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.14/1.47  tff(c_412, plain, (![A_1]: (k5_xboole_0(A_1, A_1)=k4_xboole_0(A_1, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_403])).
% 3.14/1.47  tff(c_571, plain, (![A_119, C_120, B_121]: (~r2_hidden(A_119, C_120) | ~r2_hidden(A_119, B_121) | ~r2_hidden(A_119, k5_xboole_0(B_121, C_120)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.14/1.47  tff(c_955, plain, (![A_173, A_174]: (~r2_hidden(A_173, A_174) | ~r2_hidden(A_173, A_174) | ~r2_hidden(A_173, k4_xboole_0(A_174, A_174)))), inference(superposition, [status(thm), theory('equality')], [c_412, c_571])).
% 3.14/1.47  tff(c_967, plain, (![A_173]: (~r2_hidden(A_173, k1_tarski('#skF_3')) | ~r2_hidden(A_173, k1_tarski('#skF_3')) | ~r2_hidden(A_173, k1_tarski('#skF_3')) | r2_hidden('#skF_3', '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_570, c_955])).
% 3.14/1.47  tff(c_1089, plain, (![A_185]: (~r2_hidden(A_185, k1_tarski('#skF_3')) | ~r2_hidden(A_185, k1_tarski('#skF_3')) | ~r2_hidden(A_185, k1_tarski('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_74, c_967])).
% 3.14/1.47  tff(c_1092, plain, (~r2_hidden('#skF_3', k1_tarski('#skF_3'))), inference(resolution, [status(thm)], [c_162, c_1089])).
% 3.14/1.47  tff(c_1096, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_162, c_1092])).
% 3.14/1.47  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.14/1.47  
% 3.14/1.47  Inference rules
% 3.14/1.47  ----------------------
% 3.14/1.47  #Ref     : 0
% 3.14/1.47  #Sup     : 247
% 3.14/1.47  #Fact    : 0
% 3.14/1.47  #Define  : 0
% 3.14/1.47  #Split   : 1
% 3.14/1.47  #Chain   : 0
% 3.14/1.47  #Close   : 0
% 3.14/1.47  
% 3.14/1.47  Ordering : KBO
% 3.14/1.47  
% 3.14/1.47  Simplification rules
% 3.14/1.47  ----------------------
% 3.14/1.47  #Subsume      : 55
% 3.14/1.47  #Demod        : 32
% 3.14/1.47  #Tautology    : 132
% 3.14/1.47  #SimpNegUnit  : 2
% 3.14/1.47  #BackRed      : 2
% 3.14/1.47  
% 3.14/1.47  #Partial instantiations: 0
% 3.14/1.47  #Strategies tried      : 1
% 3.14/1.47  
% 3.14/1.47  Timing (in seconds)
% 3.14/1.47  ----------------------
% 3.14/1.47  Preprocessing        : 0.41
% 3.14/1.47  Parsing              : 0.21
% 3.14/1.47  CNF conversion       : 0.03
% 3.14/1.47  Main loop            : 0.39
% 3.14/1.47  Inferencing          : 0.15
% 3.14/1.47  Reduction            : 0.13
% 3.14/1.47  Demodulation         : 0.09
% 3.14/1.47  BG Simplification    : 0.03
% 3.14/1.47  Subsumption          : 0.08
% 3.14/1.47  Abstraction          : 0.02
% 3.14/1.47  MUC search           : 0.00
% 3.14/1.47  Cooper               : 0.00
% 3.14/1.47  Total                : 0.84
% 3.14/1.47  Index Insertion      : 0.00
% 3.14/1.47  Index Deletion       : 0.00
% 3.14/1.47  Index Matching       : 0.00
% 3.14/1.47  BG Taut test         : 0.00
%------------------------------------------------------------------------------
