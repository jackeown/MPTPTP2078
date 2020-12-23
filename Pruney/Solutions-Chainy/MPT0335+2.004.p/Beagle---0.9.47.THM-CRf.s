%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:54:54 EST 2020

% Result     : Theorem 38.39s
% Output     : CNFRefutation 38.45s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 147 expanded)
%              Number of leaves         :   33 (  65 expanded)
%              Depth                    :   14
%              Number of atoms          :   89 ( 218 expanded)
%              Number of equality atoms :   32 (  93 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_11 > #skF_6 > #skF_10 > #skF_2 > #skF_9 > #skF_7 > #skF_8 > #skF_3 > #skF_1 > #skF_5 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_11',type,(
    '#skF_11': $i )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i ) > $i )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_93,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( r1_tarski(A,B)
          & k3_xboole_0(B,C) = k1_tarski(D)
          & r2_hidden(D,A) )
       => k3_xboole_0(A,C) = k1_tarski(D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_zfmisc_1)).

tff(f_67,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_60,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_44,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_46,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_54,axiom,(
    ! [A,B,C] : k3_xboole_0(k3_xboole_0(A,B),C) = k3_xboole_0(A,k3_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_xboole_1)).

tff(f_58,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_34,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_52,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(c_82,plain,(
    r2_hidden('#skF_11','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_44,plain,(
    ! [C_29] : r2_hidden(C_29,k1_tarski(C_29)) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_84,plain,(
    k3_xboole_0('#skF_9','#skF_10') = k1_tarski('#skF_11') ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_214,plain,(
    ! [A_71,B_72] : k4_xboole_0(A_71,k4_xboole_0(A_71,B_72)) = k3_xboole_0(A_71,B_72) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_14,plain,(
    ! [D_13,A_8,B_9] :
      ( r2_hidden(D_13,A_8)
      | ~ r2_hidden(D_13,k4_xboole_0(A_8,B_9)) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_241,plain,(
    ! [D_76,A_77,B_78] :
      ( r2_hidden(D_76,A_77)
      | ~ r2_hidden(D_76,k3_xboole_0(A_77,B_78)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_214,c_14])).

tff(c_417,plain,(
    ! [D_104,B_105,A_106] :
      ( r2_hidden(D_104,B_105)
      | ~ r2_hidden(D_104,k3_xboole_0(A_106,B_105)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_241])).

tff(c_448,plain,(
    ! [D_107] :
      ( r2_hidden(D_107,'#skF_10')
      | ~ r2_hidden(D_107,k1_tarski('#skF_11')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_84,c_417])).

tff(c_468,plain,(
    r2_hidden('#skF_11','#skF_10') ),
    inference(resolution,[status(thm)],[c_44,c_448])).

tff(c_40,plain,(
    ! [A_23,B_24] : k4_xboole_0(A_23,k4_xboole_0(A_23,B_24)) = k3_xboole_0(A_23,B_24) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_1564,plain,(
    ! [D_158,A_159,B_160] :
      ( r2_hidden(D_158,k4_xboole_0(A_159,B_160))
      | r2_hidden(D_158,B_160)
      | ~ r2_hidden(D_158,A_159) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_17143,plain,(
    ! [D_21751,A_21752,B_21753] :
      ( r2_hidden(D_21751,k3_xboole_0(A_21752,B_21753))
      | r2_hidden(D_21751,k4_xboole_0(A_21752,B_21753))
      | ~ r2_hidden(D_21751,A_21752) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_1564])).

tff(c_12,plain,(
    ! [D_13,B_9,A_8] :
      ( ~ r2_hidden(D_13,B_9)
      | ~ r2_hidden(D_13,k4_xboole_0(A_8,B_9)) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_141765,plain,(
    ! [D_71413,B_71414,A_71415] :
      ( ~ r2_hidden(D_71413,B_71414)
      | r2_hidden(D_71413,k3_xboole_0(A_71415,B_71414))
      | ~ r2_hidden(D_71413,A_71415) ) ),
    inference(resolution,[status(thm)],[c_17143,c_12])).

tff(c_80,plain,(
    k3_xboole_0('#skF_8','#skF_10') != k1_tarski('#skF_11') ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_28,plain,(
    ! [A_14] : k3_xboole_0(A_14,A_14) = A_14 ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_611,plain,(
    ! [A_123,B_124,C_125] : k3_xboole_0(k3_xboole_0(A_123,B_124),C_125) = k3_xboole_0(A_123,k3_xboole_0(B_124,C_125)) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_671,plain,(
    ! [A_14,C_125] : k3_xboole_0(A_14,k3_xboole_0(A_14,C_125)) = k3_xboole_0(A_14,C_125) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_611])).

tff(c_86,plain,(
    r1_tarski('#skF_8','#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_161,plain,(
    ! [A_58,B_59] :
      ( k3_xboole_0(A_58,B_59) = A_58
      | ~ r1_tarski(A_58,B_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_170,plain,(
    k3_xboole_0('#skF_8','#skF_9') = '#skF_8' ),
    inference(resolution,[status(thm)],[c_86,c_161])).

tff(c_651,plain,(
    ! [C_125] : k3_xboole_0('#skF_8',k3_xboole_0('#skF_9',C_125)) = k3_xboole_0('#skF_8',C_125) ),
    inference(superposition,[status(thm),theory(equality)],[c_170,c_611])).

tff(c_2370,plain,(
    ! [C_184,A_185,B_186] : k3_xboole_0(C_184,k3_xboole_0(A_185,B_186)) = k3_xboole_0(A_185,k3_xboole_0(B_186,C_184)) ),
    inference(superposition,[status(thm),theory(equality)],[c_611,c_2])).

tff(c_3274,plain,(
    ! [A_191,C_192] : k3_xboole_0(A_191,k3_xboole_0(A_191,C_192)) = k3_xboole_0(C_192,A_191) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_2370])).

tff(c_3460,plain,(
    ! [C_125] : k3_xboole_0(k3_xboole_0('#skF_9',C_125),'#skF_8') = k3_xboole_0('#skF_8',k3_xboole_0('#skF_8',C_125)) ),
    inference(superposition,[status(thm),theory(equality)],[c_651,c_3274])).

tff(c_4280,plain,(
    ! [C_197] : k3_xboole_0(k3_xboole_0('#skF_9',C_197),'#skF_8') = k3_xboole_0('#skF_8',C_197) ),
    inference(demodulation,[status(thm),theory(equality)],[c_671,c_3460])).

tff(c_4406,plain,(
    k3_xboole_0(k1_tarski('#skF_11'),'#skF_8') = k3_xboole_0('#skF_8','#skF_10') ),
    inference(superposition,[status(thm),theory(equality)],[c_84,c_4280])).

tff(c_196,plain,(
    ! [A_67,B_68] :
      ( r2_hidden('#skF_1'(A_67,B_68),A_67)
      | r1_tarski(A_67,B_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_14402,plain,(
    ! [A_13743,B_13744,B_13745] :
      ( r2_hidden('#skF_1'(k4_xboole_0(A_13743,B_13744),B_13745),A_13743)
      | r1_tarski(k4_xboole_0(A_13743,B_13744),B_13745) ) ),
    inference(resolution,[status(thm)],[c_196,c_14])).

tff(c_6,plain,(
    ! [A_3,B_4] :
      ( ~ r2_hidden('#skF_1'(A_3,B_4),B_4)
      | r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_14561,plain,(
    ! [A_13896,B_13897] : r1_tarski(k4_xboole_0(A_13896,B_13897),A_13896) ),
    inference(resolution,[status(thm)],[c_14402,c_6])).

tff(c_14657,plain,(
    ! [A_14120,B_14121] : r1_tarski(k3_xboole_0(A_14120,B_14121),A_14120) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_14561])).

tff(c_14749,plain,(
    r1_tarski(k3_xboole_0('#skF_8','#skF_10'),k1_tarski('#skF_11')) ),
    inference(superposition,[status(thm),theory(equality)],[c_4406,c_14657])).

tff(c_30,plain,(
    ! [B_17,A_16] :
      ( B_17 = A_16
      | ~ r1_tarski(B_17,A_16)
      | ~ r1_tarski(A_16,B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_17584,plain,
    ( k3_xboole_0('#skF_8','#skF_10') = k1_tarski('#skF_11')
    | ~ r1_tarski(k1_tarski('#skF_11'),k3_xboole_0('#skF_8','#skF_10')) ),
    inference(resolution,[status(thm)],[c_14749,c_30])).

tff(c_17642,plain,(
    ~ r1_tarski(k1_tarski('#skF_11'),k3_xboole_0('#skF_8','#skF_10')) ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_17584])).

tff(c_42,plain,(
    ! [C_29,A_25] :
      ( C_29 = A_25
      | ~ r2_hidden(C_29,k1_tarski(A_25)) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_206,plain,(
    ! [A_25,B_68] :
      ( '#skF_1'(k1_tarski(A_25),B_68) = A_25
      | r1_tarski(k1_tarski(A_25),B_68) ) ),
    inference(resolution,[status(thm)],[c_196,c_42])).

tff(c_17661,plain,(
    '#skF_1'(k1_tarski('#skF_11'),k3_xboole_0('#skF_8','#skF_10')) = '#skF_11' ),
    inference(resolution,[status(thm)],[c_206,c_17642])).

tff(c_20260,plain,
    ( ~ r2_hidden('#skF_11',k3_xboole_0('#skF_8','#skF_10'))
    | r1_tarski(k1_tarski('#skF_11'),k3_xboole_0('#skF_8','#skF_10')) ),
    inference(superposition,[status(thm),theory(equality)],[c_17661,c_6])).

tff(c_20322,plain,(
    ~ r2_hidden('#skF_11',k3_xboole_0('#skF_8','#skF_10')) ),
    inference(negUnitSimplification,[status(thm)],[c_17642,c_20260])).

tff(c_141868,plain,
    ( ~ r2_hidden('#skF_11','#skF_10')
    | ~ r2_hidden('#skF_11','#skF_8') ),
    inference(resolution,[status(thm)],[c_141765,c_20322])).

tff(c_142192,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_468,c_141868])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:39:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 38.39/28.13  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 38.43/28.14  
% 38.43/28.14  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 38.45/28.14  %$ r2_hidden > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_11 > #skF_6 > #skF_10 > #skF_2 > #skF_9 > #skF_7 > #skF_8 > #skF_3 > #skF_1 > #skF_5 > #skF_4
% 38.45/28.14  
% 38.45/28.14  %Foreground sorts:
% 38.45/28.14  
% 38.45/28.14  
% 38.45/28.14  %Background operators:
% 38.45/28.14  
% 38.45/28.14  
% 38.45/28.14  %Foreground operators:
% 38.45/28.14  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 38.45/28.14  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 38.45/28.14  tff('#skF_11', type, '#skF_11': $i).
% 38.45/28.14  tff('#skF_6', type, '#skF_6': ($i * $i * $i) > $i).
% 38.45/28.14  tff(k1_tarski, type, k1_tarski: $i > $i).
% 38.45/28.14  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 38.45/28.14  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 38.45/28.14  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 38.45/28.14  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 38.45/28.14  tff('#skF_10', type, '#skF_10': $i).
% 38.45/28.14  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 38.45/28.14  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 38.45/28.14  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 38.45/28.14  tff('#skF_9', type, '#skF_9': $i).
% 38.45/28.14  tff('#skF_7', type, '#skF_7': ($i * $i * $i) > $i).
% 38.45/28.14  tff('#skF_8', type, '#skF_8': $i).
% 38.45/28.14  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 38.45/28.14  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 38.45/28.14  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 38.45/28.14  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 38.45/28.14  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 38.45/28.14  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 38.45/28.14  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 38.45/28.14  
% 38.45/28.16  tff(f_93, negated_conjecture, ~(![A, B, C, D]: (((r1_tarski(A, B) & (k3_xboole_0(B, C) = k1_tarski(D))) & r2_hidden(D, A)) => (k3_xboole_0(A, C) = k1_tarski(D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_zfmisc_1)).
% 38.45/28.16  tff(f_67, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 38.45/28.16  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 38.45/28.16  tff(f_60, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 38.45/28.16  tff(f_44, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 38.45/28.16  tff(f_46, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 38.45/28.16  tff(f_54, axiom, (![A, B, C]: (k3_xboole_0(k3_xboole_0(A, B), C) = k3_xboole_0(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t16_xboole_1)).
% 38.45/28.16  tff(f_58, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 38.45/28.16  tff(f_34, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 38.45/28.16  tff(f_52, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 38.45/28.16  tff(c_82, plain, (r2_hidden('#skF_11', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_93])).
% 38.45/28.16  tff(c_44, plain, (![C_29]: (r2_hidden(C_29, k1_tarski(C_29)))), inference(cnfTransformation, [status(thm)], [f_67])).
% 38.45/28.16  tff(c_84, plain, (k3_xboole_0('#skF_9', '#skF_10')=k1_tarski('#skF_11')), inference(cnfTransformation, [status(thm)], [f_93])).
% 38.45/28.16  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 38.45/28.16  tff(c_214, plain, (![A_71, B_72]: (k4_xboole_0(A_71, k4_xboole_0(A_71, B_72))=k3_xboole_0(A_71, B_72))), inference(cnfTransformation, [status(thm)], [f_60])).
% 38.45/28.16  tff(c_14, plain, (![D_13, A_8, B_9]: (r2_hidden(D_13, A_8) | ~r2_hidden(D_13, k4_xboole_0(A_8, B_9)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 38.45/28.16  tff(c_241, plain, (![D_76, A_77, B_78]: (r2_hidden(D_76, A_77) | ~r2_hidden(D_76, k3_xboole_0(A_77, B_78)))), inference(superposition, [status(thm), theory('equality')], [c_214, c_14])).
% 38.45/28.16  tff(c_417, plain, (![D_104, B_105, A_106]: (r2_hidden(D_104, B_105) | ~r2_hidden(D_104, k3_xboole_0(A_106, B_105)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_241])).
% 38.45/28.16  tff(c_448, plain, (![D_107]: (r2_hidden(D_107, '#skF_10') | ~r2_hidden(D_107, k1_tarski('#skF_11')))), inference(superposition, [status(thm), theory('equality')], [c_84, c_417])).
% 38.45/28.16  tff(c_468, plain, (r2_hidden('#skF_11', '#skF_10')), inference(resolution, [status(thm)], [c_44, c_448])).
% 38.45/28.16  tff(c_40, plain, (![A_23, B_24]: (k4_xboole_0(A_23, k4_xboole_0(A_23, B_24))=k3_xboole_0(A_23, B_24))), inference(cnfTransformation, [status(thm)], [f_60])).
% 38.45/28.16  tff(c_1564, plain, (![D_158, A_159, B_160]: (r2_hidden(D_158, k4_xboole_0(A_159, B_160)) | r2_hidden(D_158, B_160) | ~r2_hidden(D_158, A_159))), inference(cnfTransformation, [status(thm)], [f_44])).
% 38.45/28.16  tff(c_17143, plain, (![D_21751, A_21752, B_21753]: (r2_hidden(D_21751, k3_xboole_0(A_21752, B_21753)) | r2_hidden(D_21751, k4_xboole_0(A_21752, B_21753)) | ~r2_hidden(D_21751, A_21752))), inference(superposition, [status(thm), theory('equality')], [c_40, c_1564])).
% 38.45/28.16  tff(c_12, plain, (![D_13, B_9, A_8]: (~r2_hidden(D_13, B_9) | ~r2_hidden(D_13, k4_xboole_0(A_8, B_9)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 38.45/28.16  tff(c_141765, plain, (![D_71413, B_71414, A_71415]: (~r2_hidden(D_71413, B_71414) | r2_hidden(D_71413, k3_xboole_0(A_71415, B_71414)) | ~r2_hidden(D_71413, A_71415))), inference(resolution, [status(thm)], [c_17143, c_12])).
% 38.45/28.16  tff(c_80, plain, (k3_xboole_0('#skF_8', '#skF_10')!=k1_tarski('#skF_11')), inference(cnfTransformation, [status(thm)], [f_93])).
% 38.45/28.16  tff(c_28, plain, (![A_14]: (k3_xboole_0(A_14, A_14)=A_14)), inference(cnfTransformation, [status(thm)], [f_46])).
% 38.45/28.16  tff(c_611, plain, (![A_123, B_124, C_125]: (k3_xboole_0(k3_xboole_0(A_123, B_124), C_125)=k3_xboole_0(A_123, k3_xboole_0(B_124, C_125)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 38.45/28.16  tff(c_671, plain, (![A_14, C_125]: (k3_xboole_0(A_14, k3_xboole_0(A_14, C_125))=k3_xboole_0(A_14, C_125))), inference(superposition, [status(thm), theory('equality')], [c_28, c_611])).
% 38.45/28.16  tff(c_86, plain, (r1_tarski('#skF_8', '#skF_9')), inference(cnfTransformation, [status(thm)], [f_93])).
% 38.45/28.16  tff(c_161, plain, (![A_58, B_59]: (k3_xboole_0(A_58, B_59)=A_58 | ~r1_tarski(A_58, B_59))), inference(cnfTransformation, [status(thm)], [f_58])).
% 38.45/28.16  tff(c_170, plain, (k3_xboole_0('#skF_8', '#skF_9')='#skF_8'), inference(resolution, [status(thm)], [c_86, c_161])).
% 38.45/28.16  tff(c_651, plain, (![C_125]: (k3_xboole_0('#skF_8', k3_xboole_0('#skF_9', C_125))=k3_xboole_0('#skF_8', C_125))), inference(superposition, [status(thm), theory('equality')], [c_170, c_611])).
% 38.45/28.16  tff(c_2370, plain, (![C_184, A_185, B_186]: (k3_xboole_0(C_184, k3_xboole_0(A_185, B_186))=k3_xboole_0(A_185, k3_xboole_0(B_186, C_184)))), inference(superposition, [status(thm), theory('equality')], [c_611, c_2])).
% 38.45/28.16  tff(c_3274, plain, (![A_191, C_192]: (k3_xboole_0(A_191, k3_xboole_0(A_191, C_192))=k3_xboole_0(C_192, A_191))), inference(superposition, [status(thm), theory('equality')], [c_28, c_2370])).
% 38.45/28.16  tff(c_3460, plain, (![C_125]: (k3_xboole_0(k3_xboole_0('#skF_9', C_125), '#skF_8')=k3_xboole_0('#skF_8', k3_xboole_0('#skF_8', C_125)))), inference(superposition, [status(thm), theory('equality')], [c_651, c_3274])).
% 38.45/28.16  tff(c_4280, plain, (![C_197]: (k3_xboole_0(k3_xboole_0('#skF_9', C_197), '#skF_8')=k3_xboole_0('#skF_8', C_197))), inference(demodulation, [status(thm), theory('equality')], [c_671, c_3460])).
% 38.45/28.16  tff(c_4406, plain, (k3_xboole_0(k1_tarski('#skF_11'), '#skF_8')=k3_xboole_0('#skF_8', '#skF_10')), inference(superposition, [status(thm), theory('equality')], [c_84, c_4280])).
% 38.45/28.16  tff(c_196, plain, (![A_67, B_68]: (r2_hidden('#skF_1'(A_67, B_68), A_67) | r1_tarski(A_67, B_68))), inference(cnfTransformation, [status(thm)], [f_34])).
% 38.45/28.16  tff(c_14402, plain, (![A_13743, B_13744, B_13745]: (r2_hidden('#skF_1'(k4_xboole_0(A_13743, B_13744), B_13745), A_13743) | r1_tarski(k4_xboole_0(A_13743, B_13744), B_13745))), inference(resolution, [status(thm)], [c_196, c_14])).
% 38.45/28.16  tff(c_6, plain, (![A_3, B_4]: (~r2_hidden('#skF_1'(A_3, B_4), B_4) | r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_34])).
% 38.45/28.16  tff(c_14561, plain, (![A_13896, B_13897]: (r1_tarski(k4_xboole_0(A_13896, B_13897), A_13896))), inference(resolution, [status(thm)], [c_14402, c_6])).
% 38.45/28.16  tff(c_14657, plain, (![A_14120, B_14121]: (r1_tarski(k3_xboole_0(A_14120, B_14121), A_14120))), inference(superposition, [status(thm), theory('equality')], [c_40, c_14561])).
% 38.45/28.16  tff(c_14749, plain, (r1_tarski(k3_xboole_0('#skF_8', '#skF_10'), k1_tarski('#skF_11'))), inference(superposition, [status(thm), theory('equality')], [c_4406, c_14657])).
% 38.45/28.16  tff(c_30, plain, (![B_17, A_16]: (B_17=A_16 | ~r1_tarski(B_17, A_16) | ~r1_tarski(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_52])).
% 38.45/28.16  tff(c_17584, plain, (k3_xboole_0('#skF_8', '#skF_10')=k1_tarski('#skF_11') | ~r1_tarski(k1_tarski('#skF_11'), k3_xboole_0('#skF_8', '#skF_10'))), inference(resolution, [status(thm)], [c_14749, c_30])).
% 38.45/28.16  tff(c_17642, plain, (~r1_tarski(k1_tarski('#skF_11'), k3_xboole_0('#skF_8', '#skF_10'))), inference(negUnitSimplification, [status(thm)], [c_80, c_17584])).
% 38.45/28.16  tff(c_42, plain, (![C_29, A_25]: (C_29=A_25 | ~r2_hidden(C_29, k1_tarski(A_25)))), inference(cnfTransformation, [status(thm)], [f_67])).
% 38.45/28.16  tff(c_206, plain, (![A_25, B_68]: ('#skF_1'(k1_tarski(A_25), B_68)=A_25 | r1_tarski(k1_tarski(A_25), B_68))), inference(resolution, [status(thm)], [c_196, c_42])).
% 38.45/28.16  tff(c_17661, plain, ('#skF_1'(k1_tarski('#skF_11'), k3_xboole_0('#skF_8', '#skF_10'))='#skF_11'), inference(resolution, [status(thm)], [c_206, c_17642])).
% 38.45/28.16  tff(c_20260, plain, (~r2_hidden('#skF_11', k3_xboole_0('#skF_8', '#skF_10')) | r1_tarski(k1_tarski('#skF_11'), k3_xboole_0('#skF_8', '#skF_10'))), inference(superposition, [status(thm), theory('equality')], [c_17661, c_6])).
% 38.45/28.16  tff(c_20322, plain, (~r2_hidden('#skF_11', k3_xboole_0('#skF_8', '#skF_10'))), inference(negUnitSimplification, [status(thm)], [c_17642, c_20260])).
% 38.45/28.16  tff(c_141868, plain, (~r2_hidden('#skF_11', '#skF_10') | ~r2_hidden('#skF_11', '#skF_8')), inference(resolution, [status(thm)], [c_141765, c_20322])).
% 38.45/28.16  tff(c_142192, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_82, c_468, c_141868])).
% 38.45/28.16  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 38.45/28.16  
% 38.45/28.16  Inference rules
% 38.45/28.16  ----------------------
% 38.45/28.16  #Ref     : 0
% 38.45/28.16  #Sup     : 31499
% 38.45/28.16  #Fact    : 238
% 38.45/28.16  #Define  : 0
% 38.45/28.16  #Split   : 6
% 38.45/28.16  #Chain   : 0
% 38.45/28.16  #Close   : 0
% 38.45/28.16  
% 38.45/28.16  Ordering : KBO
% 38.45/28.16  
% 38.45/28.16  Simplification rules
% 38.45/28.16  ----------------------
% 38.45/28.16  #Subsume      : 7532
% 38.45/28.16  #Demod        : 26192
% 38.45/28.16  #Tautology    : 11995
% 38.45/28.16  #SimpNegUnit  : 310
% 38.45/28.16  #BackRed      : 47
% 38.45/28.16  
% 38.45/28.16  #Partial instantiations: 34218
% 38.45/28.16  #Strategies tried      : 1
% 38.45/28.16  
% 38.45/28.16  Timing (in seconds)
% 38.45/28.16  ----------------------
% 38.45/28.16  Preprocessing        : 0.36
% 38.45/28.16  Parsing              : 0.18
% 38.45/28.16  CNF conversion       : 0.03
% 38.45/28.16  Main loop            : 27.02
% 38.45/28.16  Inferencing          : 3.59
% 38.45/28.16  Reduction            : 15.55
% 38.45/28.16  Demodulation         : 13.89
% 38.45/28.16  BG Simplification    : 0.41
% 38.45/28.16  Subsumption          : 6.31
% 38.45/28.16  Abstraction          : 0.67
% 38.45/28.16  MUC search           : 0.00
% 38.45/28.16  Cooper               : 0.00
% 38.45/28.16  Total                : 27.42
% 38.45/28.16  Index Insertion      : 0.00
% 38.45/28.16  Index Deletion       : 0.00
% 38.45/28.16  Index Matching       : 0.00
% 38.45/28.16  BG Taut test         : 0.00
%------------------------------------------------------------------------------
