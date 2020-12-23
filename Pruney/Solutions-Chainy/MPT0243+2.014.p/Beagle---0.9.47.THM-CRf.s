%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:49:56 EST 2020

% Result     : Theorem 3.13s
% Output     : CNFRefutation 3.13s
% Verified   : 
% Statistics : Number of formulae       :   72 ( 147 expanded)
%              Number of leaves         :   21 (  54 expanded)
%              Depth                    :    8
%              Number of atoms          :   94 ( 270 expanded)
%              Number of equality atoms :    6 (  16 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_73,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r1_tarski(k2_tarski(A,B),C)
      <=> ( r2_hidden(A,C)
          & r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).

tff(f_62,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k2_tarski(B,C))
    <=> ~ ( A != k1_xboole_0
          & A != k1_tarski(B)
          & A != k1_tarski(C)
          & A != k2_tarski(B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l45_zfmisc_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_66,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_zfmisc_1)).

tff(f_43,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_xboole_0(k1_tarski(A),k1_tarski(B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_enumset1)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(C,B) )
     => r1_tarski(k2_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_xboole_1)).

tff(c_32,plain,
    ( r2_hidden('#skF_1','#skF_3')
    | ~ r2_hidden('#skF_5','#skF_6')
    | ~ r2_hidden('#skF_4','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_94,plain,(
    ~ r2_hidden('#skF_4','#skF_6') ),
    inference(splitLeft,[status(thm)],[c_32])).

tff(c_20,plain,(
    ! [B_15,C_16] : r1_tarski(k1_tarski(B_15),k2_tarski(B_15,C_16)) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_38,plain,
    ( r2_hidden('#skF_1','#skF_3')
    | r1_tarski(k2_tarski('#skF_4','#skF_5'),'#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_59,plain,(
    r1_tarski(k2_tarski('#skF_4','#skF_5'),'#skF_6') ),
    inference(splitLeft,[status(thm)],[c_38])).

tff(c_75,plain,(
    ! [A_40,C_41,B_42] :
      ( r1_tarski(A_40,C_41)
      | ~ r1_tarski(B_42,C_41)
      | ~ r1_tarski(A_40,B_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_109,plain,(
    ! [A_46] :
      ( r1_tarski(A_46,'#skF_6')
      | ~ r1_tarski(A_46,k2_tarski('#skF_4','#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_59,c_75])).

tff(c_139,plain,(
    r1_tarski(k1_tarski('#skF_4'),'#skF_6') ),
    inference(resolution,[status(thm)],[c_20,c_109])).

tff(c_24,plain,(
    ! [A_17,B_18] :
      ( r2_hidden(A_17,B_18)
      | ~ r1_tarski(k1_tarski(A_17),B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_155,plain,(
    r2_hidden('#skF_4','#skF_6') ),
    inference(resolution,[status(thm)],[c_139,c_24])).

tff(c_160,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_94,c_155])).

tff(c_162,plain,(
    r2_hidden('#skF_4','#skF_6') ),
    inference(splitRight,[status(thm)],[c_32])).

tff(c_161,plain,
    ( ~ r2_hidden('#skF_5','#skF_6')
    | r2_hidden('#skF_1','#skF_3') ),
    inference(splitRight,[status(thm)],[c_32])).

tff(c_163,plain,(
    ~ r2_hidden('#skF_5','#skF_6') ),
    inference(splitLeft,[status(thm)],[c_161])).

tff(c_18,plain,(
    ! [C_16,B_15] : r1_tarski(k1_tarski(C_16),k2_tarski(B_15,C_16)) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_178,plain,(
    ! [A_50] :
      ( r1_tarski(A_50,'#skF_6')
      | ~ r1_tarski(A_50,k2_tarski('#skF_4','#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_59,c_75])).

tff(c_207,plain,(
    r1_tarski(k1_tarski('#skF_5'),'#skF_6') ),
    inference(resolution,[status(thm)],[c_18,c_178])).

tff(c_219,plain,(
    r2_hidden('#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_207,c_24])).

tff(c_224,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_163,c_219])).

tff(c_226,plain,(
    r2_hidden('#skF_5','#skF_6') ),
    inference(splitRight,[status(thm)],[c_161])).

tff(c_30,plain,
    ( r2_hidden('#skF_2','#skF_3')
    | ~ r2_hidden('#skF_5','#skF_6')
    | ~ r2_hidden('#skF_4','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_242,plain,(
    r2_hidden('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_162,c_226,c_30])).

tff(c_26,plain,(
    ! [A_17,B_18] :
      ( r1_tarski(k1_tarski(A_17),B_18)
      | ~ r2_hidden(A_17,B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_225,plain,(
    r2_hidden('#skF_1','#skF_3') ),
    inference(splitRight,[status(thm)],[c_161])).

tff(c_8,plain,(
    ! [A_10,B_11] : k2_xboole_0(k1_tarski(A_10),k1_tarski(B_11)) = k2_tarski(A_10,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_409,plain,(
    ! [A_75,C_76,B_77] :
      ( r1_tarski(k2_xboole_0(A_75,C_76),B_77)
      | ~ r1_tarski(C_76,B_77)
      | ~ r1_tarski(A_75,B_77) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_690,plain,(
    ! [A_129,B_130,B_131] :
      ( r1_tarski(k2_tarski(A_129,B_130),B_131)
      | ~ r1_tarski(k1_tarski(B_130),B_131)
      | ~ r1_tarski(k1_tarski(A_129),B_131) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_409])).

tff(c_28,plain,
    ( ~ r1_tarski(k2_tarski('#skF_1','#skF_2'),'#skF_3')
    | ~ r2_hidden('#skF_5','#skF_6')
    | ~ r2_hidden('#skF_4','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_311,plain,(
    ~ r1_tarski(k2_tarski('#skF_1','#skF_2'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_162,c_226,c_28])).

tff(c_735,plain,
    ( ~ r1_tarski(k1_tarski('#skF_2'),'#skF_3')
    | ~ r1_tarski(k1_tarski('#skF_1'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_690,c_311])).

tff(c_739,plain,(
    ~ r1_tarski(k1_tarski('#skF_1'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_735])).

tff(c_742,plain,(
    ~ r2_hidden('#skF_1','#skF_3') ),
    inference(resolution,[status(thm)],[c_26,c_739])).

tff(c_746,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_225,c_742])).

tff(c_747,plain,(
    ~ r1_tarski(k1_tarski('#skF_2'),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_735])).

tff(c_751,plain,(
    ~ r2_hidden('#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_26,c_747])).

tff(c_755,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_242,c_751])).

tff(c_757,plain,(
    ~ r1_tarski(k2_tarski('#skF_4','#skF_5'),'#skF_6') ),
    inference(splitRight,[status(thm)],[c_38])).

tff(c_36,plain,
    ( r2_hidden('#skF_2','#skF_3')
    | r1_tarski(k2_tarski('#skF_4','#skF_5'),'#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_758,plain,(
    r2_hidden('#skF_2','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_757,c_36])).

tff(c_756,plain,(
    r2_hidden('#skF_1','#skF_3') ),
    inference(splitRight,[status(thm)],[c_38])).

tff(c_868,plain,(
    ! [A_165,C_166,B_167] :
      ( r1_tarski(k2_xboole_0(A_165,C_166),B_167)
      | ~ r1_tarski(C_166,B_167)
      | ~ r1_tarski(A_165,B_167) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_1036,plain,(
    ! [A_211,B_212,B_213] :
      ( r1_tarski(k2_tarski(A_211,B_212),B_213)
      | ~ r1_tarski(k1_tarski(B_212),B_213)
      | ~ r1_tarski(k1_tarski(A_211),B_213) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_868])).

tff(c_34,plain,
    ( ~ r1_tarski(k2_tarski('#skF_1','#skF_2'),'#skF_3')
    | r1_tarski(k2_tarski('#skF_4','#skF_5'),'#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_854,plain,(
    ~ r1_tarski(k2_tarski('#skF_1','#skF_2'),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_757,c_34])).

tff(c_1068,plain,
    ( ~ r1_tarski(k1_tarski('#skF_2'),'#skF_3')
    | ~ r1_tarski(k1_tarski('#skF_1'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_1036,c_854])).

tff(c_1072,plain,(
    ~ r1_tarski(k1_tarski('#skF_1'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_1068])).

tff(c_1075,plain,(
    ~ r2_hidden('#skF_1','#skF_3') ),
    inference(resolution,[status(thm)],[c_26,c_1072])).

tff(c_1079,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_756,c_1075])).

tff(c_1080,plain,(
    ~ r1_tarski(k1_tarski('#skF_2'),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_1068])).

tff(c_1084,plain,(
    ~ r2_hidden('#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_26,c_1080])).

tff(c_1088,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_758,c_1084])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n005.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 16:48:17 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.13/1.48  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.13/1.48  
% 3.13/1.48  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.13/1.48  %$ r2_hidden > r1_tarski > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 3.13/1.48  
% 3.13/1.48  %Foreground sorts:
% 3.13/1.48  
% 3.13/1.48  
% 3.13/1.48  %Background operators:
% 3.13/1.48  
% 3.13/1.48  
% 3.13/1.48  %Foreground operators:
% 3.13/1.48  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.13/1.48  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.13/1.48  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.13/1.48  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.13/1.48  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.13/1.48  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.13/1.48  tff('#skF_5', type, '#skF_5': $i).
% 3.13/1.48  tff('#skF_6', type, '#skF_6': $i).
% 3.13/1.48  tff('#skF_2', type, '#skF_2': $i).
% 3.13/1.48  tff('#skF_3', type, '#skF_3': $i).
% 3.13/1.48  tff('#skF_1', type, '#skF_1': $i).
% 3.13/1.48  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.13/1.48  tff('#skF_4', type, '#skF_4': $i).
% 3.13/1.48  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.13/1.48  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.13/1.48  
% 3.13/1.50  tff(f_73, negated_conjecture, ~(![A, B, C]: (r1_tarski(k2_tarski(A, B), C) <=> (r2_hidden(A, C) & r2_hidden(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 3.13/1.50  tff(f_62, axiom, (![A, B, C]: (r1_tarski(A, k2_tarski(B, C)) <=> ~(((~(A = k1_xboole_0) & ~(A = k1_tarski(B))) & ~(A = k1_tarski(C))) & ~(A = k2_tarski(B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l45_zfmisc_1)).
% 3.13/1.50  tff(f_35, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 3.13/1.50  tff(f_66, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t37_zfmisc_1)).
% 3.13/1.50  tff(f_43, axiom, (![A, B]: (k2_tarski(A, B) = k2_xboole_0(k1_tarski(A), k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_enumset1)).
% 3.13/1.50  tff(f_41, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(C, B)) => r1_tarski(k2_xboole_0(A, C), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_xboole_1)).
% 3.13/1.50  tff(c_32, plain, (r2_hidden('#skF_1', '#skF_3') | ~r2_hidden('#skF_5', '#skF_6') | ~r2_hidden('#skF_4', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.13/1.50  tff(c_94, plain, (~r2_hidden('#skF_4', '#skF_6')), inference(splitLeft, [status(thm)], [c_32])).
% 3.13/1.50  tff(c_20, plain, (![B_15, C_16]: (r1_tarski(k1_tarski(B_15), k2_tarski(B_15, C_16)))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.13/1.50  tff(c_38, plain, (r2_hidden('#skF_1', '#skF_3') | r1_tarski(k2_tarski('#skF_4', '#skF_5'), '#skF_6')), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.13/1.50  tff(c_59, plain, (r1_tarski(k2_tarski('#skF_4', '#skF_5'), '#skF_6')), inference(splitLeft, [status(thm)], [c_38])).
% 3.13/1.50  tff(c_75, plain, (![A_40, C_41, B_42]: (r1_tarski(A_40, C_41) | ~r1_tarski(B_42, C_41) | ~r1_tarski(A_40, B_42))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.13/1.50  tff(c_109, plain, (![A_46]: (r1_tarski(A_46, '#skF_6') | ~r1_tarski(A_46, k2_tarski('#skF_4', '#skF_5')))), inference(resolution, [status(thm)], [c_59, c_75])).
% 3.13/1.50  tff(c_139, plain, (r1_tarski(k1_tarski('#skF_4'), '#skF_6')), inference(resolution, [status(thm)], [c_20, c_109])).
% 3.13/1.50  tff(c_24, plain, (![A_17, B_18]: (r2_hidden(A_17, B_18) | ~r1_tarski(k1_tarski(A_17), B_18))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.13/1.50  tff(c_155, plain, (r2_hidden('#skF_4', '#skF_6')), inference(resolution, [status(thm)], [c_139, c_24])).
% 3.13/1.50  tff(c_160, plain, $false, inference(negUnitSimplification, [status(thm)], [c_94, c_155])).
% 3.13/1.50  tff(c_162, plain, (r2_hidden('#skF_4', '#skF_6')), inference(splitRight, [status(thm)], [c_32])).
% 3.13/1.50  tff(c_161, plain, (~r2_hidden('#skF_5', '#skF_6') | r2_hidden('#skF_1', '#skF_3')), inference(splitRight, [status(thm)], [c_32])).
% 3.13/1.50  tff(c_163, plain, (~r2_hidden('#skF_5', '#skF_6')), inference(splitLeft, [status(thm)], [c_161])).
% 3.13/1.50  tff(c_18, plain, (![C_16, B_15]: (r1_tarski(k1_tarski(C_16), k2_tarski(B_15, C_16)))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.13/1.50  tff(c_178, plain, (![A_50]: (r1_tarski(A_50, '#skF_6') | ~r1_tarski(A_50, k2_tarski('#skF_4', '#skF_5')))), inference(resolution, [status(thm)], [c_59, c_75])).
% 3.13/1.50  tff(c_207, plain, (r1_tarski(k1_tarski('#skF_5'), '#skF_6')), inference(resolution, [status(thm)], [c_18, c_178])).
% 3.13/1.50  tff(c_219, plain, (r2_hidden('#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_207, c_24])).
% 3.13/1.50  tff(c_224, plain, $false, inference(negUnitSimplification, [status(thm)], [c_163, c_219])).
% 3.13/1.50  tff(c_226, plain, (r2_hidden('#skF_5', '#skF_6')), inference(splitRight, [status(thm)], [c_161])).
% 3.13/1.50  tff(c_30, plain, (r2_hidden('#skF_2', '#skF_3') | ~r2_hidden('#skF_5', '#skF_6') | ~r2_hidden('#skF_4', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.13/1.50  tff(c_242, plain, (r2_hidden('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_162, c_226, c_30])).
% 3.13/1.50  tff(c_26, plain, (![A_17, B_18]: (r1_tarski(k1_tarski(A_17), B_18) | ~r2_hidden(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.13/1.50  tff(c_225, plain, (r2_hidden('#skF_1', '#skF_3')), inference(splitRight, [status(thm)], [c_161])).
% 3.13/1.50  tff(c_8, plain, (![A_10, B_11]: (k2_xboole_0(k1_tarski(A_10), k1_tarski(B_11))=k2_tarski(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.13/1.50  tff(c_409, plain, (![A_75, C_76, B_77]: (r1_tarski(k2_xboole_0(A_75, C_76), B_77) | ~r1_tarski(C_76, B_77) | ~r1_tarski(A_75, B_77))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.13/1.50  tff(c_690, plain, (![A_129, B_130, B_131]: (r1_tarski(k2_tarski(A_129, B_130), B_131) | ~r1_tarski(k1_tarski(B_130), B_131) | ~r1_tarski(k1_tarski(A_129), B_131))), inference(superposition, [status(thm), theory('equality')], [c_8, c_409])).
% 3.13/1.50  tff(c_28, plain, (~r1_tarski(k2_tarski('#skF_1', '#skF_2'), '#skF_3') | ~r2_hidden('#skF_5', '#skF_6') | ~r2_hidden('#skF_4', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.13/1.50  tff(c_311, plain, (~r1_tarski(k2_tarski('#skF_1', '#skF_2'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_162, c_226, c_28])).
% 3.13/1.50  tff(c_735, plain, (~r1_tarski(k1_tarski('#skF_2'), '#skF_3') | ~r1_tarski(k1_tarski('#skF_1'), '#skF_3')), inference(resolution, [status(thm)], [c_690, c_311])).
% 3.13/1.50  tff(c_739, plain, (~r1_tarski(k1_tarski('#skF_1'), '#skF_3')), inference(splitLeft, [status(thm)], [c_735])).
% 3.13/1.50  tff(c_742, plain, (~r2_hidden('#skF_1', '#skF_3')), inference(resolution, [status(thm)], [c_26, c_739])).
% 3.13/1.50  tff(c_746, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_225, c_742])).
% 3.13/1.50  tff(c_747, plain, (~r1_tarski(k1_tarski('#skF_2'), '#skF_3')), inference(splitRight, [status(thm)], [c_735])).
% 3.13/1.50  tff(c_751, plain, (~r2_hidden('#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_26, c_747])).
% 3.13/1.50  tff(c_755, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_242, c_751])).
% 3.13/1.50  tff(c_757, plain, (~r1_tarski(k2_tarski('#skF_4', '#skF_5'), '#skF_6')), inference(splitRight, [status(thm)], [c_38])).
% 3.13/1.50  tff(c_36, plain, (r2_hidden('#skF_2', '#skF_3') | r1_tarski(k2_tarski('#skF_4', '#skF_5'), '#skF_6')), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.13/1.50  tff(c_758, plain, (r2_hidden('#skF_2', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_757, c_36])).
% 3.13/1.50  tff(c_756, plain, (r2_hidden('#skF_1', '#skF_3')), inference(splitRight, [status(thm)], [c_38])).
% 3.13/1.50  tff(c_868, plain, (![A_165, C_166, B_167]: (r1_tarski(k2_xboole_0(A_165, C_166), B_167) | ~r1_tarski(C_166, B_167) | ~r1_tarski(A_165, B_167))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.13/1.50  tff(c_1036, plain, (![A_211, B_212, B_213]: (r1_tarski(k2_tarski(A_211, B_212), B_213) | ~r1_tarski(k1_tarski(B_212), B_213) | ~r1_tarski(k1_tarski(A_211), B_213))), inference(superposition, [status(thm), theory('equality')], [c_8, c_868])).
% 3.13/1.50  tff(c_34, plain, (~r1_tarski(k2_tarski('#skF_1', '#skF_2'), '#skF_3') | r1_tarski(k2_tarski('#skF_4', '#skF_5'), '#skF_6')), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.13/1.50  tff(c_854, plain, (~r1_tarski(k2_tarski('#skF_1', '#skF_2'), '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_757, c_34])).
% 3.13/1.50  tff(c_1068, plain, (~r1_tarski(k1_tarski('#skF_2'), '#skF_3') | ~r1_tarski(k1_tarski('#skF_1'), '#skF_3')), inference(resolution, [status(thm)], [c_1036, c_854])).
% 3.13/1.50  tff(c_1072, plain, (~r1_tarski(k1_tarski('#skF_1'), '#skF_3')), inference(splitLeft, [status(thm)], [c_1068])).
% 3.13/1.50  tff(c_1075, plain, (~r2_hidden('#skF_1', '#skF_3')), inference(resolution, [status(thm)], [c_26, c_1072])).
% 3.13/1.50  tff(c_1079, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_756, c_1075])).
% 3.13/1.50  tff(c_1080, plain, (~r1_tarski(k1_tarski('#skF_2'), '#skF_3')), inference(splitRight, [status(thm)], [c_1068])).
% 3.13/1.50  tff(c_1084, plain, (~r2_hidden('#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_26, c_1080])).
% 3.13/1.50  tff(c_1088, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_758, c_1084])).
% 3.13/1.50  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.13/1.50  
% 3.13/1.50  Inference rules
% 3.13/1.50  ----------------------
% 3.13/1.50  #Ref     : 0
% 3.13/1.50  #Sup     : 235
% 3.13/1.50  #Fact    : 0
% 3.13/1.50  #Define  : 0
% 3.13/1.50  #Split   : 7
% 3.13/1.50  #Chain   : 0
% 3.13/1.50  #Close   : 0
% 3.13/1.50  
% 3.13/1.50  Ordering : KBO
% 3.13/1.50  
% 3.13/1.50  Simplification rules
% 3.13/1.50  ----------------------
% 3.13/1.50  #Subsume      : 36
% 3.13/1.50  #Demod        : 26
% 3.13/1.50  #Tautology    : 36
% 3.13/1.50  #SimpNegUnit  : 4
% 3.13/1.50  #BackRed      : 0
% 3.13/1.50  
% 3.13/1.50  #Partial instantiations: 0
% 3.13/1.50  #Strategies tried      : 1
% 3.13/1.50  
% 3.13/1.50  Timing (in seconds)
% 3.13/1.50  ----------------------
% 3.13/1.50  Preprocessing        : 0.28
% 3.13/1.50  Parsing              : 0.15
% 3.13/1.50  CNF conversion       : 0.02
% 3.13/1.50  Main loop            : 0.44
% 3.13/1.50  Inferencing          : 0.16
% 3.13/1.50  Reduction            : 0.12
% 3.13/1.50  Demodulation         : 0.08
% 3.13/1.50  BG Simplification    : 0.02
% 3.13/1.50  Subsumption          : 0.11
% 3.13/1.50  Abstraction          : 0.02
% 3.13/1.50  MUC search           : 0.00
% 3.13/1.50  Cooper               : 0.00
% 3.13/1.50  Total                : 0.75
% 3.13/1.50  Index Insertion      : 0.00
% 3.13/1.50  Index Deletion       : 0.00
% 3.13/1.50  Index Matching       : 0.00
% 3.13/1.50  BG Taut test         : 0.00
%------------------------------------------------------------------------------
