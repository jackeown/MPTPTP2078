%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:51:47 EST 2020

% Result     : Theorem 2.40s
% Output     : CNFRefutation 2.66s
% Verified   : 
% Statistics : Number of formulae       :   53 (  86 expanded)
%              Number of leaves         :   28 (  42 expanded)
%              Depth                    :   10
%              Number of atoms          :   49 ( 104 expanded)
%              Number of equality atoms :   25 (  56 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_4 > #skF_7 > #skF_6 > #skF_5 > #skF_2 > #skF_8 > #skF_3 > #skF_1

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

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_65,axiom,(
    ! [A,B] : k2_xboole_0(k1_tarski(A),B) != k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_zfmisc_1)).

tff(f_56,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_45,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_54,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).

tff(f_69,negated_conjecture,(
    ~ ! [A,B,C] : k2_xboole_0(k2_tarski(A,B),C) != k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_zfmisc_1)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( C = k2_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            | r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_xboole_0)).

tff(f_34,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(c_80,plain,(
    ! [B_40,A_41] : k2_xboole_0(B_40,A_41) = k2_xboole_0(A_41,B_40) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_56,plain,(
    ! [A_29,B_30] : k2_xboole_0(k1_tarski(A_29),B_30) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_96,plain,(
    ! [B_40,A_29] : k2_xboole_0(B_40,k1_tarski(A_29)) != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_80,c_56])).

tff(c_48,plain,(
    ! [A_21] : k2_tarski(A_21,A_21) = k1_tarski(A_21) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_28,plain,(
    ! [A_14] : r1_tarski(k1_xboole_0,A_14) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_34,plain,(
    ! [D_20,B_16] : r2_hidden(D_20,k2_tarski(D_20,B_16)) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_58,plain,(
    k2_xboole_0(k2_tarski('#skF_6','#skF_7'),'#skF_8') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_199,plain,(
    ! [D_52,A_53,B_54] :
      ( ~ r2_hidden(D_52,A_53)
      | r2_hidden(D_52,k2_xboole_0(A_53,B_54)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_290,plain,(
    ! [D_69] :
      ( ~ r2_hidden(D_69,k2_tarski('#skF_6','#skF_7'))
      | r2_hidden(D_69,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_58,c_199])).

tff(c_305,plain,(
    r2_hidden('#skF_6',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_34,c_290])).

tff(c_4,plain,(
    ! [C_7,B_4,A_3] :
      ( r2_hidden(C_7,B_4)
      | ~ r2_hidden(C_7,A_3)
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_312,plain,(
    ! [B_4] :
      ( r2_hidden('#skF_6',B_4)
      | ~ r1_tarski(k1_xboole_0,B_4) ) ),
    inference(resolution,[status(thm)],[c_305,c_4])).

tff(c_315,plain,(
    ! [B_4] : r2_hidden('#skF_6',B_4) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_312])).

tff(c_360,plain,(
    ! [D_75,B_76,A_77] :
      ( D_75 = B_76
      | D_75 = A_77
      | ~ r2_hidden(D_75,k2_tarski(A_77,B_76)) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_382,plain,(
    ! [B_76,A_77] :
      ( B_76 = '#skF_6'
      | A_77 = '#skF_6' ) ),
    inference(resolution,[status(thm)],[c_315,c_360])).

tff(c_390,plain,(
    ! [A_78] : A_78 = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_382])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_133,plain,(
    k2_xboole_0('#skF_8',k2_tarski('#skF_6','#skF_7')) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_58,c_2])).

tff(c_440,plain,(
    k2_xboole_0('#skF_8',k2_tarski('#skF_6','#skF_6')) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_390,c_133])).

tff(c_485,plain,(
    k2_xboole_0('#skF_8',k1_tarski('#skF_6')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_440])).

tff(c_487,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_96,c_485])).

tff(c_489,plain,(
    ! [B_902] : B_902 = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_382])).

tff(c_539,plain,(
    k2_xboole_0('#skF_8',k2_tarski('#skF_6','#skF_6')) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_489,c_133])).

tff(c_584,plain,(
    k2_xboole_0('#skF_8',k1_tarski('#skF_6')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_539])).

tff(c_586,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_96,c_584])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:22:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.40/1.37  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.66/1.37  
% 2.66/1.37  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.66/1.38  %$ r2_hidden > r1_tarski > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_4 > #skF_7 > #skF_6 > #skF_5 > #skF_2 > #skF_8 > #skF_3 > #skF_1
% 2.66/1.38  
% 2.66/1.38  %Foreground sorts:
% 2.66/1.38  
% 2.66/1.38  
% 2.66/1.38  %Background operators:
% 2.66/1.38  
% 2.66/1.38  
% 2.66/1.38  %Foreground operators:
% 2.66/1.38  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.66/1.38  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.66/1.38  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.66/1.38  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.66/1.38  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 2.66/1.38  tff('#skF_7', type, '#skF_7': $i).
% 2.66/1.38  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.66/1.38  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.66/1.38  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.66/1.38  tff('#skF_6', type, '#skF_6': $i).
% 2.66/1.38  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 2.66/1.38  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.66/1.38  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.66/1.38  tff('#skF_8', type, '#skF_8': $i).
% 2.66/1.38  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.66/1.38  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.66/1.38  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 2.66/1.38  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.66/1.38  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.66/1.38  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.66/1.38  
% 2.66/1.39  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 2.66/1.39  tff(f_65, axiom, (![A, B]: ~(k2_xboole_0(k1_tarski(A), B) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_zfmisc_1)).
% 2.66/1.39  tff(f_56, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 2.66/1.39  tff(f_45, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.66/1.39  tff(f_54, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_tarski)).
% 2.66/1.39  tff(f_69, negated_conjecture, ~(![A, B, C]: ~(k2_xboole_0(k2_tarski(A, B), C) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t50_zfmisc_1)).
% 2.66/1.39  tff(f_43, axiom, (![A, B, C]: ((C = k2_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) | r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_xboole_0)).
% 2.66/1.39  tff(f_34, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 2.66/1.39  tff(c_80, plain, (![B_40, A_41]: (k2_xboole_0(B_40, A_41)=k2_xboole_0(A_41, B_40))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.66/1.39  tff(c_56, plain, (![A_29, B_30]: (k2_xboole_0(k1_tarski(A_29), B_30)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.66/1.39  tff(c_96, plain, (![B_40, A_29]: (k2_xboole_0(B_40, k1_tarski(A_29))!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_80, c_56])).
% 2.66/1.39  tff(c_48, plain, (![A_21]: (k2_tarski(A_21, A_21)=k1_tarski(A_21))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.66/1.39  tff(c_28, plain, (![A_14]: (r1_tarski(k1_xboole_0, A_14))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.66/1.39  tff(c_34, plain, (![D_20, B_16]: (r2_hidden(D_20, k2_tarski(D_20, B_16)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.66/1.39  tff(c_58, plain, (k2_xboole_0(k2_tarski('#skF_6', '#skF_7'), '#skF_8')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.66/1.39  tff(c_199, plain, (![D_52, A_53, B_54]: (~r2_hidden(D_52, A_53) | r2_hidden(D_52, k2_xboole_0(A_53, B_54)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.66/1.39  tff(c_290, plain, (![D_69]: (~r2_hidden(D_69, k2_tarski('#skF_6', '#skF_7')) | r2_hidden(D_69, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_58, c_199])).
% 2.66/1.39  tff(c_305, plain, (r2_hidden('#skF_6', k1_xboole_0)), inference(resolution, [status(thm)], [c_34, c_290])).
% 2.66/1.39  tff(c_4, plain, (![C_7, B_4, A_3]: (r2_hidden(C_7, B_4) | ~r2_hidden(C_7, A_3) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.66/1.39  tff(c_312, plain, (![B_4]: (r2_hidden('#skF_6', B_4) | ~r1_tarski(k1_xboole_0, B_4))), inference(resolution, [status(thm)], [c_305, c_4])).
% 2.66/1.39  tff(c_315, plain, (![B_4]: (r2_hidden('#skF_6', B_4))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_312])).
% 2.66/1.39  tff(c_360, plain, (![D_75, B_76, A_77]: (D_75=B_76 | D_75=A_77 | ~r2_hidden(D_75, k2_tarski(A_77, B_76)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.66/1.39  tff(c_382, plain, (![B_76, A_77]: (B_76='#skF_6' | A_77='#skF_6')), inference(resolution, [status(thm)], [c_315, c_360])).
% 2.66/1.39  tff(c_390, plain, (![A_78]: (A_78='#skF_6')), inference(splitLeft, [status(thm)], [c_382])).
% 2.66/1.39  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.66/1.39  tff(c_133, plain, (k2_xboole_0('#skF_8', k2_tarski('#skF_6', '#skF_7'))=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_58, c_2])).
% 2.66/1.39  tff(c_440, plain, (k2_xboole_0('#skF_8', k2_tarski('#skF_6', '#skF_6'))=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_390, c_133])).
% 2.66/1.39  tff(c_485, plain, (k2_xboole_0('#skF_8', k1_tarski('#skF_6'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_48, c_440])).
% 2.66/1.39  tff(c_487, plain, $false, inference(negUnitSimplification, [status(thm)], [c_96, c_485])).
% 2.66/1.39  tff(c_489, plain, (![B_902]: (B_902='#skF_6')), inference(splitRight, [status(thm)], [c_382])).
% 2.66/1.39  tff(c_539, plain, (k2_xboole_0('#skF_8', k2_tarski('#skF_6', '#skF_6'))=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_489, c_133])).
% 2.66/1.39  tff(c_584, plain, (k2_xboole_0('#skF_8', k1_tarski('#skF_6'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_48, c_539])).
% 2.66/1.39  tff(c_586, plain, $false, inference(negUnitSimplification, [status(thm)], [c_96, c_584])).
% 2.66/1.39  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.66/1.39  
% 2.66/1.39  Inference rules
% 2.66/1.39  ----------------------
% 2.66/1.39  #Ref     : 0
% 2.66/1.39  #Sup     : 161
% 2.66/1.39  #Fact    : 0
% 2.66/1.39  #Define  : 0
% 2.66/1.39  #Split   : 1
% 2.66/1.39  #Chain   : 0
% 2.66/1.39  #Close   : 0
% 2.66/1.39  
% 2.66/1.39  Ordering : KBO
% 2.66/1.39  
% 2.66/1.39  Simplification rules
% 2.66/1.39  ----------------------
% 2.66/1.39  #Subsume      : 20
% 2.66/1.39  #Demod        : 29
% 2.66/1.39  #Tautology    : 40
% 2.66/1.39  #SimpNegUnit  : 2
% 2.66/1.39  #BackRed      : 0
% 2.66/1.39  
% 2.66/1.39  #Partial instantiations: 58
% 2.66/1.39  #Strategies tried      : 1
% 2.66/1.39  
% 2.66/1.39  Timing (in seconds)
% 2.66/1.39  ----------------------
% 2.66/1.39  Preprocessing        : 0.31
% 2.66/1.39  Parsing              : 0.16
% 2.66/1.39  CNF conversion       : 0.02
% 2.66/1.39  Main loop            : 0.27
% 2.66/1.39  Inferencing          : 0.11
% 2.66/1.39  Reduction            : 0.08
% 2.66/1.39  Demodulation         : 0.06
% 2.66/1.39  BG Simplification    : 0.02
% 2.66/1.39  Subsumption          : 0.04
% 2.66/1.39  Abstraction          : 0.01
% 2.66/1.39  MUC search           : 0.00
% 2.66/1.39  Cooper               : 0.00
% 2.66/1.39  Total                : 0.61
% 2.66/1.39  Index Insertion      : 0.00
% 2.66/1.39  Index Deletion       : 0.00
% 2.66/1.39  Index Matching       : 0.00
% 2.66/1.39  BG Taut test         : 0.00
%------------------------------------------------------------------------------
