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
% DateTime   : Thu Dec  3 09:55:08 EST 2020

% Result     : Theorem 2.17s
% Output     : CNFRefutation 2.46s
% Verified   : 
% Statistics : Number of formulae       :   60 (  79 expanded)
%              Number of leaves         :   29 (  40 expanded)
%              Depth                    :    8
%              Number of atoms          :   67 ( 108 expanded)
%              Number of equality atoms :   23 (  37 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1

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

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

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
    '#skF_1': ( $i * $i ) > $i )).

tff(f_86,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( r1_tarski(k3_xboole_0(A,B),k1_tarski(D))
          & r2_hidden(D,C)
          & r1_xboole_0(C,B) )
       => r1_xboole_0(k2_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t149_zfmisc_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_69,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k1_tarski(B))
    <=> ( A = k1_xboole_0
        | A = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_zfmisc_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_55,axiom,(
    ! [A,B,C] :
      ( r1_xboole_0(A,B)
     => k3_xboole_0(A,k2_xboole_0(B,C)) = k3_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t78_xboole_1)).

tff(f_51,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_57,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_77,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_tarski(A,B),C)
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).

tff(f_49,axiom,(
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

tff(c_44,plain,(
    r2_hidden('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_46,plain,(
    r1_tarski(k3_xboole_0('#skF_2','#skF_3'),k1_tarski('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_47,plain,(
    r1_tarski(k3_xboole_0('#skF_3','#skF_2'),k1_tarski('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_46])).

tff(c_263,plain,(
    ! [B_72,A_73] :
      ( k1_tarski(B_72) = A_73
      | k1_xboole_0 = A_73
      | ~ r1_tarski(A_73,k1_tarski(B_72)) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_282,plain,
    ( k3_xboole_0('#skF_3','#skF_2') = k1_tarski('#skF_5')
    | k3_xboole_0('#skF_3','#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_47,c_263])).

tff(c_288,plain,(
    k3_xboole_0('#skF_3','#skF_2') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_282])).

tff(c_6,plain,(
    ! [A_3,B_4] :
      ( r1_xboole_0(A_3,B_4)
      | k3_xboole_0(A_3,B_4) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_42,plain,(
    r1_xboole_0('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_99,plain,(
    ! [A_39,B_40] :
      ( k3_xboole_0(A_39,B_40) = k1_xboole_0
      | ~ r1_xboole_0(A_39,B_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_103,plain,(
    k3_xboole_0('#skF_4','#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_42,c_99])).

tff(c_329,plain,(
    ! [A_79,B_80,C_81] :
      ( k3_xboole_0(A_79,k2_xboole_0(B_80,C_81)) = k3_xboole_0(A_79,C_81)
      | ~ r1_xboole_0(A_79,B_80) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_133,plain,(
    ! [A_45,B_46] :
      ( r1_xboole_0(A_45,B_46)
      | k3_xboole_0(A_45,B_46) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_40,plain,(
    ~ r1_xboole_0(k2_xboole_0('#skF_2','#skF_4'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_139,plain,(
    k3_xboole_0(k2_xboole_0('#skF_2','#skF_4'),'#skF_3') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_133,c_40])).

tff(c_142,plain,(
    k3_xboole_0('#skF_3',k2_xboole_0('#skF_2','#skF_4')) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_139])).

tff(c_335,plain,
    ( k3_xboole_0('#skF_3','#skF_4') != k1_xboole_0
    | ~ r1_xboole_0('#skF_3','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_329,c_142])).

tff(c_364,plain,(
    ~ r1_xboole_0('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_103,c_2,c_335])).

tff(c_369,plain,(
    k3_xboole_0('#skF_3','#skF_2') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_6,c_364])).

tff(c_373,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_288,c_369])).

tff(c_374,plain,(
    k3_xboole_0('#skF_3','#skF_2') = k1_tarski('#skF_5') ),
    inference(splitRight,[status(thm)],[c_282])).

tff(c_14,plain,(
    ! [A_10,B_11] : r1_tarski(k3_xboole_0(A_10,B_11),A_10) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_385,plain,(
    r1_tarski(k1_tarski('#skF_5'),'#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_374,c_14])).

tff(c_18,plain,(
    ! [A_15] : k2_tarski(A_15,A_15) = k1_tarski(A_15) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_155,plain,(
    ! [A_49,C_50,B_51] :
      ( r2_hidden(A_49,C_50)
      | ~ r1_tarski(k2_tarski(A_49,B_51),C_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_158,plain,(
    ! [A_15,C_50] :
      ( r2_hidden(A_15,C_50)
      | ~ r1_tarski(k1_tarski(A_15),C_50) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_155])).

tff(c_405,plain,(
    r2_hidden('#skF_5','#skF_3') ),
    inference(resolution,[status(thm)],[c_385,c_158])).

tff(c_197,plain,(
    ! [A_66,B_67,C_68] :
      ( ~ r1_xboole_0(A_66,B_67)
      | ~ r2_hidden(C_68,B_67)
      | ~ r2_hidden(C_68,A_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_203,plain,(
    ! [C_68] :
      ( ~ r2_hidden(C_68,'#skF_3')
      | ~ r2_hidden(C_68,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_42,c_197])).

tff(c_408,plain,(
    ~ r2_hidden('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_405,c_203])).

tff(c_412,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_408])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n006.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 19:31:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.17/1.32  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.17/1.33  
% 2.17/1.33  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.17/1.33  %$ r2_hidden > r1_xboole_0 > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 2.17/1.33  
% 2.17/1.33  %Foreground sorts:
% 2.17/1.33  
% 2.17/1.33  
% 2.17/1.33  %Background operators:
% 2.17/1.33  
% 2.17/1.33  
% 2.17/1.33  %Foreground operators:
% 2.17/1.33  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.17/1.33  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.17/1.33  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.17/1.33  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.17/1.33  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.17/1.33  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.17/1.33  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.17/1.33  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.17/1.33  tff('#skF_5', type, '#skF_5': $i).
% 2.17/1.33  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.17/1.33  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.17/1.33  tff('#skF_2', type, '#skF_2': $i).
% 2.17/1.33  tff('#skF_3', type, '#skF_3': $i).
% 2.17/1.33  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.17/1.33  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.17/1.33  tff('#skF_4', type, '#skF_4': $i).
% 2.17/1.33  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.17/1.33  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.17/1.33  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.17/1.33  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.17/1.33  
% 2.46/1.34  tff(f_86, negated_conjecture, ~(![A, B, C, D]: (((r1_tarski(k3_xboole_0(A, B), k1_tarski(D)) & r2_hidden(D, C)) & r1_xboole_0(C, B)) => r1_xboole_0(k2_xboole_0(A, C), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t149_zfmisc_1)).
% 2.46/1.34  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 2.46/1.34  tff(f_69, axiom, (![A, B]: (r1_tarski(A, k1_tarski(B)) <=> ((A = k1_xboole_0) | (A = k1_tarski(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_zfmisc_1)).
% 2.46/1.34  tff(f_31, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 2.46/1.34  tff(f_55, axiom, (![A, B, C]: (r1_xboole_0(A, B) => (k3_xboole_0(A, k2_xboole_0(B, C)) = k3_xboole_0(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t78_xboole_1)).
% 2.46/1.34  tff(f_51, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 2.46/1.34  tff(f_57, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 2.46/1.34  tff(f_77, axiom, (![A, B, C]: (r1_tarski(k2_tarski(A, B), C) <=> (r2_hidden(A, C) & r2_hidden(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 2.46/1.34  tff(f_49, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 2.46/1.34  tff(c_44, plain, (r2_hidden('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.46/1.34  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.46/1.34  tff(c_46, plain, (r1_tarski(k3_xboole_0('#skF_2', '#skF_3'), k1_tarski('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.46/1.34  tff(c_47, plain, (r1_tarski(k3_xboole_0('#skF_3', '#skF_2'), k1_tarski('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_46])).
% 2.46/1.34  tff(c_263, plain, (![B_72, A_73]: (k1_tarski(B_72)=A_73 | k1_xboole_0=A_73 | ~r1_tarski(A_73, k1_tarski(B_72)))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.46/1.34  tff(c_282, plain, (k3_xboole_0('#skF_3', '#skF_2')=k1_tarski('#skF_5') | k3_xboole_0('#skF_3', '#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_47, c_263])).
% 2.46/1.34  tff(c_288, plain, (k3_xboole_0('#skF_3', '#skF_2')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_282])).
% 2.46/1.34  tff(c_6, plain, (![A_3, B_4]: (r1_xboole_0(A_3, B_4) | k3_xboole_0(A_3, B_4)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.46/1.34  tff(c_42, plain, (r1_xboole_0('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.46/1.34  tff(c_99, plain, (![A_39, B_40]: (k3_xboole_0(A_39, B_40)=k1_xboole_0 | ~r1_xboole_0(A_39, B_40))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.46/1.34  tff(c_103, plain, (k3_xboole_0('#skF_4', '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_42, c_99])).
% 2.46/1.34  tff(c_329, plain, (![A_79, B_80, C_81]: (k3_xboole_0(A_79, k2_xboole_0(B_80, C_81))=k3_xboole_0(A_79, C_81) | ~r1_xboole_0(A_79, B_80))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.46/1.34  tff(c_133, plain, (![A_45, B_46]: (r1_xboole_0(A_45, B_46) | k3_xboole_0(A_45, B_46)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.46/1.34  tff(c_40, plain, (~r1_xboole_0(k2_xboole_0('#skF_2', '#skF_4'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.46/1.34  tff(c_139, plain, (k3_xboole_0(k2_xboole_0('#skF_2', '#skF_4'), '#skF_3')!=k1_xboole_0), inference(resolution, [status(thm)], [c_133, c_40])).
% 2.46/1.34  tff(c_142, plain, (k3_xboole_0('#skF_3', k2_xboole_0('#skF_2', '#skF_4'))!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_2, c_139])).
% 2.46/1.34  tff(c_335, plain, (k3_xboole_0('#skF_3', '#skF_4')!=k1_xboole_0 | ~r1_xboole_0('#skF_3', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_329, c_142])).
% 2.46/1.34  tff(c_364, plain, (~r1_xboole_0('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_103, c_2, c_335])).
% 2.46/1.34  tff(c_369, plain, (k3_xboole_0('#skF_3', '#skF_2')!=k1_xboole_0), inference(resolution, [status(thm)], [c_6, c_364])).
% 2.46/1.34  tff(c_373, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_288, c_369])).
% 2.46/1.34  tff(c_374, plain, (k3_xboole_0('#skF_3', '#skF_2')=k1_tarski('#skF_5')), inference(splitRight, [status(thm)], [c_282])).
% 2.46/1.34  tff(c_14, plain, (![A_10, B_11]: (r1_tarski(k3_xboole_0(A_10, B_11), A_10))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.46/1.34  tff(c_385, plain, (r1_tarski(k1_tarski('#skF_5'), '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_374, c_14])).
% 2.46/1.34  tff(c_18, plain, (![A_15]: (k2_tarski(A_15, A_15)=k1_tarski(A_15))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.46/1.34  tff(c_155, plain, (![A_49, C_50, B_51]: (r2_hidden(A_49, C_50) | ~r1_tarski(k2_tarski(A_49, B_51), C_50))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.46/1.34  tff(c_158, plain, (![A_15, C_50]: (r2_hidden(A_15, C_50) | ~r1_tarski(k1_tarski(A_15), C_50))), inference(superposition, [status(thm), theory('equality')], [c_18, c_155])).
% 2.46/1.34  tff(c_405, plain, (r2_hidden('#skF_5', '#skF_3')), inference(resolution, [status(thm)], [c_385, c_158])).
% 2.46/1.34  tff(c_197, plain, (![A_66, B_67, C_68]: (~r1_xboole_0(A_66, B_67) | ~r2_hidden(C_68, B_67) | ~r2_hidden(C_68, A_66))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.46/1.34  tff(c_203, plain, (![C_68]: (~r2_hidden(C_68, '#skF_3') | ~r2_hidden(C_68, '#skF_4'))), inference(resolution, [status(thm)], [c_42, c_197])).
% 2.46/1.34  tff(c_408, plain, (~r2_hidden('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_405, c_203])).
% 2.46/1.34  tff(c_412, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_44, c_408])).
% 2.46/1.34  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.46/1.34  
% 2.46/1.34  Inference rules
% 2.46/1.34  ----------------------
% 2.46/1.34  #Ref     : 0
% 2.46/1.34  #Sup     : 86
% 2.46/1.34  #Fact    : 0
% 2.46/1.34  #Define  : 0
% 2.46/1.34  #Split   : 1
% 2.46/1.34  #Chain   : 0
% 2.46/1.34  #Close   : 0
% 2.46/1.34  
% 2.46/1.34  Ordering : KBO
% 2.46/1.34  
% 2.46/1.34  Simplification rules
% 2.46/1.34  ----------------------
% 2.46/1.34  #Subsume      : 2
% 2.46/1.34  #Demod        : 23
% 2.46/1.34  #Tautology    : 52
% 2.46/1.34  #SimpNegUnit  : 0
% 2.46/1.34  #BackRed      : 3
% 2.46/1.34  
% 2.46/1.34  #Partial instantiations: 0
% 2.46/1.34  #Strategies tried      : 1
% 2.46/1.34  
% 2.46/1.34  Timing (in seconds)
% 2.46/1.34  ----------------------
% 2.46/1.34  Preprocessing        : 0.31
% 2.46/1.34  Parsing              : 0.16
% 2.46/1.34  CNF conversion       : 0.02
% 2.46/1.34  Main loop            : 0.26
% 2.46/1.34  Inferencing          : 0.09
% 2.46/1.34  Reduction            : 0.08
% 2.46/1.34  Demodulation         : 0.06
% 2.46/1.34  BG Simplification    : 0.01
% 2.46/1.35  Subsumption          : 0.05
% 2.46/1.35  Abstraction          : 0.02
% 2.46/1.35  MUC search           : 0.00
% 2.46/1.35  Cooper               : 0.00
% 2.46/1.35  Total                : 0.60
% 2.46/1.35  Index Insertion      : 0.00
% 2.46/1.35  Index Deletion       : 0.00
% 2.46/1.35  Index Matching       : 0.00
% 2.46/1.35  BG Taut test         : 0.00
%------------------------------------------------------------------------------
