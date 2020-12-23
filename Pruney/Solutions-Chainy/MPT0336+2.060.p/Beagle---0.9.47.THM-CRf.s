%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:55:08 EST 2020

% Result     : Theorem 3.11s
% Output     : CNFRefutation 3.11s
% Verified   : 
% Statistics : Number of formulae       :   58 (  72 expanded)
%              Number of leaves         :   27 (  37 expanded)
%              Depth                    :    9
%              Number of atoms          :   66 (  95 expanded)
%              Number of equality atoms :   21 (  30 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_2 > #skF_1

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

tff(f_97,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( r1_tarski(k3_xboole_0(A,B),k1_tarski(D))
          & r2_hidden(D,C)
          & r1_xboole_0(C,B) )
       => r1_xboole_0(k2_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t149_zfmisc_1)).

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

tff(f_88,axiom,(
    ! [A,B] :
      ( ~ r2_hidden(A,B)
     => r1_xboole_0(k1_tarski(A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l27_zfmisc_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_77,axiom,(
    ! [A,B,C] :
      ( r1_xboole_0(A,B)
     => k3_xboole_0(A,k2_xboole_0(B,C)) = k3_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t78_xboole_1)).

tff(f_73,axiom,(
    ! [A,B,C] :
      ~ ( ~ r1_xboole_0(A,k3_xboole_0(B,C))
        & r1_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_xboole_1)).

tff(f_67,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(c_36,plain,(
    r2_hidden('#skF_6','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_34,plain,(
    r1_xboole_0('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_443,plain,(
    ! [A_67,B_68,C_69] :
      ( ~ r1_xboole_0(A_67,B_68)
      | ~ r2_hidden(C_69,B_68)
      | ~ r2_hidden(C_69,A_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_465,plain,(
    ! [C_70] :
      ( ~ r2_hidden(C_70,'#skF_4')
      | ~ r2_hidden(C_70,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_34,c_443])).

tff(c_479,plain,(
    ~ r2_hidden('#skF_6','#skF_4') ),
    inference(resolution,[status(thm)],[c_36,c_465])).

tff(c_30,plain,(
    ! [A_29,B_30] :
      ( r1_xboole_0(k1_tarski(A_29),B_30)
      | r2_hidden(A_29,B_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_6,plain,(
    ! [A_3,B_4] :
      ( r1_xboole_0(A_3,B_4)
      | k3_xboole_0(A_3,B_4) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_119,plain,(
    ! [A_42,B_43] :
      ( k3_xboole_0(A_42,B_43) = k1_xboole_0
      | ~ r1_xboole_0(A_42,B_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_131,plain,(
    k3_xboole_0('#skF_5','#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_34,c_119])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_135,plain,(
    k3_xboole_0('#skF_4','#skF_5') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_131,c_2])).

tff(c_1019,plain,(
    ! [A_107,B_108,C_109] :
      ( k3_xboole_0(A_107,k2_xboole_0(B_108,C_109)) = k3_xboole_0(A_107,C_109)
      | ~ r1_xboole_0(A_107,B_108) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_113,plain,(
    ! [A_40,B_41] :
      ( r1_xboole_0(A_40,B_41)
      | k3_xboole_0(A_40,B_41) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_32,plain,(
    ~ r1_xboole_0(k2_xboole_0('#skF_3','#skF_5'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_116,plain,(
    k3_xboole_0(k2_xboole_0('#skF_3','#skF_5'),'#skF_4') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_113,c_32])).

tff(c_118,plain,(
    k3_xboole_0('#skF_4',k2_xboole_0('#skF_3','#skF_5')) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_116])).

tff(c_1068,plain,
    ( k3_xboole_0('#skF_4','#skF_5') != k1_xboole_0
    | ~ r1_xboole_0('#skF_4','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1019,c_118])).

tff(c_1098,plain,(
    ~ r1_xboole_0('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_135,c_1068])).

tff(c_1110,plain,(
    k3_xboole_0('#skF_4','#skF_3') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_6,c_1098])).

tff(c_279,plain,(
    ! [A_56,B_57,C_58] :
      ( ~ r1_xboole_0(A_56,B_57)
      | r1_xboole_0(A_56,k3_xboole_0(B_57,C_58)) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_4,plain,(
    ! [A_3,B_4] :
      ( k3_xboole_0(A_3,B_4) = k1_xboole_0
      | ~ r1_xboole_0(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_1112,plain,(
    ! [A_110,B_111,C_112] :
      ( k3_xboole_0(A_110,k3_xboole_0(B_111,C_112)) = k1_xboole_0
      | ~ r1_xboole_0(A_110,B_111) ) ),
    inference(resolution,[status(thm)],[c_279,c_4])).

tff(c_38,plain,(
    r1_tarski(k3_xboole_0('#skF_3','#skF_4'),k1_tarski('#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_39,plain,(
    r1_tarski(k3_xboole_0('#skF_4','#skF_3'),k1_tarski('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_38])).

tff(c_91,plain,(
    ! [A_36,B_37] :
      ( k3_xboole_0(A_36,B_37) = A_36
      | ~ r1_tarski(A_36,B_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_95,plain,(
    k3_xboole_0(k3_xboole_0('#skF_4','#skF_3'),k1_tarski('#skF_6')) = k3_xboole_0('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_39,c_91])).

tff(c_100,plain,(
    k3_xboole_0(k1_tarski('#skF_6'),k3_xboole_0('#skF_4','#skF_3')) = k3_xboole_0('#skF_4','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_95,c_2])).

tff(c_1157,plain,
    ( k3_xboole_0('#skF_4','#skF_3') = k1_xboole_0
    | ~ r1_xboole_0(k1_tarski('#skF_6'),'#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1112,c_100])).

tff(c_1242,plain,(
    ~ r1_xboole_0(k1_tarski('#skF_6'),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_1110,c_1157])).

tff(c_1268,plain,(
    r2_hidden('#skF_6','#skF_4') ),
    inference(resolution,[status(thm)],[c_30,c_1242])).

tff(c_1275,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_479,c_1268])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:48:44 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.11/1.44  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.11/1.44  
% 3.11/1.44  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.11/1.45  %$ r2_hidden > r1_xboole_0 > r1_tarski > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 3.11/1.45  
% 3.11/1.45  %Foreground sorts:
% 3.11/1.45  
% 3.11/1.45  
% 3.11/1.45  %Background operators:
% 3.11/1.45  
% 3.11/1.45  
% 3.11/1.45  %Foreground operators:
% 3.11/1.45  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.11/1.45  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.11/1.45  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.11/1.45  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.11/1.45  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.11/1.45  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.11/1.45  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.11/1.45  tff('#skF_5', type, '#skF_5': $i).
% 3.11/1.45  tff('#skF_6', type, '#skF_6': $i).
% 3.11/1.45  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.11/1.45  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.11/1.45  tff('#skF_3', type, '#skF_3': $i).
% 3.11/1.45  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.11/1.45  tff('#skF_4', type, '#skF_4': $i).
% 3.11/1.45  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.11/1.45  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.11/1.45  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.11/1.45  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.11/1.45  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.11/1.45  
% 3.11/1.46  tff(f_97, negated_conjecture, ~(![A, B, C, D]: (((r1_tarski(k3_xboole_0(A, B), k1_tarski(D)) & r2_hidden(D, C)) & r1_xboole_0(C, B)) => r1_xboole_0(k2_xboole_0(A, C), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t149_zfmisc_1)).
% 3.11/1.46  tff(f_49, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 3.11/1.46  tff(f_88, axiom, (![A, B]: (~r2_hidden(A, B) => r1_xboole_0(k1_tarski(A), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 3.11/1.46  tff(f_31, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 3.11/1.46  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 3.11/1.46  tff(f_77, axiom, (![A, B, C]: (r1_xboole_0(A, B) => (k3_xboole_0(A, k2_xboole_0(B, C)) = k3_xboole_0(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t78_xboole_1)).
% 3.11/1.46  tff(f_73, axiom, (![A, B, C]: ~(~r1_xboole_0(A, k3_xboole_0(B, C)) & r1_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t74_xboole_1)).
% 3.11/1.46  tff(f_67, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 3.11/1.46  tff(c_36, plain, (r2_hidden('#skF_6', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_97])).
% 3.11/1.46  tff(c_34, plain, (r1_xboole_0('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_97])).
% 3.11/1.46  tff(c_443, plain, (![A_67, B_68, C_69]: (~r1_xboole_0(A_67, B_68) | ~r2_hidden(C_69, B_68) | ~r2_hidden(C_69, A_67))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.11/1.46  tff(c_465, plain, (![C_70]: (~r2_hidden(C_70, '#skF_4') | ~r2_hidden(C_70, '#skF_5'))), inference(resolution, [status(thm)], [c_34, c_443])).
% 3.11/1.46  tff(c_479, plain, (~r2_hidden('#skF_6', '#skF_4')), inference(resolution, [status(thm)], [c_36, c_465])).
% 3.11/1.46  tff(c_30, plain, (![A_29, B_30]: (r1_xboole_0(k1_tarski(A_29), B_30) | r2_hidden(A_29, B_30))), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.11/1.46  tff(c_6, plain, (![A_3, B_4]: (r1_xboole_0(A_3, B_4) | k3_xboole_0(A_3, B_4)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.11/1.46  tff(c_119, plain, (![A_42, B_43]: (k3_xboole_0(A_42, B_43)=k1_xboole_0 | ~r1_xboole_0(A_42, B_43))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.11/1.46  tff(c_131, plain, (k3_xboole_0('#skF_5', '#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_34, c_119])).
% 3.11/1.46  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.11/1.46  tff(c_135, plain, (k3_xboole_0('#skF_4', '#skF_5')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_131, c_2])).
% 3.11/1.46  tff(c_1019, plain, (![A_107, B_108, C_109]: (k3_xboole_0(A_107, k2_xboole_0(B_108, C_109))=k3_xboole_0(A_107, C_109) | ~r1_xboole_0(A_107, B_108))), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.11/1.46  tff(c_113, plain, (![A_40, B_41]: (r1_xboole_0(A_40, B_41) | k3_xboole_0(A_40, B_41)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.11/1.46  tff(c_32, plain, (~r1_xboole_0(k2_xboole_0('#skF_3', '#skF_5'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_97])).
% 3.11/1.46  tff(c_116, plain, (k3_xboole_0(k2_xboole_0('#skF_3', '#skF_5'), '#skF_4')!=k1_xboole_0), inference(resolution, [status(thm)], [c_113, c_32])).
% 3.11/1.46  tff(c_118, plain, (k3_xboole_0('#skF_4', k2_xboole_0('#skF_3', '#skF_5'))!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_2, c_116])).
% 3.11/1.46  tff(c_1068, plain, (k3_xboole_0('#skF_4', '#skF_5')!=k1_xboole_0 | ~r1_xboole_0('#skF_4', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1019, c_118])).
% 3.11/1.46  tff(c_1098, plain, (~r1_xboole_0('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_135, c_1068])).
% 3.11/1.46  tff(c_1110, plain, (k3_xboole_0('#skF_4', '#skF_3')!=k1_xboole_0), inference(resolution, [status(thm)], [c_6, c_1098])).
% 3.11/1.46  tff(c_279, plain, (![A_56, B_57, C_58]: (~r1_xboole_0(A_56, B_57) | r1_xboole_0(A_56, k3_xboole_0(B_57, C_58)))), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.11/1.46  tff(c_4, plain, (![A_3, B_4]: (k3_xboole_0(A_3, B_4)=k1_xboole_0 | ~r1_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.11/1.46  tff(c_1112, plain, (![A_110, B_111, C_112]: (k3_xboole_0(A_110, k3_xboole_0(B_111, C_112))=k1_xboole_0 | ~r1_xboole_0(A_110, B_111))), inference(resolution, [status(thm)], [c_279, c_4])).
% 3.11/1.46  tff(c_38, plain, (r1_tarski(k3_xboole_0('#skF_3', '#skF_4'), k1_tarski('#skF_6'))), inference(cnfTransformation, [status(thm)], [f_97])).
% 3.11/1.46  tff(c_39, plain, (r1_tarski(k3_xboole_0('#skF_4', '#skF_3'), k1_tarski('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_38])).
% 3.11/1.46  tff(c_91, plain, (![A_36, B_37]: (k3_xboole_0(A_36, B_37)=A_36 | ~r1_tarski(A_36, B_37))), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.11/1.46  tff(c_95, plain, (k3_xboole_0(k3_xboole_0('#skF_4', '#skF_3'), k1_tarski('#skF_6'))=k3_xboole_0('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_39, c_91])).
% 3.11/1.46  tff(c_100, plain, (k3_xboole_0(k1_tarski('#skF_6'), k3_xboole_0('#skF_4', '#skF_3'))=k3_xboole_0('#skF_4', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_95, c_2])).
% 3.11/1.46  tff(c_1157, plain, (k3_xboole_0('#skF_4', '#skF_3')=k1_xboole_0 | ~r1_xboole_0(k1_tarski('#skF_6'), '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1112, c_100])).
% 3.11/1.46  tff(c_1242, plain, (~r1_xboole_0(k1_tarski('#skF_6'), '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_1110, c_1157])).
% 3.11/1.46  tff(c_1268, plain, (r2_hidden('#skF_6', '#skF_4')), inference(resolution, [status(thm)], [c_30, c_1242])).
% 3.11/1.46  tff(c_1275, plain, $false, inference(negUnitSimplification, [status(thm)], [c_479, c_1268])).
% 3.11/1.46  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.11/1.46  
% 3.11/1.46  Inference rules
% 3.11/1.46  ----------------------
% 3.11/1.46  #Ref     : 0
% 3.11/1.46  #Sup     : 318
% 3.11/1.46  #Fact    : 0
% 3.11/1.46  #Define  : 0
% 3.11/1.46  #Split   : 0
% 3.11/1.46  #Chain   : 0
% 3.11/1.46  #Close   : 0
% 3.11/1.46  
% 3.11/1.46  Ordering : KBO
% 3.11/1.46  
% 3.11/1.46  Simplification rules
% 3.11/1.46  ----------------------
% 3.11/1.46  #Subsume      : 67
% 3.11/1.46  #Demod        : 126
% 3.11/1.46  #Tautology    : 146
% 3.11/1.46  #SimpNegUnit  : 14
% 3.11/1.46  #BackRed      : 0
% 3.11/1.46  
% 3.11/1.46  #Partial instantiations: 0
% 3.11/1.46  #Strategies tried      : 1
% 3.11/1.46  
% 3.11/1.46  Timing (in seconds)
% 3.11/1.46  ----------------------
% 3.11/1.46  Preprocessing        : 0.30
% 3.11/1.46  Parsing              : 0.16
% 3.11/1.46  CNF conversion       : 0.02
% 3.11/1.46  Main loop            : 0.39
% 3.11/1.46  Inferencing          : 0.13
% 3.11/1.46  Reduction            : 0.14
% 3.11/1.46  Demodulation         : 0.11
% 3.11/1.46  BG Simplification    : 0.02
% 3.11/1.46  Subsumption          : 0.07
% 3.11/1.46  Abstraction          : 0.02
% 3.11/1.46  MUC search           : 0.00
% 3.11/1.46  Cooper               : 0.00
% 3.11/1.46  Total                : 0.72
% 3.11/1.46  Index Insertion      : 0.00
% 3.11/1.46  Index Deletion       : 0.00
% 3.11/1.46  Index Matching       : 0.00
% 3.11/1.46  BG Taut test         : 0.00
%------------------------------------------------------------------------------
