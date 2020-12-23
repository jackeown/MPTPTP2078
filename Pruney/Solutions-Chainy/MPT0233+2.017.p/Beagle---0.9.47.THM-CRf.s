%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:49:26 EST 2020

% Result     : Theorem 3.91s
% Output     : CNFRefutation 3.91s
% Verified   : 
% Statistics : Number of formulae       :   53 (  56 expanded)
%              Number of leaves         :   33 (  36 expanded)
%              Depth                    :    9
%              Number of atoms          :   48 (  58 expanded)
%              Number of equality atoms :   26 (  33 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_xboole_0 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_11 > #skF_6 > #skF_1 > #skF_10 > #skF_2 > #skF_9 > #skF_7 > #skF_8 > #skF_3 > #skF_5 > #skF_4

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

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_94,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ~ ( r1_tarski(k2_tarski(A,B),k2_tarski(C,D))
          & A != C
          & A != D ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_zfmisc_1)).

tff(f_76,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).

tff(f_54,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_56,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_60,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_46,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_58,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_42,axiom,(
    ! [A,B,C] :
      ( C = k3_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

tff(c_80,plain,(
    '#skF_10' != '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_78,plain,(
    '#skF_11' != '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_56,plain,(
    ! [D_35,B_31] : r2_hidden(D_35,k2_tarski(D_35,B_31)) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_82,plain,(
    r1_tarski(k2_tarski('#skF_8','#skF_9'),k2_tarski('#skF_10','#skF_11')) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_211,plain,(
    ! [A_66,B_67] :
      ( k2_xboole_0(A_66,B_67) = B_67
      | ~ r1_tarski(A_66,B_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_222,plain,(
    k2_xboole_0(k2_tarski('#skF_8','#skF_9'),k2_tarski('#skF_10','#skF_11')) = k2_tarski('#skF_10','#skF_11') ),
    inference(resolution,[status(thm)],[c_82,c_211])).

tff(c_34,plain,(
    ! [A_20] : k4_xboole_0(A_20,k1_xboole_0) = A_20 ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_38,plain,(
    ! [A_23,B_24] : r1_tarski(A_23,k2_xboole_0(A_23,B_24)) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_249,plain,(
    ! [A_72,B_73] :
      ( k4_xboole_0(A_72,B_73) = k1_xboole_0
      | ~ r1_tarski(A_72,B_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_265,plain,(
    ! [A_23,B_24] : k4_xboole_0(A_23,k2_xboole_0(A_23,B_24)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_38,c_249])).

tff(c_400,plain,(
    ! [A_88,B_89] : k4_xboole_0(A_88,k4_xboole_0(A_88,B_89)) = k3_xboole_0(A_88,B_89) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_427,plain,(
    ! [A_23,B_24] : k3_xboole_0(A_23,k2_xboole_0(A_23,B_24)) = k4_xboole_0(A_23,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_265,c_400])).

tff(c_437,plain,(
    ! [A_23,B_24] : k3_xboole_0(A_23,k2_xboole_0(A_23,B_24)) = A_23 ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_427])).

tff(c_540,plain,(
    ! [D_96,B_97,A_98] :
      ( r2_hidden(D_96,B_97)
      | ~ r2_hidden(D_96,k3_xboole_0(A_98,B_97)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_2613,plain,(
    ! [D_177,A_178,B_179] :
      ( r2_hidden(D_177,k2_xboole_0(A_178,B_179))
      | ~ r2_hidden(D_177,A_178) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_437,c_540])).

tff(c_2793,plain,(
    ! [D_191] :
      ( r2_hidden(D_191,k2_tarski('#skF_10','#skF_11'))
      | ~ r2_hidden(D_191,k2_tarski('#skF_8','#skF_9')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_222,c_2613])).

tff(c_52,plain,(
    ! [D_35,B_31,A_30] :
      ( D_35 = B_31
      | D_35 = A_30
      | ~ r2_hidden(D_35,k2_tarski(A_30,B_31)) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_2907,plain,(
    ! [D_203] :
      ( D_203 = '#skF_11'
      | D_203 = '#skF_10'
      | ~ r2_hidden(D_203,k2_tarski('#skF_8','#skF_9')) ) ),
    inference(resolution,[status(thm)],[c_2793,c_52])).

tff(c_2923,plain,
    ( '#skF_11' = '#skF_8'
    | '#skF_10' = '#skF_8' ),
    inference(resolution,[status(thm)],[c_56,c_2907])).

tff(c_2936,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_78,c_2923])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:50:52 EST 2020
% 0.19/0.34  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.91/1.90  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.91/1.90  
% 3.91/1.90  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.91/1.91  %$ r2_hidden > r1_tarski > v1_xboole_0 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_11 > #skF_6 > #skF_1 > #skF_10 > #skF_2 > #skF_9 > #skF_7 > #skF_8 > #skF_3 > #skF_5 > #skF_4
% 3.91/1.91  
% 3.91/1.91  %Foreground sorts:
% 3.91/1.91  
% 3.91/1.91  
% 3.91/1.91  %Background operators:
% 3.91/1.91  
% 3.91/1.91  
% 3.91/1.91  %Foreground operators:
% 3.91/1.91  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.91/1.91  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.91/1.91  tff('#skF_11', type, '#skF_11': $i).
% 3.91/1.91  tff('#skF_6', type, '#skF_6': ($i * $i * $i) > $i).
% 3.91/1.91  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.91/1.91  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.91/1.91  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.91/1.91  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.91/1.91  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.91/1.91  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.91/1.91  tff('#skF_10', type, '#skF_10': $i).
% 3.91/1.91  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.91/1.91  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.91/1.91  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 3.91/1.91  tff('#skF_9', type, '#skF_9': $i).
% 3.91/1.91  tff('#skF_7', type, '#skF_7': ($i * $i * $i) > $i).
% 3.91/1.91  tff('#skF_8', type, '#skF_8': $i).
% 3.91/1.91  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.91/1.91  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 3.91/1.91  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.91/1.91  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.91/1.91  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.91/1.91  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.91/1.91  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 3.91/1.91  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 3.91/1.91  
% 3.91/1.92  tff(f_94, negated_conjecture, ~(![A, B, C, D]: ~((r1_tarski(k2_tarski(A, B), k2_tarski(C, D)) & ~(A = C)) & ~(A = D))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_zfmisc_1)).
% 3.91/1.92  tff(f_76, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_tarski)).
% 3.91/1.92  tff(f_54, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 3.91/1.92  tff(f_56, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 3.91/1.92  tff(f_60, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 3.91/1.92  tff(f_46, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 3.91/1.92  tff(f_58, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 3.91/1.92  tff(f_42, axiom, (![A, B, C]: ((C = k3_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_xboole_0)).
% 3.91/1.92  tff(c_80, plain, ('#skF_10'!='#skF_8'), inference(cnfTransformation, [status(thm)], [f_94])).
% 3.91/1.92  tff(c_78, plain, ('#skF_11'!='#skF_8'), inference(cnfTransformation, [status(thm)], [f_94])).
% 3.91/1.92  tff(c_56, plain, (![D_35, B_31]: (r2_hidden(D_35, k2_tarski(D_35, B_31)))), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.91/1.92  tff(c_82, plain, (r1_tarski(k2_tarski('#skF_8', '#skF_9'), k2_tarski('#skF_10', '#skF_11'))), inference(cnfTransformation, [status(thm)], [f_94])).
% 3.91/1.92  tff(c_211, plain, (![A_66, B_67]: (k2_xboole_0(A_66, B_67)=B_67 | ~r1_tarski(A_66, B_67))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.91/1.92  tff(c_222, plain, (k2_xboole_0(k2_tarski('#skF_8', '#skF_9'), k2_tarski('#skF_10', '#skF_11'))=k2_tarski('#skF_10', '#skF_11')), inference(resolution, [status(thm)], [c_82, c_211])).
% 3.91/1.92  tff(c_34, plain, (![A_20]: (k4_xboole_0(A_20, k1_xboole_0)=A_20)), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.91/1.92  tff(c_38, plain, (![A_23, B_24]: (r1_tarski(A_23, k2_xboole_0(A_23, B_24)))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.91/1.92  tff(c_249, plain, (![A_72, B_73]: (k4_xboole_0(A_72, B_73)=k1_xboole_0 | ~r1_tarski(A_72, B_73))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.91/1.92  tff(c_265, plain, (![A_23, B_24]: (k4_xboole_0(A_23, k2_xboole_0(A_23, B_24))=k1_xboole_0)), inference(resolution, [status(thm)], [c_38, c_249])).
% 3.91/1.92  tff(c_400, plain, (![A_88, B_89]: (k4_xboole_0(A_88, k4_xboole_0(A_88, B_89))=k3_xboole_0(A_88, B_89))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.91/1.92  tff(c_427, plain, (![A_23, B_24]: (k3_xboole_0(A_23, k2_xboole_0(A_23, B_24))=k4_xboole_0(A_23, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_265, c_400])).
% 3.91/1.92  tff(c_437, plain, (![A_23, B_24]: (k3_xboole_0(A_23, k2_xboole_0(A_23, B_24))=A_23)), inference(demodulation, [status(thm), theory('equality')], [c_34, c_427])).
% 3.91/1.92  tff(c_540, plain, (![D_96, B_97, A_98]: (r2_hidden(D_96, B_97) | ~r2_hidden(D_96, k3_xboole_0(A_98, B_97)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.91/1.92  tff(c_2613, plain, (![D_177, A_178, B_179]: (r2_hidden(D_177, k2_xboole_0(A_178, B_179)) | ~r2_hidden(D_177, A_178))), inference(superposition, [status(thm), theory('equality')], [c_437, c_540])).
% 3.91/1.92  tff(c_2793, plain, (![D_191]: (r2_hidden(D_191, k2_tarski('#skF_10', '#skF_11')) | ~r2_hidden(D_191, k2_tarski('#skF_8', '#skF_9')))), inference(superposition, [status(thm), theory('equality')], [c_222, c_2613])).
% 3.91/1.92  tff(c_52, plain, (![D_35, B_31, A_30]: (D_35=B_31 | D_35=A_30 | ~r2_hidden(D_35, k2_tarski(A_30, B_31)))), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.91/1.92  tff(c_2907, plain, (![D_203]: (D_203='#skF_11' | D_203='#skF_10' | ~r2_hidden(D_203, k2_tarski('#skF_8', '#skF_9')))), inference(resolution, [status(thm)], [c_2793, c_52])).
% 3.91/1.92  tff(c_2923, plain, ('#skF_11'='#skF_8' | '#skF_10'='#skF_8'), inference(resolution, [status(thm)], [c_56, c_2907])).
% 3.91/1.92  tff(c_2936, plain, $false, inference(negUnitSimplification, [status(thm)], [c_80, c_78, c_2923])).
% 3.91/1.92  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.91/1.92  
% 3.91/1.92  Inference rules
% 3.91/1.92  ----------------------
% 3.91/1.92  #Ref     : 0
% 3.91/1.92  #Sup     : 742
% 3.91/1.92  #Fact    : 0
% 3.91/1.92  #Define  : 0
% 3.91/1.92  #Split   : 3
% 3.91/1.92  #Chain   : 0
% 3.91/1.92  #Close   : 0
% 3.91/1.92  
% 3.91/1.92  Ordering : KBO
% 3.91/1.92  
% 3.91/1.92  Simplification rules
% 3.91/1.92  ----------------------
% 3.91/1.92  #Subsume      : 115
% 3.91/1.92  #Demod        : 393
% 3.91/1.92  #Tautology    : 422
% 3.91/1.92  #SimpNegUnit  : 31
% 3.91/1.92  #BackRed      : 23
% 3.91/1.92  
% 3.91/1.92  #Partial instantiations: 0
% 3.91/1.92  #Strategies tried      : 1
% 3.91/1.92  
% 3.91/1.92  Timing (in seconds)
% 3.91/1.92  ----------------------
% 3.91/1.92  Preprocessing        : 0.30
% 3.91/1.92  Parsing              : 0.14
% 3.91/1.92  CNF conversion       : 0.03
% 3.91/1.92  Main loop            : 0.65
% 3.91/1.92  Inferencing          : 0.21
% 3.91/1.92  Reduction            : 0.26
% 3.91/1.92  Demodulation         : 0.21
% 3.91/1.92  BG Simplification    : 0.03
% 3.91/1.92  Subsumption          : 0.10
% 3.91/1.92  Abstraction          : 0.04
% 3.91/1.92  MUC search           : 0.00
% 3.91/1.92  Cooper               : 0.00
% 3.91/1.92  Total                : 0.98
% 3.91/1.92  Index Insertion      : 0.00
% 3.91/1.92  Index Deletion       : 0.00
% 3.91/1.92  Index Matching       : 0.00
% 3.91/1.92  BG Taut test         : 0.00
%------------------------------------------------------------------------------
