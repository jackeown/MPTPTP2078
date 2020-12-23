%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:51:04 EST 2020

% Result     : Theorem 3.27s
% Output     : CNFRefutation 3.27s
% Verified   : 
% Statistics : Number of formulae       :   54 (  62 expanded)
%              Number of leaves         :   32 (  36 expanded)
%              Depth                    :    6
%              Number of atoms          :   46 (  61 expanded)
%              Number of equality atoms :   20 (  25 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(f_84,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r1_tarski(k2_xboole_0(k2_tarski(A,B),C),C)
       => r2_hidden(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_zfmisc_1)).

tff(f_67,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_65,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

tff(f_46,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k5_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

tff(f_50,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(k5_xboole_0(A,B),k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_44,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_38,axiom,(
    ! [A,B,C] :
      ( C = k2_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            | r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).

tff(c_74,plain,(
    ~ r2_hidden('#skF_5','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_149,plain,(
    ! [A_72,B_73] : k1_enumset1(A_72,A_72,B_73) = k2_tarski(A_72,B_73) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_42,plain,(
    ! [E_26,B_21,C_22] : r2_hidden(E_26,k1_enumset1(E_26,B_21,C_22)) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_161,plain,(
    ! [A_72,B_73] : r2_hidden(A_72,k2_tarski(A_72,B_73)) ),
    inference(superposition,[status(thm),theory(equality)],[c_149,c_42])).

tff(c_30,plain,(
    ! [A_13,B_14] : r1_tarski(A_13,k2_xboole_0(A_13,B_14)) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_4,plain,(
    ! [B_4,A_3] : k5_xboole_0(B_4,A_3) = k5_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_242,plain,(
    ! [A_96,B_97] : k5_xboole_0(k5_xboole_0(A_96,B_97),k3_xboole_0(A_96,B_97)) = k2_xboole_0(A_96,B_97) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_681,plain,(
    ! [B_114,A_115] : k5_xboole_0(k5_xboole_0(B_114,A_115),k3_xboole_0(A_115,B_114)) = k2_xboole_0(A_115,B_114) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_242])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_279,plain,(
    ! [B_2,A_1] : k5_xboole_0(k5_xboole_0(B_2,A_1),k3_xboole_0(A_1,B_2)) = k2_xboole_0(B_2,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_242])).

tff(c_696,plain,(
    ! [B_114,A_115] : k2_xboole_0(B_114,A_115) = k2_xboole_0(A_115,B_114) ),
    inference(superposition,[status(thm),theory(equality)],[c_681,c_279])).

tff(c_76,plain,(
    r1_tarski(k2_xboole_0(k2_tarski('#skF_5','#skF_6'),'#skF_7'),'#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_181,plain,(
    ! [B_86,A_87] :
      ( B_86 = A_87
      | ~ r1_tarski(B_86,A_87)
      | ~ r1_tarski(A_87,B_86) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_188,plain,
    ( k2_xboole_0(k2_tarski('#skF_5','#skF_6'),'#skF_7') = '#skF_7'
    | ~ r1_tarski('#skF_7',k2_xboole_0(k2_tarski('#skF_5','#skF_6'),'#skF_7')) ),
    inference(resolution,[status(thm)],[c_76,c_181])).

tff(c_204,plain,(
    ~ r1_tarski('#skF_7',k2_xboole_0(k2_tarski('#skF_5','#skF_6'),'#skF_7')) ),
    inference(splitLeft,[status(thm)],[c_188])).

tff(c_788,plain,(
    ~ r1_tarski('#skF_7',k2_xboole_0('#skF_7',k2_tarski('#skF_5','#skF_6'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_696,c_204])).

tff(c_792,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_788])).

tff(c_793,plain,(
    k2_xboole_0(k2_tarski('#skF_5','#skF_6'),'#skF_7') = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_188])).

tff(c_10,plain,(
    ! [D_10,A_5,B_6] :
      ( ~ r2_hidden(D_10,A_5)
      | r2_hidden(D_10,k2_xboole_0(A_5,B_6)) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_855,plain,(
    ! [D_119] :
      ( ~ r2_hidden(D_119,k2_tarski('#skF_5','#skF_6'))
      | r2_hidden(D_119,'#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_793,c_10])).

tff(c_859,plain,(
    r2_hidden('#skF_5','#skF_7') ),
    inference(resolution,[status(thm)],[c_161,c_855])).

tff(c_867,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_859])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n021.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 09:43:49 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.27/1.58  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.27/1.59  
% 3.27/1.59  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.27/1.59  %$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3
% 3.27/1.59  
% 3.27/1.59  %Foreground sorts:
% 3.27/1.59  
% 3.27/1.59  
% 3.27/1.59  %Background operators:
% 3.27/1.59  
% 3.27/1.59  
% 3.27/1.59  %Foreground operators:
% 3.27/1.59  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 3.27/1.59  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.27/1.59  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.27/1.59  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.27/1.59  tff('#skF_7', type, '#skF_7': $i).
% 3.27/1.59  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.27/1.59  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.27/1.59  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.27/1.59  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.27/1.59  tff('#skF_5', type, '#skF_5': $i).
% 3.27/1.59  tff('#skF_6', type, '#skF_6': $i).
% 3.27/1.59  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.27/1.59  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 3.27/1.59  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.27/1.59  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i) > $i).
% 3.27/1.59  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.27/1.59  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.27/1.59  tff(k3_tarski, type, k3_tarski: $i > $i).
% 3.27/1.59  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.27/1.59  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.27/1.59  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 3.27/1.59  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.27/1.59  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.27/1.59  
% 3.27/1.60  tff(f_84, negated_conjecture, ~(![A, B, C]: (r1_tarski(k2_xboole_0(k2_tarski(A, B), C), C) => r2_hidden(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_zfmisc_1)).
% 3.27/1.60  tff(f_67, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 3.27/1.60  tff(f_65, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_enumset1)).
% 3.27/1.60  tff(f_46, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 3.27/1.60  tff(f_29, axiom, (![A, B]: (k5_xboole_0(A, B) = k5_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 3.27/1.60  tff(f_50, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(k5_xboole_0(A, B), k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t94_xboole_1)).
% 3.27/1.60  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 3.27/1.60  tff(f_44, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.27/1.60  tff(f_38, axiom, (![A, B, C]: ((C = k2_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) | r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_xboole_0)).
% 3.27/1.60  tff(c_74, plain, (~r2_hidden('#skF_5', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.27/1.60  tff(c_149, plain, (![A_72, B_73]: (k1_enumset1(A_72, A_72, B_73)=k2_tarski(A_72, B_73))), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.27/1.60  tff(c_42, plain, (![E_26, B_21, C_22]: (r2_hidden(E_26, k1_enumset1(E_26, B_21, C_22)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.27/1.60  tff(c_161, plain, (![A_72, B_73]: (r2_hidden(A_72, k2_tarski(A_72, B_73)))), inference(superposition, [status(thm), theory('equality')], [c_149, c_42])).
% 3.27/1.60  tff(c_30, plain, (![A_13, B_14]: (r1_tarski(A_13, k2_xboole_0(A_13, B_14)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.27/1.60  tff(c_4, plain, (![B_4, A_3]: (k5_xboole_0(B_4, A_3)=k5_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.27/1.60  tff(c_242, plain, (![A_96, B_97]: (k5_xboole_0(k5_xboole_0(A_96, B_97), k3_xboole_0(A_96, B_97))=k2_xboole_0(A_96, B_97))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.27/1.60  tff(c_681, plain, (![B_114, A_115]: (k5_xboole_0(k5_xboole_0(B_114, A_115), k3_xboole_0(A_115, B_114))=k2_xboole_0(A_115, B_114))), inference(superposition, [status(thm), theory('equality')], [c_4, c_242])).
% 3.27/1.60  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.27/1.60  tff(c_279, plain, (![B_2, A_1]: (k5_xboole_0(k5_xboole_0(B_2, A_1), k3_xboole_0(A_1, B_2))=k2_xboole_0(B_2, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_242])).
% 3.27/1.60  tff(c_696, plain, (![B_114, A_115]: (k2_xboole_0(B_114, A_115)=k2_xboole_0(A_115, B_114))), inference(superposition, [status(thm), theory('equality')], [c_681, c_279])).
% 3.27/1.60  tff(c_76, plain, (r1_tarski(k2_xboole_0(k2_tarski('#skF_5', '#skF_6'), '#skF_7'), '#skF_7')), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.27/1.60  tff(c_181, plain, (![B_86, A_87]: (B_86=A_87 | ~r1_tarski(B_86, A_87) | ~r1_tarski(A_87, B_86))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.27/1.60  tff(c_188, plain, (k2_xboole_0(k2_tarski('#skF_5', '#skF_6'), '#skF_7')='#skF_7' | ~r1_tarski('#skF_7', k2_xboole_0(k2_tarski('#skF_5', '#skF_6'), '#skF_7'))), inference(resolution, [status(thm)], [c_76, c_181])).
% 3.27/1.60  tff(c_204, plain, (~r1_tarski('#skF_7', k2_xboole_0(k2_tarski('#skF_5', '#skF_6'), '#skF_7'))), inference(splitLeft, [status(thm)], [c_188])).
% 3.27/1.60  tff(c_788, plain, (~r1_tarski('#skF_7', k2_xboole_0('#skF_7', k2_tarski('#skF_5', '#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_696, c_204])).
% 3.27/1.60  tff(c_792, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_30, c_788])).
% 3.27/1.60  tff(c_793, plain, (k2_xboole_0(k2_tarski('#skF_5', '#skF_6'), '#skF_7')='#skF_7'), inference(splitRight, [status(thm)], [c_188])).
% 3.27/1.60  tff(c_10, plain, (![D_10, A_5, B_6]: (~r2_hidden(D_10, A_5) | r2_hidden(D_10, k2_xboole_0(A_5, B_6)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.27/1.60  tff(c_855, plain, (![D_119]: (~r2_hidden(D_119, k2_tarski('#skF_5', '#skF_6')) | r2_hidden(D_119, '#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_793, c_10])).
% 3.27/1.60  tff(c_859, plain, (r2_hidden('#skF_5', '#skF_7')), inference(resolution, [status(thm)], [c_161, c_855])).
% 3.27/1.60  tff(c_867, plain, $false, inference(negUnitSimplification, [status(thm)], [c_74, c_859])).
% 3.27/1.60  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.27/1.60  
% 3.27/1.60  Inference rules
% 3.27/1.60  ----------------------
% 3.27/1.60  #Ref     : 0
% 3.27/1.60  #Sup     : 209
% 3.27/1.60  #Fact    : 0
% 3.27/1.60  #Define  : 0
% 3.27/1.60  #Split   : 1
% 3.27/1.60  #Chain   : 0
% 3.27/1.60  #Close   : 0
% 3.27/1.60  
% 3.27/1.60  Ordering : KBO
% 3.27/1.60  
% 3.27/1.60  Simplification rules
% 3.27/1.60  ----------------------
% 3.27/1.60  #Subsume      : 5
% 3.27/1.60  #Demod        : 69
% 3.27/1.60  #Tautology    : 72
% 3.27/1.60  #SimpNegUnit  : 1
% 3.27/1.60  #BackRed      : 3
% 3.27/1.60  
% 3.27/1.60  #Partial instantiations: 0
% 3.27/1.60  #Strategies tried      : 1
% 3.27/1.60  
% 3.27/1.60  Timing (in seconds)
% 3.27/1.60  ----------------------
% 3.27/1.60  Preprocessing        : 0.43
% 3.27/1.60  Parsing              : 0.22
% 3.27/1.60  CNF conversion       : 0.03
% 3.27/1.60  Main loop            : 0.38
% 3.27/1.60  Inferencing          : 0.11
% 3.27/1.60  Reduction            : 0.17
% 3.27/1.60  Demodulation         : 0.14
% 3.27/1.60  BG Simplification    : 0.03
% 3.27/1.60  Subsumption          : 0.06
% 3.27/1.60  Abstraction          : 0.03
% 3.27/1.60  MUC search           : 0.00
% 3.27/1.60  Cooper               : 0.00
% 3.27/1.60  Total                : 0.84
% 3.27/1.60  Index Insertion      : 0.00
% 3.27/1.60  Index Deletion       : 0.00
% 3.27/1.60  Index Matching       : 0.00
% 3.27/1.60  BG Taut test         : 0.00
%------------------------------------------------------------------------------
