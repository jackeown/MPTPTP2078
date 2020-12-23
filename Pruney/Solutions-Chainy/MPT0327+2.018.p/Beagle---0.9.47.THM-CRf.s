%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:54:32 EST 2020

% Result     : Theorem 6.15s
% Output     : CNFRefutation 6.15s
% Verified   : 
% Statistics : Number of formulae       :   53 (  61 expanded)
%              Number of leaves         :   31 (  36 expanded)
%              Depth                    :   10
%              Number of atoms          :   51 (  65 expanded)
%              Number of equality atoms :   19 (  26 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_112,negated_conjecture,(
    ~ ! [A,B] :
        ( r2_hidden(A,B)
       => k2_xboole_0(k4_xboole_0(B,k1_tarski(A)),k1_tarski(A)) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t140_zfmisc_1)).

tff(f_105,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_81,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_93,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_69,axiom,(
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

tff(f_44,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_91,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

tff(c_82,plain,(
    r2_hidden('#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_283,plain,(
    ! [A_73,B_74] :
      ( r1_tarski(k1_tarski(A_73),B_74)
      | ~ r2_hidden(A_73,B_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_54,plain,(
    ! [A_26,B_27] :
      ( k2_xboole_0(A_26,B_27) = B_27
      | ~ r1_tarski(A_26,B_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_378,plain,(
    ! [A_96,B_97] :
      ( k2_xboole_0(k1_tarski(A_96),B_97) = B_97
      | ~ r2_hidden(A_96,B_97) ) ),
    inference(resolution,[status(thm)],[c_283,c_54])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_394,plain,(
    ! [B_97,A_96] :
      ( k2_xboole_0(B_97,k1_tarski(A_96)) = B_97
      | ~ r2_hidden(A_96,B_97) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_378,c_2])).

tff(c_64,plain,(
    ! [A_33,B_34] : k5_xboole_0(A_33,k4_xboole_0(B_34,A_33)) = k2_xboole_0(A_33,B_34) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_42,plain,(
    ! [A_17,B_18] :
      ( r2_hidden('#skF_4'(A_17,B_18),B_18)
      | r1_xboole_0(A_17,B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_304,plain,(
    ! [A_82,B_83] :
      ( r2_hidden('#skF_4'(A_82,B_83),A_82)
      | r1_xboole_0(A_82,B_83) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_12,plain,(
    ! [D_13,B_9,A_8] :
      ( ~ r2_hidden(D_13,B_9)
      | ~ r2_hidden(D_13,k4_xboole_0(A_8,B_9)) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_4359,plain,(
    ! [A_288,B_289,B_290] :
      ( ~ r2_hidden('#skF_4'(k4_xboole_0(A_288,B_289),B_290),B_289)
      | r1_xboole_0(k4_xboole_0(A_288,B_289),B_290) ) ),
    inference(resolution,[status(thm)],[c_304,c_12])).

tff(c_4408,plain,(
    ! [A_291,B_292] : r1_xboole_0(k4_xboole_0(A_291,B_292),B_292) ),
    inference(resolution,[status(thm)],[c_42,c_4359])).

tff(c_60,plain,(
    ! [A_31,B_32] :
      ( k4_xboole_0(A_31,B_32) = A_31
      | ~ r1_xboole_0(A_31,B_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_5501,plain,(
    ! [A_344,B_345] : k4_xboole_0(k4_xboole_0(A_344,B_345),B_345) = k4_xboole_0(A_344,B_345) ),
    inference(resolution,[status(thm)],[c_4408,c_60])).

tff(c_5631,plain,(
    ! [B_345,A_344] : k5_xboole_0(B_345,k4_xboole_0(A_344,B_345)) = k2_xboole_0(B_345,k4_xboole_0(A_344,B_345)) ),
    inference(superposition,[status(thm),theory(equality)],[c_5501,c_64])).

tff(c_5692,plain,(
    ! [B_345,A_344] : k2_xboole_0(B_345,k4_xboole_0(A_344,B_345)) = k2_xboole_0(B_345,A_344) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_5631])).

tff(c_80,plain,(
    k2_xboole_0(k4_xboole_0('#skF_6',k1_tarski('#skF_5')),k1_tarski('#skF_5')) != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_84,plain,(
    k2_xboole_0(k1_tarski('#skF_5'),k4_xboole_0('#skF_6',k1_tarski('#skF_5'))) != '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_80])).

tff(c_5778,plain,(
    k2_xboole_0(k1_tarski('#skF_5'),'#skF_6') != '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5692,c_84])).

tff(c_5779,plain,(
    k2_xboole_0('#skF_6',k1_tarski('#skF_5')) != '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_5778])).

tff(c_5843,plain,(
    ~ r2_hidden('#skF_5','#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_394,c_5779])).

tff(c_5847,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_5843])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:36:41 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.15/2.46  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.15/2.47  
% 6.15/2.47  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.15/2.47  %$ r2_hidden > r1_xboole_0 > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 6.15/2.47  
% 6.15/2.47  %Foreground sorts:
% 6.15/2.47  
% 6.15/2.47  
% 6.15/2.47  %Background operators:
% 6.15/2.47  
% 6.15/2.47  
% 6.15/2.47  %Foreground operators:
% 6.15/2.47  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.15/2.47  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 6.15/2.47  tff(k1_tarski, type, k1_tarski: $i > $i).
% 6.15/2.47  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 6.15/2.47  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 6.15/2.47  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 6.15/2.47  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 6.15/2.47  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.15/2.47  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 6.15/2.47  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 6.15/2.47  tff('#skF_5', type, '#skF_5': $i).
% 6.15/2.47  tff('#skF_6', type, '#skF_6': $i).
% 6.15/2.47  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 6.15/2.47  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 6.15/2.47  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 6.15/2.47  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.15/2.47  tff(k3_tarski, type, k3_tarski: $i > $i).
% 6.15/2.47  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 6.15/2.47  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.15/2.47  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 6.15/2.47  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 6.15/2.47  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 6.15/2.47  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 6.15/2.47  
% 6.15/2.48  tff(f_112, negated_conjecture, ~(![A, B]: (r2_hidden(A, B) => (k2_xboole_0(k4_xboole_0(B, k1_tarski(A)), k1_tarski(A)) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t140_zfmisc_1)).
% 6.15/2.48  tff(f_105, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 6.15/2.48  tff(f_81, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 6.15/2.48  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 6.15/2.48  tff(f_93, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_xboole_1)).
% 6.15/2.48  tff(f_69, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 6.15/2.48  tff(f_44, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 6.15/2.48  tff(f_91, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_xboole_1)).
% 6.15/2.48  tff(c_82, plain, (r2_hidden('#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_112])).
% 6.15/2.48  tff(c_283, plain, (![A_73, B_74]: (r1_tarski(k1_tarski(A_73), B_74) | ~r2_hidden(A_73, B_74))), inference(cnfTransformation, [status(thm)], [f_105])).
% 6.15/2.48  tff(c_54, plain, (![A_26, B_27]: (k2_xboole_0(A_26, B_27)=B_27 | ~r1_tarski(A_26, B_27))), inference(cnfTransformation, [status(thm)], [f_81])).
% 6.15/2.48  tff(c_378, plain, (![A_96, B_97]: (k2_xboole_0(k1_tarski(A_96), B_97)=B_97 | ~r2_hidden(A_96, B_97))), inference(resolution, [status(thm)], [c_283, c_54])).
% 6.15/2.48  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 6.15/2.48  tff(c_394, plain, (![B_97, A_96]: (k2_xboole_0(B_97, k1_tarski(A_96))=B_97 | ~r2_hidden(A_96, B_97))), inference(superposition, [status(thm), theory('equality')], [c_378, c_2])).
% 6.15/2.48  tff(c_64, plain, (![A_33, B_34]: (k5_xboole_0(A_33, k4_xboole_0(B_34, A_33))=k2_xboole_0(A_33, B_34))), inference(cnfTransformation, [status(thm)], [f_93])).
% 6.15/2.48  tff(c_42, plain, (![A_17, B_18]: (r2_hidden('#skF_4'(A_17, B_18), B_18) | r1_xboole_0(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_69])).
% 6.15/2.48  tff(c_304, plain, (![A_82, B_83]: (r2_hidden('#skF_4'(A_82, B_83), A_82) | r1_xboole_0(A_82, B_83))), inference(cnfTransformation, [status(thm)], [f_69])).
% 6.15/2.48  tff(c_12, plain, (![D_13, B_9, A_8]: (~r2_hidden(D_13, B_9) | ~r2_hidden(D_13, k4_xboole_0(A_8, B_9)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 6.15/2.48  tff(c_4359, plain, (![A_288, B_289, B_290]: (~r2_hidden('#skF_4'(k4_xboole_0(A_288, B_289), B_290), B_289) | r1_xboole_0(k4_xboole_0(A_288, B_289), B_290))), inference(resolution, [status(thm)], [c_304, c_12])).
% 6.15/2.48  tff(c_4408, plain, (![A_291, B_292]: (r1_xboole_0(k4_xboole_0(A_291, B_292), B_292))), inference(resolution, [status(thm)], [c_42, c_4359])).
% 6.15/2.48  tff(c_60, plain, (![A_31, B_32]: (k4_xboole_0(A_31, B_32)=A_31 | ~r1_xboole_0(A_31, B_32))), inference(cnfTransformation, [status(thm)], [f_91])).
% 6.15/2.48  tff(c_5501, plain, (![A_344, B_345]: (k4_xboole_0(k4_xboole_0(A_344, B_345), B_345)=k4_xboole_0(A_344, B_345))), inference(resolution, [status(thm)], [c_4408, c_60])).
% 6.15/2.48  tff(c_5631, plain, (![B_345, A_344]: (k5_xboole_0(B_345, k4_xboole_0(A_344, B_345))=k2_xboole_0(B_345, k4_xboole_0(A_344, B_345)))), inference(superposition, [status(thm), theory('equality')], [c_5501, c_64])).
% 6.15/2.48  tff(c_5692, plain, (![B_345, A_344]: (k2_xboole_0(B_345, k4_xboole_0(A_344, B_345))=k2_xboole_0(B_345, A_344))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_5631])).
% 6.15/2.48  tff(c_80, plain, (k2_xboole_0(k4_xboole_0('#skF_6', k1_tarski('#skF_5')), k1_tarski('#skF_5'))!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_112])).
% 6.15/2.48  tff(c_84, plain, (k2_xboole_0(k1_tarski('#skF_5'), k4_xboole_0('#skF_6', k1_tarski('#skF_5')))!='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_2, c_80])).
% 6.15/2.48  tff(c_5778, plain, (k2_xboole_0(k1_tarski('#skF_5'), '#skF_6')!='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_5692, c_84])).
% 6.15/2.48  tff(c_5779, plain, (k2_xboole_0('#skF_6', k1_tarski('#skF_5'))!='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_2, c_5778])).
% 6.15/2.48  tff(c_5843, plain, (~r2_hidden('#skF_5', '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_394, c_5779])).
% 6.15/2.48  tff(c_5847, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_82, c_5843])).
% 6.15/2.48  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.15/2.48  
% 6.15/2.48  Inference rules
% 6.15/2.48  ----------------------
% 6.15/2.48  #Ref     : 0
% 6.15/2.48  #Sup     : 1395
% 6.15/2.48  #Fact    : 0
% 6.15/2.48  #Define  : 0
% 6.15/2.48  #Split   : 6
% 6.15/2.48  #Chain   : 0
% 6.15/2.48  #Close   : 0
% 6.15/2.48  
% 6.15/2.48  Ordering : KBO
% 6.15/2.48  
% 6.15/2.48  Simplification rules
% 6.15/2.48  ----------------------
% 6.15/2.48  #Subsume      : 286
% 6.15/2.48  #Demod        : 469
% 6.15/2.48  #Tautology    : 597
% 6.15/2.48  #SimpNegUnit  : 32
% 6.15/2.48  #BackRed      : 8
% 6.15/2.48  
% 6.15/2.48  #Partial instantiations: 0
% 6.15/2.48  #Strategies tried      : 1
% 6.15/2.48  
% 6.15/2.48  Timing (in seconds)
% 6.15/2.48  ----------------------
% 6.15/2.48  Preprocessing        : 0.41
% 6.15/2.48  Parsing              : 0.21
% 6.15/2.48  CNF conversion       : 0.03
% 6.15/2.48  Main loop            : 1.17
% 6.15/2.48  Inferencing          : 0.39
% 6.15/2.49  Reduction            : 0.37
% 6.15/2.49  Demodulation         : 0.26
% 6.15/2.49  BG Simplification    : 0.05
% 6.15/2.49  Subsumption          : 0.26
% 6.15/2.49  Abstraction          : 0.06
% 6.15/2.49  MUC search           : 0.00
% 6.15/2.49  Cooper               : 0.00
% 6.15/2.49  Total                : 1.60
% 6.15/2.49  Index Insertion      : 0.00
% 6.15/2.49  Index Deletion       : 0.00
% 6.15/2.49  Index Matching       : 0.00
% 6.15/2.49  BG Taut test         : 0.00
%------------------------------------------------------------------------------
