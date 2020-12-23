%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:50:04 EST 2020

% Result     : Theorem 2.78s
% Output     : CNFRefutation 3.03s
% Verified   : 
% Statistics : Number of formulae       :   72 ( 124 expanded)
%              Number of leaves         :   24 (  51 expanded)
%              Depth                    :   10
%              Number of atoms          :   87 ( 244 expanded)
%              Number of equality atoms :   60 ( 209 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1

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

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_75,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( k1_tarski(A) = k2_xboole_0(B,C)
          & ~ ( B = k1_tarski(A)
              & C = k1_tarski(A) )
          & ~ ( B = k1_xboole_0
              & C = k1_tarski(A) )
          & ~ ( B = k1_tarski(A)
              & C = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_zfmisc_1)).

tff(f_38,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_54,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k1_tarski(B))
    <=> ( A = k1_xboole_0
        | A = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_zfmisc_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_36,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_40,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_56,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(c_32,plain,
    ( k1_tarski('#skF_2') != '#skF_4'
    | k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_43,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_32])).

tff(c_30,plain,
    ( k1_xboole_0 != '#skF_4'
    | k1_tarski('#skF_2') != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_38,plain,(
    k1_tarski('#skF_2') != '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_30])).

tff(c_36,plain,(
    k2_xboole_0('#skF_3','#skF_4') = k1_tarski('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_54,plain,(
    ! [A_29,B_30] : r1_tarski(A_29,k2_xboole_0(A_29,B_30)) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_57,plain,(
    r1_tarski('#skF_3',k1_tarski('#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_54])).

tff(c_382,plain,(
    ! [B_57,A_58] :
      ( k1_tarski(B_57) = A_58
      | k1_xboole_0 = A_58
      | ~ r1_tarski(A_58,k1_tarski(B_57)) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_392,plain,
    ( k1_tarski('#skF_2') = '#skF_3'
    | k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_57,c_382])).

tff(c_402,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_43,c_38,c_392])).

tff(c_403,plain,(
    k1_tarski('#skF_2') != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_32])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_647,plain,(
    ! [A_83,B_84] :
      ( ~ r2_hidden('#skF_1'(A_83,B_84),B_84)
      | r1_tarski(A_83,B_84) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_654,plain,(
    ! [A_85] : r1_tarski(A_85,A_85) ),
    inference(resolution,[status(thm)],[c_6,c_647])).

tff(c_8,plain,(
    ! [A_6,B_7] :
      ( k2_xboole_0(A_6,B_7) = B_7
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_658,plain,(
    ! [A_85] : k2_xboole_0(A_85,A_85) = A_85 ),
    inference(resolution,[status(thm)],[c_654,c_8])).

tff(c_12,plain,(
    ! [B_11,A_10] : k2_tarski(B_11,A_10) = k2_tarski(A_10,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_468,plain,(
    ! [A_68,B_69] : k3_tarski(k2_tarski(A_68,B_69)) = k2_xboole_0(A_68,B_69) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_542,plain,(
    ! [A_77,B_78] : k3_tarski(k2_tarski(A_77,B_78)) = k2_xboole_0(B_78,A_77) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_468])).

tff(c_28,plain,(
    ! [A_24,B_25] : k3_tarski(k2_tarski(A_24,B_25)) = k2_xboole_0(A_24,B_25) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_568,plain,(
    ! [B_79,A_80] : k2_xboole_0(B_79,A_80) = k2_xboole_0(A_80,B_79) ),
    inference(superposition,[status(thm),theory(equality)],[c_542,c_28])).

tff(c_10,plain,(
    ! [A_8,B_9] : r1_tarski(A_8,k2_xboole_0(A_8,B_9)) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_619,plain,(
    ! [A_81,B_82] : r1_tarski(A_81,k2_xboole_0(B_82,A_81)) ),
    inference(superposition,[status(thm),theory(equality)],[c_568,c_10])).

tff(c_637,plain,(
    r1_tarski('#skF_4',k1_tarski('#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_619])).

tff(c_404,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_32])).

tff(c_22,plain,(
    ! [B_23,A_22] :
      ( k1_tarski(B_23) = A_22
      | k1_xboole_0 = A_22
      | ~ r1_tarski(A_22,k1_tarski(B_23)) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_723,plain,(
    ! [B_91,A_92] :
      ( k1_tarski(B_91) = A_92
      | A_92 = '#skF_3'
      | ~ r1_tarski(A_92,k1_tarski(B_91)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_404,c_22])).

tff(c_730,plain,
    ( k1_tarski('#skF_2') = '#skF_4'
    | '#skF_3' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_637,c_723])).

tff(c_738,plain,(
    '#skF_3' = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_403,c_730])).

tff(c_610,plain,(
    k2_xboole_0('#skF_4','#skF_3') = k1_tarski('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_568])).

tff(c_742,plain,(
    k2_xboole_0('#skF_4','#skF_4') = k1_tarski('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_738,c_610])).

tff(c_748,plain,(
    k1_tarski('#skF_2') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_658,c_742])).

tff(c_750,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_403,c_748])).

tff(c_751,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_30])).

tff(c_752,plain,(
    k1_tarski('#skF_2') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_30])).

tff(c_34,plain,
    ( k1_tarski('#skF_2') != '#skF_4'
    | k1_tarski('#skF_2') != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_780,plain,(
    '#skF_3' != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_752,c_752,c_34])).

tff(c_852,plain,(
    ! [A_101,B_102] : k3_tarski(k2_tarski(A_101,B_102)) = k2_xboole_0(A_101,B_102) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_959,plain,(
    ! [B_108,A_109] : k3_tarski(k2_tarski(B_108,A_109)) = k2_xboole_0(A_109,B_108) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_852])).

tff(c_986,plain,(
    ! [B_112,A_113] : k2_xboole_0(B_112,A_113) = k2_xboole_0(A_113,B_112) ),
    inference(superposition,[status(thm),theory(equality)],[c_959,c_28])).

tff(c_759,plain,(
    k2_xboole_0('#skF_3','#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_752,c_36])).

tff(c_1016,plain,(
    k2_xboole_0('#skF_4','#skF_3') = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_986,c_759])).

tff(c_1060,plain,(
    r1_tarski('#skF_4','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1016,c_10])).

tff(c_1606,plain,(
    ! [B_137,A_138] :
      ( k1_tarski(B_137) = A_138
      | k1_xboole_0 = A_138
      | ~ r1_tarski(A_138,k1_tarski(B_137)) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_1613,plain,(
    ! [A_138] :
      ( k1_tarski('#skF_2') = A_138
      | k1_xboole_0 = A_138
      | ~ r1_tarski(A_138,'#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_752,c_1606])).

tff(c_1683,plain,(
    ! [A_140] :
      ( A_140 = '#skF_3'
      | k1_xboole_0 = A_140
      | ~ r1_tarski(A_140,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_752,c_1613])).

tff(c_1690,plain,
    ( '#skF_3' = '#skF_4'
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_1060,c_1683])).

tff(c_1701,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_751,c_780,c_1690])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:54:53 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.78/1.45  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.78/1.45  
% 2.78/1.45  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.78/1.46  %$ r2_hidden > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 2.78/1.46  
% 2.78/1.46  %Foreground sorts:
% 2.78/1.46  
% 2.78/1.46  
% 2.78/1.46  %Background operators:
% 2.78/1.46  
% 2.78/1.46  
% 2.78/1.46  %Foreground operators:
% 2.78/1.46  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.78/1.46  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.78/1.46  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.78/1.46  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.78/1.46  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.78/1.46  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.78/1.46  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.78/1.46  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.78/1.46  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.78/1.46  tff('#skF_2', type, '#skF_2': $i).
% 2.78/1.46  tff('#skF_3', type, '#skF_3': $i).
% 2.78/1.46  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.78/1.46  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.78/1.46  tff('#skF_4', type, '#skF_4': $i).
% 2.78/1.46  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.78/1.46  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.78/1.46  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.78/1.46  
% 3.03/1.47  tff(f_75, negated_conjecture, ~(![A, B, C]: ~((((k1_tarski(A) = k2_xboole_0(B, C)) & ~((B = k1_tarski(A)) & (C = k1_tarski(A)))) & ~((B = k1_xboole_0) & (C = k1_tarski(A)))) & ~((B = k1_tarski(A)) & (C = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_zfmisc_1)).
% 3.03/1.47  tff(f_38, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 3.03/1.47  tff(f_54, axiom, (![A, B]: (r1_tarski(A, k1_tarski(B)) <=> ((A = k1_xboole_0) | (A = k1_tarski(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_zfmisc_1)).
% 3.03/1.47  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 3.03/1.47  tff(f_36, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 3.03/1.47  tff(f_40, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 3.03/1.47  tff(f_56, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 3.03/1.47  tff(c_32, plain, (k1_tarski('#skF_2')!='#skF_4' | k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.03/1.47  tff(c_43, plain, (k1_xboole_0!='#skF_3'), inference(splitLeft, [status(thm)], [c_32])).
% 3.03/1.47  tff(c_30, plain, (k1_xboole_0!='#skF_4' | k1_tarski('#skF_2')!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.03/1.47  tff(c_38, plain, (k1_tarski('#skF_2')!='#skF_3'), inference(splitLeft, [status(thm)], [c_30])).
% 3.03/1.47  tff(c_36, plain, (k2_xboole_0('#skF_3', '#skF_4')=k1_tarski('#skF_2')), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.03/1.47  tff(c_54, plain, (![A_29, B_30]: (r1_tarski(A_29, k2_xboole_0(A_29, B_30)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.03/1.47  tff(c_57, plain, (r1_tarski('#skF_3', k1_tarski('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_36, c_54])).
% 3.03/1.47  tff(c_382, plain, (![B_57, A_58]: (k1_tarski(B_57)=A_58 | k1_xboole_0=A_58 | ~r1_tarski(A_58, k1_tarski(B_57)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.03/1.47  tff(c_392, plain, (k1_tarski('#skF_2')='#skF_3' | k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_57, c_382])).
% 3.03/1.47  tff(c_402, plain, $false, inference(negUnitSimplification, [status(thm)], [c_43, c_38, c_392])).
% 3.03/1.47  tff(c_403, plain, (k1_tarski('#skF_2')!='#skF_4'), inference(splitRight, [status(thm)], [c_32])).
% 3.03/1.47  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.03/1.47  tff(c_647, plain, (![A_83, B_84]: (~r2_hidden('#skF_1'(A_83, B_84), B_84) | r1_tarski(A_83, B_84))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.03/1.47  tff(c_654, plain, (![A_85]: (r1_tarski(A_85, A_85))), inference(resolution, [status(thm)], [c_6, c_647])).
% 3.03/1.47  tff(c_8, plain, (![A_6, B_7]: (k2_xboole_0(A_6, B_7)=B_7 | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.03/1.47  tff(c_658, plain, (![A_85]: (k2_xboole_0(A_85, A_85)=A_85)), inference(resolution, [status(thm)], [c_654, c_8])).
% 3.03/1.47  tff(c_12, plain, (![B_11, A_10]: (k2_tarski(B_11, A_10)=k2_tarski(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.03/1.47  tff(c_468, plain, (![A_68, B_69]: (k3_tarski(k2_tarski(A_68, B_69))=k2_xboole_0(A_68, B_69))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.03/1.47  tff(c_542, plain, (![A_77, B_78]: (k3_tarski(k2_tarski(A_77, B_78))=k2_xboole_0(B_78, A_77))), inference(superposition, [status(thm), theory('equality')], [c_12, c_468])).
% 3.03/1.47  tff(c_28, plain, (![A_24, B_25]: (k3_tarski(k2_tarski(A_24, B_25))=k2_xboole_0(A_24, B_25))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.03/1.47  tff(c_568, plain, (![B_79, A_80]: (k2_xboole_0(B_79, A_80)=k2_xboole_0(A_80, B_79))), inference(superposition, [status(thm), theory('equality')], [c_542, c_28])).
% 3.03/1.47  tff(c_10, plain, (![A_8, B_9]: (r1_tarski(A_8, k2_xboole_0(A_8, B_9)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.03/1.47  tff(c_619, plain, (![A_81, B_82]: (r1_tarski(A_81, k2_xboole_0(B_82, A_81)))), inference(superposition, [status(thm), theory('equality')], [c_568, c_10])).
% 3.03/1.47  tff(c_637, plain, (r1_tarski('#skF_4', k1_tarski('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_36, c_619])).
% 3.03/1.47  tff(c_404, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_32])).
% 3.03/1.47  tff(c_22, plain, (![B_23, A_22]: (k1_tarski(B_23)=A_22 | k1_xboole_0=A_22 | ~r1_tarski(A_22, k1_tarski(B_23)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.03/1.47  tff(c_723, plain, (![B_91, A_92]: (k1_tarski(B_91)=A_92 | A_92='#skF_3' | ~r1_tarski(A_92, k1_tarski(B_91)))), inference(demodulation, [status(thm), theory('equality')], [c_404, c_22])).
% 3.03/1.47  tff(c_730, plain, (k1_tarski('#skF_2')='#skF_4' | '#skF_3'='#skF_4'), inference(resolution, [status(thm)], [c_637, c_723])).
% 3.03/1.47  tff(c_738, plain, ('#skF_3'='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_403, c_730])).
% 3.03/1.47  tff(c_610, plain, (k2_xboole_0('#skF_4', '#skF_3')=k1_tarski('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_36, c_568])).
% 3.03/1.47  tff(c_742, plain, (k2_xboole_0('#skF_4', '#skF_4')=k1_tarski('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_738, c_610])).
% 3.03/1.47  tff(c_748, plain, (k1_tarski('#skF_2')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_658, c_742])).
% 3.03/1.47  tff(c_750, plain, $false, inference(negUnitSimplification, [status(thm)], [c_403, c_748])).
% 3.03/1.47  tff(c_751, plain, (k1_xboole_0!='#skF_4'), inference(splitRight, [status(thm)], [c_30])).
% 3.03/1.47  tff(c_752, plain, (k1_tarski('#skF_2')='#skF_3'), inference(splitRight, [status(thm)], [c_30])).
% 3.03/1.47  tff(c_34, plain, (k1_tarski('#skF_2')!='#skF_4' | k1_tarski('#skF_2')!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.03/1.47  tff(c_780, plain, ('#skF_3'!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_752, c_752, c_34])).
% 3.03/1.47  tff(c_852, plain, (![A_101, B_102]: (k3_tarski(k2_tarski(A_101, B_102))=k2_xboole_0(A_101, B_102))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.03/1.47  tff(c_959, plain, (![B_108, A_109]: (k3_tarski(k2_tarski(B_108, A_109))=k2_xboole_0(A_109, B_108))), inference(superposition, [status(thm), theory('equality')], [c_12, c_852])).
% 3.03/1.47  tff(c_986, plain, (![B_112, A_113]: (k2_xboole_0(B_112, A_113)=k2_xboole_0(A_113, B_112))), inference(superposition, [status(thm), theory('equality')], [c_959, c_28])).
% 3.03/1.47  tff(c_759, plain, (k2_xboole_0('#skF_3', '#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_752, c_36])).
% 3.03/1.47  tff(c_1016, plain, (k2_xboole_0('#skF_4', '#skF_3')='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_986, c_759])).
% 3.03/1.47  tff(c_1060, plain, (r1_tarski('#skF_4', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1016, c_10])).
% 3.03/1.47  tff(c_1606, plain, (![B_137, A_138]: (k1_tarski(B_137)=A_138 | k1_xboole_0=A_138 | ~r1_tarski(A_138, k1_tarski(B_137)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.03/1.47  tff(c_1613, plain, (![A_138]: (k1_tarski('#skF_2')=A_138 | k1_xboole_0=A_138 | ~r1_tarski(A_138, '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_752, c_1606])).
% 3.03/1.47  tff(c_1683, plain, (![A_140]: (A_140='#skF_3' | k1_xboole_0=A_140 | ~r1_tarski(A_140, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_752, c_1613])).
% 3.03/1.47  tff(c_1690, plain, ('#skF_3'='#skF_4' | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_1060, c_1683])).
% 3.03/1.47  tff(c_1701, plain, $false, inference(negUnitSimplification, [status(thm)], [c_751, c_780, c_1690])).
% 3.03/1.47  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.03/1.47  
% 3.03/1.47  Inference rules
% 3.03/1.47  ----------------------
% 3.03/1.47  #Ref     : 0
% 3.03/1.47  #Sup     : 406
% 3.03/1.47  #Fact    : 0
% 3.03/1.47  #Define  : 0
% 3.03/1.47  #Split   : 3
% 3.03/1.47  #Chain   : 0
% 3.03/1.47  #Close   : 0
% 3.03/1.47  
% 3.03/1.47  Ordering : KBO
% 3.03/1.47  
% 3.03/1.47  Simplification rules
% 3.03/1.47  ----------------------
% 3.03/1.47  #Subsume      : 14
% 3.03/1.47  #Demod        : 293
% 3.03/1.47  #Tautology    : 328
% 3.03/1.47  #SimpNegUnit  : 5
% 3.03/1.47  #BackRed      : 17
% 3.03/1.47  
% 3.03/1.47  #Partial instantiations: 0
% 3.03/1.47  #Strategies tried      : 1
% 3.03/1.47  
% 3.03/1.47  Timing (in seconds)
% 3.03/1.47  ----------------------
% 3.03/1.47  Preprocessing        : 0.29
% 3.03/1.47  Parsing              : 0.16
% 3.03/1.47  CNF conversion       : 0.02
% 3.03/1.47  Main loop            : 0.41
% 3.03/1.47  Inferencing          : 0.15
% 3.03/1.47  Reduction            : 0.16
% 3.03/1.47  Demodulation         : 0.12
% 3.03/1.47  BG Simplification    : 0.02
% 3.03/1.47  Subsumption          : 0.05
% 3.03/1.47  Abstraction          : 0.02
% 3.03/1.47  MUC search           : 0.00
% 3.03/1.47  Cooper               : 0.00
% 3.03/1.48  Total                : 0.74
% 3.03/1.48  Index Insertion      : 0.00
% 3.03/1.48  Index Deletion       : 0.00
% 3.03/1.48  Index Matching       : 0.00
% 3.03/1.48  BG Taut test         : 0.00
%------------------------------------------------------------------------------
