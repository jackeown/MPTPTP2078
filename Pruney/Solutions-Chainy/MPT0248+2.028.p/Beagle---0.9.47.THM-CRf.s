%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:50:07 EST 2020

% Result     : Theorem 2.89s
% Output     : CNFRefutation 2.89s
% Verified   : 
% Statistics : Number of formulae       :   65 ( 106 expanded)
%              Number of leaves         :   23 (  45 expanded)
%              Depth                    :    8
%              Number of atoms          :   80 ( 226 expanded)
%              Number of equality atoms :   53 ( 191 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal term depth       :    2 (   1 average)

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

tff(f_40,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_54,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k1_tarski(B))
    <=> ( A = k1_xboole_0
        | A = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_zfmisc_1)).

tff(f_34,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

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

tff(c_44,plain,(
    ! [A_27,B_28] : r1_tarski(A_27,k2_xboole_0(A_27,B_28)) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_47,plain,(
    r1_tarski('#skF_3',k1_tarski('#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_44])).

tff(c_468,plain,(
    ! [B_60,A_61] :
      ( k1_tarski(B_60) = A_61
      | k1_xboole_0 = A_61
      | ~ r1_tarski(A_61,k1_tarski(B_60)) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_478,plain,
    ( k1_tarski('#skF_2') = '#skF_3'
    | k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_47,c_468])).

tff(c_488,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_43,c_38,c_478])).

tff(c_489,plain,(
    k1_tarski('#skF_2') != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_32])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( r2_hidden('#skF_1'(A_3,B_4),A_3)
      | r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_731,plain,(
    ! [A_84,B_85] :
      ( ~ r2_hidden('#skF_1'(A_84,B_85),B_85)
      | r1_tarski(A_84,B_85) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_738,plain,(
    ! [A_86] : r1_tarski(A_86,A_86) ),
    inference(resolution,[status(thm)],[c_8,c_731])).

tff(c_10,plain,(
    ! [A_8,B_9] :
      ( k2_xboole_0(A_8,B_9) = B_9
      | ~ r1_tarski(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_742,plain,(
    ! [A_86] : k2_xboole_0(A_86,A_86) = A_86 ),
    inference(resolution,[status(thm)],[c_738,c_10])).

tff(c_512,plain,(
    ! [B_67,A_68] : k2_xboole_0(B_67,A_68) = k2_xboole_0(A_68,B_67) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_12,plain,(
    ! [A_10,B_11] : r1_tarski(A_10,k2_xboole_0(A_10,B_11)) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_563,plain,(
    ! [A_69,B_70] : r1_tarski(A_69,k2_xboole_0(B_70,A_69)) ),
    inference(superposition,[status(thm),theory(equality)],[c_512,c_12])).

tff(c_572,plain,(
    r1_tarski('#skF_4',k1_tarski('#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_563])).

tff(c_490,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_32])).

tff(c_22,plain,(
    ! [B_23,A_22] :
      ( k1_tarski(B_23) = A_22
      | k1_xboole_0 = A_22
      | ~ r1_tarski(A_22,k1_tarski(B_23)) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_744,plain,(
    ! [B_87,A_88] :
      ( k1_tarski(B_87) = A_88
      | A_88 = '#skF_3'
      | ~ r1_tarski(A_88,k1_tarski(B_87)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_490,c_22])).

tff(c_751,plain,
    ( k1_tarski('#skF_2') = '#skF_4'
    | '#skF_3' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_572,c_744])).

tff(c_759,plain,(
    '#skF_3' = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_489,c_751])).

tff(c_554,plain,(
    k2_xboole_0('#skF_4','#skF_3') = k1_tarski('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_512])).

tff(c_764,plain,(
    k2_xboole_0('#skF_4','#skF_4') = k1_tarski('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_759,c_554])).

tff(c_823,plain,(
    k1_tarski('#skF_2') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_742,c_764])).

tff(c_824,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_489,c_823])).

tff(c_825,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_30])).

tff(c_826,plain,(
    k1_tarski('#skF_2') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_30])).

tff(c_34,plain,
    ( k1_tarski('#skF_2') != '#skF_4'
    | k1_tarski('#skF_2') != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_916,plain,(
    '#skF_3' != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_826,c_826,c_34])).

tff(c_864,plain,(
    ! [B_99,A_100] : k2_xboole_0(B_99,A_100) = k2_xboole_0(A_100,B_99) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_833,plain,(
    k2_xboole_0('#skF_3','#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_826,c_36])).

tff(c_885,plain,(
    k2_xboole_0('#skF_4','#skF_3') = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_864,c_833])).

tff(c_920,plain,(
    r1_tarski('#skF_4','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_885,c_12])).

tff(c_1296,plain,(
    ! [B_124,A_125] :
      ( k1_tarski(B_124) = A_125
      | k1_xboole_0 = A_125
      | ~ r1_tarski(A_125,k1_tarski(B_124)) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_1303,plain,(
    ! [A_125] :
      ( k1_tarski('#skF_2') = A_125
      | k1_xboole_0 = A_125
      | ~ r1_tarski(A_125,'#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_826,c_1296])).

tff(c_1312,plain,(
    ! [A_126] :
      ( A_126 = '#skF_3'
      | k1_xboole_0 = A_126
      | ~ r1_tarski(A_126,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_826,c_1303])).

tff(c_1319,plain,
    ( '#skF_3' = '#skF_4'
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_920,c_1312])).

tff(c_1330,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_825,c_916,c_1319])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:28:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.89/1.45  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.89/1.45  
% 2.89/1.45  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.89/1.45  %$ r2_hidden > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 2.89/1.45  
% 2.89/1.45  %Foreground sorts:
% 2.89/1.45  
% 2.89/1.45  
% 2.89/1.45  %Background operators:
% 2.89/1.45  
% 2.89/1.45  
% 2.89/1.45  %Foreground operators:
% 2.89/1.45  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.89/1.45  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.89/1.45  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.89/1.45  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.89/1.45  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.89/1.45  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.89/1.45  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.89/1.45  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.89/1.45  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.89/1.45  tff('#skF_2', type, '#skF_2': $i).
% 2.89/1.45  tff('#skF_3', type, '#skF_3': $i).
% 2.89/1.45  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.89/1.45  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.89/1.45  tff('#skF_4', type, '#skF_4': $i).
% 2.89/1.45  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.89/1.45  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.89/1.45  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.89/1.45  
% 2.89/1.47  tff(f_75, negated_conjecture, ~(![A, B, C]: ~((((k1_tarski(A) = k2_xboole_0(B, C)) & ~((B = k1_tarski(A)) & (C = k1_tarski(A)))) & ~((B = k1_xboole_0) & (C = k1_tarski(A)))) & ~((B = k1_tarski(A)) & (C = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_zfmisc_1)).
% 2.89/1.47  tff(f_40, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 2.89/1.47  tff(f_54, axiom, (![A, B]: (r1_tarski(A, k1_tarski(B)) <=> ((A = k1_xboole_0) | (A = k1_tarski(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_zfmisc_1)).
% 2.89/1.47  tff(f_34, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 2.89/1.47  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 2.89/1.47  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 2.89/1.47  tff(c_32, plain, (k1_tarski('#skF_2')!='#skF_4' | k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.89/1.47  tff(c_43, plain, (k1_xboole_0!='#skF_3'), inference(splitLeft, [status(thm)], [c_32])).
% 2.89/1.47  tff(c_30, plain, (k1_xboole_0!='#skF_4' | k1_tarski('#skF_2')!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.89/1.47  tff(c_38, plain, (k1_tarski('#skF_2')!='#skF_3'), inference(splitLeft, [status(thm)], [c_30])).
% 2.89/1.47  tff(c_36, plain, (k2_xboole_0('#skF_3', '#skF_4')=k1_tarski('#skF_2')), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.89/1.47  tff(c_44, plain, (![A_27, B_28]: (r1_tarski(A_27, k2_xboole_0(A_27, B_28)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.89/1.47  tff(c_47, plain, (r1_tarski('#skF_3', k1_tarski('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_36, c_44])).
% 2.89/1.47  tff(c_468, plain, (![B_60, A_61]: (k1_tarski(B_60)=A_61 | k1_xboole_0=A_61 | ~r1_tarski(A_61, k1_tarski(B_60)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.89/1.47  tff(c_478, plain, (k1_tarski('#skF_2')='#skF_3' | k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_47, c_468])).
% 2.89/1.47  tff(c_488, plain, $false, inference(negUnitSimplification, [status(thm)], [c_43, c_38, c_478])).
% 2.89/1.47  tff(c_489, plain, (k1_tarski('#skF_2')!='#skF_4'), inference(splitRight, [status(thm)], [c_32])).
% 2.89/1.47  tff(c_8, plain, (![A_3, B_4]: (r2_hidden('#skF_1'(A_3, B_4), A_3) | r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.89/1.47  tff(c_731, plain, (![A_84, B_85]: (~r2_hidden('#skF_1'(A_84, B_85), B_85) | r1_tarski(A_84, B_85))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.89/1.47  tff(c_738, plain, (![A_86]: (r1_tarski(A_86, A_86))), inference(resolution, [status(thm)], [c_8, c_731])).
% 2.89/1.47  tff(c_10, plain, (![A_8, B_9]: (k2_xboole_0(A_8, B_9)=B_9 | ~r1_tarski(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.89/1.47  tff(c_742, plain, (![A_86]: (k2_xboole_0(A_86, A_86)=A_86)), inference(resolution, [status(thm)], [c_738, c_10])).
% 2.89/1.47  tff(c_512, plain, (![B_67, A_68]: (k2_xboole_0(B_67, A_68)=k2_xboole_0(A_68, B_67))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.89/1.47  tff(c_12, plain, (![A_10, B_11]: (r1_tarski(A_10, k2_xboole_0(A_10, B_11)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.89/1.47  tff(c_563, plain, (![A_69, B_70]: (r1_tarski(A_69, k2_xboole_0(B_70, A_69)))), inference(superposition, [status(thm), theory('equality')], [c_512, c_12])).
% 2.89/1.47  tff(c_572, plain, (r1_tarski('#skF_4', k1_tarski('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_36, c_563])).
% 2.89/1.47  tff(c_490, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_32])).
% 2.89/1.47  tff(c_22, plain, (![B_23, A_22]: (k1_tarski(B_23)=A_22 | k1_xboole_0=A_22 | ~r1_tarski(A_22, k1_tarski(B_23)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.89/1.47  tff(c_744, plain, (![B_87, A_88]: (k1_tarski(B_87)=A_88 | A_88='#skF_3' | ~r1_tarski(A_88, k1_tarski(B_87)))), inference(demodulation, [status(thm), theory('equality')], [c_490, c_22])).
% 2.89/1.47  tff(c_751, plain, (k1_tarski('#skF_2')='#skF_4' | '#skF_3'='#skF_4'), inference(resolution, [status(thm)], [c_572, c_744])).
% 2.89/1.47  tff(c_759, plain, ('#skF_3'='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_489, c_751])).
% 2.89/1.47  tff(c_554, plain, (k2_xboole_0('#skF_4', '#skF_3')=k1_tarski('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_36, c_512])).
% 2.89/1.47  tff(c_764, plain, (k2_xboole_0('#skF_4', '#skF_4')=k1_tarski('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_759, c_554])).
% 2.89/1.47  tff(c_823, plain, (k1_tarski('#skF_2')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_742, c_764])).
% 2.89/1.47  tff(c_824, plain, $false, inference(negUnitSimplification, [status(thm)], [c_489, c_823])).
% 2.89/1.47  tff(c_825, plain, (k1_xboole_0!='#skF_4'), inference(splitRight, [status(thm)], [c_30])).
% 2.89/1.47  tff(c_826, plain, (k1_tarski('#skF_2')='#skF_3'), inference(splitRight, [status(thm)], [c_30])).
% 2.89/1.47  tff(c_34, plain, (k1_tarski('#skF_2')!='#skF_4' | k1_tarski('#skF_2')!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.89/1.47  tff(c_916, plain, ('#skF_3'!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_826, c_826, c_34])).
% 2.89/1.47  tff(c_864, plain, (![B_99, A_100]: (k2_xboole_0(B_99, A_100)=k2_xboole_0(A_100, B_99))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.89/1.47  tff(c_833, plain, (k2_xboole_0('#skF_3', '#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_826, c_36])).
% 2.89/1.47  tff(c_885, plain, (k2_xboole_0('#skF_4', '#skF_3')='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_864, c_833])).
% 2.89/1.47  tff(c_920, plain, (r1_tarski('#skF_4', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_885, c_12])).
% 2.89/1.47  tff(c_1296, plain, (![B_124, A_125]: (k1_tarski(B_124)=A_125 | k1_xboole_0=A_125 | ~r1_tarski(A_125, k1_tarski(B_124)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.89/1.47  tff(c_1303, plain, (![A_125]: (k1_tarski('#skF_2')=A_125 | k1_xboole_0=A_125 | ~r1_tarski(A_125, '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_826, c_1296])).
% 2.89/1.47  tff(c_1312, plain, (![A_126]: (A_126='#skF_3' | k1_xboole_0=A_126 | ~r1_tarski(A_126, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_826, c_1303])).
% 2.89/1.47  tff(c_1319, plain, ('#skF_3'='#skF_4' | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_920, c_1312])).
% 2.89/1.47  tff(c_1330, plain, $false, inference(negUnitSimplification, [status(thm)], [c_825, c_916, c_1319])).
% 2.89/1.47  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.89/1.47  
% 2.89/1.47  Inference rules
% 2.89/1.47  ----------------------
% 2.89/1.47  #Ref     : 0
% 2.89/1.47  #Sup     : 318
% 2.89/1.47  #Fact    : 0
% 2.89/1.47  #Define  : 0
% 2.89/1.47  #Split   : 3
% 2.89/1.47  #Chain   : 0
% 2.89/1.47  #Close   : 0
% 2.89/1.47  
% 2.89/1.47  Ordering : KBO
% 2.89/1.47  
% 2.89/1.47  Simplification rules
% 2.89/1.47  ----------------------
% 2.89/1.47  #Subsume      : 9
% 2.89/1.47  #Demod        : 188
% 2.89/1.47  #Tautology    : 264
% 2.89/1.47  #SimpNegUnit  : 5
% 2.89/1.47  #BackRed      : 18
% 2.89/1.47  
% 2.89/1.47  #Partial instantiations: 0
% 2.89/1.47  #Strategies tried      : 1
% 2.89/1.47  
% 2.89/1.47  Timing (in seconds)
% 2.89/1.47  ----------------------
% 2.89/1.47  Preprocessing        : 0.30
% 2.89/1.47  Parsing              : 0.16
% 2.89/1.47  CNF conversion       : 0.02
% 2.89/1.47  Main loop            : 0.38
% 2.89/1.47  Inferencing          : 0.14
% 2.89/1.47  Reduction            : 0.14
% 2.89/1.47  Demodulation         : 0.11
% 2.89/1.47  BG Simplification    : 0.02
% 2.89/1.47  Subsumption          : 0.05
% 2.89/1.47  Abstraction          : 0.02
% 2.89/1.47  MUC search           : 0.00
% 2.89/1.47  Cooper               : 0.00
% 2.89/1.47  Total                : 0.71
% 2.89/1.47  Index Insertion      : 0.00
% 2.89/1.47  Index Deletion       : 0.00
% 2.89/1.47  Index Matching       : 0.00
% 2.89/1.47  BG Taut test         : 0.00
%------------------------------------------------------------------------------
