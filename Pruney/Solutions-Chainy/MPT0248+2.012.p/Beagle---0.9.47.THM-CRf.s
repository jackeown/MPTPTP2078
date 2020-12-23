%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:50:05 EST 2020

% Result     : Theorem 2.72s
% Output     : CNFRefutation 2.72s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 137 expanded)
%              Number of leaves         :   26 (  57 expanded)
%              Depth                    :    9
%              Number of atoms          :   84 ( 251 expanded)
%              Number of equality atoms :   62 ( 220 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

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

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(f_76,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( k1_tarski(A) = k2_xboole_0(B,C)
          & ~ ( B = k1_tarski(A)
              & C = k1_tarski(A) )
          & ~ ( B = k1_xboole_0
              & C = k1_tarski(A) )
          & ~ ( B = k1_tarski(A)
              & C = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_zfmisc_1)).

tff(f_33,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k1_tarski(B))
    <=> ( A = k1_xboole_0
        | A = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).

tff(f_31,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_57,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(c_34,plain,
    ( k1_tarski('#skF_1') != '#skF_3'
    | k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_60,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_34])).

tff(c_32,plain,
    ( k1_xboole_0 != '#skF_3'
    | k1_tarski('#skF_1') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_40,plain,(
    k1_tarski('#skF_1') != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_32])).

tff(c_38,plain,(
    k2_xboole_0('#skF_2','#skF_3') = k1_tarski('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_6,plain,(
    ! [A_5,B_6] : r1_tarski(A_5,k2_xboole_0(A_5,B_6)) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_46,plain,(
    r1_tarski('#skF_2',k1_tarski('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_6])).

tff(c_403,plain,(
    ! [B_73,A_74] :
      ( k1_tarski(B_73) = A_74
      | k1_xboole_0 = A_74
      | ~ r1_tarski(A_74,k1_tarski(B_73)) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_413,plain,
    ( k1_tarski('#skF_1') = '#skF_2'
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_46,c_403])).

tff(c_427,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_40,c_413])).

tff(c_428,plain,(
    k1_tarski('#skF_1') != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_34])).

tff(c_4,plain,(
    ! [A_3,B_4] : r1_tarski(k3_xboole_0(A_3,B_4),A_3) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_479,plain,(
    ! [A_80,B_81] :
      ( k2_xboole_0(A_80,B_81) = B_81
      | ~ r1_tarski(A_80,B_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_494,plain,(
    ! [A_3,B_4] : k2_xboole_0(k3_xboole_0(A_3,B_4),A_3) = A_3 ),
    inference(resolution,[status(thm)],[c_4,c_479])).

tff(c_8,plain,(
    ! [B_8,A_7] : k2_tarski(B_8,A_7) = k2_tarski(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_522,plain,(
    ! [A_85,B_86] : k3_tarski(k2_tarski(A_85,B_86)) = k2_xboole_0(A_85,B_86) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_569,plain,(
    ! [B_89,A_90] : k3_tarski(k2_tarski(B_89,A_90)) = k2_xboole_0(A_90,B_89) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_522])).

tff(c_30,plain,(
    ! [A_39,B_40] : k3_tarski(k2_tarski(A_39,B_40)) = k2_xboole_0(A_39,B_40) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_604,plain,(
    ! [B_94,A_95] : k2_xboole_0(B_94,A_95) = k2_xboole_0(A_95,B_94) ),
    inference(superposition,[status(thm),theory(equality)],[c_569,c_30])).

tff(c_680,plain,(
    ! [B_96,A_97] : r1_tarski(B_96,k2_xboole_0(A_97,B_96)) ),
    inference(superposition,[status(thm),theory(equality)],[c_604,c_6])).

tff(c_713,plain,(
    ! [A_98] : r1_tarski(A_98,A_98) ),
    inference(superposition,[status(thm),theory(equality)],[c_494,c_680])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( k2_xboole_0(A_1,B_2) = B_2
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_717,plain,(
    ! [A_98] : k2_xboole_0(A_98,A_98) = A_98 ),
    inference(resolution,[status(thm)],[c_713,c_2])).

tff(c_627,plain,(
    k2_xboole_0('#skF_3','#skF_2') = k1_tarski('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_604,c_38])).

tff(c_672,plain,(
    r1_tarski('#skF_3',k1_tarski('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_627,c_6])).

tff(c_429,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_34])).

tff(c_24,plain,(
    ! [B_38,A_37] :
      ( k1_tarski(B_38) = A_37
      | k1_xboole_0 = A_37
      | ~ r1_tarski(A_37,k1_tarski(B_38)) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_719,plain,(
    ! [B_99,A_100] :
      ( k1_tarski(B_99) = A_100
      | A_100 = '#skF_2'
      | ~ r1_tarski(A_100,k1_tarski(B_99)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_429,c_24])).

tff(c_726,plain,
    ( k1_tarski('#skF_1') = '#skF_3'
    | '#skF_2' = '#skF_3' ),
    inference(resolution,[status(thm)],[c_672,c_719])).

tff(c_738,plain,(
    '#skF_2' = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_428,c_726])).

tff(c_630,plain,(
    k2_xboole_0('#skF_3','#skF_2') = k1_tarski('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_604,c_38])).

tff(c_775,plain,(
    k1_tarski('#skF_1') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_717,c_738,c_630])).

tff(c_776,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_428,c_775])).

tff(c_777,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_32])).

tff(c_778,plain,(
    k1_tarski('#skF_1') = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_32])).

tff(c_36,plain,
    ( k1_tarski('#skF_1') != '#skF_3'
    | k1_tarski('#skF_1') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_816,plain,(
    '#skF_2' != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_778,c_778,c_36])).

tff(c_883,plain,(
    ! [A_112,B_113] : k3_tarski(k2_tarski(A_112,B_113)) = k2_xboole_0(A_112,B_113) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_1012,plain,(
    ! [A_124,B_125] : k3_tarski(k2_tarski(A_124,B_125)) = k2_xboole_0(B_125,A_124) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_883])).

tff(c_1038,plain,(
    ! [B_126,A_127] : k2_xboole_0(B_126,A_127) = k2_xboole_0(A_127,B_126) ),
    inference(superposition,[status(thm),theory(equality)],[c_1012,c_30])).

tff(c_787,plain,(
    k2_xboole_0('#skF_2','#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_778,c_38])).

tff(c_1070,plain,(
    k2_xboole_0('#skF_3','#skF_2') = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_1038,c_787])).

tff(c_1126,plain,(
    r1_tarski('#skF_3','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_1070,c_6])).

tff(c_1139,plain,(
    ! [B_128,A_129] :
      ( k1_tarski(B_128) = A_129
      | k1_xboole_0 = A_129
      | ~ r1_tarski(A_129,k1_tarski(B_128)) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_1149,plain,(
    ! [A_129] :
      ( k1_tarski('#skF_1') = A_129
      | k1_xboole_0 = A_129
      | ~ r1_tarski(A_129,'#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_778,c_1139])).

tff(c_1212,plain,(
    ! [A_132] :
      ( A_132 = '#skF_2'
      | k1_xboole_0 = A_132
      | ~ r1_tarski(A_132,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_778,c_1149])).

tff(c_1215,plain,
    ( '#skF_2' = '#skF_3'
    | k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_1126,c_1212])).

tff(c_1229,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_777,c_816,c_1215])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:00:51 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.72/1.44  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.72/1.45  
% 2.72/1.45  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.72/1.45  %$ r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.72/1.45  
% 2.72/1.45  %Foreground sorts:
% 2.72/1.45  
% 2.72/1.45  
% 2.72/1.45  %Background operators:
% 2.72/1.45  
% 2.72/1.45  
% 2.72/1.45  %Foreground operators:
% 2.72/1.45  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.72/1.45  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.72/1.45  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.72/1.45  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.72/1.45  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.72/1.45  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.72/1.45  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.72/1.45  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.72/1.45  tff('#skF_2', type, '#skF_2': $i).
% 2.72/1.45  tff('#skF_3', type, '#skF_3': $i).
% 2.72/1.45  tff('#skF_1', type, '#skF_1': $i).
% 2.72/1.45  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.72/1.45  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.72/1.45  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.72/1.45  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.72/1.45  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.72/1.45  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.72/1.45  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.72/1.45  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.72/1.45  
% 2.72/1.47  tff(f_76, negated_conjecture, ~(![A, B, C]: ~((((k1_tarski(A) = k2_xboole_0(B, C)) & ~((B = k1_tarski(A)) & (C = k1_tarski(A)))) & ~((B = k1_xboole_0) & (C = k1_tarski(A)))) & ~((B = k1_tarski(A)) & (C = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_zfmisc_1)).
% 2.72/1.47  tff(f_33, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 2.72/1.47  tff(f_55, axiom, (![A, B]: (r1_tarski(A, k1_tarski(B)) <=> ((A = k1_xboole_0) | (A = k1_tarski(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_zfmisc_1)).
% 2.72/1.47  tff(f_31, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 2.72/1.47  tff(f_29, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 2.72/1.47  tff(f_35, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 2.72/1.47  tff(f_57, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 2.72/1.47  tff(c_34, plain, (k1_tarski('#skF_1')!='#skF_3' | k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.72/1.47  tff(c_60, plain, (k1_xboole_0!='#skF_2'), inference(splitLeft, [status(thm)], [c_34])).
% 2.72/1.47  tff(c_32, plain, (k1_xboole_0!='#skF_3' | k1_tarski('#skF_1')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.72/1.47  tff(c_40, plain, (k1_tarski('#skF_1')!='#skF_2'), inference(splitLeft, [status(thm)], [c_32])).
% 2.72/1.47  tff(c_38, plain, (k2_xboole_0('#skF_2', '#skF_3')=k1_tarski('#skF_1')), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.72/1.47  tff(c_6, plain, (![A_5, B_6]: (r1_tarski(A_5, k2_xboole_0(A_5, B_6)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.72/1.47  tff(c_46, plain, (r1_tarski('#skF_2', k1_tarski('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_38, c_6])).
% 2.72/1.47  tff(c_403, plain, (![B_73, A_74]: (k1_tarski(B_73)=A_74 | k1_xboole_0=A_74 | ~r1_tarski(A_74, k1_tarski(B_73)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.72/1.47  tff(c_413, plain, (k1_tarski('#skF_1')='#skF_2' | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_46, c_403])).
% 2.72/1.47  tff(c_427, plain, $false, inference(negUnitSimplification, [status(thm)], [c_60, c_40, c_413])).
% 2.72/1.47  tff(c_428, plain, (k1_tarski('#skF_1')!='#skF_3'), inference(splitRight, [status(thm)], [c_34])).
% 2.72/1.47  tff(c_4, plain, (![A_3, B_4]: (r1_tarski(k3_xboole_0(A_3, B_4), A_3))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.72/1.47  tff(c_479, plain, (![A_80, B_81]: (k2_xboole_0(A_80, B_81)=B_81 | ~r1_tarski(A_80, B_81))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.72/1.47  tff(c_494, plain, (![A_3, B_4]: (k2_xboole_0(k3_xboole_0(A_3, B_4), A_3)=A_3)), inference(resolution, [status(thm)], [c_4, c_479])).
% 2.72/1.47  tff(c_8, plain, (![B_8, A_7]: (k2_tarski(B_8, A_7)=k2_tarski(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.72/1.47  tff(c_522, plain, (![A_85, B_86]: (k3_tarski(k2_tarski(A_85, B_86))=k2_xboole_0(A_85, B_86))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.72/1.47  tff(c_569, plain, (![B_89, A_90]: (k3_tarski(k2_tarski(B_89, A_90))=k2_xboole_0(A_90, B_89))), inference(superposition, [status(thm), theory('equality')], [c_8, c_522])).
% 2.72/1.47  tff(c_30, plain, (![A_39, B_40]: (k3_tarski(k2_tarski(A_39, B_40))=k2_xboole_0(A_39, B_40))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.72/1.47  tff(c_604, plain, (![B_94, A_95]: (k2_xboole_0(B_94, A_95)=k2_xboole_0(A_95, B_94))), inference(superposition, [status(thm), theory('equality')], [c_569, c_30])).
% 2.72/1.47  tff(c_680, plain, (![B_96, A_97]: (r1_tarski(B_96, k2_xboole_0(A_97, B_96)))), inference(superposition, [status(thm), theory('equality')], [c_604, c_6])).
% 2.72/1.47  tff(c_713, plain, (![A_98]: (r1_tarski(A_98, A_98))), inference(superposition, [status(thm), theory('equality')], [c_494, c_680])).
% 2.72/1.47  tff(c_2, plain, (![A_1, B_2]: (k2_xboole_0(A_1, B_2)=B_2 | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.72/1.47  tff(c_717, plain, (![A_98]: (k2_xboole_0(A_98, A_98)=A_98)), inference(resolution, [status(thm)], [c_713, c_2])).
% 2.72/1.47  tff(c_627, plain, (k2_xboole_0('#skF_3', '#skF_2')=k1_tarski('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_604, c_38])).
% 2.72/1.47  tff(c_672, plain, (r1_tarski('#skF_3', k1_tarski('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_627, c_6])).
% 2.72/1.47  tff(c_429, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_34])).
% 2.72/1.47  tff(c_24, plain, (![B_38, A_37]: (k1_tarski(B_38)=A_37 | k1_xboole_0=A_37 | ~r1_tarski(A_37, k1_tarski(B_38)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.72/1.47  tff(c_719, plain, (![B_99, A_100]: (k1_tarski(B_99)=A_100 | A_100='#skF_2' | ~r1_tarski(A_100, k1_tarski(B_99)))), inference(demodulation, [status(thm), theory('equality')], [c_429, c_24])).
% 2.72/1.47  tff(c_726, plain, (k1_tarski('#skF_1')='#skF_3' | '#skF_2'='#skF_3'), inference(resolution, [status(thm)], [c_672, c_719])).
% 2.72/1.47  tff(c_738, plain, ('#skF_2'='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_428, c_726])).
% 2.72/1.47  tff(c_630, plain, (k2_xboole_0('#skF_3', '#skF_2')=k1_tarski('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_604, c_38])).
% 2.72/1.47  tff(c_775, plain, (k1_tarski('#skF_1')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_717, c_738, c_630])).
% 2.72/1.47  tff(c_776, plain, $false, inference(negUnitSimplification, [status(thm)], [c_428, c_775])).
% 2.72/1.47  tff(c_777, plain, (k1_xboole_0!='#skF_3'), inference(splitRight, [status(thm)], [c_32])).
% 2.72/1.47  tff(c_778, plain, (k1_tarski('#skF_1')='#skF_2'), inference(splitRight, [status(thm)], [c_32])).
% 2.72/1.47  tff(c_36, plain, (k1_tarski('#skF_1')!='#skF_3' | k1_tarski('#skF_1')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.72/1.47  tff(c_816, plain, ('#skF_2'!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_778, c_778, c_36])).
% 2.72/1.47  tff(c_883, plain, (![A_112, B_113]: (k3_tarski(k2_tarski(A_112, B_113))=k2_xboole_0(A_112, B_113))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.72/1.47  tff(c_1012, plain, (![A_124, B_125]: (k3_tarski(k2_tarski(A_124, B_125))=k2_xboole_0(B_125, A_124))), inference(superposition, [status(thm), theory('equality')], [c_8, c_883])).
% 2.72/1.47  tff(c_1038, plain, (![B_126, A_127]: (k2_xboole_0(B_126, A_127)=k2_xboole_0(A_127, B_126))), inference(superposition, [status(thm), theory('equality')], [c_1012, c_30])).
% 2.72/1.47  tff(c_787, plain, (k2_xboole_0('#skF_2', '#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_778, c_38])).
% 2.72/1.47  tff(c_1070, plain, (k2_xboole_0('#skF_3', '#skF_2')='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_1038, c_787])).
% 2.72/1.47  tff(c_1126, plain, (r1_tarski('#skF_3', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_1070, c_6])).
% 2.72/1.47  tff(c_1139, plain, (![B_128, A_129]: (k1_tarski(B_128)=A_129 | k1_xboole_0=A_129 | ~r1_tarski(A_129, k1_tarski(B_128)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.72/1.47  tff(c_1149, plain, (![A_129]: (k1_tarski('#skF_1')=A_129 | k1_xboole_0=A_129 | ~r1_tarski(A_129, '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_778, c_1139])).
% 2.72/1.47  tff(c_1212, plain, (![A_132]: (A_132='#skF_2' | k1_xboole_0=A_132 | ~r1_tarski(A_132, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_778, c_1149])).
% 2.72/1.47  tff(c_1215, plain, ('#skF_2'='#skF_3' | k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_1126, c_1212])).
% 2.72/1.47  tff(c_1229, plain, $false, inference(negUnitSimplification, [status(thm)], [c_777, c_816, c_1215])).
% 2.72/1.47  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.72/1.47  
% 2.72/1.47  Inference rules
% 2.72/1.47  ----------------------
% 2.72/1.47  #Ref     : 0
% 2.72/1.47  #Sup     : 302
% 2.72/1.47  #Fact    : 0
% 2.72/1.47  #Define  : 0
% 2.72/1.47  #Split   : 3
% 2.72/1.47  #Chain   : 0
% 2.72/1.47  #Close   : 0
% 2.72/1.47  
% 2.72/1.47  Ordering : KBO
% 2.72/1.47  
% 2.72/1.47  Simplification rules
% 2.72/1.47  ----------------------
% 2.72/1.47  #Subsume      : 6
% 2.72/1.47  #Demod        : 90
% 2.72/1.47  #Tautology    : 211
% 2.72/1.47  #SimpNegUnit  : 4
% 2.72/1.47  #BackRed      : 11
% 2.72/1.47  
% 2.72/1.47  #Partial instantiations: 0
% 2.72/1.47  #Strategies tried      : 1
% 2.72/1.47  
% 2.72/1.47  Timing (in seconds)
% 2.72/1.47  ----------------------
% 3.05/1.47  Preprocessing        : 0.34
% 3.05/1.47  Parsing              : 0.18
% 3.05/1.47  CNF conversion       : 0.02
% 3.05/1.47  Main loop            : 0.35
% 3.05/1.47  Inferencing          : 0.13
% 3.05/1.47  Reduction            : 0.12
% 3.05/1.47  Demodulation         : 0.09
% 3.05/1.47  BG Simplification    : 0.02
% 3.05/1.47  Subsumption          : 0.05
% 3.05/1.47  Abstraction          : 0.02
% 3.05/1.47  MUC search           : 0.00
% 3.05/1.47  Cooper               : 0.00
% 3.05/1.47  Total                : 0.72
% 3.05/1.47  Index Insertion      : 0.00
% 3.05/1.47  Index Deletion       : 0.00
% 3.05/1.47  Index Matching       : 0.00
% 3.05/1.47  BG Taut test         : 0.00
%------------------------------------------------------------------------------
