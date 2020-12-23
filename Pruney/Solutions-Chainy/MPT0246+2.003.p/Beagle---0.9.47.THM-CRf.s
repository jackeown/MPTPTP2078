%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:50:00 EST 2020

% Result     : Theorem 3.28s
% Output     : CNFRefutation 3.28s
% Verified   : 
% Statistics : Number of formulae       :   64 ( 128 expanded)
%              Number of leaves         :   22 (  54 expanded)
%              Depth                    :   16
%              Number of atoms          :   98 ( 244 expanded)
%              Number of equality atoms :   34 ( 105 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_2',type,(
    '#skF_2': $i > $i )).

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

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_73,negated_conjecture,(
    ~ ! [A,B] :
        ~ ( A != k1_tarski(B)
          & A != k1_xboole_0
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & C != B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_zfmisc_1)).

tff(f_42,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_58,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_46,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_34,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(c_30,plain,(
    k1_tarski('#skF_4') != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_28,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_41,plain,(
    ! [A_28] :
      ( r2_hidden('#skF_2'(A_28),A_28)
      | k1_xboole_0 = A_28 ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_26,plain,(
    ! [C_25] :
      ( C_25 = '#skF_4'
      | ~ r2_hidden(C_25,'#skF_3') ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_45,plain,
    ( '#skF_2'('#skF_3') = '#skF_4'
    | k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_41,c_26])).

tff(c_48,plain,(
    '#skF_2'('#skF_3') = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_45])).

tff(c_10,plain,(
    ! [A_8] :
      ( r2_hidden('#skF_2'(A_8),A_8)
      | k1_xboole_0 = A_8 ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_85,plain,
    ( r2_hidden('#skF_4','#skF_3')
    | k1_xboole_0 = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_10])).

tff(c_88,plain,(
    r2_hidden('#skF_4','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_85])).

tff(c_24,plain,(
    ! [A_22,B_23] :
      ( r1_tarski(k1_tarski(A_22),B_23)
      | ~ r2_hidden(A_22,B_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_110,plain,(
    ! [A_37,B_38] :
      ( k3_xboole_0(A_37,B_38) = A_37
      | ~ r1_tarski(A_37,B_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_319,plain,(
    ! [A_64,B_65] :
      ( k3_xboole_0(k1_tarski(A_64),B_65) = k1_tarski(A_64)
      | ~ r2_hidden(A_64,B_65) ) ),
    inference(resolution,[status(thm)],[c_24,c_110])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_364,plain,(
    ! [B_66,A_67] :
      ( k3_xboole_0(B_66,k1_tarski(A_67)) = k1_tarski(A_67)
      | ~ r2_hidden(A_67,B_66) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_319,c_2])).

tff(c_115,plain,(
    ! [A_39,B_40] :
      ( r2_hidden('#skF_1'(A_39,B_40),A_39)
      | r1_tarski(A_39,B_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_121,plain,(
    ! [B_41] :
      ( '#skF_1'('#skF_3',B_41) = '#skF_4'
      | r1_tarski('#skF_3',B_41) ) ),
    inference(resolution,[status(thm)],[c_115,c_26])).

tff(c_12,plain,(
    ! [A_10,B_11] :
      ( k3_xboole_0(A_10,B_11) = A_10
      | ~ r1_tarski(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_125,plain,(
    ! [B_41] :
      ( k3_xboole_0('#skF_3',B_41) = '#skF_3'
      | '#skF_1'('#skF_3',B_41) = '#skF_4' ) ),
    inference(resolution,[status(thm)],[c_121,c_12])).

tff(c_375,plain,(
    ! [A_67] :
      ( k1_tarski(A_67) = '#skF_3'
      | '#skF_1'('#skF_3',k1_tarski(A_67)) = '#skF_4'
      | ~ r2_hidden(A_67,'#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_364,c_125])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( r2_hidden('#skF_1'(A_3,B_4),A_3)
      | r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_126,plain,(
    ! [A_42,B_43] :
      ( ~ r2_hidden('#skF_1'(A_42,B_43),B_43)
      | r1_tarski(A_42,B_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_141,plain,(
    ! [A_47] : r1_tarski(A_47,A_47) ),
    inference(resolution,[status(thm)],[c_8,c_126])).

tff(c_22,plain,(
    ! [A_22,B_23] :
      ( r2_hidden(A_22,B_23)
      | ~ r1_tarski(k1_tarski(A_22),B_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_150,plain,(
    ! [A_22] : r2_hidden(A_22,k1_tarski(A_22)) ),
    inference(resolution,[status(thm)],[c_141,c_22])).

tff(c_237,plain,(
    ! [C_52,B_53,A_54] :
      ( r2_hidden(C_52,B_53)
      | ~ r2_hidden(C_52,A_54)
      | ~ r1_tarski(A_54,B_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_417,plain,(
    ! [A_68,B_69,B_70] :
      ( r2_hidden('#skF_1'(A_68,B_69),B_70)
      | ~ r1_tarski(A_68,B_70)
      | r1_tarski(A_68,B_69) ) ),
    inference(resolution,[status(thm)],[c_8,c_237])).

tff(c_453,plain,(
    ! [A_74,B_75] :
      ( '#skF_1'(A_74,B_75) = '#skF_4'
      | ~ r1_tarski(A_74,'#skF_3')
      | r1_tarski(A_74,B_75) ) ),
    inference(resolution,[status(thm)],[c_417,c_26])).

tff(c_466,plain,(
    ! [A_76,B_77] :
      ( '#skF_1'(k1_tarski(A_76),B_77) = '#skF_4'
      | r1_tarski(k1_tarski(A_76),B_77)
      | ~ r2_hidden(A_76,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_24,c_453])).

tff(c_537,plain,(
    ! [A_86,B_87] :
      ( r2_hidden(A_86,B_87)
      | '#skF_1'(k1_tarski(A_86),B_87) = '#skF_4'
      | ~ r2_hidden(A_86,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_466,c_22])).

tff(c_6,plain,(
    ! [A_3,B_4] :
      ( ~ r2_hidden('#skF_1'(A_3,B_4),B_4)
      | r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_965,plain,(
    ! [B_117,A_118] :
      ( ~ r2_hidden('#skF_4',B_117)
      | r1_tarski(k1_tarski(A_118),B_117)
      | r2_hidden(A_118,B_117)
      | ~ r2_hidden(A_118,'#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_537,c_6])).

tff(c_1034,plain,(
    ! [B_123,A_124] :
      ( ~ r2_hidden('#skF_4',B_123)
      | r2_hidden(A_124,B_123)
      | ~ r2_hidden(A_124,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_965,c_22])).

tff(c_1051,plain,(
    ! [A_125] :
      ( r2_hidden(A_125,k1_tarski('#skF_4'))
      | ~ r2_hidden(A_125,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_150,c_1034])).

tff(c_1141,plain,(
    ! [A_131] :
      ( r1_tarski(A_131,k1_tarski('#skF_4'))
      | ~ r2_hidden('#skF_1'(A_131,k1_tarski('#skF_4')),'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_1051,c_6])).

tff(c_1157,plain,
    ( r1_tarski('#skF_3',k1_tarski('#skF_4'))
    | ~ r2_hidden('#skF_4','#skF_3')
    | k1_tarski('#skF_4') = '#skF_3'
    | ~ r2_hidden('#skF_4','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_375,c_1141])).

tff(c_1171,plain,
    ( r1_tarski('#skF_3',k1_tarski('#skF_4'))
    | k1_tarski('#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_88,c_1157])).

tff(c_1172,plain,(
    r1_tarski('#skF_3',k1_tarski('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_1171])).

tff(c_1204,plain,(
    k3_xboole_0('#skF_3',k1_tarski('#skF_4')) = '#skF_3' ),
    inference(resolution,[status(thm)],[c_1172,c_12])).

tff(c_333,plain,(
    ! [B_65,A_64] :
      ( k3_xboole_0(B_65,k1_tarski(A_64)) = k1_tarski(A_64)
      | ~ r2_hidden(A_64,B_65) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_319,c_2])).

tff(c_1209,plain,
    ( k1_tarski('#skF_4') = '#skF_3'
    | ~ r2_hidden('#skF_4','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1204,c_333])).

tff(c_1222,plain,(
    k1_tarski('#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_1209])).

tff(c_1224,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_1222])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:26:53 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.28/1.59  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.28/1.59  
% 3.28/1.59  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.28/1.60  %$ r2_hidden > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 3.28/1.60  
% 3.28/1.60  %Foreground sorts:
% 3.28/1.60  
% 3.28/1.60  
% 3.28/1.60  %Background operators:
% 3.28/1.60  
% 3.28/1.60  
% 3.28/1.60  %Foreground operators:
% 3.28/1.60  tff('#skF_2', type, '#skF_2': $i > $i).
% 3.28/1.60  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.28/1.60  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.28/1.60  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.28/1.60  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.28/1.60  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.28/1.60  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.28/1.60  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.28/1.60  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.28/1.60  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.28/1.60  tff('#skF_3', type, '#skF_3': $i).
% 3.28/1.60  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.28/1.60  tff('#skF_4', type, '#skF_4': $i).
% 3.28/1.60  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.28/1.60  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.28/1.60  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.28/1.60  
% 3.28/1.61  tff(f_73, negated_conjecture, ~(![A, B]: ~((~(A = k1_tarski(B)) & ~(A = k1_xboole_0)) & (![C]: ~(r2_hidden(C, A) & ~(C = B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_zfmisc_1)).
% 3.28/1.61  tff(f_42, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 3.28/1.61  tff(f_58, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 3.28/1.61  tff(f_46, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 3.28/1.61  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 3.28/1.61  tff(f_34, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 3.28/1.61  tff(c_30, plain, (k1_tarski('#skF_4')!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.28/1.61  tff(c_28, plain, (k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.28/1.61  tff(c_41, plain, (![A_28]: (r2_hidden('#skF_2'(A_28), A_28) | k1_xboole_0=A_28)), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.28/1.61  tff(c_26, plain, (![C_25]: (C_25='#skF_4' | ~r2_hidden(C_25, '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.28/1.61  tff(c_45, plain, ('#skF_2'('#skF_3')='#skF_4' | k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_41, c_26])).
% 3.28/1.61  tff(c_48, plain, ('#skF_2'('#skF_3')='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_28, c_45])).
% 3.28/1.61  tff(c_10, plain, (![A_8]: (r2_hidden('#skF_2'(A_8), A_8) | k1_xboole_0=A_8)), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.28/1.61  tff(c_85, plain, (r2_hidden('#skF_4', '#skF_3') | k1_xboole_0='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_48, c_10])).
% 3.28/1.61  tff(c_88, plain, (r2_hidden('#skF_4', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_28, c_85])).
% 3.28/1.61  tff(c_24, plain, (![A_22, B_23]: (r1_tarski(k1_tarski(A_22), B_23) | ~r2_hidden(A_22, B_23))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.28/1.61  tff(c_110, plain, (![A_37, B_38]: (k3_xboole_0(A_37, B_38)=A_37 | ~r1_tarski(A_37, B_38))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.28/1.61  tff(c_319, plain, (![A_64, B_65]: (k3_xboole_0(k1_tarski(A_64), B_65)=k1_tarski(A_64) | ~r2_hidden(A_64, B_65))), inference(resolution, [status(thm)], [c_24, c_110])).
% 3.28/1.61  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.28/1.61  tff(c_364, plain, (![B_66, A_67]: (k3_xboole_0(B_66, k1_tarski(A_67))=k1_tarski(A_67) | ~r2_hidden(A_67, B_66))), inference(superposition, [status(thm), theory('equality')], [c_319, c_2])).
% 3.28/1.61  tff(c_115, plain, (![A_39, B_40]: (r2_hidden('#skF_1'(A_39, B_40), A_39) | r1_tarski(A_39, B_40))), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.28/1.61  tff(c_121, plain, (![B_41]: ('#skF_1'('#skF_3', B_41)='#skF_4' | r1_tarski('#skF_3', B_41))), inference(resolution, [status(thm)], [c_115, c_26])).
% 3.28/1.61  tff(c_12, plain, (![A_10, B_11]: (k3_xboole_0(A_10, B_11)=A_10 | ~r1_tarski(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.28/1.61  tff(c_125, plain, (![B_41]: (k3_xboole_0('#skF_3', B_41)='#skF_3' | '#skF_1'('#skF_3', B_41)='#skF_4')), inference(resolution, [status(thm)], [c_121, c_12])).
% 3.28/1.61  tff(c_375, plain, (![A_67]: (k1_tarski(A_67)='#skF_3' | '#skF_1'('#skF_3', k1_tarski(A_67))='#skF_4' | ~r2_hidden(A_67, '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_364, c_125])).
% 3.28/1.61  tff(c_8, plain, (![A_3, B_4]: (r2_hidden('#skF_1'(A_3, B_4), A_3) | r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.28/1.61  tff(c_126, plain, (![A_42, B_43]: (~r2_hidden('#skF_1'(A_42, B_43), B_43) | r1_tarski(A_42, B_43))), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.28/1.61  tff(c_141, plain, (![A_47]: (r1_tarski(A_47, A_47))), inference(resolution, [status(thm)], [c_8, c_126])).
% 3.28/1.61  tff(c_22, plain, (![A_22, B_23]: (r2_hidden(A_22, B_23) | ~r1_tarski(k1_tarski(A_22), B_23))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.28/1.61  tff(c_150, plain, (![A_22]: (r2_hidden(A_22, k1_tarski(A_22)))), inference(resolution, [status(thm)], [c_141, c_22])).
% 3.28/1.61  tff(c_237, plain, (![C_52, B_53, A_54]: (r2_hidden(C_52, B_53) | ~r2_hidden(C_52, A_54) | ~r1_tarski(A_54, B_53))), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.28/1.61  tff(c_417, plain, (![A_68, B_69, B_70]: (r2_hidden('#skF_1'(A_68, B_69), B_70) | ~r1_tarski(A_68, B_70) | r1_tarski(A_68, B_69))), inference(resolution, [status(thm)], [c_8, c_237])).
% 3.28/1.61  tff(c_453, plain, (![A_74, B_75]: ('#skF_1'(A_74, B_75)='#skF_4' | ~r1_tarski(A_74, '#skF_3') | r1_tarski(A_74, B_75))), inference(resolution, [status(thm)], [c_417, c_26])).
% 3.28/1.61  tff(c_466, plain, (![A_76, B_77]: ('#skF_1'(k1_tarski(A_76), B_77)='#skF_4' | r1_tarski(k1_tarski(A_76), B_77) | ~r2_hidden(A_76, '#skF_3'))), inference(resolution, [status(thm)], [c_24, c_453])).
% 3.28/1.61  tff(c_537, plain, (![A_86, B_87]: (r2_hidden(A_86, B_87) | '#skF_1'(k1_tarski(A_86), B_87)='#skF_4' | ~r2_hidden(A_86, '#skF_3'))), inference(resolution, [status(thm)], [c_466, c_22])).
% 3.28/1.61  tff(c_6, plain, (![A_3, B_4]: (~r2_hidden('#skF_1'(A_3, B_4), B_4) | r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.28/1.61  tff(c_965, plain, (![B_117, A_118]: (~r2_hidden('#skF_4', B_117) | r1_tarski(k1_tarski(A_118), B_117) | r2_hidden(A_118, B_117) | ~r2_hidden(A_118, '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_537, c_6])).
% 3.28/1.61  tff(c_1034, plain, (![B_123, A_124]: (~r2_hidden('#skF_4', B_123) | r2_hidden(A_124, B_123) | ~r2_hidden(A_124, '#skF_3'))), inference(resolution, [status(thm)], [c_965, c_22])).
% 3.28/1.61  tff(c_1051, plain, (![A_125]: (r2_hidden(A_125, k1_tarski('#skF_4')) | ~r2_hidden(A_125, '#skF_3'))), inference(resolution, [status(thm)], [c_150, c_1034])).
% 3.28/1.61  tff(c_1141, plain, (![A_131]: (r1_tarski(A_131, k1_tarski('#skF_4')) | ~r2_hidden('#skF_1'(A_131, k1_tarski('#skF_4')), '#skF_3'))), inference(resolution, [status(thm)], [c_1051, c_6])).
% 3.28/1.61  tff(c_1157, plain, (r1_tarski('#skF_3', k1_tarski('#skF_4')) | ~r2_hidden('#skF_4', '#skF_3') | k1_tarski('#skF_4')='#skF_3' | ~r2_hidden('#skF_4', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_375, c_1141])).
% 3.28/1.61  tff(c_1171, plain, (r1_tarski('#skF_3', k1_tarski('#skF_4')) | k1_tarski('#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_88, c_88, c_1157])).
% 3.28/1.61  tff(c_1172, plain, (r1_tarski('#skF_3', k1_tarski('#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_30, c_1171])).
% 3.28/1.61  tff(c_1204, plain, (k3_xboole_0('#skF_3', k1_tarski('#skF_4'))='#skF_3'), inference(resolution, [status(thm)], [c_1172, c_12])).
% 3.28/1.61  tff(c_333, plain, (![B_65, A_64]: (k3_xboole_0(B_65, k1_tarski(A_64))=k1_tarski(A_64) | ~r2_hidden(A_64, B_65))), inference(superposition, [status(thm), theory('equality')], [c_319, c_2])).
% 3.28/1.61  tff(c_1209, plain, (k1_tarski('#skF_4')='#skF_3' | ~r2_hidden('#skF_4', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1204, c_333])).
% 3.28/1.61  tff(c_1222, plain, (k1_tarski('#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_88, c_1209])).
% 3.28/1.61  tff(c_1224, plain, $false, inference(negUnitSimplification, [status(thm)], [c_30, c_1222])).
% 3.28/1.61  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.28/1.61  
% 3.28/1.61  Inference rules
% 3.28/1.61  ----------------------
% 3.28/1.61  #Ref     : 0
% 3.28/1.61  #Sup     : 284
% 3.28/1.61  #Fact    : 0
% 3.28/1.61  #Define  : 0
% 3.28/1.61  #Split   : 0
% 3.28/1.61  #Chain   : 0
% 3.28/1.61  #Close   : 0
% 3.28/1.61  
% 3.28/1.61  Ordering : KBO
% 3.28/1.61  
% 3.28/1.61  Simplification rules
% 3.28/1.61  ----------------------
% 3.28/1.61  #Subsume      : 86
% 3.28/1.61  #Demod        : 36
% 3.28/1.61  #Tautology    : 74
% 3.28/1.61  #SimpNegUnit  : 12
% 3.28/1.61  #BackRed      : 0
% 3.28/1.61  
% 3.28/1.61  #Partial instantiations: 0
% 3.28/1.61  #Strategies tried      : 1
% 3.28/1.61  
% 3.28/1.61  Timing (in seconds)
% 3.28/1.61  ----------------------
% 3.28/1.61  Preprocessing        : 0.30
% 3.28/1.61  Parsing              : 0.16
% 3.28/1.61  CNF conversion       : 0.02
% 3.28/1.61  Main loop            : 0.54
% 3.28/1.61  Inferencing          : 0.20
% 3.28/1.61  Reduction            : 0.15
% 3.28/1.61  Demodulation         : 0.10
% 3.28/1.61  BG Simplification    : 0.02
% 3.28/1.61  Subsumption          : 0.13
% 3.28/1.61  Abstraction          : 0.02
% 3.28/1.61  MUC search           : 0.00
% 3.28/1.61  Cooper               : 0.00
% 3.28/1.61  Total                : 0.87
% 3.28/1.61  Index Insertion      : 0.00
% 3.28/1.61  Index Deletion       : 0.00
% 3.28/1.61  Index Matching       : 0.00
% 3.28/1.61  BG Taut test         : 0.00
%------------------------------------------------------------------------------
