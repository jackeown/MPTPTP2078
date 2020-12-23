%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:50:30 EST 2020

% Result     : Theorem 3.50s
% Output     : CNFRefutation 3.50s
% Verified   : 
% Statistics : Number of formulae       :   65 (  92 expanded)
%              Number of leaves         :   33 (  47 expanded)
%              Depth                    :   11
%              Number of atoms          :   77 ( 137 expanded)
%              Number of equality atoms :   38 (  88 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_1 > #skF_4 > #skF_7 > #skF_6 > #skF_5 > #skF_2 > #skF_8 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

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

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#skF_3',type,(
    '#skF_3': $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(f_98,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( k1_tarski(A) = k2_xboole_0(B,C)
          & B != C
          & B != k1_xboole_0
          & C != k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_zfmisc_1)).

tff(f_42,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_34,axiom,(
    ! [A,B,C] :
      ( C = k2_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            | r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).

tff(f_59,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_57,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

tff(f_48,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_77,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k1_tarski(B))
    <=> ( A = k1_xboole_0
        | A = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).

tff(f_85,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_tarski(A,B),C)
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_zfmisc_1)).

tff(f_46,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(c_76,plain,(
    '#skF_7' != '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_72,plain,(
    k1_xboole_0 != '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_20,plain,(
    ! [A_7] :
      ( r2_hidden('#skF_3'(A_7),A_7)
      | k1_xboole_0 = A_7 ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_78,plain,(
    k2_xboole_0('#skF_7','#skF_8') = k1_tarski('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_252,plain,(
    ! [D_82,B_83,A_84] :
      ( ~ r2_hidden(D_82,B_83)
      | r2_hidden(D_82,k2_xboole_0(A_84,B_83)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_267,plain,(
    ! [D_82] :
      ( ~ r2_hidden(D_82,'#skF_8')
      | r2_hidden(D_82,k1_tarski('#skF_6')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_78,c_252])).

tff(c_44,plain,(
    ! [A_19] : k2_tarski(A_19,A_19) = k1_tarski(A_19) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_350,plain,(
    ! [D_106,B_107,A_108] :
      ( D_106 = B_107
      | D_106 = A_108
      | ~ r2_hidden(D_106,k2_tarski(A_108,B_107)) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_430,plain,(
    ! [D_111,A_112] :
      ( D_111 = A_112
      | D_111 = A_112
      | ~ r2_hidden(D_111,k1_tarski(A_112)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_350])).

tff(c_483,plain,(
    ! [D_117] :
      ( D_117 = '#skF_6'
      | ~ r2_hidden(D_117,'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_267,c_430])).

tff(c_487,plain,
    ( '#skF_3'('#skF_8') = '#skF_6'
    | k1_xboole_0 = '#skF_8' ),
    inference(resolution,[status(thm)],[c_20,c_483])).

tff(c_490,plain,(
    '#skF_3'('#skF_8') = '#skF_6' ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_487])).

tff(c_494,plain,
    ( r2_hidden('#skF_6','#skF_8')
    | k1_xboole_0 = '#skF_8' ),
    inference(superposition,[status(thm),theory(equality)],[c_490,c_20])).

tff(c_497,plain,(
    r2_hidden('#skF_6','#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_494])).

tff(c_74,plain,(
    k1_xboole_0 != '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_93,plain,(
    ! [A_56,B_57] : r1_tarski(A_56,k2_xboole_0(A_56,B_57)) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_96,plain,(
    r1_tarski('#skF_7',k1_tarski('#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_78,c_93])).

tff(c_504,plain,(
    ! [B_118,A_119] :
      ( k1_tarski(B_118) = A_119
      | k1_xboole_0 = A_119
      | ~ r1_tarski(A_119,k1_tarski(B_118)) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_510,plain,
    ( k1_tarski('#skF_6') = '#skF_7'
    | k1_xboole_0 = '#skF_7' ),
    inference(resolution,[status(thm)],[c_96,c_504])).

tff(c_518,plain,(
    k1_tarski('#skF_6') = '#skF_7' ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_510])).

tff(c_825,plain,(
    ! [A_133,B_134,C_135] :
      ( r1_tarski(k2_tarski(A_133,B_134),C_135)
      | ~ r2_hidden(B_134,C_135)
      | ~ r2_hidden(A_133,C_135) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_1139,plain,(
    ! [A_152,C_153] :
      ( r1_tarski(k1_tarski(A_152),C_153)
      | ~ r2_hidden(A_152,C_153)
      | ~ r2_hidden(A_152,C_153) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_825])).

tff(c_22,plain,(
    ! [A_9,B_10] :
      ( k2_xboole_0(A_9,B_10) = B_10
      | ~ r1_tarski(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_1161,plain,(
    ! [A_154,C_155] :
      ( k2_xboole_0(k1_tarski(A_154),C_155) = C_155
      | ~ r2_hidden(A_154,C_155) ) ),
    inference(resolution,[status(thm)],[c_1139,c_22])).

tff(c_24,plain,(
    ! [A_11,B_12] : r1_tarski(A_11,k2_xboole_0(A_11,B_12)) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_1273,plain,(
    ! [A_156,C_157] :
      ( r1_tarski(k1_tarski(A_156),C_157)
      | ~ r2_hidden(A_156,C_157) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1161,c_24])).

tff(c_1326,plain,(
    ! [C_161] :
      ( r1_tarski('#skF_7',C_161)
      | ~ r2_hidden('#skF_6',C_161) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_518,c_1273])).

tff(c_1403,plain,(
    r1_tarski('#skF_7','#skF_8') ),
    inference(resolution,[status(thm)],[c_497,c_1326])).

tff(c_1422,plain,(
    k2_xboole_0('#skF_7','#skF_8') = '#skF_8' ),
    inference(resolution,[status(thm)],[c_1403,c_22])).

tff(c_525,plain,(
    k2_xboole_0('#skF_7','#skF_8') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_518,c_78])).

tff(c_1423,plain,(
    '#skF_7' = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1422,c_525])).

tff(c_1425,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_1423])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:00:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.50/1.82  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.50/1.83  
% 3.50/1.83  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.50/1.83  %$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_1 > #skF_4 > #skF_7 > #skF_6 > #skF_5 > #skF_2 > #skF_8 > #skF_3
% 3.50/1.83  
% 3.50/1.83  %Foreground sorts:
% 3.50/1.83  
% 3.50/1.83  
% 3.50/1.83  %Background operators:
% 3.50/1.83  
% 3.50/1.83  
% 3.50/1.83  %Foreground operators:
% 3.50/1.83  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 3.50/1.83  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.50/1.83  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.50/1.83  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.50/1.83  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.50/1.83  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.50/1.83  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 3.50/1.83  tff('#skF_7', type, '#skF_7': $i).
% 3.50/1.83  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.50/1.83  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.50/1.83  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.50/1.83  tff('#skF_6', type, '#skF_6': $i).
% 3.50/1.83  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 3.50/1.83  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.50/1.83  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 3.50/1.83  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.50/1.83  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.50/1.83  tff('#skF_8', type, '#skF_8': $i).
% 3.50/1.83  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.50/1.83  tff(k3_tarski, type, k3_tarski: $i > $i).
% 3.50/1.83  tff('#skF_3', type, '#skF_3': $i > $i).
% 3.50/1.83  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.50/1.83  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.50/1.83  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.50/1.83  
% 3.50/1.84  tff(f_98, negated_conjecture, ~(![A, B, C]: ~((((k1_tarski(A) = k2_xboole_0(B, C)) & ~(B = C)) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_zfmisc_1)).
% 3.50/1.84  tff(f_42, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 3.50/1.84  tff(f_34, axiom, (![A, B, C]: ((C = k2_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) | r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_xboole_0)).
% 3.50/1.84  tff(f_59, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 3.50/1.84  tff(f_57, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_tarski)).
% 3.50/1.84  tff(f_48, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 3.50/1.84  tff(f_77, axiom, (![A, B]: (r1_tarski(A, k1_tarski(B)) <=> ((A = k1_xboole_0) | (A = k1_tarski(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_zfmisc_1)).
% 3.50/1.84  tff(f_85, axiom, (![A, B, C]: (r1_tarski(k2_tarski(A, B), C) <=> (r2_hidden(A, C) & r2_hidden(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 3.50/1.84  tff(f_46, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 3.50/1.84  tff(c_76, plain, ('#skF_7'!='#skF_8'), inference(cnfTransformation, [status(thm)], [f_98])).
% 3.50/1.84  tff(c_72, plain, (k1_xboole_0!='#skF_8'), inference(cnfTransformation, [status(thm)], [f_98])).
% 3.50/1.84  tff(c_20, plain, (![A_7]: (r2_hidden('#skF_3'(A_7), A_7) | k1_xboole_0=A_7)), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.50/1.84  tff(c_78, plain, (k2_xboole_0('#skF_7', '#skF_8')=k1_tarski('#skF_6')), inference(cnfTransformation, [status(thm)], [f_98])).
% 3.50/1.84  tff(c_252, plain, (![D_82, B_83, A_84]: (~r2_hidden(D_82, B_83) | r2_hidden(D_82, k2_xboole_0(A_84, B_83)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.50/1.84  tff(c_267, plain, (![D_82]: (~r2_hidden(D_82, '#skF_8') | r2_hidden(D_82, k1_tarski('#skF_6')))), inference(superposition, [status(thm), theory('equality')], [c_78, c_252])).
% 3.50/1.84  tff(c_44, plain, (![A_19]: (k2_tarski(A_19, A_19)=k1_tarski(A_19))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.50/1.84  tff(c_350, plain, (![D_106, B_107, A_108]: (D_106=B_107 | D_106=A_108 | ~r2_hidden(D_106, k2_tarski(A_108, B_107)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.50/1.84  tff(c_430, plain, (![D_111, A_112]: (D_111=A_112 | D_111=A_112 | ~r2_hidden(D_111, k1_tarski(A_112)))), inference(superposition, [status(thm), theory('equality')], [c_44, c_350])).
% 3.50/1.84  tff(c_483, plain, (![D_117]: (D_117='#skF_6' | ~r2_hidden(D_117, '#skF_8'))), inference(resolution, [status(thm)], [c_267, c_430])).
% 3.50/1.84  tff(c_487, plain, ('#skF_3'('#skF_8')='#skF_6' | k1_xboole_0='#skF_8'), inference(resolution, [status(thm)], [c_20, c_483])).
% 3.50/1.84  tff(c_490, plain, ('#skF_3'('#skF_8')='#skF_6'), inference(negUnitSimplification, [status(thm)], [c_72, c_487])).
% 3.50/1.84  tff(c_494, plain, (r2_hidden('#skF_6', '#skF_8') | k1_xboole_0='#skF_8'), inference(superposition, [status(thm), theory('equality')], [c_490, c_20])).
% 3.50/1.84  tff(c_497, plain, (r2_hidden('#skF_6', '#skF_8')), inference(negUnitSimplification, [status(thm)], [c_72, c_494])).
% 3.50/1.84  tff(c_74, plain, (k1_xboole_0!='#skF_7'), inference(cnfTransformation, [status(thm)], [f_98])).
% 3.50/1.84  tff(c_93, plain, (![A_56, B_57]: (r1_tarski(A_56, k2_xboole_0(A_56, B_57)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.50/1.84  tff(c_96, plain, (r1_tarski('#skF_7', k1_tarski('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_78, c_93])).
% 3.50/1.84  tff(c_504, plain, (![B_118, A_119]: (k1_tarski(B_118)=A_119 | k1_xboole_0=A_119 | ~r1_tarski(A_119, k1_tarski(B_118)))), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.50/1.84  tff(c_510, plain, (k1_tarski('#skF_6')='#skF_7' | k1_xboole_0='#skF_7'), inference(resolution, [status(thm)], [c_96, c_504])).
% 3.50/1.84  tff(c_518, plain, (k1_tarski('#skF_6')='#skF_7'), inference(negUnitSimplification, [status(thm)], [c_74, c_510])).
% 3.50/1.84  tff(c_825, plain, (![A_133, B_134, C_135]: (r1_tarski(k2_tarski(A_133, B_134), C_135) | ~r2_hidden(B_134, C_135) | ~r2_hidden(A_133, C_135))), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.50/1.84  tff(c_1139, plain, (![A_152, C_153]: (r1_tarski(k1_tarski(A_152), C_153) | ~r2_hidden(A_152, C_153) | ~r2_hidden(A_152, C_153))), inference(superposition, [status(thm), theory('equality')], [c_44, c_825])).
% 3.50/1.84  tff(c_22, plain, (![A_9, B_10]: (k2_xboole_0(A_9, B_10)=B_10 | ~r1_tarski(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.50/1.84  tff(c_1161, plain, (![A_154, C_155]: (k2_xboole_0(k1_tarski(A_154), C_155)=C_155 | ~r2_hidden(A_154, C_155))), inference(resolution, [status(thm)], [c_1139, c_22])).
% 3.50/1.84  tff(c_24, plain, (![A_11, B_12]: (r1_tarski(A_11, k2_xboole_0(A_11, B_12)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.50/1.84  tff(c_1273, plain, (![A_156, C_157]: (r1_tarski(k1_tarski(A_156), C_157) | ~r2_hidden(A_156, C_157))), inference(superposition, [status(thm), theory('equality')], [c_1161, c_24])).
% 3.50/1.84  tff(c_1326, plain, (![C_161]: (r1_tarski('#skF_7', C_161) | ~r2_hidden('#skF_6', C_161))), inference(superposition, [status(thm), theory('equality')], [c_518, c_1273])).
% 3.50/1.84  tff(c_1403, plain, (r1_tarski('#skF_7', '#skF_8')), inference(resolution, [status(thm)], [c_497, c_1326])).
% 3.50/1.84  tff(c_1422, plain, (k2_xboole_0('#skF_7', '#skF_8')='#skF_8'), inference(resolution, [status(thm)], [c_1403, c_22])).
% 3.50/1.84  tff(c_525, plain, (k2_xboole_0('#skF_7', '#skF_8')='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_518, c_78])).
% 3.50/1.84  tff(c_1423, plain, ('#skF_7'='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_1422, c_525])).
% 3.50/1.84  tff(c_1425, plain, $false, inference(negUnitSimplification, [status(thm)], [c_76, c_1423])).
% 3.50/1.84  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.50/1.84  
% 3.50/1.84  Inference rules
% 3.50/1.84  ----------------------
% 3.50/1.84  #Ref     : 0
% 3.50/1.84  #Sup     : 315
% 3.50/1.84  #Fact    : 0
% 3.50/1.84  #Define  : 0
% 3.50/1.84  #Split   : 1
% 3.50/1.84  #Chain   : 0
% 3.50/1.84  #Close   : 0
% 3.50/1.84  
% 3.50/1.84  Ordering : KBO
% 3.50/1.84  
% 3.50/1.84  Simplification rules
% 3.50/1.84  ----------------------
% 3.50/1.84  #Subsume      : 22
% 3.50/1.84  #Demod        : 181
% 3.50/1.84  #Tautology    : 207
% 3.50/1.84  #SimpNegUnit  : 9
% 3.50/1.84  #BackRed      : 5
% 3.50/1.84  
% 3.50/1.84  #Partial instantiations: 0
% 3.50/1.84  #Strategies tried      : 1
% 3.50/1.84  
% 3.50/1.84  Timing (in seconds)
% 3.50/1.84  ----------------------
% 3.50/1.84  Preprocessing        : 0.53
% 3.50/1.84  Parsing              : 0.27
% 3.50/1.84  CNF conversion       : 0.04
% 3.50/1.84  Main loop            : 0.48
% 3.50/1.84  Inferencing          : 0.17
% 3.50/1.84  Reduction            : 0.16
% 3.50/1.84  Demodulation         : 0.12
% 3.50/1.84  BG Simplification    : 0.03
% 3.50/1.84  Subsumption          : 0.08
% 3.50/1.84  Abstraction          : 0.02
% 3.50/1.84  MUC search           : 0.00
% 3.50/1.84  Cooper               : 0.00
% 3.50/1.84  Total                : 1.04
% 3.50/1.85  Index Insertion      : 0.00
% 3.50/1.85  Index Deletion       : 0.00
% 3.50/1.85  Index Matching       : 0.00
% 3.50/1.85  BG Taut test         : 0.00
%------------------------------------------------------------------------------
