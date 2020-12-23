%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:51:20 EST 2020

% Result     : Theorem 5.82s
% Output     : CNFRefutation 5.97s
% Verified   : 
% Statistics : Number of formulae       :   62 ( 127 expanded)
%              Number of leaves         :   33 (  58 expanded)
%              Depth                    :   11
%              Number of atoms          :   56 ( 141 expanded)
%              Number of equality atoms :   24 (  67 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2 > #skF_4

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

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

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

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(f_44,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_87,negated_conjecture,(
    ~ ! [A,B] : k2_xboole_0(k1_tarski(A),B) != k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_zfmisc_1)).

tff(f_58,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_83,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_50,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_40,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_69,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_67,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

tff(f_54,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_34,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k5_xboole_0(B,C))
    <=> ~ ( r2_hidden(A,B)
        <=> r2_hidden(A,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_0)).

tff(c_24,plain,(
    ! [A_10] : r1_tarski(k1_xboole_0,A_10) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_74,plain,(
    k2_xboole_0(k1_tarski('#skF_3'),'#skF_4') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_38,plain,(
    ! [B_23,A_22] : k2_tarski(B_23,A_22) = k2_tarski(A_22,B_23) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_287,plain,(
    ! [A_81,B_82] : k3_tarski(k2_tarski(A_81,B_82)) = k2_xboole_0(A_81,B_82) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_330,plain,(
    ! [B_85,A_86] : k3_tarski(k2_tarski(B_85,A_86)) = k2_xboole_0(A_86,B_85) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_287])).

tff(c_72,plain,(
    ! [A_58,B_59] : k3_tarski(k2_tarski(A_58,B_59)) = k2_xboole_0(A_58,B_59) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_356,plain,(
    ! [B_87,A_88] : k2_xboole_0(B_87,A_88) = k2_xboole_0(A_88,B_87) ),
    inference(superposition,[status(thm),theory(equality)],[c_330,c_72])).

tff(c_30,plain,(
    ! [A_14,B_15] : r1_tarski(A_14,k2_xboole_0(A_14,B_15)) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_407,plain,(
    ! [A_89,B_90] : r1_tarski(A_89,k2_xboole_0(B_90,A_89)) ),
    inference(superposition,[status(thm),theory(equality)],[c_356,c_30])).

tff(c_419,plain,(
    r1_tarski('#skF_4',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_74,c_407])).

tff(c_16,plain,(
    ! [B_7,A_6] :
      ( B_7 = A_6
      | ~ r1_tarski(B_7,A_6)
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_467,plain,
    ( k1_xboole_0 = '#skF_4'
    | ~ r1_tarski(k1_xboole_0,'#skF_4') ),
    inference(resolution,[status(thm)],[c_419,c_16])).

tff(c_470,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_467])).

tff(c_110,plain,(
    ! [A_68,B_69] : r1_tarski(A_68,k2_xboole_0(A_68,B_69)) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_113,plain,(
    r1_tarski(k1_tarski('#skF_3'),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_74,c_110])).

tff(c_423,plain,(
    ! [B_91,A_92] :
      ( B_91 = A_92
      | ~ r1_tarski(B_91,A_92)
      | ~ r1_tarski(A_92,B_91) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_429,plain,
    ( k1_tarski('#skF_3') = k1_xboole_0
    | ~ r1_tarski(k1_xboole_0,k1_tarski('#skF_3')) ),
    inference(resolution,[status(thm)],[c_113,c_423])).

tff(c_442,plain,(
    k1_tarski('#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_429])).

tff(c_114,plain,(
    ! [A_70] : k2_tarski(A_70,A_70) = k1_tarski(A_70) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_44,plain,(
    ! [D_29,B_25] : r2_hidden(D_29,k2_tarski(D_29,B_25)) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_120,plain,(
    ! [A_70] : r2_hidden(A_70,k1_tarski(A_70)) ),
    inference(superposition,[status(thm),theory(equality)],[c_114,c_44])).

tff(c_462,plain,(
    r2_hidden('#skF_3',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_442,c_120])).

tff(c_497,plain,(
    r2_hidden('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_470,c_462])).

tff(c_34,plain,(
    ! [A_19] : k5_xboole_0(A_19,A_19) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_500,plain,(
    ! [A_19] : k5_xboole_0(A_19,A_19) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_470,c_34])).

tff(c_2010,plain,(
    ! [A_142,C_143,B_144] :
      ( ~ r2_hidden(A_142,C_143)
      | ~ r2_hidden(A_142,B_144)
      | ~ r2_hidden(A_142,k5_xboole_0(B_144,C_143)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_5320,plain,(
    ! [A_5542,A_5543] :
      ( ~ r2_hidden(A_5542,A_5543)
      | ~ r2_hidden(A_5542,A_5543)
      | ~ r2_hidden(A_5542,'#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_500,c_2010])).

tff(c_5330,plain,(
    ~ r2_hidden('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_497,c_5320])).

tff(c_5344,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_497,c_5330])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.35  % Computer   : n025.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 09:29:50 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.82/2.15  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.82/2.16  
% 5.82/2.16  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.97/2.16  %$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2 > #skF_4
% 5.97/2.16  
% 5.97/2.16  %Foreground sorts:
% 5.97/2.16  
% 5.97/2.16  
% 5.97/2.16  %Background operators:
% 5.97/2.16  
% 5.97/2.16  
% 5.97/2.16  %Foreground operators:
% 5.97/2.16  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 5.97/2.16  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.97/2.16  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.97/2.16  tff(k1_tarski, type, k1_tarski: $i > $i).
% 5.97/2.16  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 5.97/2.16  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.97/2.16  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 5.97/2.16  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 5.97/2.16  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.97/2.16  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 5.97/2.16  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 5.97/2.16  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 5.97/2.16  tff('#skF_3', type, '#skF_3': $i).
% 5.97/2.16  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 5.97/2.16  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 5.97/2.16  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 5.97/2.16  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.97/2.16  tff(k3_tarski, type, k3_tarski: $i > $i).
% 5.97/2.16  tff('#skF_4', type, '#skF_4': $i).
% 5.97/2.16  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.97/2.16  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 5.97/2.16  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 5.97/2.16  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 5.97/2.16  
% 5.97/2.17  tff(f_44, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 5.97/2.17  tff(f_87, negated_conjecture, ~(![A, B]: ~(k2_xboole_0(k1_tarski(A), B) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_zfmisc_1)).
% 5.97/2.17  tff(f_58, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 5.97/2.17  tff(f_83, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 5.97/2.17  tff(f_50, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 5.97/2.17  tff(f_40, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 5.97/2.17  tff(f_69, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 5.97/2.17  tff(f_67, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_tarski)).
% 5.97/2.17  tff(f_54, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t92_xboole_1)).
% 5.97/2.17  tff(f_34, axiom, (![A, B, C]: (r2_hidden(A, k5_xboole_0(B, C)) <=> ~(r2_hidden(A, B) <=> r2_hidden(A, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_0)).
% 5.97/2.17  tff(c_24, plain, (![A_10]: (r1_tarski(k1_xboole_0, A_10))), inference(cnfTransformation, [status(thm)], [f_44])).
% 5.97/2.17  tff(c_74, plain, (k2_xboole_0(k1_tarski('#skF_3'), '#skF_4')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_87])).
% 5.97/2.17  tff(c_38, plain, (![B_23, A_22]: (k2_tarski(B_23, A_22)=k2_tarski(A_22, B_23))), inference(cnfTransformation, [status(thm)], [f_58])).
% 5.97/2.17  tff(c_287, plain, (![A_81, B_82]: (k3_tarski(k2_tarski(A_81, B_82))=k2_xboole_0(A_81, B_82))), inference(cnfTransformation, [status(thm)], [f_83])).
% 5.97/2.17  tff(c_330, plain, (![B_85, A_86]: (k3_tarski(k2_tarski(B_85, A_86))=k2_xboole_0(A_86, B_85))), inference(superposition, [status(thm), theory('equality')], [c_38, c_287])).
% 5.97/2.17  tff(c_72, plain, (![A_58, B_59]: (k3_tarski(k2_tarski(A_58, B_59))=k2_xboole_0(A_58, B_59))), inference(cnfTransformation, [status(thm)], [f_83])).
% 5.97/2.17  tff(c_356, plain, (![B_87, A_88]: (k2_xboole_0(B_87, A_88)=k2_xboole_0(A_88, B_87))), inference(superposition, [status(thm), theory('equality')], [c_330, c_72])).
% 5.97/2.17  tff(c_30, plain, (![A_14, B_15]: (r1_tarski(A_14, k2_xboole_0(A_14, B_15)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 5.97/2.17  tff(c_407, plain, (![A_89, B_90]: (r1_tarski(A_89, k2_xboole_0(B_90, A_89)))), inference(superposition, [status(thm), theory('equality')], [c_356, c_30])).
% 5.97/2.17  tff(c_419, plain, (r1_tarski('#skF_4', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_74, c_407])).
% 5.97/2.17  tff(c_16, plain, (![B_7, A_6]: (B_7=A_6 | ~r1_tarski(B_7, A_6) | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_40])).
% 5.97/2.17  tff(c_467, plain, (k1_xboole_0='#skF_4' | ~r1_tarski(k1_xboole_0, '#skF_4')), inference(resolution, [status(thm)], [c_419, c_16])).
% 5.97/2.17  tff(c_470, plain, (k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_24, c_467])).
% 5.97/2.17  tff(c_110, plain, (![A_68, B_69]: (r1_tarski(A_68, k2_xboole_0(A_68, B_69)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 5.97/2.17  tff(c_113, plain, (r1_tarski(k1_tarski('#skF_3'), k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_74, c_110])).
% 5.97/2.17  tff(c_423, plain, (![B_91, A_92]: (B_91=A_92 | ~r1_tarski(B_91, A_92) | ~r1_tarski(A_92, B_91))), inference(cnfTransformation, [status(thm)], [f_40])).
% 5.97/2.17  tff(c_429, plain, (k1_tarski('#skF_3')=k1_xboole_0 | ~r1_tarski(k1_xboole_0, k1_tarski('#skF_3'))), inference(resolution, [status(thm)], [c_113, c_423])).
% 5.97/2.17  tff(c_442, plain, (k1_tarski('#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_24, c_429])).
% 5.97/2.17  tff(c_114, plain, (![A_70]: (k2_tarski(A_70, A_70)=k1_tarski(A_70))), inference(cnfTransformation, [status(thm)], [f_69])).
% 5.97/2.17  tff(c_44, plain, (![D_29, B_25]: (r2_hidden(D_29, k2_tarski(D_29, B_25)))), inference(cnfTransformation, [status(thm)], [f_67])).
% 5.97/2.17  tff(c_120, plain, (![A_70]: (r2_hidden(A_70, k1_tarski(A_70)))), inference(superposition, [status(thm), theory('equality')], [c_114, c_44])).
% 5.97/2.17  tff(c_462, plain, (r2_hidden('#skF_3', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_442, c_120])).
% 5.97/2.17  tff(c_497, plain, (r2_hidden('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_470, c_462])).
% 5.97/2.17  tff(c_34, plain, (![A_19]: (k5_xboole_0(A_19, A_19)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_54])).
% 5.97/2.17  tff(c_500, plain, (![A_19]: (k5_xboole_0(A_19, A_19)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_470, c_34])).
% 5.97/2.17  tff(c_2010, plain, (![A_142, C_143, B_144]: (~r2_hidden(A_142, C_143) | ~r2_hidden(A_142, B_144) | ~r2_hidden(A_142, k5_xboole_0(B_144, C_143)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 5.97/2.17  tff(c_5320, plain, (![A_5542, A_5543]: (~r2_hidden(A_5542, A_5543) | ~r2_hidden(A_5542, A_5543) | ~r2_hidden(A_5542, '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_500, c_2010])).
% 5.97/2.17  tff(c_5330, plain, (~r2_hidden('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_497, c_5320])).
% 5.97/2.17  tff(c_5344, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_497, c_5330])).
% 5.97/2.17  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.97/2.17  
% 5.97/2.17  Inference rules
% 5.97/2.17  ----------------------
% 5.97/2.17  #Ref     : 0
% 5.97/2.17  #Sup     : 1200
% 5.97/2.17  #Fact    : 2
% 5.97/2.17  #Define  : 0
% 5.97/2.17  #Split   : 1
% 5.97/2.17  #Chain   : 0
% 5.97/2.17  #Close   : 0
% 5.97/2.17  
% 5.97/2.17  Ordering : KBO
% 5.97/2.17  
% 5.97/2.17  Simplification rules
% 5.97/2.17  ----------------------
% 5.97/2.17  #Subsume      : 60
% 5.97/2.17  #Demod        : 823
% 5.97/2.17  #Tautology    : 669
% 5.97/2.17  #SimpNegUnit  : 0
% 5.97/2.17  #BackRed      : 12
% 5.97/2.17  
% 5.97/2.17  #Partial instantiations: 1872
% 5.97/2.17  #Strategies tried      : 1
% 5.97/2.17  
% 5.97/2.17  Timing (in seconds)
% 5.97/2.17  ----------------------
% 5.97/2.17  Preprocessing        : 0.35
% 5.97/2.17  Parsing              : 0.18
% 5.97/2.17  CNF conversion       : 0.02
% 5.97/2.17  Main loop            : 1.06
% 5.97/2.17  Inferencing          : 0.38
% 5.97/2.17  Reduction            : 0.42
% 5.97/2.17  Demodulation         : 0.35
% 5.97/2.17  BG Simplification    : 0.04
% 5.97/2.17  Subsumption          : 0.16
% 5.97/2.17  Abstraction          : 0.04
% 5.97/2.17  MUC search           : 0.00
% 5.97/2.17  Cooper               : 0.00
% 5.97/2.17  Total                : 1.44
% 5.97/2.17  Index Insertion      : 0.00
% 5.97/2.17  Index Deletion       : 0.00
% 5.97/2.17  Index Matching       : 0.00
% 5.97/2.17  BG Taut test         : 0.00
%------------------------------------------------------------------------------
