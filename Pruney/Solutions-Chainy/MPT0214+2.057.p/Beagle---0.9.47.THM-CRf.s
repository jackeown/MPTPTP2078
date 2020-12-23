%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:47:37 EST 2020

% Result     : Theorem 2.17s
% Output     : CNFRefutation 2.17s
% Verified   : 
% Statistics : Number of formulae       :   57 (  87 expanded)
%              Number of leaves         :   31 (  44 expanded)
%              Depth                    :    6
%              Number of atoms          :   55 ( 115 expanded)
%              Number of equality atoms :   24 (  53 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_3 > #skF_5 > #skF_4 > #skF_2

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

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

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

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(f_76,negated_conjecture,(
    ~ ! [A,B] :
        ( r1_tarski(k1_tarski(A),k1_tarski(B))
       => A = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_zfmisc_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_71,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k1_tarski(B))
    <=> ( A = k1_xboole_0
        | A = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).

tff(f_44,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_33,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_42,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_40,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k5_xboole_0(B,C))
    <=> ~ ( r2_hidden(A,B)
        <=> r2_hidden(A,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_0)).

tff(c_56,plain,(
    '#skF_5' != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_26,plain,(
    ! [C_17] : r2_hidden(C_17,k1_tarski(C_17)) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_80,plain,(
    ! [B_53,A_54] :
      ( ~ r2_hidden(B_53,A_54)
      | ~ v1_xboole_0(A_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_84,plain,(
    ! [C_17] : ~ v1_xboole_0(k1_tarski(C_17)) ),
    inference(resolution,[status(thm)],[c_26,c_80])).

tff(c_101,plain,(
    ! [A_59] :
      ( v1_xboole_0(A_59)
      | r2_hidden('#skF_1'(A_59),A_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_24,plain,(
    ! [C_17,A_13] :
      ( C_17 = A_13
      | ~ r2_hidden(C_17,k1_tarski(A_13)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_105,plain,(
    ! [A_13] :
      ( '#skF_1'(k1_tarski(A_13)) = A_13
      | v1_xboole_0(k1_tarski(A_13)) ) ),
    inference(resolution,[status(thm)],[c_101,c_24])).

tff(c_111,plain,(
    ! [A_13] : '#skF_1'(k1_tarski(A_13)) = A_13 ),
    inference(negUnitSimplification,[status(thm)],[c_84,c_105])).

tff(c_58,plain,(
    r1_tarski(k1_tarski('#skF_4'),k1_tarski('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_148,plain,(
    ! [B_65,A_66] :
      ( k1_tarski(B_65) = A_66
      | k1_xboole_0 = A_66
      | ~ r1_tarski(A_66,k1_tarski(B_65)) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_158,plain,
    ( k1_tarski('#skF_5') = k1_tarski('#skF_4')
    | k1_tarski('#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_58,c_148])).

tff(c_172,plain,(
    k1_tarski('#skF_4') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_158])).

tff(c_197,plain,(
    r2_hidden('#skF_4',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_172,c_26])).

tff(c_22,plain,(
    ! [A_12] : k4_xboole_0(A_12,k1_xboole_0) = A_12 ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_6,plain,(
    ! [A_5] : k3_xboole_0(A_5,A_5) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_136,plain,(
    ! [A_63,B_64] : k5_xboole_0(A_63,k3_xboole_0(A_63,B_64)) = k4_xboole_0(A_63,B_64) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_145,plain,(
    ! [A_5] : k5_xboole_0(A_5,A_5) = k4_xboole_0(A_5,A_5) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_136])).

tff(c_246,plain,(
    ! [A_73,C_74,B_75] :
      ( ~ r2_hidden(A_73,C_74)
      | ~ r2_hidden(A_73,B_75)
      | ~ r2_hidden(A_73,k5_xboole_0(B_75,C_74)) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_354,plain,(
    ! [A_101,A_102] :
      ( ~ r2_hidden(A_101,A_102)
      | ~ r2_hidden(A_101,A_102)
      | ~ r2_hidden(A_101,k4_xboole_0(A_102,A_102)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_145,c_246])).

tff(c_369,plain,(
    ! [A_103] :
      ( ~ r2_hidden(A_103,k1_xboole_0)
      | ~ r2_hidden(A_103,k1_xboole_0)
      | ~ r2_hidden(A_103,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_354])).

tff(c_374,plain,(
    ~ r2_hidden('#skF_4',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_197,c_369])).

tff(c_382,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_197,c_374])).

tff(c_383,plain,(
    k1_tarski('#skF_5') = k1_tarski('#skF_4') ),
    inference(splitRight,[status(thm)],[c_158])).

tff(c_393,plain,(
    '#skF_1'(k1_tarski('#skF_4')) = '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_383,c_111])).

tff(c_413,plain,(
    '#skF_5' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_111,c_393])).

tff(c_415,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_413])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n014.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 18:26:52 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.17/1.29  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.17/1.29  
% 2.17/1.29  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.17/1.30  %$ r2_hidden > r1_tarski > v1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_3 > #skF_5 > #skF_4 > #skF_2
% 2.17/1.30  
% 2.17/1.30  %Foreground sorts:
% 2.17/1.30  
% 2.17/1.30  
% 2.17/1.30  %Background operators:
% 2.17/1.30  
% 2.17/1.30  
% 2.17/1.30  %Foreground operators:
% 2.17/1.30  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.17/1.30  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.17/1.30  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.17/1.30  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.17/1.30  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.17/1.30  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.17/1.30  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.17/1.30  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.17/1.30  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.17/1.30  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.17/1.30  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.17/1.30  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.17/1.30  tff('#skF_5', type, '#skF_5': $i).
% 2.17/1.30  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.17/1.30  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.17/1.30  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.17/1.30  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.17/1.30  tff('#skF_4', type, '#skF_4': $i).
% 2.17/1.30  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.17/1.30  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.17/1.30  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.17/1.30  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.17/1.30  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.17/1.30  
% 2.17/1.31  tff(f_76, negated_conjecture, ~(![A, B]: (r1_tarski(k1_tarski(A), k1_tarski(B)) => (A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_zfmisc_1)).
% 2.17/1.31  tff(f_51, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 2.17/1.31  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 2.17/1.31  tff(f_71, axiom, (![A, B]: (r1_tarski(A, k1_tarski(B)) <=> ((A = k1_xboole_0) | (A = k1_tarski(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_zfmisc_1)).
% 2.17/1.31  tff(f_44, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 2.17/1.31  tff(f_33, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 2.17/1.31  tff(f_42, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 2.17/1.31  tff(f_40, axiom, (![A, B, C]: (r2_hidden(A, k5_xboole_0(B, C)) <=> ~(r2_hidden(A, B) <=> r2_hidden(A, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_0)).
% 2.17/1.31  tff(c_56, plain, ('#skF_5'!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.17/1.31  tff(c_26, plain, (![C_17]: (r2_hidden(C_17, k1_tarski(C_17)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.17/1.31  tff(c_80, plain, (![B_53, A_54]: (~r2_hidden(B_53, A_54) | ~v1_xboole_0(A_54))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.17/1.31  tff(c_84, plain, (![C_17]: (~v1_xboole_0(k1_tarski(C_17)))), inference(resolution, [status(thm)], [c_26, c_80])).
% 2.17/1.31  tff(c_101, plain, (![A_59]: (v1_xboole_0(A_59) | r2_hidden('#skF_1'(A_59), A_59))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.17/1.31  tff(c_24, plain, (![C_17, A_13]: (C_17=A_13 | ~r2_hidden(C_17, k1_tarski(A_13)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.17/1.31  tff(c_105, plain, (![A_13]: ('#skF_1'(k1_tarski(A_13))=A_13 | v1_xboole_0(k1_tarski(A_13)))), inference(resolution, [status(thm)], [c_101, c_24])).
% 2.17/1.31  tff(c_111, plain, (![A_13]: ('#skF_1'(k1_tarski(A_13))=A_13)), inference(negUnitSimplification, [status(thm)], [c_84, c_105])).
% 2.17/1.31  tff(c_58, plain, (r1_tarski(k1_tarski('#skF_4'), k1_tarski('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.17/1.31  tff(c_148, plain, (![B_65, A_66]: (k1_tarski(B_65)=A_66 | k1_xboole_0=A_66 | ~r1_tarski(A_66, k1_tarski(B_65)))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.17/1.31  tff(c_158, plain, (k1_tarski('#skF_5')=k1_tarski('#skF_4') | k1_tarski('#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_58, c_148])).
% 2.17/1.31  tff(c_172, plain, (k1_tarski('#skF_4')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_158])).
% 2.17/1.31  tff(c_197, plain, (r2_hidden('#skF_4', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_172, c_26])).
% 2.17/1.31  tff(c_22, plain, (![A_12]: (k4_xboole_0(A_12, k1_xboole_0)=A_12)), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.17/1.31  tff(c_6, plain, (![A_5]: (k3_xboole_0(A_5, A_5)=A_5)), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.17/1.31  tff(c_136, plain, (![A_63, B_64]: (k5_xboole_0(A_63, k3_xboole_0(A_63, B_64))=k4_xboole_0(A_63, B_64))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.17/1.31  tff(c_145, plain, (![A_5]: (k5_xboole_0(A_5, A_5)=k4_xboole_0(A_5, A_5))), inference(superposition, [status(thm), theory('equality')], [c_6, c_136])).
% 2.17/1.31  tff(c_246, plain, (![A_73, C_74, B_75]: (~r2_hidden(A_73, C_74) | ~r2_hidden(A_73, B_75) | ~r2_hidden(A_73, k5_xboole_0(B_75, C_74)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.17/1.31  tff(c_354, plain, (![A_101, A_102]: (~r2_hidden(A_101, A_102) | ~r2_hidden(A_101, A_102) | ~r2_hidden(A_101, k4_xboole_0(A_102, A_102)))), inference(superposition, [status(thm), theory('equality')], [c_145, c_246])).
% 2.17/1.31  tff(c_369, plain, (![A_103]: (~r2_hidden(A_103, k1_xboole_0) | ~r2_hidden(A_103, k1_xboole_0) | ~r2_hidden(A_103, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_22, c_354])).
% 2.17/1.31  tff(c_374, plain, (~r2_hidden('#skF_4', k1_xboole_0)), inference(resolution, [status(thm)], [c_197, c_369])).
% 2.17/1.31  tff(c_382, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_197, c_374])).
% 2.17/1.31  tff(c_383, plain, (k1_tarski('#skF_5')=k1_tarski('#skF_4')), inference(splitRight, [status(thm)], [c_158])).
% 2.17/1.31  tff(c_393, plain, ('#skF_1'(k1_tarski('#skF_4'))='#skF_5'), inference(superposition, [status(thm), theory('equality')], [c_383, c_111])).
% 2.17/1.31  tff(c_413, plain, ('#skF_5'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_111, c_393])).
% 2.17/1.31  tff(c_415, plain, $false, inference(negUnitSimplification, [status(thm)], [c_56, c_413])).
% 2.17/1.31  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.17/1.31  
% 2.17/1.31  Inference rules
% 2.17/1.31  ----------------------
% 2.17/1.31  #Ref     : 0
% 2.17/1.31  #Sup     : 85
% 2.17/1.31  #Fact    : 0
% 2.17/1.31  #Define  : 0
% 2.17/1.31  #Split   : 1
% 2.17/1.31  #Chain   : 0
% 2.17/1.31  #Close   : 0
% 2.17/1.31  
% 2.17/1.31  Ordering : KBO
% 2.17/1.31  
% 2.17/1.31  Simplification rules
% 2.17/1.31  ----------------------
% 2.17/1.31  #Subsume      : 2
% 2.17/1.31  #Demod        : 14
% 2.17/1.31  #Tautology    : 46
% 2.17/1.31  #SimpNegUnit  : 5
% 2.17/1.31  #BackRed      : 2
% 2.17/1.31  
% 2.17/1.31  #Partial instantiations: 0
% 2.17/1.31  #Strategies tried      : 1
% 2.17/1.31  
% 2.17/1.31  Timing (in seconds)
% 2.17/1.31  ----------------------
% 2.17/1.31  Preprocessing        : 0.32
% 2.17/1.31  Parsing              : 0.16
% 2.17/1.31  CNF conversion       : 0.02
% 2.17/1.31  Main loop            : 0.23
% 2.17/1.31  Inferencing          : 0.08
% 2.17/1.31  Reduction            : 0.07
% 2.17/1.31  Demodulation         : 0.04
% 2.17/1.31  BG Simplification    : 0.02
% 2.17/1.31  Subsumption          : 0.04
% 2.17/1.31  Abstraction          : 0.01
% 2.17/1.31  MUC search           : 0.00
% 2.17/1.31  Cooper               : 0.00
% 2.17/1.31  Total                : 0.57
% 2.17/1.31  Index Insertion      : 0.00
% 2.17/1.31  Index Deletion       : 0.00
% 2.17/1.31  Index Matching       : 0.00
% 2.17/1.31  BG Taut test         : 0.00
%------------------------------------------------------------------------------
