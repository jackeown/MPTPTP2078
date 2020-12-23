%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:58:59 EST 2020

% Result     : Theorem 2.57s
% Output     : CNFRefutation 2.57s
% Verified   : 
% Statistics : Number of formulae       :   60 (  71 expanded)
%              Number of leaves         :   37 (  43 expanded)
%              Depth                    :    7
%              Number of atoms          :   43 (  60 expanded)
%              Number of equality atoms :   24 (  36 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_tarski > #nlpp > k2_relat_1 > k1_tarski > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_6 > #skF_1 > #skF_3 > #skF_5 > #skF_8 > #skF_9 > #skF_2 > #skF_7 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

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

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': ( $i * $i ) > $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': ( $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_82,negated_conjecture,(
    ~ ( k1_relat_1(k1_xboole_0) = k1_xboole_0
      & k2_relat_1(k1_xboole_0) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_35,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_70,axiom,(
    ! [A,B] :
      ( B = k1_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(C,D),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_1)).

tff(f_39,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_37,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_60,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k4_xboole_0(B,k1_tarski(C)))
    <=> ( r2_hidden(A,B)
        & A != C ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_zfmisc_1)).

tff(f_78,axiom,(
    ! [A,B] :
      ( B = k2_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(D,C),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_relat_1)).

tff(c_56,plain,
    ( k2_relat_1(k1_xboole_0) != k1_xboole_0
    | k1_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_83,plain,(
    k1_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_56])).

tff(c_4,plain,(
    ! [A_3] :
      ( r2_hidden('#skF_1'(A_3),A_3)
      | k1_xboole_0 = A_3 ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_375,plain,(
    ! [C_136,A_137] :
      ( r2_hidden(k4_tarski(C_136,'#skF_5'(A_137,k1_relat_1(A_137),C_136)),A_137)
      | ~ r2_hidden(C_136,k1_relat_1(A_137)) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_8,plain,(
    ! [A_7] : k5_xboole_0(A_7,A_7) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_2,plain,(
    ! [A_1] : k3_xboole_0(A_1,A_1) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_116,plain,(
    ! [A_90,B_91] : k5_xboole_0(A_90,k3_xboole_0(A_90,B_91)) = k4_xboole_0(A_90,B_91) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_125,plain,(
    ! [A_1] : k5_xboole_0(A_1,A_1) = k4_xboole_0(A_1,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_116])).

tff(c_129,plain,(
    ! [A_92] : k4_xboole_0(A_92,A_92) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_125])).

tff(c_26,plain,(
    ! [C_38,B_37] : ~ r2_hidden(C_38,k4_xboole_0(B_37,k1_tarski(C_38))) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_134,plain,(
    ! [C_38] : ~ r2_hidden(C_38,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_129,c_26])).

tff(c_405,plain,(
    ! [C_140] : ~ r2_hidden(C_140,k1_relat_1(k1_xboole_0)) ),
    inference(resolution,[status(thm)],[c_375,c_134])).

tff(c_425,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_4,c_405])).

tff(c_434,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_83,c_425])).

tff(c_435,plain,(
    k2_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_655,plain,(
    ! [A_181,C_182] :
      ( r2_hidden(k4_tarski('#skF_9'(A_181,k2_relat_1(A_181),C_182),C_182),A_181)
      | ~ r2_hidden(C_182,k2_relat_1(A_181)) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_473,plain,(
    ! [A_147,B_148] : k5_xboole_0(A_147,k3_xboole_0(A_147,B_148)) = k4_xboole_0(A_147,B_148) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_482,plain,(
    ! [A_1] : k5_xboole_0(A_1,A_1) = k4_xboole_0(A_1,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_473])).

tff(c_486,plain,(
    ! [A_149] : k4_xboole_0(A_149,A_149) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_482])).

tff(c_491,plain,(
    ! [C_38] : ~ r2_hidden(C_38,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_486,c_26])).

tff(c_679,plain,(
    ! [C_183] : ~ r2_hidden(C_183,k2_relat_1(k1_xboole_0)) ),
    inference(resolution,[status(thm)],[c_655,c_491])).

tff(c_691,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_4,c_679])).

tff(c_697,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_435,c_691])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:23:39 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.57/1.35  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.57/1.35  
% 2.57/1.35  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.57/1.35  %$ r2_hidden > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_tarski > #nlpp > k2_relat_1 > k1_tarski > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_6 > #skF_1 > #skF_3 > #skF_5 > #skF_8 > #skF_9 > #skF_2 > #skF_7 > #skF_4
% 2.57/1.35  
% 2.57/1.35  %Foreground sorts:
% 2.57/1.35  
% 2.57/1.35  
% 2.57/1.35  %Background operators:
% 2.57/1.35  
% 2.57/1.35  
% 2.57/1.35  %Foreground operators:
% 2.57/1.35  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 2.57/1.35  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.57/1.35  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.57/1.35  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.57/1.35  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.57/1.35  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.57/1.35  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.57/1.35  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.57/1.35  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.57/1.35  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.57/1.35  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.57/1.35  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.57/1.35  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.57/1.35  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.57/1.35  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 2.57/1.35  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.57/1.35  tff('#skF_8', type, '#skF_8': ($i * $i) > $i).
% 2.57/1.35  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.57/1.35  tff('#skF_9', type, '#skF_9': ($i * $i * $i) > $i).
% 2.57/1.35  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.57/1.35  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.57/1.35  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.57/1.35  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.57/1.35  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.57/1.35  tff('#skF_7', type, '#skF_7': ($i * $i) > $i).
% 2.57/1.35  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.57/1.35  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.57/1.35  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 2.57/1.35  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.57/1.35  
% 2.57/1.37  tff(f_82, negated_conjecture, ~((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 2.57/1.37  tff(f_35, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 2.57/1.37  tff(f_70, axiom, (![A, B]: ((B = k1_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(C, D), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_relat_1)).
% 2.57/1.37  tff(f_39, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t92_xboole_1)).
% 2.57/1.37  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 2.57/1.37  tff(f_37, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 2.57/1.37  tff(f_60, axiom, (![A, B, C]: (r2_hidden(A, k4_xboole_0(B, k1_tarski(C))) <=> (r2_hidden(A, B) & ~(A = C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_zfmisc_1)).
% 2.57/1.37  tff(f_78, axiom, (![A, B]: ((B = k2_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(D, C), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_relat_1)).
% 2.57/1.37  tff(c_56, plain, (k2_relat_1(k1_xboole_0)!=k1_xboole_0 | k1_relat_1(k1_xboole_0)!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.57/1.37  tff(c_83, plain, (k1_relat_1(k1_xboole_0)!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_56])).
% 2.57/1.37  tff(c_4, plain, (![A_3]: (r2_hidden('#skF_1'(A_3), A_3) | k1_xboole_0=A_3)), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.57/1.37  tff(c_375, plain, (![C_136, A_137]: (r2_hidden(k4_tarski(C_136, '#skF_5'(A_137, k1_relat_1(A_137), C_136)), A_137) | ~r2_hidden(C_136, k1_relat_1(A_137)))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.57/1.37  tff(c_8, plain, (![A_7]: (k5_xboole_0(A_7, A_7)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.57/1.37  tff(c_2, plain, (![A_1]: (k3_xboole_0(A_1, A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.57/1.37  tff(c_116, plain, (![A_90, B_91]: (k5_xboole_0(A_90, k3_xboole_0(A_90, B_91))=k4_xboole_0(A_90, B_91))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.57/1.37  tff(c_125, plain, (![A_1]: (k5_xboole_0(A_1, A_1)=k4_xboole_0(A_1, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_116])).
% 2.57/1.37  tff(c_129, plain, (![A_92]: (k4_xboole_0(A_92, A_92)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_8, c_125])).
% 2.57/1.37  tff(c_26, plain, (![C_38, B_37]: (~r2_hidden(C_38, k4_xboole_0(B_37, k1_tarski(C_38))))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.57/1.37  tff(c_134, plain, (![C_38]: (~r2_hidden(C_38, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_129, c_26])).
% 2.57/1.37  tff(c_405, plain, (![C_140]: (~r2_hidden(C_140, k1_relat_1(k1_xboole_0)))), inference(resolution, [status(thm)], [c_375, c_134])).
% 2.57/1.37  tff(c_425, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_4, c_405])).
% 2.57/1.37  tff(c_434, plain, $false, inference(negUnitSimplification, [status(thm)], [c_83, c_425])).
% 2.57/1.37  tff(c_435, plain, (k2_relat_1(k1_xboole_0)!=k1_xboole_0), inference(splitRight, [status(thm)], [c_56])).
% 2.57/1.37  tff(c_655, plain, (![A_181, C_182]: (r2_hidden(k4_tarski('#skF_9'(A_181, k2_relat_1(A_181), C_182), C_182), A_181) | ~r2_hidden(C_182, k2_relat_1(A_181)))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.57/1.37  tff(c_473, plain, (![A_147, B_148]: (k5_xboole_0(A_147, k3_xboole_0(A_147, B_148))=k4_xboole_0(A_147, B_148))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.57/1.37  tff(c_482, plain, (![A_1]: (k5_xboole_0(A_1, A_1)=k4_xboole_0(A_1, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_473])).
% 2.57/1.37  tff(c_486, plain, (![A_149]: (k4_xboole_0(A_149, A_149)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_8, c_482])).
% 2.57/1.37  tff(c_491, plain, (![C_38]: (~r2_hidden(C_38, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_486, c_26])).
% 2.57/1.37  tff(c_679, plain, (![C_183]: (~r2_hidden(C_183, k2_relat_1(k1_xboole_0)))), inference(resolution, [status(thm)], [c_655, c_491])).
% 2.57/1.37  tff(c_691, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_4, c_679])).
% 2.57/1.37  tff(c_697, plain, $false, inference(negUnitSimplification, [status(thm)], [c_435, c_691])).
% 2.57/1.37  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.57/1.37  
% 2.57/1.37  Inference rules
% 2.57/1.37  ----------------------
% 2.57/1.37  #Ref     : 0
% 2.57/1.37  #Sup     : 133
% 2.57/1.37  #Fact    : 0
% 2.57/1.37  #Define  : 0
% 2.57/1.37  #Split   : 1
% 2.57/1.37  #Chain   : 0
% 2.57/1.37  #Close   : 0
% 2.57/1.37  
% 2.57/1.37  Ordering : KBO
% 2.57/1.37  
% 2.57/1.37  Simplification rules
% 2.57/1.37  ----------------------
% 2.57/1.37  #Subsume      : 13
% 2.57/1.37  #Demod        : 16
% 2.57/1.37  #Tautology    : 64
% 2.57/1.37  #SimpNegUnit  : 11
% 2.57/1.37  #BackRed      : 1
% 2.57/1.37  
% 2.57/1.37  #Partial instantiations: 0
% 2.57/1.37  #Strategies tried      : 1
% 2.57/1.37  
% 2.57/1.37  Timing (in seconds)
% 2.57/1.37  ----------------------
% 2.57/1.37  Preprocessing        : 0.33
% 2.57/1.37  Parsing              : 0.17
% 2.57/1.37  CNF conversion       : 0.03
% 2.57/1.37  Main loop            : 0.28
% 2.57/1.37  Inferencing          : 0.11
% 2.57/1.37  Reduction            : 0.08
% 2.57/1.37  Demodulation         : 0.05
% 2.57/1.37  BG Simplification    : 0.02
% 2.57/1.37  Subsumption          : 0.05
% 2.57/1.37  Abstraction          : 0.02
% 2.57/1.37  MUC search           : 0.00
% 2.57/1.37  Cooper               : 0.00
% 2.57/1.37  Total                : 0.64
% 2.57/1.37  Index Insertion      : 0.00
% 2.57/1.37  Index Deletion       : 0.00
% 2.57/1.37  Index Matching       : 0.00
% 2.57/1.37  BG Taut test         : 0.00
%------------------------------------------------------------------------------
