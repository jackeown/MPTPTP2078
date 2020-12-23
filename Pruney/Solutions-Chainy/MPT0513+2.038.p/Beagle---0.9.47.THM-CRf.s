%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:00:03 EST 2020

% Result     : Theorem 2.09s
% Output     : CNFRefutation 2.34s
% Verified   : 
% Statistics : Number of formulae       :   59 (  75 expanded)
%              Number of leaves         :   37 (  43 expanded)
%              Depth                    :    6
%              Number of atoms          :   47 (  75 expanded)
%              Number of equality atoms :   23 (  42 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k7_relat_1 > k5_xboole_0 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_tarski > #nlpp > k2_relat_1 > k1_tarski > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2

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

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

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

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_75,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_79,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k7_relat_1(A,k1_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_relat_1)).

tff(f_66,axiom,(
    ! [A] :
      ( v1_relat_1(A)
    <=> ! [B] :
          ~ ( r2_hidden(B,A)
            & ! [C,D] : B != k4_tarski(C,D) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_relat_1)).

tff(f_33,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_29,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_54,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k4_xboole_0(B,k1_tarski(C)))
    <=> ( r2_hidden(A,B)
        & A != C ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_zfmisc_1)).

tff(f_31,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_72,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r1_tarski(A,B)
       => k7_relat_1(k7_relat_1(C,A),B) = k7_relat_1(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t102_relat_1)).

tff(f_82,negated_conjecture,(
    ~ ! [A] : k7_relat_1(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t111_relat_1)).

tff(c_42,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_83,plain,(
    ! [A_69] :
      ( k7_relat_1(A_69,k1_relat_1(A_69)) = A_69
      | ~ v1_relat_1(A_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_92,plain,
    ( k7_relat_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_83])).

tff(c_95,plain,(
    ~ v1_relat_1(k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_92])).

tff(c_36,plain,(
    ! [A_40] :
      ( r2_hidden('#skF_1'(A_40),A_40)
      | v1_relat_1(A_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_8,plain,(
    ! [A_6] : k5_xboole_0(A_6,A_6) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_2,plain,(
    ! [A_1] : k3_xboole_0(A_1,A_1) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_128,plain,(
    ! [A_78,B_79] : k5_xboole_0(A_78,k3_xboole_0(A_78,B_79)) = k4_xboole_0(A_78,B_79) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_137,plain,(
    ! [A_1] : k5_xboole_0(A_1,A_1) = k4_xboole_0(A_1,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_128])).

tff(c_141,plain,(
    ! [A_80] : k4_xboole_0(A_80,A_80) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_137])).

tff(c_26,plain,(
    ! [C_37,B_36] : ~ r2_hidden(C_37,k4_xboole_0(B_36,k1_tarski(C_37))) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_151,plain,(
    ! [C_81] : ~ r2_hidden(C_81,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_141,c_26])).

tff(c_155,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_36,c_151])).

tff(c_159,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_95,c_155])).

tff(c_161,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_92])).

tff(c_6,plain,(
    ! [A_5] : r1_tarski(k1_xboole_0,A_5) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_160,plain,(
    k7_relat_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_92])).

tff(c_300,plain,(
    ! [C_112,A_113,B_114] :
      ( k7_relat_1(k7_relat_1(C_112,A_113),B_114) = k7_relat_1(C_112,A_113)
      | ~ r1_tarski(A_113,B_114)
      | ~ v1_relat_1(C_112) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_319,plain,(
    ! [B_114] :
      ( k7_relat_1(k1_xboole_0,k1_xboole_0) = k7_relat_1(k1_xboole_0,B_114)
      | ~ r1_tarski(k1_xboole_0,B_114)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_160,c_300])).

tff(c_331,plain,(
    ! [B_114] : k7_relat_1(k1_xboole_0,B_114) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_161,c_6,c_160,c_319])).

tff(c_46,plain,(
    k7_relat_1(k1_xboole_0,'#skF_4') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_336,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_331,c_46])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n003.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 16:39:42 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.09/1.30  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.34/1.31  
% 2.34/1.31  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.34/1.31  %$ r2_hidden > r1_tarski > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k7_relat_1 > k5_xboole_0 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_tarski > #nlpp > k2_relat_1 > k1_tarski > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2
% 2.34/1.31  
% 2.34/1.31  %Foreground sorts:
% 2.34/1.31  
% 2.34/1.31  
% 2.34/1.31  %Background operators:
% 2.34/1.31  
% 2.34/1.31  
% 2.34/1.31  %Foreground operators:
% 2.34/1.31  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.34/1.31  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.34/1.31  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.34/1.31  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.34/1.31  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.34/1.31  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.34/1.31  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.34/1.31  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.34/1.31  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.34/1.31  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.34/1.31  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.34/1.31  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.34/1.31  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.34/1.31  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.34/1.31  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.34/1.31  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.34/1.31  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.34/1.31  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.34/1.31  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.34/1.31  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.34/1.31  tff('#skF_4', type, '#skF_4': $i).
% 2.34/1.31  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.34/1.31  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.34/1.31  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.34/1.31  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.34/1.31  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.34/1.31  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.34/1.31  
% 2.34/1.32  tff(f_75, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 2.34/1.32  tff(f_79, axiom, (![A]: (v1_relat_1(A) => (k7_relat_1(A, k1_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_relat_1)).
% 2.34/1.32  tff(f_66, axiom, (![A]: (v1_relat_1(A) <=> (![B]: ~(r2_hidden(B, A) & (![C, D]: ~(B = k4_tarski(C, D))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_relat_1)).
% 2.34/1.32  tff(f_33, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t92_xboole_1)).
% 2.34/1.32  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 2.34/1.32  tff(f_29, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 2.34/1.32  tff(f_54, axiom, (![A, B, C]: (r2_hidden(A, k4_xboole_0(B, k1_tarski(C))) <=> (r2_hidden(A, B) & ~(A = C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_zfmisc_1)).
% 2.34/1.32  tff(f_31, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.34/1.32  tff(f_72, axiom, (![A, B, C]: (v1_relat_1(C) => (r1_tarski(A, B) => (k7_relat_1(k7_relat_1(C, A), B) = k7_relat_1(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t102_relat_1)).
% 2.34/1.32  tff(f_82, negated_conjecture, ~(![A]: (k7_relat_1(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t111_relat_1)).
% 2.34/1.32  tff(c_42, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.34/1.32  tff(c_83, plain, (![A_69]: (k7_relat_1(A_69, k1_relat_1(A_69))=A_69 | ~v1_relat_1(A_69))), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.34/1.32  tff(c_92, plain, (k7_relat_1(k1_xboole_0, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_42, c_83])).
% 2.34/1.32  tff(c_95, plain, (~v1_relat_1(k1_xboole_0)), inference(splitLeft, [status(thm)], [c_92])).
% 2.34/1.32  tff(c_36, plain, (![A_40]: (r2_hidden('#skF_1'(A_40), A_40) | v1_relat_1(A_40))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.34/1.32  tff(c_8, plain, (![A_6]: (k5_xboole_0(A_6, A_6)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.34/1.32  tff(c_2, plain, (![A_1]: (k3_xboole_0(A_1, A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.34/1.32  tff(c_128, plain, (![A_78, B_79]: (k5_xboole_0(A_78, k3_xboole_0(A_78, B_79))=k4_xboole_0(A_78, B_79))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.34/1.32  tff(c_137, plain, (![A_1]: (k5_xboole_0(A_1, A_1)=k4_xboole_0(A_1, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_128])).
% 2.34/1.32  tff(c_141, plain, (![A_80]: (k4_xboole_0(A_80, A_80)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_8, c_137])).
% 2.34/1.32  tff(c_26, plain, (![C_37, B_36]: (~r2_hidden(C_37, k4_xboole_0(B_36, k1_tarski(C_37))))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.34/1.32  tff(c_151, plain, (![C_81]: (~r2_hidden(C_81, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_141, c_26])).
% 2.34/1.32  tff(c_155, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_36, c_151])).
% 2.34/1.32  tff(c_159, plain, $false, inference(negUnitSimplification, [status(thm)], [c_95, c_155])).
% 2.34/1.32  tff(c_161, plain, (v1_relat_1(k1_xboole_0)), inference(splitRight, [status(thm)], [c_92])).
% 2.34/1.32  tff(c_6, plain, (![A_5]: (r1_tarski(k1_xboole_0, A_5))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.34/1.32  tff(c_160, plain, (k7_relat_1(k1_xboole_0, k1_xboole_0)=k1_xboole_0), inference(splitRight, [status(thm)], [c_92])).
% 2.34/1.32  tff(c_300, plain, (![C_112, A_113, B_114]: (k7_relat_1(k7_relat_1(C_112, A_113), B_114)=k7_relat_1(C_112, A_113) | ~r1_tarski(A_113, B_114) | ~v1_relat_1(C_112))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.34/1.32  tff(c_319, plain, (![B_114]: (k7_relat_1(k1_xboole_0, k1_xboole_0)=k7_relat_1(k1_xboole_0, B_114) | ~r1_tarski(k1_xboole_0, B_114) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_160, c_300])).
% 2.34/1.32  tff(c_331, plain, (![B_114]: (k7_relat_1(k1_xboole_0, B_114)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_161, c_6, c_160, c_319])).
% 2.34/1.32  tff(c_46, plain, (k7_relat_1(k1_xboole_0, '#skF_4')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.34/1.32  tff(c_336, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_331, c_46])).
% 2.34/1.32  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.34/1.32  
% 2.34/1.32  Inference rules
% 2.34/1.32  ----------------------
% 2.34/1.32  #Ref     : 0
% 2.34/1.32  #Sup     : 65
% 2.34/1.32  #Fact    : 0
% 2.34/1.32  #Define  : 0
% 2.34/1.32  #Split   : 1
% 2.34/1.32  #Chain   : 0
% 2.34/1.32  #Close   : 0
% 2.34/1.32  
% 2.34/1.32  Ordering : KBO
% 2.34/1.32  
% 2.34/1.32  Simplification rules
% 2.34/1.32  ----------------------
% 2.34/1.32  #Subsume      : 1
% 2.34/1.32  #Demod        : 12
% 2.34/1.32  #Tautology    : 47
% 2.34/1.32  #SimpNegUnit  : 2
% 2.34/1.32  #BackRed      : 1
% 2.34/1.32  
% 2.34/1.32  #Partial instantiations: 0
% 2.34/1.32  #Strategies tried      : 1
% 2.34/1.32  
% 2.34/1.32  Timing (in seconds)
% 2.34/1.32  ----------------------
% 2.34/1.32  Preprocessing        : 0.36
% 2.34/1.32  Parsing              : 0.19
% 2.34/1.32  CNF conversion       : 0.02
% 2.34/1.32  Main loop            : 0.18
% 2.34/1.32  Inferencing          : 0.07
% 2.34/1.32  Reduction            : 0.06
% 2.34/1.32  Demodulation         : 0.04
% 2.34/1.32  BG Simplification    : 0.02
% 2.34/1.32  Subsumption          : 0.02
% 2.34/1.32  Abstraction          : 0.01
% 2.34/1.32  MUC search           : 0.00
% 2.34/1.32  Cooper               : 0.00
% 2.34/1.32  Total                : 0.57
% 2.34/1.32  Index Insertion      : 0.00
% 2.34/1.32  Index Deletion       : 0.00
% 2.34/1.32  Index Matching       : 0.00
% 2.34/1.32  BG Taut test         : 0.00
%------------------------------------------------------------------------------
