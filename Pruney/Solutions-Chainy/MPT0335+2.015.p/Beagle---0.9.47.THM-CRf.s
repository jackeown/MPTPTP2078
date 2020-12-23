%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:54:55 EST 2020

% Result     : Theorem 6.30s
% Output     : CNFRefutation 6.55s
% Verified   : 
% Statistics : Number of formulae       :   60 (  74 expanded)
%              Number of leaves         :   28 (  37 expanded)
%              Depth                    :   11
%              Number of atoms          :   53 (  78 expanded)
%              Number of equality atoms :   39 (  56 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_68,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( r1_tarski(A,B)
          & k3_xboole_0(B,C) = k1_tarski(D)
          & r2_hidden(D,A) )
       => k3_xboole_0(A,C) = k1_tarski(D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_zfmisc_1)).

tff(f_47,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_45,axiom,(
    ! [A,B] : k4_xboole_0(A,k3_xboole_0(A,B)) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).

tff(f_43,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_37,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_39,axiom,(
    ! [A,B,C] : k3_xboole_0(k3_xboole_0(A,B),C) = k3_xboole_0(A,k3_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_59,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => k2_xboole_0(k1_tarski(A),B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l22_zfmisc_1)).

tff(f_41,axiom,(
    ! [A,B] : k3_xboole_0(A,k2_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_xboole_1)).

tff(c_34,plain,(
    k3_xboole_0('#skF_1','#skF_3') != k1_tarski('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_36,plain,(
    r2_hidden('#skF_4','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_38,plain,(
    k3_xboole_0('#skF_2','#skF_3') = k1_tarski('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_22,plain,(
    ! [A_15,B_16] : k4_xboole_0(A_15,k4_xboole_0(A_15,B_16)) = k3_xboole_0(A_15,B_16) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_296,plain,(
    ! [A_48,B_49] : k4_xboole_0(A_48,k3_xboole_0(A_48,B_49)) = k4_xboole_0(A_48,B_49) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_302,plain,(
    ! [A_48,B_49] : k4_xboole_0(A_48,k4_xboole_0(A_48,B_49)) = k3_xboole_0(A_48,k3_xboole_0(A_48,B_49)) ),
    inference(superposition,[status(thm),theory(equality)],[c_296,c_22])).

tff(c_334,plain,(
    ! [A_48,B_49] : k3_xboole_0(A_48,k3_xboole_0(A_48,B_49)) = k3_xboole_0(A_48,B_49) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_302])).

tff(c_18,plain,(
    ! [A_12] : k4_xboole_0(A_12,k1_xboole_0) = A_12 ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_40,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_135,plain,(
    ! [A_38,B_39] :
      ( k4_xboole_0(A_38,B_39) = k1_xboole_0
      | ~ r1_tarski(A_38,B_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_143,plain,(
    k4_xboole_0('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_40,c_135])).

tff(c_170,plain,(
    ! [A_43,B_44] : k4_xboole_0(A_43,k4_xboole_0(A_43,B_44)) = k3_xboole_0(A_43,B_44) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_185,plain,(
    k4_xboole_0('#skF_1',k1_xboole_0) = k3_xboole_0('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_143,c_170])).

tff(c_194,plain,(
    k3_xboole_0('#skF_1','#skF_2') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_185])).

tff(c_798,plain,(
    ! [A_68,B_69,C_70] : k3_xboole_0(k3_xboole_0(A_68,B_69),C_70) = k3_xboole_0(A_68,k3_xboole_0(B_69,C_70)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_880,plain,(
    ! [C_70] : k3_xboole_0('#skF_1',k3_xboole_0('#skF_2',C_70)) = k3_xboole_0('#skF_1',C_70) ),
    inference(superposition,[status(thm),theory(equality)],[c_194,c_798])).

tff(c_8,plain,(
    ! [B_4] : r1_tarski(B_4,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_142,plain,(
    ! [B_4] : k4_xboole_0(B_4,B_4) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_8,c_135])).

tff(c_188,plain,(
    ! [B_4] : k4_xboole_0(B_4,k1_xboole_0) = k3_xboole_0(B_4,B_4) ),
    inference(superposition,[status(thm),theory(equality)],[c_142,c_170])).

tff(c_195,plain,(
    ! [B_4] : k3_xboole_0(B_4,B_4) = B_4 ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_188])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_3493,plain,(
    ! [B_109,A_110,B_111] : k3_xboole_0(B_109,k3_xboole_0(A_110,B_111)) = k3_xboole_0(A_110,k3_xboole_0(B_111,B_109)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_798])).

tff(c_4560,plain,(
    ! [B_116,B_117] : k3_xboole_0(B_116,k3_xboole_0(B_116,B_117)) = k3_xboole_0(B_117,B_116) ),
    inference(superposition,[status(thm),theory(equality)],[c_195,c_3493])).

tff(c_4741,plain,(
    ! [C_70] : k3_xboole_0(k3_xboole_0('#skF_2',C_70),'#skF_1') = k3_xboole_0('#skF_1',k3_xboole_0('#skF_1',C_70)) ),
    inference(superposition,[status(thm),theory(equality)],[c_880,c_4560])).

tff(c_7288,plain,(
    ! [C_136] : k3_xboole_0(k3_xboole_0('#skF_2',C_136),'#skF_1') = k3_xboole_0('#skF_1',C_136) ),
    inference(demodulation,[status(thm),theory(equality)],[c_334,c_4741])).

tff(c_7455,plain,(
    k3_xboole_0(k1_tarski('#skF_4'),'#skF_1') = k3_xboole_0('#skF_1','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_7288])).

tff(c_456,plain,(
    ! [A_55,B_56] :
      ( k2_xboole_0(k1_tarski(A_55),B_56) = B_56
      | ~ r2_hidden(A_55,B_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_16,plain,(
    ! [A_10,B_11] : k3_xboole_0(A_10,k2_xboole_0(A_10,B_11)) = A_10 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_465,plain,(
    ! [A_55,B_56] :
      ( k3_xboole_0(k1_tarski(A_55),B_56) = k1_tarski(A_55)
      | ~ r2_hidden(A_55,B_56) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_456,c_16])).

tff(c_7523,plain,
    ( k3_xboole_0('#skF_1','#skF_3') = k1_tarski('#skF_4')
    | ~ r2_hidden('#skF_4','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_7455,c_465])).

tff(c_7587,plain,(
    k3_xboole_0('#skF_1','#skF_3') = k1_tarski('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_7523])).

tff(c_7589,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_7587])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:31:19 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.30/2.59  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.55/2.60  
% 6.55/2.60  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.55/2.60  %$ r2_hidden > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 6.55/2.60  
% 6.55/2.60  %Foreground sorts:
% 6.55/2.60  
% 6.55/2.60  
% 6.55/2.60  %Background operators:
% 6.55/2.60  
% 6.55/2.60  
% 6.55/2.60  %Foreground operators:
% 6.55/2.60  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.55/2.60  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 6.55/2.60  tff(k1_tarski, type, k1_tarski: $i > $i).
% 6.55/2.60  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 6.55/2.60  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 6.55/2.60  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 6.55/2.60  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.55/2.60  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 6.55/2.60  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 6.55/2.60  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 6.55/2.60  tff('#skF_2', type, '#skF_2': $i).
% 6.55/2.60  tff('#skF_3', type, '#skF_3': $i).
% 6.55/2.60  tff('#skF_1', type, '#skF_1': $i).
% 6.55/2.60  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.55/2.60  tff('#skF_4', type, '#skF_4': $i).
% 6.55/2.60  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.55/2.60  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 6.55/2.60  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 6.55/2.60  
% 6.55/2.62  tff(f_68, negated_conjecture, ~(![A, B, C, D]: (((r1_tarski(A, B) & (k3_xboole_0(B, C) = k1_tarski(D))) & r2_hidden(D, A)) => (k3_xboole_0(A, C) = k1_tarski(D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_zfmisc_1)).
% 6.55/2.62  tff(f_47, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 6.55/2.62  tff(f_45, axiom, (![A, B]: (k4_xboole_0(A, k3_xboole_0(A, B)) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_xboole_1)).
% 6.55/2.62  tff(f_43, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 6.55/2.62  tff(f_37, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 6.55/2.62  tff(f_39, axiom, (![A, B, C]: (k3_xboole_0(k3_xboole_0(A, B), C) = k3_xboole_0(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t16_xboole_1)).
% 6.55/2.62  tff(f_33, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 6.55/2.62  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 6.55/2.62  tff(f_59, axiom, (![A, B]: (r2_hidden(A, B) => (k2_xboole_0(k1_tarski(A), B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l22_zfmisc_1)).
% 6.55/2.62  tff(f_41, axiom, (![A, B]: (k3_xboole_0(A, k2_xboole_0(A, B)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t21_xboole_1)).
% 6.55/2.62  tff(c_34, plain, (k3_xboole_0('#skF_1', '#skF_3')!=k1_tarski('#skF_4')), inference(cnfTransformation, [status(thm)], [f_68])).
% 6.55/2.62  tff(c_36, plain, (r2_hidden('#skF_4', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_68])).
% 6.55/2.62  tff(c_38, plain, (k3_xboole_0('#skF_2', '#skF_3')=k1_tarski('#skF_4')), inference(cnfTransformation, [status(thm)], [f_68])).
% 6.55/2.62  tff(c_22, plain, (![A_15, B_16]: (k4_xboole_0(A_15, k4_xboole_0(A_15, B_16))=k3_xboole_0(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_47])).
% 6.55/2.62  tff(c_296, plain, (![A_48, B_49]: (k4_xboole_0(A_48, k3_xboole_0(A_48, B_49))=k4_xboole_0(A_48, B_49))), inference(cnfTransformation, [status(thm)], [f_45])).
% 6.55/2.62  tff(c_302, plain, (![A_48, B_49]: (k4_xboole_0(A_48, k4_xboole_0(A_48, B_49))=k3_xboole_0(A_48, k3_xboole_0(A_48, B_49)))), inference(superposition, [status(thm), theory('equality')], [c_296, c_22])).
% 6.55/2.62  tff(c_334, plain, (![A_48, B_49]: (k3_xboole_0(A_48, k3_xboole_0(A_48, B_49))=k3_xboole_0(A_48, B_49))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_302])).
% 6.55/2.62  tff(c_18, plain, (![A_12]: (k4_xboole_0(A_12, k1_xboole_0)=A_12)), inference(cnfTransformation, [status(thm)], [f_43])).
% 6.55/2.62  tff(c_40, plain, (r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_68])).
% 6.55/2.62  tff(c_135, plain, (![A_38, B_39]: (k4_xboole_0(A_38, B_39)=k1_xboole_0 | ~r1_tarski(A_38, B_39))), inference(cnfTransformation, [status(thm)], [f_37])).
% 6.55/2.62  tff(c_143, plain, (k4_xboole_0('#skF_1', '#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_40, c_135])).
% 6.55/2.62  tff(c_170, plain, (![A_43, B_44]: (k4_xboole_0(A_43, k4_xboole_0(A_43, B_44))=k3_xboole_0(A_43, B_44))), inference(cnfTransformation, [status(thm)], [f_47])).
% 6.55/2.62  tff(c_185, plain, (k4_xboole_0('#skF_1', k1_xboole_0)=k3_xboole_0('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_143, c_170])).
% 6.55/2.62  tff(c_194, plain, (k3_xboole_0('#skF_1', '#skF_2')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_18, c_185])).
% 6.55/2.62  tff(c_798, plain, (![A_68, B_69, C_70]: (k3_xboole_0(k3_xboole_0(A_68, B_69), C_70)=k3_xboole_0(A_68, k3_xboole_0(B_69, C_70)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 6.55/2.62  tff(c_880, plain, (![C_70]: (k3_xboole_0('#skF_1', k3_xboole_0('#skF_2', C_70))=k3_xboole_0('#skF_1', C_70))), inference(superposition, [status(thm), theory('equality')], [c_194, c_798])).
% 6.55/2.62  tff(c_8, plain, (![B_4]: (r1_tarski(B_4, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 6.55/2.62  tff(c_142, plain, (![B_4]: (k4_xboole_0(B_4, B_4)=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_135])).
% 6.55/2.62  tff(c_188, plain, (![B_4]: (k4_xboole_0(B_4, k1_xboole_0)=k3_xboole_0(B_4, B_4))), inference(superposition, [status(thm), theory('equality')], [c_142, c_170])).
% 6.55/2.62  tff(c_195, plain, (![B_4]: (k3_xboole_0(B_4, B_4)=B_4)), inference(demodulation, [status(thm), theory('equality')], [c_18, c_188])).
% 6.55/2.62  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 6.55/2.62  tff(c_3493, plain, (![B_109, A_110, B_111]: (k3_xboole_0(B_109, k3_xboole_0(A_110, B_111))=k3_xboole_0(A_110, k3_xboole_0(B_111, B_109)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_798])).
% 6.55/2.62  tff(c_4560, plain, (![B_116, B_117]: (k3_xboole_0(B_116, k3_xboole_0(B_116, B_117))=k3_xboole_0(B_117, B_116))), inference(superposition, [status(thm), theory('equality')], [c_195, c_3493])).
% 6.55/2.62  tff(c_4741, plain, (![C_70]: (k3_xboole_0(k3_xboole_0('#skF_2', C_70), '#skF_1')=k3_xboole_0('#skF_1', k3_xboole_0('#skF_1', C_70)))), inference(superposition, [status(thm), theory('equality')], [c_880, c_4560])).
% 6.55/2.62  tff(c_7288, plain, (![C_136]: (k3_xboole_0(k3_xboole_0('#skF_2', C_136), '#skF_1')=k3_xboole_0('#skF_1', C_136))), inference(demodulation, [status(thm), theory('equality')], [c_334, c_4741])).
% 6.55/2.62  tff(c_7455, plain, (k3_xboole_0(k1_tarski('#skF_4'), '#skF_1')=k3_xboole_0('#skF_1', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_38, c_7288])).
% 6.55/2.62  tff(c_456, plain, (![A_55, B_56]: (k2_xboole_0(k1_tarski(A_55), B_56)=B_56 | ~r2_hidden(A_55, B_56))), inference(cnfTransformation, [status(thm)], [f_59])).
% 6.55/2.62  tff(c_16, plain, (![A_10, B_11]: (k3_xboole_0(A_10, k2_xboole_0(A_10, B_11))=A_10)), inference(cnfTransformation, [status(thm)], [f_41])).
% 6.55/2.62  tff(c_465, plain, (![A_55, B_56]: (k3_xboole_0(k1_tarski(A_55), B_56)=k1_tarski(A_55) | ~r2_hidden(A_55, B_56))), inference(superposition, [status(thm), theory('equality')], [c_456, c_16])).
% 6.55/2.62  tff(c_7523, plain, (k3_xboole_0('#skF_1', '#skF_3')=k1_tarski('#skF_4') | ~r2_hidden('#skF_4', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_7455, c_465])).
% 6.55/2.62  tff(c_7587, plain, (k3_xboole_0('#skF_1', '#skF_3')=k1_tarski('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_7523])).
% 6.55/2.62  tff(c_7589, plain, $false, inference(negUnitSimplification, [status(thm)], [c_34, c_7587])).
% 6.55/2.62  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.55/2.62  
% 6.55/2.62  Inference rules
% 6.55/2.62  ----------------------
% 6.55/2.62  #Ref     : 0
% 6.55/2.62  #Sup     : 1877
% 6.55/2.62  #Fact    : 0
% 6.55/2.62  #Define  : 0
% 6.55/2.62  #Split   : 1
% 6.55/2.62  #Chain   : 0
% 6.55/2.62  #Close   : 0
% 6.55/2.62  
% 6.55/2.62  Ordering : KBO
% 6.55/2.62  
% 6.55/2.62  Simplification rules
% 6.55/2.62  ----------------------
% 6.55/2.62  #Subsume      : 57
% 6.55/2.62  #Demod        : 2005
% 6.55/2.62  #Tautology    : 1206
% 6.55/2.62  #SimpNegUnit  : 1
% 6.55/2.62  #BackRed      : 2
% 6.55/2.62  
% 6.55/2.62  #Partial instantiations: 0
% 6.55/2.62  #Strategies tried      : 1
% 6.55/2.62  
% 6.55/2.62  Timing (in seconds)
% 6.55/2.62  ----------------------
% 6.55/2.62  Preprocessing        : 0.30
% 6.55/2.62  Parsing              : 0.15
% 6.55/2.62  CNF conversion       : 0.02
% 6.55/2.62  Main loop            : 1.55
% 6.55/2.62  Inferencing          : 0.39
% 6.55/2.62  Reduction            : 0.85
% 6.55/2.62  Demodulation         : 0.74
% 6.55/2.62  BG Simplification    : 0.04
% 6.55/2.62  Subsumption          : 0.20
% 6.55/2.62  Abstraction          : 0.06
% 6.55/2.62  MUC search           : 0.00
% 6.55/2.62  Cooper               : 0.00
% 6.55/2.62  Total                : 1.88
% 6.55/2.62  Index Insertion      : 0.00
% 6.55/2.62  Index Deletion       : 0.00
% 6.55/2.62  Index Matching       : 0.00
% 6.55/2.62  BG Taut test         : 0.00
%------------------------------------------------------------------------------
