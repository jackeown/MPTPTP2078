%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:50:57 EST 2020

% Result     : Theorem 3.96s
% Output     : CNFRefutation 4.22s
% Verified   : 
% Statistics : Number of formulae       :   66 (  72 expanded)
%              Number of leaves         :   32 (  37 expanded)
%              Depth                    :   10
%              Number of atoms          :   68 (  76 expanded)
%              Number of equality atoms :   35 (  41 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1

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

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

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

tff(f_78,negated_conjecture,(
    ~ ! [A,B] :
        ( r2_hidden(A,B)
       => k2_xboole_0(k1_tarski(A),B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_zfmisc_1)).

tff(f_41,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

tff(f_51,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_55,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_49,axiom,(
    ! [A,B] : k4_xboole_0(k2_xboole_0(A,B),B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_45,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_59,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_73,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_tarski(A,B),C)
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).

tff(f_47,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

tff(c_48,plain,(
    r2_hidden('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_14,plain,(
    ! [A_9] : k2_xboole_0(A_9,k1_xboole_0) = A_9 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_22,plain,(
    ! [A_16] : r1_xboole_0(A_16,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_71,plain,(
    ! [B_40,A_41] :
      ( r1_xboole_0(B_40,A_41)
      | ~ r1_xboole_0(A_41,B_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_74,plain,(
    ! [A_16] : r1_xboole_0(k1_xboole_0,A_16) ),
    inference(resolution,[status(thm)],[c_22,c_71])).

tff(c_217,plain,(
    ! [A_54,B_55] :
      ( k4_xboole_0(A_54,B_55) = A_54
      | ~ r1_xboole_0(A_54,B_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_224,plain,(
    ! [A_16] : k4_xboole_0(k1_xboole_0,A_16) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_74,c_217])).

tff(c_80,plain,(
    ! [B_43,A_44] : k2_xboole_0(B_43,A_44) = k2_xboole_0(A_44,B_43) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_96,plain,(
    ! [A_44] : k2_xboole_0(k1_xboole_0,A_44) = A_44 ),
    inference(superposition,[status(thm),theory(equality)],[c_80,c_14])).

tff(c_287,plain,(
    ! [A_66,B_67] : k4_xboole_0(k2_xboole_0(A_66,B_67),B_67) = k4_xboole_0(A_66,B_67) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_307,plain,(
    ! [A_44] : k4_xboole_0(k1_xboole_0,A_44) = k4_xboole_0(A_44,A_44) ),
    inference(superposition,[status(thm),theory(equality)],[c_96,c_287])).

tff(c_321,plain,(
    ! [A_44] : k4_xboole_0(A_44,A_44) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_224,c_307])).

tff(c_10,plain,(
    ! [B_6] : r1_tarski(B_6,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_127,plain,(
    ! [A_45,B_46] :
      ( k3_xboole_0(A_45,B_46) = A_45
      | ~ r1_tarski(A_45,B_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_131,plain,(
    ! [B_6] : k3_xboole_0(B_6,B_6) = B_6 ),
    inference(resolution,[status(thm)],[c_10,c_127])).

tff(c_275,plain,(
    ! [A_64,B_65] : k5_xboole_0(A_64,k3_xboole_0(A_64,B_65)) = k4_xboole_0(A_64,B_65) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_284,plain,(
    ! [B_6] : k5_xboole_0(B_6,B_6) = k4_xboole_0(B_6,B_6) ),
    inference(superposition,[status(thm),theory(equality)],[c_131,c_275])).

tff(c_348,plain,(
    ! [B_6] : k5_xboole_0(B_6,B_6) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_321,c_284])).

tff(c_30,plain,(
    ! [A_21] : k2_tarski(A_21,A_21) = k1_tarski(A_21) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_715,plain,(
    ! [A_99,B_100,C_101] :
      ( r1_tarski(k2_tarski(A_99,B_100),C_101)
      | ~ r2_hidden(B_100,C_101)
      | ~ r2_hidden(A_99,C_101) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_1281,plain,(
    ! [A_124,C_125] :
      ( r1_tarski(k1_tarski(A_124),C_125)
      | ~ r2_hidden(A_124,C_125)
      | ~ r2_hidden(A_124,C_125) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_715])).

tff(c_16,plain,(
    ! [A_10,B_11] :
      ( k3_xboole_0(A_10,B_11) = A_10
      | ~ r1_tarski(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_3632,plain,(
    ! [A_168,C_169] :
      ( k3_xboole_0(k1_tarski(A_168),C_169) = k1_tarski(A_168)
      | ~ r2_hidden(A_168,C_169) ) ),
    inference(resolution,[status(thm)],[c_1281,c_16])).

tff(c_12,plain,(
    ! [A_7,B_8] : k5_xboole_0(A_7,k3_xboole_0(A_7,B_8)) = k4_xboole_0(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_3638,plain,(
    ! [A_168,C_169] :
      ( k5_xboole_0(k1_tarski(A_168),k1_tarski(A_168)) = k4_xboole_0(k1_tarski(A_168),C_169)
      | ~ r2_hidden(A_168,C_169) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3632,c_12])).

tff(c_3659,plain,(
    ! [A_170,C_171] :
      ( k4_xboole_0(k1_tarski(A_170),C_171) = k1_xboole_0
      | ~ r2_hidden(A_170,C_171) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_348,c_3638])).

tff(c_18,plain,(
    ! [A_12,B_13] : k2_xboole_0(A_12,k4_xboole_0(B_13,A_12)) = k2_xboole_0(A_12,B_13) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_3721,plain,(
    ! [C_171,A_170] :
      ( k2_xboole_0(C_171,k1_tarski(A_170)) = k2_xboole_0(C_171,k1_xboole_0)
      | ~ r2_hidden(A_170,C_171) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3659,c_18])).

tff(c_3795,plain,(
    ! [C_173,A_174] :
      ( k2_xboole_0(C_173,k1_tarski(A_174)) = C_173
      | ~ r2_hidden(A_174,C_173) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_3721])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_46,plain,(
    k2_xboole_0(k1_tarski('#skF_1'),'#skF_2') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_50,plain,(
    k2_xboole_0('#skF_2',k1_tarski('#skF_1')) != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_46])).

tff(c_3889,plain,(
    ~ r2_hidden('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_3795,c_50])).

tff(c_3948,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_3889])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:24:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.96/1.76  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.96/1.76  
% 3.96/1.76  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.96/1.76  %$ r2_hidden > r1_xboole_0 > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1
% 3.96/1.76  
% 3.96/1.76  %Foreground sorts:
% 3.96/1.76  
% 3.96/1.76  
% 3.96/1.76  %Background operators:
% 3.96/1.76  
% 3.96/1.76  
% 3.96/1.76  %Foreground operators:
% 3.96/1.76  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.96/1.76  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.96/1.76  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.96/1.76  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.96/1.76  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.96/1.76  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.96/1.76  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.96/1.76  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.96/1.76  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.96/1.76  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.96/1.76  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.96/1.76  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.96/1.76  tff('#skF_2', type, '#skF_2': $i).
% 3.96/1.76  tff('#skF_1', type, '#skF_1': $i).
% 3.96/1.76  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.96/1.76  tff(k3_tarski, type, k3_tarski: $i > $i).
% 3.96/1.76  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.96/1.76  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.96/1.76  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.96/1.76  
% 4.22/1.78  tff(f_78, negated_conjecture, ~(![A, B]: (r2_hidden(A, B) => (k2_xboole_0(k1_tarski(A), B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_zfmisc_1)).
% 4.22/1.78  tff(f_41, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 4.22/1.78  tff(f_51, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 4.22/1.78  tff(f_31, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 4.22/1.78  tff(f_55, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_xboole_1)).
% 4.22/1.78  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 4.22/1.78  tff(f_49, axiom, (![A, B]: (k4_xboole_0(k2_xboole_0(A, B), B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t40_xboole_1)).
% 4.22/1.78  tff(f_37, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 4.22/1.78  tff(f_45, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 4.22/1.78  tff(f_39, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 4.22/1.78  tff(f_59, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 4.22/1.78  tff(f_73, axiom, (![A, B, C]: (r1_tarski(k2_tarski(A, B), C) <=> (r2_hidden(A, C) & r2_hidden(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 4.22/1.78  tff(f_47, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 4.22/1.78  tff(c_48, plain, (r2_hidden('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_78])).
% 4.22/1.78  tff(c_14, plain, (![A_9]: (k2_xboole_0(A_9, k1_xboole_0)=A_9)), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.22/1.78  tff(c_22, plain, (![A_16]: (r1_xboole_0(A_16, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_51])).
% 4.22/1.78  tff(c_71, plain, (![B_40, A_41]: (r1_xboole_0(B_40, A_41) | ~r1_xboole_0(A_41, B_40))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.22/1.78  tff(c_74, plain, (![A_16]: (r1_xboole_0(k1_xboole_0, A_16))), inference(resolution, [status(thm)], [c_22, c_71])).
% 4.22/1.78  tff(c_217, plain, (![A_54, B_55]: (k4_xboole_0(A_54, B_55)=A_54 | ~r1_xboole_0(A_54, B_55))), inference(cnfTransformation, [status(thm)], [f_55])).
% 4.22/1.78  tff(c_224, plain, (![A_16]: (k4_xboole_0(k1_xboole_0, A_16)=k1_xboole_0)), inference(resolution, [status(thm)], [c_74, c_217])).
% 4.22/1.78  tff(c_80, plain, (![B_43, A_44]: (k2_xboole_0(B_43, A_44)=k2_xboole_0(A_44, B_43))), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.22/1.78  tff(c_96, plain, (![A_44]: (k2_xboole_0(k1_xboole_0, A_44)=A_44)), inference(superposition, [status(thm), theory('equality')], [c_80, c_14])).
% 4.22/1.78  tff(c_287, plain, (![A_66, B_67]: (k4_xboole_0(k2_xboole_0(A_66, B_67), B_67)=k4_xboole_0(A_66, B_67))), inference(cnfTransformation, [status(thm)], [f_49])).
% 4.22/1.78  tff(c_307, plain, (![A_44]: (k4_xboole_0(k1_xboole_0, A_44)=k4_xboole_0(A_44, A_44))), inference(superposition, [status(thm), theory('equality')], [c_96, c_287])).
% 4.22/1.78  tff(c_321, plain, (![A_44]: (k4_xboole_0(A_44, A_44)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_224, c_307])).
% 4.22/1.78  tff(c_10, plain, (![B_6]: (r1_tarski(B_6, B_6))), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.22/1.78  tff(c_127, plain, (![A_45, B_46]: (k3_xboole_0(A_45, B_46)=A_45 | ~r1_tarski(A_45, B_46))), inference(cnfTransformation, [status(thm)], [f_45])).
% 4.22/1.78  tff(c_131, plain, (![B_6]: (k3_xboole_0(B_6, B_6)=B_6)), inference(resolution, [status(thm)], [c_10, c_127])).
% 4.22/1.78  tff(c_275, plain, (![A_64, B_65]: (k5_xboole_0(A_64, k3_xboole_0(A_64, B_65))=k4_xboole_0(A_64, B_65))), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.22/1.78  tff(c_284, plain, (![B_6]: (k5_xboole_0(B_6, B_6)=k4_xboole_0(B_6, B_6))), inference(superposition, [status(thm), theory('equality')], [c_131, c_275])).
% 4.22/1.78  tff(c_348, plain, (![B_6]: (k5_xboole_0(B_6, B_6)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_321, c_284])).
% 4.22/1.78  tff(c_30, plain, (![A_21]: (k2_tarski(A_21, A_21)=k1_tarski(A_21))), inference(cnfTransformation, [status(thm)], [f_59])).
% 4.22/1.78  tff(c_715, plain, (![A_99, B_100, C_101]: (r1_tarski(k2_tarski(A_99, B_100), C_101) | ~r2_hidden(B_100, C_101) | ~r2_hidden(A_99, C_101))), inference(cnfTransformation, [status(thm)], [f_73])).
% 4.22/1.78  tff(c_1281, plain, (![A_124, C_125]: (r1_tarski(k1_tarski(A_124), C_125) | ~r2_hidden(A_124, C_125) | ~r2_hidden(A_124, C_125))), inference(superposition, [status(thm), theory('equality')], [c_30, c_715])).
% 4.22/1.78  tff(c_16, plain, (![A_10, B_11]: (k3_xboole_0(A_10, B_11)=A_10 | ~r1_tarski(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_45])).
% 4.22/1.78  tff(c_3632, plain, (![A_168, C_169]: (k3_xboole_0(k1_tarski(A_168), C_169)=k1_tarski(A_168) | ~r2_hidden(A_168, C_169))), inference(resolution, [status(thm)], [c_1281, c_16])).
% 4.22/1.78  tff(c_12, plain, (![A_7, B_8]: (k5_xboole_0(A_7, k3_xboole_0(A_7, B_8))=k4_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.22/1.78  tff(c_3638, plain, (![A_168, C_169]: (k5_xboole_0(k1_tarski(A_168), k1_tarski(A_168))=k4_xboole_0(k1_tarski(A_168), C_169) | ~r2_hidden(A_168, C_169))), inference(superposition, [status(thm), theory('equality')], [c_3632, c_12])).
% 4.22/1.78  tff(c_3659, plain, (![A_170, C_171]: (k4_xboole_0(k1_tarski(A_170), C_171)=k1_xboole_0 | ~r2_hidden(A_170, C_171))), inference(demodulation, [status(thm), theory('equality')], [c_348, c_3638])).
% 4.22/1.78  tff(c_18, plain, (![A_12, B_13]: (k2_xboole_0(A_12, k4_xboole_0(B_13, A_12))=k2_xboole_0(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_47])).
% 4.22/1.78  tff(c_3721, plain, (![C_171, A_170]: (k2_xboole_0(C_171, k1_tarski(A_170))=k2_xboole_0(C_171, k1_xboole_0) | ~r2_hidden(A_170, C_171))), inference(superposition, [status(thm), theory('equality')], [c_3659, c_18])).
% 4.22/1.78  tff(c_3795, plain, (![C_173, A_174]: (k2_xboole_0(C_173, k1_tarski(A_174))=C_173 | ~r2_hidden(A_174, C_173))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_3721])).
% 4.22/1.78  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.22/1.78  tff(c_46, plain, (k2_xboole_0(k1_tarski('#skF_1'), '#skF_2')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_78])).
% 4.22/1.78  tff(c_50, plain, (k2_xboole_0('#skF_2', k1_tarski('#skF_1'))!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_2, c_46])).
% 4.22/1.78  tff(c_3889, plain, (~r2_hidden('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_3795, c_50])).
% 4.22/1.78  tff(c_3948, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_48, c_3889])).
% 4.22/1.78  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.22/1.78  
% 4.22/1.78  Inference rules
% 4.22/1.78  ----------------------
% 4.22/1.78  #Ref     : 0
% 4.22/1.78  #Sup     : 949
% 4.22/1.78  #Fact    : 0
% 4.22/1.78  #Define  : 0
% 4.22/1.78  #Split   : 0
% 4.22/1.78  #Chain   : 0
% 4.22/1.78  #Close   : 0
% 4.22/1.78  
% 4.22/1.78  Ordering : KBO
% 4.22/1.78  
% 4.22/1.78  Simplification rules
% 4.22/1.78  ----------------------
% 4.22/1.78  #Subsume      : 94
% 4.22/1.78  #Demod        : 1028
% 4.22/1.78  #Tautology    : 640
% 4.22/1.78  #SimpNegUnit  : 0
% 4.22/1.78  #BackRed      : 1
% 4.22/1.78  
% 4.22/1.78  #Partial instantiations: 0
% 4.22/1.78  #Strategies tried      : 1
% 4.22/1.78  
% 4.22/1.78  Timing (in seconds)
% 4.22/1.78  ----------------------
% 4.22/1.78  Preprocessing        : 0.31
% 4.22/1.78  Parsing              : 0.17
% 4.22/1.78  CNF conversion       : 0.02
% 4.22/1.78  Main loop            : 0.70
% 4.22/1.78  Inferencing          : 0.21
% 4.22/1.78  Reduction            : 0.33
% 4.22/1.78  Demodulation         : 0.28
% 4.22/1.78  BG Simplification    : 0.03
% 4.22/1.78  Subsumption          : 0.09
% 4.22/1.78  Abstraction          : 0.04
% 4.22/1.78  MUC search           : 0.00
% 4.22/1.78  Cooper               : 0.00
% 4.22/1.78  Total                : 1.04
% 4.22/1.78  Index Insertion      : 0.00
% 4.22/1.78  Index Deletion       : 0.00
% 4.22/1.78  Index Matching       : 0.00
% 4.22/1.78  BG Taut test         : 0.00
%------------------------------------------------------------------------------
