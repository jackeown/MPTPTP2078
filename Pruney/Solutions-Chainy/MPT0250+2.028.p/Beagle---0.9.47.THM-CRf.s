%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:50:35 EST 2020

% Result     : Theorem 2.27s
% Output     : CNFRefutation 2.65s
% Verified   : 
% Statistics : Number of formulae       :   61 ( 100 expanded)
%              Number of leaves         :   30 (  47 expanded)
%              Depth                    :   11
%              Number of atoms          :   49 (  89 expanded)
%              Number of equality atoms :   33 (  71 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1

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

tff('#skF_2',type,(
    '#skF_2': $i )).

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

tff(f_72,negated_conjecture,(
    ~ ! [A,B] :
        ( r1_tarski(k2_xboole_0(k1_tarski(A),B),B)
       => r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_zfmisc_1)).

tff(f_37,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

tff(f_41,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_43,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_47,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_67,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_45,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k5_xboole_0(k5_xboole_0(A,B),k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_xboole_1)).

tff(f_65,axiom,(
    ! [A,B] :
      ( k3_xboole_0(A,k1_tarski(B)) = k1_tarski(B)
     => r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l29_zfmisc_1)).

tff(c_42,plain,(
    ~ r2_hidden('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_12,plain,(
    ! [A_7] : k5_xboole_0(A_7,k1_xboole_0) = A_7 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_325,plain,(
    ! [A_81,B_82,C_83] : k5_xboole_0(k5_xboole_0(A_81,B_82),C_83) = k5_xboole_0(A_81,k5_xboole_0(B_82,C_83)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_18,plain,(
    ! [A_13] : k5_xboole_0(A_13,A_13) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_335,plain,(
    ! [A_81,B_82] : k5_xboole_0(A_81,k5_xboole_0(B_82,k5_xboole_0(A_81,B_82))) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_325,c_18])).

tff(c_461,plain,(
    ! [A_87,C_88] : k5_xboole_0(A_87,k5_xboole_0(A_87,C_88)) = k5_xboole_0(k1_xboole_0,C_88) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_325])).

tff(c_523,plain,(
    ! [A_13] : k5_xboole_0(k1_xboole_0,A_13) = k5_xboole_0(A_13,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_461])).

tff(c_541,plain,(
    ! [A_13] : k5_xboole_0(k1_xboole_0,A_13) = A_13 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_523])).

tff(c_348,plain,(
    ! [A_13,C_83] : k5_xboole_0(A_13,k5_xboole_0(A_13,C_83)) = k5_xboole_0(k1_xboole_0,C_83) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_325])).

tff(c_598,plain,(
    ! [A_90,C_91] : k5_xboole_0(A_90,k5_xboole_0(A_90,C_91)) = C_91 ),
    inference(demodulation,[status(thm),theory(equality)],[c_541,c_348])).

tff(c_642,plain,(
    ! [B_82,A_81] : k5_xboole_0(B_82,k5_xboole_0(A_81,B_82)) = k5_xboole_0(A_81,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_335,c_598])).

tff(c_746,plain,(
    ! [B_94,A_95] : k5_xboole_0(B_94,k5_xboole_0(A_95,B_94)) = A_95 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_642])).

tff(c_672,plain,(
    ! [B_82,A_81] : k5_xboole_0(B_82,k5_xboole_0(A_81,B_82)) = A_81 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_642])).

tff(c_749,plain,(
    ! [A_95,B_94] : k5_xboole_0(k5_xboole_0(A_95,B_94),A_95) = B_94 ),
    inference(superposition,[status(thm),theory(equality)],[c_746,c_672])).

tff(c_14,plain,(
    ! [A_8,B_9] : r1_tarski(A_8,k2_xboole_0(A_8,B_9)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_22,plain,(
    ! [B_17,A_16] : k2_tarski(B_17,A_16) = k2_tarski(A_16,B_17) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_138,plain,(
    ! [A_60,B_61] : k3_tarski(k2_tarski(A_60,B_61)) = k2_xboole_0(A_60,B_61) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_175,plain,(
    ! [B_65,A_66] : k3_tarski(k2_tarski(B_65,A_66)) = k2_xboole_0(A_66,B_65) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_138])).

tff(c_40,plain,(
    ! [A_48,B_49] : k3_tarski(k2_tarski(A_48,B_49)) = k2_xboole_0(A_48,B_49) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_181,plain,(
    ! [B_65,A_66] : k2_xboole_0(B_65,A_66) = k2_xboole_0(A_66,B_65) ),
    inference(superposition,[status(thm),theory(equality)],[c_175,c_40])).

tff(c_44,plain,(
    r1_tarski(k2_xboole_0(k1_tarski('#skF_1'),'#skF_2'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_202,plain,(
    r1_tarski(k2_xboole_0('#skF_2',k1_tarski('#skF_1')),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_181,c_44])).

tff(c_6,plain,(
    ! [B_6,A_5] :
      ( B_6 = A_5
      | ~ r1_tarski(B_6,A_5)
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_270,plain,
    ( k2_xboole_0('#skF_2',k1_tarski('#skF_1')) = '#skF_2'
    | ~ r1_tarski('#skF_2',k2_xboole_0('#skF_2',k1_tarski('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_202,c_6])).

tff(c_273,plain,(
    k2_xboole_0('#skF_2',k1_tarski('#skF_1')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_270])).

tff(c_677,plain,(
    ! [A_92,B_93] : k5_xboole_0(k5_xboole_0(A_92,B_93),k2_xboole_0(A_92,B_93)) = k3_xboole_0(A_92,B_93) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_720,plain,(
    k5_xboole_0(k5_xboole_0('#skF_2',k1_tarski('#skF_1')),'#skF_2') = k3_xboole_0('#skF_2',k1_tarski('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_273,c_677])).

tff(c_895,plain,(
    k3_xboole_0('#skF_2',k1_tarski('#skF_1')) = k1_tarski('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_749,c_720])).

tff(c_38,plain,(
    ! [B_47,A_46] :
      ( r2_hidden(B_47,A_46)
      | k3_xboole_0(A_46,k1_tarski(B_47)) != k1_tarski(B_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_899,plain,(
    r2_hidden('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_895,c_38])).

tff(c_905,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_899])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n018.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 20:28:27 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.27/1.32  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.27/1.32  
% 2.27/1.32  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.27/1.32  %$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1
% 2.27/1.32  
% 2.27/1.32  %Foreground sorts:
% 2.27/1.32  
% 2.27/1.32  
% 2.27/1.32  %Background operators:
% 2.27/1.32  
% 2.27/1.32  
% 2.27/1.32  %Foreground operators:
% 2.27/1.32  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.27/1.32  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.27/1.32  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.27/1.32  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.27/1.32  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.27/1.32  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.27/1.32  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.27/1.32  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.27/1.32  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.27/1.32  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.27/1.32  tff('#skF_2', type, '#skF_2': $i).
% 2.27/1.32  tff('#skF_1', type, '#skF_1': $i).
% 2.27/1.32  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.27/1.32  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.27/1.32  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.27/1.32  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.27/1.32  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.27/1.32  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.27/1.32  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.27/1.32  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.27/1.32  
% 2.65/1.33  tff(f_72, negated_conjecture, ~(![A, B]: (r1_tarski(k2_xboole_0(k1_tarski(A), B), B) => r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t45_zfmisc_1)).
% 2.65/1.33  tff(f_37, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 2.65/1.33  tff(f_41, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_xboole_1)).
% 2.65/1.33  tff(f_43, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t92_xboole_1)).
% 2.65/1.33  tff(f_39, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 2.65/1.33  tff(f_47, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 2.65/1.33  tff(f_67, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 2.65/1.33  tff(f_35, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.65/1.33  tff(f_45, axiom, (![A, B]: (k3_xboole_0(A, B) = k5_xboole_0(k5_xboole_0(A, B), k2_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t95_xboole_1)).
% 2.65/1.33  tff(f_65, axiom, (![A, B]: ((k3_xboole_0(A, k1_tarski(B)) = k1_tarski(B)) => r2_hidden(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l29_zfmisc_1)).
% 2.65/1.33  tff(c_42, plain, (~r2_hidden('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.65/1.33  tff(c_12, plain, (![A_7]: (k5_xboole_0(A_7, k1_xboole_0)=A_7)), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.65/1.33  tff(c_325, plain, (![A_81, B_82, C_83]: (k5_xboole_0(k5_xboole_0(A_81, B_82), C_83)=k5_xboole_0(A_81, k5_xboole_0(B_82, C_83)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.65/1.33  tff(c_18, plain, (![A_13]: (k5_xboole_0(A_13, A_13)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.65/1.33  tff(c_335, plain, (![A_81, B_82]: (k5_xboole_0(A_81, k5_xboole_0(B_82, k5_xboole_0(A_81, B_82)))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_325, c_18])).
% 2.65/1.33  tff(c_461, plain, (![A_87, C_88]: (k5_xboole_0(A_87, k5_xboole_0(A_87, C_88))=k5_xboole_0(k1_xboole_0, C_88))), inference(superposition, [status(thm), theory('equality')], [c_18, c_325])).
% 2.65/1.33  tff(c_523, plain, (![A_13]: (k5_xboole_0(k1_xboole_0, A_13)=k5_xboole_0(A_13, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_18, c_461])).
% 2.65/1.33  tff(c_541, plain, (![A_13]: (k5_xboole_0(k1_xboole_0, A_13)=A_13)), inference(demodulation, [status(thm), theory('equality')], [c_12, c_523])).
% 2.65/1.33  tff(c_348, plain, (![A_13, C_83]: (k5_xboole_0(A_13, k5_xboole_0(A_13, C_83))=k5_xboole_0(k1_xboole_0, C_83))), inference(superposition, [status(thm), theory('equality')], [c_18, c_325])).
% 2.65/1.33  tff(c_598, plain, (![A_90, C_91]: (k5_xboole_0(A_90, k5_xboole_0(A_90, C_91))=C_91)), inference(demodulation, [status(thm), theory('equality')], [c_541, c_348])).
% 2.65/1.33  tff(c_642, plain, (![B_82, A_81]: (k5_xboole_0(B_82, k5_xboole_0(A_81, B_82))=k5_xboole_0(A_81, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_335, c_598])).
% 2.65/1.33  tff(c_746, plain, (![B_94, A_95]: (k5_xboole_0(B_94, k5_xboole_0(A_95, B_94))=A_95)), inference(demodulation, [status(thm), theory('equality')], [c_12, c_642])).
% 2.65/1.33  tff(c_672, plain, (![B_82, A_81]: (k5_xboole_0(B_82, k5_xboole_0(A_81, B_82))=A_81)), inference(demodulation, [status(thm), theory('equality')], [c_12, c_642])).
% 2.65/1.33  tff(c_749, plain, (![A_95, B_94]: (k5_xboole_0(k5_xboole_0(A_95, B_94), A_95)=B_94)), inference(superposition, [status(thm), theory('equality')], [c_746, c_672])).
% 2.65/1.33  tff(c_14, plain, (![A_8, B_9]: (r1_tarski(A_8, k2_xboole_0(A_8, B_9)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.65/1.33  tff(c_22, plain, (![B_17, A_16]: (k2_tarski(B_17, A_16)=k2_tarski(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.65/1.33  tff(c_138, plain, (![A_60, B_61]: (k3_tarski(k2_tarski(A_60, B_61))=k2_xboole_0(A_60, B_61))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.65/1.33  tff(c_175, plain, (![B_65, A_66]: (k3_tarski(k2_tarski(B_65, A_66))=k2_xboole_0(A_66, B_65))), inference(superposition, [status(thm), theory('equality')], [c_22, c_138])).
% 2.65/1.33  tff(c_40, plain, (![A_48, B_49]: (k3_tarski(k2_tarski(A_48, B_49))=k2_xboole_0(A_48, B_49))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.65/1.33  tff(c_181, plain, (![B_65, A_66]: (k2_xboole_0(B_65, A_66)=k2_xboole_0(A_66, B_65))), inference(superposition, [status(thm), theory('equality')], [c_175, c_40])).
% 2.65/1.33  tff(c_44, plain, (r1_tarski(k2_xboole_0(k1_tarski('#skF_1'), '#skF_2'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.65/1.33  tff(c_202, plain, (r1_tarski(k2_xboole_0('#skF_2', k1_tarski('#skF_1')), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_181, c_44])).
% 2.65/1.33  tff(c_6, plain, (![B_6, A_5]: (B_6=A_5 | ~r1_tarski(B_6, A_5) | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.65/1.33  tff(c_270, plain, (k2_xboole_0('#skF_2', k1_tarski('#skF_1'))='#skF_2' | ~r1_tarski('#skF_2', k2_xboole_0('#skF_2', k1_tarski('#skF_1')))), inference(resolution, [status(thm)], [c_202, c_6])).
% 2.65/1.33  tff(c_273, plain, (k2_xboole_0('#skF_2', k1_tarski('#skF_1'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_14, c_270])).
% 2.65/1.33  tff(c_677, plain, (![A_92, B_93]: (k5_xboole_0(k5_xboole_0(A_92, B_93), k2_xboole_0(A_92, B_93))=k3_xboole_0(A_92, B_93))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.65/1.33  tff(c_720, plain, (k5_xboole_0(k5_xboole_0('#skF_2', k1_tarski('#skF_1')), '#skF_2')=k3_xboole_0('#skF_2', k1_tarski('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_273, c_677])).
% 2.65/1.33  tff(c_895, plain, (k3_xboole_0('#skF_2', k1_tarski('#skF_1'))=k1_tarski('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_749, c_720])).
% 2.65/1.33  tff(c_38, plain, (![B_47, A_46]: (r2_hidden(B_47, A_46) | k3_xboole_0(A_46, k1_tarski(B_47))!=k1_tarski(B_47))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.65/1.33  tff(c_899, plain, (r2_hidden('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_895, c_38])).
% 2.65/1.33  tff(c_905, plain, $false, inference(negUnitSimplification, [status(thm)], [c_42, c_899])).
% 2.65/1.33  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.65/1.33  
% 2.65/1.33  Inference rules
% 2.65/1.33  ----------------------
% 2.65/1.33  #Ref     : 0
% 2.65/1.33  #Sup     : 207
% 2.65/1.33  #Fact    : 0
% 2.65/1.33  #Define  : 0
% 2.65/1.33  #Split   : 1
% 2.65/1.33  #Chain   : 0
% 2.65/1.33  #Close   : 0
% 2.65/1.33  
% 2.65/1.33  Ordering : KBO
% 2.65/1.33  
% 2.65/1.33  Simplification rules
% 2.65/1.33  ----------------------
% 2.65/1.33  #Subsume      : 1
% 2.65/1.33  #Demod        : 133
% 2.65/1.33  #Tautology    : 141
% 2.65/1.33  #SimpNegUnit  : 1
% 2.65/1.33  #BackRed      : 5
% 2.65/1.33  
% 2.65/1.33  #Partial instantiations: 0
% 2.65/1.33  #Strategies tried      : 1
% 2.65/1.33  
% 2.65/1.33  Timing (in seconds)
% 2.65/1.33  ----------------------
% 2.65/1.34  Preprocessing        : 0.30
% 2.65/1.34  Parsing              : 0.16
% 2.65/1.34  CNF conversion       : 0.02
% 2.65/1.34  Main loop            : 0.28
% 2.65/1.34  Inferencing          : 0.10
% 2.65/1.34  Reduction            : 0.11
% 2.65/1.34  Demodulation         : 0.09
% 2.65/1.34  BG Simplification    : 0.02
% 2.65/1.34  Subsumption          : 0.05
% 2.65/1.34  Abstraction          : 0.02
% 2.65/1.34  MUC search           : 0.00
% 2.65/1.34  Cooper               : 0.00
% 2.65/1.34  Total                : 0.61
% 2.65/1.34  Index Insertion      : 0.00
% 2.65/1.34  Index Deletion       : 0.00
% 2.65/1.34  Index Matching       : 0.00
% 2.65/1.34  BG Taut test         : 0.00
%------------------------------------------------------------------------------
