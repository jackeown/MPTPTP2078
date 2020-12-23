%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:50:51 EST 2020

% Result     : Theorem 3.86s
% Output     : CNFRefutation 4.14s
% Verified   : 
% Statistics : Number of formulae       :   71 ( 107 expanded)
%              Number of leaves         :   32 (  50 expanded)
%              Depth                    :   12
%              Number of atoms          :   62 ( 107 expanded)
%              Number of equality atoms :   42 (  77 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_5 > #skF_2 > #skF_4 > #skF_3 > #skF_1

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

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_92,negated_conjecture,(
    ~ ! [A,B] :
        ( r2_hidden(A,B)
       => k2_xboole_0(k1_tarski(A),B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_zfmisc_1)).

tff(f_67,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_69,axiom,(
    ! [A,B] : k4_xboole_0(k2_xboole_0(A,B),B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_xboole_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_61,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_57,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_63,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_73,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_87,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_85,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_65,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

tff(c_76,plain,(
    r2_hidden('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_52,plain,(
    ! [A_24] : k4_xboole_0(A_24,k1_xboole_0) = A_24 ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_476,plain,(
    ! [A_89,B_90] : k4_xboole_0(k2_xboole_0(A_89,B_90),B_90) = k4_xboole_0(A_89,B_90) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_492,plain,(
    ! [A_89] : k4_xboole_0(A_89,k1_xboole_0) = k2_xboole_0(A_89,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_476,c_52])).

tff(c_514,plain,(
    ! [A_89] : k2_xboole_0(A_89,k1_xboole_0) = A_89 ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_492])).

tff(c_42,plain,(
    ! [B_16] : r1_tarski(B_16,B_16) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_187,plain,(
    ! [A_61,B_62] :
      ( k3_xboole_0(A_61,B_62) = A_61
      | ~ r1_tarski(A_61,B_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_219,plain,(
    ! [B_66] : k3_xboole_0(B_66,B_66) = B_66 ),
    inference(resolution,[status(thm)],[c_42,c_187])).

tff(c_44,plain,(
    ! [A_17,B_18] : k5_xboole_0(A_17,k3_xboole_0(A_17,B_18)) = k4_xboole_0(A_17,B_18) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_250,plain,(
    ! [B_68] : k5_xboole_0(B_68,B_68) = k4_xboole_0(B_68,B_68) ),
    inference(superposition,[status(thm),theory(equality)],[c_219,c_44])).

tff(c_48,plain,(
    ! [A_21] : r1_tarski(k1_xboole_0,A_21) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_198,plain,(
    ! [A_21] : k3_xboole_0(k1_xboole_0,A_21) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_48,c_187])).

tff(c_207,plain,(
    ! [A_64,B_65] : k5_xboole_0(A_64,k3_xboole_0(A_64,B_65)) = k4_xboole_0(A_64,B_65) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_216,plain,(
    ! [A_21] : k5_xboole_0(k1_xboole_0,k1_xboole_0) = k4_xboole_0(k1_xboole_0,A_21) ),
    inference(superposition,[status(thm),theory(equality)],[c_198,c_207])).

tff(c_256,plain,(
    ! [A_21] : k4_xboole_0(k1_xboole_0,k1_xboole_0) = k4_xboole_0(k1_xboole_0,A_21) ),
    inference(superposition,[status(thm),theory(equality)],[c_250,c_216])).

tff(c_264,plain,(
    ! [A_21] : k4_xboole_0(k1_xboole_0,A_21) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_256])).

tff(c_519,plain,(
    ! [A_91] : k2_xboole_0(A_91,k1_xboole_0) = A_91 ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_492])).

tff(c_58,plain,(
    ! [B_30,A_29] : k2_tarski(B_30,A_29) = k2_tarski(A_29,B_30) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_131,plain,(
    ! [A_51,B_52] : k3_tarski(k2_tarski(A_51,B_52)) = k2_xboole_0(A_51,B_52) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_343,plain,(
    ! [B_77,A_78] : k3_tarski(k2_tarski(B_77,A_78)) = k2_xboole_0(A_78,B_77) ),
    inference(superposition,[status(thm),theory(equality)],[c_58,c_131])).

tff(c_72,plain,(
    ! [A_43,B_44] : k3_tarski(k2_tarski(A_43,B_44)) = k2_xboole_0(A_43,B_44) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_349,plain,(
    ! [B_77,A_78] : k2_xboole_0(B_77,A_78) = k2_xboole_0(A_78,B_77) ),
    inference(superposition,[status(thm),theory(equality)],[c_343,c_72])).

tff(c_548,plain,(
    ! [A_92] : k2_xboole_0(k1_xboole_0,A_92) = A_92 ),
    inference(superposition,[status(thm),theory(equality)],[c_519,c_349])).

tff(c_54,plain,(
    ! [A_25,B_26] : k4_xboole_0(k2_xboole_0(A_25,B_26),B_26) = k4_xboole_0(A_25,B_26) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_558,plain,(
    ! [A_92] : k4_xboole_0(k1_xboole_0,A_92) = k4_xboole_0(A_92,A_92) ),
    inference(superposition,[status(thm),theory(equality)],[c_548,c_54])).

tff(c_582,plain,(
    ! [A_92] : k4_xboole_0(A_92,A_92) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_264,c_558])).

tff(c_225,plain,(
    ! [B_66] : k5_xboole_0(B_66,B_66) = k4_xboole_0(B_66,B_66) ),
    inference(superposition,[status(thm),theory(equality)],[c_219,c_44])).

tff(c_692,plain,(
    ! [B_66] : k5_xboole_0(B_66,B_66) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_582,c_225])).

tff(c_70,plain,(
    ! [A_41,B_42] :
      ( r1_tarski(k1_tarski(A_41),B_42)
      | ~ r2_hidden(A_41,B_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_2982,plain,(
    ! [A_176,B_177] :
      ( k3_xboole_0(k1_tarski(A_176),B_177) = k1_tarski(A_176)
      | ~ r2_hidden(A_176,B_177) ) ),
    inference(resolution,[status(thm)],[c_70,c_187])).

tff(c_2992,plain,(
    ! [A_176,B_177] :
      ( k5_xboole_0(k1_tarski(A_176),k1_tarski(A_176)) = k4_xboole_0(k1_tarski(A_176),B_177)
      | ~ r2_hidden(A_176,B_177) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2982,c_44])).

tff(c_3009,plain,(
    ! [A_178,B_179] :
      ( k4_xboole_0(k1_tarski(A_178),B_179) = k1_xboole_0
      | ~ r2_hidden(A_178,B_179) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_692,c_2992])).

tff(c_50,plain,(
    ! [A_22,B_23] : k2_xboole_0(A_22,k4_xboole_0(B_23,A_22)) = k2_xboole_0(A_22,B_23) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_3048,plain,(
    ! [B_179,A_178] :
      ( k2_xboole_0(B_179,k1_tarski(A_178)) = k2_xboole_0(B_179,k1_xboole_0)
      | ~ r2_hidden(A_178,B_179) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3009,c_50])).

tff(c_3099,plain,(
    ! [B_180,A_181] :
      ( k2_xboole_0(B_180,k1_tarski(A_181)) = B_180
      | ~ r2_hidden(A_181,B_180) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_514,c_3048])).

tff(c_74,plain,(
    k2_xboole_0(k1_tarski('#skF_4'),'#skF_5') != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_377,plain,(
    k2_xboole_0('#skF_5',k1_tarski('#skF_4')) != '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_349,c_74])).

tff(c_3187,plain,(
    ~ r2_hidden('#skF_4','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_3099,c_377])).

tff(c_3254,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_3187])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n007.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:04:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.86/1.73  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.86/1.73  
% 3.86/1.73  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.86/1.73  %$ r2_hidden > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_5 > #skF_2 > #skF_4 > #skF_3 > #skF_1
% 3.86/1.73  
% 3.86/1.73  %Foreground sorts:
% 3.86/1.73  
% 3.86/1.73  
% 3.86/1.73  %Background operators:
% 3.86/1.73  
% 3.86/1.73  
% 3.86/1.73  %Foreground operators:
% 3.86/1.73  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.86/1.73  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.86/1.73  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.86/1.73  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.86/1.73  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.86/1.73  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.86/1.73  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.86/1.73  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.86/1.73  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.86/1.73  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.86/1.73  tff('#skF_5', type, '#skF_5': $i).
% 3.86/1.73  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.86/1.73  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 3.86/1.73  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.86/1.73  tff(k3_tarski, type, k3_tarski: $i > $i).
% 3.86/1.73  tff('#skF_4', type, '#skF_4': $i).
% 3.86/1.73  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 3.86/1.73  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.86/1.73  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.86/1.73  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.86/1.73  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.86/1.73  
% 4.14/1.75  tff(f_92, negated_conjecture, ~(![A, B]: (r2_hidden(A, B) => (k2_xboole_0(k1_tarski(A), B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_zfmisc_1)).
% 4.14/1.75  tff(f_67, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 4.14/1.75  tff(f_69, axiom, (![A, B]: (k4_xboole_0(k2_xboole_0(A, B), B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t40_xboole_1)).
% 4.14/1.75  tff(f_55, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 4.14/1.75  tff(f_61, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 4.14/1.75  tff(f_57, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 4.14/1.75  tff(f_63, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 4.14/1.75  tff(f_73, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 4.14/1.75  tff(f_87, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 4.14/1.75  tff(f_85, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 4.14/1.75  tff(f_65, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_xboole_1)).
% 4.14/1.75  tff(c_76, plain, (r2_hidden('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_92])).
% 4.14/1.75  tff(c_52, plain, (![A_24]: (k4_xboole_0(A_24, k1_xboole_0)=A_24)), inference(cnfTransformation, [status(thm)], [f_67])).
% 4.14/1.75  tff(c_476, plain, (![A_89, B_90]: (k4_xboole_0(k2_xboole_0(A_89, B_90), B_90)=k4_xboole_0(A_89, B_90))), inference(cnfTransformation, [status(thm)], [f_69])).
% 4.14/1.75  tff(c_492, plain, (![A_89]: (k4_xboole_0(A_89, k1_xboole_0)=k2_xboole_0(A_89, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_476, c_52])).
% 4.14/1.75  tff(c_514, plain, (![A_89]: (k2_xboole_0(A_89, k1_xboole_0)=A_89)), inference(demodulation, [status(thm), theory('equality')], [c_52, c_492])).
% 4.14/1.75  tff(c_42, plain, (![B_16]: (r1_tarski(B_16, B_16))), inference(cnfTransformation, [status(thm)], [f_55])).
% 4.14/1.75  tff(c_187, plain, (![A_61, B_62]: (k3_xboole_0(A_61, B_62)=A_61 | ~r1_tarski(A_61, B_62))), inference(cnfTransformation, [status(thm)], [f_61])).
% 4.14/1.75  tff(c_219, plain, (![B_66]: (k3_xboole_0(B_66, B_66)=B_66)), inference(resolution, [status(thm)], [c_42, c_187])).
% 4.14/1.75  tff(c_44, plain, (![A_17, B_18]: (k5_xboole_0(A_17, k3_xboole_0(A_17, B_18))=k4_xboole_0(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_57])).
% 4.14/1.75  tff(c_250, plain, (![B_68]: (k5_xboole_0(B_68, B_68)=k4_xboole_0(B_68, B_68))), inference(superposition, [status(thm), theory('equality')], [c_219, c_44])).
% 4.14/1.75  tff(c_48, plain, (![A_21]: (r1_tarski(k1_xboole_0, A_21))), inference(cnfTransformation, [status(thm)], [f_63])).
% 4.14/1.75  tff(c_198, plain, (![A_21]: (k3_xboole_0(k1_xboole_0, A_21)=k1_xboole_0)), inference(resolution, [status(thm)], [c_48, c_187])).
% 4.14/1.75  tff(c_207, plain, (![A_64, B_65]: (k5_xboole_0(A_64, k3_xboole_0(A_64, B_65))=k4_xboole_0(A_64, B_65))), inference(cnfTransformation, [status(thm)], [f_57])).
% 4.14/1.75  tff(c_216, plain, (![A_21]: (k5_xboole_0(k1_xboole_0, k1_xboole_0)=k4_xboole_0(k1_xboole_0, A_21))), inference(superposition, [status(thm), theory('equality')], [c_198, c_207])).
% 4.14/1.75  tff(c_256, plain, (![A_21]: (k4_xboole_0(k1_xboole_0, k1_xboole_0)=k4_xboole_0(k1_xboole_0, A_21))), inference(superposition, [status(thm), theory('equality')], [c_250, c_216])).
% 4.14/1.75  tff(c_264, plain, (![A_21]: (k4_xboole_0(k1_xboole_0, A_21)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_52, c_256])).
% 4.14/1.75  tff(c_519, plain, (![A_91]: (k2_xboole_0(A_91, k1_xboole_0)=A_91)), inference(demodulation, [status(thm), theory('equality')], [c_52, c_492])).
% 4.14/1.75  tff(c_58, plain, (![B_30, A_29]: (k2_tarski(B_30, A_29)=k2_tarski(A_29, B_30))), inference(cnfTransformation, [status(thm)], [f_73])).
% 4.14/1.75  tff(c_131, plain, (![A_51, B_52]: (k3_tarski(k2_tarski(A_51, B_52))=k2_xboole_0(A_51, B_52))), inference(cnfTransformation, [status(thm)], [f_87])).
% 4.14/1.75  tff(c_343, plain, (![B_77, A_78]: (k3_tarski(k2_tarski(B_77, A_78))=k2_xboole_0(A_78, B_77))), inference(superposition, [status(thm), theory('equality')], [c_58, c_131])).
% 4.14/1.75  tff(c_72, plain, (![A_43, B_44]: (k3_tarski(k2_tarski(A_43, B_44))=k2_xboole_0(A_43, B_44))), inference(cnfTransformation, [status(thm)], [f_87])).
% 4.14/1.75  tff(c_349, plain, (![B_77, A_78]: (k2_xboole_0(B_77, A_78)=k2_xboole_0(A_78, B_77))), inference(superposition, [status(thm), theory('equality')], [c_343, c_72])).
% 4.14/1.75  tff(c_548, plain, (![A_92]: (k2_xboole_0(k1_xboole_0, A_92)=A_92)), inference(superposition, [status(thm), theory('equality')], [c_519, c_349])).
% 4.14/1.75  tff(c_54, plain, (![A_25, B_26]: (k4_xboole_0(k2_xboole_0(A_25, B_26), B_26)=k4_xboole_0(A_25, B_26))), inference(cnfTransformation, [status(thm)], [f_69])).
% 4.14/1.75  tff(c_558, plain, (![A_92]: (k4_xboole_0(k1_xboole_0, A_92)=k4_xboole_0(A_92, A_92))), inference(superposition, [status(thm), theory('equality')], [c_548, c_54])).
% 4.14/1.75  tff(c_582, plain, (![A_92]: (k4_xboole_0(A_92, A_92)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_264, c_558])).
% 4.14/1.75  tff(c_225, plain, (![B_66]: (k5_xboole_0(B_66, B_66)=k4_xboole_0(B_66, B_66))), inference(superposition, [status(thm), theory('equality')], [c_219, c_44])).
% 4.14/1.75  tff(c_692, plain, (![B_66]: (k5_xboole_0(B_66, B_66)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_582, c_225])).
% 4.14/1.75  tff(c_70, plain, (![A_41, B_42]: (r1_tarski(k1_tarski(A_41), B_42) | ~r2_hidden(A_41, B_42))), inference(cnfTransformation, [status(thm)], [f_85])).
% 4.14/1.75  tff(c_2982, plain, (![A_176, B_177]: (k3_xboole_0(k1_tarski(A_176), B_177)=k1_tarski(A_176) | ~r2_hidden(A_176, B_177))), inference(resolution, [status(thm)], [c_70, c_187])).
% 4.14/1.75  tff(c_2992, plain, (![A_176, B_177]: (k5_xboole_0(k1_tarski(A_176), k1_tarski(A_176))=k4_xboole_0(k1_tarski(A_176), B_177) | ~r2_hidden(A_176, B_177))), inference(superposition, [status(thm), theory('equality')], [c_2982, c_44])).
% 4.14/1.75  tff(c_3009, plain, (![A_178, B_179]: (k4_xboole_0(k1_tarski(A_178), B_179)=k1_xboole_0 | ~r2_hidden(A_178, B_179))), inference(demodulation, [status(thm), theory('equality')], [c_692, c_2992])).
% 4.14/1.75  tff(c_50, plain, (![A_22, B_23]: (k2_xboole_0(A_22, k4_xboole_0(B_23, A_22))=k2_xboole_0(A_22, B_23))), inference(cnfTransformation, [status(thm)], [f_65])).
% 4.14/1.75  tff(c_3048, plain, (![B_179, A_178]: (k2_xboole_0(B_179, k1_tarski(A_178))=k2_xboole_0(B_179, k1_xboole_0) | ~r2_hidden(A_178, B_179))), inference(superposition, [status(thm), theory('equality')], [c_3009, c_50])).
% 4.14/1.75  tff(c_3099, plain, (![B_180, A_181]: (k2_xboole_0(B_180, k1_tarski(A_181))=B_180 | ~r2_hidden(A_181, B_180))), inference(demodulation, [status(thm), theory('equality')], [c_514, c_3048])).
% 4.14/1.75  tff(c_74, plain, (k2_xboole_0(k1_tarski('#skF_4'), '#skF_5')!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_92])).
% 4.14/1.75  tff(c_377, plain, (k2_xboole_0('#skF_5', k1_tarski('#skF_4'))!='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_349, c_74])).
% 4.14/1.75  tff(c_3187, plain, (~r2_hidden('#skF_4', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_3099, c_377])).
% 4.14/1.75  tff(c_3254, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_76, c_3187])).
% 4.14/1.75  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.14/1.75  
% 4.14/1.75  Inference rules
% 4.14/1.75  ----------------------
% 4.14/1.75  #Ref     : 0
% 4.14/1.75  #Sup     : 780
% 4.14/1.75  #Fact    : 0
% 4.14/1.75  #Define  : 0
% 4.14/1.75  #Split   : 2
% 4.14/1.75  #Chain   : 0
% 4.14/1.75  #Close   : 0
% 4.14/1.75  
% 4.14/1.75  Ordering : KBO
% 4.14/1.75  
% 4.14/1.75  Simplification rules
% 4.14/1.75  ----------------------
% 4.14/1.75  #Subsume      : 114
% 4.14/1.75  #Demod        : 754
% 4.14/1.75  #Tautology    : 524
% 4.14/1.75  #SimpNegUnit  : 0
% 4.14/1.75  #BackRed      : 5
% 4.14/1.75  
% 4.14/1.75  #Partial instantiations: 0
% 4.14/1.75  #Strategies tried      : 1
% 4.14/1.75  
% 4.14/1.75  Timing (in seconds)
% 4.14/1.75  ----------------------
% 4.14/1.75  Preprocessing        : 0.32
% 4.14/1.75  Parsing              : 0.16
% 4.14/1.75  CNF conversion       : 0.02
% 4.14/1.75  Main loop            : 0.62
% 4.14/1.75  Inferencing          : 0.20
% 4.14/1.75  Reduction            : 0.27
% 4.14/1.75  Demodulation         : 0.22
% 4.14/1.75  BG Simplification    : 0.02
% 4.14/1.75  Subsumption          : 0.10
% 4.14/1.75  Abstraction          : 0.03
% 4.14/1.75  MUC search           : 0.00
% 4.14/1.75  Cooper               : 0.00
% 4.14/1.75  Total                : 0.97
% 4.14/1.75  Index Insertion      : 0.00
% 4.14/1.75  Index Deletion       : 0.00
% 4.14/1.75  Index Matching       : 0.00
% 4.14/1.75  BG Taut test         : 0.00
%------------------------------------------------------------------------------
