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
% DateTime   : Thu Dec  3 09:49:50 EST 2020

% Result     : Theorem 2.22s
% Output     : CNFRefutation 2.22s
% Verified   : 
% Statistics : Number of formulae       :   65 (  98 expanded)
%              Number of leaves         :   34 (  48 expanded)
%              Depth                    :    8
%              Number of atoms          :   56 (  99 expanded)
%              Number of equality atoms :   47 (  86 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

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

tff(f_37,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_35,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_29,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_45,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_68,axiom,(
    ! [A,B] : k4_xboole_0(k1_tarski(A),k2_tarski(A,B)) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_zfmisc_1)).

tff(f_43,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_59,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_64,axiom,(
    ! [A,B] :
      ( A != B
     => r1_xboole_0(k1_tarski(A),k1_tarski(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_zfmisc_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_73,axiom,(
    ! [A,B] :
      ( A != B
     => k5_xboole_0(k1_tarski(A),k1_tarski(B)) = k2_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_zfmisc_1)).

tff(f_76,negated_conjecture,(
    ~ ! [A,B] : k3_tarski(k2_tarski(k1_tarski(A),k1_tarski(B))) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_zfmisc_1)).

tff(c_10,plain,(
    ! [A_8] : k4_xboole_0(A_8,k1_xboole_0) = A_8 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_8,plain,(
    ! [A_7] : r1_tarski(k1_xboole_0,A_7) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_96,plain,(
    ! [A_56,B_57] :
      ( k3_xboole_0(A_56,B_57) = A_56
      | ~ r1_tarski(A_56,B_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_102,plain,(
    ! [A_60] : k3_xboole_0(k1_xboole_0,A_60) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_8,c_96])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_107,plain,(
    ! [A_60] : k3_xboole_0(A_60,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_102,c_2])).

tff(c_282,plain,(
    ! [A_80,B_81] : k5_xboole_0(A_80,k3_xboole_0(A_80,B_81)) = k4_xboole_0(A_80,B_81) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_305,plain,(
    ! [A_60] : k5_xboole_0(A_60,k1_xboole_0) = k4_xboole_0(A_60,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_107,c_282])).

tff(c_321,plain,(
    ! [A_60] : k5_xboole_0(A_60,k1_xboole_0) = A_60 ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_305])).

tff(c_18,plain,(
    ! [A_13] : k2_tarski(A_13,A_13) = k1_tarski(A_13) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_193,plain,(
    ! [A_67,B_68] : k4_xboole_0(k1_tarski(A_67),k2_tarski(A_67,B_68)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_200,plain,(
    ! [A_13] : k4_xboole_0(k1_tarski(A_13),k1_tarski(A_13)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_193])).

tff(c_224,plain,(
    ! [A_74,B_75] : k5_xboole_0(A_74,k4_xboole_0(B_75,A_74)) = k2_xboole_0(A_74,B_75) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_233,plain,(
    ! [A_13] : k2_xboole_0(k1_tarski(A_13),k1_tarski(A_13)) = k5_xboole_0(k1_tarski(A_13),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_200,c_224])).

tff(c_510,plain,(
    ! [A_104] : k2_xboole_0(k1_tarski(A_104),k1_tarski(A_104)) = k1_tarski(A_104) ),
    inference(demodulation,[status(thm),theory(equality)],[c_321,c_233])).

tff(c_164,plain,(
    ! [A_64,B_65] : k3_tarski(k2_tarski(A_64,B_65)) = k2_xboole_0(A_64,B_65) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_173,plain,(
    ! [A_13] : k3_tarski(k1_tarski(A_13)) = k2_xboole_0(A_13,A_13) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_164])).

tff(c_516,plain,(
    ! [A_104] : k3_tarski(k1_tarski(k1_tarski(A_104))) = k1_tarski(A_104) ),
    inference(superposition,[status(thm),theory(equality)],[c_510,c_173])).

tff(c_159,plain,(
    ! [A_62,B_63] :
      ( r1_xboole_0(k1_tarski(A_62),k1_tarski(B_63))
      | B_63 = A_62 ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_12,plain,(
    ! [A_9,B_10] :
      ( k4_xboole_0(A_9,B_10) = A_9
      | ~ r1_xboole_0(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_479,plain,(
    ! [A_97,B_98] :
      ( k4_xboole_0(k1_tarski(A_97),k1_tarski(B_98)) = k1_tarski(A_97)
      | B_98 = A_97 ) ),
    inference(resolution,[status(thm)],[c_159,c_12])).

tff(c_16,plain,(
    ! [A_11,B_12] : k5_xboole_0(A_11,k4_xboole_0(B_12,A_11)) = k2_xboole_0(A_11,B_12) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_571,plain,(
    ! [B_116,A_117] :
      ( k5_xboole_0(k1_tarski(B_116),k1_tarski(A_117)) = k2_xboole_0(k1_tarski(B_116),k1_tarski(A_117))
      | B_116 = A_117 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_479,c_16])).

tff(c_40,plain,(
    ! [A_49,B_50] :
      ( k5_xboole_0(k1_tarski(A_49),k1_tarski(B_50)) = k2_tarski(A_49,B_50)
      | B_50 = A_49 ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_597,plain,(
    ! [B_118,A_119] :
      ( k2_xboole_0(k1_tarski(B_118),k1_tarski(A_119)) = k2_tarski(B_118,A_119)
      | B_118 = A_119
      | B_118 = A_119 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_571,c_40])).

tff(c_32,plain,(
    ! [A_41,B_42] : k3_tarski(k2_tarski(A_41,B_42)) = k2_xboole_0(A_41,B_42) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_42,plain,(
    k3_tarski(k2_tarski(k1_tarski('#skF_1'),k1_tarski('#skF_2'))) != k2_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_43,plain,(
    k2_xboole_0(k1_tarski('#skF_1'),k1_tarski('#skF_2')) != k2_tarski('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_42])).

tff(c_627,plain,(
    '#skF_2' = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_597,c_43])).

tff(c_633,plain,(
    k2_xboole_0(k1_tarski('#skF_1'),k1_tarski('#skF_1')) != k2_tarski('#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_627,c_627,c_43])).

tff(c_636,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_516,c_173,c_18,c_633])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n003.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 13:52:42 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.22/1.29  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.22/1.30  
% 2.22/1.30  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.22/1.30  %$ r1_xboole_0 > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1
% 2.22/1.30  
% 2.22/1.30  %Foreground sorts:
% 2.22/1.30  
% 2.22/1.30  
% 2.22/1.30  %Background operators:
% 2.22/1.30  
% 2.22/1.30  
% 2.22/1.30  %Foreground operators:
% 2.22/1.30  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.22/1.30  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.22/1.30  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.22/1.30  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.22/1.30  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.22/1.30  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.22/1.30  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.22/1.30  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.22/1.30  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.22/1.30  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.22/1.30  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.22/1.30  tff('#skF_2', type, '#skF_2': $i).
% 2.22/1.30  tff('#skF_1', type, '#skF_1': $i).
% 2.22/1.30  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.22/1.30  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.22/1.30  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.22/1.30  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.22/1.30  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.22/1.30  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.22/1.30  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.22/1.30  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.22/1.30  
% 2.22/1.31  tff(f_37, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 2.22/1.31  tff(f_35, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.22/1.31  tff(f_33, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 2.22/1.31  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 2.22/1.31  tff(f_29, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 2.22/1.31  tff(f_45, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 2.22/1.31  tff(f_68, axiom, (![A, B]: (k4_xboole_0(k1_tarski(A), k2_tarski(A, B)) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_zfmisc_1)).
% 2.22/1.31  tff(f_43, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_xboole_1)).
% 2.22/1.31  tff(f_59, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 2.22/1.31  tff(f_64, axiom, (![A, B]: (~(A = B) => r1_xboole_0(k1_tarski(A), k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_zfmisc_1)).
% 2.22/1.31  tff(f_41, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_xboole_1)).
% 2.22/1.31  tff(f_73, axiom, (![A, B]: (~(A = B) => (k5_xboole_0(k1_tarski(A), k1_tarski(B)) = k2_tarski(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_zfmisc_1)).
% 2.22/1.31  tff(f_76, negated_conjecture, ~(![A, B]: (k3_tarski(k2_tarski(k1_tarski(A), k1_tarski(B))) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t32_zfmisc_1)).
% 2.22/1.31  tff(c_10, plain, (![A_8]: (k4_xboole_0(A_8, k1_xboole_0)=A_8)), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.22/1.31  tff(c_8, plain, (![A_7]: (r1_tarski(k1_xboole_0, A_7))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.22/1.31  tff(c_96, plain, (![A_56, B_57]: (k3_xboole_0(A_56, B_57)=A_56 | ~r1_tarski(A_56, B_57))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.22/1.31  tff(c_102, plain, (![A_60]: (k3_xboole_0(k1_xboole_0, A_60)=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_96])).
% 2.22/1.31  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.22/1.31  tff(c_107, plain, (![A_60]: (k3_xboole_0(A_60, k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_102, c_2])).
% 2.22/1.31  tff(c_282, plain, (![A_80, B_81]: (k5_xboole_0(A_80, k3_xboole_0(A_80, B_81))=k4_xboole_0(A_80, B_81))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.22/1.31  tff(c_305, plain, (![A_60]: (k5_xboole_0(A_60, k1_xboole_0)=k4_xboole_0(A_60, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_107, c_282])).
% 2.22/1.31  tff(c_321, plain, (![A_60]: (k5_xboole_0(A_60, k1_xboole_0)=A_60)), inference(demodulation, [status(thm), theory('equality')], [c_10, c_305])).
% 2.22/1.31  tff(c_18, plain, (![A_13]: (k2_tarski(A_13, A_13)=k1_tarski(A_13))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.22/1.31  tff(c_193, plain, (![A_67, B_68]: (k4_xboole_0(k1_tarski(A_67), k2_tarski(A_67, B_68))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.22/1.31  tff(c_200, plain, (![A_13]: (k4_xboole_0(k1_tarski(A_13), k1_tarski(A_13))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_18, c_193])).
% 2.22/1.31  tff(c_224, plain, (![A_74, B_75]: (k5_xboole_0(A_74, k4_xboole_0(B_75, A_74))=k2_xboole_0(A_74, B_75))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.22/1.31  tff(c_233, plain, (![A_13]: (k2_xboole_0(k1_tarski(A_13), k1_tarski(A_13))=k5_xboole_0(k1_tarski(A_13), k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_200, c_224])).
% 2.22/1.31  tff(c_510, plain, (![A_104]: (k2_xboole_0(k1_tarski(A_104), k1_tarski(A_104))=k1_tarski(A_104))), inference(demodulation, [status(thm), theory('equality')], [c_321, c_233])).
% 2.22/1.31  tff(c_164, plain, (![A_64, B_65]: (k3_tarski(k2_tarski(A_64, B_65))=k2_xboole_0(A_64, B_65))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.22/1.31  tff(c_173, plain, (![A_13]: (k3_tarski(k1_tarski(A_13))=k2_xboole_0(A_13, A_13))), inference(superposition, [status(thm), theory('equality')], [c_18, c_164])).
% 2.22/1.31  tff(c_516, plain, (![A_104]: (k3_tarski(k1_tarski(k1_tarski(A_104)))=k1_tarski(A_104))), inference(superposition, [status(thm), theory('equality')], [c_510, c_173])).
% 2.22/1.31  tff(c_159, plain, (![A_62, B_63]: (r1_xboole_0(k1_tarski(A_62), k1_tarski(B_63)) | B_63=A_62)), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.22/1.31  tff(c_12, plain, (![A_9, B_10]: (k4_xboole_0(A_9, B_10)=A_9 | ~r1_xboole_0(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.22/1.31  tff(c_479, plain, (![A_97, B_98]: (k4_xboole_0(k1_tarski(A_97), k1_tarski(B_98))=k1_tarski(A_97) | B_98=A_97)), inference(resolution, [status(thm)], [c_159, c_12])).
% 2.22/1.31  tff(c_16, plain, (![A_11, B_12]: (k5_xboole_0(A_11, k4_xboole_0(B_12, A_11))=k2_xboole_0(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.22/1.31  tff(c_571, plain, (![B_116, A_117]: (k5_xboole_0(k1_tarski(B_116), k1_tarski(A_117))=k2_xboole_0(k1_tarski(B_116), k1_tarski(A_117)) | B_116=A_117)), inference(superposition, [status(thm), theory('equality')], [c_479, c_16])).
% 2.22/1.31  tff(c_40, plain, (![A_49, B_50]: (k5_xboole_0(k1_tarski(A_49), k1_tarski(B_50))=k2_tarski(A_49, B_50) | B_50=A_49)), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.22/1.31  tff(c_597, plain, (![B_118, A_119]: (k2_xboole_0(k1_tarski(B_118), k1_tarski(A_119))=k2_tarski(B_118, A_119) | B_118=A_119 | B_118=A_119)), inference(superposition, [status(thm), theory('equality')], [c_571, c_40])).
% 2.22/1.31  tff(c_32, plain, (![A_41, B_42]: (k3_tarski(k2_tarski(A_41, B_42))=k2_xboole_0(A_41, B_42))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.22/1.31  tff(c_42, plain, (k3_tarski(k2_tarski(k1_tarski('#skF_1'), k1_tarski('#skF_2')))!=k2_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.22/1.31  tff(c_43, plain, (k2_xboole_0(k1_tarski('#skF_1'), k1_tarski('#skF_2'))!=k2_tarski('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_42])).
% 2.22/1.31  tff(c_627, plain, ('#skF_2'='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_597, c_43])).
% 2.22/1.31  tff(c_633, plain, (k2_xboole_0(k1_tarski('#skF_1'), k1_tarski('#skF_1'))!=k2_tarski('#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_627, c_627, c_43])).
% 2.22/1.31  tff(c_636, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_516, c_173, c_18, c_633])).
% 2.22/1.31  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.22/1.31  
% 2.22/1.31  Inference rules
% 2.22/1.31  ----------------------
% 2.22/1.31  #Ref     : 0
% 2.22/1.31  #Sup     : 136
% 2.22/1.31  #Fact    : 0
% 2.22/1.31  #Define  : 0
% 2.22/1.31  #Split   : 0
% 2.22/1.31  #Chain   : 0
% 2.22/1.31  #Close   : 0
% 2.22/1.31  
% 2.22/1.31  Ordering : KBO
% 2.22/1.31  
% 2.22/1.31  Simplification rules
% 2.22/1.31  ----------------------
% 2.22/1.31  #Subsume      : 0
% 2.22/1.31  #Demod        : 66
% 2.22/1.31  #Tautology    : 116
% 2.22/1.31  #SimpNegUnit  : 0
% 2.22/1.31  #BackRed      : 1
% 2.22/1.31  
% 2.22/1.31  #Partial instantiations: 0
% 2.22/1.31  #Strategies tried      : 1
% 2.22/1.31  
% 2.22/1.31  Timing (in seconds)
% 2.22/1.31  ----------------------
% 2.22/1.32  Preprocessing        : 0.32
% 2.22/1.32  Parsing              : 0.18
% 2.22/1.32  CNF conversion       : 0.02
% 2.22/1.32  Main loop            : 0.24
% 2.22/1.32  Inferencing          : 0.10
% 2.22/1.32  Reduction            : 0.09
% 2.22/1.32  Demodulation         : 0.07
% 2.22/1.32  BG Simplification    : 0.02
% 2.22/1.32  Subsumption          : 0.03
% 2.22/1.32  Abstraction          : 0.02
% 2.22/1.32  MUC search           : 0.00
% 2.22/1.32  Cooper               : 0.00
% 2.22/1.32  Total                : 0.59
% 2.22/1.32  Index Insertion      : 0.00
% 2.22/1.32  Index Deletion       : 0.00
% 2.22/1.32  Index Matching       : 0.00
% 2.22/1.32  BG Taut test         : 0.00
%------------------------------------------------------------------------------
