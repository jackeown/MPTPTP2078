%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:49:47 EST 2020

% Result     : Theorem 2.46s
% Output     : CNFRefutation 2.78s
% Verified   : 
% Statistics : Number of formulae       :   65 (  98 expanded)
%              Number of leaves         :   34 (  48 expanded)
%              Depth                    :    7
%              Number of atoms          :   58 ( 101 expanded)
%              Number of equality atoms :   44 (  83 expanded)
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

tff(f_39,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_41,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_37,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_49,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_65,axiom,(
    ! [A,B] : r1_tarski(k1_tarski(A),k2_tarski(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_zfmisc_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_47,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_63,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_70,axiom,(
    ! [A,B] :
      ( A != B
     => r1_xboole_0(k1_tarski(A),k1_tarski(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_zfmisc_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_75,axiom,(
    ! [A,B] :
      ( A != B
     => k5_xboole_0(k1_tarski(A),k1_tarski(B)) = k2_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_zfmisc_1)).

tff(f_78,negated_conjecture,(
    ~ ! [A,B] : k3_tarski(k2_tarski(k1_tarski(A),k1_tarski(B))) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_zfmisc_1)).

tff(c_14,plain,(
    ! [A_9] : k4_xboole_0(A_9,k1_xboole_0) = A_9 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_16,plain,(
    ! [A_10] : r1_xboole_0(A_10,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_142,plain,(
    ! [A_70,B_71] :
      ( k3_xboole_0(A_70,B_71) = k1_xboole_0
      | ~ r1_xboole_0(A_70,B_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_154,plain,(
    ! [A_10] : k3_xboole_0(A_10,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_16,c_142])).

tff(c_270,plain,(
    ! [A_83,B_84] : k5_xboole_0(A_83,k3_xboole_0(A_83,B_84)) = k4_xboole_0(A_83,B_84) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_282,plain,(
    ! [A_10] : k5_xboole_0(A_10,k1_xboole_0) = k4_xboole_0(A_10,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_154,c_270])).

tff(c_291,plain,(
    ! [A_10] : k5_xboole_0(A_10,k1_xboole_0) = A_10 ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_282])).

tff(c_24,plain,(
    ! [A_15] : k2_tarski(A_15,A_15) = k1_tarski(A_15) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_100,plain,(
    ! [A_56,B_57] : r1_tarski(k1_tarski(A_56),k2_tarski(A_56,B_57)) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_109,plain,(
    ! [A_60] : r1_tarski(k1_tarski(A_60),k1_tarski(A_60)) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_100])).

tff(c_10,plain,(
    ! [A_5,B_6] :
      ( k4_xboole_0(A_5,B_6) = k1_xboole_0
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_113,plain,(
    ! [A_60] : k4_xboole_0(k1_tarski(A_60),k1_tarski(A_60)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_109,c_10])).

tff(c_292,plain,(
    ! [A_85,B_86] : k5_xboole_0(A_85,k4_xboole_0(B_86,A_85)) = k2_xboole_0(A_85,B_86) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_304,plain,(
    ! [A_60] : k2_xboole_0(k1_tarski(A_60),k1_tarski(A_60)) = k5_xboole_0(k1_tarski(A_60),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_113,c_292])).

tff(c_621,plain,(
    ! [A_116] : k2_xboole_0(k1_tarski(A_116),k1_tarski(A_116)) = k1_tarski(A_116) ),
    inference(demodulation,[status(thm),theory(equality)],[c_291,c_304])).

tff(c_220,plain,(
    ! [A_76,B_77] : k3_tarski(k2_tarski(A_76,B_77)) = k2_xboole_0(A_76,B_77) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_229,plain,(
    ! [A_15] : k3_tarski(k1_tarski(A_15)) = k2_xboole_0(A_15,A_15) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_220])).

tff(c_627,plain,(
    ! [A_116] : k3_tarski(k1_tarski(k1_tarski(A_116))) = k1_tarski(A_116) ),
    inference(superposition,[status(thm),theory(equality)],[c_621,c_229])).

tff(c_42,plain,(
    ! [A_47,B_48] :
      ( r1_xboole_0(k1_tarski(A_47),k1_tarski(B_48))
      | B_48 = A_47 ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_122,plain,(
    ! [A_64,B_65] :
      ( k4_xboole_0(A_64,B_65) = A_64
      | ~ r1_xboole_0(A_64,B_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_571,plain,(
    ! [A_108,B_109] :
      ( k4_xboole_0(k1_tarski(A_108),k1_tarski(B_109)) = k1_tarski(A_108)
      | B_109 = A_108 ) ),
    inference(resolution,[status(thm)],[c_42,c_122])).

tff(c_22,plain,(
    ! [A_13,B_14] : k5_xboole_0(A_13,k4_xboole_0(B_14,A_13)) = k2_xboole_0(A_13,B_14) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_802,plain,(
    ! [B_140,A_141] :
      ( k5_xboole_0(k1_tarski(B_140),k1_tarski(A_141)) = k2_xboole_0(k1_tarski(B_140),k1_tarski(A_141))
      | B_140 = A_141 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_571,c_22])).

tff(c_44,plain,(
    ! [A_49,B_50] :
      ( k5_xboole_0(k1_tarski(A_49),k1_tarski(B_50)) = k2_tarski(A_49,B_50)
      | B_50 = A_49 ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_856,plain,(
    ! [B_144,A_145] :
      ( k2_xboole_0(k1_tarski(B_144),k1_tarski(A_145)) = k2_tarski(B_144,A_145)
      | B_144 = A_145
      | B_144 = A_145 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_802,c_44])).

tff(c_38,plain,(
    ! [A_43,B_44] : k3_tarski(k2_tarski(A_43,B_44)) = k2_xboole_0(A_43,B_44) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_46,plain,(
    k3_tarski(k2_tarski(k1_tarski('#skF_1'),k1_tarski('#skF_2'))) != k2_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_47,plain,(
    k2_xboole_0(k1_tarski('#skF_1'),k1_tarski('#skF_2')) != k2_tarski('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_46])).

tff(c_886,plain,(
    '#skF_2' = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_856,c_47])).

tff(c_892,plain,(
    k2_xboole_0(k1_tarski('#skF_1'),k1_tarski('#skF_1')) != k2_tarski('#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_886,c_886,c_47])).

tff(c_895,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_627,c_229,c_24,c_892])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n008.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 15:39:30 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.46/1.34  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.78/1.34  
% 2.78/1.34  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.78/1.34  %$ r1_xboole_0 > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1
% 2.78/1.34  
% 2.78/1.34  %Foreground sorts:
% 2.78/1.34  
% 2.78/1.34  
% 2.78/1.34  %Background operators:
% 2.78/1.34  
% 2.78/1.34  
% 2.78/1.34  %Foreground operators:
% 2.78/1.34  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.78/1.34  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.78/1.34  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.78/1.34  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.78/1.34  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.78/1.34  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.78/1.34  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.78/1.34  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.78/1.34  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.78/1.34  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.78/1.34  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.78/1.34  tff('#skF_2', type, '#skF_2': $i).
% 2.78/1.34  tff('#skF_1', type, '#skF_1': $i).
% 2.78/1.34  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.78/1.34  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.78/1.34  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.78/1.34  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.78/1.34  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.78/1.34  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.78/1.34  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.78/1.34  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.78/1.34  
% 2.78/1.36  tff(f_39, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 2.78/1.36  tff(f_41, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 2.78/1.36  tff(f_31, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 2.78/1.36  tff(f_37, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 2.78/1.36  tff(f_49, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 2.78/1.36  tff(f_65, axiom, (![A, B]: r1_tarski(k1_tarski(A), k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_zfmisc_1)).
% 2.78/1.36  tff(f_35, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 2.78/1.36  tff(f_47, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_xboole_1)).
% 2.78/1.36  tff(f_63, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 2.78/1.36  tff(f_70, axiom, (![A, B]: (~(A = B) => r1_xboole_0(k1_tarski(A), k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_zfmisc_1)).
% 2.78/1.36  tff(f_45, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_xboole_1)).
% 2.78/1.36  tff(f_75, axiom, (![A, B]: (~(A = B) => (k5_xboole_0(k1_tarski(A), k1_tarski(B)) = k2_tarski(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_zfmisc_1)).
% 2.78/1.36  tff(f_78, negated_conjecture, ~(![A, B]: (k3_tarski(k2_tarski(k1_tarski(A), k1_tarski(B))) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t32_zfmisc_1)).
% 2.78/1.36  tff(c_14, plain, (![A_9]: (k4_xboole_0(A_9, k1_xboole_0)=A_9)), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.78/1.36  tff(c_16, plain, (![A_10]: (r1_xboole_0(A_10, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.78/1.36  tff(c_142, plain, (![A_70, B_71]: (k3_xboole_0(A_70, B_71)=k1_xboole_0 | ~r1_xboole_0(A_70, B_71))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.78/1.36  tff(c_154, plain, (![A_10]: (k3_xboole_0(A_10, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_16, c_142])).
% 2.78/1.36  tff(c_270, plain, (![A_83, B_84]: (k5_xboole_0(A_83, k3_xboole_0(A_83, B_84))=k4_xboole_0(A_83, B_84))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.78/1.36  tff(c_282, plain, (![A_10]: (k5_xboole_0(A_10, k1_xboole_0)=k4_xboole_0(A_10, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_154, c_270])).
% 2.78/1.36  tff(c_291, plain, (![A_10]: (k5_xboole_0(A_10, k1_xboole_0)=A_10)), inference(demodulation, [status(thm), theory('equality')], [c_14, c_282])).
% 2.78/1.36  tff(c_24, plain, (![A_15]: (k2_tarski(A_15, A_15)=k1_tarski(A_15))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.78/1.36  tff(c_100, plain, (![A_56, B_57]: (r1_tarski(k1_tarski(A_56), k2_tarski(A_56, B_57)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.78/1.36  tff(c_109, plain, (![A_60]: (r1_tarski(k1_tarski(A_60), k1_tarski(A_60)))), inference(superposition, [status(thm), theory('equality')], [c_24, c_100])).
% 2.78/1.36  tff(c_10, plain, (![A_5, B_6]: (k4_xboole_0(A_5, B_6)=k1_xboole_0 | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.78/1.36  tff(c_113, plain, (![A_60]: (k4_xboole_0(k1_tarski(A_60), k1_tarski(A_60))=k1_xboole_0)), inference(resolution, [status(thm)], [c_109, c_10])).
% 2.78/1.36  tff(c_292, plain, (![A_85, B_86]: (k5_xboole_0(A_85, k4_xboole_0(B_86, A_85))=k2_xboole_0(A_85, B_86))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.78/1.36  tff(c_304, plain, (![A_60]: (k2_xboole_0(k1_tarski(A_60), k1_tarski(A_60))=k5_xboole_0(k1_tarski(A_60), k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_113, c_292])).
% 2.78/1.36  tff(c_621, plain, (![A_116]: (k2_xboole_0(k1_tarski(A_116), k1_tarski(A_116))=k1_tarski(A_116))), inference(demodulation, [status(thm), theory('equality')], [c_291, c_304])).
% 2.78/1.36  tff(c_220, plain, (![A_76, B_77]: (k3_tarski(k2_tarski(A_76, B_77))=k2_xboole_0(A_76, B_77))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.78/1.36  tff(c_229, plain, (![A_15]: (k3_tarski(k1_tarski(A_15))=k2_xboole_0(A_15, A_15))), inference(superposition, [status(thm), theory('equality')], [c_24, c_220])).
% 2.78/1.36  tff(c_627, plain, (![A_116]: (k3_tarski(k1_tarski(k1_tarski(A_116)))=k1_tarski(A_116))), inference(superposition, [status(thm), theory('equality')], [c_621, c_229])).
% 2.78/1.36  tff(c_42, plain, (![A_47, B_48]: (r1_xboole_0(k1_tarski(A_47), k1_tarski(B_48)) | B_48=A_47)), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.78/1.36  tff(c_122, plain, (![A_64, B_65]: (k4_xboole_0(A_64, B_65)=A_64 | ~r1_xboole_0(A_64, B_65))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.78/1.36  tff(c_571, plain, (![A_108, B_109]: (k4_xboole_0(k1_tarski(A_108), k1_tarski(B_109))=k1_tarski(A_108) | B_109=A_108)), inference(resolution, [status(thm)], [c_42, c_122])).
% 2.78/1.36  tff(c_22, plain, (![A_13, B_14]: (k5_xboole_0(A_13, k4_xboole_0(B_14, A_13))=k2_xboole_0(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.78/1.36  tff(c_802, plain, (![B_140, A_141]: (k5_xboole_0(k1_tarski(B_140), k1_tarski(A_141))=k2_xboole_0(k1_tarski(B_140), k1_tarski(A_141)) | B_140=A_141)), inference(superposition, [status(thm), theory('equality')], [c_571, c_22])).
% 2.78/1.36  tff(c_44, plain, (![A_49, B_50]: (k5_xboole_0(k1_tarski(A_49), k1_tarski(B_50))=k2_tarski(A_49, B_50) | B_50=A_49)), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.78/1.36  tff(c_856, plain, (![B_144, A_145]: (k2_xboole_0(k1_tarski(B_144), k1_tarski(A_145))=k2_tarski(B_144, A_145) | B_144=A_145 | B_144=A_145)), inference(superposition, [status(thm), theory('equality')], [c_802, c_44])).
% 2.78/1.36  tff(c_38, plain, (![A_43, B_44]: (k3_tarski(k2_tarski(A_43, B_44))=k2_xboole_0(A_43, B_44))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.78/1.36  tff(c_46, plain, (k3_tarski(k2_tarski(k1_tarski('#skF_1'), k1_tarski('#skF_2')))!=k2_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.78/1.36  tff(c_47, plain, (k2_xboole_0(k1_tarski('#skF_1'), k1_tarski('#skF_2'))!=k2_tarski('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_46])).
% 2.78/1.36  tff(c_886, plain, ('#skF_2'='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_856, c_47])).
% 2.78/1.36  tff(c_892, plain, (k2_xboole_0(k1_tarski('#skF_1'), k1_tarski('#skF_1'))!=k2_tarski('#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_886, c_886, c_47])).
% 2.78/1.36  tff(c_895, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_627, c_229, c_24, c_892])).
% 2.78/1.36  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.78/1.36  
% 2.78/1.36  Inference rules
% 2.78/1.36  ----------------------
% 2.78/1.36  #Ref     : 0
% 2.78/1.36  #Sup     : 194
% 2.78/1.36  #Fact    : 0
% 2.78/1.36  #Define  : 0
% 2.78/1.36  #Split   : 0
% 2.78/1.36  #Chain   : 0
% 2.78/1.36  #Close   : 0
% 2.78/1.36  
% 2.78/1.36  Ordering : KBO
% 2.78/1.36  
% 2.78/1.36  Simplification rules
% 2.78/1.36  ----------------------
% 2.78/1.36  #Subsume      : 12
% 2.78/1.36  #Demod        : 84
% 2.78/1.36  #Tautology    : 145
% 2.78/1.36  #SimpNegUnit  : 0
% 2.78/1.36  #BackRed      : 1
% 2.78/1.36  
% 2.78/1.36  #Partial instantiations: 0
% 2.78/1.36  #Strategies tried      : 1
% 2.78/1.36  
% 2.78/1.36  Timing (in seconds)
% 2.78/1.36  ----------------------
% 2.78/1.36  Preprocessing        : 0.30
% 2.78/1.36  Parsing              : 0.16
% 2.78/1.36  CNF conversion       : 0.02
% 2.78/1.36  Main loop            : 0.31
% 2.78/1.36  Inferencing          : 0.13
% 2.78/1.36  Reduction            : 0.11
% 2.78/1.36  Demodulation         : 0.08
% 2.78/1.36  BG Simplification    : 0.02
% 2.78/1.36  Subsumption          : 0.04
% 2.78/1.36  Abstraction          : 0.02
% 2.78/1.36  MUC search           : 0.00
% 2.78/1.36  Cooper               : 0.00
% 2.78/1.36  Total                : 0.65
% 2.78/1.36  Index Insertion      : 0.00
% 2.78/1.36  Index Deletion       : 0.00
% 2.78/1.36  Index Matching       : 0.00
% 2.78/1.36  BG Taut test         : 0.00
%------------------------------------------------------------------------------
