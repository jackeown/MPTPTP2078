%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:55:25 EST 2020

% Result     : Theorem 2.10s
% Output     : CNFRefutation 2.33s
% Verified   : 
% Statistics : Number of formulae       :   61 (  86 expanded)
%              Number of leaves         :   34 (  45 expanded)
%              Depth                    :   10
%              Number of atoms          :   41 (  66 expanded)
%              Number of equality atoms :   36 (  61 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m1_subset_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k2_subset_1 > k1_zfmisc_1 > k1_subset_1 > k1_xboole_0 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_subset_1,type,(
    k1_subset_1: $i > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_37,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

tff(f_39,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k5_xboole_0(k5_xboole_0(A,B),k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_xboole_1)).

tff(f_35,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_63,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_61,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_33,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

tff(f_31,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_55,axiom,(
    ! [A] : k1_subset_1(A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_subset_1)).

tff(f_57,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_66,negated_conjecture,(
    ~ ! [A] : k2_subset_1(A) = k3_subset_1(A,k1_subset_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_subset_1)).

tff(c_12,plain,(
    ! [A_11] : k5_xboole_0(A_11,A_11) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_4,plain,(
    ! [A_3] : k3_xboole_0(A_3,A_3) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_2,plain,(
    ! [A_1] : k2_xboole_0(A_1,A_1) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_171,plain,(
    ! [A_68,B_69] : k5_xboole_0(k5_xboole_0(A_68,B_69),k2_xboole_0(A_68,B_69)) = k3_xboole_0(A_68,B_69) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_189,plain,(
    ! [A_11] : k5_xboole_0(k1_xboole_0,k2_xboole_0(A_11,A_11)) = k3_xboole_0(A_11,A_11) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_171])).

tff(c_198,plain,(
    ! [A_11] : k5_xboole_0(k1_xboole_0,A_11) = A_11 ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_2,c_189])).

tff(c_235,plain,(
    ! [A_71,B_72,C_73] : k5_xboole_0(k5_xboole_0(A_71,B_72),C_73) = k5_xboole_0(A_71,k5_xboole_0(B_72,C_73)) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_281,plain,(
    ! [A_11,C_73] : k5_xboole_0(A_11,k5_xboole_0(A_11,C_73)) = k5_xboole_0(k1_xboole_0,C_73) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_235])).

tff(c_293,plain,(
    ! [A_74,C_75] : k5_xboole_0(A_74,k5_xboole_0(A_74,C_75)) = C_75 ),
    inference(demodulation,[status(thm),theory(equality)],[c_198,c_281])).

tff(c_342,plain,(
    ! [A_11] : k5_xboole_0(A_11,k1_xboole_0) = A_11 ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_293])).

tff(c_36,plain,(
    ! [A_47] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_47)) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_149,plain,(
    ! [A_65,B_66] :
      ( k4_xboole_0(A_65,B_66) = k3_subset_1(A_65,B_66)
      | ~ m1_subset_1(B_66,k1_zfmisc_1(A_65)) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_153,plain,(
    ! [A_47] : k4_xboole_0(A_47,k1_xboole_0) = k3_subset_1(A_47,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_36,c_149])).

tff(c_8,plain,(
    ! [A_7] : k2_xboole_0(A_7,k1_xboole_0) = A_7 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_353,plain,(
    ! [A_76] : k5_xboole_0(A_76,k1_xboole_0) = A_76 ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_293])).

tff(c_14,plain,(
    ! [A_12,B_13] : k5_xboole_0(k5_xboole_0(A_12,B_13),k2_xboole_0(A_12,B_13)) = k3_xboole_0(A_12,B_13) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_373,plain,(
    ! [A_76] : k5_xboole_0(A_76,k2_xboole_0(A_76,k1_xboole_0)) = k3_xboole_0(A_76,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_353,c_14])).

tff(c_404,plain,(
    ! [A_77] : k3_xboole_0(A_77,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_8,c_373])).

tff(c_6,plain,(
    ! [A_5,B_6] : k5_xboole_0(A_5,k3_xboole_0(A_5,B_6)) = k4_xboole_0(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_409,plain,(
    ! [A_77] : k5_xboole_0(A_77,k1_xboole_0) = k4_xboole_0(A_77,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_404,c_6])).

tff(c_421,plain,(
    ! [A_77] : k3_subset_1(A_77,k1_xboole_0) = A_77 ),
    inference(demodulation,[status(thm),theory(equality)],[c_342,c_153,c_409])).

tff(c_30,plain,(
    ! [A_43] : k1_subset_1(A_43) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_32,plain,(
    ! [A_44] : k2_subset_1(A_44) = A_44 ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_38,plain,(
    k3_subset_1('#skF_1',k1_subset_1('#skF_1')) != k2_subset_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_39,plain,(
    k3_subset_1('#skF_1',k1_subset_1('#skF_1')) != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_38])).

tff(c_40,plain,(
    k3_subset_1('#skF_1',k1_xboole_0) != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_39])).

tff(c_429,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_421,c_40])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n023.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 14:15:35 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.10/1.31  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.10/1.32  
% 2.10/1.32  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.10/1.32  %$ m1_subset_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k2_subset_1 > k1_zfmisc_1 > k1_subset_1 > k1_xboole_0 > #skF_1
% 2.10/1.32  
% 2.10/1.32  %Foreground sorts:
% 2.10/1.32  
% 2.10/1.32  
% 2.10/1.32  %Background operators:
% 2.10/1.32  
% 2.10/1.32  
% 2.10/1.32  %Foreground operators:
% 2.10/1.32  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.10/1.32  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.10/1.32  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.10/1.32  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.10/1.32  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.10/1.32  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.10/1.32  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.10/1.32  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 2.10/1.32  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.10/1.32  tff('#skF_1', type, '#skF_1': $i).
% 2.10/1.32  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.10/1.32  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.10/1.32  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.10/1.32  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.10/1.32  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.10/1.32  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.10/1.32  tff(k1_subset_1, type, k1_subset_1: $i > $i).
% 2.10/1.32  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.10/1.32  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.10/1.32  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.10/1.32  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 2.10/1.32  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.10/1.32  
% 2.33/1.33  tff(f_37, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t92_xboole_1)).
% 2.33/1.33  tff(f_29, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 2.33/1.33  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k2_xboole_0)).
% 2.33/1.33  tff(f_39, axiom, (![A, B]: (k3_xboole_0(A, B) = k5_xboole_0(k5_xboole_0(A, B), k2_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t95_xboole_1)).
% 2.33/1.33  tff(f_35, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_xboole_1)).
% 2.33/1.33  tff(f_63, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 2.33/1.33  tff(f_61, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_subset_1)).
% 2.33/1.33  tff(f_33, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 2.33/1.33  tff(f_31, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 2.33/1.33  tff(f_55, axiom, (![A]: (k1_subset_1(A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_subset_1)).
% 2.33/1.33  tff(f_57, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 2.33/1.33  tff(f_66, negated_conjecture, ~(![A]: (k2_subset_1(A) = k3_subset_1(A, k1_subset_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t22_subset_1)).
% 2.33/1.33  tff(c_12, plain, (![A_11]: (k5_xboole_0(A_11, A_11)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.33/1.33  tff(c_4, plain, (![A_3]: (k3_xboole_0(A_3, A_3)=A_3)), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.33/1.33  tff(c_2, plain, (![A_1]: (k2_xboole_0(A_1, A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.33/1.33  tff(c_171, plain, (![A_68, B_69]: (k5_xboole_0(k5_xboole_0(A_68, B_69), k2_xboole_0(A_68, B_69))=k3_xboole_0(A_68, B_69))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.33/1.33  tff(c_189, plain, (![A_11]: (k5_xboole_0(k1_xboole_0, k2_xboole_0(A_11, A_11))=k3_xboole_0(A_11, A_11))), inference(superposition, [status(thm), theory('equality')], [c_12, c_171])).
% 2.33/1.33  tff(c_198, plain, (![A_11]: (k5_xboole_0(k1_xboole_0, A_11)=A_11)), inference(demodulation, [status(thm), theory('equality')], [c_4, c_2, c_189])).
% 2.33/1.33  tff(c_235, plain, (![A_71, B_72, C_73]: (k5_xboole_0(k5_xboole_0(A_71, B_72), C_73)=k5_xboole_0(A_71, k5_xboole_0(B_72, C_73)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.33/1.33  tff(c_281, plain, (![A_11, C_73]: (k5_xboole_0(A_11, k5_xboole_0(A_11, C_73))=k5_xboole_0(k1_xboole_0, C_73))), inference(superposition, [status(thm), theory('equality')], [c_12, c_235])).
% 2.33/1.33  tff(c_293, plain, (![A_74, C_75]: (k5_xboole_0(A_74, k5_xboole_0(A_74, C_75))=C_75)), inference(demodulation, [status(thm), theory('equality')], [c_198, c_281])).
% 2.33/1.33  tff(c_342, plain, (![A_11]: (k5_xboole_0(A_11, k1_xboole_0)=A_11)), inference(superposition, [status(thm), theory('equality')], [c_12, c_293])).
% 2.33/1.33  tff(c_36, plain, (![A_47]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_47)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.33/1.33  tff(c_149, plain, (![A_65, B_66]: (k4_xboole_0(A_65, B_66)=k3_subset_1(A_65, B_66) | ~m1_subset_1(B_66, k1_zfmisc_1(A_65)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.33/1.33  tff(c_153, plain, (![A_47]: (k4_xboole_0(A_47, k1_xboole_0)=k3_subset_1(A_47, k1_xboole_0))), inference(resolution, [status(thm)], [c_36, c_149])).
% 2.33/1.33  tff(c_8, plain, (![A_7]: (k2_xboole_0(A_7, k1_xboole_0)=A_7)), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.33/1.33  tff(c_353, plain, (![A_76]: (k5_xboole_0(A_76, k1_xboole_0)=A_76)), inference(superposition, [status(thm), theory('equality')], [c_12, c_293])).
% 2.33/1.33  tff(c_14, plain, (![A_12, B_13]: (k5_xboole_0(k5_xboole_0(A_12, B_13), k2_xboole_0(A_12, B_13))=k3_xboole_0(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.33/1.33  tff(c_373, plain, (![A_76]: (k5_xboole_0(A_76, k2_xboole_0(A_76, k1_xboole_0))=k3_xboole_0(A_76, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_353, c_14])).
% 2.33/1.33  tff(c_404, plain, (![A_77]: (k3_xboole_0(A_77, k1_xboole_0)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_12, c_8, c_373])).
% 2.33/1.33  tff(c_6, plain, (![A_5, B_6]: (k5_xboole_0(A_5, k3_xboole_0(A_5, B_6))=k4_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.33/1.33  tff(c_409, plain, (![A_77]: (k5_xboole_0(A_77, k1_xboole_0)=k4_xboole_0(A_77, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_404, c_6])).
% 2.33/1.33  tff(c_421, plain, (![A_77]: (k3_subset_1(A_77, k1_xboole_0)=A_77)), inference(demodulation, [status(thm), theory('equality')], [c_342, c_153, c_409])).
% 2.33/1.33  tff(c_30, plain, (![A_43]: (k1_subset_1(A_43)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.33/1.33  tff(c_32, plain, (![A_44]: (k2_subset_1(A_44)=A_44)), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.33/1.33  tff(c_38, plain, (k3_subset_1('#skF_1', k1_subset_1('#skF_1'))!=k2_subset_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.33/1.33  tff(c_39, plain, (k3_subset_1('#skF_1', k1_subset_1('#skF_1'))!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_32, c_38])).
% 2.33/1.33  tff(c_40, plain, (k3_subset_1('#skF_1', k1_xboole_0)!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_30, c_39])).
% 2.33/1.33  tff(c_429, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_421, c_40])).
% 2.33/1.33  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.33/1.33  
% 2.33/1.33  Inference rules
% 2.33/1.33  ----------------------
% 2.33/1.33  #Ref     : 0
% 2.33/1.33  #Sup     : 93
% 2.33/1.33  #Fact    : 0
% 2.33/1.33  #Define  : 0
% 2.33/1.33  #Split   : 0
% 2.33/1.33  #Chain   : 0
% 2.33/1.33  #Close   : 0
% 2.33/1.33  
% 2.33/1.33  Ordering : KBO
% 2.33/1.33  
% 2.33/1.33  Simplification rules
% 2.33/1.33  ----------------------
% 2.33/1.33  #Subsume      : 0
% 2.33/1.33  #Demod        : 35
% 2.33/1.33  #Tautology    : 64
% 2.33/1.34  #SimpNegUnit  : 0
% 2.33/1.34  #BackRed      : 2
% 2.33/1.34  
% 2.33/1.34  #Partial instantiations: 0
% 2.33/1.34  #Strategies tried      : 1
% 2.33/1.34  
% 2.33/1.34  Timing (in seconds)
% 2.33/1.34  ----------------------
% 2.33/1.34  Preprocessing        : 0.30
% 2.33/1.34  Parsing              : 0.16
% 2.33/1.34  CNF conversion       : 0.02
% 2.33/1.34  Main loop            : 0.20
% 2.33/1.34  Inferencing          : 0.07
% 2.33/1.34  Reduction            : 0.07
% 2.33/1.34  Demodulation         : 0.06
% 2.33/1.34  BG Simplification    : 0.02
% 2.33/1.34  Subsumption          : 0.02
% 2.33/1.34  Abstraction          : 0.02
% 2.33/1.34  MUC search           : 0.00
% 2.33/1.34  Cooper               : 0.00
% 2.33/1.34  Total                : 0.53
% 2.33/1.34  Index Insertion      : 0.00
% 2.33/1.34  Index Deletion       : 0.00
% 2.33/1.34  Index Matching       : 0.00
% 2.33/1.34  BG Taut test         : 0.00
%------------------------------------------------------------------------------
