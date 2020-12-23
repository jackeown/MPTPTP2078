%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:55:41 EST 2020

% Result     : Theorem 3.38s
% Output     : CNFRefutation 3.38s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 102 expanded)
%              Number of leaves         :   36 (  49 expanded)
%              Depth                    :    9
%              Number of atoms          :   75 ( 104 expanded)
%              Number of equality atoms :   48 (  65 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > m1_subset_1 > k3_enumset1 > k2_enumset1 > k4_subset_1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k2_subset_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_1

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

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff(k4_subset_1,type,(
    k4_subset_1: ( $i * $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

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

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_41,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_49,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_76,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => k4_subset_1(A,B,k2_subset_1(A)) = k2_subset_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_subset_1)).

tff(f_51,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_57,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_71,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_37,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_65,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,k3_subset_1(A,B)) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

tff(f_61,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k3_subset_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

tff(f_29,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_35,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

tff(c_16,plain,(
    ! [B_14,A_13] : k2_tarski(B_14,A_13) = k2_tarski(A_13,B_14) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_198,plain,(
    ! [A_57,B_58] : k3_tarski(k2_tarski(A_57,B_58)) = k2_xboole_0(A_57,B_58) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_236,plain,(
    ! [B_61,A_62] : k3_tarski(k2_tarski(B_61,A_62)) = k2_xboole_0(A_62,B_61) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_198])).

tff(c_24,plain,(
    ! [A_24,B_25] : k3_tarski(k2_tarski(A_24,B_25)) = k2_xboole_0(A_24,B_25) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_242,plain,(
    ! [B_61,A_62] : k2_xboole_0(B_61,A_62) = k2_xboole_0(A_62,B_61) ),
    inference(superposition,[status(thm),theory(equality)],[c_236,c_24])).

tff(c_40,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_26,plain,(
    ! [A_26] : k2_subset_1(A_26) = A_26 ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_30,plain,(
    ! [A_29] : m1_subset_1(k2_subset_1(A_29),k1_zfmisc_1(A_29)) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_42,plain,(
    ! [A_29] : m1_subset_1(A_29,k1_zfmisc_1(A_29)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_30])).

tff(c_871,plain,(
    ! [A_99,B_100,C_101] :
      ( k4_subset_1(A_99,B_100,C_101) = k2_xboole_0(B_100,C_101)
      | ~ m1_subset_1(C_101,k1_zfmisc_1(A_99))
      | ~ m1_subset_1(B_100,k1_zfmisc_1(A_99)) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_1415,plain,(
    ! [A_119,B_120] :
      ( k4_subset_1(A_119,B_120,A_119) = k2_xboole_0(B_120,A_119)
      | ~ m1_subset_1(B_120,k1_zfmisc_1(A_119)) ) ),
    inference(resolution,[status(thm)],[c_42,c_871])).

tff(c_1421,plain,(
    k4_subset_1('#skF_1','#skF_2','#skF_1') = k2_xboole_0('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_40,c_1415])).

tff(c_1429,plain,(
    k4_subset_1('#skF_1','#skF_2','#skF_1') = k2_xboole_0('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_242,c_1421])).

tff(c_38,plain,(
    k4_subset_1('#skF_1','#skF_2',k2_subset_1('#skF_1')) != k2_subset_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_41,plain,(
    k4_subset_1('#skF_1','#skF_2','#skF_1') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_26,c_38])).

tff(c_1548,plain,(
    k2_xboole_0('#skF_1','#skF_2') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1429,c_41])).

tff(c_578,plain,(
    ! [A_84,B_85] :
      ( k4_xboole_0(A_84,B_85) = k3_subset_1(A_84,B_85)
      | ~ m1_subset_1(B_85,k1_zfmisc_1(A_84)) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_589,plain,(
    k4_xboole_0('#skF_1','#skF_2') = k3_subset_1('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_40,c_578])).

tff(c_12,plain,(
    ! [A_9,B_10] : k4_xboole_0(A_9,k4_xboole_0(A_9,B_10)) = k3_xboole_0(A_9,B_10) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_640,plain,(
    k4_xboole_0('#skF_1',k3_subset_1('#skF_1','#skF_2')) = k3_xboole_0('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_589,c_12])).

tff(c_528,plain,(
    ! [A_81,B_82] :
      ( k3_subset_1(A_81,k3_subset_1(A_81,B_82)) = B_82
      | ~ m1_subset_1(B_82,k1_zfmisc_1(A_81)) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_536,plain,(
    k3_subset_1('#skF_1',k3_subset_1('#skF_1','#skF_2')) = '#skF_2' ),
    inference(resolution,[status(thm)],[c_40,c_528])).

tff(c_32,plain,(
    ! [A_30,B_31] :
      ( m1_subset_1(k3_subset_1(A_30,B_31),k1_zfmisc_1(A_30))
      | ~ m1_subset_1(B_31,k1_zfmisc_1(A_30)) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_1879,plain,(
    ! [A_131,B_132] :
      ( k4_xboole_0(A_131,k3_subset_1(A_131,B_132)) = k3_subset_1(A_131,k3_subset_1(A_131,B_132))
      | ~ m1_subset_1(B_132,k1_zfmisc_1(A_131)) ) ),
    inference(resolution,[status(thm)],[c_32,c_578])).

tff(c_1885,plain,(
    k4_xboole_0('#skF_1',k3_subset_1('#skF_1','#skF_2')) = k3_subset_1('#skF_1',k3_subset_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_40,c_1879])).

tff(c_1892,plain,(
    k3_xboole_0('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_640,c_536,c_1885])).

tff(c_2,plain,(
    ! [A_1] : k2_xboole_0(A_1,A_1) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_4,plain,(
    ! [A_3] : k3_xboole_0(A_3,A_3) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_293,plain,(
    ! [A_65,B_66] : k4_xboole_0(A_65,k4_xboole_0(A_65,B_66)) = k3_xboole_0(A_65,B_66) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_10,plain,(
    ! [A_7,B_8] : r1_tarski(k4_xboole_0(A_7,B_8),A_7) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_359,plain,(
    ! [A_68,B_69] : r1_tarski(k3_xboole_0(A_68,B_69),A_68) ),
    inference(superposition,[status(thm),theory(equality)],[c_293,c_10])).

tff(c_381,plain,(
    ! [A_73] : r1_tarski(A_73,A_73) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_359])).

tff(c_8,plain,(
    ! [A_5,B_6] :
      ( k4_xboole_0(A_5,B_6) = k1_xboole_0
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_387,plain,(
    ! [A_74] : k4_xboole_0(A_74,A_74) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_381,c_8])).

tff(c_14,plain,(
    ! [A_11,B_12] : k5_xboole_0(A_11,k4_xboole_0(B_12,A_11)) = k2_xboole_0(A_11,B_12) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_395,plain,(
    ! [A_74] : k5_xboole_0(A_74,k1_xboole_0) = k2_xboole_0(A_74,A_74) ),
    inference(superposition,[status(thm),theory(equality)],[c_387,c_14])).

tff(c_410,plain,(
    ! [A_74] : k5_xboole_0(A_74,k1_xboole_0) = A_74 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_395])).

tff(c_106,plain,(
    ! [A_47,B_48] :
      ( k4_xboole_0(A_47,B_48) = k1_xboole_0
      | ~ r1_tarski(A_47,B_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_114,plain,(
    ! [A_7,B_8] : k4_xboole_0(k4_xboole_0(A_7,B_8),A_7) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_10,c_106])).

tff(c_659,plain,(
    ! [A_89,B_90] : k4_xboole_0(k3_xboole_0(A_89,B_90),A_89) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_293,c_114])).

tff(c_671,plain,(
    ! [A_89,B_90] : k2_xboole_0(A_89,k3_xboole_0(A_89,B_90)) = k5_xboole_0(A_89,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_659,c_14])).

tff(c_696,plain,(
    ! [A_89,B_90] : k2_xboole_0(A_89,k3_xboole_0(A_89,B_90)) = A_89 ),
    inference(demodulation,[status(thm),theory(equality)],[c_410,c_671])).

tff(c_1920,plain,(
    k2_xboole_0('#skF_1','#skF_2') = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_1892,c_696])).

tff(c_1935,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1548,c_1920])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:34:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.38/1.53  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.38/1.54  
% 3.38/1.54  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.38/1.54  %$ r1_tarski > m1_subset_1 > k3_enumset1 > k2_enumset1 > k4_subset_1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k2_subset_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_1
% 3.38/1.54  
% 3.38/1.54  %Foreground sorts:
% 3.38/1.54  
% 3.38/1.54  
% 3.38/1.54  %Background operators:
% 3.38/1.54  
% 3.38/1.54  
% 3.38/1.54  %Foreground operators:
% 3.38/1.54  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.38/1.54  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.38/1.54  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.38/1.54  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.38/1.54  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.38/1.54  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.38/1.54  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.38/1.54  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.38/1.54  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 3.38/1.54  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 3.38/1.54  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.38/1.54  tff('#skF_2', type, '#skF_2': $i).
% 3.38/1.54  tff('#skF_1', type, '#skF_1': $i).
% 3.38/1.54  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.38/1.54  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.38/1.54  tff(k3_tarski, type, k3_tarski: $i > $i).
% 3.38/1.54  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.38/1.54  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.38/1.54  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.38/1.54  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 3.38/1.54  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.38/1.54  
% 3.38/1.56  tff(f_41, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 3.38/1.56  tff(f_49, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 3.38/1.56  tff(f_76, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k4_subset_1(A, B, k2_subset_1(A)) = k2_subset_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_subset_1)).
% 3.38/1.56  tff(f_51, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 3.38/1.56  tff(f_57, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 3.38/1.56  tff(f_71, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 3.38/1.56  tff(f_55, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 3.38/1.56  tff(f_37, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 3.38/1.56  tff(f_65, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, k3_subset_1(A, B)) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 3.38/1.56  tff(f_61, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k3_subset_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 3.38/1.56  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k2_xboole_0)).
% 3.38/1.56  tff(f_29, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 3.38/1.56  tff(f_35, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 3.38/1.56  tff(f_33, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 3.38/1.56  tff(f_39, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_xboole_1)).
% 3.38/1.56  tff(c_16, plain, (![B_14, A_13]: (k2_tarski(B_14, A_13)=k2_tarski(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.38/1.56  tff(c_198, plain, (![A_57, B_58]: (k3_tarski(k2_tarski(A_57, B_58))=k2_xboole_0(A_57, B_58))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.38/1.56  tff(c_236, plain, (![B_61, A_62]: (k3_tarski(k2_tarski(B_61, A_62))=k2_xboole_0(A_62, B_61))), inference(superposition, [status(thm), theory('equality')], [c_16, c_198])).
% 3.38/1.56  tff(c_24, plain, (![A_24, B_25]: (k3_tarski(k2_tarski(A_24, B_25))=k2_xboole_0(A_24, B_25))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.38/1.56  tff(c_242, plain, (![B_61, A_62]: (k2_xboole_0(B_61, A_62)=k2_xboole_0(A_62, B_61))), inference(superposition, [status(thm), theory('equality')], [c_236, c_24])).
% 3.38/1.56  tff(c_40, plain, (m1_subset_1('#skF_2', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.38/1.56  tff(c_26, plain, (![A_26]: (k2_subset_1(A_26)=A_26)), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.38/1.56  tff(c_30, plain, (![A_29]: (m1_subset_1(k2_subset_1(A_29), k1_zfmisc_1(A_29)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.38/1.56  tff(c_42, plain, (![A_29]: (m1_subset_1(A_29, k1_zfmisc_1(A_29)))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_30])).
% 3.38/1.56  tff(c_871, plain, (![A_99, B_100, C_101]: (k4_subset_1(A_99, B_100, C_101)=k2_xboole_0(B_100, C_101) | ~m1_subset_1(C_101, k1_zfmisc_1(A_99)) | ~m1_subset_1(B_100, k1_zfmisc_1(A_99)))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.38/1.56  tff(c_1415, plain, (![A_119, B_120]: (k4_subset_1(A_119, B_120, A_119)=k2_xboole_0(B_120, A_119) | ~m1_subset_1(B_120, k1_zfmisc_1(A_119)))), inference(resolution, [status(thm)], [c_42, c_871])).
% 3.38/1.56  tff(c_1421, plain, (k4_subset_1('#skF_1', '#skF_2', '#skF_1')=k2_xboole_0('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_40, c_1415])).
% 3.38/1.56  tff(c_1429, plain, (k4_subset_1('#skF_1', '#skF_2', '#skF_1')=k2_xboole_0('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_242, c_1421])).
% 3.38/1.56  tff(c_38, plain, (k4_subset_1('#skF_1', '#skF_2', k2_subset_1('#skF_1'))!=k2_subset_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.38/1.56  tff(c_41, plain, (k4_subset_1('#skF_1', '#skF_2', '#skF_1')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_26, c_26, c_38])).
% 3.38/1.56  tff(c_1548, plain, (k2_xboole_0('#skF_1', '#skF_2')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_1429, c_41])).
% 3.38/1.56  tff(c_578, plain, (![A_84, B_85]: (k4_xboole_0(A_84, B_85)=k3_subset_1(A_84, B_85) | ~m1_subset_1(B_85, k1_zfmisc_1(A_84)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.38/1.56  tff(c_589, plain, (k4_xboole_0('#skF_1', '#skF_2')=k3_subset_1('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_40, c_578])).
% 3.38/1.56  tff(c_12, plain, (![A_9, B_10]: (k4_xboole_0(A_9, k4_xboole_0(A_9, B_10))=k3_xboole_0(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.38/1.56  tff(c_640, plain, (k4_xboole_0('#skF_1', k3_subset_1('#skF_1', '#skF_2'))=k3_xboole_0('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_589, c_12])).
% 3.38/1.56  tff(c_528, plain, (![A_81, B_82]: (k3_subset_1(A_81, k3_subset_1(A_81, B_82))=B_82 | ~m1_subset_1(B_82, k1_zfmisc_1(A_81)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.38/1.56  tff(c_536, plain, (k3_subset_1('#skF_1', k3_subset_1('#skF_1', '#skF_2'))='#skF_2'), inference(resolution, [status(thm)], [c_40, c_528])).
% 3.38/1.56  tff(c_32, plain, (![A_30, B_31]: (m1_subset_1(k3_subset_1(A_30, B_31), k1_zfmisc_1(A_30)) | ~m1_subset_1(B_31, k1_zfmisc_1(A_30)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.38/1.56  tff(c_1879, plain, (![A_131, B_132]: (k4_xboole_0(A_131, k3_subset_1(A_131, B_132))=k3_subset_1(A_131, k3_subset_1(A_131, B_132)) | ~m1_subset_1(B_132, k1_zfmisc_1(A_131)))), inference(resolution, [status(thm)], [c_32, c_578])).
% 3.38/1.56  tff(c_1885, plain, (k4_xboole_0('#skF_1', k3_subset_1('#skF_1', '#skF_2'))=k3_subset_1('#skF_1', k3_subset_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_40, c_1879])).
% 3.38/1.56  tff(c_1892, plain, (k3_xboole_0('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_640, c_536, c_1885])).
% 3.38/1.56  tff(c_2, plain, (![A_1]: (k2_xboole_0(A_1, A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.38/1.56  tff(c_4, plain, (![A_3]: (k3_xboole_0(A_3, A_3)=A_3)), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.38/1.56  tff(c_293, plain, (![A_65, B_66]: (k4_xboole_0(A_65, k4_xboole_0(A_65, B_66))=k3_xboole_0(A_65, B_66))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.38/1.56  tff(c_10, plain, (![A_7, B_8]: (r1_tarski(k4_xboole_0(A_7, B_8), A_7))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.38/1.56  tff(c_359, plain, (![A_68, B_69]: (r1_tarski(k3_xboole_0(A_68, B_69), A_68))), inference(superposition, [status(thm), theory('equality')], [c_293, c_10])).
% 3.38/1.56  tff(c_381, plain, (![A_73]: (r1_tarski(A_73, A_73))), inference(superposition, [status(thm), theory('equality')], [c_4, c_359])).
% 3.38/1.56  tff(c_8, plain, (![A_5, B_6]: (k4_xboole_0(A_5, B_6)=k1_xboole_0 | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.38/1.56  tff(c_387, plain, (![A_74]: (k4_xboole_0(A_74, A_74)=k1_xboole_0)), inference(resolution, [status(thm)], [c_381, c_8])).
% 3.38/1.56  tff(c_14, plain, (![A_11, B_12]: (k5_xboole_0(A_11, k4_xboole_0(B_12, A_11))=k2_xboole_0(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.38/1.56  tff(c_395, plain, (![A_74]: (k5_xboole_0(A_74, k1_xboole_0)=k2_xboole_0(A_74, A_74))), inference(superposition, [status(thm), theory('equality')], [c_387, c_14])).
% 3.38/1.56  tff(c_410, plain, (![A_74]: (k5_xboole_0(A_74, k1_xboole_0)=A_74)), inference(demodulation, [status(thm), theory('equality')], [c_2, c_395])).
% 3.38/1.56  tff(c_106, plain, (![A_47, B_48]: (k4_xboole_0(A_47, B_48)=k1_xboole_0 | ~r1_tarski(A_47, B_48))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.38/1.56  tff(c_114, plain, (![A_7, B_8]: (k4_xboole_0(k4_xboole_0(A_7, B_8), A_7)=k1_xboole_0)), inference(resolution, [status(thm)], [c_10, c_106])).
% 3.38/1.56  tff(c_659, plain, (![A_89, B_90]: (k4_xboole_0(k3_xboole_0(A_89, B_90), A_89)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_293, c_114])).
% 3.38/1.56  tff(c_671, plain, (![A_89, B_90]: (k2_xboole_0(A_89, k3_xboole_0(A_89, B_90))=k5_xboole_0(A_89, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_659, c_14])).
% 3.38/1.56  tff(c_696, plain, (![A_89, B_90]: (k2_xboole_0(A_89, k3_xboole_0(A_89, B_90))=A_89)), inference(demodulation, [status(thm), theory('equality')], [c_410, c_671])).
% 3.38/1.56  tff(c_1920, plain, (k2_xboole_0('#skF_1', '#skF_2')='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_1892, c_696])).
% 3.38/1.56  tff(c_1935, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1548, c_1920])).
% 3.38/1.56  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.38/1.56  
% 3.38/1.56  Inference rules
% 3.38/1.56  ----------------------
% 3.38/1.56  #Ref     : 0
% 3.38/1.56  #Sup     : 476
% 3.38/1.56  #Fact    : 0
% 3.38/1.56  #Define  : 0
% 3.38/1.56  #Split   : 0
% 3.38/1.56  #Chain   : 0
% 3.38/1.56  #Close   : 0
% 3.38/1.56  
% 3.38/1.56  Ordering : KBO
% 3.38/1.56  
% 3.38/1.56  Simplification rules
% 3.38/1.56  ----------------------
% 3.38/1.56  #Subsume      : 2
% 3.38/1.56  #Demod        : 423
% 3.38/1.56  #Tautology    : 379
% 3.38/1.56  #SimpNegUnit  : 1
% 3.38/1.56  #BackRed      : 7
% 3.38/1.56  
% 3.38/1.56  #Partial instantiations: 0
% 3.38/1.56  #Strategies tried      : 1
% 3.38/1.56  
% 3.38/1.56  Timing (in seconds)
% 3.38/1.56  ----------------------
% 3.38/1.56  Preprocessing        : 0.32
% 3.38/1.56  Parsing              : 0.18
% 3.38/1.56  CNF conversion       : 0.02
% 3.38/1.56  Main loop            : 0.48
% 3.38/1.56  Inferencing          : 0.17
% 3.38/1.56  Reduction            : 0.19
% 3.38/1.56  Demodulation         : 0.15
% 3.38/1.56  BG Simplification    : 0.02
% 3.38/1.56  Subsumption          : 0.07
% 3.38/1.56  Abstraction          : 0.03
% 3.38/1.56  MUC search           : 0.00
% 3.38/1.56  Cooper               : 0.00
% 3.38/1.56  Total                : 0.83
% 3.38/1.56  Index Insertion      : 0.00
% 3.38/1.56  Index Deletion       : 0.00
% 3.38/1.56  Index Matching       : 0.00
% 3.38/1.56  BG Taut test         : 0.00
%------------------------------------------------------------------------------
