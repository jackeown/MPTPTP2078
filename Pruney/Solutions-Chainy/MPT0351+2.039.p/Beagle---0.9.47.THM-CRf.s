%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:55:42 EST 2020

% Result     : Theorem 2.74s
% Output     : CNFRefutation 2.74s
% Verified   : 
% Statistics : Number of formulae       :   68 (  80 expanded)
%              Number of leaves         :   34 (  41 expanded)
%              Depth                    :    7
%              Number of atoms          :   63 (  78 expanded)
%              Number of equality atoms :   39 (  49 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > m1_subset_1 > k3_enumset1 > k2_enumset1 > k4_subset_1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k2_subset_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_1

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_49,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_74,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => k4_subset_1(A,B,k2_subset_1(A)) = k2_subset_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_subset_1)).

tff(f_63,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,k3_subset_1(A,B)) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k3_subset_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_31,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

tff(f_35,axiom,(
    ! [A] : k4_xboole_0(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).

tff(f_37,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_47,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_55,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_69,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(c_24,plain,(
    ! [A_22] : k2_subset_1(A_22) = A_22 ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_36,plain,(
    k4_subset_1('#skF_1','#skF_2',k2_subset_1('#skF_1')) != k2_subset_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_39,plain,(
    k4_subset_1('#skF_1','#skF_2','#skF_1') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_24,c_36])).

tff(c_38,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_433,plain,(
    ! [A_71,B_72] :
      ( k3_subset_1(A_71,k3_subset_1(A_71,B_72)) = B_72
      | ~ m1_subset_1(B_72,k1_zfmisc_1(A_71)) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_441,plain,(
    k3_subset_1('#skF_1',k3_subset_1('#skF_1','#skF_2')) = '#skF_2' ),
    inference(resolution,[status(thm)],[c_38,c_433])).

tff(c_30,plain,(
    ! [A_26,B_27] :
      ( m1_subset_1(k3_subset_1(A_26,B_27),k1_zfmisc_1(A_26))
      | ~ m1_subset_1(B_27,k1_zfmisc_1(A_26)) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_351,plain,(
    ! [A_68,B_69] :
      ( k4_xboole_0(A_68,B_69) = k3_subset_1(A_68,B_69)
      | ~ m1_subset_1(B_69,k1_zfmisc_1(A_68)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_647,plain,(
    ! [A_85,B_86] :
      ( k4_xboole_0(A_85,k3_subset_1(A_85,B_86)) = k3_subset_1(A_85,k3_subset_1(A_85,B_86))
      | ~ m1_subset_1(B_86,k1_zfmisc_1(A_85)) ) ),
    inference(resolution,[status(thm)],[c_30,c_351])).

tff(c_651,plain,(
    k4_xboole_0('#skF_1',k3_subset_1('#skF_1','#skF_2')) = k3_subset_1('#skF_1',k3_subset_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_38,c_647])).

tff(c_656,plain,(
    k4_xboole_0('#skF_1',k3_subset_1('#skF_1','#skF_2')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_441,c_651])).

tff(c_6,plain,(
    ! [A_3] : k2_xboole_0(A_3,k1_xboole_0) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_10,plain,(
    ! [A_6] : k4_xboole_0(k1_xboole_0,A_6) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_177,plain,(
    ! [A_53,B_54] : k5_xboole_0(A_53,k4_xboole_0(B_54,A_53)) = k2_xboole_0(A_53,B_54) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_189,plain,(
    ! [A_6] : k5_xboole_0(A_6,k1_xboole_0) = k2_xboole_0(A_6,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_177])).

tff(c_192,plain,(
    ! [A_6] : k5_xboole_0(A_6,k1_xboole_0) = A_6 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_189])).

tff(c_8,plain,(
    ! [A_4,B_5] : r1_tarski(k4_xboole_0(A_4,B_5),A_4) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_104,plain,(
    ! [A_41,B_42] :
      ( k4_xboole_0(A_41,B_42) = k1_xboole_0
      | ~ r1_tarski(A_41,B_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_113,plain,(
    ! [A_4,B_5] : k4_xboole_0(k4_xboole_0(A_4,B_5),A_4) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_8,c_104])).

tff(c_186,plain,(
    ! [A_4,B_5] : k2_xboole_0(A_4,k4_xboole_0(A_4,B_5)) = k5_xboole_0(A_4,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_113,c_177])).

tff(c_323,plain,(
    ! [A_4,B_5] : k2_xboole_0(A_4,k4_xboole_0(A_4,B_5)) = A_4 ),
    inference(demodulation,[status(thm),theory(equality)],[c_192,c_186])).

tff(c_662,plain,(
    k2_xboole_0('#skF_1','#skF_2') = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_656,c_323])).

tff(c_14,plain,(
    ! [B_10,A_9] : k2_tarski(B_10,A_9) = k2_tarski(A_9,B_10) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_153,plain,(
    ! [A_49,B_50] : k3_tarski(k2_tarski(A_49,B_50)) = k2_xboole_0(A_49,B_50) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_202,plain,(
    ! [B_56,A_57] : k3_tarski(k2_tarski(B_56,A_57)) = k2_xboole_0(A_57,B_56) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_153])).

tff(c_22,plain,(
    ! [A_20,B_21] : k3_tarski(k2_tarski(A_20,B_21)) = k2_xboole_0(A_20,B_21) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_208,plain,(
    ! [B_56,A_57] : k2_xboole_0(B_56,A_57) = k2_xboole_0(A_57,B_56) ),
    inference(superposition,[status(thm),theory(equality)],[c_202,c_22])).

tff(c_28,plain,(
    ! [A_25] : m1_subset_1(k2_subset_1(A_25),k1_zfmisc_1(A_25)) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_40,plain,(
    ! [A_25] : m1_subset_1(A_25,k1_zfmisc_1(A_25)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_28])).

tff(c_683,plain,(
    ! [A_87,B_88,C_89] :
      ( k4_subset_1(A_87,B_88,C_89) = k2_xboole_0(B_88,C_89)
      | ~ m1_subset_1(C_89,k1_zfmisc_1(A_87))
      | ~ m1_subset_1(B_88,k1_zfmisc_1(A_87)) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_801,plain,(
    ! [A_94,B_95] :
      ( k4_subset_1(A_94,B_95,A_94) = k2_xboole_0(B_95,A_94)
      | ~ m1_subset_1(B_95,k1_zfmisc_1(A_94)) ) ),
    inference(resolution,[status(thm)],[c_40,c_683])).

tff(c_805,plain,(
    k4_subset_1('#skF_1','#skF_2','#skF_1') = k2_xboole_0('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_38,c_801])).

tff(c_811,plain,(
    k4_subset_1('#skF_1','#skF_2','#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_662,c_208,c_805])).

tff(c_813,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_39,c_811])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:47:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.74/1.38  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.74/1.38  
% 2.74/1.38  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.74/1.39  %$ r1_tarski > m1_subset_1 > k3_enumset1 > k2_enumset1 > k4_subset_1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k2_subset_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_1
% 2.74/1.39  
% 2.74/1.39  %Foreground sorts:
% 2.74/1.39  
% 2.74/1.39  
% 2.74/1.39  %Background operators:
% 2.74/1.39  
% 2.74/1.39  
% 2.74/1.39  %Foreground operators:
% 2.74/1.39  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.74/1.39  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.74/1.39  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.74/1.39  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.74/1.39  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.74/1.39  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.74/1.39  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.74/1.39  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.74/1.39  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 2.74/1.39  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 2.74/1.39  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.74/1.39  tff('#skF_2', type, '#skF_2': $i).
% 2.74/1.39  tff('#skF_1', type, '#skF_1': $i).
% 2.74/1.39  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.74/1.39  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.74/1.39  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.74/1.39  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.74/1.39  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.74/1.39  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 2.74/1.39  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.74/1.39  
% 2.74/1.40  tff(f_49, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 2.74/1.40  tff(f_74, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k4_subset_1(A, B, k2_subset_1(A)) = k2_subset_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_subset_1)).
% 2.74/1.40  tff(f_63, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, k3_subset_1(A, B)) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 2.74/1.40  tff(f_59, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k3_subset_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 2.74/1.40  tff(f_53, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_subset_1)).
% 2.74/1.40  tff(f_31, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 2.74/1.40  tff(f_35, axiom, (![A]: (k4_xboole_0(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_boole)).
% 2.74/1.40  tff(f_37, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_xboole_1)).
% 2.74/1.40  tff(f_33, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 2.74/1.40  tff(f_29, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 2.74/1.40  tff(f_39, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 2.74/1.40  tff(f_47, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 2.74/1.40  tff(f_55, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 2.74/1.40  tff(f_69, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 2.74/1.40  tff(c_24, plain, (![A_22]: (k2_subset_1(A_22)=A_22)), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.74/1.40  tff(c_36, plain, (k4_subset_1('#skF_1', '#skF_2', k2_subset_1('#skF_1'))!=k2_subset_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.74/1.40  tff(c_39, plain, (k4_subset_1('#skF_1', '#skF_2', '#skF_1')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_24, c_24, c_36])).
% 2.74/1.40  tff(c_38, plain, (m1_subset_1('#skF_2', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.74/1.40  tff(c_433, plain, (![A_71, B_72]: (k3_subset_1(A_71, k3_subset_1(A_71, B_72))=B_72 | ~m1_subset_1(B_72, k1_zfmisc_1(A_71)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.74/1.40  tff(c_441, plain, (k3_subset_1('#skF_1', k3_subset_1('#skF_1', '#skF_2'))='#skF_2'), inference(resolution, [status(thm)], [c_38, c_433])).
% 2.74/1.40  tff(c_30, plain, (![A_26, B_27]: (m1_subset_1(k3_subset_1(A_26, B_27), k1_zfmisc_1(A_26)) | ~m1_subset_1(B_27, k1_zfmisc_1(A_26)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.74/1.40  tff(c_351, plain, (![A_68, B_69]: (k4_xboole_0(A_68, B_69)=k3_subset_1(A_68, B_69) | ~m1_subset_1(B_69, k1_zfmisc_1(A_68)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.74/1.40  tff(c_647, plain, (![A_85, B_86]: (k4_xboole_0(A_85, k3_subset_1(A_85, B_86))=k3_subset_1(A_85, k3_subset_1(A_85, B_86)) | ~m1_subset_1(B_86, k1_zfmisc_1(A_85)))), inference(resolution, [status(thm)], [c_30, c_351])).
% 2.74/1.40  tff(c_651, plain, (k4_xboole_0('#skF_1', k3_subset_1('#skF_1', '#skF_2'))=k3_subset_1('#skF_1', k3_subset_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_38, c_647])).
% 2.74/1.40  tff(c_656, plain, (k4_xboole_0('#skF_1', k3_subset_1('#skF_1', '#skF_2'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_441, c_651])).
% 2.74/1.40  tff(c_6, plain, (![A_3]: (k2_xboole_0(A_3, k1_xboole_0)=A_3)), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.74/1.40  tff(c_10, plain, (![A_6]: (k4_xboole_0(k1_xboole_0, A_6)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.74/1.40  tff(c_177, plain, (![A_53, B_54]: (k5_xboole_0(A_53, k4_xboole_0(B_54, A_53))=k2_xboole_0(A_53, B_54))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.74/1.40  tff(c_189, plain, (![A_6]: (k5_xboole_0(A_6, k1_xboole_0)=k2_xboole_0(A_6, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_10, c_177])).
% 2.74/1.40  tff(c_192, plain, (![A_6]: (k5_xboole_0(A_6, k1_xboole_0)=A_6)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_189])).
% 2.74/1.40  tff(c_8, plain, (![A_4, B_5]: (r1_tarski(k4_xboole_0(A_4, B_5), A_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.74/1.40  tff(c_104, plain, (![A_41, B_42]: (k4_xboole_0(A_41, B_42)=k1_xboole_0 | ~r1_tarski(A_41, B_42))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.74/1.40  tff(c_113, plain, (![A_4, B_5]: (k4_xboole_0(k4_xboole_0(A_4, B_5), A_4)=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_104])).
% 2.74/1.40  tff(c_186, plain, (![A_4, B_5]: (k2_xboole_0(A_4, k4_xboole_0(A_4, B_5))=k5_xboole_0(A_4, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_113, c_177])).
% 2.74/1.40  tff(c_323, plain, (![A_4, B_5]: (k2_xboole_0(A_4, k4_xboole_0(A_4, B_5))=A_4)), inference(demodulation, [status(thm), theory('equality')], [c_192, c_186])).
% 2.74/1.40  tff(c_662, plain, (k2_xboole_0('#skF_1', '#skF_2')='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_656, c_323])).
% 2.74/1.40  tff(c_14, plain, (![B_10, A_9]: (k2_tarski(B_10, A_9)=k2_tarski(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.74/1.40  tff(c_153, plain, (![A_49, B_50]: (k3_tarski(k2_tarski(A_49, B_50))=k2_xboole_0(A_49, B_50))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.74/1.40  tff(c_202, plain, (![B_56, A_57]: (k3_tarski(k2_tarski(B_56, A_57))=k2_xboole_0(A_57, B_56))), inference(superposition, [status(thm), theory('equality')], [c_14, c_153])).
% 2.74/1.40  tff(c_22, plain, (![A_20, B_21]: (k3_tarski(k2_tarski(A_20, B_21))=k2_xboole_0(A_20, B_21))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.74/1.40  tff(c_208, plain, (![B_56, A_57]: (k2_xboole_0(B_56, A_57)=k2_xboole_0(A_57, B_56))), inference(superposition, [status(thm), theory('equality')], [c_202, c_22])).
% 2.74/1.40  tff(c_28, plain, (![A_25]: (m1_subset_1(k2_subset_1(A_25), k1_zfmisc_1(A_25)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.74/1.40  tff(c_40, plain, (![A_25]: (m1_subset_1(A_25, k1_zfmisc_1(A_25)))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_28])).
% 2.74/1.40  tff(c_683, plain, (![A_87, B_88, C_89]: (k4_subset_1(A_87, B_88, C_89)=k2_xboole_0(B_88, C_89) | ~m1_subset_1(C_89, k1_zfmisc_1(A_87)) | ~m1_subset_1(B_88, k1_zfmisc_1(A_87)))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.74/1.40  tff(c_801, plain, (![A_94, B_95]: (k4_subset_1(A_94, B_95, A_94)=k2_xboole_0(B_95, A_94) | ~m1_subset_1(B_95, k1_zfmisc_1(A_94)))), inference(resolution, [status(thm)], [c_40, c_683])).
% 2.74/1.40  tff(c_805, plain, (k4_subset_1('#skF_1', '#skF_2', '#skF_1')=k2_xboole_0('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_38, c_801])).
% 2.74/1.40  tff(c_811, plain, (k4_subset_1('#skF_1', '#skF_2', '#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_662, c_208, c_805])).
% 2.74/1.40  tff(c_813, plain, $false, inference(negUnitSimplification, [status(thm)], [c_39, c_811])).
% 2.74/1.40  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.74/1.40  
% 2.74/1.40  Inference rules
% 2.74/1.40  ----------------------
% 2.74/1.40  #Ref     : 0
% 2.74/1.40  #Sup     : 196
% 2.74/1.40  #Fact    : 0
% 2.74/1.40  #Define  : 0
% 2.74/1.40  #Split   : 0
% 2.74/1.40  #Chain   : 0
% 2.74/1.40  #Close   : 0
% 2.74/1.40  
% 2.74/1.40  Ordering : KBO
% 2.74/1.40  
% 2.74/1.40  Simplification rules
% 2.74/1.40  ----------------------
% 2.74/1.40  #Subsume      : 4
% 2.74/1.40  #Demod        : 92
% 2.74/1.40  #Tautology    : 149
% 2.74/1.40  #SimpNegUnit  : 1
% 2.74/1.40  #BackRed      : 1
% 2.74/1.40  
% 2.74/1.40  #Partial instantiations: 0
% 2.74/1.40  #Strategies tried      : 1
% 2.74/1.40  
% 2.74/1.40  Timing (in seconds)
% 2.74/1.40  ----------------------
% 2.74/1.40  Preprocessing        : 0.32
% 2.74/1.40  Parsing              : 0.18
% 2.74/1.40  CNF conversion       : 0.02
% 2.74/1.40  Main loop            : 0.31
% 2.74/1.40  Inferencing          : 0.12
% 2.74/1.40  Reduction            : 0.11
% 2.74/1.40  Demodulation         : 0.08
% 2.74/1.40  BG Simplification    : 0.02
% 2.74/1.40  Subsumption          : 0.05
% 2.74/1.41  Abstraction          : 0.02
% 2.74/1.41  MUC search           : 0.00
% 2.74/1.41  Cooper               : 0.00
% 2.74/1.41  Total                : 0.66
% 2.74/1.41  Index Insertion      : 0.00
% 2.74/1.41  Index Deletion       : 0.00
% 2.74/1.41  Index Matching       : 0.00
% 2.74/1.41  BG Taut test         : 0.00
%------------------------------------------------------------------------------
