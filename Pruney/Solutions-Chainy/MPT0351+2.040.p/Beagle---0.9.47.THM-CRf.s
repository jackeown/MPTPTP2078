%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:55:42 EST 2020

% Result     : Theorem 2.63s
% Output     : CNFRefutation 2.98s
% Verified   : 
% Statistics : Number of formulae       :   64 (  74 expanded)
%              Number of leaves         :   33 (  39 expanded)
%              Depth                    :    7
%              Number of atoms          :   59 (  72 expanded)
%              Number of equality atoms :   35 (  43 expanded)
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

tff(f_47,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_72,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => k4_subset_1(A,B,k2_subset_1(A)) = k2_subset_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_subset_1)).

tff(f_61,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,k3_subset_1(A,B)) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k3_subset_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_33,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

tff(f_31,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_45,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_53,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_67,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(c_22,plain,(
    ! [A_21] : k2_subset_1(A_21) = A_21 ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_34,plain,(
    k4_subset_1('#skF_1','#skF_2',k2_subset_1('#skF_1')) != k2_subset_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_37,plain,(
    k4_subset_1('#skF_1','#skF_2','#skF_1') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_22,c_34])).

tff(c_36,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_579,plain,(
    ! [A_77,B_78] :
      ( k3_subset_1(A_77,k3_subset_1(A_77,B_78)) = B_78
      | ~ m1_subset_1(B_78,k1_zfmisc_1(A_77)) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_587,plain,(
    k3_subset_1('#skF_1',k3_subset_1('#skF_1','#skF_2')) = '#skF_2' ),
    inference(resolution,[status(thm)],[c_36,c_579])).

tff(c_28,plain,(
    ! [A_25,B_26] :
      ( m1_subset_1(k3_subset_1(A_25,B_26),k1_zfmisc_1(A_25))
      | ~ m1_subset_1(B_26,k1_zfmisc_1(A_25)) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_486,plain,(
    ! [A_73,B_74] :
      ( k4_xboole_0(A_73,B_74) = k3_subset_1(A_73,B_74)
      | ~ m1_subset_1(B_74,k1_zfmisc_1(A_73)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_734,plain,(
    ! [A_88,B_89] :
      ( k4_xboole_0(A_88,k3_subset_1(A_88,B_89)) = k3_subset_1(A_88,k3_subset_1(A_88,B_89))
      | ~ m1_subset_1(B_89,k1_zfmisc_1(A_88)) ) ),
    inference(resolution,[status(thm)],[c_28,c_486])).

tff(c_738,plain,(
    k4_xboole_0('#skF_1',k3_subset_1('#skF_1','#skF_2')) = k3_subset_1('#skF_1',k3_subset_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_36,c_734])).

tff(c_743,plain,(
    k4_xboole_0('#skF_1',k3_subset_1('#skF_1','#skF_2')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_587,c_738])).

tff(c_8,plain,(
    ! [A_5] : k5_xboole_0(A_5,k1_xboole_0) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_6,plain,(
    ! [A_3,B_4] : r1_tarski(k4_xboole_0(A_3,B_4),A_3) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_93,plain,(
    ! [A_41,B_42] :
      ( k4_xboole_0(A_41,B_42) = k1_xboole_0
      | ~ r1_tarski(A_41,B_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_101,plain,(
    ! [A_3,B_4] : k4_xboole_0(k4_xboole_0(A_3,B_4),A_3) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_6,c_93])).

tff(c_223,plain,(
    ! [A_55,B_56] : k5_xboole_0(A_55,k4_xboole_0(B_56,A_55)) = k2_xboole_0(A_55,B_56) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_238,plain,(
    ! [A_3,B_4] : k2_xboole_0(A_3,k4_xboole_0(A_3,B_4)) = k5_xboole_0(A_3,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_101,c_223])).

tff(c_243,plain,(
    ! [A_3,B_4] : k2_xboole_0(A_3,k4_xboole_0(A_3,B_4)) = A_3 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_238])).

tff(c_749,plain,(
    k2_xboole_0('#skF_1','#skF_2') = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_743,c_243])).

tff(c_12,plain,(
    ! [B_9,A_8] : k2_tarski(B_9,A_8) = k2_tarski(A_8,B_9) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_102,plain,(
    ! [A_43,B_44] : k3_tarski(k2_tarski(A_43,B_44)) = k2_xboole_0(A_43,B_44) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_200,plain,(
    ! [B_53,A_54] : k3_tarski(k2_tarski(B_53,A_54)) = k2_xboole_0(A_54,B_53) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_102])).

tff(c_20,plain,(
    ! [A_19,B_20] : k3_tarski(k2_tarski(A_19,B_20)) = k2_xboole_0(A_19,B_20) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_206,plain,(
    ! [B_53,A_54] : k2_xboole_0(B_53,A_54) = k2_xboole_0(A_54,B_53) ),
    inference(superposition,[status(thm),theory(equality)],[c_200,c_20])).

tff(c_26,plain,(
    ! [A_24] : m1_subset_1(k2_subset_1(A_24),k1_zfmisc_1(A_24)) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_38,plain,(
    ! [A_24] : m1_subset_1(A_24,k1_zfmisc_1(A_24)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_26])).

tff(c_765,plain,(
    ! [A_90,B_91,C_92] :
      ( k4_subset_1(A_90,B_91,C_92) = k2_xboole_0(B_91,C_92)
      | ~ m1_subset_1(C_92,k1_zfmisc_1(A_90))
      | ~ m1_subset_1(B_91,k1_zfmisc_1(A_90)) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_883,plain,(
    ! [A_96,B_97] :
      ( k4_subset_1(A_96,B_97,A_96) = k2_xboole_0(B_97,A_96)
      | ~ m1_subset_1(B_97,k1_zfmisc_1(A_96)) ) ),
    inference(resolution,[status(thm)],[c_38,c_765])).

tff(c_887,plain,(
    k4_subset_1('#skF_1','#skF_2','#skF_1') = k2_xboole_0('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_36,c_883])).

tff(c_893,plain,(
    k4_subset_1('#skF_1','#skF_2','#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_749,c_206,c_887])).

tff(c_895,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_37,c_893])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n012.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:20:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.63/1.43  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.63/1.44  
% 2.63/1.44  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.63/1.44  %$ r1_tarski > m1_subset_1 > k3_enumset1 > k2_enumset1 > k4_subset_1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k2_subset_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_1
% 2.63/1.44  
% 2.63/1.44  %Foreground sorts:
% 2.63/1.44  
% 2.63/1.44  
% 2.63/1.44  %Background operators:
% 2.63/1.44  
% 2.63/1.44  
% 2.63/1.44  %Foreground operators:
% 2.63/1.44  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.63/1.44  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.63/1.44  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.63/1.44  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.63/1.44  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.63/1.44  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.63/1.44  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.63/1.44  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.63/1.44  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 2.63/1.44  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 2.63/1.44  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.63/1.44  tff('#skF_2', type, '#skF_2': $i).
% 2.63/1.44  tff('#skF_1', type, '#skF_1': $i).
% 2.63/1.44  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.63/1.44  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.63/1.44  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.63/1.44  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.63/1.44  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.63/1.44  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 2.63/1.44  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.63/1.44  
% 2.98/1.46  tff(f_47, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 2.98/1.46  tff(f_72, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k4_subset_1(A, B, k2_subset_1(A)) = k2_subset_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_subset_1)).
% 2.98/1.46  tff(f_61, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, k3_subset_1(A, B)) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 2.98/1.46  tff(f_57, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k3_subset_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 2.98/1.46  tff(f_51, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_subset_1)).
% 2.98/1.46  tff(f_33, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 2.98/1.46  tff(f_31, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 2.98/1.46  tff(f_29, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 2.98/1.46  tff(f_35, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_xboole_1)).
% 2.98/1.46  tff(f_37, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 2.98/1.46  tff(f_45, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 2.98/1.46  tff(f_53, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 2.98/1.46  tff(f_67, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 2.98/1.46  tff(c_22, plain, (![A_21]: (k2_subset_1(A_21)=A_21)), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.98/1.46  tff(c_34, plain, (k4_subset_1('#skF_1', '#skF_2', k2_subset_1('#skF_1'))!=k2_subset_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.98/1.46  tff(c_37, plain, (k4_subset_1('#skF_1', '#skF_2', '#skF_1')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_22, c_22, c_34])).
% 2.98/1.46  tff(c_36, plain, (m1_subset_1('#skF_2', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.98/1.46  tff(c_579, plain, (![A_77, B_78]: (k3_subset_1(A_77, k3_subset_1(A_77, B_78))=B_78 | ~m1_subset_1(B_78, k1_zfmisc_1(A_77)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.98/1.46  tff(c_587, plain, (k3_subset_1('#skF_1', k3_subset_1('#skF_1', '#skF_2'))='#skF_2'), inference(resolution, [status(thm)], [c_36, c_579])).
% 2.98/1.46  tff(c_28, plain, (![A_25, B_26]: (m1_subset_1(k3_subset_1(A_25, B_26), k1_zfmisc_1(A_25)) | ~m1_subset_1(B_26, k1_zfmisc_1(A_25)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.98/1.46  tff(c_486, plain, (![A_73, B_74]: (k4_xboole_0(A_73, B_74)=k3_subset_1(A_73, B_74) | ~m1_subset_1(B_74, k1_zfmisc_1(A_73)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.98/1.46  tff(c_734, plain, (![A_88, B_89]: (k4_xboole_0(A_88, k3_subset_1(A_88, B_89))=k3_subset_1(A_88, k3_subset_1(A_88, B_89)) | ~m1_subset_1(B_89, k1_zfmisc_1(A_88)))), inference(resolution, [status(thm)], [c_28, c_486])).
% 2.98/1.46  tff(c_738, plain, (k4_xboole_0('#skF_1', k3_subset_1('#skF_1', '#skF_2'))=k3_subset_1('#skF_1', k3_subset_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_36, c_734])).
% 2.98/1.46  tff(c_743, plain, (k4_xboole_0('#skF_1', k3_subset_1('#skF_1', '#skF_2'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_587, c_738])).
% 2.98/1.46  tff(c_8, plain, (![A_5]: (k5_xboole_0(A_5, k1_xboole_0)=A_5)), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.98/1.46  tff(c_6, plain, (![A_3, B_4]: (r1_tarski(k4_xboole_0(A_3, B_4), A_3))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.98/1.46  tff(c_93, plain, (![A_41, B_42]: (k4_xboole_0(A_41, B_42)=k1_xboole_0 | ~r1_tarski(A_41, B_42))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.98/1.46  tff(c_101, plain, (![A_3, B_4]: (k4_xboole_0(k4_xboole_0(A_3, B_4), A_3)=k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_93])).
% 2.98/1.46  tff(c_223, plain, (![A_55, B_56]: (k5_xboole_0(A_55, k4_xboole_0(B_56, A_55))=k2_xboole_0(A_55, B_56))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.98/1.46  tff(c_238, plain, (![A_3, B_4]: (k2_xboole_0(A_3, k4_xboole_0(A_3, B_4))=k5_xboole_0(A_3, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_101, c_223])).
% 2.98/1.46  tff(c_243, plain, (![A_3, B_4]: (k2_xboole_0(A_3, k4_xboole_0(A_3, B_4))=A_3)), inference(demodulation, [status(thm), theory('equality')], [c_8, c_238])).
% 2.98/1.46  tff(c_749, plain, (k2_xboole_0('#skF_1', '#skF_2')='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_743, c_243])).
% 2.98/1.46  tff(c_12, plain, (![B_9, A_8]: (k2_tarski(B_9, A_8)=k2_tarski(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.98/1.46  tff(c_102, plain, (![A_43, B_44]: (k3_tarski(k2_tarski(A_43, B_44))=k2_xboole_0(A_43, B_44))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.98/1.46  tff(c_200, plain, (![B_53, A_54]: (k3_tarski(k2_tarski(B_53, A_54))=k2_xboole_0(A_54, B_53))), inference(superposition, [status(thm), theory('equality')], [c_12, c_102])).
% 2.98/1.46  tff(c_20, plain, (![A_19, B_20]: (k3_tarski(k2_tarski(A_19, B_20))=k2_xboole_0(A_19, B_20))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.98/1.46  tff(c_206, plain, (![B_53, A_54]: (k2_xboole_0(B_53, A_54)=k2_xboole_0(A_54, B_53))), inference(superposition, [status(thm), theory('equality')], [c_200, c_20])).
% 2.98/1.46  tff(c_26, plain, (![A_24]: (m1_subset_1(k2_subset_1(A_24), k1_zfmisc_1(A_24)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.98/1.46  tff(c_38, plain, (![A_24]: (m1_subset_1(A_24, k1_zfmisc_1(A_24)))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_26])).
% 2.98/1.46  tff(c_765, plain, (![A_90, B_91, C_92]: (k4_subset_1(A_90, B_91, C_92)=k2_xboole_0(B_91, C_92) | ~m1_subset_1(C_92, k1_zfmisc_1(A_90)) | ~m1_subset_1(B_91, k1_zfmisc_1(A_90)))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.98/1.46  tff(c_883, plain, (![A_96, B_97]: (k4_subset_1(A_96, B_97, A_96)=k2_xboole_0(B_97, A_96) | ~m1_subset_1(B_97, k1_zfmisc_1(A_96)))), inference(resolution, [status(thm)], [c_38, c_765])).
% 2.98/1.46  tff(c_887, plain, (k4_subset_1('#skF_1', '#skF_2', '#skF_1')=k2_xboole_0('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_36, c_883])).
% 2.98/1.46  tff(c_893, plain, (k4_subset_1('#skF_1', '#skF_2', '#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_749, c_206, c_887])).
% 2.98/1.46  tff(c_895, plain, $false, inference(negUnitSimplification, [status(thm)], [c_37, c_893])).
% 2.98/1.46  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.98/1.46  
% 2.98/1.46  Inference rules
% 2.98/1.46  ----------------------
% 2.98/1.46  #Ref     : 0
% 2.98/1.46  #Sup     : 221
% 2.98/1.46  #Fact    : 0
% 2.98/1.46  #Define  : 0
% 2.98/1.46  #Split   : 0
% 2.98/1.46  #Chain   : 0
% 2.98/1.46  #Close   : 0
% 2.98/1.46  
% 2.98/1.46  Ordering : KBO
% 2.98/1.46  
% 2.98/1.46  Simplification rules
% 2.98/1.46  ----------------------
% 2.98/1.46  #Subsume      : 3
% 2.98/1.46  #Demod        : 121
% 2.98/1.46  #Tautology    : 175
% 2.98/1.46  #SimpNegUnit  : 1
% 2.98/1.46  #BackRed      : 1
% 2.98/1.46  
% 2.98/1.46  #Partial instantiations: 0
% 2.98/1.46  #Strategies tried      : 1
% 2.98/1.46  
% 2.98/1.46  Timing (in seconds)
% 2.98/1.46  ----------------------
% 2.98/1.46  Preprocessing        : 0.32
% 2.98/1.46  Parsing              : 0.18
% 2.98/1.46  CNF conversion       : 0.02
% 2.98/1.46  Main loop            : 0.35
% 2.98/1.46  Inferencing          : 0.13
% 2.98/1.46  Reduction            : 0.13
% 2.98/1.46  Demodulation         : 0.10
% 2.98/1.46  BG Simplification    : 0.02
% 2.98/1.46  Subsumption          : 0.05
% 2.98/1.46  Abstraction          : 0.02
% 2.98/1.46  MUC search           : 0.00
% 2.98/1.46  Cooper               : 0.00
% 2.98/1.46  Total                : 0.71
% 2.98/1.46  Index Insertion      : 0.00
% 2.98/1.46  Index Deletion       : 0.00
% 2.98/1.46  Index Matching       : 0.00
% 2.98/1.46  BG Taut test         : 0.00
%------------------------------------------------------------------------------
