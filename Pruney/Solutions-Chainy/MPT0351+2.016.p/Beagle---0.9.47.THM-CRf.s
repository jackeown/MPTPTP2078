%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:55:38 EST 2020

% Result     : Theorem 2.94s
% Output     : CNFRefutation 2.94s
% Verified   : 
% Statistics : Number of formulae       :   68 (  78 expanded)
%              Number of leaves         :   36 (  42 expanded)
%              Depth                    :    7
%              Number of atoms          :   60 (  73 expanded)
%              Number of equality atoms :   36 (  44 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > m1_subset_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k4_subset_1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k2_subset_1 > k1_zfmisc_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

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

tff(f_39,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_53,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_80,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => k4_subset_1(A,B,k2_subset_1(A)) = k2_subset_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_subset_1)).

tff(f_55,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_61,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_75,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(f_69,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,k3_subset_1(A,B)) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

tff(f_65,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k3_subset_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_37,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_31,axiom,(
    ! [A,B] : k2_xboole_0(A,k3_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_xboole_1)).

tff(c_12,plain,(
    ! [B_12,A_11] : k2_tarski(B_12,A_11) = k2_tarski(A_11,B_12) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_179,plain,(
    ! [A_69,B_70] : k3_tarski(k2_tarski(A_69,B_70)) = k2_xboole_0(A_69,B_70) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_194,plain,(
    ! [B_71,A_72] : k3_tarski(k2_tarski(B_71,A_72)) = k2_xboole_0(A_72,B_71) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_179])).

tff(c_26,plain,(
    ! [A_40,B_41] : k3_tarski(k2_tarski(A_40,B_41)) = k2_xboole_0(A_40,B_41) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_200,plain,(
    ! [B_71,A_72] : k2_xboole_0(B_71,A_72) = k2_xboole_0(A_72,B_71) ),
    inference(superposition,[status(thm),theory(equality)],[c_194,c_26])).

tff(c_42,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_28,plain,(
    ! [A_42] : k2_subset_1(A_42) = A_42 ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_32,plain,(
    ! [A_45] : m1_subset_1(k2_subset_1(A_45),k1_zfmisc_1(A_45)) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_44,plain,(
    ! [A_45] : m1_subset_1(A_45,k1_zfmisc_1(A_45)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_32])).

tff(c_730,plain,(
    ! [A_123,B_124,C_125] :
      ( k4_subset_1(A_123,B_124,C_125) = k2_xboole_0(B_124,C_125)
      | ~ m1_subset_1(C_125,k1_zfmisc_1(A_123))
      | ~ m1_subset_1(B_124,k1_zfmisc_1(A_123)) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_777,plain,(
    ! [A_128,B_129] :
      ( k4_subset_1(A_128,B_129,A_128) = k2_xboole_0(B_129,A_128)
      | ~ m1_subset_1(B_129,k1_zfmisc_1(A_128)) ) ),
    inference(resolution,[status(thm)],[c_44,c_730])).

tff(c_781,plain,(
    k4_subset_1('#skF_1','#skF_2','#skF_1') = k2_xboole_0('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_42,c_777])).

tff(c_787,plain,(
    k4_subset_1('#skF_1','#skF_2','#skF_1') = k2_xboole_0('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_200,c_781])).

tff(c_40,plain,(
    k4_subset_1('#skF_1','#skF_2',k2_subset_1('#skF_1')) != k2_subset_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_43,plain,(
    k4_subset_1('#skF_1','#skF_2','#skF_1') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_28,c_40])).

tff(c_789,plain,(
    k2_xboole_0('#skF_1','#skF_2') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_787,c_43])).

tff(c_370,plain,(
    ! [A_88,B_89] :
      ( k3_subset_1(A_88,k3_subset_1(A_88,B_89)) = B_89
      | ~ m1_subset_1(B_89,k1_zfmisc_1(A_88)) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_375,plain,(
    k3_subset_1('#skF_1',k3_subset_1('#skF_1','#skF_2')) = '#skF_2' ),
    inference(resolution,[status(thm)],[c_42,c_370])).

tff(c_454,plain,(
    ! [A_95,B_96] :
      ( m1_subset_1(k3_subset_1(A_95,B_96),k1_zfmisc_1(A_95))
      | ~ m1_subset_1(B_96,k1_zfmisc_1(A_95)) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_30,plain,(
    ! [A_43,B_44] :
      ( k4_xboole_0(A_43,B_44) = k3_subset_1(A_43,B_44)
      | ~ m1_subset_1(B_44,k1_zfmisc_1(A_43)) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_917,plain,(
    ! [A_142,B_143] :
      ( k4_xboole_0(A_142,k3_subset_1(A_142,B_143)) = k3_subset_1(A_142,k3_subset_1(A_142,B_143))
      | ~ m1_subset_1(B_143,k1_zfmisc_1(A_142)) ) ),
    inference(resolution,[status(thm)],[c_454,c_30])).

tff(c_921,plain,(
    k4_xboole_0('#skF_1',k3_subset_1('#skF_1','#skF_2')) = k3_subset_1('#skF_1',k3_subset_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_42,c_917])).

tff(c_926,plain,(
    k4_xboole_0('#skF_1',k3_subset_1('#skF_1','#skF_2')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_375,c_921])).

tff(c_10,plain,(
    ! [A_9,B_10] : r1_tarski(k4_xboole_0(A_9,B_10),A_9) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_174,plain,(
    ! [A_67,B_68] :
      ( k3_xboole_0(A_67,B_68) = A_67
      | ~ r1_tarski(A_67,B_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_266,plain,(
    ! [A_77,B_78] : k3_xboole_0(k4_xboole_0(A_77,B_78),A_77) = k4_xboole_0(A_77,B_78) ),
    inference(resolution,[status(thm)],[c_10,c_174])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_122,plain,(
    ! [A_61,B_62] : k2_xboole_0(A_61,k3_xboole_0(A_61,B_62)) = A_61 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_131,plain,(
    ! [A_1,B_2] : k2_xboole_0(A_1,k3_xboole_0(B_2,A_1)) = A_1 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_122])).

tff(c_275,plain,(
    ! [A_77,B_78] : k2_xboole_0(A_77,k4_xboole_0(A_77,B_78)) = A_77 ),
    inference(superposition,[status(thm),theory(equality)],[c_266,c_131])).

tff(c_951,plain,(
    k2_xboole_0('#skF_1','#skF_2') = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_926,c_275])).

tff(c_967,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_789,c_951])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:57:34 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.94/1.43  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.94/1.43  
% 2.94/1.43  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.94/1.43  %$ r1_tarski > m1_subset_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k4_subset_1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k2_subset_1 > k1_zfmisc_1 > #skF_2 > #skF_1
% 2.94/1.43  
% 2.94/1.43  %Foreground sorts:
% 2.94/1.43  
% 2.94/1.43  
% 2.94/1.43  %Background operators:
% 2.94/1.43  
% 2.94/1.43  
% 2.94/1.43  %Foreground operators:
% 2.94/1.43  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.94/1.43  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.94/1.43  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.94/1.43  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.94/1.43  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.94/1.43  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.94/1.43  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.94/1.43  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 2.94/1.43  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 2.94/1.43  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.94/1.43  tff('#skF_2', type, '#skF_2': $i).
% 2.94/1.43  tff('#skF_1', type, '#skF_1': $i).
% 2.94/1.43  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.94/1.43  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.94/1.43  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.94/1.43  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.94/1.43  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.94/1.43  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.94/1.43  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.94/1.43  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.94/1.43  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.94/1.43  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 2.94/1.43  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.94/1.43  
% 2.94/1.45  tff(f_39, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 2.94/1.45  tff(f_53, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 2.94/1.45  tff(f_80, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k4_subset_1(A, B, k2_subset_1(A)) = k2_subset_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_subset_1)).
% 2.94/1.45  tff(f_55, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 2.94/1.45  tff(f_61, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 2.94/1.45  tff(f_75, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 2.94/1.45  tff(f_69, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, k3_subset_1(A, B)) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 2.94/1.45  tff(f_65, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k3_subset_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 2.94/1.45  tff(f_59, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_subset_1)).
% 2.94/1.45  tff(f_37, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 2.94/1.45  tff(f_35, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 2.94/1.45  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 2.94/1.45  tff(f_31, axiom, (![A, B]: (k2_xboole_0(A, k3_xboole_0(A, B)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t22_xboole_1)).
% 2.94/1.45  tff(c_12, plain, (![B_12, A_11]: (k2_tarski(B_12, A_11)=k2_tarski(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.94/1.45  tff(c_179, plain, (![A_69, B_70]: (k3_tarski(k2_tarski(A_69, B_70))=k2_xboole_0(A_69, B_70))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.94/1.45  tff(c_194, plain, (![B_71, A_72]: (k3_tarski(k2_tarski(B_71, A_72))=k2_xboole_0(A_72, B_71))), inference(superposition, [status(thm), theory('equality')], [c_12, c_179])).
% 2.94/1.45  tff(c_26, plain, (![A_40, B_41]: (k3_tarski(k2_tarski(A_40, B_41))=k2_xboole_0(A_40, B_41))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.94/1.45  tff(c_200, plain, (![B_71, A_72]: (k2_xboole_0(B_71, A_72)=k2_xboole_0(A_72, B_71))), inference(superposition, [status(thm), theory('equality')], [c_194, c_26])).
% 2.94/1.45  tff(c_42, plain, (m1_subset_1('#skF_2', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.94/1.45  tff(c_28, plain, (![A_42]: (k2_subset_1(A_42)=A_42)), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.94/1.45  tff(c_32, plain, (![A_45]: (m1_subset_1(k2_subset_1(A_45), k1_zfmisc_1(A_45)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.94/1.45  tff(c_44, plain, (![A_45]: (m1_subset_1(A_45, k1_zfmisc_1(A_45)))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_32])).
% 2.94/1.45  tff(c_730, plain, (![A_123, B_124, C_125]: (k4_subset_1(A_123, B_124, C_125)=k2_xboole_0(B_124, C_125) | ~m1_subset_1(C_125, k1_zfmisc_1(A_123)) | ~m1_subset_1(B_124, k1_zfmisc_1(A_123)))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.94/1.45  tff(c_777, plain, (![A_128, B_129]: (k4_subset_1(A_128, B_129, A_128)=k2_xboole_0(B_129, A_128) | ~m1_subset_1(B_129, k1_zfmisc_1(A_128)))), inference(resolution, [status(thm)], [c_44, c_730])).
% 2.94/1.45  tff(c_781, plain, (k4_subset_1('#skF_1', '#skF_2', '#skF_1')=k2_xboole_0('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_42, c_777])).
% 2.94/1.45  tff(c_787, plain, (k4_subset_1('#skF_1', '#skF_2', '#skF_1')=k2_xboole_0('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_200, c_781])).
% 2.94/1.45  tff(c_40, plain, (k4_subset_1('#skF_1', '#skF_2', k2_subset_1('#skF_1'))!=k2_subset_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.94/1.45  tff(c_43, plain, (k4_subset_1('#skF_1', '#skF_2', '#skF_1')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_28, c_28, c_40])).
% 2.94/1.45  tff(c_789, plain, (k2_xboole_0('#skF_1', '#skF_2')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_787, c_43])).
% 2.94/1.45  tff(c_370, plain, (![A_88, B_89]: (k3_subset_1(A_88, k3_subset_1(A_88, B_89))=B_89 | ~m1_subset_1(B_89, k1_zfmisc_1(A_88)))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.94/1.45  tff(c_375, plain, (k3_subset_1('#skF_1', k3_subset_1('#skF_1', '#skF_2'))='#skF_2'), inference(resolution, [status(thm)], [c_42, c_370])).
% 2.94/1.45  tff(c_454, plain, (![A_95, B_96]: (m1_subset_1(k3_subset_1(A_95, B_96), k1_zfmisc_1(A_95)) | ~m1_subset_1(B_96, k1_zfmisc_1(A_95)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.94/1.45  tff(c_30, plain, (![A_43, B_44]: (k4_xboole_0(A_43, B_44)=k3_subset_1(A_43, B_44) | ~m1_subset_1(B_44, k1_zfmisc_1(A_43)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.94/1.45  tff(c_917, plain, (![A_142, B_143]: (k4_xboole_0(A_142, k3_subset_1(A_142, B_143))=k3_subset_1(A_142, k3_subset_1(A_142, B_143)) | ~m1_subset_1(B_143, k1_zfmisc_1(A_142)))), inference(resolution, [status(thm)], [c_454, c_30])).
% 2.94/1.45  tff(c_921, plain, (k4_xboole_0('#skF_1', k3_subset_1('#skF_1', '#skF_2'))=k3_subset_1('#skF_1', k3_subset_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_42, c_917])).
% 2.94/1.45  tff(c_926, plain, (k4_xboole_0('#skF_1', k3_subset_1('#skF_1', '#skF_2'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_375, c_921])).
% 2.94/1.45  tff(c_10, plain, (![A_9, B_10]: (r1_tarski(k4_xboole_0(A_9, B_10), A_9))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.94/1.45  tff(c_174, plain, (![A_67, B_68]: (k3_xboole_0(A_67, B_68)=A_67 | ~r1_tarski(A_67, B_68))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.94/1.45  tff(c_266, plain, (![A_77, B_78]: (k3_xboole_0(k4_xboole_0(A_77, B_78), A_77)=k4_xboole_0(A_77, B_78))), inference(resolution, [status(thm)], [c_10, c_174])).
% 2.94/1.45  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.94/1.45  tff(c_122, plain, (![A_61, B_62]: (k2_xboole_0(A_61, k3_xboole_0(A_61, B_62))=A_61)), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.94/1.45  tff(c_131, plain, (![A_1, B_2]: (k2_xboole_0(A_1, k3_xboole_0(B_2, A_1))=A_1)), inference(superposition, [status(thm), theory('equality')], [c_2, c_122])).
% 2.94/1.45  tff(c_275, plain, (![A_77, B_78]: (k2_xboole_0(A_77, k4_xboole_0(A_77, B_78))=A_77)), inference(superposition, [status(thm), theory('equality')], [c_266, c_131])).
% 2.94/1.45  tff(c_951, plain, (k2_xboole_0('#skF_1', '#skF_2')='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_926, c_275])).
% 2.94/1.45  tff(c_967, plain, $false, inference(negUnitSimplification, [status(thm)], [c_789, c_951])).
% 2.94/1.45  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.94/1.45  
% 2.94/1.45  Inference rules
% 2.94/1.45  ----------------------
% 2.94/1.45  #Ref     : 0
% 2.94/1.45  #Sup     : 234
% 2.94/1.45  #Fact    : 0
% 2.94/1.45  #Define  : 0
% 2.94/1.45  #Split   : 0
% 2.94/1.45  #Chain   : 0
% 2.94/1.45  #Close   : 0
% 2.94/1.45  
% 2.94/1.45  Ordering : KBO
% 2.94/1.45  
% 2.94/1.45  Simplification rules
% 2.94/1.45  ----------------------
% 2.94/1.45  #Subsume      : 6
% 2.94/1.45  #Demod        : 108
% 2.94/1.45  #Tautology    : 171
% 2.94/1.45  #SimpNegUnit  : 1
% 2.94/1.45  #BackRed      : 2
% 2.94/1.45  
% 2.94/1.45  #Partial instantiations: 0
% 2.94/1.45  #Strategies tried      : 1
% 2.94/1.45  
% 2.94/1.45  Timing (in seconds)
% 2.94/1.45  ----------------------
% 2.94/1.45  Preprocessing        : 0.31
% 2.94/1.45  Parsing              : 0.17
% 2.94/1.45  CNF conversion       : 0.02
% 2.94/1.45  Main loop            : 0.37
% 2.94/1.45  Inferencing          : 0.14
% 2.94/1.45  Reduction            : 0.13
% 2.94/1.45  Demodulation         : 0.11
% 2.94/1.45  BG Simplification    : 0.02
% 2.94/1.45  Subsumption          : 0.06
% 2.94/1.45  Abstraction          : 0.02
% 2.94/1.45  MUC search           : 0.00
% 2.94/1.45  Cooper               : 0.00
% 2.94/1.45  Total                : 0.71
% 2.94/1.45  Index Insertion      : 0.00
% 2.94/1.45  Index Deletion       : 0.00
% 2.94/1.45  Index Matching       : 0.00
% 2.94/1.45  BG Taut test         : 0.00
%------------------------------------------------------------------------------
