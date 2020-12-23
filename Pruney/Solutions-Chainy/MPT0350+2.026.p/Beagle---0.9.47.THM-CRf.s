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
% DateTime   : Thu Dec  3 09:55:29 EST 2020

% Result     : Theorem 5.54s
% Output     : CNFRefutation 5.73s
% Verified   : 
% Statistics : Number of formulae       :   67 (  88 expanded)
%              Number of leaves         :   29 (  41 expanded)
%              Depth                    :   10
%              Number of atoms          :   67 (  95 expanded)
%              Number of equality atoms :   45 (  61 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m1_subset_1 > k2_enumset1 > k4_subset_1 > k1_enumset1 > k4_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k2_subset_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

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

tff(f_45,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_68,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => k4_subset_1(A,B,k3_subset_1(A,B)) = k2_subset_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_subset_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,k3_subset_1(A,B)) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k3_subset_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_27,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

tff(f_37,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_43,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_35,axiom,(
    ! [A,B] : k4_xboole_0(A,k2_xboole_0(A,B)) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).

tff(f_33,axiom,(
    ! [A,B,C] : k4_xboole_0(k4_xboole_0(A,B),C) = k4_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_63,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(c_20,plain,(
    ! [A_19] : k2_subset_1(A_19) = A_19 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_30,plain,(
    k4_subset_1('#skF_1','#skF_2',k3_subset_1('#skF_1','#skF_2')) != k2_subset_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_33,plain,(
    k4_subset_1('#skF_1','#skF_2',k3_subset_1('#skF_1','#skF_2')) != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_30])).

tff(c_32,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_811,plain,(
    ! [A_65,B_66] :
      ( k3_subset_1(A_65,k3_subset_1(A_65,B_66)) = B_66
      | ~ m1_subset_1(B_66,k1_zfmisc_1(A_65)) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_814,plain,(
    k3_subset_1('#skF_1',k3_subset_1('#skF_1','#skF_2')) = '#skF_2' ),
    inference(resolution,[status(thm)],[c_32,c_811])).

tff(c_949,plain,(
    ! [A_69,B_70] :
      ( m1_subset_1(k3_subset_1(A_69,B_70),k1_zfmisc_1(A_69))
      | ~ m1_subset_1(B_70,k1_zfmisc_1(A_69)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_22,plain,(
    ! [A_20,B_21] :
      ( k4_xboole_0(A_20,B_21) = k3_subset_1(A_20,B_21)
      | ~ m1_subset_1(B_21,k1_zfmisc_1(A_20)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_4782,plain,(
    ! [A_122,B_123] :
      ( k4_xboole_0(A_122,k3_subset_1(A_122,B_123)) = k3_subset_1(A_122,k3_subset_1(A_122,B_123))
      | ~ m1_subset_1(B_123,k1_zfmisc_1(A_122)) ) ),
    inference(resolution,[status(thm)],[c_949,c_22])).

tff(c_4786,plain,(
    k4_xboole_0('#skF_1',k3_subset_1('#skF_1','#skF_2')) = k3_subset_1('#skF_1',k3_subset_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_32,c_4782])).

tff(c_4789,plain,(
    k4_xboole_0('#skF_1',k3_subset_1('#skF_1','#skF_2')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_814,c_4786])).

tff(c_2,plain,(
    ! [A_1] : k2_xboole_0(A_1,k1_xboole_0) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_12,plain,(
    ! [B_11,A_10] : k2_tarski(B_11,A_10) = k2_tarski(A_10,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_121,plain,(
    ! [A_37,B_38] : k3_tarski(k2_tarski(A_37,B_38)) = k2_xboole_0(A_37,B_38) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_145,plain,(
    ! [B_41,A_42] : k3_tarski(k2_tarski(B_41,A_42)) = k2_xboole_0(A_42,B_41) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_121])).

tff(c_18,plain,(
    ! [A_17,B_18] : k3_tarski(k2_tarski(A_17,B_18)) = k2_xboole_0(A_17,B_18) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_168,plain,(
    ! [B_43,A_44] : k2_xboole_0(B_43,A_44) = k2_xboole_0(A_44,B_43) ),
    inference(superposition,[status(thm),theory(equality)],[c_145,c_18])).

tff(c_10,plain,(
    ! [A_8,B_9] : k4_xboole_0(A_8,k2_xboole_0(A_8,B_9)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_183,plain,(
    ! [A_44,B_43] : k4_xboole_0(A_44,k2_xboole_0(B_43,A_44)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_168,c_10])).

tff(c_1531,plain,(
    ! [A_79,B_80,C_81] : k4_xboole_0(k4_xboole_0(A_79,B_80),C_81) = k4_xboole_0(A_79,k2_xboole_0(B_80,C_81)) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_4,plain,(
    ! [A_2,B_3] : k2_xboole_0(A_2,k4_xboole_0(B_3,A_2)) = k2_xboole_0(A_2,B_3) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_3711,plain,(
    ! [C_113,A_114,B_115] : k2_xboole_0(C_113,k4_xboole_0(A_114,k2_xboole_0(B_115,C_113))) = k2_xboole_0(C_113,k4_xboole_0(A_114,B_115)) ),
    inference(superposition,[status(thm),theory(equality)],[c_1531,c_4])).

tff(c_3880,plain,(
    ! [A_44,B_43] : k2_xboole_0(A_44,k4_xboole_0(A_44,B_43)) = k2_xboole_0(A_44,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_183,c_3711])).

tff(c_3956,plain,(
    ! [A_44,B_43] : k2_xboole_0(A_44,k4_xboole_0(A_44,B_43)) = A_44 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_3880])).

tff(c_4799,plain,(
    k2_xboole_0('#skF_1','#skF_2') = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_4789,c_3956])).

tff(c_151,plain,(
    ! [B_41,A_42] : k2_xboole_0(B_41,A_42) = k2_xboole_0(A_42,B_41) ),
    inference(superposition,[status(thm),theory(equality)],[c_145,c_18])).

tff(c_501,plain,(
    ! [A_57,B_58] :
      ( k4_xboole_0(A_57,B_58) = k3_subset_1(A_57,B_58)
      | ~ m1_subset_1(B_58,k1_zfmisc_1(A_57)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_505,plain,(
    k4_xboole_0('#skF_1','#skF_2') = k3_subset_1('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_32,c_501])).

tff(c_509,plain,(
    k2_xboole_0('#skF_2',k3_subset_1('#skF_1','#skF_2')) = k2_xboole_0('#skF_2','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_505,c_4])).

tff(c_512,plain,(
    k2_xboole_0('#skF_2',k3_subset_1('#skF_1','#skF_2')) = k2_xboole_0('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_151,c_509])).

tff(c_4830,plain,(
    k2_xboole_0('#skF_2',k3_subset_1('#skF_1','#skF_2')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4799,c_512])).

tff(c_24,plain,(
    ! [A_22,B_23] :
      ( m1_subset_1(k3_subset_1(A_22,B_23),k1_zfmisc_1(A_22))
      | ~ m1_subset_1(B_23,k1_zfmisc_1(A_22)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_2351,plain,(
    ! [A_94,B_95,C_96] :
      ( k4_subset_1(A_94,B_95,C_96) = k2_xboole_0(B_95,C_96)
      | ~ m1_subset_1(C_96,k1_zfmisc_1(A_94))
      | ~ m1_subset_1(B_95,k1_zfmisc_1(A_94)) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_6532,plain,(
    ! [A_136,B_137,B_138] :
      ( k4_subset_1(A_136,B_137,k3_subset_1(A_136,B_138)) = k2_xboole_0(B_137,k3_subset_1(A_136,B_138))
      | ~ m1_subset_1(B_137,k1_zfmisc_1(A_136))
      | ~ m1_subset_1(B_138,k1_zfmisc_1(A_136)) ) ),
    inference(resolution,[status(thm)],[c_24,c_2351])).

tff(c_6826,plain,(
    ! [B_141] :
      ( k4_subset_1('#skF_1','#skF_2',k3_subset_1('#skF_1',B_141)) = k2_xboole_0('#skF_2',k3_subset_1('#skF_1',B_141))
      | ~ m1_subset_1(B_141,k1_zfmisc_1('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_32,c_6532])).

tff(c_6833,plain,(
    k4_subset_1('#skF_1','#skF_2',k3_subset_1('#skF_1','#skF_2')) = k2_xboole_0('#skF_2',k3_subset_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_32,c_6826])).

tff(c_6836,plain,(
    k4_subset_1('#skF_1','#skF_2',k3_subset_1('#skF_1','#skF_2')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4830,c_6833])).

tff(c_6838,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_33,c_6836])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n018.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 14:13:42 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.54/2.20  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.54/2.21  
% 5.54/2.21  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.54/2.21  %$ m1_subset_1 > k2_enumset1 > k4_subset_1 > k1_enumset1 > k4_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k2_subset_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_1
% 5.54/2.21  
% 5.54/2.21  %Foreground sorts:
% 5.54/2.21  
% 5.54/2.21  
% 5.54/2.21  %Background operators:
% 5.54/2.21  
% 5.54/2.21  
% 5.54/2.21  %Foreground operators:
% 5.54/2.21  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.54/2.21  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 5.54/2.21  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.54/2.21  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 5.54/2.21  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 5.54/2.21  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 5.54/2.21  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 5.54/2.21  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 5.54/2.21  tff('#skF_2', type, '#skF_2': $i).
% 5.54/2.21  tff('#skF_1', type, '#skF_1': $i).
% 5.54/2.21  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.54/2.21  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.54/2.21  tff(k3_tarski, type, k3_tarski: $i > $i).
% 5.54/2.21  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.54/2.21  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 5.54/2.21  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 5.54/2.21  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.54/2.21  
% 5.73/2.23  tff(f_45, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 5.73/2.23  tff(f_68, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k4_subset_1(A, B, k3_subset_1(A, B)) = k2_subset_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t25_subset_1)).
% 5.73/2.23  tff(f_57, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, k3_subset_1(A, B)) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 5.73/2.23  tff(f_53, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k3_subset_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 5.73/2.23  tff(f_49, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_subset_1)).
% 5.73/2.23  tff(f_27, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 5.73/2.23  tff(f_37, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 5.73/2.23  tff(f_43, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 5.73/2.23  tff(f_35, axiom, (![A, B]: (k4_xboole_0(A, k2_xboole_0(A, B)) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_xboole_1)).
% 5.73/2.23  tff(f_33, axiom, (![A, B, C]: (k4_xboole_0(k4_xboole_0(A, B), C) = k4_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_xboole_1)).
% 5.73/2.23  tff(f_29, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_xboole_1)).
% 5.73/2.23  tff(f_63, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 5.73/2.23  tff(c_20, plain, (![A_19]: (k2_subset_1(A_19)=A_19)), inference(cnfTransformation, [status(thm)], [f_45])).
% 5.73/2.23  tff(c_30, plain, (k4_subset_1('#skF_1', '#skF_2', k3_subset_1('#skF_1', '#skF_2'))!=k2_subset_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_68])).
% 5.73/2.23  tff(c_33, plain, (k4_subset_1('#skF_1', '#skF_2', k3_subset_1('#skF_1', '#skF_2'))!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_20, c_30])).
% 5.73/2.23  tff(c_32, plain, (m1_subset_1('#skF_2', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_68])).
% 5.73/2.23  tff(c_811, plain, (![A_65, B_66]: (k3_subset_1(A_65, k3_subset_1(A_65, B_66))=B_66 | ~m1_subset_1(B_66, k1_zfmisc_1(A_65)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 5.73/2.23  tff(c_814, plain, (k3_subset_1('#skF_1', k3_subset_1('#skF_1', '#skF_2'))='#skF_2'), inference(resolution, [status(thm)], [c_32, c_811])).
% 5.73/2.23  tff(c_949, plain, (![A_69, B_70]: (m1_subset_1(k3_subset_1(A_69, B_70), k1_zfmisc_1(A_69)) | ~m1_subset_1(B_70, k1_zfmisc_1(A_69)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 5.73/2.23  tff(c_22, plain, (![A_20, B_21]: (k4_xboole_0(A_20, B_21)=k3_subset_1(A_20, B_21) | ~m1_subset_1(B_21, k1_zfmisc_1(A_20)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 5.73/2.23  tff(c_4782, plain, (![A_122, B_123]: (k4_xboole_0(A_122, k3_subset_1(A_122, B_123))=k3_subset_1(A_122, k3_subset_1(A_122, B_123)) | ~m1_subset_1(B_123, k1_zfmisc_1(A_122)))), inference(resolution, [status(thm)], [c_949, c_22])).
% 5.73/2.23  tff(c_4786, plain, (k4_xboole_0('#skF_1', k3_subset_1('#skF_1', '#skF_2'))=k3_subset_1('#skF_1', k3_subset_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_32, c_4782])).
% 5.73/2.23  tff(c_4789, plain, (k4_xboole_0('#skF_1', k3_subset_1('#skF_1', '#skF_2'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_814, c_4786])).
% 5.73/2.23  tff(c_2, plain, (![A_1]: (k2_xboole_0(A_1, k1_xboole_0)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 5.73/2.23  tff(c_12, plain, (![B_11, A_10]: (k2_tarski(B_11, A_10)=k2_tarski(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_37])).
% 5.73/2.23  tff(c_121, plain, (![A_37, B_38]: (k3_tarski(k2_tarski(A_37, B_38))=k2_xboole_0(A_37, B_38))), inference(cnfTransformation, [status(thm)], [f_43])).
% 5.73/2.23  tff(c_145, plain, (![B_41, A_42]: (k3_tarski(k2_tarski(B_41, A_42))=k2_xboole_0(A_42, B_41))), inference(superposition, [status(thm), theory('equality')], [c_12, c_121])).
% 5.73/2.23  tff(c_18, plain, (![A_17, B_18]: (k3_tarski(k2_tarski(A_17, B_18))=k2_xboole_0(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_43])).
% 5.73/2.23  tff(c_168, plain, (![B_43, A_44]: (k2_xboole_0(B_43, A_44)=k2_xboole_0(A_44, B_43))), inference(superposition, [status(thm), theory('equality')], [c_145, c_18])).
% 5.73/2.23  tff(c_10, plain, (![A_8, B_9]: (k4_xboole_0(A_8, k2_xboole_0(A_8, B_9))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_35])).
% 5.73/2.23  tff(c_183, plain, (![A_44, B_43]: (k4_xboole_0(A_44, k2_xboole_0(B_43, A_44))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_168, c_10])).
% 5.73/2.23  tff(c_1531, plain, (![A_79, B_80, C_81]: (k4_xboole_0(k4_xboole_0(A_79, B_80), C_81)=k4_xboole_0(A_79, k2_xboole_0(B_80, C_81)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 5.73/2.23  tff(c_4, plain, (![A_2, B_3]: (k2_xboole_0(A_2, k4_xboole_0(B_3, A_2))=k2_xboole_0(A_2, B_3))), inference(cnfTransformation, [status(thm)], [f_29])).
% 5.73/2.23  tff(c_3711, plain, (![C_113, A_114, B_115]: (k2_xboole_0(C_113, k4_xboole_0(A_114, k2_xboole_0(B_115, C_113)))=k2_xboole_0(C_113, k4_xboole_0(A_114, B_115)))), inference(superposition, [status(thm), theory('equality')], [c_1531, c_4])).
% 5.73/2.23  tff(c_3880, plain, (![A_44, B_43]: (k2_xboole_0(A_44, k4_xboole_0(A_44, B_43))=k2_xboole_0(A_44, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_183, c_3711])).
% 5.73/2.23  tff(c_3956, plain, (![A_44, B_43]: (k2_xboole_0(A_44, k4_xboole_0(A_44, B_43))=A_44)), inference(demodulation, [status(thm), theory('equality')], [c_2, c_3880])).
% 5.73/2.23  tff(c_4799, plain, (k2_xboole_0('#skF_1', '#skF_2')='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_4789, c_3956])).
% 5.73/2.23  tff(c_151, plain, (![B_41, A_42]: (k2_xboole_0(B_41, A_42)=k2_xboole_0(A_42, B_41))), inference(superposition, [status(thm), theory('equality')], [c_145, c_18])).
% 5.73/2.23  tff(c_501, plain, (![A_57, B_58]: (k4_xboole_0(A_57, B_58)=k3_subset_1(A_57, B_58) | ~m1_subset_1(B_58, k1_zfmisc_1(A_57)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 5.73/2.23  tff(c_505, plain, (k4_xboole_0('#skF_1', '#skF_2')=k3_subset_1('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_32, c_501])).
% 5.73/2.23  tff(c_509, plain, (k2_xboole_0('#skF_2', k3_subset_1('#skF_1', '#skF_2'))=k2_xboole_0('#skF_2', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_505, c_4])).
% 5.73/2.23  tff(c_512, plain, (k2_xboole_0('#skF_2', k3_subset_1('#skF_1', '#skF_2'))=k2_xboole_0('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_151, c_509])).
% 5.73/2.23  tff(c_4830, plain, (k2_xboole_0('#skF_2', k3_subset_1('#skF_1', '#skF_2'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_4799, c_512])).
% 5.73/2.23  tff(c_24, plain, (![A_22, B_23]: (m1_subset_1(k3_subset_1(A_22, B_23), k1_zfmisc_1(A_22)) | ~m1_subset_1(B_23, k1_zfmisc_1(A_22)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 5.73/2.23  tff(c_2351, plain, (![A_94, B_95, C_96]: (k4_subset_1(A_94, B_95, C_96)=k2_xboole_0(B_95, C_96) | ~m1_subset_1(C_96, k1_zfmisc_1(A_94)) | ~m1_subset_1(B_95, k1_zfmisc_1(A_94)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 5.73/2.23  tff(c_6532, plain, (![A_136, B_137, B_138]: (k4_subset_1(A_136, B_137, k3_subset_1(A_136, B_138))=k2_xboole_0(B_137, k3_subset_1(A_136, B_138)) | ~m1_subset_1(B_137, k1_zfmisc_1(A_136)) | ~m1_subset_1(B_138, k1_zfmisc_1(A_136)))), inference(resolution, [status(thm)], [c_24, c_2351])).
% 5.73/2.23  tff(c_6826, plain, (![B_141]: (k4_subset_1('#skF_1', '#skF_2', k3_subset_1('#skF_1', B_141))=k2_xboole_0('#skF_2', k3_subset_1('#skF_1', B_141)) | ~m1_subset_1(B_141, k1_zfmisc_1('#skF_1')))), inference(resolution, [status(thm)], [c_32, c_6532])).
% 5.73/2.23  tff(c_6833, plain, (k4_subset_1('#skF_1', '#skF_2', k3_subset_1('#skF_1', '#skF_2'))=k2_xboole_0('#skF_2', k3_subset_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_32, c_6826])).
% 5.73/2.23  tff(c_6836, plain, (k4_subset_1('#skF_1', '#skF_2', k3_subset_1('#skF_1', '#skF_2'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_4830, c_6833])).
% 5.73/2.23  tff(c_6838, plain, $false, inference(negUnitSimplification, [status(thm)], [c_33, c_6836])).
% 5.73/2.23  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.73/2.23  
% 5.73/2.23  Inference rules
% 5.73/2.23  ----------------------
% 5.73/2.23  #Ref     : 0
% 5.73/2.23  #Sup     : 1685
% 5.73/2.23  #Fact    : 0
% 5.73/2.23  #Define  : 0
% 5.73/2.23  #Split   : 0
% 5.73/2.23  #Chain   : 0
% 5.73/2.23  #Close   : 0
% 5.73/2.23  
% 5.73/2.23  Ordering : KBO
% 5.73/2.23  
% 5.73/2.23  Simplification rules
% 5.73/2.23  ----------------------
% 5.73/2.23  #Subsume      : 22
% 5.73/2.23  #Demod        : 1805
% 5.73/2.23  #Tautology    : 1257
% 5.73/2.23  #SimpNegUnit  : 1
% 5.73/2.23  #BackRed      : 4
% 5.73/2.23  
% 5.73/2.23  #Partial instantiations: 0
% 5.73/2.23  #Strategies tried      : 1
% 5.73/2.23  
% 5.73/2.23  Timing (in seconds)
% 5.73/2.23  ----------------------
% 5.73/2.23  Preprocessing        : 0.31
% 5.73/2.23  Parsing              : 0.17
% 5.73/2.23  CNF conversion       : 0.02
% 5.73/2.23  Main loop            : 1.13
% 5.73/2.23  Inferencing          : 0.29
% 5.73/2.23  Reduction            : 0.61
% 5.73/2.23  Demodulation         : 0.53
% 5.73/2.23  BG Simplification    : 0.03
% 5.73/2.23  Subsumption          : 0.14
% 5.73/2.23  Abstraction          : 0.05
% 5.73/2.23  MUC search           : 0.00
% 5.73/2.23  Cooper               : 0.00
% 5.73/2.23  Total                : 1.47
% 5.73/2.23  Index Insertion      : 0.00
% 5.73/2.23  Index Deletion       : 0.00
% 5.73/2.23  Index Matching       : 0.00
% 5.73/2.23  BG Taut test         : 0.00
%------------------------------------------------------------------------------
