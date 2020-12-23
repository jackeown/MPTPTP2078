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
% DateTime   : Thu Dec  3 09:55:54 EST 2020

% Result     : Theorem 6.45s
% Output     : CNFRefutation 6.63s
% Verified   : 
% Statistics : Number of formulae       :   59 ( 102 expanded)
%              Number of leaves         :   23 (  44 expanded)
%              Depth                    :    9
%              Number of atoms          :   62 ( 136 expanded)
%              Number of equality atoms :   40 (  73 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m1_subset_1 > k9_subset_1 > k7_subset_1 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k7_subset_1,type,(
    k7_subset_1: ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_61,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => ! [C] :
            ( m1_subset_1(C,k1_zfmisc_1(A))
           => k7_subset_1(A,B,C) = k9_subset_1(A,B,k3_subset_1(A,C)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_subset_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,k3_subset_1(A,B)) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

tff(f_33,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k3_subset_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_31,axiom,(
    ! [A,B] : k4_xboole_0(A,k3_xboole_0(A,B)) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).

tff(f_29,axiom,(
    ! [A,B,C] : k4_xboole_0(k3_xboole_0(A,B),k3_xboole_0(C,B)) = k3_xboole_0(k4_xboole_0(A,C),B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t111_xboole_1)).

tff(f_53,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(f_49,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

tff(c_22,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_92,plain,(
    ! [A_29,B_30] :
      ( k4_xboole_0(A_29,B_30) = k3_subset_1(A_29,B_30)
      | ~ m1_subset_1(B_30,k1_zfmisc_1(A_29)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_99,plain,(
    k4_xboole_0('#skF_1','#skF_3') = k3_subset_1('#skF_1','#skF_3') ),
    inference(resolution,[status(thm)],[c_22,c_92])).

tff(c_24,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_241,plain,(
    ! [A_37,B_38] :
      ( k3_subset_1(A_37,k3_subset_1(A_37,B_38)) = B_38
      | ~ m1_subset_1(B_38,k1_zfmisc_1(A_37)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_247,plain,(
    k3_subset_1('#skF_1',k3_subset_1('#skF_1','#skF_2')) = '#skF_2' ),
    inference(resolution,[status(thm)],[c_24,c_241])).

tff(c_100,plain,(
    k4_xboole_0('#skF_1','#skF_2') = k3_subset_1('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_24,c_92])).

tff(c_8,plain,(
    ! [A_8,B_9] : k4_xboole_0(A_8,k4_xboole_0(A_8,B_9)) = k3_xboole_0(A_8,B_9) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_111,plain,(
    k4_xboole_0('#skF_1',k3_subset_1('#skF_1','#skF_2')) = k3_xboole_0('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_100,c_8])).

tff(c_296,plain,(
    ! [A_39,B_40] :
      ( m1_subset_1(k3_subset_1(A_39,B_40),k1_zfmisc_1(A_39))
      | ~ m1_subset_1(B_40,k1_zfmisc_1(A_39)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_10,plain,(
    ! [A_10,B_11] :
      ( k4_xboole_0(A_10,B_11) = k3_subset_1(A_10,B_11)
      | ~ m1_subset_1(B_11,k1_zfmisc_1(A_10)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_3046,plain,(
    ! [A_85,B_86] :
      ( k4_xboole_0(A_85,k3_subset_1(A_85,B_86)) = k3_subset_1(A_85,k3_subset_1(A_85,B_86))
      | ~ m1_subset_1(B_86,k1_zfmisc_1(A_85)) ) ),
    inference(resolution,[status(thm)],[c_296,c_10])).

tff(c_3052,plain,(
    k4_xboole_0('#skF_1',k3_subset_1('#skF_1','#skF_2')) = k3_subset_1('#skF_1',k3_subset_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_24,c_3046])).

tff(c_3057,plain,(
    k3_xboole_0('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_247,c_111,c_3052])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_6,plain,(
    ! [A_6,B_7] : k4_xboole_0(A_6,k3_xboole_0(A_6,B_7)) = k4_xboole_0(A_6,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_73,plain,(
    ! [A_27,B_28] : k4_xboole_0(A_27,k3_xboole_0(A_27,B_28)) = k4_xboole_0(A_27,B_28) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_79,plain,(
    ! [A_27,B_28] : k4_xboole_0(A_27,k4_xboole_0(A_27,B_28)) = k3_xboole_0(A_27,k3_xboole_0(A_27,B_28)) ),
    inference(superposition,[status(thm),theory(equality)],[c_73,c_8])).

tff(c_90,plain,(
    ! [A_27,B_28] : k3_xboole_0(A_27,k3_xboole_0(A_27,B_28)) = k3_xboole_0(A_27,B_28) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_79])).

tff(c_1021,plain,(
    ! [A_61,B_62,C_63] : k4_xboole_0(k3_xboole_0(A_61,B_62),k3_xboole_0(C_63,B_62)) = k3_xboole_0(k4_xboole_0(A_61,C_63),B_62) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_1720,plain,(
    ! [A_73,A_74,B_75] : k4_xboole_0(k3_xboole_0(A_73,A_74),k3_xboole_0(A_74,B_75)) = k3_xboole_0(k4_xboole_0(A_73,B_75),A_74) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_1021])).

tff(c_1835,plain,(
    ! [A_27,B_28,B_75] : k4_xboole_0(k3_xboole_0(A_27,B_28),k3_xboole_0(k3_xboole_0(A_27,B_28),B_75)) = k3_xboole_0(k4_xboole_0(A_27,B_75),k3_xboole_0(A_27,B_28)) ),
    inference(superposition,[status(thm),theory(equality)],[c_90,c_1720])).

tff(c_1886,plain,(
    ! [A_27,B_75,B_28] : k3_xboole_0(k4_xboole_0(A_27,B_75),k3_xboole_0(A_27,B_28)) = k4_xboole_0(k3_xboole_0(A_27,B_28),B_75) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_1835])).

tff(c_3149,plain,(
    ! [B_75] : k4_xboole_0(k3_xboole_0('#skF_1','#skF_2'),B_75) = k3_xboole_0(k4_xboole_0('#skF_1',B_75),'#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_3057,c_1886])).

tff(c_3908,plain,(
    ! [B_94] : k3_xboole_0('#skF_2',k4_xboole_0('#skF_1',B_94)) = k4_xboole_0('#skF_2',B_94) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3057,c_2,c_3149])).

tff(c_4009,plain,(
    k3_xboole_0('#skF_2',k3_subset_1('#skF_1','#skF_3')) = k4_xboole_0('#skF_2','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_99,c_3908])).

tff(c_12,plain,(
    ! [A_12,B_13] :
      ( m1_subset_1(k3_subset_1(A_12,B_13),k1_zfmisc_1(A_12))
      | ~ m1_subset_1(B_13,k1_zfmisc_1(A_12)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_366,plain,(
    ! [A_43,B_44,C_45] :
      ( k9_subset_1(A_43,B_44,C_45) = k3_xboole_0(B_44,C_45)
      | ~ m1_subset_1(C_45,k1_zfmisc_1(A_43)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_4503,plain,(
    ! [A_97,B_98,B_99] :
      ( k9_subset_1(A_97,B_98,k3_subset_1(A_97,B_99)) = k3_xboole_0(B_98,k3_subset_1(A_97,B_99))
      | ~ m1_subset_1(B_99,k1_zfmisc_1(A_97)) ) ),
    inference(resolution,[status(thm)],[c_12,c_366])).

tff(c_4511,plain,(
    ! [B_98] : k9_subset_1('#skF_1',B_98,k3_subset_1('#skF_1','#skF_3')) = k3_xboole_0(B_98,k3_subset_1('#skF_1','#skF_3')) ),
    inference(resolution,[status(thm)],[c_22,c_4503])).

tff(c_772,plain,(
    ! [A_54,B_55,C_56] :
      ( k7_subset_1(A_54,B_55,C_56) = k4_xboole_0(B_55,C_56)
      | ~ m1_subset_1(B_55,k1_zfmisc_1(A_54)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_781,plain,(
    ! [C_56] : k7_subset_1('#skF_1','#skF_2',C_56) = k4_xboole_0('#skF_2',C_56) ),
    inference(resolution,[status(thm)],[c_24,c_772])).

tff(c_20,plain,(
    k9_subset_1('#skF_1','#skF_2',k3_subset_1('#skF_1','#skF_3')) != k7_subset_1('#skF_1','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_791,plain,(
    k9_subset_1('#skF_1','#skF_2',k3_subset_1('#skF_1','#skF_3')) != k4_xboole_0('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_781,c_20])).

tff(c_5331,plain,(
    k3_xboole_0('#skF_2',k3_subset_1('#skF_1','#skF_3')) != k4_xboole_0('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4511,c_791])).

tff(c_5334,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4009,c_5331])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:46:04 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.45/2.57  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.45/2.58  
% 6.45/2.58  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.45/2.58  %$ m1_subset_1 > k9_subset_1 > k7_subset_1 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1
% 6.45/2.58  
% 6.45/2.58  %Foreground sorts:
% 6.45/2.58  
% 6.45/2.58  
% 6.45/2.58  %Background operators:
% 6.45/2.58  
% 6.45/2.58  
% 6.45/2.58  %Foreground operators:
% 6.45/2.58  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.45/2.58  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 6.45/2.58  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 6.45/2.58  tff('#skF_2', type, '#skF_2': $i).
% 6.45/2.58  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 6.45/2.58  tff('#skF_3', type, '#skF_3': $i).
% 6.45/2.58  tff('#skF_1', type, '#skF_1': $i).
% 6.45/2.58  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 6.45/2.58  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.45/2.58  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.45/2.58  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 6.45/2.58  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 6.45/2.58  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 6.45/2.58  
% 6.63/2.59  tff(f_61, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k9_subset_1(A, B, k3_subset_1(A, C))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t32_subset_1)).
% 6.63/2.59  tff(f_37, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_subset_1)).
% 6.63/2.59  tff(f_45, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, k3_subset_1(A, B)) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 6.63/2.59  tff(f_33, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 6.63/2.59  tff(f_41, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k3_subset_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 6.63/2.59  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 6.63/2.59  tff(f_31, axiom, (![A, B]: (k4_xboole_0(A, k3_xboole_0(A, B)) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_xboole_1)).
% 6.63/2.59  tff(f_29, axiom, (![A, B, C]: (k4_xboole_0(k3_xboole_0(A, B), k3_xboole_0(C, B)) = k3_xboole_0(k4_xboole_0(A, C), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t111_xboole_1)).
% 6.63/2.59  tff(f_53, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 6.63/2.59  tff(f_49, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 6.63/2.59  tff(c_22, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_61])).
% 6.63/2.59  tff(c_92, plain, (![A_29, B_30]: (k4_xboole_0(A_29, B_30)=k3_subset_1(A_29, B_30) | ~m1_subset_1(B_30, k1_zfmisc_1(A_29)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 6.63/2.59  tff(c_99, plain, (k4_xboole_0('#skF_1', '#skF_3')=k3_subset_1('#skF_1', '#skF_3')), inference(resolution, [status(thm)], [c_22, c_92])).
% 6.63/2.59  tff(c_24, plain, (m1_subset_1('#skF_2', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_61])).
% 6.63/2.59  tff(c_241, plain, (![A_37, B_38]: (k3_subset_1(A_37, k3_subset_1(A_37, B_38))=B_38 | ~m1_subset_1(B_38, k1_zfmisc_1(A_37)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 6.63/2.59  tff(c_247, plain, (k3_subset_1('#skF_1', k3_subset_1('#skF_1', '#skF_2'))='#skF_2'), inference(resolution, [status(thm)], [c_24, c_241])).
% 6.63/2.59  tff(c_100, plain, (k4_xboole_0('#skF_1', '#skF_2')=k3_subset_1('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_24, c_92])).
% 6.63/2.59  tff(c_8, plain, (![A_8, B_9]: (k4_xboole_0(A_8, k4_xboole_0(A_8, B_9))=k3_xboole_0(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_33])).
% 6.63/2.59  tff(c_111, plain, (k4_xboole_0('#skF_1', k3_subset_1('#skF_1', '#skF_2'))=k3_xboole_0('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_100, c_8])).
% 6.63/2.59  tff(c_296, plain, (![A_39, B_40]: (m1_subset_1(k3_subset_1(A_39, B_40), k1_zfmisc_1(A_39)) | ~m1_subset_1(B_40, k1_zfmisc_1(A_39)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 6.63/2.59  tff(c_10, plain, (![A_10, B_11]: (k4_xboole_0(A_10, B_11)=k3_subset_1(A_10, B_11) | ~m1_subset_1(B_11, k1_zfmisc_1(A_10)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 6.63/2.59  tff(c_3046, plain, (![A_85, B_86]: (k4_xboole_0(A_85, k3_subset_1(A_85, B_86))=k3_subset_1(A_85, k3_subset_1(A_85, B_86)) | ~m1_subset_1(B_86, k1_zfmisc_1(A_85)))), inference(resolution, [status(thm)], [c_296, c_10])).
% 6.63/2.59  tff(c_3052, plain, (k4_xboole_0('#skF_1', k3_subset_1('#skF_1', '#skF_2'))=k3_subset_1('#skF_1', k3_subset_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_24, c_3046])).
% 6.63/2.59  tff(c_3057, plain, (k3_xboole_0('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_247, c_111, c_3052])).
% 6.63/2.59  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 6.63/2.59  tff(c_6, plain, (![A_6, B_7]: (k4_xboole_0(A_6, k3_xboole_0(A_6, B_7))=k4_xboole_0(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_31])).
% 6.63/2.59  tff(c_73, plain, (![A_27, B_28]: (k4_xboole_0(A_27, k3_xboole_0(A_27, B_28))=k4_xboole_0(A_27, B_28))), inference(cnfTransformation, [status(thm)], [f_31])).
% 6.63/2.59  tff(c_79, plain, (![A_27, B_28]: (k4_xboole_0(A_27, k4_xboole_0(A_27, B_28))=k3_xboole_0(A_27, k3_xboole_0(A_27, B_28)))), inference(superposition, [status(thm), theory('equality')], [c_73, c_8])).
% 6.63/2.59  tff(c_90, plain, (![A_27, B_28]: (k3_xboole_0(A_27, k3_xboole_0(A_27, B_28))=k3_xboole_0(A_27, B_28))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_79])).
% 6.63/2.59  tff(c_1021, plain, (![A_61, B_62, C_63]: (k4_xboole_0(k3_xboole_0(A_61, B_62), k3_xboole_0(C_63, B_62))=k3_xboole_0(k4_xboole_0(A_61, C_63), B_62))), inference(cnfTransformation, [status(thm)], [f_29])).
% 6.63/2.59  tff(c_1720, plain, (![A_73, A_74, B_75]: (k4_xboole_0(k3_xboole_0(A_73, A_74), k3_xboole_0(A_74, B_75))=k3_xboole_0(k4_xboole_0(A_73, B_75), A_74))), inference(superposition, [status(thm), theory('equality')], [c_2, c_1021])).
% 6.63/2.59  tff(c_1835, plain, (![A_27, B_28, B_75]: (k4_xboole_0(k3_xboole_0(A_27, B_28), k3_xboole_0(k3_xboole_0(A_27, B_28), B_75))=k3_xboole_0(k4_xboole_0(A_27, B_75), k3_xboole_0(A_27, B_28)))), inference(superposition, [status(thm), theory('equality')], [c_90, c_1720])).
% 6.63/2.59  tff(c_1886, plain, (![A_27, B_75, B_28]: (k3_xboole_0(k4_xboole_0(A_27, B_75), k3_xboole_0(A_27, B_28))=k4_xboole_0(k3_xboole_0(A_27, B_28), B_75))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_1835])).
% 6.63/2.59  tff(c_3149, plain, (![B_75]: (k4_xboole_0(k3_xboole_0('#skF_1', '#skF_2'), B_75)=k3_xboole_0(k4_xboole_0('#skF_1', B_75), '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_3057, c_1886])).
% 6.63/2.59  tff(c_3908, plain, (![B_94]: (k3_xboole_0('#skF_2', k4_xboole_0('#skF_1', B_94))=k4_xboole_0('#skF_2', B_94))), inference(demodulation, [status(thm), theory('equality')], [c_3057, c_2, c_3149])).
% 6.63/2.59  tff(c_4009, plain, (k3_xboole_0('#skF_2', k3_subset_1('#skF_1', '#skF_3'))=k4_xboole_0('#skF_2', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_99, c_3908])).
% 6.63/2.59  tff(c_12, plain, (![A_12, B_13]: (m1_subset_1(k3_subset_1(A_12, B_13), k1_zfmisc_1(A_12)) | ~m1_subset_1(B_13, k1_zfmisc_1(A_12)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 6.63/2.59  tff(c_366, plain, (![A_43, B_44, C_45]: (k9_subset_1(A_43, B_44, C_45)=k3_xboole_0(B_44, C_45) | ~m1_subset_1(C_45, k1_zfmisc_1(A_43)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 6.63/2.59  tff(c_4503, plain, (![A_97, B_98, B_99]: (k9_subset_1(A_97, B_98, k3_subset_1(A_97, B_99))=k3_xboole_0(B_98, k3_subset_1(A_97, B_99)) | ~m1_subset_1(B_99, k1_zfmisc_1(A_97)))), inference(resolution, [status(thm)], [c_12, c_366])).
% 6.63/2.59  tff(c_4511, plain, (![B_98]: (k9_subset_1('#skF_1', B_98, k3_subset_1('#skF_1', '#skF_3'))=k3_xboole_0(B_98, k3_subset_1('#skF_1', '#skF_3')))), inference(resolution, [status(thm)], [c_22, c_4503])).
% 6.63/2.59  tff(c_772, plain, (![A_54, B_55, C_56]: (k7_subset_1(A_54, B_55, C_56)=k4_xboole_0(B_55, C_56) | ~m1_subset_1(B_55, k1_zfmisc_1(A_54)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 6.63/2.59  tff(c_781, plain, (![C_56]: (k7_subset_1('#skF_1', '#skF_2', C_56)=k4_xboole_0('#skF_2', C_56))), inference(resolution, [status(thm)], [c_24, c_772])).
% 6.63/2.59  tff(c_20, plain, (k9_subset_1('#skF_1', '#skF_2', k3_subset_1('#skF_1', '#skF_3'))!=k7_subset_1('#skF_1', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_61])).
% 6.63/2.59  tff(c_791, plain, (k9_subset_1('#skF_1', '#skF_2', k3_subset_1('#skF_1', '#skF_3'))!=k4_xboole_0('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_781, c_20])).
% 6.63/2.59  tff(c_5331, plain, (k3_xboole_0('#skF_2', k3_subset_1('#skF_1', '#skF_3'))!=k4_xboole_0('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_4511, c_791])).
% 6.63/2.59  tff(c_5334, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4009, c_5331])).
% 6.63/2.59  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.63/2.59  
% 6.63/2.59  Inference rules
% 6.63/2.59  ----------------------
% 6.63/2.59  #Ref     : 0
% 6.63/2.59  #Sup     : 1403
% 6.63/2.59  #Fact    : 0
% 6.63/2.59  #Define  : 0
% 6.63/2.59  #Split   : 0
% 6.63/2.59  #Chain   : 0
% 6.63/2.59  #Close   : 0
% 6.63/2.59  
% 6.63/2.59  Ordering : KBO
% 6.63/2.59  
% 6.63/2.59  Simplification rules
% 6.63/2.59  ----------------------
% 6.63/2.59  #Subsume      : 60
% 6.63/2.59  #Demod        : 1840
% 6.63/2.59  #Tautology    : 655
% 6.63/2.59  #SimpNegUnit  : 0
% 6.63/2.59  #BackRed      : 4
% 6.63/2.59  
% 6.63/2.59  #Partial instantiations: 0
% 6.63/2.59  #Strategies tried      : 1
% 6.63/2.59  
% 6.63/2.59  Timing (in seconds)
% 6.63/2.59  ----------------------
% 6.63/2.60  Preprocessing        : 0.43
% 6.63/2.60  Parsing              : 0.25
% 6.63/2.60  CNF conversion       : 0.02
% 6.63/2.60  Main loop            : 1.31
% 6.63/2.60  Inferencing          : 0.35
% 6.63/2.60  Reduction            : 0.68
% 6.63/2.60  Demodulation         : 0.60
% 6.63/2.60  BG Simplification    : 0.05
% 6.63/2.60  Subsumption          : 0.17
% 6.63/2.60  Abstraction          : 0.07
% 6.63/2.60  MUC search           : 0.00
% 6.63/2.60  Cooper               : 0.00
% 6.63/2.60  Total                : 1.78
% 6.63/2.60  Index Insertion      : 0.00
% 6.63/2.60  Index Deletion       : 0.00
% 6.63/2.60  Index Matching       : 0.00
% 6.63/2.60  BG Taut test         : 0.00
%------------------------------------------------------------------------------
