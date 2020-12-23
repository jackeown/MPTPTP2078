%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:55:54 EST 2020

% Result     : Theorem 4.54s
% Output     : CNFRefutation 4.54s
% Verified   : 
% Statistics : Number of formulae       :   64 ( 112 expanded)
%              Number of leaves         :   26 (  48 expanded)
%              Depth                    :   10
%              Number of atoms          :   59 ( 137 expanded)
%              Number of equality atoms :   43 (  79 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m1_subset_1 > k9_subset_1 > k7_subset_1 > k6_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k7_subset_1,type,(
    k7_subset_1: ( $i * $i * $i ) > $i )).

tff(k6_subset_1,type,(
    k6_subset_1: ( $i * $i ) > $i )).

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

tff(f_63,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => ! [C] :
            ( m1_subset_1(C,k1_zfmisc_1(A))
           => k7_subset_1(A,B,C) = k9_subset_1(A,B,k3_subset_1(A,C)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_subset_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,k3_subset_1(A,B)) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

tff(f_35,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_47,axiom,(
    ! [A,B] : k6_subset_1(A,B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

tff(f_41,axiom,(
    ! [A,B] : m1_subset_1(k6_subset_1(A,B),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_subset_1)).

tff(f_31,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_33,axiom,(
    ! [A,B,C] : k5_xboole_0(k3_xboole_0(A,B),k3_xboole_0(C,B)) = k3_xboole_0(k5_xboole_0(A,C),B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t112_xboole_1)).

tff(f_55,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

tff(c_26,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_183,plain,(
    ! [A_46,B_47] :
      ( k4_xboole_0(A_46,B_47) = k3_subset_1(A_46,B_47)
      | ~ m1_subset_1(B_47,k1_zfmisc_1(A_46)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_207,plain,(
    k4_xboole_0('#skF_1','#skF_3') = k3_subset_1('#skF_1','#skF_3') ),
    inference(resolution,[status(thm)],[c_26,c_183])).

tff(c_295,plain,(
    ! [A_53,B_54] :
      ( k3_subset_1(A_53,k3_subset_1(A_53,B_54)) = B_54
      | ~ m1_subset_1(B_54,k1_zfmisc_1(A_53)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_323,plain,(
    k3_subset_1('#skF_1',k3_subset_1('#skF_1','#skF_3')) = '#skF_3' ),
    inference(resolution,[status(thm)],[c_26,c_295])).

tff(c_10,plain,(
    ! [A_10,B_11] : k4_xboole_0(A_10,k4_xboole_0(A_10,B_11)) = k3_xboole_0(A_10,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_18,plain,(
    ! [A_18,B_19] : k6_subset_1(A_18,B_19) = k4_xboole_0(A_18,B_19) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_14,plain,(
    ! [A_14,B_15] : m1_subset_1(k6_subset_1(A_14,B_15),k1_zfmisc_1(A_14)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_29,plain,(
    ! [A_14,B_15] : m1_subset_1(k4_xboole_0(A_14,B_15),k1_zfmisc_1(A_14)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_14])).

tff(c_195,plain,(
    ! [A_14,B_15] : k4_xboole_0(A_14,k4_xboole_0(A_14,B_15)) = k3_subset_1(A_14,k4_xboole_0(A_14,B_15)) ),
    inference(resolution,[status(thm)],[c_29,c_183])).

tff(c_333,plain,(
    ! [A_55,B_56] : k3_subset_1(A_55,k4_xboole_0(A_55,B_56)) = k3_xboole_0(A_55,B_56) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_195])).

tff(c_351,plain,(
    k3_subset_1('#skF_1',k3_subset_1('#skF_1','#skF_3')) = k3_xboole_0('#skF_1','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_207,c_333])).

tff(c_359,plain,(
    k3_xboole_0('#skF_1','#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_323,c_351])).

tff(c_6,plain,(
    ! [A_5,B_6] : k5_xboole_0(A_5,k3_xboole_0(A_5,B_6)) = k4_xboole_0(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_407,plain,(
    k5_xboole_0('#skF_1','#skF_3') = k4_xboole_0('#skF_1','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_359,c_6])).

tff(c_413,plain,(
    k5_xboole_0('#skF_1','#skF_3') = k3_subset_1('#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_207,c_407])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_82,plain,(
    ! [A_34,B_35] : k5_xboole_0(A_34,k3_xboole_0(A_34,B_35)) = k4_xboole_0(A_34,B_35) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_91,plain,(
    ! [A_1,B_2] : k5_xboole_0(A_1,k3_xboole_0(B_2,A_1)) = k4_xboole_0(A_1,B_2) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_82])).

tff(c_28,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_324,plain,(
    k3_subset_1('#skF_1',k3_subset_1('#skF_1','#skF_2')) = '#skF_2' ),
    inference(resolution,[status(thm)],[c_28,c_295])).

tff(c_208,plain,(
    k4_xboole_0('#skF_1','#skF_2') = k3_subset_1('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_28,c_183])).

tff(c_348,plain,(
    k3_subset_1('#skF_1',k3_subset_1('#skF_1','#skF_2')) = k3_xboole_0('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_208,c_333])).

tff(c_358,plain,(
    k3_xboole_0('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_324,c_348])).

tff(c_670,plain,(
    ! [A_72,B_73,C_74] : k5_xboole_0(k3_xboole_0(A_72,B_73),k3_xboole_0(C_74,B_73)) = k3_xboole_0(k5_xboole_0(A_72,C_74),B_73) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_711,plain,(
    ! [C_74] : k5_xboole_0('#skF_2',k3_xboole_0(C_74,'#skF_2')) = k3_xboole_0(k5_xboole_0('#skF_1',C_74),'#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_358,c_670])).

tff(c_919,plain,(
    ! [C_79] : k3_xboole_0('#skF_2',k5_xboole_0('#skF_1',C_79)) = k4_xboole_0('#skF_2',C_79) ),
    inference(demodulation,[status(thm),theory(equality)],[c_91,c_2,c_711])).

tff(c_956,plain,(
    k3_xboole_0('#skF_2',k3_subset_1('#skF_1','#skF_3')) = k4_xboole_0('#skF_2','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_413,c_919])).

tff(c_566,plain,(
    ! [A_64,B_65,C_66] :
      ( k9_subset_1(A_64,B_65,C_66) = k3_xboole_0(B_65,C_66)
      | ~ m1_subset_1(C_66,k1_zfmisc_1(A_64)) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_3280,plain,(
    ! [A_116,B_117,B_118] : k9_subset_1(A_116,B_117,k4_xboole_0(A_116,B_118)) = k3_xboole_0(B_117,k4_xboole_0(A_116,B_118)) ),
    inference(resolution,[status(thm)],[c_29,c_566])).

tff(c_3346,plain,(
    ! [B_117] : k9_subset_1('#skF_1',B_117,k3_subset_1('#skF_1','#skF_3')) = k3_xboole_0(B_117,k4_xboole_0('#skF_1','#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_207,c_3280])).

tff(c_3371,plain,(
    ! [B_117] : k9_subset_1('#skF_1',B_117,k3_subset_1('#skF_1','#skF_3')) = k3_xboole_0(B_117,k3_subset_1('#skF_1','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_207,c_3346])).

tff(c_450,plain,(
    ! [A_57,B_58,C_59] :
      ( k7_subset_1(A_57,B_58,C_59) = k4_xboole_0(B_58,C_59)
      | ~ m1_subset_1(B_58,k1_zfmisc_1(A_57)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_477,plain,(
    ! [C_59] : k7_subset_1('#skF_1','#skF_2',C_59) = k4_xboole_0('#skF_2',C_59) ),
    inference(resolution,[status(thm)],[c_28,c_450])).

tff(c_24,plain,(
    k9_subset_1('#skF_1','#skF_2',k3_subset_1('#skF_1','#skF_3')) != k7_subset_1('#skF_1','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_507,plain,(
    k9_subset_1('#skF_1','#skF_2',k3_subset_1('#skF_1','#skF_3')) != k4_xboole_0('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_477,c_24])).

tff(c_3517,plain,(
    k3_xboole_0('#skF_2',k3_subset_1('#skF_1','#skF_3')) != k4_xboole_0('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3371,c_507])).

tff(c_3520,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_956,c_3517])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:32:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.54/1.81  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.54/1.82  
% 4.54/1.82  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.54/1.82  %$ m1_subset_1 > k9_subset_1 > k7_subset_1 > k6_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1
% 4.54/1.82  
% 4.54/1.82  %Foreground sorts:
% 4.54/1.82  
% 4.54/1.82  
% 4.54/1.82  %Background operators:
% 4.54/1.82  
% 4.54/1.82  
% 4.54/1.82  %Foreground operators:
% 4.54/1.82  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.54/1.82  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.54/1.82  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 4.54/1.82  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 4.54/1.82  tff('#skF_2', type, '#skF_2': $i).
% 4.54/1.82  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 4.54/1.82  tff(k6_subset_1, type, k6_subset_1: ($i * $i) > $i).
% 4.54/1.82  tff('#skF_3', type, '#skF_3': $i).
% 4.54/1.82  tff('#skF_1', type, '#skF_1': $i).
% 4.54/1.82  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.54/1.82  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.54/1.82  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.54/1.82  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.54/1.82  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 4.54/1.82  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.54/1.82  
% 4.54/1.83  tff(f_63, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k9_subset_1(A, B, k3_subset_1(A, C))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t32_subset_1)).
% 4.54/1.83  tff(f_39, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 4.54/1.83  tff(f_45, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, k3_subset_1(A, B)) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 4.54/1.83  tff(f_35, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 4.54/1.83  tff(f_47, axiom, (![A, B]: (k6_subset_1(A, B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 4.54/1.83  tff(f_41, axiom, (![A, B]: m1_subset_1(k6_subset_1(A, B), k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_subset_1)).
% 4.54/1.83  tff(f_31, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 4.54/1.83  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 4.54/1.83  tff(f_33, axiom, (![A, B, C]: (k5_xboole_0(k3_xboole_0(A, B), k3_xboole_0(C, B)) = k3_xboole_0(k5_xboole_0(A, C), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t112_xboole_1)).
% 4.54/1.83  tff(f_55, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 4.54/1.83  tff(f_51, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 4.54/1.83  tff(c_26, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_63])).
% 4.54/1.83  tff(c_183, plain, (![A_46, B_47]: (k4_xboole_0(A_46, B_47)=k3_subset_1(A_46, B_47) | ~m1_subset_1(B_47, k1_zfmisc_1(A_46)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.54/1.83  tff(c_207, plain, (k4_xboole_0('#skF_1', '#skF_3')=k3_subset_1('#skF_1', '#skF_3')), inference(resolution, [status(thm)], [c_26, c_183])).
% 4.54/1.83  tff(c_295, plain, (![A_53, B_54]: (k3_subset_1(A_53, k3_subset_1(A_53, B_54))=B_54 | ~m1_subset_1(B_54, k1_zfmisc_1(A_53)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 4.54/1.83  tff(c_323, plain, (k3_subset_1('#skF_1', k3_subset_1('#skF_1', '#skF_3'))='#skF_3'), inference(resolution, [status(thm)], [c_26, c_295])).
% 4.54/1.83  tff(c_10, plain, (![A_10, B_11]: (k4_xboole_0(A_10, k4_xboole_0(A_10, B_11))=k3_xboole_0(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.54/1.83  tff(c_18, plain, (![A_18, B_19]: (k6_subset_1(A_18, B_19)=k4_xboole_0(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_47])).
% 4.54/1.83  tff(c_14, plain, (![A_14, B_15]: (m1_subset_1(k6_subset_1(A_14, B_15), k1_zfmisc_1(A_14)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.54/1.83  tff(c_29, plain, (![A_14, B_15]: (m1_subset_1(k4_xboole_0(A_14, B_15), k1_zfmisc_1(A_14)))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_14])).
% 4.54/1.83  tff(c_195, plain, (![A_14, B_15]: (k4_xboole_0(A_14, k4_xboole_0(A_14, B_15))=k3_subset_1(A_14, k4_xboole_0(A_14, B_15)))), inference(resolution, [status(thm)], [c_29, c_183])).
% 4.54/1.83  tff(c_333, plain, (![A_55, B_56]: (k3_subset_1(A_55, k4_xboole_0(A_55, B_56))=k3_xboole_0(A_55, B_56))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_195])).
% 4.54/1.83  tff(c_351, plain, (k3_subset_1('#skF_1', k3_subset_1('#skF_1', '#skF_3'))=k3_xboole_0('#skF_1', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_207, c_333])).
% 4.54/1.83  tff(c_359, plain, (k3_xboole_0('#skF_1', '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_323, c_351])).
% 4.54/1.83  tff(c_6, plain, (![A_5, B_6]: (k5_xboole_0(A_5, k3_xboole_0(A_5, B_6))=k4_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.54/1.83  tff(c_407, plain, (k5_xboole_0('#skF_1', '#skF_3')=k4_xboole_0('#skF_1', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_359, c_6])).
% 4.54/1.83  tff(c_413, plain, (k5_xboole_0('#skF_1', '#skF_3')=k3_subset_1('#skF_1', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_207, c_407])).
% 4.54/1.83  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.54/1.83  tff(c_82, plain, (![A_34, B_35]: (k5_xboole_0(A_34, k3_xboole_0(A_34, B_35))=k4_xboole_0(A_34, B_35))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.54/1.83  tff(c_91, plain, (![A_1, B_2]: (k5_xboole_0(A_1, k3_xboole_0(B_2, A_1))=k4_xboole_0(A_1, B_2))), inference(superposition, [status(thm), theory('equality')], [c_2, c_82])).
% 4.54/1.83  tff(c_28, plain, (m1_subset_1('#skF_2', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_63])).
% 4.54/1.83  tff(c_324, plain, (k3_subset_1('#skF_1', k3_subset_1('#skF_1', '#skF_2'))='#skF_2'), inference(resolution, [status(thm)], [c_28, c_295])).
% 4.54/1.83  tff(c_208, plain, (k4_xboole_0('#skF_1', '#skF_2')=k3_subset_1('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_28, c_183])).
% 4.54/1.83  tff(c_348, plain, (k3_subset_1('#skF_1', k3_subset_1('#skF_1', '#skF_2'))=k3_xboole_0('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_208, c_333])).
% 4.54/1.83  tff(c_358, plain, (k3_xboole_0('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_324, c_348])).
% 4.54/1.83  tff(c_670, plain, (![A_72, B_73, C_74]: (k5_xboole_0(k3_xboole_0(A_72, B_73), k3_xboole_0(C_74, B_73))=k3_xboole_0(k5_xboole_0(A_72, C_74), B_73))), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.54/1.83  tff(c_711, plain, (![C_74]: (k5_xboole_0('#skF_2', k3_xboole_0(C_74, '#skF_2'))=k3_xboole_0(k5_xboole_0('#skF_1', C_74), '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_358, c_670])).
% 4.54/1.83  tff(c_919, plain, (![C_79]: (k3_xboole_0('#skF_2', k5_xboole_0('#skF_1', C_79))=k4_xboole_0('#skF_2', C_79))), inference(demodulation, [status(thm), theory('equality')], [c_91, c_2, c_711])).
% 4.54/1.83  tff(c_956, plain, (k3_xboole_0('#skF_2', k3_subset_1('#skF_1', '#skF_3'))=k4_xboole_0('#skF_2', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_413, c_919])).
% 4.54/1.83  tff(c_566, plain, (![A_64, B_65, C_66]: (k9_subset_1(A_64, B_65, C_66)=k3_xboole_0(B_65, C_66) | ~m1_subset_1(C_66, k1_zfmisc_1(A_64)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 4.54/1.83  tff(c_3280, plain, (![A_116, B_117, B_118]: (k9_subset_1(A_116, B_117, k4_xboole_0(A_116, B_118))=k3_xboole_0(B_117, k4_xboole_0(A_116, B_118)))), inference(resolution, [status(thm)], [c_29, c_566])).
% 4.54/1.83  tff(c_3346, plain, (![B_117]: (k9_subset_1('#skF_1', B_117, k3_subset_1('#skF_1', '#skF_3'))=k3_xboole_0(B_117, k4_xboole_0('#skF_1', '#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_207, c_3280])).
% 4.54/1.83  tff(c_3371, plain, (![B_117]: (k9_subset_1('#skF_1', B_117, k3_subset_1('#skF_1', '#skF_3'))=k3_xboole_0(B_117, k3_subset_1('#skF_1', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_207, c_3346])).
% 4.54/1.83  tff(c_450, plain, (![A_57, B_58, C_59]: (k7_subset_1(A_57, B_58, C_59)=k4_xboole_0(B_58, C_59) | ~m1_subset_1(B_58, k1_zfmisc_1(A_57)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 4.54/1.83  tff(c_477, plain, (![C_59]: (k7_subset_1('#skF_1', '#skF_2', C_59)=k4_xboole_0('#skF_2', C_59))), inference(resolution, [status(thm)], [c_28, c_450])).
% 4.54/1.83  tff(c_24, plain, (k9_subset_1('#skF_1', '#skF_2', k3_subset_1('#skF_1', '#skF_3'))!=k7_subset_1('#skF_1', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_63])).
% 4.54/1.83  tff(c_507, plain, (k9_subset_1('#skF_1', '#skF_2', k3_subset_1('#skF_1', '#skF_3'))!=k4_xboole_0('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_477, c_24])).
% 4.54/1.83  tff(c_3517, plain, (k3_xboole_0('#skF_2', k3_subset_1('#skF_1', '#skF_3'))!=k4_xboole_0('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_3371, c_507])).
% 4.54/1.83  tff(c_3520, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_956, c_3517])).
% 4.54/1.83  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.54/1.83  
% 4.54/1.83  Inference rules
% 4.54/1.83  ----------------------
% 4.54/1.83  #Ref     : 0
% 4.54/1.83  #Sup     : 921
% 4.54/1.83  #Fact    : 0
% 4.54/1.83  #Define  : 0
% 4.54/1.83  #Split   : 0
% 4.54/1.83  #Chain   : 0
% 4.54/1.83  #Close   : 0
% 4.54/1.83  
% 4.54/1.83  Ordering : KBO
% 4.54/1.83  
% 4.54/1.83  Simplification rules
% 4.54/1.83  ----------------------
% 4.54/1.83  #Subsume      : 0
% 4.54/1.83  #Demod        : 912
% 4.54/1.83  #Tautology    : 521
% 4.54/1.83  #SimpNegUnit  : 0
% 4.54/1.83  #BackRed      : 5
% 4.54/1.83  
% 4.54/1.83  #Partial instantiations: 0
% 4.54/1.83  #Strategies tried      : 1
% 4.54/1.83  
% 4.54/1.83  Timing (in seconds)
% 4.54/1.83  ----------------------
% 4.54/1.83  Preprocessing        : 0.29
% 4.54/1.83  Parsing              : 0.16
% 4.54/1.83  CNF conversion       : 0.02
% 4.54/1.83  Main loop            : 0.77
% 4.54/1.84  Inferencing          : 0.23
% 4.54/1.84  Reduction            : 0.34
% 4.54/1.84  Demodulation         : 0.27
% 4.54/1.84  BG Simplification    : 0.03
% 4.54/1.84  Subsumption          : 0.12
% 4.54/1.84  Abstraction          : 0.04
% 4.54/1.84  MUC search           : 0.00
% 4.54/1.84  Cooper               : 0.00
% 4.54/1.84  Total                : 1.09
% 4.54/1.84  Index Insertion      : 0.00
% 4.54/1.84  Index Deletion       : 0.00
% 4.54/1.84  Index Matching       : 0.00
% 4.54/1.84  BG Taut test         : 0.00
%------------------------------------------------------------------------------
