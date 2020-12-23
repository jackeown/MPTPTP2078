%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:22:40 EST 2020

% Result     : Theorem 2.58s
% Output     : CNFRefutation 2.64s
% Verified   : 
% Statistics : Number of formulae       :   65 (  96 expanded)
%              Number of leaves         :   34 (  48 expanded)
%              Depth                    :   13
%              Number of atoms          :   63 ( 103 expanded)
%              Number of equality atoms :   38 (  67 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > m1_subset_1 > k7_subset_1 > k1_enumset1 > k7_setfam_1 > k6_setfam_1 > k5_xboole_0 > k5_setfam_1 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_tarski > #nlpp > k2_subset_1 > k1_zfmisc_1 > k1_subset_1 > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k7_setfam_1,type,(
    k7_setfam_1: ( $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k7_subset_1,type,(
    k7_subset_1: ( $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k5_setfam_1,type,(
    k5_setfam_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k6_setfam_1,type,(
    k6_setfam_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_subset_1,type,(
    k1_subset_1: $i > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_78,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
       => ( B != k1_xboole_0
         => k6_setfam_1(A,k7_setfam_1(A,B)) = k3_subset_1(A,k5_setfam_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_tops_2)).

tff(f_51,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_31,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

tff(f_29,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_27,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_35,axiom,(
    ! [A] : k1_subset_1(A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_subset_1)).

tff(f_49,axiom,(
    ! [A] : k2_subset_1(A) = k3_subset_1(A,k1_subset_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_subset_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k3_subset_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).

tff(f_47,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

tff(f_64,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => ( B != k1_xboole_0
       => k7_subset_1(A,k2_subset_1(A),k5_setfam_1(A,B)) = k6_setfam_1(A,k7_setfam_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_setfam_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => m1_subset_1(k5_setfam_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_setfam_1)).

tff(c_32,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_34,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k1_zfmisc_1('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_20,plain,(
    ! [A_16] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_16)) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_6,plain,(
    ! [A_4] : k5_xboole_0(A_4,k1_xboole_0) = A_4 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_4,plain,(
    ! [A_3] : k3_xboole_0(A_3,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_87,plain,(
    ! [A_35,B_36] : k5_xboole_0(A_35,k3_xboole_0(A_35,B_36)) = k4_xboole_0(A_35,B_36) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_96,plain,(
    ! [A_3] : k5_xboole_0(A_3,k1_xboole_0) = k4_xboole_0(A_3,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_87])).

tff(c_99,plain,(
    ! [A_3] : k4_xboole_0(A_3,k1_xboole_0) = A_3 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_96])).

tff(c_10,plain,(
    ! [A_7] : k1_subset_1(A_7) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_18,plain,(
    ! [A_15] : k3_subset_1(A_15,k1_subset_1(A_15)) = k2_subset_1(A_15) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_35,plain,(
    ! [A_15] : k3_subset_1(A_15,k1_xboole_0) = k2_subset_1(A_15) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_18])).

tff(c_121,plain,(
    ! [A_44,B_45] :
      ( k4_xboole_0(A_44,B_45) = k3_subset_1(A_44,B_45)
      | ~ m1_subset_1(B_45,k1_zfmisc_1(A_44)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_130,plain,(
    ! [A_16] : k4_xboole_0(A_16,k1_xboole_0) = k3_subset_1(A_16,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_20,c_121])).

tff(c_134,plain,(
    ! [A_16] : k2_subset_1(A_16) = A_16 ),
    inference(demodulation,[status(thm),theory(equality)],[c_99,c_35,c_130])).

tff(c_135,plain,(
    ! [A_15] : k3_subset_1(A_15,k1_xboole_0) = A_15 ),
    inference(demodulation,[status(thm),theory(equality)],[c_134,c_35])).

tff(c_160,plain,(
    ! [A_51,B_52] :
      ( m1_subset_1(k3_subset_1(A_51,B_52),k1_zfmisc_1(A_51))
      | ~ m1_subset_1(B_52,k1_zfmisc_1(A_51)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_168,plain,(
    ! [A_15] :
      ( m1_subset_1(A_15,k1_zfmisc_1(A_15))
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_15)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_135,c_160])).

tff(c_172,plain,(
    ! [A_15] : m1_subset_1(A_15,k1_zfmisc_1(A_15)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_168])).

tff(c_209,plain,(
    ! [A_59,B_60,C_61] :
      ( k7_subset_1(A_59,B_60,C_61) = k4_xboole_0(B_60,C_61)
      | ~ m1_subset_1(B_60,k1_zfmisc_1(A_59)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_223,plain,(
    ! [A_15,C_61] : k7_subset_1(A_15,A_15,C_61) = k4_xboole_0(A_15,C_61) ),
    inference(resolution,[status(thm)],[c_172,c_209])).

tff(c_26,plain,(
    ! [A_21,B_22] :
      ( k7_subset_1(A_21,k2_subset_1(A_21),k5_setfam_1(A_21,B_22)) = k6_setfam_1(A_21,k7_setfam_1(A_21,B_22))
      | k1_xboole_0 = B_22
      | ~ m1_subset_1(B_22,k1_zfmisc_1(k1_zfmisc_1(A_21))) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_308,plain,(
    ! [A_78,B_79] :
      ( k6_setfam_1(A_78,k7_setfam_1(A_78,B_79)) = k4_xboole_0(A_78,k5_setfam_1(A_78,B_79))
      | k1_xboole_0 = B_79
      | ~ m1_subset_1(B_79,k1_zfmisc_1(k1_zfmisc_1(A_78))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_223,c_134,c_26])).

tff(c_319,plain,
    ( k6_setfam_1('#skF_1',k7_setfam_1('#skF_1','#skF_2')) = k4_xboole_0('#skF_1',k5_setfam_1('#skF_1','#skF_2'))
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_34,c_308])).

tff(c_328,plain,(
    k6_setfam_1('#skF_1',k7_setfam_1('#skF_1','#skF_2')) = k4_xboole_0('#skF_1',k5_setfam_1('#skF_1','#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_319])).

tff(c_30,plain,(
    k6_setfam_1('#skF_1',k7_setfam_1('#skF_1','#skF_2')) != k3_subset_1('#skF_1',k5_setfam_1('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_331,plain,(
    k4_xboole_0('#skF_1',k5_setfam_1('#skF_1','#skF_2')) != k3_subset_1('#skF_1',k5_setfam_1('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_328,c_30])).

tff(c_201,plain,(
    ! [A_57,B_58] :
      ( m1_subset_1(k5_setfam_1(A_57,B_58),k1_zfmisc_1(A_57))
      | ~ m1_subset_1(B_58,k1_zfmisc_1(k1_zfmisc_1(A_57))) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_12,plain,(
    ! [A_8,B_9] :
      ( k4_xboole_0(A_8,B_9) = k3_subset_1(A_8,B_9)
      | ~ m1_subset_1(B_9,k1_zfmisc_1(A_8)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_431,plain,(
    ! [A_89,B_90] :
      ( k4_xboole_0(A_89,k5_setfam_1(A_89,B_90)) = k3_subset_1(A_89,k5_setfam_1(A_89,B_90))
      | ~ m1_subset_1(B_90,k1_zfmisc_1(k1_zfmisc_1(A_89))) ) ),
    inference(resolution,[status(thm)],[c_201,c_12])).

tff(c_442,plain,(
    k4_xboole_0('#skF_1',k5_setfam_1('#skF_1','#skF_2')) = k3_subset_1('#skF_1',k5_setfam_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_34,c_431])).

tff(c_452,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_331,c_442])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n007.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 15:16:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.58/1.61  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.58/1.61  
% 2.58/1.61  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.58/1.61  %$ r2_hidden > m1_subset_1 > k7_subset_1 > k1_enumset1 > k7_setfam_1 > k6_setfam_1 > k5_xboole_0 > k5_setfam_1 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_tarski > #nlpp > k2_subset_1 > k1_zfmisc_1 > k1_subset_1 > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_1
% 2.58/1.61  
% 2.58/1.61  %Foreground sorts:
% 2.58/1.61  
% 2.58/1.61  
% 2.58/1.61  %Background operators:
% 2.58/1.61  
% 2.58/1.61  
% 2.58/1.61  %Foreground operators:
% 2.58/1.61  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.58/1.61  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.58/1.61  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.58/1.61  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.58/1.61  tff(k7_setfam_1, type, k7_setfam_1: ($i * $i) > $i).
% 2.58/1.61  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.58/1.61  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.58/1.61  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 2.58/1.61  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.58/1.61  tff('#skF_2', type, '#skF_2': $i).
% 2.58/1.61  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 2.58/1.61  tff('#skF_1', type, '#skF_1': $i).
% 2.58/1.61  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.58/1.61  tff(k5_setfam_1, type, k5_setfam_1: ($i * $i) > $i).
% 2.58/1.61  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.58/1.61  tff(k6_setfam_1, type, k6_setfam_1: ($i * $i) > $i).
% 2.58/1.61  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.58/1.61  tff(k1_subset_1, type, k1_subset_1: $i > $i).
% 2.58/1.61  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.58/1.61  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 2.58/1.61  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.58/1.61  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.58/1.61  
% 2.64/1.63  tff(f_78, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (~(B = k1_xboole_0) => (k6_setfam_1(A, k7_setfam_1(A, B)) = k3_subset_1(A, k5_setfam_1(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_tops_2)).
% 2.64/1.63  tff(f_51, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 2.64/1.63  tff(f_31, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 2.64/1.63  tff(f_29, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 2.64/1.63  tff(f_27, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 2.64/1.63  tff(f_35, axiom, (![A]: (k1_subset_1(A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_subset_1)).
% 2.64/1.63  tff(f_49, axiom, (![A]: (k2_subset_1(A) = k3_subset_1(A, k1_subset_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_subset_1)).
% 2.64/1.63  tff(f_39, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 2.64/1.63  tff(f_43, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k3_subset_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 2.64/1.63  tff(f_47, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 2.64/1.63  tff(f_64, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (~(B = k1_xboole_0) => (k7_subset_1(A, k2_subset_1(A), k5_setfam_1(A, B)) = k6_setfam_1(A, k7_setfam_1(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_setfam_1)).
% 2.64/1.63  tff(f_55, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => m1_subset_1(k5_setfam_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k5_setfam_1)).
% 2.64/1.63  tff(c_32, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.64/1.63  tff(c_34, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k1_zfmisc_1('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.64/1.63  tff(c_20, plain, (![A_16]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_16)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.64/1.63  tff(c_6, plain, (![A_4]: (k5_xboole_0(A_4, k1_xboole_0)=A_4)), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.64/1.63  tff(c_4, plain, (![A_3]: (k3_xboole_0(A_3, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.64/1.63  tff(c_87, plain, (![A_35, B_36]: (k5_xboole_0(A_35, k3_xboole_0(A_35, B_36))=k4_xboole_0(A_35, B_36))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.64/1.63  tff(c_96, plain, (![A_3]: (k5_xboole_0(A_3, k1_xboole_0)=k4_xboole_0(A_3, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_4, c_87])).
% 2.64/1.63  tff(c_99, plain, (![A_3]: (k4_xboole_0(A_3, k1_xboole_0)=A_3)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_96])).
% 2.64/1.63  tff(c_10, plain, (![A_7]: (k1_subset_1(A_7)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.64/1.63  tff(c_18, plain, (![A_15]: (k3_subset_1(A_15, k1_subset_1(A_15))=k2_subset_1(A_15))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.64/1.63  tff(c_35, plain, (![A_15]: (k3_subset_1(A_15, k1_xboole_0)=k2_subset_1(A_15))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_18])).
% 2.64/1.63  tff(c_121, plain, (![A_44, B_45]: (k4_xboole_0(A_44, B_45)=k3_subset_1(A_44, B_45) | ~m1_subset_1(B_45, k1_zfmisc_1(A_44)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.64/1.63  tff(c_130, plain, (![A_16]: (k4_xboole_0(A_16, k1_xboole_0)=k3_subset_1(A_16, k1_xboole_0))), inference(resolution, [status(thm)], [c_20, c_121])).
% 2.64/1.63  tff(c_134, plain, (![A_16]: (k2_subset_1(A_16)=A_16)), inference(demodulation, [status(thm), theory('equality')], [c_99, c_35, c_130])).
% 2.64/1.63  tff(c_135, plain, (![A_15]: (k3_subset_1(A_15, k1_xboole_0)=A_15)), inference(demodulation, [status(thm), theory('equality')], [c_134, c_35])).
% 2.64/1.63  tff(c_160, plain, (![A_51, B_52]: (m1_subset_1(k3_subset_1(A_51, B_52), k1_zfmisc_1(A_51)) | ~m1_subset_1(B_52, k1_zfmisc_1(A_51)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.64/1.63  tff(c_168, plain, (![A_15]: (m1_subset_1(A_15, k1_zfmisc_1(A_15)) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_15)))), inference(superposition, [status(thm), theory('equality')], [c_135, c_160])).
% 2.64/1.63  tff(c_172, plain, (![A_15]: (m1_subset_1(A_15, k1_zfmisc_1(A_15)))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_168])).
% 2.64/1.63  tff(c_209, plain, (![A_59, B_60, C_61]: (k7_subset_1(A_59, B_60, C_61)=k4_xboole_0(B_60, C_61) | ~m1_subset_1(B_60, k1_zfmisc_1(A_59)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.64/1.63  tff(c_223, plain, (![A_15, C_61]: (k7_subset_1(A_15, A_15, C_61)=k4_xboole_0(A_15, C_61))), inference(resolution, [status(thm)], [c_172, c_209])).
% 2.64/1.63  tff(c_26, plain, (![A_21, B_22]: (k7_subset_1(A_21, k2_subset_1(A_21), k5_setfam_1(A_21, B_22))=k6_setfam_1(A_21, k7_setfam_1(A_21, B_22)) | k1_xboole_0=B_22 | ~m1_subset_1(B_22, k1_zfmisc_1(k1_zfmisc_1(A_21))))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.64/1.63  tff(c_308, plain, (![A_78, B_79]: (k6_setfam_1(A_78, k7_setfam_1(A_78, B_79))=k4_xboole_0(A_78, k5_setfam_1(A_78, B_79)) | k1_xboole_0=B_79 | ~m1_subset_1(B_79, k1_zfmisc_1(k1_zfmisc_1(A_78))))), inference(demodulation, [status(thm), theory('equality')], [c_223, c_134, c_26])).
% 2.64/1.63  tff(c_319, plain, (k6_setfam_1('#skF_1', k7_setfam_1('#skF_1', '#skF_2'))=k4_xboole_0('#skF_1', k5_setfam_1('#skF_1', '#skF_2')) | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_34, c_308])).
% 2.64/1.63  tff(c_328, plain, (k6_setfam_1('#skF_1', k7_setfam_1('#skF_1', '#skF_2'))=k4_xboole_0('#skF_1', k5_setfam_1('#skF_1', '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_32, c_319])).
% 2.64/1.63  tff(c_30, plain, (k6_setfam_1('#skF_1', k7_setfam_1('#skF_1', '#skF_2'))!=k3_subset_1('#skF_1', k5_setfam_1('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.64/1.63  tff(c_331, plain, (k4_xboole_0('#skF_1', k5_setfam_1('#skF_1', '#skF_2'))!=k3_subset_1('#skF_1', k5_setfam_1('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_328, c_30])).
% 2.64/1.63  tff(c_201, plain, (![A_57, B_58]: (m1_subset_1(k5_setfam_1(A_57, B_58), k1_zfmisc_1(A_57)) | ~m1_subset_1(B_58, k1_zfmisc_1(k1_zfmisc_1(A_57))))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.64/1.63  tff(c_12, plain, (![A_8, B_9]: (k4_xboole_0(A_8, B_9)=k3_subset_1(A_8, B_9) | ~m1_subset_1(B_9, k1_zfmisc_1(A_8)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.64/1.63  tff(c_431, plain, (![A_89, B_90]: (k4_xboole_0(A_89, k5_setfam_1(A_89, B_90))=k3_subset_1(A_89, k5_setfam_1(A_89, B_90)) | ~m1_subset_1(B_90, k1_zfmisc_1(k1_zfmisc_1(A_89))))), inference(resolution, [status(thm)], [c_201, c_12])).
% 2.64/1.63  tff(c_442, plain, (k4_xboole_0('#skF_1', k5_setfam_1('#skF_1', '#skF_2'))=k3_subset_1('#skF_1', k5_setfam_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_34, c_431])).
% 2.64/1.63  tff(c_452, plain, $false, inference(negUnitSimplification, [status(thm)], [c_331, c_442])).
% 2.64/1.63  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.64/1.63  
% 2.64/1.63  Inference rules
% 2.64/1.63  ----------------------
% 2.64/1.63  #Ref     : 0
% 2.64/1.63  #Sup     : 99
% 2.64/1.63  #Fact    : 0
% 2.64/1.63  #Define  : 0
% 2.64/1.63  #Split   : 0
% 2.64/1.63  #Chain   : 0
% 2.64/1.63  #Close   : 0
% 2.64/1.63  
% 2.64/1.63  Ordering : KBO
% 2.64/1.63  
% 2.64/1.63  Simplification rules
% 2.64/1.63  ----------------------
% 2.64/1.63  #Subsume      : 1
% 2.64/1.63  #Demod        : 27
% 2.64/1.63  #Tautology    : 59
% 2.64/1.63  #SimpNegUnit  : 2
% 2.64/1.63  #BackRed      : 2
% 2.64/1.63  
% 2.64/1.63  #Partial instantiations: 0
% 2.64/1.63  #Strategies tried      : 1
% 2.64/1.63  
% 2.64/1.63  Timing (in seconds)
% 2.64/1.63  ----------------------
% 2.64/1.63  Preprocessing        : 0.43
% 2.64/1.63  Parsing              : 0.24
% 2.64/1.63  CNF conversion       : 0.02
% 2.64/1.63  Main loop            : 0.27
% 2.64/1.63  Inferencing          : 0.10
% 2.64/1.63  Reduction            : 0.08
% 2.64/1.63  Demodulation         : 0.06
% 2.64/1.63  BG Simplification    : 0.02
% 2.64/1.63  Subsumption          : 0.04
% 2.64/1.63  Abstraction          : 0.02
% 2.64/1.63  MUC search           : 0.00
% 2.64/1.63  Cooper               : 0.00
% 2.64/1.63  Total                : 0.73
% 2.64/1.63  Index Insertion      : 0.00
% 2.64/1.63  Index Deletion       : 0.00
% 2.64/1.63  Index Matching       : 0.00
% 2.64/1.63  BG Taut test         : 0.00
%------------------------------------------------------------------------------
