%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:22:41 EST 2020

% Result     : Theorem 2.32s
% Output     : CNFRefutation 2.32s
% Verified   : 
% Statistics : Number of formulae       :   58 ( 141 expanded)
%              Number of leaves         :   28 (  60 expanded)
%              Depth                    :   11
%              Number of atoms          :   71 ( 225 expanded)
%              Number of equality atoms :   30 (  91 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m1_subset_1 > k7_subset_1 > k4_subset_1 > k7_setfam_1 > k6_setfam_1 > k5_setfam_1 > k4_xboole_0 > k3_subset_1 > #nlpp > k3_tarski > k2_subset_1 > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k7_setfam_1,type,(
    k7_setfam_1: ( $i * $i ) > $i )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff(k4_subset_1,type,(
    k4_subset_1: ( $i * $i * $i ) > $i )).

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

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff(k6_setfam_1,type,(
    k6_setfam_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_82,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
       => ( B != k1_xboole_0
         => k5_setfam_1(A,k7_setfam_1(A,B)) = k3_subset_1(A,k6_setfam_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_tops_2)).

tff(f_67,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => k6_setfam_1(A,B) = k1_setfam_1(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_setfam_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => m1_subset_1(k6_setfam_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_setfam_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k3_subset_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).

tff(f_29,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k4_subset_1(A,B,k3_subset_1(A,B)) = k2_subset_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_subset_1)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => m1_subset_1(k4_subset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_subset_1)).

tff(f_47,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

tff(f_74,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => ( B != k1_xboole_0
       => k5_setfam_1(A,k7_setfam_1(A,B)) = k7_subset_1(A,k2_subset_1(A),k6_setfam_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_setfam_1)).

tff(c_28,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_30,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k1_zfmisc_1('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_51,plain,(
    ! [A_27,B_28] :
      ( k6_setfam_1(A_27,B_28) = k1_setfam_1(B_28)
      | ~ m1_subset_1(B_28,k1_zfmisc_1(k1_zfmisc_1(A_27))) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_55,plain,(
    k6_setfam_1('#skF_1','#skF_2') = k1_setfam_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_30,c_51])).

tff(c_26,plain,(
    k5_setfam_1('#skF_1',k7_setfam_1('#skF_1','#skF_2')) != k3_subset_1('#skF_1',k6_setfam_1('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_80,plain,(
    k5_setfam_1('#skF_1',k7_setfam_1('#skF_1','#skF_2')) != k3_subset_1('#skF_1',k1_setfam_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_55,c_26])).

tff(c_94,plain,(
    ! [A_35,B_36] :
      ( m1_subset_1(k6_setfam_1(A_35,B_36),k1_zfmisc_1(A_35))
      | ~ m1_subset_1(B_36,k1_zfmisc_1(k1_zfmisc_1(A_35))) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_108,plain,
    ( m1_subset_1(k1_setfam_1('#skF_2'),k1_zfmisc_1('#skF_1'))
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k1_zfmisc_1('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_55,c_94])).

tff(c_113,plain,(
    m1_subset_1(k1_setfam_1('#skF_2'),k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_108])).

tff(c_6,plain,(
    ! [A_3,B_4] :
      ( k4_xboole_0(A_3,B_4) = k3_subset_1(A_3,B_4)
      | ~ m1_subset_1(B_4,k1_zfmisc_1(A_3)) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_117,plain,(
    k4_xboole_0('#skF_1',k1_setfam_1('#skF_2')) = k3_subset_1('#skF_1',k1_setfam_1('#skF_2')) ),
    inference(resolution,[status(thm)],[c_113,c_6])).

tff(c_8,plain,(
    ! [A_5,B_6] :
      ( m1_subset_1(k3_subset_1(A_5,B_6),k1_zfmisc_1(A_5))
      | ~ m1_subset_1(B_6,k1_zfmisc_1(A_5)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_4,plain,(
    ! [A_2] : k2_subset_1(A_2) = A_2 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_14,plain,(
    ! [A_13,B_14] :
      ( k4_subset_1(A_13,B_14,k3_subset_1(A_13,B_14)) = k2_subset_1(A_13)
      | ~ m1_subset_1(B_14,k1_zfmisc_1(A_13)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_122,plain,(
    ! [A_37,B_38] :
      ( k4_subset_1(A_37,B_38,k3_subset_1(A_37,B_38)) = A_37
      | ~ m1_subset_1(B_38,k1_zfmisc_1(A_37)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_14])).

tff(c_131,plain,(
    k4_subset_1('#skF_1',k1_setfam_1('#skF_2'),k3_subset_1('#skF_1',k1_setfam_1('#skF_2'))) = '#skF_1' ),
    inference(resolution,[status(thm)],[c_113,c_122])).

tff(c_223,plain,(
    ! [A_47,B_48,C_49] :
      ( m1_subset_1(k4_subset_1(A_47,B_48,C_49),k1_zfmisc_1(A_47))
      | ~ m1_subset_1(C_49,k1_zfmisc_1(A_47))
      | ~ m1_subset_1(B_48,k1_zfmisc_1(A_47)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_244,plain,
    ( m1_subset_1('#skF_1',k1_zfmisc_1('#skF_1'))
    | ~ m1_subset_1(k3_subset_1('#skF_1',k1_setfam_1('#skF_2')),k1_zfmisc_1('#skF_1'))
    | ~ m1_subset_1(k1_setfam_1('#skF_2'),k1_zfmisc_1('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_131,c_223])).

tff(c_253,plain,
    ( m1_subset_1('#skF_1',k1_zfmisc_1('#skF_1'))
    | ~ m1_subset_1(k3_subset_1('#skF_1',k1_setfam_1('#skF_2')),k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_113,c_244])).

tff(c_263,plain,(
    ~ m1_subset_1(k3_subset_1('#skF_1',k1_setfam_1('#skF_2')),k1_zfmisc_1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_253])).

tff(c_266,plain,(
    ~ m1_subset_1(k1_setfam_1('#skF_2'),k1_zfmisc_1('#skF_1')) ),
    inference(resolution,[status(thm)],[c_8,c_263])).

tff(c_270,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_113,c_266])).

tff(c_271,plain,(
    m1_subset_1('#skF_1',k1_zfmisc_1('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_253])).

tff(c_12,plain,(
    ! [A_10,B_11,C_12] :
      ( k7_subset_1(A_10,B_11,C_12) = k4_xboole_0(B_11,C_12)
      | ~ m1_subset_1(B_11,k1_zfmisc_1(A_10)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_281,plain,(
    ! [C_12] : k7_subset_1('#skF_1','#skF_1',C_12) = k4_xboole_0('#skF_1',C_12) ),
    inference(resolution,[status(thm)],[c_271,c_12])).

tff(c_24,plain,(
    ! [A_23,B_24] :
      ( k7_subset_1(A_23,k2_subset_1(A_23),k6_setfam_1(A_23,B_24)) = k5_setfam_1(A_23,k7_setfam_1(A_23,B_24))
      | k1_xboole_0 = B_24
      | ~ m1_subset_1(B_24,k1_zfmisc_1(k1_zfmisc_1(A_23))) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_316,plain,(
    ! [A_51,B_52] :
      ( k7_subset_1(A_51,A_51,k6_setfam_1(A_51,B_52)) = k5_setfam_1(A_51,k7_setfam_1(A_51,B_52))
      | k1_xboole_0 = B_52
      | ~ m1_subset_1(B_52,k1_zfmisc_1(k1_zfmisc_1(A_51))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_24])).

tff(c_330,plain,
    ( k7_subset_1('#skF_1','#skF_1',k6_setfam_1('#skF_1','#skF_2')) = k5_setfam_1('#skF_1',k7_setfam_1('#skF_1','#skF_2'))
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_30,c_316])).

tff(c_336,plain,
    ( k5_setfam_1('#skF_1',k7_setfam_1('#skF_1','#skF_2')) = k3_subset_1('#skF_1',k1_setfam_1('#skF_2'))
    | k1_xboole_0 = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_117,c_281,c_55,c_330])).

tff(c_338,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_80,c_336])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n025.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 18:21:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.32/1.30  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.32/1.31  
% 2.32/1.31  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.32/1.31  %$ m1_subset_1 > k7_subset_1 > k4_subset_1 > k7_setfam_1 > k6_setfam_1 > k5_setfam_1 > k4_xboole_0 > k3_subset_1 > #nlpp > k3_tarski > k2_subset_1 > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_1
% 2.32/1.31  
% 2.32/1.31  %Foreground sorts:
% 2.32/1.31  
% 2.32/1.31  
% 2.32/1.31  %Background operators:
% 2.32/1.31  
% 2.32/1.31  
% 2.32/1.31  %Foreground operators:
% 2.32/1.31  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.32/1.31  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.32/1.31  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.32/1.31  tff(k7_setfam_1, type, k7_setfam_1: ($i * $i) > $i).
% 2.32/1.31  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 2.32/1.31  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 2.32/1.31  tff('#skF_2', type, '#skF_2': $i).
% 2.32/1.31  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 2.32/1.31  tff('#skF_1', type, '#skF_1': $i).
% 2.32/1.31  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.32/1.31  tff(k5_setfam_1, type, k5_setfam_1: ($i * $i) > $i).
% 2.32/1.31  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.32/1.31  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.32/1.31  tff(k6_setfam_1, type, k6_setfam_1: ($i * $i) > $i).
% 2.32/1.31  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.32/1.31  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 2.32/1.31  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.32/1.31  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.32/1.31  
% 2.32/1.32  tff(f_82, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (~(B = k1_xboole_0) => (k5_setfam_1(A, k7_setfam_1(A, B)) = k3_subset_1(A, k6_setfam_1(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_tops_2)).
% 2.32/1.32  tff(f_67, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (k6_setfam_1(A, B) = k1_setfam_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_setfam_1)).
% 2.32/1.32  tff(f_59, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => m1_subset_1(k6_setfam_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_setfam_1)).
% 2.32/1.32  tff(f_33, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_subset_1)).
% 2.32/1.32  tff(f_37, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k3_subset_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 2.32/1.32  tff(f_29, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 2.32/1.32  tff(f_51, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k4_subset_1(A, B, k3_subset_1(A, B)) = k2_subset_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t25_subset_1)).
% 2.32/1.32  tff(f_43, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => m1_subset_1(k4_subset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k4_subset_1)).
% 2.32/1.32  tff(f_47, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 2.32/1.32  tff(f_74, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (~(B = k1_xboole_0) => (k5_setfam_1(A, k7_setfam_1(A, B)) = k7_subset_1(A, k2_subset_1(A), k6_setfam_1(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_setfam_1)).
% 2.32/1.32  tff(c_28, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.32/1.32  tff(c_30, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k1_zfmisc_1('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.32/1.32  tff(c_51, plain, (![A_27, B_28]: (k6_setfam_1(A_27, B_28)=k1_setfam_1(B_28) | ~m1_subset_1(B_28, k1_zfmisc_1(k1_zfmisc_1(A_27))))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.32/1.32  tff(c_55, plain, (k6_setfam_1('#skF_1', '#skF_2')=k1_setfam_1('#skF_2')), inference(resolution, [status(thm)], [c_30, c_51])).
% 2.32/1.32  tff(c_26, plain, (k5_setfam_1('#skF_1', k7_setfam_1('#skF_1', '#skF_2'))!=k3_subset_1('#skF_1', k6_setfam_1('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.32/1.32  tff(c_80, plain, (k5_setfam_1('#skF_1', k7_setfam_1('#skF_1', '#skF_2'))!=k3_subset_1('#skF_1', k1_setfam_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_55, c_26])).
% 2.32/1.32  tff(c_94, plain, (![A_35, B_36]: (m1_subset_1(k6_setfam_1(A_35, B_36), k1_zfmisc_1(A_35)) | ~m1_subset_1(B_36, k1_zfmisc_1(k1_zfmisc_1(A_35))))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.32/1.32  tff(c_108, plain, (m1_subset_1(k1_setfam_1('#skF_2'), k1_zfmisc_1('#skF_1')) | ~m1_subset_1('#skF_2', k1_zfmisc_1(k1_zfmisc_1('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_55, c_94])).
% 2.32/1.32  tff(c_113, plain, (m1_subset_1(k1_setfam_1('#skF_2'), k1_zfmisc_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_108])).
% 2.32/1.32  tff(c_6, plain, (![A_3, B_4]: (k4_xboole_0(A_3, B_4)=k3_subset_1(A_3, B_4) | ~m1_subset_1(B_4, k1_zfmisc_1(A_3)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.32/1.32  tff(c_117, plain, (k4_xboole_0('#skF_1', k1_setfam_1('#skF_2'))=k3_subset_1('#skF_1', k1_setfam_1('#skF_2'))), inference(resolution, [status(thm)], [c_113, c_6])).
% 2.32/1.32  tff(c_8, plain, (![A_5, B_6]: (m1_subset_1(k3_subset_1(A_5, B_6), k1_zfmisc_1(A_5)) | ~m1_subset_1(B_6, k1_zfmisc_1(A_5)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.32/1.32  tff(c_4, plain, (![A_2]: (k2_subset_1(A_2)=A_2)), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.32/1.32  tff(c_14, plain, (![A_13, B_14]: (k4_subset_1(A_13, B_14, k3_subset_1(A_13, B_14))=k2_subset_1(A_13) | ~m1_subset_1(B_14, k1_zfmisc_1(A_13)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.32/1.32  tff(c_122, plain, (![A_37, B_38]: (k4_subset_1(A_37, B_38, k3_subset_1(A_37, B_38))=A_37 | ~m1_subset_1(B_38, k1_zfmisc_1(A_37)))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_14])).
% 2.32/1.32  tff(c_131, plain, (k4_subset_1('#skF_1', k1_setfam_1('#skF_2'), k3_subset_1('#skF_1', k1_setfam_1('#skF_2')))='#skF_1'), inference(resolution, [status(thm)], [c_113, c_122])).
% 2.32/1.32  tff(c_223, plain, (![A_47, B_48, C_49]: (m1_subset_1(k4_subset_1(A_47, B_48, C_49), k1_zfmisc_1(A_47)) | ~m1_subset_1(C_49, k1_zfmisc_1(A_47)) | ~m1_subset_1(B_48, k1_zfmisc_1(A_47)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.32/1.32  tff(c_244, plain, (m1_subset_1('#skF_1', k1_zfmisc_1('#skF_1')) | ~m1_subset_1(k3_subset_1('#skF_1', k1_setfam_1('#skF_2')), k1_zfmisc_1('#skF_1')) | ~m1_subset_1(k1_setfam_1('#skF_2'), k1_zfmisc_1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_131, c_223])).
% 2.32/1.32  tff(c_253, plain, (m1_subset_1('#skF_1', k1_zfmisc_1('#skF_1')) | ~m1_subset_1(k3_subset_1('#skF_1', k1_setfam_1('#skF_2')), k1_zfmisc_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_113, c_244])).
% 2.32/1.32  tff(c_263, plain, (~m1_subset_1(k3_subset_1('#skF_1', k1_setfam_1('#skF_2')), k1_zfmisc_1('#skF_1'))), inference(splitLeft, [status(thm)], [c_253])).
% 2.32/1.32  tff(c_266, plain, (~m1_subset_1(k1_setfam_1('#skF_2'), k1_zfmisc_1('#skF_1'))), inference(resolution, [status(thm)], [c_8, c_263])).
% 2.32/1.32  tff(c_270, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_113, c_266])).
% 2.32/1.32  tff(c_271, plain, (m1_subset_1('#skF_1', k1_zfmisc_1('#skF_1'))), inference(splitRight, [status(thm)], [c_253])).
% 2.32/1.32  tff(c_12, plain, (![A_10, B_11, C_12]: (k7_subset_1(A_10, B_11, C_12)=k4_xboole_0(B_11, C_12) | ~m1_subset_1(B_11, k1_zfmisc_1(A_10)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.32/1.32  tff(c_281, plain, (![C_12]: (k7_subset_1('#skF_1', '#skF_1', C_12)=k4_xboole_0('#skF_1', C_12))), inference(resolution, [status(thm)], [c_271, c_12])).
% 2.32/1.32  tff(c_24, plain, (![A_23, B_24]: (k7_subset_1(A_23, k2_subset_1(A_23), k6_setfam_1(A_23, B_24))=k5_setfam_1(A_23, k7_setfam_1(A_23, B_24)) | k1_xboole_0=B_24 | ~m1_subset_1(B_24, k1_zfmisc_1(k1_zfmisc_1(A_23))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.32/1.32  tff(c_316, plain, (![A_51, B_52]: (k7_subset_1(A_51, A_51, k6_setfam_1(A_51, B_52))=k5_setfam_1(A_51, k7_setfam_1(A_51, B_52)) | k1_xboole_0=B_52 | ~m1_subset_1(B_52, k1_zfmisc_1(k1_zfmisc_1(A_51))))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_24])).
% 2.32/1.32  tff(c_330, plain, (k7_subset_1('#skF_1', '#skF_1', k6_setfam_1('#skF_1', '#skF_2'))=k5_setfam_1('#skF_1', k7_setfam_1('#skF_1', '#skF_2')) | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_30, c_316])).
% 2.32/1.32  tff(c_336, plain, (k5_setfam_1('#skF_1', k7_setfam_1('#skF_1', '#skF_2'))=k3_subset_1('#skF_1', k1_setfam_1('#skF_2')) | k1_xboole_0='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_117, c_281, c_55, c_330])).
% 2.32/1.32  tff(c_338, plain, $false, inference(negUnitSimplification, [status(thm)], [c_28, c_80, c_336])).
% 2.32/1.32  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.32/1.32  
% 2.32/1.32  Inference rules
% 2.32/1.32  ----------------------
% 2.32/1.32  #Ref     : 0
% 2.32/1.32  #Sup     : 81
% 2.32/1.32  #Fact    : 0
% 2.32/1.32  #Define  : 0
% 2.32/1.32  #Split   : 2
% 2.32/1.32  #Chain   : 0
% 2.32/1.32  #Close   : 0
% 2.32/1.32  
% 2.32/1.32  Ordering : KBO
% 2.32/1.32  
% 2.32/1.32  Simplification rules
% 2.32/1.32  ----------------------
% 2.32/1.32  #Subsume      : 0
% 2.32/1.32  #Demod        : 14
% 2.32/1.32  #Tautology    : 33
% 2.32/1.32  #SimpNegUnit  : 1
% 2.32/1.32  #BackRed      : 0
% 2.32/1.32  
% 2.32/1.32  #Partial instantiations: 0
% 2.32/1.32  #Strategies tried      : 1
% 2.32/1.32  
% 2.32/1.32  Timing (in seconds)
% 2.32/1.32  ----------------------
% 2.32/1.33  Preprocessing        : 0.29
% 2.32/1.33  Parsing              : 0.16
% 2.32/1.33  CNF conversion       : 0.02
% 2.32/1.33  Main loop            : 0.21
% 2.32/1.33  Inferencing          : 0.07
% 2.32/1.33  Reduction            : 0.07
% 2.32/1.33  Demodulation         : 0.05
% 2.32/1.33  BG Simplification    : 0.02
% 2.32/1.33  Subsumption          : 0.04
% 2.32/1.33  Abstraction          : 0.01
% 2.32/1.33  MUC search           : 0.00
% 2.32/1.33  Cooper               : 0.00
% 2.32/1.33  Total                : 0.54
% 2.32/1.33  Index Insertion      : 0.00
% 2.32/1.33  Index Deletion       : 0.00
% 2.32/1.33  Index Matching       : 0.00
% 2.32/1.33  BG Taut test         : 0.00
%------------------------------------------------------------------------------
