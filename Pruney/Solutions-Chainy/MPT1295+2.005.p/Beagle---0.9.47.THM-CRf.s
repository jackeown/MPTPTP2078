%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:22:40 EST 2020

% Result     : Theorem 2.27s
% Output     : CNFRefutation 2.35s
% Verified   : 
% Statistics : Number of formulae       :   60 ( 143 expanded)
%              Number of leaves         :   27 (  59 expanded)
%              Depth                    :   12
%              Number of atoms          :   74 ( 228 expanded)
%              Number of equality atoms :   33 (  94 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m1_subset_1 > k7_subset_1 > k4_subset_1 > k7_setfam_1 > k6_setfam_1 > k5_setfam_1 > k4_xboole_0 > k3_subset_1 > #nlpp > k3_tarski > k2_subset_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_1

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

tff(f_74,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
       => ( B != k1_xboole_0
         => k6_setfam_1(A,k7_setfam_1(A,B)) = k3_subset_1(A,k5_setfam_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_tops_2)).

tff(f_59,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => k5_setfam_1(A,B) = k3_tarski(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k5_setfam_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => m1_subset_1(k5_setfam_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_setfam_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k3_subset_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).

tff(f_29,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k4_subset_1(A,B,k3_subset_1(A,B)) = k2_subset_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_subset_1)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => m1_subset_1(k4_subset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_subset_1)).

tff(f_47,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

tff(f_66,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => ( B != k1_xboole_0
       => k7_subset_1(A,k2_subset_1(A),k5_setfam_1(A,B)) = k6_setfam_1(A,k7_setfam_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_setfam_1)).

tff(c_26,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k1_zfmisc_1('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_61,plain,(
    ! [A_27,B_28] :
      ( k5_setfam_1(A_27,B_28) = k3_tarski(B_28)
      | ~ m1_subset_1(B_28,k1_zfmisc_1(k1_zfmisc_1(A_27))) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_70,plain,(
    k5_setfam_1('#skF_1','#skF_2') = k3_tarski('#skF_2') ),
    inference(resolution,[status(thm)],[c_26,c_61])).

tff(c_22,plain,(
    k6_setfam_1('#skF_1',k7_setfam_1('#skF_1','#skF_2')) != k3_subset_1('#skF_1',k5_setfam_1('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_71,plain,(
    k6_setfam_1('#skF_1',k7_setfam_1('#skF_1','#skF_2')) != k3_subset_1('#skF_1',k3_tarski('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_22])).

tff(c_76,plain,(
    ! [A_29,B_30] :
      ( m1_subset_1(k5_setfam_1(A_29,B_30),k1_zfmisc_1(A_29))
      | ~ m1_subset_1(B_30,k1_zfmisc_1(k1_zfmisc_1(A_29))) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_86,plain,
    ( m1_subset_1(k3_tarski('#skF_2'),k1_zfmisc_1('#skF_1'))
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k1_zfmisc_1('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_70,c_76])).

tff(c_90,plain,(
    m1_subset_1(k3_tarski('#skF_2'),k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_86])).

tff(c_6,plain,(
    ! [A_3,B_4] :
      ( k4_xboole_0(A_3,B_4) = k3_subset_1(A_3,B_4)
      | ~ m1_subset_1(B_4,k1_zfmisc_1(A_3)) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_94,plain,(
    k4_xboole_0('#skF_1',k3_tarski('#skF_2')) = k3_subset_1('#skF_1',k3_tarski('#skF_2')) ),
    inference(resolution,[status(thm)],[c_90,c_6])).

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

tff(c_99,plain,(
    ! [A_31,B_32] :
      ( k4_subset_1(A_31,B_32,k3_subset_1(A_31,B_32)) = A_31
      | ~ m1_subset_1(B_32,k1_zfmisc_1(A_31)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_14])).

tff(c_108,plain,(
    k4_subset_1('#skF_1',k3_tarski('#skF_2'),k3_subset_1('#skF_1',k3_tarski('#skF_2'))) = '#skF_1' ),
    inference(resolution,[status(thm)],[c_90,c_99])).

tff(c_172,plain,(
    ! [A_40,B_41,C_42] :
      ( m1_subset_1(k4_subset_1(A_40,B_41,C_42),k1_zfmisc_1(A_40))
      | ~ m1_subset_1(C_42,k1_zfmisc_1(A_40))
      | ~ m1_subset_1(B_41,k1_zfmisc_1(A_40)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_191,plain,
    ( m1_subset_1('#skF_1',k1_zfmisc_1('#skF_1'))
    | ~ m1_subset_1(k3_subset_1('#skF_1',k3_tarski('#skF_2')),k1_zfmisc_1('#skF_1'))
    | ~ m1_subset_1(k3_tarski('#skF_2'),k1_zfmisc_1('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_108,c_172])).

tff(c_200,plain,
    ( m1_subset_1('#skF_1',k1_zfmisc_1('#skF_1'))
    | ~ m1_subset_1(k3_subset_1('#skF_1',k3_tarski('#skF_2')),k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_191])).

tff(c_201,plain,(
    ~ m1_subset_1(k3_subset_1('#skF_1',k3_tarski('#skF_2')),k1_zfmisc_1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_200])).

tff(c_222,plain,(
    ~ m1_subset_1(k3_tarski('#skF_2'),k1_zfmisc_1('#skF_1')) ),
    inference(resolution,[status(thm)],[c_8,c_201])).

tff(c_226,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_222])).

tff(c_227,plain,(
    m1_subset_1('#skF_1',k1_zfmisc_1('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_200])).

tff(c_12,plain,(
    ! [A_10,B_11,C_12] :
      ( k7_subset_1(A_10,B_11,C_12) = k4_xboole_0(B_11,C_12)
      | ~ m1_subset_1(B_11,k1_zfmisc_1(A_10)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_239,plain,(
    ! [C_12] : k7_subset_1('#skF_1','#skF_1',C_12) = k4_xboole_0('#skF_1',C_12) ),
    inference(resolution,[status(thm)],[c_227,c_12])).

tff(c_24,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_20,plain,(
    ! [A_19,B_20] :
      ( k7_subset_1(A_19,k2_subset_1(A_19),k5_setfam_1(A_19,B_20)) = k6_setfam_1(A_19,k7_setfam_1(A_19,B_20))
      | k1_xboole_0 = B_20
      | ~ m1_subset_1(B_20,k1_zfmisc_1(k1_zfmisc_1(A_19))) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_306,plain,(
    ! [A_46,B_47] :
      ( k7_subset_1(A_46,A_46,k5_setfam_1(A_46,B_47)) = k6_setfam_1(A_46,k7_setfam_1(A_46,B_47))
      | k1_xboole_0 = B_47
      | ~ m1_subset_1(B_47,k1_zfmisc_1(k1_zfmisc_1(A_46))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_20])).

tff(c_319,plain,
    ( k7_subset_1('#skF_1','#skF_1',k5_setfam_1('#skF_1','#skF_2')) = k6_setfam_1('#skF_1',k7_setfam_1('#skF_1','#skF_2'))
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_26,c_306])).

tff(c_325,plain,
    ( k7_subset_1('#skF_1','#skF_1',k3_tarski('#skF_2')) = k6_setfam_1('#skF_1',k7_setfam_1('#skF_1','#skF_2'))
    | k1_xboole_0 = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_319])).

tff(c_326,plain,(
    k7_subset_1('#skF_1','#skF_1',k3_tarski('#skF_2')) = k6_setfam_1('#skF_1',k7_setfam_1('#skF_1','#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_325])).

tff(c_363,plain,(
    k6_setfam_1('#skF_1',k7_setfam_1('#skF_1','#skF_2')) = k4_xboole_0('#skF_1',k3_tarski('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_239,c_326])).

tff(c_364,plain,(
    k6_setfam_1('#skF_1',k7_setfam_1('#skF_1','#skF_2')) = k3_subset_1('#skF_1',k3_tarski('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_363])).

tff(c_366,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_71,c_364])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:58:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.27/1.35  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.35/1.36  
% 2.35/1.36  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.35/1.36  %$ m1_subset_1 > k7_subset_1 > k4_subset_1 > k7_setfam_1 > k6_setfam_1 > k5_setfam_1 > k4_xboole_0 > k3_subset_1 > #nlpp > k3_tarski > k2_subset_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_1
% 2.35/1.36  
% 2.35/1.36  %Foreground sorts:
% 2.35/1.36  
% 2.35/1.36  
% 2.35/1.36  %Background operators:
% 2.35/1.36  
% 2.35/1.36  
% 2.35/1.36  %Foreground operators:
% 2.35/1.36  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.35/1.36  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.35/1.36  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.35/1.36  tff(k7_setfam_1, type, k7_setfam_1: ($i * $i) > $i).
% 2.35/1.36  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 2.35/1.36  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 2.35/1.36  tff('#skF_2', type, '#skF_2': $i).
% 2.35/1.36  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 2.35/1.36  tff('#skF_1', type, '#skF_1': $i).
% 2.35/1.36  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.35/1.36  tff(k5_setfam_1, type, k5_setfam_1: ($i * $i) > $i).
% 2.35/1.36  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.35/1.36  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.35/1.36  tff(k6_setfam_1, type, k6_setfam_1: ($i * $i) > $i).
% 2.35/1.36  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.35/1.36  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 2.35/1.36  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.35/1.36  
% 2.35/1.38  tff(f_74, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (~(B = k1_xboole_0) => (k6_setfam_1(A, k7_setfam_1(A, B)) = k3_subset_1(A, k5_setfam_1(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_tops_2)).
% 2.35/1.38  tff(f_59, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (k5_setfam_1(A, B) = k3_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k5_setfam_1)).
% 2.35/1.38  tff(f_55, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => m1_subset_1(k5_setfam_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k5_setfam_1)).
% 2.35/1.38  tff(f_33, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 2.35/1.38  tff(f_37, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k3_subset_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 2.35/1.38  tff(f_29, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 2.35/1.38  tff(f_51, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k4_subset_1(A, B, k3_subset_1(A, B)) = k2_subset_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t25_subset_1)).
% 2.35/1.38  tff(f_43, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => m1_subset_1(k4_subset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k4_subset_1)).
% 2.35/1.38  tff(f_47, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 2.35/1.38  tff(f_66, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (~(B = k1_xboole_0) => (k7_subset_1(A, k2_subset_1(A), k5_setfam_1(A, B)) = k6_setfam_1(A, k7_setfam_1(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_setfam_1)).
% 2.35/1.38  tff(c_26, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k1_zfmisc_1('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.35/1.38  tff(c_61, plain, (![A_27, B_28]: (k5_setfam_1(A_27, B_28)=k3_tarski(B_28) | ~m1_subset_1(B_28, k1_zfmisc_1(k1_zfmisc_1(A_27))))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.35/1.38  tff(c_70, plain, (k5_setfam_1('#skF_1', '#skF_2')=k3_tarski('#skF_2')), inference(resolution, [status(thm)], [c_26, c_61])).
% 2.35/1.38  tff(c_22, plain, (k6_setfam_1('#skF_1', k7_setfam_1('#skF_1', '#skF_2'))!=k3_subset_1('#skF_1', k5_setfam_1('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.35/1.38  tff(c_71, plain, (k6_setfam_1('#skF_1', k7_setfam_1('#skF_1', '#skF_2'))!=k3_subset_1('#skF_1', k3_tarski('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_22])).
% 2.35/1.38  tff(c_76, plain, (![A_29, B_30]: (m1_subset_1(k5_setfam_1(A_29, B_30), k1_zfmisc_1(A_29)) | ~m1_subset_1(B_30, k1_zfmisc_1(k1_zfmisc_1(A_29))))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.35/1.38  tff(c_86, plain, (m1_subset_1(k3_tarski('#skF_2'), k1_zfmisc_1('#skF_1')) | ~m1_subset_1('#skF_2', k1_zfmisc_1(k1_zfmisc_1('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_70, c_76])).
% 2.35/1.38  tff(c_90, plain, (m1_subset_1(k3_tarski('#skF_2'), k1_zfmisc_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_86])).
% 2.35/1.38  tff(c_6, plain, (![A_3, B_4]: (k4_xboole_0(A_3, B_4)=k3_subset_1(A_3, B_4) | ~m1_subset_1(B_4, k1_zfmisc_1(A_3)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.35/1.38  tff(c_94, plain, (k4_xboole_0('#skF_1', k3_tarski('#skF_2'))=k3_subset_1('#skF_1', k3_tarski('#skF_2'))), inference(resolution, [status(thm)], [c_90, c_6])).
% 2.35/1.38  tff(c_8, plain, (![A_5, B_6]: (m1_subset_1(k3_subset_1(A_5, B_6), k1_zfmisc_1(A_5)) | ~m1_subset_1(B_6, k1_zfmisc_1(A_5)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.35/1.38  tff(c_4, plain, (![A_2]: (k2_subset_1(A_2)=A_2)), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.35/1.38  tff(c_14, plain, (![A_13, B_14]: (k4_subset_1(A_13, B_14, k3_subset_1(A_13, B_14))=k2_subset_1(A_13) | ~m1_subset_1(B_14, k1_zfmisc_1(A_13)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.35/1.38  tff(c_99, plain, (![A_31, B_32]: (k4_subset_1(A_31, B_32, k3_subset_1(A_31, B_32))=A_31 | ~m1_subset_1(B_32, k1_zfmisc_1(A_31)))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_14])).
% 2.35/1.38  tff(c_108, plain, (k4_subset_1('#skF_1', k3_tarski('#skF_2'), k3_subset_1('#skF_1', k3_tarski('#skF_2')))='#skF_1'), inference(resolution, [status(thm)], [c_90, c_99])).
% 2.35/1.38  tff(c_172, plain, (![A_40, B_41, C_42]: (m1_subset_1(k4_subset_1(A_40, B_41, C_42), k1_zfmisc_1(A_40)) | ~m1_subset_1(C_42, k1_zfmisc_1(A_40)) | ~m1_subset_1(B_41, k1_zfmisc_1(A_40)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.35/1.38  tff(c_191, plain, (m1_subset_1('#skF_1', k1_zfmisc_1('#skF_1')) | ~m1_subset_1(k3_subset_1('#skF_1', k3_tarski('#skF_2')), k1_zfmisc_1('#skF_1')) | ~m1_subset_1(k3_tarski('#skF_2'), k1_zfmisc_1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_108, c_172])).
% 2.35/1.38  tff(c_200, plain, (m1_subset_1('#skF_1', k1_zfmisc_1('#skF_1')) | ~m1_subset_1(k3_subset_1('#skF_1', k3_tarski('#skF_2')), k1_zfmisc_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_90, c_191])).
% 2.35/1.38  tff(c_201, plain, (~m1_subset_1(k3_subset_1('#skF_1', k3_tarski('#skF_2')), k1_zfmisc_1('#skF_1'))), inference(splitLeft, [status(thm)], [c_200])).
% 2.35/1.38  tff(c_222, plain, (~m1_subset_1(k3_tarski('#skF_2'), k1_zfmisc_1('#skF_1'))), inference(resolution, [status(thm)], [c_8, c_201])).
% 2.35/1.38  tff(c_226, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_90, c_222])).
% 2.35/1.38  tff(c_227, plain, (m1_subset_1('#skF_1', k1_zfmisc_1('#skF_1'))), inference(splitRight, [status(thm)], [c_200])).
% 2.35/1.38  tff(c_12, plain, (![A_10, B_11, C_12]: (k7_subset_1(A_10, B_11, C_12)=k4_xboole_0(B_11, C_12) | ~m1_subset_1(B_11, k1_zfmisc_1(A_10)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.35/1.38  tff(c_239, plain, (![C_12]: (k7_subset_1('#skF_1', '#skF_1', C_12)=k4_xboole_0('#skF_1', C_12))), inference(resolution, [status(thm)], [c_227, c_12])).
% 2.35/1.38  tff(c_24, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.35/1.38  tff(c_20, plain, (![A_19, B_20]: (k7_subset_1(A_19, k2_subset_1(A_19), k5_setfam_1(A_19, B_20))=k6_setfam_1(A_19, k7_setfam_1(A_19, B_20)) | k1_xboole_0=B_20 | ~m1_subset_1(B_20, k1_zfmisc_1(k1_zfmisc_1(A_19))))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.35/1.38  tff(c_306, plain, (![A_46, B_47]: (k7_subset_1(A_46, A_46, k5_setfam_1(A_46, B_47))=k6_setfam_1(A_46, k7_setfam_1(A_46, B_47)) | k1_xboole_0=B_47 | ~m1_subset_1(B_47, k1_zfmisc_1(k1_zfmisc_1(A_46))))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_20])).
% 2.35/1.38  tff(c_319, plain, (k7_subset_1('#skF_1', '#skF_1', k5_setfam_1('#skF_1', '#skF_2'))=k6_setfam_1('#skF_1', k7_setfam_1('#skF_1', '#skF_2')) | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_26, c_306])).
% 2.35/1.38  tff(c_325, plain, (k7_subset_1('#skF_1', '#skF_1', k3_tarski('#skF_2'))=k6_setfam_1('#skF_1', k7_setfam_1('#skF_1', '#skF_2')) | k1_xboole_0='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_70, c_319])).
% 2.35/1.38  tff(c_326, plain, (k7_subset_1('#skF_1', '#skF_1', k3_tarski('#skF_2'))=k6_setfam_1('#skF_1', k7_setfam_1('#skF_1', '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_24, c_325])).
% 2.35/1.38  tff(c_363, plain, (k6_setfam_1('#skF_1', k7_setfam_1('#skF_1', '#skF_2'))=k4_xboole_0('#skF_1', k3_tarski('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_239, c_326])).
% 2.35/1.38  tff(c_364, plain, (k6_setfam_1('#skF_1', k7_setfam_1('#skF_1', '#skF_2'))=k3_subset_1('#skF_1', k3_tarski('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_94, c_363])).
% 2.35/1.38  tff(c_366, plain, $false, inference(negUnitSimplification, [status(thm)], [c_71, c_364])).
% 2.35/1.38  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.35/1.38  
% 2.35/1.38  Inference rules
% 2.35/1.38  ----------------------
% 2.35/1.38  #Ref     : 0
% 2.35/1.38  #Sup     : 92
% 2.35/1.38  #Fact    : 0
% 2.35/1.38  #Define  : 0
% 2.35/1.38  #Split   : 2
% 2.35/1.38  #Chain   : 0
% 2.35/1.38  #Close   : 0
% 2.35/1.38  
% 2.35/1.38  Ordering : KBO
% 2.35/1.38  
% 2.35/1.38  Simplification rules
% 2.35/1.38  ----------------------
% 2.35/1.38  #Subsume      : 0
% 2.35/1.38  #Demod        : 21
% 2.35/1.38  #Tautology    : 39
% 2.35/1.38  #SimpNegUnit  : 3
% 2.35/1.38  #BackRed      : 2
% 2.35/1.38  
% 2.35/1.38  #Partial instantiations: 0
% 2.35/1.38  #Strategies tried      : 1
% 2.35/1.38  
% 2.35/1.38  Timing (in seconds)
% 2.35/1.38  ----------------------
% 2.35/1.38  Preprocessing        : 0.32
% 2.35/1.38  Parsing              : 0.18
% 2.35/1.38  CNF conversion       : 0.02
% 2.35/1.38  Main loop            : 0.23
% 2.35/1.38  Inferencing          : 0.08
% 2.35/1.38  Reduction            : 0.07
% 2.35/1.38  Demodulation         : 0.05
% 2.35/1.38  BG Simplification    : 0.02
% 2.35/1.38  Subsumption          : 0.04
% 2.35/1.38  Abstraction          : 0.02
% 2.35/1.38  MUC search           : 0.00
% 2.35/1.38  Cooper               : 0.00
% 2.35/1.38  Total                : 0.58
% 2.35/1.38  Index Insertion      : 0.00
% 2.35/1.38  Index Deletion       : 0.00
% 2.35/1.38  Index Matching       : 0.00
% 2.35/1.38  BG Taut test         : 0.00
%------------------------------------------------------------------------------
