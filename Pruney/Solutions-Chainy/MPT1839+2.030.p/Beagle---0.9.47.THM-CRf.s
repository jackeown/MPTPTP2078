%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:28:25 EST 2020

% Result     : Theorem 2.23s
% Output     : CNFRefutation 2.23s
% Verified   : 
% Statistics : Number of formulae       :   70 (  89 expanded)
%              Number of leaves         :   31 (  43 expanded)
%              Depth                    :   13
%              Number of atoms          :  103 ( 160 expanded)
%              Number of equality atoms :   54 (  63 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > m1_subset_1 > v1_zfmisc_1 > v1_xboole_0 > k6_domain_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_setfam_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(k6_domain_1,type,(
    k6_domain_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_zfmisc_1,type,(
    v1_zfmisc_1: $i > $o )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_30,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_86,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v1_xboole_0(A)
          & v1_zfmisc_1(A) )
       => ! [B] :
            ( ~ v1_xboole_0(k3_xboole_0(A,B))
           => r1_tarski(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tex_2)).

tff(f_40,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_36,axiom,(
    ! [A,B] : k3_xboole_0(A,k2_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_xboole_1)).

tff(f_32,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_74,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ( v1_zfmisc_1(A)
      <=> ? [B] :
            ( m1_subset_1(B,A)
            & A = k6_domain_1(A,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tex_2)).

tff(f_64,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_34,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

tff(f_55,axiom,(
    ! [A,B] : k2_xboole_0(k1_tarski(A),B) != k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_zfmisc_1)).

tff(f_38,axiom,(
    ! [A,B] : k2_xboole_0(A,k3_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_xboole_1)).

tff(f_52,axiom,(
    ! [A,B,C] :
      ~ ( k1_tarski(A) = k2_xboole_0(B,C)
        & B != C
        & B != k1_xboole_0
        & C != k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_zfmisc_1)).

tff(c_157,plain,(
    ! [A_43,B_44] :
      ( r1_tarski(A_43,B_44)
      | k4_xboole_0(A_43,B_44) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_32,plain,(
    ~ r1_tarski('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_165,plain,(
    k4_xboole_0('#skF_2','#skF_3') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_157,c_32])).

tff(c_16,plain,(
    ! [A_10,B_11] : r1_tarski(A_10,k2_xboole_0(A_10,B_11)) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_148,plain,(
    ! [A_41,B_42] :
      ( k4_xboole_0(A_41,B_42) = k1_xboole_0
      | ~ r1_tarski(A_41,B_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_156,plain,(
    ! [A_10,B_11] : k4_xboole_0(A_10,k2_xboole_0(A_10,B_11)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_16,c_148])).

tff(c_12,plain,(
    ! [A_6,B_7] : k3_xboole_0(A_6,k2_xboole_0(A_6,B_7)) = A_6 ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_193,plain,(
    ! [A_49,B_50] : k5_xboole_0(A_49,k3_xboole_0(A_49,B_50)) = k4_xboole_0(A_49,B_50) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_205,plain,(
    ! [A_6,B_7] : k4_xboole_0(A_6,k2_xboole_0(A_6,B_7)) = k5_xboole_0(A_6,A_6) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_193])).

tff(c_209,plain,(
    ! [A_6] : k5_xboole_0(A_6,A_6) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_156,c_205])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_38,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_36,plain,(
    v1_zfmisc_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_30,plain,(
    ! [A_21] :
      ( m1_subset_1('#skF_1'(A_21),A_21)
      | ~ v1_zfmisc_1(A_21)
      | v1_xboole_0(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_227,plain,(
    ! [A_53,B_54] :
      ( k6_domain_1(A_53,B_54) = k1_tarski(B_54)
      | ~ m1_subset_1(B_54,A_53)
      | v1_xboole_0(A_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_249,plain,(
    ! [A_60] :
      ( k6_domain_1(A_60,'#skF_1'(A_60)) = k1_tarski('#skF_1'(A_60))
      | ~ v1_zfmisc_1(A_60)
      | v1_xboole_0(A_60) ) ),
    inference(resolution,[status(thm)],[c_30,c_227])).

tff(c_28,plain,(
    ! [A_21] :
      ( k6_domain_1(A_21,'#skF_1'(A_21)) = A_21
      | ~ v1_zfmisc_1(A_21)
      | v1_xboole_0(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_264,plain,(
    ! [A_61] :
      ( k1_tarski('#skF_1'(A_61)) = A_61
      | ~ v1_zfmisc_1(A_61)
      | v1_xboole_0(A_61)
      | ~ v1_zfmisc_1(A_61)
      | v1_xboole_0(A_61) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_249,c_28])).

tff(c_10,plain,(
    ! [A_5] : k2_xboole_0(A_5,k1_xboole_0) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_53,plain,(
    ! [A_30,B_31] : k2_xboole_0(k1_tarski(A_30),B_31) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_57,plain,(
    ! [A_30] : k1_tarski(A_30) != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_53])).

tff(c_280,plain,(
    ! [A_62] :
      ( k1_xboole_0 != A_62
      | ~ v1_zfmisc_1(A_62)
      | v1_xboole_0(A_62)
      | ~ v1_zfmisc_1(A_62)
      | v1_xboole_0(A_62) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_264,c_57])).

tff(c_282,plain,
    ( k1_xboole_0 != '#skF_2'
    | ~ v1_zfmisc_1('#skF_2')
    | v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_36,c_280])).

tff(c_285,plain,
    ( k1_xboole_0 != '#skF_2'
    | v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_282])).

tff(c_286,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_285])).

tff(c_255,plain,(
    ! [A_60] :
      ( k1_tarski('#skF_1'(A_60)) = A_60
      | ~ v1_zfmisc_1(A_60)
      | v1_xboole_0(A_60)
      | ~ v1_zfmisc_1(A_60)
      | v1_xboole_0(A_60) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_249,c_28])).

tff(c_14,plain,(
    ! [A_8,B_9] : k2_xboole_0(A_8,k3_xboole_0(A_8,B_9)) = A_8 ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_237,plain,(
    ! [C_57,B_58,A_59] :
      ( k1_xboole_0 = C_57
      | k1_xboole_0 = B_58
      | C_57 = B_58
      | k2_xboole_0(B_58,C_57) != k1_tarski(A_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_292,plain,(
    ! [A_63,B_64,A_65] :
      ( k3_xboole_0(A_63,B_64) = k1_xboole_0
      | k1_xboole_0 = A_63
      | k3_xboole_0(A_63,B_64) = A_63
      | k1_tarski(A_65) != A_63 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_237])).

tff(c_394,plain,(
    ! [A_72,B_73] :
      ( k3_xboole_0(A_72,B_73) = k1_xboole_0
      | k1_xboole_0 = A_72
      | k3_xboole_0(A_72,B_73) = A_72
      | ~ v1_zfmisc_1(A_72)
      | v1_xboole_0(A_72) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_255,c_292])).

tff(c_396,plain,(
    ! [B_73] :
      ( k3_xboole_0('#skF_2',B_73) = k1_xboole_0
      | k1_xboole_0 = '#skF_2'
      | k3_xboole_0('#skF_2',B_73) = '#skF_2'
      | v1_xboole_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_36,c_394])).

tff(c_404,plain,(
    ! [B_74] :
      ( k3_xboole_0('#skF_2',B_74) = k1_xboole_0
      | k3_xboole_0('#skF_2',B_74) = '#skF_2' ) ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_286,c_396])).

tff(c_34,plain,(
    ~ v1_xboole_0(k3_xboole_0('#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_424,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | k3_xboole_0('#skF_2','#skF_3') = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_404,c_34])).

tff(c_443,plain,(
    k3_xboole_0('#skF_2','#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_424])).

tff(c_8,plain,(
    ! [A_3,B_4] : k5_xboole_0(A_3,k3_xboole_0(A_3,B_4)) = k4_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_456,plain,(
    k5_xboole_0('#skF_2','#skF_2') = k4_xboole_0('#skF_2','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_443,c_8])).

tff(c_467,plain,(
    k4_xboole_0('#skF_2','#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_209,c_456])).

tff(c_469,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_165,c_467])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:00:06 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.23/1.33  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.23/1.34  
% 2.23/1.34  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.23/1.34  %$ r1_tarski > m1_subset_1 > v1_zfmisc_1 > v1_xboole_0 > k6_domain_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_setfam_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3
% 2.23/1.34  
% 2.23/1.34  %Foreground sorts:
% 2.23/1.34  
% 2.23/1.34  
% 2.23/1.34  %Background operators:
% 2.23/1.34  
% 2.23/1.34  
% 2.23/1.34  %Foreground operators:
% 2.23/1.34  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.23/1.34  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.23/1.34  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.23/1.34  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.23/1.34  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.23/1.34  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.23/1.34  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 2.23/1.34  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.23/1.34  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.23/1.34  tff('#skF_2', type, '#skF_2': $i).
% 2.23/1.34  tff('#skF_3', type, '#skF_3': $i).
% 2.23/1.34  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.23/1.34  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.23/1.34  tff(v1_zfmisc_1, type, v1_zfmisc_1: $i > $o).
% 2.23/1.34  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.23/1.34  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.23/1.34  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.23/1.34  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.23/1.34  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.23/1.34  
% 2.23/1.35  tff(f_30, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 2.23/1.35  tff(f_86, negated_conjecture, ~(![A]: ((~v1_xboole_0(A) & v1_zfmisc_1(A)) => (![B]: (~v1_xboole_0(k3_xboole_0(A, B)) => r1_tarski(A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_tex_2)).
% 2.23/1.35  tff(f_40, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 2.23/1.35  tff(f_36, axiom, (![A, B]: (k3_xboole_0(A, k2_xboole_0(A, B)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t21_xboole_1)).
% 2.23/1.35  tff(f_32, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 2.23/1.35  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.23/1.35  tff(f_74, axiom, (![A]: (~v1_xboole_0(A) => (v1_zfmisc_1(A) <=> (?[B]: (m1_subset_1(B, A) & (A = k6_domain_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tex_2)).
% 2.23/1.35  tff(f_64, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 2.23/1.35  tff(f_34, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 2.23/1.35  tff(f_55, axiom, (![A, B]: ~(k2_xboole_0(k1_tarski(A), B) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_zfmisc_1)).
% 2.23/1.35  tff(f_38, axiom, (![A, B]: (k2_xboole_0(A, k3_xboole_0(A, B)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_xboole_1)).
% 2.23/1.35  tff(f_52, axiom, (![A, B, C]: ~((((k1_tarski(A) = k2_xboole_0(B, C)) & ~(B = C)) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_zfmisc_1)).
% 2.23/1.35  tff(c_157, plain, (![A_43, B_44]: (r1_tarski(A_43, B_44) | k4_xboole_0(A_43, B_44)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_30])).
% 2.23/1.35  tff(c_32, plain, (~r1_tarski('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.23/1.35  tff(c_165, plain, (k4_xboole_0('#skF_2', '#skF_3')!=k1_xboole_0), inference(resolution, [status(thm)], [c_157, c_32])).
% 2.23/1.35  tff(c_16, plain, (![A_10, B_11]: (r1_tarski(A_10, k2_xboole_0(A_10, B_11)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.23/1.35  tff(c_148, plain, (![A_41, B_42]: (k4_xboole_0(A_41, B_42)=k1_xboole_0 | ~r1_tarski(A_41, B_42))), inference(cnfTransformation, [status(thm)], [f_30])).
% 2.23/1.35  tff(c_156, plain, (![A_10, B_11]: (k4_xboole_0(A_10, k2_xboole_0(A_10, B_11))=k1_xboole_0)), inference(resolution, [status(thm)], [c_16, c_148])).
% 2.23/1.35  tff(c_12, plain, (![A_6, B_7]: (k3_xboole_0(A_6, k2_xboole_0(A_6, B_7))=A_6)), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.23/1.35  tff(c_193, plain, (![A_49, B_50]: (k5_xboole_0(A_49, k3_xboole_0(A_49, B_50))=k4_xboole_0(A_49, B_50))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.23/1.35  tff(c_205, plain, (![A_6, B_7]: (k4_xboole_0(A_6, k2_xboole_0(A_6, B_7))=k5_xboole_0(A_6, A_6))), inference(superposition, [status(thm), theory('equality')], [c_12, c_193])).
% 2.23/1.35  tff(c_209, plain, (![A_6]: (k5_xboole_0(A_6, A_6)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_156, c_205])).
% 2.23/1.35  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 2.23/1.35  tff(c_38, plain, (~v1_xboole_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.23/1.35  tff(c_36, plain, (v1_zfmisc_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.23/1.35  tff(c_30, plain, (![A_21]: (m1_subset_1('#skF_1'(A_21), A_21) | ~v1_zfmisc_1(A_21) | v1_xboole_0(A_21))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.23/1.35  tff(c_227, plain, (![A_53, B_54]: (k6_domain_1(A_53, B_54)=k1_tarski(B_54) | ~m1_subset_1(B_54, A_53) | v1_xboole_0(A_53))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.23/1.35  tff(c_249, plain, (![A_60]: (k6_domain_1(A_60, '#skF_1'(A_60))=k1_tarski('#skF_1'(A_60)) | ~v1_zfmisc_1(A_60) | v1_xboole_0(A_60))), inference(resolution, [status(thm)], [c_30, c_227])).
% 2.23/1.35  tff(c_28, plain, (![A_21]: (k6_domain_1(A_21, '#skF_1'(A_21))=A_21 | ~v1_zfmisc_1(A_21) | v1_xboole_0(A_21))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.23/1.35  tff(c_264, plain, (![A_61]: (k1_tarski('#skF_1'(A_61))=A_61 | ~v1_zfmisc_1(A_61) | v1_xboole_0(A_61) | ~v1_zfmisc_1(A_61) | v1_xboole_0(A_61))), inference(superposition, [status(thm), theory('equality')], [c_249, c_28])).
% 2.23/1.35  tff(c_10, plain, (![A_5]: (k2_xboole_0(A_5, k1_xboole_0)=A_5)), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.23/1.35  tff(c_53, plain, (![A_30, B_31]: (k2_xboole_0(k1_tarski(A_30), B_31)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.23/1.35  tff(c_57, plain, (![A_30]: (k1_tarski(A_30)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_10, c_53])).
% 2.23/1.35  tff(c_280, plain, (![A_62]: (k1_xboole_0!=A_62 | ~v1_zfmisc_1(A_62) | v1_xboole_0(A_62) | ~v1_zfmisc_1(A_62) | v1_xboole_0(A_62))), inference(superposition, [status(thm), theory('equality')], [c_264, c_57])).
% 2.23/1.35  tff(c_282, plain, (k1_xboole_0!='#skF_2' | ~v1_zfmisc_1('#skF_2') | v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_36, c_280])).
% 2.23/1.35  tff(c_285, plain, (k1_xboole_0!='#skF_2' | v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_282])).
% 2.23/1.35  tff(c_286, plain, (k1_xboole_0!='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_38, c_285])).
% 2.23/1.35  tff(c_255, plain, (![A_60]: (k1_tarski('#skF_1'(A_60))=A_60 | ~v1_zfmisc_1(A_60) | v1_xboole_0(A_60) | ~v1_zfmisc_1(A_60) | v1_xboole_0(A_60))), inference(superposition, [status(thm), theory('equality')], [c_249, c_28])).
% 2.23/1.35  tff(c_14, plain, (![A_8, B_9]: (k2_xboole_0(A_8, k3_xboole_0(A_8, B_9))=A_8)), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.23/1.35  tff(c_237, plain, (![C_57, B_58, A_59]: (k1_xboole_0=C_57 | k1_xboole_0=B_58 | C_57=B_58 | k2_xboole_0(B_58, C_57)!=k1_tarski(A_59))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.23/1.35  tff(c_292, plain, (![A_63, B_64, A_65]: (k3_xboole_0(A_63, B_64)=k1_xboole_0 | k1_xboole_0=A_63 | k3_xboole_0(A_63, B_64)=A_63 | k1_tarski(A_65)!=A_63)), inference(superposition, [status(thm), theory('equality')], [c_14, c_237])).
% 2.23/1.35  tff(c_394, plain, (![A_72, B_73]: (k3_xboole_0(A_72, B_73)=k1_xboole_0 | k1_xboole_0=A_72 | k3_xboole_0(A_72, B_73)=A_72 | ~v1_zfmisc_1(A_72) | v1_xboole_0(A_72))), inference(superposition, [status(thm), theory('equality')], [c_255, c_292])).
% 2.23/1.35  tff(c_396, plain, (![B_73]: (k3_xboole_0('#skF_2', B_73)=k1_xboole_0 | k1_xboole_0='#skF_2' | k3_xboole_0('#skF_2', B_73)='#skF_2' | v1_xboole_0('#skF_2'))), inference(resolution, [status(thm)], [c_36, c_394])).
% 2.23/1.35  tff(c_404, plain, (![B_74]: (k3_xboole_0('#skF_2', B_74)=k1_xboole_0 | k3_xboole_0('#skF_2', B_74)='#skF_2')), inference(negUnitSimplification, [status(thm)], [c_38, c_286, c_396])).
% 2.23/1.35  tff(c_34, plain, (~v1_xboole_0(k3_xboole_0('#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.23/1.35  tff(c_424, plain, (~v1_xboole_0(k1_xboole_0) | k3_xboole_0('#skF_2', '#skF_3')='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_404, c_34])).
% 2.23/1.35  tff(c_443, plain, (k3_xboole_0('#skF_2', '#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_2, c_424])).
% 2.23/1.35  tff(c_8, plain, (![A_3, B_4]: (k5_xboole_0(A_3, k3_xboole_0(A_3, B_4))=k4_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.23/1.35  tff(c_456, plain, (k5_xboole_0('#skF_2', '#skF_2')=k4_xboole_0('#skF_2', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_443, c_8])).
% 2.23/1.35  tff(c_467, plain, (k4_xboole_0('#skF_2', '#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_209, c_456])).
% 2.23/1.35  tff(c_469, plain, $false, inference(negUnitSimplification, [status(thm)], [c_165, c_467])).
% 2.23/1.35  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.23/1.35  
% 2.23/1.35  Inference rules
% 2.23/1.35  ----------------------
% 2.23/1.35  #Ref     : 1
% 2.23/1.35  #Sup     : 95
% 2.23/1.35  #Fact    : 2
% 2.23/1.35  #Define  : 0
% 2.23/1.35  #Split   : 0
% 2.23/1.35  #Chain   : 0
% 2.23/1.35  #Close   : 0
% 2.23/1.35  
% 2.23/1.35  Ordering : KBO
% 2.23/1.35  
% 2.23/1.35  Simplification rules
% 2.23/1.35  ----------------------
% 2.23/1.35  #Subsume      : 9
% 2.23/1.35  #Demod        : 31
% 2.45/1.35  #Tautology    : 63
% 2.45/1.35  #SimpNegUnit  : 17
% 2.45/1.35  #BackRed      : 1
% 2.45/1.35  
% 2.45/1.35  #Partial instantiations: 0
% 2.45/1.35  #Strategies tried      : 1
% 2.45/1.35  
% 2.45/1.35  Timing (in seconds)
% 2.45/1.35  ----------------------
% 2.45/1.36  Preprocessing        : 0.31
% 2.45/1.36  Parsing              : 0.17
% 2.45/1.36  CNF conversion       : 0.02
% 2.45/1.36  Main loop            : 0.22
% 2.45/1.36  Inferencing          : 0.09
% 2.45/1.36  Reduction            : 0.07
% 2.45/1.36  Demodulation         : 0.05
% 2.45/1.36  BG Simplification    : 0.01
% 2.45/1.36  Subsumption          : 0.04
% 2.45/1.36  Abstraction          : 0.02
% 2.45/1.36  MUC search           : 0.00
% 2.45/1.36  Cooper               : 0.00
% 2.45/1.36  Total                : 0.57
% 2.45/1.36  Index Insertion      : 0.00
% 2.45/1.36  Index Deletion       : 0.00
% 2.45/1.36  Index Matching       : 0.00
% 2.45/1.36  BG Taut test         : 0.00
%------------------------------------------------------------------------------
