%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:55:53 EST 2020

% Result     : Theorem 12.62s
% Output     : CNFRefutation 12.72s
% Verified   : 
% Statistics : Number of formulae       :   83 ( 144 expanded)
%              Number of leaves         :   36 (  63 expanded)
%              Depth                    :   11
%              Number of atoms          :   85 ( 198 expanded)
%              Number of equality atoms :   42 (  80 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k9_subset_1 > k7_subset_1 > k6_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > #nlpp > k1_zfmisc_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k7_subset_1,type,(
    k7_subset_1: ( $i * $i * $i ) > $i )).

tff(k6_subset_1,type,(
    k6_subset_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_88,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => ! [C] :
            ( m1_subset_1(C,k1_zfmisc_1(A))
           => k7_subset_1(A,B,C) = k9_subset_1(A,B,k3_subset_1(A,C)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_subset_1)).

tff(f_65,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_72,axiom,(
    ! [A,B] : k6_subset_1(A,B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

tff(f_67,axiom,(
    ! [A,B] : m1_subset_1(k6_subset_1(A,B),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_subset_1)).

tff(f_80,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(f_76,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

tff(f_70,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_61,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_48,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_39,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_37,axiom,(
    ! [A,B,C] : k4_xboole_0(k4_xboole_0(A,B),C) = k4_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

tff(f_41,axiom,(
    ! [A,B,C] : k4_xboole_0(A,k2_xboole_0(B,C)) = k3_xboole_0(k4_xboole_0(A,B),k4_xboole_0(A,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t53_xboole_1)).

tff(c_50,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_271,plain,(
    ! [A_77,B_78] :
      ( k4_xboole_0(A_77,B_78) = k3_subset_1(A_77,B_78)
      | ~ m1_subset_1(B_78,k1_zfmisc_1(A_77)) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_301,plain,(
    k4_xboole_0('#skF_3','#skF_5') = k3_subset_1('#skF_3','#skF_5') ),
    inference(resolution,[status(thm)],[c_50,c_271])).

tff(c_42,plain,(
    ! [A_29,B_30] : k6_subset_1(A_29,B_30) = k4_xboole_0(A_29,B_30) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_38,plain,(
    ! [A_26,B_27] : m1_subset_1(k6_subset_1(A_26,B_27),k1_zfmisc_1(A_26)) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_53,plain,(
    ! [A_26,B_27] : m1_subset_1(k4_xboole_0(A_26,B_27),k1_zfmisc_1(A_26)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_38])).

tff(c_686,plain,(
    ! [A_86,B_87,C_88] :
      ( k9_subset_1(A_86,B_87,C_88) = k3_xboole_0(B_87,C_88)
      | ~ m1_subset_1(C_88,k1_zfmisc_1(A_86)) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_3612,plain,(
    ! [A_154,B_155,B_156] : k9_subset_1(A_154,B_155,k4_xboole_0(A_154,B_156)) = k3_xboole_0(B_155,k4_xboole_0(A_154,B_156)) ),
    inference(resolution,[status(thm)],[c_53,c_686])).

tff(c_3654,plain,(
    ! [B_155] : k9_subset_1('#skF_3',B_155,k3_subset_1('#skF_3','#skF_5')) = k3_xboole_0(B_155,k4_xboole_0('#skF_3','#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_301,c_3612])).

tff(c_3677,plain,(
    ! [B_155] : k9_subset_1('#skF_3',B_155,k3_subset_1('#skF_3','#skF_5')) = k3_xboole_0(B_155,k3_subset_1('#skF_3','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_301,c_3654])).

tff(c_52,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_547,plain,(
    ! [A_82,B_83,C_84] :
      ( k7_subset_1(A_82,B_83,C_84) = k4_xboole_0(B_83,C_84)
      | ~ m1_subset_1(B_83,k1_zfmisc_1(A_82)) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_575,plain,(
    ! [C_84] : k7_subset_1('#skF_3','#skF_4',C_84) = k4_xboole_0('#skF_4',C_84) ),
    inference(resolution,[status(thm)],[c_52,c_547])).

tff(c_48,plain,(
    k9_subset_1('#skF_3','#skF_4',k3_subset_1('#skF_3','#skF_5')) != k7_subset_1('#skF_3','#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_613,plain,(
    k9_subset_1('#skF_3','#skF_4',k3_subset_1('#skF_3','#skF_5')) != k4_xboole_0('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_575,c_48])).

tff(c_24913,plain,(
    k3_xboole_0('#skF_4',k3_subset_1('#skF_3','#skF_5')) != k4_xboole_0('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3677,c_613])).

tff(c_40,plain,(
    ! [A_28] : ~ v1_xboole_0(k1_zfmisc_1(A_28)) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_143,plain,(
    ! [B_59,A_60] :
      ( r2_hidden(B_59,A_60)
      | ~ m1_subset_1(B_59,A_60)
      | v1_xboole_0(A_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_16,plain,(
    ! [C_21,A_17] :
      ( r1_tarski(C_21,A_17)
      | ~ r2_hidden(C_21,k1_zfmisc_1(A_17)) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_147,plain,(
    ! [B_59,A_17] :
      ( r1_tarski(B_59,A_17)
      | ~ m1_subset_1(B_59,k1_zfmisc_1(A_17))
      | v1_xboole_0(k1_zfmisc_1(A_17)) ) ),
    inference(resolution,[status(thm)],[c_143,c_16])).

tff(c_238,plain,(
    ! [B_75,A_76] :
      ( r1_tarski(B_75,A_76)
      | ~ m1_subset_1(B_75,k1_zfmisc_1(A_76)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_147])).

tff(c_269,plain,(
    r1_tarski('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_52,c_238])).

tff(c_6,plain,(
    ! [A_5,B_6] :
      ( k3_xboole_0(A_5,B_6) = A_5
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_305,plain,(
    k3_xboole_0('#skF_4','#skF_3') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_269,c_6])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_151,plain,(
    ! [A_61,B_62] : k4_xboole_0(A_61,k4_xboole_0(A_61,B_62)) = k3_xboole_0(A_61,B_62) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_8,plain,(
    ! [A_7,B_8] : r1_tarski(k4_xboole_0(A_7,B_8),A_7) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_163,plain,(
    ! [A_61,B_62] : r1_tarski(k3_xboole_0(A_61,B_62),A_61) ),
    inference(superposition,[status(thm),theory(equality)],[c_151,c_8])).

tff(c_322,plain,(
    r1_tarski('#skF_4','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_305,c_163])).

tff(c_348,plain,(
    k3_xboole_0('#skF_4','#skF_4') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_322,c_6])).

tff(c_172,plain,(
    ! [A_63,B_64] : r1_tarski(k3_xboole_0(A_63,B_64),A_63) ),
    inference(superposition,[status(thm),theory(equality)],[c_151,c_8])).

tff(c_183,plain,(
    ! [B_65,A_66] : r1_tarski(k3_xboole_0(B_65,A_66),A_66) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_172])).

tff(c_3406,plain,(
    ! [B_151,A_152] : k3_xboole_0(k3_xboole_0(B_151,A_152),A_152) = k3_xboole_0(B_151,A_152) ),
    inference(resolution,[status(thm)],[c_183,c_6])).

tff(c_17294,plain,(
    ! [A_347,B_348] : k3_xboole_0(k3_xboole_0(A_347,B_348),A_347) = k3_xboole_0(B_348,A_347) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_3406])).

tff(c_17708,plain,(
    k3_xboole_0('#skF_3','#skF_4') = k3_xboole_0('#skF_4','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_305,c_17294])).

tff(c_17829,plain,(
    k3_xboole_0('#skF_3','#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_348,c_17708])).

tff(c_12,plain,(
    ! [A_12,B_13] : k4_xboole_0(A_12,k4_xboole_0(A_12,B_13)) = k3_xboole_0(A_12,B_13) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_409,plain,(
    ! [A_79,B_80,C_81] : k4_xboole_0(k4_xboole_0(A_79,B_80),C_81) = k4_xboole_0(A_79,k2_xboole_0(B_80,C_81)) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_440,plain,(
    ! [A_12,B_13,C_81] : k4_xboole_0(A_12,k2_xboole_0(k4_xboole_0(A_12,B_13),C_81)) = k4_xboole_0(k3_xboole_0(A_12,B_13),C_81) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_409])).

tff(c_836,plain,(
    ! [A_90,B_91,C_92] : k3_xboole_0(k4_xboole_0(A_90,B_91),k4_xboole_0(A_90,C_92)) = k4_xboole_0(A_90,k2_xboole_0(B_91,C_92)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_920,plain,(
    ! [A_12,B_13,C_92] : k4_xboole_0(A_12,k2_xboole_0(k4_xboole_0(A_12,B_13),C_92)) = k3_xboole_0(k3_xboole_0(A_12,B_13),k4_xboole_0(A_12,C_92)) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_836])).

tff(c_6600,plain,(
    ! [A_213,B_214,C_215] : k3_xboole_0(k3_xboole_0(A_213,B_214),k4_xboole_0(A_213,C_215)) = k4_xboole_0(k3_xboole_0(A_213,B_214),C_215) ),
    inference(demodulation,[status(thm),theory(equality)],[c_440,c_920])).

tff(c_25310,plain,(
    ! [A_397,C_398,B_399] : k3_xboole_0(k4_xboole_0(A_397,C_398),k3_xboole_0(A_397,B_399)) = k4_xboole_0(k3_xboole_0(A_397,B_399),C_398) ),
    inference(superposition,[status(thm),theory(equality)],[c_6600,c_2])).

tff(c_26372,plain,(
    ! [B_402] : k3_xboole_0(k3_subset_1('#skF_3','#skF_5'),k3_xboole_0('#skF_3',B_402)) = k4_xboole_0(k3_xboole_0('#skF_3',B_402),'#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_301,c_25310])).

tff(c_26553,plain,(
    k4_xboole_0(k3_xboole_0('#skF_3','#skF_4'),'#skF_5') = k3_xboole_0(k3_subset_1('#skF_3','#skF_5'),'#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_17829,c_26372])).

tff(c_26655,plain,(
    k3_xboole_0('#skF_4',k3_subset_1('#skF_3','#skF_5')) = k4_xboole_0('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_305,c_2,c_2,c_26553])).

tff(c_26657,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_24913,c_26655])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:10:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 12.62/5.34  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 12.62/5.35  
% 12.62/5.35  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 12.72/5.35  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k9_subset_1 > k7_subset_1 > k6_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > #nlpp > k1_zfmisc_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 12.72/5.35  
% 12.72/5.35  %Foreground sorts:
% 12.72/5.35  
% 12.72/5.35  
% 12.72/5.35  %Background operators:
% 12.72/5.35  
% 12.72/5.35  
% 12.72/5.35  %Foreground operators:
% 12.72/5.35  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 12.72/5.35  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 12.72/5.35  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 12.72/5.35  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 12.72/5.35  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 12.72/5.35  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 12.72/5.35  tff('#skF_5', type, '#skF_5': $i).
% 12.72/5.35  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 12.72/5.35  tff(k6_subset_1, type, k6_subset_1: ($i * $i) > $i).
% 12.72/5.35  tff('#skF_3', type, '#skF_3': $i).
% 12.72/5.35  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 12.72/5.35  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 12.72/5.35  tff('#skF_4', type, '#skF_4': $i).
% 12.72/5.35  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 12.72/5.35  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 12.72/5.35  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 12.72/5.35  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 12.72/5.35  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 12.72/5.35  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 12.72/5.35  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 12.72/5.35  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 12.72/5.35  
% 12.72/5.37  tff(f_88, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k9_subset_1(A, B, k3_subset_1(A, C))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t32_subset_1)).
% 12.72/5.37  tff(f_65, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 12.72/5.37  tff(f_72, axiom, (![A, B]: (k6_subset_1(A, B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 12.72/5.37  tff(f_67, axiom, (![A, B]: m1_subset_1(k6_subset_1(A, B), k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_subset_1)).
% 12.72/5.37  tff(f_80, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 12.72/5.37  tff(f_76, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 12.72/5.37  tff(f_70, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_subset_1)).
% 12.72/5.37  tff(f_61, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 12.72/5.37  tff(f_48, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 12.72/5.37  tff(f_33, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 12.72/5.37  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 12.72/5.37  tff(f_39, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 12.72/5.37  tff(f_35, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 12.72/5.37  tff(f_37, axiom, (![A, B, C]: (k4_xboole_0(k4_xboole_0(A, B), C) = k4_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_xboole_1)).
% 12.72/5.37  tff(f_41, axiom, (![A, B, C]: (k4_xboole_0(A, k2_xboole_0(B, C)) = k3_xboole_0(k4_xboole_0(A, B), k4_xboole_0(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t53_xboole_1)).
% 12.72/5.37  tff(c_50, plain, (m1_subset_1('#skF_5', k1_zfmisc_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_88])).
% 12.72/5.37  tff(c_271, plain, (![A_77, B_78]: (k4_xboole_0(A_77, B_78)=k3_subset_1(A_77, B_78) | ~m1_subset_1(B_78, k1_zfmisc_1(A_77)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 12.72/5.37  tff(c_301, plain, (k4_xboole_0('#skF_3', '#skF_5')=k3_subset_1('#skF_3', '#skF_5')), inference(resolution, [status(thm)], [c_50, c_271])).
% 12.72/5.37  tff(c_42, plain, (![A_29, B_30]: (k6_subset_1(A_29, B_30)=k4_xboole_0(A_29, B_30))), inference(cnfTransformation, [status(thm)], [f_72])).
% 12.72/5.37  tff(c_38, plain, (![A_26, B_27]: (m1_subset_1(k6_subset_1(A_26, B_27), k1_zfmisc_1(A_26)))), inference(cnfTransformation, [status(thm)], [f_67])).
% 12.72/5.37  tff(c_53, plain, (![A_26, B_27]: (m1_subset_1(k4_xboole_0(A_26, B_27), k1_zfmisc_1(A_26)))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_38])).
% 12.72/5.37  tff(c_686, plain, (![A_86, B_87, C_88]: (k9_subset_1(A_86, B_87, C_88)=k3_xboole_0(B_87, C_88) | ~m1_subset_1(C_88, k1_zfmisc_1(A_86)))), inference(cnfTransformation, [status(thm)], [f_80])).
% 12.72/5.37  tff(c_3612, plain, (![A_154, B_155, B_156]: (k9_subset_1(A_154, B_155, k4_xboole_0(A_154, B_156))=k3_xboole_0(B_155, k4_xboole_0(A_154, B_156)))), inference(resolution, [status(thm)], [c_53, c_686])).
% 12.72/5.37  tff(c_3654, plain, (![B_155]: (k9_subset_1('#skF_3', B_155, k3_subset_1('#skF_3', '#skF_5'))=k3_xboole_0(B_155, k4_xboole_0('#skF_3', '#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_301, c_3612])).
% 12.72/5.37  tff(c_3677, plain, (![B_155]: (k9_subset_1('#skF_3', B_155, k3_subset_1('#skF_3', '#skF_5'))=k3_xboole_0(B_155, k3_subset_1('#skF_3', '#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_301, c_3654])).
% 12.72/5.37  tff(c_52, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_88])).
% 12.72/5.37  tff(c_547, plain, (![A_82, B_83, C_84]: (k7_subset_1(A_82, B_83, C_84)=k4_xboole_0(B_83, C_84) | ~m1_subset_1(B_83, k1_zfmisc_1(A_82)))), inference(cnfTransformation, [status(thm)], [f_76])).
% 12.72/5.37  tff(c_575, plain, (![C_84]: (k7_subset_1('#skF_3', '#skF_4', C_84)=k4_xboole_0('#skF_4', C_84))), inference(resolution, [status(thm)], [c_52, c_547])).
% 12.72/5.37  tff(c_48, plain, (k9_subset_1('#skF_3', '#skF_4', k3_subset_1('#skF_3', '#skF_5'))!=k7_subset_1('#skF_3', '#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_88])).
% 12.72/5.37  tff(c_613, plain, (k9_subset_1('#skF_3', '#skF_4', k3_subset_1('#skF_3', '#skF_5'))!=k4_xboole_0('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_575, c_48])).
% 12.72/5.37  tff(c_24913, plain, (k3_xboole_0('#skF_4', k3_subset_1('#skF_3', '#skF_5'))!=k4_xboole_0('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_3677, c_613])).
% 12.72/5.37  tff(c_40, plain, (![A_28]: (~v1_xboole_0(k1_zfmisc_1(A_28)))), inference(cnfTransformation, [status(thm)], [f_70])).
% 12.72/5.37  tff(c_143, plain, (![B_59, A_60]: (r2_hidden(B_59, A_60) | ~m1_subset_1(B_59, A_60) | v1_xboole_0(A_60))), inference(cnfTransformation, [status(thm)], [f_61])).
% 12.72/5.37  tff(c_16, plain, (![C_21, A_17]: (r1_tarski(C_21, A_17) | ~r2_hidden(C_21, k1_zfmisc_1(A_17)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 12.72/5.37  tff(c_147, plain, (![B_59, A_17]: (r1_tarski(B_59, A_17) | ~m1_subset_1(B_59, k1_zfmisc_1(A_17)) | v1_xboole_0(k1_zfmisc_1(A_17)))), inference(resolution, [status(thm)], [c_143, c_16])).
% 12.72/5.37  tff(c_238, plain, (![B_75, A_76]: (r1_tarski(B_75, A_76) | ~m1_subset_1(B_75, k1_zfmisc_1(A_76)))), inference(negUnitSimplification, [status(thm)], [c_40, c_147])).
% 12.72/5.37  tff(c_269, plain, (r1_tarski('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_52, c_238])).
% 12.72/5.37  tff(c_6, plain, (![A_5, B_6]: (k3_xboole_0(A_5, B_6)=A_5 | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_33])).
% 12.72/5.37  tff(c_305, plain, (k3_xboole_0('#skF_4', '#skF_3')='#skF_4'), inference(resolution, [status(thm)], [c_269, c_6])).
% 12.72/5.37  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 12.72/5.37  tff(c_151, plain, (![A_61, B_62]: (k4_xboole_0(A_61, k4_xboole_0(A_61, B_62))=k3_xboole_0(A_61, B_62))), inference(cnfTransformation, [status(thm)], [f_39])).
% 12.72/5.37  tff(c_8, plain, (![A_7, B_8]: (r1_tarski(k4_xboole_0(A_7, B_8), A_7))), inference(cnfTransformation, [status(thm)], [f_35])).
% 12.72/5.37  tff(c_163, plain, (![A_61, B_62]: (r1_tarski(k3_xboole_0(A_61, B_62), A_61))), inference(superposition, [status(thm), theory('equality')], [c_151, c_8])).
% 12.72/5.37  tff(c_322, plain, (r1_tarski('#skF_4', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_305, c_163])).
% 12.72/5.37  tff(c_348, plain, (k3_xboole_0('#skF_4', '#skF_4')='#skF_4'), inference(resolution, [status(thm)], [c_322, c_6])).
% 12.72/5.37  tff(c_172, plain, (![A_63, B_64]: (r1_tarski(k3_xboole_0(A_63, B_64), A_63))), inference(superposition, [status(thm), theory('equality')], [c_151, c_8])).
% 12.72/5.37  tff(c_183, plain, (![B_65, A_66]: (r1_tarski(k3_xboole_0(B_65, A_66), A_66))), inference(superposition, [status(thm), theory('equality')], [c_2, c_172])).
% 12.72/5.37  tff(c_3406, plain, (![B_151, A_152]: (k3_xboole_0(k3_xboole_0(B_151, A_152), A_152)=k3_xboole_0(B_151, A_152))), inference(resolution, [status(thm)], [c_183, c_6])).
% 12.72/5.37  tff(c_17294, plain, (![A_347, B_348]: (k3_xboole_0(k3_xboole_0(A_347, B_348), A_347)=k3_xboole_0(B_348, A_347))), inference(superposition, [status(thm), theory('equality')], [c_2, c_3406])).
% 12.72/5.37  tff(c_17708, plain, (k3_xboole_0('#skF_3', '#skF_4')=k3_xboole_0('#skF_4', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_305, c_17294])).
% 12.72/5.37  tff(c_17829, plain, (k3_xboole_0('#skF_3', '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_348, c_17708])).
% 12.72/5.37  tff(c_12, plain, (![A_12, B_13]: (k4_xboole_0(A_12, k4_xboole_0(A_12, B_13))=k3_xboole_0(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_39])).
% 12.72/5.37  tff(c_409, plain, (![A_79, B_80, C_81]: (k4_xboole_0(k4_xboole_0(A_79, B_80), C_81)=k4_xboole_0(A_79, k2_xboole_0(B_80, C_81)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 12.72/5.37  tff(c_440, plain, (![A_12, B_13, C_81]: (k4_xboole_0(A_12, k2_xboole_0(k4_xboole_0(A_12, B_13), C_81))=k4_xboole_0(k3_xboole_0(A_12, B_13), C_81))), inference(superposition, [status(thm), theory('equality')], [c_12, c_409])).
% 12.72/5.37  tff(c_836, plain, (![A_90, B_91, C_92]: (k3_xboole_0(k4_xboole_0(A_90, B_91), k4_xboole_0(A_90, C_92))=k4_xboole_0(A_90, k2_xboole_0(B_91, C_92)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 12.72/5.37  tff(c_920, plain, (![A_12, B_13, C_92]: (k4_xboole_0(A_12, k2_xboole_0(k4_xboole_0(A_12, B_13), C_92))=k3_xboole_0(k3_xboole_0(A_12, B_13), k4_xboole_0(A_12, C_92)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_836])).
% 12.72/5.37  tff(c_6600, plain, (![A_213, B_214, C_215]: (k3_xboole_0(k3_xboole_0(A_213, B_214), k4_xboole_0(A_213, C_215))=k4_xboole_0(k3_xboole_0(A_213, B_214), C_215))), inference(demodulation, [status(thm), theory('equality')], [c_440, c_920])).
% 12.72/5.37  tff(c_25310, plain, (![A_397, C_398, B_399]: (k3_xboole_0(k4_xboole_0(A_397, C_398), k3_xboole_0(A_397, B_399))=k4_xboole_0(k3_xboole_0(A_397, B_399), C_398))), inference(superposition, [status(thm), theory('equality')], [c_6600, c_2])).
% 12.72/5.37  tff(c_26372, plain, (![B_402]: (k3_xboole_0(k3_subset_1('#skF_3', '#skF_5'), k3_xboole_0('#skF_3', B_402))=k4_xboole_0(k3_xboole_0('#skF_3', B_402), '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_301, c_25310])).
% 12.72/5.37  tff(c_26553, plain, (k4_xboole_0(k3_xboole_0('#skF_3', '#skF_4'), '#skF_5')=k3_xboole_0(k3_subset_1('#skF_3', '#skF_5'), '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_17829, c_26372])).
% 12.72/5.37  tff(c_26655, plain, (k3_xboole_0('#skF_4', k3_subset_1('#skF_3', '#skF_5'))=k4_xboole_0('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_305, c_2, c_2, c_26553])).
% 12.72/5.37  tff(c_26657, plain, $false, inference(negUnitSimplification, [status(thm)], [c_24913, c_26655])).
% 12.72/5.37  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 12.72/5.37  
% 12.72/5.37  Inference rules
% 12.72/5.37  ----------------------
% 12.72/5.37  #Ref     : 0
% 12.72/5.37  #Sup     : 6718
% 12.72/5.37  #Fact    : 0
% 12.72/5.37  #Define  : 0
% 12.72/5.37  #Split   : 0
% 12.72/5.37  #Chain   : 0
% 12.72/5.37  #Close   : 0
% 12.72/5.37  
% 12.72/5.37  Ordering : KBO
% 12.72/5.37  
% 12.72/5.37  Simplification rules
% 12.72/5.37  ----------------------
% 12.72/5.37  #Subsume      : 96
% 12.72/5.37  #Demod        : 6870
% 12.72/5.37  #Tautology    : 3547
% 12.72/5.37  #SimpNegUnit  : 10
% 12.72/5.37  #BackRed      : 9
% 12.72/5.37  
% 12.72/5.37  #Partial instantiations: 0
% 12.72/5.37  #Strategies tried      : 1
% 12.72/5.37  
% 12.72/5.37  Timing (in seconds)
% 12.72/5.37  ----------------------
% 12.72/5.37  Preprocessing        : 0.31
% 12.72/5.37  Parsing              : 0.16
% 12.72/5.37  CNF conversion       : 0.02
% 12.72/5.37  Main loop            : 4.26
% 12.72/5.37  Inferencing          : 0.71
% 12.72/5.37  Reduction            : 2.44
% 12.72/5.37  Demodulation         : 2.14
% 12.72/5.37  BG Simplification    : 0.10
% 12.72/5.37  Subsumption          : 0.77
% 12.72/5.37  Abstraction          : 0.16
% 12.72/5.37  MUC search           : 0.00
% 12.72/5.37  Cooper               : 0.00
% 12.72/5.37  Total                : 4.60
% 12.72/5.37  Index Insertion      : 0.00
% 12.72/5.37  Index Deletion       : 0.00
% 12.72/5.37  Index Matching       : 0.00
% 12.72/5.37  BG Taut test         : 0.00
%------------------------------------------------------------------------------
