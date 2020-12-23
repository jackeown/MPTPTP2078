%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:55:55 EST 2020

% Result     : Theorem 4.85s
% Output     : CNFRefutation 4.85s
% Verified   : 
% Statistics : Number of formulae       :   68 ( 114 expanded)
%              Number of leaves         :   26 (  49 expanded)
%              Depth                    :    9
%              Number of atoms          :   74 ( 165 expanded)
%              Number of equality atoms :   38 (  64 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m1_subset_1 > k7_subset_1 > k4_subset_1 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff(k4_subset_1,type,(
    k4_subset_1: ( $i * $i * $i ) > $i )).

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

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_67,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => ! [C] :
            ( m1_subset_1(C,k1_zfmisc_1(A))
           => k3_subset_1(A,k7_subset_1(A,B,C)) = k4_subset_1(A,k3_subset_1(A,B),C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t33_subset_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_29,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,k3_subset_1(A,B)) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k3_subset_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).

tff(f_59,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k7_subset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_subset_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_31,axiom,(
    ! [A,B,C] : k4_xboole_0(A,k4_xboole_0(B,C)) = k2_xboole_0(k4_xboole_0(A,B),k3_xboole_0(A,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_xboole_1)).

tff(f_55,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(c_24,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_111,plain,(
    ! [A_36,B_37] :
      ( k4_xboole_0(A_36,B_37) = k3_subset_1(A_36,B_37)
      | ~ m1_subset_1(B_37,k1_zfmisc_1(A_36)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_122,plain,(
    k4_xboole_0('#skF_1','#skF_3') = k3_subset_1('#skF_1','#skF_3') ),
    inference(resolution,[status(thm)],[c_24,c_111])).

tff(c_4,plain,(
    ! [A_3,B_4] : k4_xboole_0(A_3,k4_xboole_0(A_3,B_4)) = k3_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_127,plain,(
    k4_xboole_0('#skF_1',k3_subset_1('#skF_1','#skF_3')) = k3_xboole_0('#skF_1','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_122,c_4])).

tff(c_85,plain,(
    ! [A_34,B_35] :
      ( k3_subset_1(A_34,k3_subset_1(A_34,B_35)) = B_35
      | ~ m1_subset_1(B_35,k1_zfmisc_1(A_34)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_93,plain,(
    k3_subset_1('#skF_1',k3_subset_1('#skF_1','#skF_3')) = '#skF_3' ),
    inference(resolution,[status(thm)],[c_24,c_85])).

tff(c_12,plain,(
    ! [A_12,B_13] :
      ( m1_subset_1(k3_subset_1(A_12,B_13),k1_zfmisc_1(A_12))
      | ~ m1_subset_1(B_13,k1_zfmisc_1(A_12)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_1509,plain,(
    ! [A_111,B_112] :
      ( k4_xboole_0(A_111,k3_subset_1(A_111,B_112)) = k3_subset_1(A_111,k3_subset_1(A_111,B_112))
      | ~ m1_subset_1(B_112,k1_zfmisc_1(A_111)) ) ),
    inference(resolution,[status(thm)],[c_12,c_111])).

tff(c_1539,plain,(
    k4_xboole_0('#skF_1',k3_subset_1('#skF_1','#skF_3')) = k3_subset_1('#skF_1',k3_subset_1('#skF_1','#skF_3')) ),
    inference(resolution,[status(thm)],[c_24,c_1509])).

tff(c_1561,plain,(
    k3_xboole_0('#skF_1','#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_127,c_93,c_1539])).

tff(c_26,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_203,plain,(
    ! [A_43,B_44,C_45] :
      ( k7_subset_1(A_43,B_44,C_45) = k4_xboole_0(B_44,C_45)
      | ~ m1_subset_1(B_44,k1_zfmisc_1(A_43)) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_261,plain,(
    ! [C_49] : k7_subset_1('#skF_1','#skF_2',C_49) = k4_xboole_0('#skF_2',C_49) ),
    inference(resolution,[status(thm)],[c_26,c_203])).

tff(c_14,plain,(
    ! [A_14,B_15,C_16] :
      ( m1_subset_1(k7_subset_1(A_14,B_15,C_16),k1_zfmisc_1(A_14))
      | ~ m1_subset_1(B_15,k1_zfmisc_1(A_14)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_267,plain,(
    ! [C_49] :
      ( m1_subset_1(k4_xboole_0('#skF_2',C_49),k1_zfmisc_1('#skF_1'))
      | ~ m1_subset_1('#skF_2',k1_zfmisc_1('#skF_1')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_261,c_14])).

tff(c_320,plain,(
    ! [C_53] : m1_subset_1(k4_xboole_0('#skF_2',C_53),k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_267])).

tff(c_10,plain,(
    ! [A_10,B_11] :
      ( k4_xboole_0(A_10,B_11) = k3_subset_1(A_10,B_11)
      | ~ m1_subset_1(B_11,k1_zfmisc_1(A_10)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_337,plain,(
    ! [C_53] : k4_xboole_0('#skF_1',k4_xboole_0('#skF_2',C_53)) = k3_subset_1('#skF_1',k4_xboole_0('#skF_2',C_53)) ),
    inference(resolution,[status(thm)],[c_320,c_10])).

tff(c_123,plain,(
    k4_xboole_0('#skF_1','#skF_2') = k3_subset_1('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_26,c_111])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_275,plain,(
    ! [A_50,B_51,C_52] : k2_xboole_0(k4_xboole_0(A_50,B_51),k3_xboole_0(A_50,C_52)) = k4_xboole_0(A_50,k4_xboole_0(B_51,C_52)) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_714,plain,(
    ! [A_73,C_74,B_75] : k2_xboole_0(k3_xboole_0(A_73,C_74),k4_xboole_0(A_73,B_75)) = k4_xboole_0(A_73,k4_xboole_0(B_75,C_74)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_275])).

tff(c_756,plain,(
    ! [C_74] : k2_xboole_0(k3_xboole_0('#skF_1',C_74),k3_subset_1('#skF_1','#skF_2')) = k4_xboole_0('#skF_1',k4_xboole_0('#skF_2',C_74)) ),
    inference(superposition,[status(thm),theory(equality)],[c_123,c_714])).

tff(c_773,plain,(
    ! [C_74] : k2_xboole_0(k3_xboole_0('#skF_1',C_74),k3_subset_1('#skF_1','#skF_2')) = k3_subset_1('#skF_1',k4_xboole_0('#skF_2',C_74)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_337,c_756])).

tff(c_1574,plain,(
    k3_subset_1('#skF_1',k4_xboole_0('#skF_2','#skF_3')) = k2_xboole_0('#skF_3',k3_subset_1('#skF_1','#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1561,c_773])).

tff(c_215,plain,(
    ! [C_45] : k7_subset_1('#skF_1','#skF_2',C_45) = k4_xboole_0('#skF_2',C_45) ),
    inference(resolution,[status(thm)],[c_26,c_203])).

tff(c_22,plain,(
    k4_subset_1('#skF_1',k3_subset_1('#skF_1','#skF_2'),'#skF_3') != k3_subset_1('#skF_1',k7_subset_1('#skF_1','#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_260,plain,(
    k4_subset_1('#skF_1',k3_subset_1('#skF_1','#skF_2'),'#skF_3') != k3_subset_1('#skF_1',k4_xboole_0('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_215,c_22])).

tff(c_2531,plain,(
    k4_subset_1('#skF_1',k3_subset_1('#skF_1','#skF_2'),'#skF_3') != k2_xboole_0('#skF_3',k3_subset_1('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1574,c_260])).

tff(c_2391,plain,(
    ! [A_128,B_129,C_130] :
      ( k7_subset_1(A_128,k3_subset_1(A_128,B_129),C_130) = k4_xboole_0(k3_subset_1(A_128,B_129),C_130)
      | ~ m1_subset_1(B_129,k1_zfmisc_1(A_128)) ) ),
    inference(resolution,[status(thm)],[c_12,c_203])).

tff(c_2748,plain,(
    ! [C_137] : k7_subset_1('#skF_1',k3_subset_1('#skF_1','#skF_2'),C_137) = k4_xboole_0(k3_subset_1('#skF_1','#skF_2'),C_137) ),
    inference(resolution,[status(thm)],[c_26,c_2391])).

tff(c_2757,plain,(
    ! [C_137] :
      ( m1_subset_1(k4_xboole_0(k3_subset_1('#skF_1','#skF_2'),C_137),k1_zfmisc_1('#skF_1'))
      | ~ m1_subset_1(k3_subset_1('#skF_1','#skF_2'),k1_zfmisc_1('#skF_1')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2748,c_14])).

tff(c_3070,plain,(
    ~ m1_subset_1(k3_subset_1('#skF_1','#skF_2'),k1_zfmisc_1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_2757])).

tff(c_3073,plain,(
    ~ m1_subset_1('#skF_2',k1_zfmisc_1('#skF_1')) ),
    inference(resolution,[status(thm)],[c_12,c_3070])).

tff(c_3077,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_3073])).

tff(c_3079,plain,(
    m1_subset_1(k3_subset_1('#skF_1','#skF_2'),k1_zfmisc_1('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_2757])).

tff(c_448,plain,(
    ! [A_59,B_60,C_61] :
      ( k4_subset_1(A_59,B_60,C_61) = k2_xboole_0(B_60,C_61)
      | ~ m1_subset_1(C_61,k1_zfmisc_1(A_59))
      | ~ m1_subset_1(B_60,k1_zfmisc_1(A_59)) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_471,plain,(
    ! [B_60] :
      ( k4_subset_1('#skF_1',B_60,'#skF_3') = k2_xboole_0(B_60,'#skF_3')
      | ~ m1_subset_1(B_60,k1_zfmisc_1('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_24,c_448])).

tff(c_3093,plain,(
    k4_subset_1('#skF_1',k3_subset_1('#skF_1','#skF_2'),'#skF_3') = k2_xboole_0(k3_subset_1('#skF_1','#skF_2'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_3079,c_471])).

tff(c_3114,plain,(
    k4_subset_1('#skF_1',k3_subset_1('#skF_1','#skF_2'),'#skF_3') = k2_xboole_0('#skF_3',k3_subset_1('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_3093])).

tff(c_3116,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2531,c_3114])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:52:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.85/2.03  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.85/2.03  
% 4.85/2.03  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.85/2.04  %$ m1_subset_1 > k7_subset_1 > k4_subset_1 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1
% 4.85/2.04  
% 4.85/2.04  %Foreground sorts:
% 4.85/2.04  
% 4.85/2.04  
% 4.85/2.04  %Background operators:
% 4.85/2.04  
% 4.85/2.04  
% 4.85/2.04  %Foreground operators:
% 4.85/2.04  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.85/2.04  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.85/2.04  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.85/2.04  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 4.85/2.04  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 4.85/2.04  tff('#skF_2', type, '#skF_2': $i).
% 4.85/2.04  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 4.85/2.04  tff('#skF_3', type, '#skF_3': $i).
% 4.85/2.04  tff('#skF_1', type, '#skF_1': $i).
% 4.85/2.04  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.85/2.04  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.85/2.04  tff(k3_tarski, type, k3_tarski: $i > $i).
% 4.85/2.04  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.85/2.04  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.85/2.04  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.85/2.04  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.85/2.04  
% 4.85/2.05  tff(f_67, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k3_subset_1(A, k7_subset_1(A, B, C)) = k4_subset_1(A, k3_subset_1(A, B), C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t33_subset_1)).
% 4.85/2.05  tff(f_37, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 4.85/2.05  tff(f_29, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 4.85/2.05  tff(f_49, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, k3_subset_1(A, B)) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 4.85/2.05  tff(f_41, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k3_subset_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 4.85/2.05  tff(f_59, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 4.85/2.05  tff(f_45, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k7_subset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_subset_1)).
% 4.85/2.05  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 4.85/2.05  tff(f_31, axiom, (![A, B, C]: (k4_xboole_0(A, k4_xboole_0(B, C)) = k2_xboole_0(k4_xboole_0(A, B), k3_xboole_0(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_xboole_1)).
% 4.85/2.05  tff(f_55, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 4.85/2.05  tff(c_24, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_67])).
% 4.85/2.05  tff(c_111, plain, (![A_36, B_37]: (k4_xboole_0(A_36, B_37)=k3_subset_1(A_36, B_37) | ~m1_subset_1(B_37, k1_zfmisc_1(A_36)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.85/2.05  tff(c_122, plain, (k4_xboole_0('#skF_1', '#skF_3')=k3_subset_1('#skF_1', '#skF_3')), inference(resolution, [status(thm)], [c_24, c_111])).
% 4.85/2.05  tff(c_4, plain, (![A_3, B_4]: (k4_xboole_0(A_3, k4_xboole_0(A_3, B_4))=k3_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 4.85/2.05  tff(c_127, plain, (k4_xboole_0('#skF_1', k3_subset_1('#skF_1', '#skF_3'))=k3_xboole_0('#skF_1', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_122, c_4])).
% 4.85/2.05  tff(c_85, plain, (![A_34, B_35]: (k3_subset_1(A_34, k3_subset_1(A_34, B_35))=B_35 | ~m1_subset_1(B_35, k1_zfmisc_1(A_34)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 4.85/2.05  tff(c_93, plain, (k3_subset_1('#skF_1', k3_subset_1('#skF_1', '#skF_3'))='#skF_3'), inference(resolution, [status(thm)], [c_24, c_85])).
% 4.85/2.05  tff(c_12, plain, (![A_12, B_13]: (m1_subset_1(k3_subset_1(A_12, B_13), k1_zfmisc_1(A_12)) | ~m1_subset_1(B_13, k1_zfmisc_1(A_12)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.85/2.05  tff(c_1509, plain, (![A_111, B_112]: (k4_xboole_0(A_111, k3_subset_1(A_111, B_112))=k3_subset_1(A_111, k3_subset_1(A_111, B_112)) | ~m1_subset_1(B_112, k1_zfmisc_1(A_111)))), inference(resolution, [status(thm)], [c_12, c_111])).
% 4.85/2.05  tff(c_1539, plain, (k4_xboole_0('#skF_1', k3_subset_1('#skF_1', '#skF_3'))=k3_subset_1('#skF_1', k3_subset_1('#skF_1', '#skF_3'))), inference(resolution, [status(thm)], [c_24, c_1509])).
% 4.85/2.05  tff(c_1561, plain, (k3_xboole_0('#skF_1', '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_127, c_93, c_1539])).
% 4.85/2.05  tff(c_26, plain, (m1_subset_1('#skF_2', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_67])).
% 4.85/2.05  tff(c_203, plain, (![A_43, B_44, C_45]: (k7_subset_1(A_43, B_44, C_45)=k4_xboole_0(B_44, C_45) | ~m1_subset_1(B_44, k1_zfmisc_1(A_43)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 4.85/2.05  tff(c_261, plain, (![C_49]: (k7_subset_1('#skF_1', '#skF_2', C_49)=k4_xboole_0('#skF_2', C_49))), inference(resolution, [status(thm)], [c_26, c_203])).
% 4.85/2.05  tff(c_14, plain, (![A_14, B_15, C_16]: (m1_subset_1(k7_subset_1(A_14, B_15, C_16), k1_zfmisc_1(A_14)) | ~m1_subset_1(B_15, k1_zfmisc_1(A_14)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 4.85/2.05  tff(c_267, plain, (![C_49]: (m1_subset_1(k4_xboole_0('#skF_2', C_49), k1_zfmisc_1('#skF_1')) | ~m1_subset_1('#skF_2', k1_zfmisc_1('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_261, c_14])).
% 4.85/2.05  tff(c_320, plain, (![C_53]: (m1_subset_1(k4_xboole_0('#skF_2', C_53), k1_zfmisc_1('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_267])).
% 4.85/2.05  tff(c_10, plain, (![A_10, B_11]: (k4_xboole_0(A_10, B_11)=k3_subset_1(A_10, B_11) | ~m1_subset_1(B_11, k1_zfmisc_1(A_10)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.85/2.05  tff(c_337, plain, (![C_53]: (k4_xboole_0('#skF_1', k4_xboole_0('#skF_2', C_53))=k3_subset_1('#skF_1', k4_xboole_0('#skF_2', C_53)))), inference(resolution, [status(thm)], [c_320, c_10])).
% 4.85/2.05  tff(c_123, plain, (k4_xboole_0('#skF_1', '#skF_2')=k3_subset_1('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_26, c_111])).
% 4.85/2.05  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.85/2.05  tff(c_275, plain, (![A_50, B_51, C_52]: (k2_xboole_0(k4_xboole_0(A_50, B_51), k3_xboole_0(A_50, C_52))=k4_xboole_0(A_50, k4_xboole_0(B_51, C_52)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.85/2.05  tff(c_714, plain, (![A_73, C_74, B_75]: (k2_xboole_0(k3_xboole_0(A_73, C_74), k4_xboole_0(A_73, B_75))=k4_xboole_0(A_73, k4_xboole_0(B_75, C_74)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_275])).
% 4.85/2.05  tff(c_756, plain, (![C_74]: (k2_xboole_0(k3_xboole_0('#skF_1', C_74), k3_subset_1('#skF_1', '#skF_2'))=k4_xboole_0('#skF_1', k4_xboole_0('#skF_2', C_74)))), inference(superposition, [status(thm), theory('equality')], [c_123, c_714])).
% 4.85/2.05  tff(c_773, plain, (![C_74]: (k2_xboole_0(k3_xboole_0('#skF_1', C_74), k3_subset_1('#skF_1', '#skF_2'))=k3_subset_1('#skF_1', k4_xboole_0('#skF_2', C_74)))), inference(demodulation, [status(thm), theory('equality')], [c_337, c_756])).
% 4.85/2.05  tff(c_1574, plain, (k3_subset_1('#skF_1', k4_xboole_0('#skF_2', '#skF_3'))=k2_xboole_0('#skF_3', k3_subset_1('#skF_1', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_1561, c_773])).
% 4.85/2.05  tff(c_215, plain, (![C_45]: (k7_subset_1('#skF_1', '#skF_2', C_45)=k4_xboole_0('#skF_2', C_45))), inference(resolution, [status(thm)], [c_26, c_203])).
% 4.85/2.05  tff(c_22, plain, (k4_subset_1('#skF_1', k3_subset_1('#skF_1', '#skF_2'), '#skF_3')!=k3_subset_1('#skF_1', k7_subset_1('#skF_1', '#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_67])).
% 4.85/2.05  tff(c_260, plain, (k4_subset_1('#skF_1', k3_subset_1('#skF_1', '#skF_2'), '#skF_3')!=k3_subset_1('#skF_1', k4_xboole_0('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_215, c_22])).
% 4.85/2.05  tff(c_2531, plain, (k4_subset_1('#skF_1', k3_subset_1('#skF_1', '#skF_2'), '#skF_3')!=k2_xboole_0('#skF_3', k3_subset_1('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_1574, c_260])).
% 4.85/2.05  tff(c_2391, plain, (![A_128, B_129, C_130]: (k7_subset_1(A_128, k3_subset_1(A_128, B_129), C_130)=k4_xboole_0(k3_subset_1(A_128, B_129), C_130) | ~m1_subset_1(B_129, k1_zfmisc_1(A_128)))), inference(resolution, [status(thm)], [c_12, c_203])).
% 4.85/2.05  tff(c_2748, plain, (![C_137]: (k7_subset_1('#skF_1', k3_subset_1('#skF_1', '#skF_2'), C_137)=k4_xboole_0(k3_subset_1('#skF_1', '#skF_2'), C_137))), inference(resolution, [status(thm)], [c_26, c_2391])).
% 4.85/2.05  tff(c_2757, plain, (![C_137]: (m1_subset_1(k4_xboole_0(k3_subset_1('#skF_1', '#skF_2'), C_137), k1_zfmisc_1('#skF_1')) | ~m1_subset_1(k3_subset_1('#skF_1', '#skF_2'), k1_zfmisc_1('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_2748, c_14])).
% 4.85/2.05  tff(c_3070, plain, (~m1_subset_1(k3_subset_1('#skF_1', '#skF_2'), k1_zfmisc_1('#skF_1'))), inference(splitLeft, [status(thm)], [c_2757])).
% 4.85/2.05  tff(c_3073, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1('#skF_1'))), inference(resolution, [status(thm)], [c_12, c_3070])).
% 4.85/2.05  tff(c_3077, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_26, c_3073])).
% 4.85/2.05  tff(c_3079, plain, (m1_subset_1(k3_subset_1('#skF_1', '#skF_2'), k1_zfmisc_1('#skF_1'))), inference(splitRight, [status(thm)], [c_2757])).
% 4.85/2.05  tff(c_448, plain, (![A_59, B_60, C_61]: (k4_subset_1(A_59, B_60, C_61)=k2_xboole_0(B_60, C_61) | ~m1_subset_1(C_61, k1_zfmisc_1(A_59)) | ~m1_subset_1(B_60, k1_zfmisc_1(A_59)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 4.85/2.05  tff(c_471, plain, (![B_60]: (k4_subset_1('#skF_1', B_60, '#skF_3')=k2_xboole_0(B_60, '#skF_3') | ~m1_subset_1(B_60, k1_zfmisc_1('#skF_1')))), inference(resolution, [status(thm)], [c_24, c_448])).
% 4.85/2.05  tff(c_3093, plain, (k4_subset_1('#skF_1', k3_subset_1('#skF_1', '#skF_2'), '#skF_3')=k2_xboole_0(k3_subset_1('#skF_1', '#skF_2'), '#skF_3')), inference(resolution, [status(thm)], [c_3079, c_471])).
% 4.85/2.05  tff(c_3114, plain, (k4_subset_1('#skF_1', k3_subset_1('#skF_1', '#skF_2'), '#skF_3')=k2_xboole_0('#skF_3', k3_subset_1('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_3093])).
% 4.85/2.05  tff(c_3116, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2531, c_3114])).
% 4.85/2.05  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.85/2.05  
% 4.85/2.05  Inference rules
% 4.85/2.05  ----------------------
% 4.85/2.05  #Ref     : 0
% 4.85/2.05  #Sup     : 797
% 4.85/2.05  #Fact    : 0
% 4.85/2.05  #Define  : 0
% 4.85/2.05  #Split   : 1
% 4.85/2.05  #Chain   : 0
% 4.85/2.05  #Close   : 0
% 4.85/2.05  
% 4.85/2.05  Ordering : KBO
% 4.85/2.05  
% 4.85/2.05  Simplification rules
% 4.85/2.05  ----------------------
% 4.85/2.05  #Subsume      : 6
% 4.85/2.05  #Demod        : 453
% 4.85/2.05  #Tautology    : 295
% 4.85/2.05  #SimpNegUnit  : 1
% 4.85/2.05  #BackRed      : 10
% 4.85/2.05  
% 4.85/2.05  #Partial instantiations: 0
% 4.85/2.05  #Strategies tried      : 1
% 4.85/2.05  
% 4.85/2.05  Timing (in seconds)
% 4.85/2.05  ----------------------
% 4.85/2.05  Preprocessing        : 0.30
% 4.85/2.05  Parsing              : 0.16
% 4.85/2.05  CNF conversion       : 0.02
% 4.85/2.06  Main loop            : 0.90
% 4.85/2.06  Inferencing          : 0.28
% 4.85/2.06  Reduction            : 0.36
% 4.85/2.06  Demodulation         : 0.29
% 4.85/2.06  BG Simplification    : 0.04
% 4.85/2.06  Subsumption          : 0.16
% 4.85/2.06  Abstraction          : 0.05
% 4.85/2.06  MUC search           : 0.00
% 4.85/2.06  Cooper               : 0.00
% 4.85/2.06  Total                : 1.23
% 4.85/2.06  Index Insertion      : 0.00
% 4.85/2.06  Index Deletion       : 0.00
% 4.85/2.06  Index Matching       : 0.00
% 4.85/2.06  BG Taut test         : 0.00
%------------------------------------------------------------------------------
