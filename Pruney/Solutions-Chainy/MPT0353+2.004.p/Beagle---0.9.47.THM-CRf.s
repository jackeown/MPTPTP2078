%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:55:52 EST 2020

% Result     : Theorem 4.87s
% Output     : CNFRefutation 4.87s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 165 expanded)
%              Number of leaves         :   26 (  65 expanded)
%              Depth                    :   13
%              Number of atoms          :   85 ( 229 expanded)
%              Number of equality atoms :   58 ( 118 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m1_subset_1 > k9_subset_1 > k7_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1

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

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_67,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => ! [C] :
            ( m1_subset_1(C,k1_zfmisc_1(A))
           => k7_subset_1(A,B,C) = k9_subset_1(A,B,k3_subset_1(A,C)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_subset_1)).

tff(f_59,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k9_subset_1(A,C,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k9_subset_1)).

tff(f_55,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,k3_subset_1(A,B)) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

tff(f_47,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => m1_subset_1(k9_subset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k9_subset_1)).

tff(f_31,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_35,axiom,(
    ! [A,B,C] : k3_xboole_0(k3_xboole_0(A,B),C) = k3_xboole_0(A,k3_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_xboole_1)).

tff(f_33,axiom,(
    ! [A,B,C] : k5_xboole_0(k3_xboole_0(A,B),k3_xboole_0(C,B)) = k3_xboole_0(k5_xboole_0(A,C),B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t112_xboole_1)).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_28,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_369,plain,(
    ! [A_51,B_52,C_53] :
      ( k9_subset_1(A_51,B_52,C_53) = k3_xboole_0(B_52,C_53)
      | ~ m1_subset_1(C_53,k1_zfmisc_1(A_51)) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_375,plain,(
    ! [B_52] : k9_subset_1('#skF_1',B_52,'#skF_2') = k3_xboole_0(B_52,'#skF_2') ),
    inference(resolution,[status(thm)],[c_28,c_369])).

tff(c_1915,plain,(
    ! [A_93,C_94,B_95] :
      ( k9_subset_1(A_93,C_94,B_95) = k9_subset_1(A_93,B_95,C_94)
      | ~ m1_subset_1(C_94,k1_zfmisc_1(A_93)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_1937,plain,(
    ! [B_95] : k9_subset_1('#skF_1',B_95,'#skF_2') = k9_subset_1('#skF_1','#skF_2',B_95) ),
    inference(resolution,[status(thm)],[c_28,c_1915])).

tff(c_1950,plain,(
    ! [B_95] : k9_subset_1('#skF_1','#skF_2',B_95) = k3_xboole_0(B_95,'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_375,c_1937])).

tff(c_436,plain,(
    ! [A_58,B_59,C_60] :
      ( k7_subset_1(A_58,B_59,C_60) = k4_xboole_0(B_59,C_60)
      | ~ m1_subset_1(B_59,k1_zfmisc_1(A_58)) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_442,plain,(
    ! [C_60] : k7_subset_1('#skF_1','#skF_2',C_60) = k4_xboole_0('#skF_2',C_60) ),
    inference(resolution,[status(thm)],[c_28,c_436])).

tff(c_24,plain,(
    k9_subset_1('#skF_1','#skF_2',k3_subset_1('#skF_1','#skF_3')) != k7_subset_1('#skF_1','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_452,plain,(
    k9_subset_1('#skF_1','#skF_2',k3_subset_1('#skF_1','#skF_3')) != k4_xboole_0('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_442,c_24])).

tff(c_1984,plain,(
    k3_xboole_0(k3_subset_1('#skF_1','#skF_3'),'#skF_2') != k4_xboole_0('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1950,c_452])).

tff(c_1985,plain,(
    k3_xboole_0('#skF_2',k3_subset_1('#skF_1','#skF_3')) != k4_xboole_0('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_1984])).

tff(c_26,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_89,plain,(
    ! [A_35,B_36] :
      ( k4_xboole_0(A_35,B_36) = k3_subset_1(A_35,B_36)
      | ~ m1_subset_1(B_36,k1_zfmisc_1(A_35)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_96,plain,(
    k4_xboole_0('#skF_1','#skF_3') = k3_subset_1('#skF_1','#skF_3') ),
    inference(resolution,[status(thm)],[c_26,c_89])).

tff(c_147,plain,(
    ! [A_40,B_41] :
      ( k3_subset_1(A_40,k3_subset_1(A_40,B_41)) = B_41
      | ~ m1_subset_1(B_41,k1_zfmisc_1(A_40)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_152,plain,(
    k3_subset_1('#skF_1',k3_subset_1('#skF_1','#skF_3')) = '#skF_3' ),
    inference(resolution,[status(thm)],[c_26,c_147])).

tff(c_374,plain,(
    ! [B_52] : k9_subset_1('#skF_1',B_52,'#skF_3') = k3_xboole_0(B_52,'#skF_3') ),
    inference(resolution,[status(thm)],[c_26,c_369])).

tff(c_973,plain,(
    ! [A_70,B_71,C_72] :
      ( m1_subset_1(k9_subset_1(A_70,B_71,C_72),k1_zfmisc_1(A_70))
      | ~ m1_subset_1(C_72,k1_zfmisc_1(A_70)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_988,plain,(
    ! [B_52] :
      ( m1_subset_1(k3_xboole_0(B_52,'#skF_3'),k1_zfmisc_1('#skF_1'))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1('#skF_1')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_374,c_973])).

tff(c_1028,plain,(
    ! [B_74] : m1_subset_1(k3_xboole_0(B_74,'#skF_3'),k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_988])).

tff(c_14,plain,(
    ! [A_16,B_17] :
      ( k4_xboole_0(A_16,B_17) = k3_subset_1(A_16,B_17)
      | ~ m1_subset_1(B_17,k1_zfmisc_1(A_16)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_2746,plain,(
    ! [B_108] : k4_xboole_0('#skF_1',k3_xboole_0(B_108,'#skF_3')) = k3_subset_1('#skF_1',k3_xboole_0(B_108,'#skF_3')) ),
    inference(resolution,[status(thm)],[c_1028,c_14])).

tff(c_6,plain,(
    ! [A_5,B_6] : k5_xboole_0(A_5,k3_xboole_0(A_5,B_6)) = k4_xboole_0(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_4,plain,(
    ! [A_3] : k3_xboole_0(A_3,A_3) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_162,plain,(
    ! [A_42,B_43,C_44] : k3_xboole_0(k3_xboole_0(A_42,B_43),C_44) = k3_xboole_0(A_42,k3_xboole_0(B_43,C_44)) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_216,plain,(
    ! [A_45,C_46] : k3_xboole_0(A_45,k3_xboole_0(A_45,C_46)) = k3_xboole_0(A_45,C_46) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_162])).

tff(c_235,plain,(
    ! [A_45,C_46] : k5_xboole_0(A_45,k3_xboole_0(A_45,C_46)) = k4_xboole_0(A_45,k3_xboole_0(A_45,C_46)) ),
    inference(superposition,[status(thm),theory(equality)],[c_216,c_6])).

tff(c_262,plain,(
    ! [A_45,C_46] : k4_xboole_0(A_45,k3_xboole_0(A_45,C_46)) = k4_xboole_0(A_45,C_46) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_235])).

tff(c_2756,plain,(
    k3_subset_1('#skF_1',k3_xboole_0('#skF_1','#skF_3')) = k4_xboole_0('#skF_1','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_2746,c_262])).

tff(c_2790,plain,(
    k3_subset_1('#skF_1',k3_xboole_0('#skF_1','#skF_3')) = k3_subset_1('#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_2756])).

tff(c_18,plain,(
    ! [A_21,B_22] :
      ( k3_subset_1(A_21,k3_subset_1(A_21,B_22)) = B_22
      | ~ m1_subset_1(B_22,k1_zfmisc_1(A_21)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_1056,plain,(
    ! [B_74] : k3_subset_1('#skF_1',k3_subset_1('#skF_1',k3_xboole_0(B_74,'#skF_3'))) = k3_xboole_0(B_74,'#skF_3') ),
    inference(resolution,[status(thm)],[c_1028,c_18])).

tff(c_2800,plain,(
    k3_subset_1('#skF_1',k3_subset_1('#skF_1','#skF_3')) = k3_xboole_0('#skF_1','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_2790,c_1056])).

tff(c_2803,plain,(
    k3_xboole_0('#skF_1','#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_152,c_2800])).

tff(c_2861,plain,(
    k5_xboole_0('#skF_1','#skF_3') = k4_xboole_0('#skF_1','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_2803,c_6])).

tff(c_2877,plain,(
    k5_xboole_0('#skF_1','#skF_3') = k3_subset_1('#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_2861])).

tff(c_71,plain,(
    ! [A_33,B_34] : k5_xboole_0(A_33,k3_xboole_0(A_33,B_34)) = k4_xboole_0(A_33,B_34) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_80,plain,(
    ! [A_1,B_2] : k5_xboole_0(A_1,k3_xboole_0(B_2,A_1)) = k4_xboole_0(A_1,B_2) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_71])).

tff(c_153,plain,(
    k3_subset_1('#skF_1',k3_subset_1('#skF_1','#skF_2')) = '#skF_2' ),
    inference(resolution,[status(thm)],[c_28,c_147])).

tff(c_97,plain,(
    k4_xboole_0('#skF_1','#skF_2') = k3_subset_1('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_28,c_89])).

tff(c_985,plain,(
    ! [B_52] :
      ( m1_subset_1(k3_xboole_0(B_52,'#skF_2'),k1_zfmisc_1('#skF_1'))
      | ~ m1_subset_1('#skF_2',k1_zfmisc_1('#skF_1')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_375,c_973])).

tff(c_997,plain,(
    ! [B_73] : m1_subset_1(k3_xboole_0(B_73,'#skF_2'),k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_985])).

tff(c_3051,plain,(
    ! [B_113] : k4_xboole_0('#skF_1',k3_xboole_0(B_113,'#skF_2')) = k3_subset_1('#skF_1',k3_xboole_0(B_113,'#skF_2')) ),
    inference(resolution,[status(thm)],[c_997,c_14])).

tff(c_3061,plain,(
    k3_subset_1('#skF_1',k3_xboole_0('#skF_1','#skF_2')) = k4_xboole_0('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_3051,c_262])).

tff(c_3095,plain,(
    k3_subset_1('#skF_1',k3_xboole_0('#skF_1','#skF_2')) = k3_subset_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_97,c_3061])).

tff(c_1025,plain,(
    ! [B_73] : k3_subset_1('#skF_1',k3_subset_1('#skF_1',k3_xboole_0(B_73,'#skF_2'))) = k3_xboole_0(B_73,'#skF_2') ),
    inference(resolution,[status(thm)],[c_997,c_18])).

tff(c_3105,plain,(
    k3_subset_1('#skF_1',k3_subset_1('#skF_1','#skF_2')) = k3_xboole_0('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_3095,c_1025])).

tff(c_3108,plain,(
    k3_xboole_0('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_153,c_3105])).

tff(c_8,plain,(
    ! [A_7,B_8,C_9] : k5_xboole_0(k3_xboole_0(A_7,B_8),k3_xboole_0(C_9,B_8)) = k3_xboole_0(k5_xboole_0(A_7,C_9),B_8) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_3126,plain,(
    ! [C_9] : k5_xboole_0('#skF_2',k3_xboole_0(C_9,'#skF_2')) = k3_xboole_0(k5_xboole_0('#skF_1',C_9),'#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_3108,c_8])).

tff(c_3397,plain,(
    ! [C_115] : k3_xboole_0('#skF_2',k5_xboole_0('#skF_1',C_115)) = k4_xboole_0('#skF_2',C_115) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_2,c_3126])).

tff(c_3467,plain,(
    k3_xboole_0('#skF_2',k3_subset_1('#skF_1','#skF_3')) = k4_xboole_0('#skF_2','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_2877,c_3397])).

tff(c_3492,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1985,c_3467])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n005.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 12:52:02 EST 2020
% 0.18/0.34  % CPUTime    : 
% 0.18/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.87/1.93  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.87/1.94  
% 4.87/1.94  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.87/1.94  %$ m1_subset_1 > k9_subset_1 > k7_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1
% 4.87/1.94  
% 4.87/1.94  %Foreground sorts:
% 4.87/1.94  
% 4.87/1.94  
% 4.87/1.94  %Background operators:
% 4.87/1.94  
% 4.87/1.94  
% 4.87/1.94  %Foreground operators:
% 4.87/1.94  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.87/1.94  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.87/1.94  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 4.87/1.94  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 4.87/1.94  tff('#skF_2', type, '#skF_2': $i).
% 4.87/1.94  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 4.87/1.94  tff('#skF_3', type, '#skF_3': $i).
% 4.87/1.94  tff('#skF_1', type, '#skF_1': $i).
% 4.87/1.94  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.87/1.94  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.87/1.94  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.87/1.94  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.87/1.94  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 4.87/1.94  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.87/1.94  
% 4.87/1.96  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 4.87/1.96  tff(f_67, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k9_subset_1(A, B, k3_subset_1(A, C))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t32_subset_1)).
% 4.87/1.96  tff(f_59, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 4.87/1.96  tff(f_39, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k9_subset_1(A, C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k9_subset_1)).
% 4.87/1.96  tff(f_55, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 4.87/1.96  tff(f_43, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 4.87/1.96  tff(f_51, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, k3_subset_1(A, B)) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 4.87/1.96  tff(f_47, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => m1_subset_1(k9_subset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k9_subset_1)).
% 4.87/1.96  tff(f_31, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 4.87/1.96  tff(f_29, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 4.87/1.96  tff(f_35, axiom, (![A, B, C]: (k3_xboole_0(k3_xboole_0(A, B), C) = k3_xboole_0(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t16_xboole_1)).
% 4.87/1.96  tff(f_33, axiom, (![A, B, C]: (k5_xboole_0(k3_xboole_0(A, B), k3_xboole_0(C, B)) = k3_xboole_0(k5_xboole_0(A, C), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t112_xboole_1)).
% 4.87/1.96  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.87/1.96  tff(c_28, plain, (m1_subset_1('#skF_2', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_67])).
% 4.87/1.96  tff(c_369, plain, (![A_51, B_52, C_53]: (k9_subset_1(A_51, B_52, C_53)=k3_xboole_0(B_52, C_53) | ~m1_subset_1(C_53, k1_zfmisc_1(A_51)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 4.87/1.96  tff(c_375, plain, (![B_52]: (k9_subset_1('#skF_1', B_52, '#skF_2')=k3_xboole_0(B_52, '#skF_2'))), inference(resolution, [status(thm)], [c_28, c_369])).
% 4.87/1.96  tff(c_1915, plain, (![A_93, C_94, B_95]: (k9_subset_1(A_93, C_94, B_95)=k9_subset_1(A_93, B_95, C_94) | ~m1_subset_1(C_94, k1_zfmisc_1(A_93)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.87/1.96  tff(c_1937, plain, (![B_95]: (k9_subset_1('#skF_1', B_95, '#skF_2')=k9_subset_1('#skF_1', '#skF_2', B_95))), inference(resolution, [status(thm)], [c_28, c_1915])).
% 4.87/1.96  tff(c_1950, plain, (![B_95]: (k9_subset_1('#skF_1', '#skF_2', B_95)=k3_xboole_0(B_95, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_375, c_1937])).
% 4.87/1.96  tff(c_436, plain, (![A_58, B_59, C_60]: (k7_subset_1(A_58, B_59, C_60)=k4_xboole_0(B_59, C_60) | ~m1_subset_1(B_59, k1_zfmisc_1(A_58)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 4.87/1.96  tff(c_442, plain, (![C_60]: (k7_subset_1('#skF_1', '#skF_2', C_60)=k4_xboole_0('#skF_2', C_60))), inference(resolution, [status(thm)], [c_28, c_436])).
% 4.87/1.96  tff(c_24, plain, (k9_subset_1('#skF_1', '#skF_2', k3_subset_1('#skF_1', '#skF_3'))!=k7_subset_1('#skF_1', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_67])).
% 4.87/1.96  tff(c_452, plain, (k9_subset_1('#skF_1', '#skF_2', k3_subset_1('#skF_1', '#skF_3'))!=k4_xboole_0('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_442, c_24])).
% 4.87/1.96  tff(c_1984, plain, (k3_xboole_0(k3_subset_1('#skF_1', '#skF_3'), '#skF_2')!=k4_xboole_0('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1950, c_452])).
% 4.87/1.96  tff(c_1985, plain, (k3_xboole_0('#skF_2', k3_subset_1('#skF_1', '#skF_3'))!=k4_xboole_0('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_1984])).
% 4.87/1.96  tff(c_26, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_67])).
% 4.87/1.96  tff(c_89, plain, (![A_35, B_36]: (k4_xboole_0(A_35, B_36)=k3_subset_1(A_35, B_36) | ~m1_subset_1(B_36, k1_zfmisc_1(A_35)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.87/1.96  tff(c_96, plain, (k4_xboole_0('#skF_1', '#skF_3')=k3_subset_1('#skF_1', '#skF_3')), inference(resolution, [status(thm)], [c_26, c_89])).
% 4.87/1.96  tff(c_147, plain, (![A_40, B_41]: (k3_subset_1(A_40, k3_subset_1(A_40, B_41))=B_41 | ~m1_subset_1(B_41, k1_zfmisc_1(A_40)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 4.87/1.96  tff(c_152, plain, (k3_subset_1('#skF_1', k3_subset_1('#skF_1', '#skF_3'))='#skF_3'), inference(resolution, [status(thm)], [c_26, c_147])).
% 4.87/1.96  tff(c_374, plain, (![B_52]: (k9_subset_1('#skF_1', B_52, '#skF_3')=k3_xboole_0(B_52, '#skF_3'))), inference(resolution, [status(thm)], [c_26, c_369])).
% 4.87/1.96  tff(c_973, plain, (![A_70, B_71, C_72]: (m1_subset_1(k9_subset_1(A_70, B_71, C_72), k1_zfmisc_1(A_70)) | ~m1_subset_1(C_72, k1_zfmisc_1(A_70)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 4.87/1.96  tff(c_988, plain, (![B_52]: (m1_subset_1(k3_xboole_0(B_52, '#skF_3'), k1_zfmisc_1('#skF_1')) | ~m1_subset_1('#skF_3', k1_zfmisc_1('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_374, c_973])).
% 4.87/1.96  tff(c_1028, plain, (![B_74]: (m1_subset_1(k3_xboole_0(B_74, '#skF_3'), k1_zfmisc_1('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_988])).
% 4.87/1.96  tff(c_14, plain, (![A_16, B_17]: (k4_xboole_0(A_16, B_17)=k3_subset_1(A_16, B_17) | ~m1_subset_1(B_17, k1_zfmisc_1(A_16)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.87/1.96  tff(c_2746, plain, (![B_108]: (k4_xboole_0('#skF_1', k3_xboole_0(B_108, '#skF_3'))=k3_subset_1('#skF_1', k3_xboole_0(B_108, '#skF_3')))), inference(resolution, [status(thm)], [c_1028, c_14])).
% 4.87/1.96  tff(c_6, plain, (![A_5, B_6]: (k5_xboole_0(A_5, k3_xboole_0(A_5, B_6))=k4_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.87/1.96  tff(c_4, plain, (![A_3]: (k3_xboole_0(A_3, A_3)=A_3)), inference(cnfTransformation, [status(thm)], [f_29])).
% 4.87/1.96  tff(c_162, plain, (![A_42, B_43, C_44]: (k3_xboole_0(k3_xboole_0(A_42, B_43), C_44)=k3_xboole_0(A_42, k3_xboole_0(B_43, C_44)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.87/1.96  tff(c_216, plain, (![A_45, C_46]: (k3_xboole_0(A_45, k3_xboole_0(A_45, C_46))=k3_xboole_0(A_45, C_46))), inference(superposition, [status(thm), theory('equality')], [c_4, c_162])).
% 4.87/1.96  tff(c_235, plain, (![A_45, C_46]: (k5_xboole_0(A_45, k3_xboole_0(A_45, C_46))=k4_xboole_0(A_45, k3_xboole_0(A_45, C_46)))), inference(superposition, [status(thm), theory('equality')], [c_216, c_6])).
% 4.87/1.96  tff(c_262, plain, (![A_45, C_46]: (k4_xboole_0(A_45, k3_xboole_0(A_45, C_46))=k4_xboole_0(A_45, C_46))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_235])).
% 4.87/1.96  tff(c_2756, plain, (k3_subset_1('#skF_1', k3_xboole_0('#skF_1', '#skF_3'))=k4_xboole_0('#skF_1', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_2746, c_262])).
% 4.87/1.96  tff(c_2790, plain, (k3_subset_1('#skF_1', k3_xboole_0('#skF_1', '#skF_3'))=k3_subset_1('#skF_1', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_96, c_2756])).
% 4.87/1.96  tff(c_18, plain, (![A_21, B_22]: (k3_subset_1(A_21, k3_subset_1(A_21, B_22))=B_22 | ~m1_subset_1(B_22, k1_zfmisc_1(A_21)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 4.87/1.96  tff(c_1056, plain, (![B_74]: (k3_subset_1('#skF_1', k3_subset_1('#skF_1', k3_xboole_0(B_74, '#skF_3')))=k3_xboole_0(B_74, '#skF_3'))), inference(resolution, [status(thm)], [c_1028, c_18])).
% 4.87/1.96  tff(c_2800, plain, (k3_subset_1('#skF_1', k3_subset_1('#skF_1', '#skF_3'))=k3_xboole_0('#skF_1', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_2790, c_1056])).
% 4.87/1.96  tff(c_2803, plain, (k3_xboole_0('#skF_1', '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_152, c_2800])).
% 4.87/1.96  tff(c_2861, plain, (k5_xboole_0('#skF_1', '#skF_3')=k4_xboole_0('#skF_1', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_2803, c_6])).
% 4.87/1.96  tff(c_2877, plain, (k5_xboole_0('#skF_1', '#skF_3')=k3_subset_1('#skF_1', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_96, c_2861])).
% 4.87/1.96  tff(c_71, plain, (![A_33, B_34]: (k5_xboole_0(A_33, k3_xboole_0(A_33, B_34))=k4_xboole_0(A_33, B_34))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.87/1.96  tff(c_80, plain, (![A_1, B_2]: (k5_xboole_0(A_1, k3_xboole_0(B_2, A_1))=k4_xboole_0(A_1, B_2))), inference(superposition, [status(thm), theory('equality')], [c_2, c_71])).
% 4.87/1.96  tff(c_153, plain, (k3_subset_1('#skF_1', k3_subset_1('#skF_1', '#skF_2'))='#skF_2'), inference(resolution, [status(thm)], [c_28, c_147])).
% 4.87/1.96  tff(c_97, plain, (k4_xboole_0('#skF_1', '#skF_2')=k3_subset_1('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_28, c_89])).
% 4.87/1.96  tff(c_985, plain, (![B_52]: (m1_subset_1(k3_xboole_0(B_52, '#skF_2'), k1_zfmisc_1('#skF_1')) | ~m1_subset_1('#skF_2', k1_zfmisc_1('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_375, c_973])).
% 4.87/1.96  tff(c_997, plain, (![B_73]: (m1_subset_1(k3_xboole_0(B_73, '#skF_2'), k1_zfmisc_1('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_985])).
% 4.87/1.96  tff(c_3051, plain, (![B_113]: (k4_xboole_0('#skF_1', k3_xboole_0(B_113, '#skF_2'))=k3_subset_1('#skF_1', k3_xboole_0(B_113, '#skF_2')))), inference(resolution, [status(thm)], [c_997, c_14])).
% 4.87/1.96  tff(c_3061, plain, (k3_subset_1('#skF_1', k3_xboole_0('#skF_1', '#skF_2'))=k4_xboole_0('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_3051, c_262])).
% 4.87/1.96  tff(c_3095, plain, (k3_subset_1('#skF_1', k3_xboole_0('#skF_1', '#skF_2'))=k3_subset_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_97, c_3061])).
% 4.87/1.96  tff(c_1025, plain, (![B_73]: (k3_subset_1('#skF_1', k3_subset_1('#skF_1', k3_xboole_0(B_73, '#skF_2')))=k3_xboole_0(B_73, '#skF_2'))), inference(resolution, [status(thm)], [c_997, c_18])).
% 4.87/1.96  tff(c_3105, plain, (k3_subset_1('#skF_1', k3_subset_1('#skF_1', '#skF_2'))=k3_xboole_0('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_3095, c_1025])).
% 4.87/1.96  tff(c_3108, plain, (k3_xboole_0('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_153, c_3105])).
% 4.87/1.96  tff(c_8, plain, (![A_7, B_8, C_9]: (k5_xboole_0(k3_xboole_0(A_7, B_8), k3_xboole_0(C_9, B_8))=k3_xboole_0(k5_xboole_0(A_7, C_9), B_8))), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.87/1.96  tff(c_3126, plain, (![C_9]: (k5_xboole_0('#skF_2', k3_xboole_0(C_9, '#skF_2'))=k3_xboole_0(k5_xboole_0('#skF_1', C_9), '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_3108, c_8])).
% 4.87/1.96  tff(c_3397, plain, (![C_115]: (k3_xboole_0('#skF_2', k5_xboole_0('#skF_1', C_115))=k4_xboole_0('#skF_2', C_115))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_2, c_3126])).
% 4.87/1.96  tff(c_3467, plain, (k3_xboole_0('#skF_2', k3_subset_1('#skF_1', '#skF_3'))=k4_xboole_0('#skF_2', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_2877, c_3397])).
% 4.87/1.96  tff(c_3492, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1985, c_3467])).
% 4.87/1.96  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.87/1.96  
% 4.87/1.96  Inference rules
% 4.87/1.96  ----------------------
% 4.87/1.96  #Ref     : 0
% 4.87/1.96  #Sup     : 869
% 4.87/1.96  #Fact    : 0
% 4.87/1.96  #Define  : 0
% 4.87/1.96  #Split   : 0
% 4.87/1.96  #Chain   : 0
% 4.87/1.96  #Close   : 0
% 4.87/1.96  
% 4.87/1.96  Ordering : KBO
% 4.87/1.96  
% 4.87/1.96  Simplification rules
% 4.87/1.96  ----------------------
% 4.87/1.96  #Subsume      : 26
% 4.87/1.96  #Demod        : 695
% 4.87/1.96  #Tautology    : 428
% 4.87/1.96  #SimpNegUnit  : 1
% 4.87/1.96  #BackRed      : 2
% 4.87/1.96  
% 4.87/1.96  #Partial instantiations: 0
% 4.87/1.96  #Strategies tried      : 1
% 4.87/1.96  
% 4.87/1.96  Timing (in seconds)
% 4.87/1.96  ----------------------
% 4.87/1.96  Preprocessing        : 0.31
% 4.87/1.96  Parsing              : 0.17
% 4.87/1.96  CNF conversion       : 0.02
% 4.87/1.96  Main loop            : 0.84
% 4.87/1.96  Inferencing          : 0.24
% 4.87/1.96  Reduction            : 0.41
% 4.87/1.96  Demodulation         : 0.35
% 4.87/1.96  BG Simplification    : 0.03
% 4.87/1.96  Subsumption          : 0.11
% 4.87/1.96  Abstraction          : 0.05
% 4.87/1.96  MUC search           : 0.00
% 4.87/1.96  Cooper               : 0.00
% 4.87/1.96  Total                : 1.19
% 4.87/1.96  Index Insertion      : 0.00
% 4.87/1.96  Index Deletion       : 0.00
% 4.87/1.96  Index Matching       : 0.00
% 4.87/1.96  BG Taut test         : 0.00
%------------------------------------------------------------------------------
