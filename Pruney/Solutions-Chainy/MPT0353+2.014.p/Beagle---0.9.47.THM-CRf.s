%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:55:54 EST 2020

% Result     : Theorem 10.34s
% Output     : CNFRefutation 10.34s
% Verified   : 
% Statistics : Number of formulae       :   72 ( 179 expanded)
%              Number of leaves         :   25 (  71 expanded)
%              Depth                    :   11
%              Number of atoms          :   74 ( 226 expanded)
%              Number of equality atoms :   52 ( 143 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   2 average)

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

tff(f_63,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => ! [C] :
            ( m1_subset_1(C,k1_zfmisc_1(A))
           => k7_subset_1(A,B,C) = k9_subset_1(A,B,k3_subset_1(A,C)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_subset_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k3_subset_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).

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

tff(f_39,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,k3_subset_1(A,B)) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_31,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_33,axiom,(
    ! [A,B,C] : k5_xboole_0(k3_xboole_0(A,B),k3_xboole_0(C,B)) = k3_xboole_0(k5_xboole_0(A,C),B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t112_xboole_1)).

tff(f_35,axiom,(
    ! [A,B,C] : k3_xboole_0(k3_xboole_0(A,B),C) = k3_xboole_0(A,k3_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_xboole_1)).

tff(c_24,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_14,plain,(
    ! [A_15,B_16] :
      ( m1_subset_1(k3_subset_1(A_15,B_16),k1_zfmisc_1(A_15))
      | ~ m1_subset_1(B_16,k1_zfmisc_1(A_15)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_427,plain,(
    ! [A_51,B_52,C_53] :
      ( k9_subset_1(A_51,B_52,C_53) = k3_xboole_0(B_52,C_53)
      | ~ m1_subset_1(C_53,k1_zfmisc_1(A_51)) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_8583,plain,(
    ! [A_136,B_137,B_138] :
      ( k9_subset_1(A_136,B_137,k3_subset_1(A_136,B_138)) = k3_xboole_0(B_137,k3_subset_1(A_136,B_138))
      | ~ m1_subset_1(B_138,k1_zfmisc_1(A_136)) ) ),
    inference(resolution,[status(thm)],[c_14,c_427])).

tff(c_8591,plain,(
    ! [B_137] : k9_subset_1('#skF_1',B_137,k3_subset_1('#skF_1','#skF_3')) = k3_xboole_0(B_137,k3_subset_1('#skF_1','#skF_3')) ),
    inference(resolution,[status(thm)],[c_24,c_8583])).

tff(c_26,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_702,plain,(
    ! [A_59,B_60,C_61] :
      ( k7_subset_1(A_59,B_60,C_61) = k4_xboole_0(B_60,C_61)
      | ~ m1_subset_1(B_60,k1_zfmisc_1(A_59)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_711,plain,(
    ! [C_61] : k7_subset_1('#skF_1','#skF_2',C_61) = k4_xboole_0('#skF_2',C_61) ),
    inference(resolution,[status(thm)],[c_26,c_702])).

tff(c_22,plain,(
    k9_subset_1('#skF_1','#skF_2',k3_subset_1('#skF_1','#skF_3')) != k7_subset_1('#skF_1','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_721,plain,(
    k9_subset_1('#skF_1','#skF_2',k3_subset_1('#skF_1','#skF_3')) != k4_xboole_0('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_711,c_22])).

tff(c_8596,plain,(
    k3_xboole_0('#skF_2',k3_subset_1('#skF_1','#skF_3')) != k4_xboole_0('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8591,c_721])).

tff(c_128,plain,(
    ! [A_34,B_35] :
      ( k4_xboole_0(A_34,B_35) = k3_subset_1(A_34,B_35)
      | ~ m1_subset_1(B_35,k1_zfmisc_1(A_34)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_135,plain,(
    k4_xboole_0('#skF_1','#skF_3') = k3_subset_1('#skF_1','#skF_3') ),
    inference(resolution,[status(thm)],[c_24,c_128])).

tff(c_277,plain,(
    ! [A_43,B_44] :
      ( k3_subset_1(A_43,k3_subset_1(A_43,B_44)) = B_44
      | ~ m1_subset_1(B_44,k1_zfmisc_1(A_43)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_282,plain,(
    k3_subset_1('#skF_1',k3_subset_1('#skF_1','#skF_3')) = '#skF_3' ),
    inference(resolution,[status(thm)],[c_24,c_277])).

tff(c_367,plain,(
    ! [A_47,B_48] :
      ( m1_subset_1(k3_subset_1(A_47,B_48),k1_zfmisc_1(A_47))
      | ~ m1_subset_1(B_48,k1_zfmisc_1(A_47)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_12,plain,(
    ! [A_13,B_14] :
      ( k4_xboole_0(A_13,B_14) = k3_subset_1(A_13,B_14)
      | ~ m1_subset_1(B_14,k1_zfmisc_1(A_13)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_8127,plain,(
    ! [A_132,B_133] :
      ( k4_xboole_0(A_132,k3_subset_1(A_132,B_133)) = k3_subset_1(A_132,k3_subset_1(A_132,B_133))
      | ~ m1_subset_1(B_133,k1_zfmisc_1(A_132)) ) ),
    inference(resolution,[status(thm)],[c_367,c_12])).

tff(c_8131,plain,(
    k4_xboole_0('#skF_1',k3_subset_1('#skF_1','#skF_3')) = k3_subset_1('#skF_1',k3_subset_1('#skF_1','#skF_3')) ),
    inference(resolution,[status(thm)],[c_24,c_8127])).

tff(c_8136,plain,(
    k4_xboole_0('#skF_1',k3_subset_1('#skF_1','#skF_3')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_282,c_8131])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_69,plain,(
    ! [A_29,B_30] : k5_xboole_0(A_29,k3_xboole_0(A_29,B_30)) = k4_xboole_0(A_29,B_30) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_81,plain,(
    ! [B_2,A_1] : k5_xboole_0(B_2,k3_xboole_0(A_1,B_2)) = k4_xboole_0(B_2,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_69])).

tff(c_4,plain,(
    ! [A_3] : k3_xboole_0(A_3,A_3) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_993,plain,(
    ! [A_68,B_69,C_70] : k5_xboole_0(k3_xboole_0(A_68,B_69),k3_xboole_0(C_70,B_69)) = k3_xboole_0(k5_xboole_0(A_68,C_70),B_69) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_1072,plain,(
    ! [A_3,C_70] : k5_xboole_0(A_3,k3_xboole_0(C_70,A_3)) = k3_xboole_0(k5_xboole_0(A_3,C_70),A_3) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_993])).

tff(c_1090,plain,(
    ! [A_3,C_70] : k3_xboole_0(A_3,k5_xboole_0(A_3,C_70)) = k4_xboole_0(A_3,C_70) ),
    inference(demodulation,[status(thm),theory(equality)],[c_81,c_2,c_1072])).

tff(c_1092,plain,(
    ! [A_71,C_72] : k3_xboole_0(A_71,k5_xboole_0(A_71,C_72)) = k4_xboole_0(A_71,C_72) ),
    inference(demodulation,[status(thm),theory(equality)],[c_81,c_2,c_1072])).

tff(c_145,plain,(
    ! [A_36,B_37,C_38] : k3_xboole_0(k3_xboole_0(A_36,B_37),C_38) = k3_xboole_0(A_36,k3_xboole_0(B_37,C_38)) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_190,plain,(
    ! [A_3,C_38] : k3_xboole_0(A_3,k3_xboole_0(A_3,C_38)) = k3_xboole_0(A_3,C_38) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_145])).

tff(c_1125,plain,(
    ! [A_71,C_72] : k3_xboole_0(A_71,k5_xboole_0(A_71,C_72)) = k3_xboole_0(A_71,k4_xboole_0(A_71,C_72)) ),
    inference(superposition,[status(thm),theory(equality)],[c_1092,c_190])).

tff(c_1161,plain,(
    ! [A_71,C_72] : k3_xboole_0(A_71,k4_xboole_0(A_71,C_72)) = k4_xboole_0(A_71,C_72) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1090,c_1125])).

tff(c_8150,plain,(
    k4_xboole_0('#skF_1',k3_subset_1('#skF_1','#skF_3')) = k3_xboole_0('#skF_1','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_8136,c_1161])).

tff(c_8154,plain,(
    k3_xboole_0('#skF_1','#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8136,c_8150])).

tff(c_6,plain,(
    ! [A_5,B_6] : k5_xboole_0(A_5,k3_xboole_0(A_5,B_6)) = k4_xboole_0(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_8255,plain,(
    k5_xboole_0('#skF_1','#skF_3') = k4_xboole_0('#skF_1','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_8154,c_6])).

tff(c_8274,plain,(
    k5_xboole_0('#skF_1','#skF_3') = k3_subset_1('#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_135,c_8255])).

tff(c_283,plain,(
    k3_subset_1('#skF_1',k3_subset_1('#skF_1','#skF_2')) = '#skF_2' ),
    inference(resolution,[status(thm)],[c_26,c_277])).

tff(c_8133,plain,(
    k4_xboole_0('#skF_1',k3_subset_1('#skF_1','#skF_2')) = k3_subset_1('#skF_1',k3_subset_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_26,c_8127])).

tff(c_8138,plain,(
    k4_xboole_0('#skF_1',k3_subset_1('#skF_1','#skF_2')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_283,c_8133])).

tff(c_8288,plain,(
    k4_xboole_0('#skF_1',k3_subset_1('#skF_1','#skF_2')) = k3_xboole_0('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_8138,c_1161])).

tff(c_8292,plain,(
    k3_xboole_0('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8138,c_8288])).

tff(c_1063,plain,(
    ! [A_68,B_2,A_1] : k5_xboole_0(k3_xboole_0(A_68,B_2),k3_xboole_0(B_2,A_1)) = k3_xboole_0(k5_xboole_0(A_68,A_1),B_2) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_993])).

tff(c_8306,plain,(
    ! [A_1] : k5_xboole_0('#skF_2',k3_xboole_0('#skF_2',A_1)) = k3_xboole_0(k5_xboole_0('#skF_1',A_1),'#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_8292,c_1063])).

tff(c_15318,plain,(
    ! [A_170] : k3_xboole_0('#skF_2',k5_xboole_0('#skF_1',A_170)) = k4_xboole_0('#skF_2',A_170) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_2,c_8306])).

tff(c_15450,plain,(
    k3_xboole_0('#skF_2',k3_subset_1('#skF_1','#skF_3')) = k4_xboole_0('#skF_2','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_8274,c_15318])).

tff(c_15482,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_8596,c_15450])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:25:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 10.34/4.33  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.34/4.34  
% 10.34/4.34  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.34/4.34  %$ m1_subset_1 > k9_subset_1 > k7_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1
% 10.34/4.34  
% 10.34/4.34  %Foreground sorts:
% 10.34/4.34  
% 10.34/4.34  
% 10.34/4.34  %Background operators:
% 10.34/4.34  
% 10.34/4.34  
% 10.34/4.34  %Foreground operators:
% 10.34/4.34  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 10.34/4.34  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 10.34/4.34  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 10.34/4.34  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 10.34/4.34  tff('#skF_2', type, '#skF_2': $i).
% 10.34/4.34  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 10.34/4.34  tff('#skF_3', type, '#skF_3': $i).
% 10.34/4.34  tff('#skF_1', type, '#skF_1': $i).
% 10.34/4.34  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 10.34/4.34  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 10.34/4.34  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 10.34/4.34  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 10.34/4.34  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 10.34/4.34  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 10.34/4.34  
% 10.34/4.35  tff(f_63, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k9_subset_1(A, B, k3_subset_1(A, C))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t32_subset_1)).
% 10.34/4.35  tff(f_43, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k3_subset_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 10.34/4.35  tff(f_55, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 10.34/4.35  tff(f_51, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 10.34/4.35  tff(f_39, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 10.34/4.35  tff(f_47, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, k3_subset_1(A, B)) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 10.34/4.35  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 10.34/4.35  tff(f_31, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 10.34/4.35  tff(f_29, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 10.34/4.35  tff(f_33, axiom, (![A, B, C]: (k5_xboole_0(k3_xboole_0(A, B), k3_xboole_0(C, B)) = k3_xboole_0(k5_xboole_0(A, C), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t112_xboole_1)).
% 10.34/4.35  tff(f_35, axiom, (![A, B, C]: (k3_xboole_0(k3_xboole_0(A, B), C) = k3_xboole_0(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t16_xboole_1)).
% 10.34/4.35  tff(c_24, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_63])).
% 10.34/4.35  tff(c_14, plain, (![A_15, B_16]: (m1_subset_1(k3_subset_1(A_15, B_16), k1_zfmisc_1(A_15)) | ~m1_subset_1(B_16, k1_zfmisc_1(A_15)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 10.34/4.35  tff(c_427, plain, (![A_51, B_52, C_53]: (k9_subset_1(A_51, B_52, C_53)=k3_xboole_0(B_52, C_53) | ~m1_subset_1(C_53, k1_zfmisc_1(A_51)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 10.34/4.35  tff(c_8583, plain, (![A_136, B_137, B_138]: (k9_subset_1(A_136, B_137, k3_subset_1(A_136, B_138))=k3_xboole_0(B_137, k3_subset_1(A_136, B_138)) | ~m1_subset_1(B_138, k1_zfmisc_1(A_136)))), inference(resolution, [status(thm)], [c_14, c_427])).
% 10.34/4.35  tff(c_8591, plain, (![B_137]: (k9_subset_1('#skF_1', B_137, k3_subset_1('#skF_1', '#skF_3'))=k3_xboole_0(B_137, k3_subset_1('#skF_1', '#skF_3')))), inference(resolution, [status(thm)], [c_24, c_8583])).
% 10.34/4.35  tff(c_26, plain, (m1_subset_1('#skF_2', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_63])).
% 10.34/4.35  tff(c_702, plain, (![A_59, B_60, C_61]: (k7_subset_1(A_59, B_60, C_61)=k4_xboole_0(B_60, C_61) | ~m1_subset_1(B_60, k1_zfmisc_1(A_59)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 10.34/4.35  tff(c_711, plain, (![C_61]: (k7_subset_1('#skF_1', '#skF_2', C_61)=k4_xboole_0('#skF_2', C_61))), inference(resolution, [status(thm)], [c_26, c_702])).
% 10.34/4.35  tff(c_22, plain, (k9_subset_1('#skF_1', '#skF_2', k3_subset_1('#skF_1', '#skF_3'))!=k7_subset_1('#skF_1', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_63])).
% 10.34/4.35  tff(c_721, plain, (k9_subset_1('#skF_1', '#skF_2', k3_subset_1('#skF_1', '#skF_3'))!=k4_xboole_0('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_711, c_22])).
% 10.34/4.35  tff(c_8596, plain, (k3_xboole_0('#skF_2', k3_subset_1('#skF_1', '#skF_3'))!=k4_xboole_0('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_8591, c_721])).
% 10.34/4.35  tff(c_128, plain, (![A_34, B_35]: (k4_xboole_0(A_34, B_35)=k3_subset_1(A_34, B_35) | ~m1_subset_1(B_35, k1_zfmisc_1(A_34)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 10.34/4.35  tff(c_135, plain, (k4_xboole_0('#skF_1', '#skF_3')=k3_subset_1('#skF_1', '#skF_3')), inference(resolution, [status(thm)], [c_24, c_128])).
% 10.34/4.35  tff(c_277, plain, (![A_43, B_44]: (k3_subset_1(A_43, k3_subset_1(A_43, B_44))=B_44 | ~m1_subset_1(B_44, k1_zfmisc_1(A_43)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 10.34/4.35  tff(c_282, plain, (k3_subset_1('#skF_1', k3_subset_1('#skF_1', '#skF_3'))='#skF_3'), inference(resolution, [status(thm)], [c_24, c_277])).
% 10.34/4.35  tff(c_367, plain, (![A_47, B_48]: (m1_subset_1(k3_subset_1(A_47, B_48), k1_zfmisc_1(A_47)) | ~m1_subset_1(B_48, k1_zfmisc_1(A_47)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 10.34/4.35  tff(c_12, plain, (![A_13, B_14]: (k4_xboole_0(A_13, B_14)=k3_subset_1(A_13, B_14) | ~m1_subset_1(B_14, k1_zfmisc_1(A_13)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 10.34/4.35  tff(c_8127, plain, (![A_132, B_133]: (k4_xboole_0(A_132, k3_subset_1(A_132, B_133))=k3_subset_1(A_132, k3_subset_1(A_132, B_133)) | ~m1_subset_1(B_133, k1_zfmisc_1(A_132)))), inference(resolution, [status(thm)], [c_367, c_12])).
% 10.34/4.35  tff(c_8131, plain, (k4_xboole_0('#skF_1', k3_subset_1('#skF_1', '#skF_3'))=k3_subset_1('#skF_1', k3_subset_1('#skF_1', '#skF_3'))), inference(resolution, [status(thm)], [c_24, c_8127])).
% 10.34/4.35  tff(c_8136, plain, (k4_xboole_0('#skF_1', k3_subset_1('#skF_1', '#skF_3'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_282, c_8131])).
% 10.34/4.35  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 10.34/4.35  tff(c_69, plain, (![A_29, B_30]: (k5_xboole_0(A_29, k3_xboole_0(A_29, B_30))=k4_xboole_0(A_29, B_30))), inference(cnfTransformation, [status(thm)], [f_31])).
% 10.34/4.35  tff(c_81, plain, (![B_2, A_1]: (k5_xboole_0(B_2, k3_xboole_0(A_1, B_2))=k4_xboole_0(B_2, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_69])).
% 10.34/4.35  tff(c_4, plain, (![A_3]: (k3_xboole_0(A_3, A_3)=A_3)), inference(cnfTransformation, [status(thm)], [f_29])).
% 10.34/4.35  tff(c_993, plain, (![A_68, B_69, C_70]: (k5_xboole_0(k3_xboole_0(A_68, B_69), k3_xboole_0(C_70, B_69))=k3_xboole_0(k5_xboole_0(A_68, C_70), B_69))), inference(cnfTransformation, [status(thm)], [f_33])).
% 10.34/4.35  tff(c_1072, plain, (![A_3, C_70]: (k5_xboole_0(A_3, k3_xboole_0(C_70, A_3))=k3_xboole_0(k5_xboole_0(A_3, C_70), A_3))), inference(superposition, [status(thm), theory('equality')], [c_4, c_993])).
% 10.34/4.35  tff(c_1090, plain, (![A_3, C_70]: (k3_xboole_0(A_3, k5_xboole_0(A_3, C_70))=k4_xboole_0(A_3, C_70))), inference(demodulation, [status(thm), theory('equality')], [c_81, c_2, c_1072])).
% 10.34/4.35  tff(c_1092, plain, (![A_71, C_72]: (k3_xboole_0(A_71, k5_xboole_0(A_71, C_72))=k4_xboole_0(A_71, C_72))), inference(demodulation, [status(thm), theory('equality')], [c_81, c_2, c_1072])).
% 10.34/4.35  tff(c_145, plain, (![A_36, B_37, C_38]: (k3_xboole_0(k3_xboole_0(A_36, B_37), C_38)=k3_xboole_0(A_36, k3_xboole_0(B_37, C_38)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 10.34/4.35  tff(c_190, plain, (![A_3, C_38]: (k3_xboole_0(A_3, k3_xboole_0(A_3, C_38))=k3_xboole_0(A_3, C_38))), inference(superposition, [status(thm), theory('equality')], [c_4, c_145])).
% 10.34/4.36  tff(c_1125, plain, (![A_71, C_72]: (k3_xboole_0(A_71, k5_xboole_0(A_71, C_72))=k3_xboole_0(A_71, k4_xboole_0(A_71, C_72)))), inference(superposition, [status(thm), theory('equality')], [c_1092, c_190])).
% 10.34/4.36  tff(c_1161, plain, (![A_71, C_72]: (k3_xboole_0(A_71, k4_xboole_0(A_71, C_72))=k4_xboole_0(A_71, C_72))), inference(demodulation, [status(thm), theory('equality')], [c_1090, c_1125])).
% 10.34/4.36  tff(c_8150, plain, (k4_xboole_0('#skF_1', k3_subset_1('#skF_1', '#skF_3'))=k3_xboole_0('#skF_1', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_8136, c_1161])).
% 10.34/4.36  tff(c_8154, plain, (k3_xboole_0('#skF_1', '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_8136, c_8150])).
% 10.34/4.36  tff(c_6, plain, (![A_5, B_6]: (k5_xboole_0(A_5, k3_xboole_0(A_5, B_6))=k4_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_31])).
% 10.34/4.36  tff(c_8255, plain, (k5_xboole_0('#skF_1', '#skF_3')=k4_xboole_0('#skF_1', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_8154, c_6])).
% 10.34/4.36  tff(c_8274, plain, (k5_xboole_0('#skF_1', '#skF_3')=k3_subset_1('#skF_1', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_135, c_8255])).
% 10.34/4.36  tff(c_283, plain, (k3_subset_1('#skF_1', k3_subset_1('#skF_1', '#skF_2'))='#skF_2'), inference(resolution, [status(thm)], [c_26, c_277])).
% 10.34/4.36  tff(c_8133, plain, (k4_xboole_0('#skF_1', k3_subset_1('#skF_1', '#skF_2'))=k3_subset_1('#skF_1', k3_subset_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_26, c_8127])).
% 10.34/4.36  tff(c_8138, plain, (k4_xboole_0('#skF_1', k3_subset_1('#skF_1', '#skF_2'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_283, c_8133])).
% 10.34/4.36  tff(c_8288, plain, (k4_xboole_0('#skF_1', k3_subset_1('#skF_1', '#skF_2'))=k3_xboole_0('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_8138, c_1161])).
% 10.34/4.36  tff(c_8292, plain, (k3_xboole_0('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_8138, c_8288])).
% 10.34/4.36  tff(c_1063, plain, (![A_68, B_2, A_1]: (k5_xboole_0(k3_xboole_0(A_68, B_2), k3_xboole_0(B_2, A_1))=k3_xboole_0(k5_xboole_0(A_68, A_1), B_2))), inference(superposition, [status(thm), theory('equality')], [c_2, c_993])).
% 10.34/4.36  tff(c_8306, plain, (![A_1]: (k5_xboole_0('#skF_2', k3_xboole_0('#skF_2', A_1))=k3_xboole_0(k5_xboole_0('#skF_1', A_1), '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_8292, c_1063])).
% 10.34/4.36  tff(c_15318, plain, (![A_170]: (k3_xboole_0('#skF_2', k5_xboole_0('#skF_1', A_170))=k4_xboole_0('#skF_2', A_170))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_2, c_8306])).
% 10.34/4.36  tff(c_15450, plain, (k3_xboole_0('#skF_2', k3_subset_1('#skF_1', '#skF_3'))=k4_xboole_0('#skF_2', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_8274, c_15318])).
% 10.34/4.36  tff(c_15482, plain, $false, inference(negUnitSimplification, [status(thm)], [c_8596, c_15450])).
% 10.34/4.36  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.34/4.36  
% 10.34/4.36  Inference rules
% 10.34/4.36  ----------------------
% 10.34/4.36  #Ref     : 0
% 10.34/4.36  #Sup     : 4018
% 10.34/4.36  #Fact    : 0
% 10.34/4.36  #Define  : 0
% 10.34/4.36  #Split   : 0
% 10.34/4.36  #Chain   : 0
% 10.34/4.36  #Close   : 0
% 10.34/4.36  
% 10.34/4.36  Ordering : KBO
% 10.34/4.36  
% 10.34/4.36  Simplification rules
% 10.34/4.36  ----------------------
% 10.34/4.36  #Subsume      : 227
% 10.34/4.36  #Demod        : 3858
% 10.34/4.36  #Tautology    : 1040
% 10.34/4.36  #SimpNegUnit  : 1
% 10.34/4.36  #BackRed      : 7
% 10.34/4.36  
% 10.34/4.36  #Partial instantiations: 0
% 10.34/4.36  #Strategies tried      : 1
% 10.34/4.36  
% 10.34/4.36  Timing (in seconds)
% 10.34/4.36  ----------------------
% 10.34/4.36  Preprocessing        : 0.29
% 10.34/4.36  Parsing              : 0.16
% 10.34/4.36  CNF conversion       : 0.02
% 10.34/4.36  Main loop            : 3.28
% 10.34/4.36  Inferencing          : 0.56
% 10.34/4.36  Reduction            : 2.10
% 10.34/4.36  Demodulation         : 1.94
% 10.34/4.36  BG Simplification    : 0.10
% 10.34/4.36  Subsumption          : 0.41
% 10.34/4.36  Abstraction          : 0.15
% 10.34/4.36  MUC search           : 0.00
% 10.34/4.36  Cooper               : 0.00
% 10.34/4.36  Total                : 3.60
% 10.34/4.36  Index Insertion      : 0.00
% 10.34/4.36  Index Deletion       : 0.00
% 10.34/4.36  Index Matching       : 0.00
% 10.34/4.36  BG Taut test         : 0.00
%------------------------------------------------------------------------------
