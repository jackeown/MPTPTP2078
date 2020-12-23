%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:22:36 EST 2020

% Result     : Theorem 14.06s
% Output     : CNFRefutation 14.06s
% Verified   : 
% Statistics : Number of formulae       :   61 (  89 expanded)
%              Number of leaves         :   27 (  42 expanded)
%              Depth                    :    9
%              Number of atoms          :   71 ( 130 expanded)
%              Number of equality atoms :   17 (  30 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > m1_subset_1 > l1_struct_0 > k7_subset_1 > k5_setfam_1 > k4_xboole_0 > k2_xboole_0 > #nlpp > u1_struct_0 > k3_tarski > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff(k5_setfam_1,type,(
    k5_setfam_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_41,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_53,axiom,(
    ! [A,B] : k3_tarski(k2_xboole_0(A,B)) = k2_xboole_0(k3_tarski(A),k3_tarski(B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t96_zfmisc_1)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k4_xboole_0(A,B),C)
     => r1_tarski(A,k2_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_80,negated_conjecture,(
    ~ ! [A] :
        ( l1_struct_0(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
               => r1_tarski(k7_subset_1(u1_struct_0(A),k5_setfam_1(u1_struct_0(A),B),k5_setfam_1(u1_struct_0(A),C)),k5_setfam_1(u1_struct_0(A),k7_subset_1(k1_zfmisc_1(u1_struct_0(A)),B,C))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_tops_2)).

tff(f_69,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_65,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => k5_setfam_1(A,B) = k3_tarski(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k5_setfam_1)).

tff(f_47,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k2_xboole_0(B,C))
     => r1_tarski(k4_xboole_0(A,B),C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_xboole_1)).

tff(f_61,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => m1_subset_1(k5_setfam_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_setfam_1)).

tff(f_57,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

tff(c_12,plain,(
    ! [A_8,B_9] : r1_tarski(k4_xboole_0(A_8,B_9),A_8) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_20,plain,(
    ! [A_18,B_19] : k2_xboole_0(k3_tarski(A_18),k3_tarski(B_19)) = k3_tarski(k2_xboole_0(A_18,B_19)) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_400,plain,(
    ! [A_73,B_74,C_75] :
      ( r1_tarski(A_73,k2_xboole_0(B_74,C_75))
      | ~ r1_tarski(k4_xboole_0(A_73,B_74),C_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_429,plain,(
    ! [A_76,B_77] : r1_tarski(A_76,k2_xboole_0(B_77,A_76)) ),
    inference(resolution,[status(thm)],[c_12,c_400])).

tff(c_443,plain,(
    ! [B_19,A_18] : r1_tarski(k3_tarski(B_19),k3_tarski(k2_xboole_0(A_18,B_19))) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_429])).

tff(c_14,plain,(
    ! [A_10,B_11] : k2_xboole_0(A_10,k4_xboole_0(B_11,A_10)) = k2_xboole_0(A_10,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_36,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_75,plain,(
    ! [A_38,B_39] :
      ( r1_tarski(A_38,B_39)
      | ~ m1_subset_1(A_38,k1_zfmisc_1(B_39)) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_83,plain,(
    r1_tarski('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_36,c_75])).

tff(c_135,plain,(
    ! [A_48,C_49,B_50] :
      ( r1_tarski(A_48,C_49)
      | ~ r1_tarski(B_50,C_49)
      | ~ r1_tarski(A_48,B_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_144,plain,(
    ! [A_48] :
      ( r1_tarski(A_48,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ r1_tarski(A_48,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_83,c_135])).

tff(c_30,plain,(
    ! [A_27,B_28] :
      ( m1_subset_1(A_27,k1_zfmisc_1(B_28))
      | ~ r1_tarski(A_27,B_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_148,plain,(
    ! [A_51,B_52] :
      ( k5_setfam_1(A_51,B_52) = k3_tarski(B_52)
      | ~ m1_subset_1(B_52,k1_zfmisc_1(k1_zfmisc_1(A_51))) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_210,plain,(
    ! [A_61,A_62] :
      ( k5_setfam_1(A_61,A_62) = k3_tarski(A_62)
      | ~ r1_tarski(A_62,k1_zfmisc_1(A_61)) ) ),
    inference(resolution,[status(thm)],[c_30,c_148])).

tff(c_235,plain,(
    ! [A_48] :
      ( k5_setfam_1(u1_struct_0('#skF_1'),A_48) = k3_tarski(A_48)
      | ~ r1_tarski(A_48,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_144,c_210])).

tff(c_16,plain,(
    ! [A_12,B_13,C_14] :
      ( r1_tarski(k4_xboole_0(A_12,B_13),C_14)
      | ~ r1_tarski(A_12,k2_xboole_0(B_13,C_14)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_161,plain,(
    k5_setfam_1(u1_struct_0('#skF_1'),'#skF_2') = k3_tarski('#skF_2') ),
    inference(resolution,[status(thm)],[c_36,c_148])).

tff(c_697,plain,(
    ! [A_97,B_98] :
      ( m1_subset_1(k5_setfam_1(A_97,B_98),k1_zfmisc_1(A_97))
      | ~ m1_subset_1(B_98,k1_zfmisc_1(k1_zfmisc_1(A_97))) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_22,plain,(
    ! [A_20,B_21,C_22] :
      ( k7_subset_1(A_20,B_21,C_22) = k4_xboole_0(B_21,C_22)
      | ~ m1_subset_1(B_21,k1_zfmisc_1(A_20)) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_2158,plain,(
    ! [A_182,B_183,C_184] :
      ( k7_subset_1(A_182,k5_setfam_1(A_182,B_183),C_184) = k4_xboole_0(k5_setfam_1(A_182,B_183),C_184)
      | ~ m1_subset_1(B_183,k1_zfmisc_1(k1_zfmisc_1(A_182))) ) ),
    inference(resolution,[status(thm)],[c_697,c_22])).

tff(c_2168,plain,(
    ! [C_184] : k7_subset_1(u1_struct_0('#skF_1'),k5_setfam_1(u1_struct_0('#skF_1'),'#skF_2'),C_184) = k4_xboole_0(k5_setfam_1(u1_struct_0('#skF_1'),'#skF_2'),C_184) ),
    inference(resolution,[status(thm)],[c_36,c_2158])).

tff(c_2174,plain,(
    ! [C_184] : k7_subset_1(u1_struct_0('#skF_1'),k3_tarski('#skF_2'),C_184) = k4_xboole_0(k3_tarski('#skF_2'),C_184) ),
    inference(demodulation,[status(thm),theory(equality)],[c_161,c_161,c_2168])).

tff(c_588,plain,(
    ! [A_86,B_87,C_88] :
      ( k7_subset_1(A_86,B_87,C_88) = k4_xboole_0(B_87,C_88)
      | ~ m1_subset_1(B_87,k1_zfmisc_1(A_86)) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_597,plain,(
    ! [C_88] : k7_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')),'#skF_2',C_88) = k4_xboole_0('#skF_2',C_88) ),
    inference(resolution,[status(thm)],[c_36,c_588])).

tff(c_34,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_160,plain,(
    k5_setfam_1(u1_struct_0('#skF_1'),'#skF_3') = k3_tarski('#skF_3') ),
    inference(resolution,[status(thm)],[c_34,c_148])).

tff(c_32,plain,(
    ~ r1_tarski(k7_subset_1(u1_struct_0('#skF_1'),k5_setfam_1(u1_struct_0('#skF_1'),'#skF_2'),k5_setfam_1(u1_struct_0('#skF_1'),'#skF_3')),k5_setfam_1(u1_struct_0('#skF_1'),k7_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')),'#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_162,plain,(
    ~ r1_tarski(k7_subset_1(u1_struct_0('#skF_1'),k5_setfam_1(u1_struct_0('#skF_1'),'#skF_2'),k3_tarski('#skF_3')),k5_setfam_1(u1_struct_0('#skF_1'),k7_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')),'#skF_2','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_160,c_32])).

tff(c_183,plain,(
    ~ r1_tarski(k7_subset_1(u1_struct_0('#skF_1'),k3_tarski('#skF_2'),k3_tarski('#skF_3')),k5_setfam_1(u1_struct_0('#skF_1'),k7_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')),'#skF_2','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_161,c_162])).

tff(c_656,plain,(
    ~ r1_tarski(k7_subset_1(u1_struct_0('#skF_1'),k3_tarski('#skF_2'),k3_tarski('#skF_3')),k5_setfam_1(u1_struct_0('#skF_1'),k4_xboole_0('#skF_2','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_597,c_183])).

tff(c_2412,plain,(
    ~ r1_tarski(k4_xboole_0(k3_tarski('#skF_2'),k3_tarski('#skF_3')),k5_setfam_1(u1_struct_0('#skF_1'),k4_xboole_0('#skF_2','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2174,c_656])).

tff(c_4383,plain,(
    ~ r1_tarski(k3_tarski('#skF_2'),k2_xboole_0(k3_tarski('#skF_3'),k5_setfam_1(u1_struct_0('#skF_1'),k4_xboole_0('#skF_2','#skF_3')))) ),
    inference(resolution,[status(thm)],[c_16,c_2412])).

tff(c_39088,plain,
    ( ~ r1_tarski(k3_tarski('#skF_2'),k2_xboole_0(k3_tarski('#skF_3'),k3_tarski(k4_xboole_0('#skF_2','#skF_3'))))
    | ~ r1_tarski(k4_xboole_0('#skF_2','#skF_3'),'#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_235,c_4383])).

tff(c_39096,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_443,c_14,c_20,c_39088])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:25:15 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 14.06/7.17  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 14.06/7.18  
% 14.06/7.18  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 14.06/7.18  %$ r1_tarski > m1_subset_1 > l1_struct_0 > k7_subset_1 > k5_setfam_1 > k4_xboole_0 > k2_xboole_0 > #nlpp > u1_struct_0 > k3_tarski > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1
% 14.06/7.18  
% 14.06/7.18  %Foreground sorts:
% 14.06/7.18  
% 14.06/7.18  
% 14.06/7.18  %Background operators:
% 14.06/7.18  
% 14.06/7.18  
% 14.06/7.18  %Foreground operators:
% 14.06/7.18  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 14.06/7.18  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 14.06/7.18  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 14.06/7.18  tff('#skF_2', type, '#skF_2': $i).
% 14.06/7.18  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 14.06/7.18  tff('#skF_3', type, '#skF_3': $i).
% 14.06/7.18  tff('#skF_1', type, '#skF_1': $i).
% 14.06/7.18  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 14.06/7.18  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 14.06/7.18  tff(k5_setfam_1, type, k5_setfam_1: ($i * $i) > $i).
% 14.06/7.18  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 14.06/7.18  tff(k3_tarski, type, k3_tarski: $i > $i).
% 14.06/7.18  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 14.06/7.18  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 14.06/7.18  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 14.06/7.18  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 14.06/7.18  
% 14.06/7.19  tff(f_41, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 14.06/7.19  tff(f_53, axiom, (![A, B]: (k3_tarski(k2_xboole_0(A, B)) = k2_xboole_0(k3_tarski(A), k3_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t96_zfmisc_1)).
% 14.06/7.19  tff(f_51, axiom, (![A, B, C]: (r1_tarski(k4_xboole_0(A, B), C) => r1_tarski(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_xboole_1)).
% 14.06/7.19  tff(f_43, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 14.06/7.19  tff(f_80, negated_conjecture, ~(![A]: (l1_struct_0(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => r1_tarski(k7_subset_1(u1_struct_0(A), k5_setfam_1(u1_struct_0(A), B), k5_setfam_1(u1_struct_0(A), C)), k5_setfam_1(u1_struct_0(A), k7_subset_1(k1_zfmisc_1(u1_struct_0(A)), B, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_tops_2)).
% 14.06/7.19  tff(f_69, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 14.06/7.19  tff(f_39, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 14.06/7.19  tff(f_65, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (k5_setfam_1(A, B) = k3_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k5_setfam_1)).
% 14.06/7.19  tff(f_47, axiom, (![A, B, C]: (r1_tarski(A, k2_xboole_0(B, C)) => r1_tarski(k4_xboole_0(A, B), C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_xboole_1)).
% 14.06/7.19  tff(f_61, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => m1_subset_1(k5_setfam_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k5_setfam_1)).
% 14.06/7.19  tff(f_57, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 14.06/7.19  tff(c_12, plain, (![A_8, B_9]: (r1_tarski(k4_xboole_0(A_8, B_9), A_8))), inference(cnfTransformation, [status(thm)], [f_41])).
% 14.06/7.19  tff(c_20, plain, (![A_18, B_19]: (k2_xboole_0(k3_tarski(A_18), k3_tarski(B_19))=k3_tarski(k2_xboole_0(A_18, B_19)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 14.06/7.19  tff(c_400, plain, (![A_73, B_74, C_75]: (r1_tarski(A_73, k2_xboole_0(B_74, C_75)) | ~r1_tarski(k4_xboole_0(A_73, B_74), C_75))), inference(cnfTransformation, [status(thm)], [f_51])).
% 14.06/7.19  tff(c_429, plain, (![A_76, B_77]: (r1_tarski(A_76, k2_xboole_0(B_77, A_76)))), inference(resolution, [status(thm)], [c_12, c_400])).
% 14.06/7.19  tff(c_443, plain, (![B_19, A_18]: (r1_tarski(k3_tarski(B_19), k3_tarski(k2_xboole_0(A_18, B_19))))), inference(superposition, [status(thm), theory('equality')], [c_20, c_429])).
% 14.06/7.19  tff(c_14, plain, (![A_10, B_11]: (k2_xboole_0(A_10, k4_xboole_0(B_11, A_10))=k2_xboole_0(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_43])).
% 14.06/7.19  tff(c_36, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(cnfTransformation, [status(thm)], [f_80])).
% 14.06/7.19  tff(c_75, plain, (![A_38, B_39]: (r1_tarski(A_38, B_39) | ~m1_subset_1(A_38, k1_zfmisc_1(B_39)))), inference(cnfTransformation, [status(thm)], [f_69])).
% 14.06/7.19  tff(c_83, plain, (r1_tarski('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_36, c_75])).
% 14.06/7.19  tff(c_135, plain, (![A_48, C_49, B_50]: (r1_tarski(A_48, C_49) | ~r1_tarski(B_50, C_49) | ~r1_tarski(A_48, B_50))), inference(cnfTransformation, [status(thm)], [f_39])).
% 14.06/7.19  tff(c_144, plain, (![A_48]: (r1_tarski(A_48, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~r1_tarski(A_48, '#skF_2'))), inference(resolution, [status(thm)], [c_83, c_135])).
% 14.06/7.19  tff(c_30, plain, (![A_27, B_28]: (m1_subset_1(A_27, k1_zfmisc_1(B_28)) | ~r1_tarski(A_27, B_28))), inference(cnfTransformation, [status(thm)], [f_69])).
% 14.06/7.19  tff(c_148, plain, (![A_51, B_52]: (k5_setfam_1(A_51, B_52)=k3_tarski(B_52) | ~m1_subset_1(B_52, k1_zfmisc_1(k1_zfmisc_1(A_51))))), inference(cnfTransformation, [status(thm)], [f_65])).
% 14.06/7.19  tff(c_210, plain, (![A_61, A_62]: (k5_setfam_1(A_61, A_62)=k3_tarski(A_62) | ~r1_tarski(A_62, k1_zfmisc_1(A_61)))), inference(resolution, [status(thm)], [c_30, c_148])).
% 14.06/7.19  tff(c_235, plain, (![A_48]: (k5_setfam_1(u1_struct_0('#skF_1'), A_48)=k3_tarski(A_48) | ~r1_tarski(A_48, '#skF_2'))), inference(resolution, [status(thm)], [c_144, c_210])).
% 14.06/7.19  tff(c_16, plain, (![A_12, B_13, C_14]: (r1_tarski(k4_xboole_0(A_12, B_13), C_14) | ~r1_tarski(A_12, k2_xboole_0(B_13, C_14)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 14.06/7.19  tff(c_161, plain, (k5_setfam_1(u1_struct_0('#skF_1'), '#skF_2')=k3_tarski('#skF_2')), inference(resolution, [status(thm)], [c_36, c_148])).
% 14.06/7.19  tff(c_697, plain, (![A_97, B_98]: (m1_subset_1(k5_setfam_1(A_97, B_98), k1_zfmisc_1(A_97)) | ~m1_subset_1(B_98, k1_zfmisc_1(k1_zfmisc_1(A_97))))), inference(cnfTransformation, [status(thm)], [f_61])).
% 14.06/7.19  tff(c_22, plain, (![A_20, B_21, C_22]: (k7_subset_1(A_20, B_21, C_22)=k4_xboole_0(B_21, C_22) | ~m1_subset_1(B_21, k1_zfmisc_1(A_20)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 14.06/7.19  tff(c_2158, plain, (![A_182, B_183, C_184]: (k7_subset_1(A_182, k5_setfam_1(A_182, B_183), C_184)=k4_xboole_0(k5_setfam_1(A_182, B_183), C_184) | ~m1_subset_1(B_183, k1_zfmisc_1(k1_zfmisc_1(A_182))))), inference(resolution, [status(thm)], [c_697, c_22])).
% 14.06/7.19  tff(c_2168, plain, (![C_184]: (k7_subset_1(u1_struct_0('#skF_1'), k5_setfam_1(u1_struct_0('#skF_1'), '#skF_2'), C_184)=k4_xboole_0(k5_setfam_1(u1_struct_0('#skF_1'), '#skF_2'), C_184))), inference(resolution, [status(thm)], [c_36, c_2158])).
% 14.06/7.19  tff(c_2174, plain, (![C_184]: (k7_subset_1(u1_struct_0('#skF_1'), k3_tarski('#skF_2'), C_184)=k4_xboole_0(k3_tarski('#skF_2'), C_184))), inference(demodulation, [status(thm), theory('equality')], [c_161, c_161, c_2168])).
% 14.06/7.19  tff(c_588, plain, (![A_86, B_87, C_88]: (k7_subset_1(A_86, B_87, C_88)=k4_xboole_0(B_87, C_88) | ~m1_subset_1(B_87, k1_zfmisc_1(A_86)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 14.06/7.19  tff(c_597, plain, (![C_88]: (k7_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')), '#skF_2', C_88)=k4_xboole_0('#skF_2', C_88))), inference(resolution, [status(thm)], [c_36, c_588])).
% 14.06/7.19  tff(c_34, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(cnfTransformation, [status(thm)], [f_80])).
% 14.06/7.19  tff(c_160, plain, (k5_setfam_1(u1_struct_0('#skF_1'), '#skF_3')=k3_tarski('#skF_3')), inference(resolution, [status(thm)], [c_34, c_148])).
% 14.06/7.19  tff(c_32, plain, (~r1_tarski(k7_subset_1(u1_struct_0('#skF_1'), k5_setfam_1(u1_struct_0('#skF_1'), '#skF_2'), k5_setfam_1(u1_struct_0('#skF_1'), '#skF_3')), k5_setfam_1(u1_struct_0('#skF_1'), k7_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')), '#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_80])).
% 14.06/7.19  tff(c_162, plain, (~r1_tarski(k7_subset_1(u1_struct_0('#skF_1'), k5_setfam_1(u1_struct_0('#skF_1'), '#skF_2'), k3_tarski('#skF_3')), k5_setfam_1(u1_struct_0('#skF_1'), k7_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')), '#skF_2', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_160, c_32])).
% 14.06/7.19  tff(c_183, plain, (~r1_tarski(k7_subset_1(u1_struct_0('#skF_1'), k3_tarski('#skF_2'), k3_tarski('#skF_3')), k5_setfam_1(u1_struct_0('#skF_1'), k7_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')), '#skF_2', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_161, c_162])).
% 14.06/7.19  tff(c_656, plain, (~r1_tarski(k7_subset_1(u1_struct_0('#skF_1'), k3_tarski('#skF_2'), k3_tarski('#skF_3')), k5_setfam_1(u1_struct_0('#skF_1'), k4_xboole_0('#skF_2', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_597, c_183])).
% 14.06/7.19  tff(c_2412, plain, (~r1_tarski(k4_xboole_0(k3_tarski('#skF_2'), k3_tarski('#skF_3')), k5_setfam_1(u1_struct_0('#skF_1'), k4_xboole_0('#skF_2', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_2174, c_656])).
% 14.06/7.19  tff(c_4383, plain, (~r1_tarski(k3_tarski('#skF_2'), k2_xboole_0(k3_tarski('#skF_3'), k5_setfam_1(u1_struct_0('#skF_1'), k4_xboole_0('#skF_2', '#skF_3'))))), inference(resolution, [status(thm)], [c_16, c_2412])).
% 14.06/7.19  tff(c_39088, plain, (~r1_tarski(k3_tarski('#skF_2'), k2_xboole_0(k3_tarski('#skF_3'), k3_tarski(k4_xboole_0('#skF_2', '#skF_3')))) | ~r1_tarski(k4_xboole_0('#skF_2', '#skF_3'), '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_235, c_4383])).
% 14.06/7.19  tff(c_39096, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12, c_443, c_14, c_20, c_39088])).
% 14.06/7.19  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 14.06/7.19  
% 14.06/7.19  Inference rules
% 14.06/7.19  ----------------------
% 14.06/7.19  #Ref     : 0
% 14.06/7.19  #Sup     : 10392
% 14.06/7.19  #Fact    : 0
% 14.06/7.19  #Define  : 0
% 14.06/7.19  #Split   : 6
% 14.06/7.19  #Chain   : 0
% 14.06/7.19  #Close   : 0
% 14.06/7.19  
% 14.06/7.19  Ordering : KBO
% 14.06/7.19  
% 14.06/7.19  Simplification rules
% 14.06/7.19  ----------------------
% 14.06/7.19  #Subsume      : 611
% 14.06/7.19  #Demod        : 4407
% 14.06/7.19  #Tautology    : 3622
% 14.06/7.19  #SimpNegUnit  : 0
% 14.06/7.19  #BackRed      : 19
% 14.06/7.19  
% 14.06/7.19  #Partial instantiations: 0
% 14.06/7.19  #Strategies tried      : 1
% 14.06/7.19  
% 14.06/7.19  Timing (in seconds)
% 14.06/7.19  ----------------------
% 14.06/7.20  Preprocessing        : 0.29
% 14.06/7.20  Parsing              : 0.16
% 14.06/7.20  CNF conversion       : 0.02
% 14.06/7.20  Main loop            : 6.15
% 14.06/7.20  Inferencing          : 0.83
% 14.06/7.20  Reduction            : 3.21
% 14.06/7.20  Demodulation         : 2.86
% 14.06/7.20  BG Simplification    : 0.14
% 14.06/7.20  Subsumption          : 1.58
% 14.06/7.20  Abstraction          : 0.19
% 14.06/7.20  MUC search           : 0.00
% 14.06/7.20  Cooper               : 0.00
% 14.06/7.20  Total                : 6.47
% 14.06/7.20  Index Insertion      : 0.00
% 14.06/7.20  Index Deletion       : 0.00
% 14.06/7.20  Index Matching       : 0.00
% 14.06/7.20  BG Taut test         : 0.00
%------------------------------------------------------------------------------
