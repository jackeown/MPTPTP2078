%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:22:36 EST 2020

% Result     : Theorem 5.19s
% Output     : CNFRefutation 5.19s
% Verified   : 
% Statistics : Number of formulae       :   59 (  95 expanded)
%              Number of leaves         :   26 (  44 expanded)
%              Depth                    :    9
%              Number of atoms          :   64 ( 139 expanded)
%              Number of equality atoms :   20 (  40 expanded)
%              Maximal formula depth    :    8 (   3 average)
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

tff(f_49,axiom,(
    ! [A,B] : k3_tarski(k2_xboole_0(A,B)) = k2_xboole_0(k3_tarski(A),k3_tarski(B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t96_zfmisc_1)).

tff(f_39,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_47,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k4_xboole_0(A,B),C)
     => r1_tarski(A,k2_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_xboole_1)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k2_xboole_0(B,C))
     => r1_tarski(k4_xboole_0(A,B),C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_xboole_1)).

tff(f_76,negated_conjecture,(
    ~ ! [A] :
        ( l1_struct_0(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
               => r1_tarski(k7_subset_1(u1_struct_0(A),k5_setfam_1(u1_struct_0(A),B),k5_setfam_1(u1_struct_0(A),C)),k5_setfam_1(u1_struct_0(A),k7_subset_1(k1_zfmisc_1(u1_struct_0(A)),B,C))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_tops_2)).

tff(f_57,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

tff(f_53,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k7_subset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_subset_1)).

tff(f_65,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => k5_setfam_1(A,B) = k3_tarski(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k5_setfam_1)).

tff(f_61,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => m1_subset_1(k5_setfam_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_setfam_1)).

tff(c_18,plain,(
    ! [A_15,B_16] : k2_xboole_0(k3_tarski(A_15),k3_tarski(B_16)) = k3_tarski(k2_xboole_0(A_15,B_16)) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_12,plain,(
    ! [A_7,B_8] : k2_xboole_0(A_7,k4_xboole_0(B_8,A_7)) = k2_xboole_0(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_8,plain,(
    ! [B_4] : r1_tarski(B_4,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_290,plain,(
    ! [A_52,B_53,C_54] :
      ( r1_tarski(A_52,k2_xboole_0(B_53,C_54))
      | ~ r1_tarski(k4_xboole_0(A_52,B_53),C_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_297,plain,(
    ! [A_52,B_53] : r1_tarski(A_52,k2_xboole_0(B_53,k4_xboole_0(A_52,B_53))) ),
    inference(resolution,[status(thm)],[c_8,c_290])).

tff(c_301,plain,(
    ! [A_55,B_56] : r1_tarski(A_55,k2_xboole_0(B_56,A_55)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_297])).

tff(c_316,plain,(
    ! [B_16,A_15] : r1_tarski(k3_tarski(B_16),k3_tarski(k2_xboole_0(A_15,B_16))) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_301])).

tff(c_14,plain,(
    ! [A_9,B_10,C_11] :
      ( r1_tarski(k4_xboole_0(A_9,B_10),C_11)
      | ~ r1_tarski(A_9,k2_xboole_0(B_10,C_11)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_32,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_540,plain,(
    ! [A_69,B_70,C_71] :
      ( k7_subset_1(A_69,B_70,C_71) = k4_xboole_0(B_70,C_71)
      | ~ m1_subset_1(B_70,k1_zfmisc_1(A_69)) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_549,plain,(
    ! [C_71] : k7_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')),'#skF_2',C_71) = k4_xboole_0('#skF_2',C_71) ),
    inference(resolution,[status(thm)],[c_32,c_540])).

tff(c_369,plain,(
    ! [A_59,B_60,C_61] :
      ( m1_subset_1(k7_subset_1(A_59,B_60,C_61),k1_zfmisc_1(A_59))
      | ~ m1_subset_1(B_60,k1_zfmisc_1(A_59)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_26,plain,(
    ! [A_25,B_26] :
      ( k5_setfam_1(A_25,B_26) = k3_tarski(B_26)
      | ~ m1_subset_1(B_26,k1_zfmisc_1(k1_zfmisc_1(A_25))) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_2566,plain,(
    ! [A_149,B_150,C_151] :
      ( k5_setfam_1(A_149,k7_subset_1(k1_zfmisc_1(A_149),B_150,C_151)) = k3_tarski(k7_subset_1(k1_zfmisc_1(A_149),B_150,C_151))
      | ~ m1_subset_1(B_150,k1_zfmisc_1(k1_zfmisc_1(A_149))) ) ),
    inference(resolution,[status(thm)],[c_369,c_26])).

tff(c_2582,plain,(
    ! [C_151] : k5_setfam_1(u1_struct_0('#skF_1'),k7_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')),'#skF_2',C_151)) = k3_tarski(k7_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')),'#skF_2',C_151)) ),
    inference(resolution,[status(thm)],[c_32,c_2566])).

tff(c_2592,plain,(
    ! [C_151] : k5_setfam_1(u1_struct_0('#skF_1'),k4_xboole_0('#skF_2',C_151)) = k3_tarski(k4_xboole_0('#skF_2',C_151)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_549,c_549,c_2582])).

tff(c_272,plain,(
    ! [A_50,B_51] :
      ( k5_setfam_1(A_50,B_51) = k3_tarski(B_51)
      | ~ m1_subset_1(B_51,k1_zfmisc_1(k1_zfmisc_1(A_50))) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_280,plain,(
    k5_setfam_1(u1_struct_0('#skF_1'),'#skF_2') = k3_tarski('#skF_2') ),
    inference(resolution,[status(thm)],[c_32,c_272])).

tff(c_659,plain,(
    ! [A_77,B_78] :
      ( m1_subset_1(k5_setfam_1(A_77,B_78),k1_zfmisc_1(A_77))
      | ~ m1_subset_1(B_78,k1_zfmisc_1(k1_zfmisc_1(A_77))) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_22,plain,(
    ! [A_20,B_21,C_22] :
      ( k7_subset_1(A_20,B_21,C_22) = k4_xboole_0(B_21,C_22)
      | ~ m1_subset_1(B_21,k1_zfmisc_1(A_20)) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_1756,plain,(
    ! [A_120,B_121,C_122] :
      ( k7_subset_1(A_120,k5_setfam_1(A_120,B_121),C_122) = k4_xboole_0(k5_setfam_1(A_120,B_121),C_122)
      | ~ m1_subset_1(B_121,k1_zfmisc_1(k1_zfmisc_1(A_120))) ) ),
    inference(resolution,[status(thm)],[c_659,c_22])).

tff(c_1772,plain,(
    ! [C_122] : k7_subset_1(u1_struct_0('#skF_1'),k5_setfam_1(u1_struct_0('#skF_1'),'#skF_2'),C_122) = k4_xboole_0(k5_setfam_1(u1_struct_0('#skF_1'),'#skF_2'),C_122) ),
    inference(resolution,[status(thm)],[c_32,c_1756])).

tff(c_1781,plain,(
    ! [C_122] : k7_subset_1(u1_struct_0('#skF_1'),k3_tarski('#skF_2'),C_122) = k4_xboole_0(k3_tarski('#skF_2'),C_122) ),
    inference(demodulation,[status(thm),theory(equality)],[c_280,c_280,c_1772])).

tff(c_30,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_279,plain,(
    k5_setfam_1(u1_struct_0('#skF_1'),'#skF_3') = k3_tarski('#skF_3') ),
    inference(resolution,[status(thm)],[c_30,c_272])).

tff(c_28,plain,(
    ~ r1_tarski(k7_subset_1(u1_struct_0('#skF_1'),k5_setfam_1(u1_struct_0('#skF_1'),'#skF_2'),k5_setfam_1(u1_struct_0('#skF_1'),'#skF_3')),k5_setfam_1(u1_struct_0('#skF_1'),k7_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')),'#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_281,plain,(
    ~ r1_tarski(k7_subset_1(u1_struct_0('#skF_1'),k5_setfam_1(u1_struct_0('#skF_1'),'#skF_2'),k3_tarski('#skF_3')),k5_setfam_1(u1_struct_0('#skF_1'),k7_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')),'#skF_2','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_279,c_28])).

tff(c_458,plain,(
    ~ r1_tarski(k7_subset_1(u1_struct_0('#skF_1'),k3_tarski('#skF_2'),k3_tarski('#skF_3')),k5_setfam_1(u1_struct_0('#skF_1'),k7_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')),'#skF_2','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_280,c_281])).

tff(c_726,plain,(
    ~ r1_tarski(k7_subset_1(u1_struct_0('#skF_1'),k3_tarski('#skF_2'),k3_tarski('#skF_3')),k5_setfam_1(u1_struct_0('#skF_1'),k4_xboole_0('#skF_2','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_549,c_458])).

tff(c_1838,plain,(
    ~ r1_tarski(k4_xboole_0(k3_tarski('#skF_2'),k3_tarski('#skF_3')),k5_setfam_1(u1_struct_0('#skF_1'),k4_xboole_0('#skF_2','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1781,c_726])).

tff(c_6025,plain,(
    ~ r1_tarski(k4_xboole_0(k3_tarski('#skF_2'),k3_tarski('#skF_3')),k3_tarski(k4_xboole_0('#skF_2','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2592,c_1838])).

tff(c_6028,plain,(
    ~ r1_tarski(k3_tarski('#skF_2'),k2_xboole_0(k3_tarski('#skF_3'),k3_tarski(k4_xboole_0('#skF_2','#skF_3')))) ),
    inference(resolution,[status(thm)],[c_14,c_6025])).

tff(c_6032,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_316,c_12,c_18,c_6028])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:13:04 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.19/2.02  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.19/2.02  
% 5.19/2.02  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.19/2.03  %$ r1_tarski > m1_subset_1 > l1_struct_0 > k7_subset_1 > k5_setfam_1 > k4_xboole_0 > k2_xboole_0 > #nlpp > u1_struct_0 > k3_tarski > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1
% 5.19/2.03  
% 5.19/2.03  %Foreground sorts:
% 5.19/2.03  
% 5.19/2.03  
% 5.19/2.03  %Background operators:
% 5.19/2.03  
% 5.19/2.03  
% 5.19/2.03  %Foreground operators:
% 5.19/2.03  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.19/2.03  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 5.19/2.03  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.19/2.03  tff('#skF_2', type, '#skF_2': $i).
% 5.19/2.03  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 5.19/2.03  tff('#skF_3', type, '#skF_3': $i).
% 5.19/2.03  tff('#skF_1', type, '#skF_1': $i).
% 5.19/2.03  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.19/2.03  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 5.19/2.03  tff(k5_setfam_1, type, k5_setfam_1: ($i * $i) > $i).
% 5.19/2.03  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.19/2.03  tff(k3_tarski, type, k3_tarski: $i > $i).
% 5.19/2.03  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.19/2.03  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 5.19/2.03  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 5.19/2.03  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.19/2.03  
% 5.19/2.04  tff(f_49, axiom, (![A, B]: (k3_tarski(k2_xboole_0(A, B)) = k2_xboole_0(k3_tarski(A), k3_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t96_zfmisc_1)).
% 5.19/2.04  tff(f_39, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 5.19/2.04  tff(f_33, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 5.19/2.04  tff(f_47, axiom, (![A, B, C]: (r1_tarski(k4_xboole_0(A, B), C) => r1_tarski(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_xboole_1)).
% 5.19/2.04  tff(f_43, axiom, (![A, B, C]: (r1_tarski(A, k2_xboole_0(B, C)) => r1_tarski(k4_xboole_0(A, B), C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_xboole_1)).
% 5.19/2.04  tff(f_76, negated_conjecture, ~(![A]: (l1_struct_0(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => r1_tarski(k7_subset_1(u1_struct_0(A), k5_setfam_1(u1_struct_0(A), B), k5_setfam_1(u1_struct_0(A), C)), k5_setfam_1(u1_struct_0(A), k7_subset_1(k1_zfmisc_1(u1_struct_0(A)), B, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_tops_2)).
% 5.19/2.04  tff(f_57, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 5.19/2.04  tff(f_53, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k7_subset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_subset_1)).
% 5.19/2.04  tff(f_65, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (k5_setfam_1(A, B) = k3_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k5_setfam_1)).
% 5.19/2.04  tff(f_61, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => m1_subset_1(k5_setfam_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k5_setfam_1)).
% 5.19/2.04  tff(c_18, plain, (![A_15, B_16]: (k2_xboole_0(k3_tarski(A_15), k3_tarski(B_16))=k3_tarski(k2_xboole_0(A_15, B_16)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 5.19/2.04  tff(c_12, plain, (![A_7, B_8]: (k2_xboole_0(A_7, k4_xboole_0(B_8, A_7))=k2_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_39])).
% 5.19/2.04  tff(c_8, plain, (![B_4]: (r1_tarski(B_4, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 5.19/2.04  tff(c_290, plain, (![A_52, B_53, C_54]: (r1_tarski(A_52, k2_xboole_0(B_53, C_54)) | ~r1_tarski(k4_xboole_0(A_52, B_53), C_54))), inference(cnfTransformation, [status(thm)], [f_47])).
% 5.19/2.04  tff(c_297, plain, (![A_52, B_53]: (r1_tarski(A_52, k2_xboole_0(B_53, k4_xboole_0(A_52, B_53))))), inference(resolution, [status(thm)], [c_8, c_290])).
% 5.19/2.04  tff(c_301, plain, (![A_55, B_56]: (r1_tarski(A_55, k2_xboole_0(B_56, A_55)))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_297])).
% 5.19/2.04  tff(c_316, plain, (![B_16, A_15]: (r1_tarski(k3_tarski(B_16), k3_tarski(k2_xboole_0(A_15, B_16))))), inference(superposition, [status(thm), theory('equality')], [c_18, c_301])).
% 5.19/2.04  tff(c_14, plain, (![A_9, B_10, C_11]: (r1_tarski(k4_xboole_0(A_9, B_10), C_11) | ~r1_tarski(A_9, k2_xboole_0(B_10, C_11)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 5.19/2.04  tff(c_32, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(cnfTransformation, [status(thm)], [f_76])).
% 5.19/2.04  tff(c_540, plain, (![A_69, B_70, C_71]: (k7_subset_1(A_69, B_70, C_71)=k4_xboole_0(B_70, C_71) | ~m1_subset_1(B_70, k1_zfmisc_1(A_69)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 5.19/2.04  tff(c_549, plain, (![C_71]: (k7_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')), '#skF_2', C_71)=k4_xboole_0('#skF_2', C_71))), inference(resolution, [status(thm)], [c_32, c_540])).
% 5.19/2.04  tff(c_369, plain, (![A_59, B_60, C_61]: (m1_subset_1(k7_subset_1(A_59, B_60, C_61), k1_zfmisc_1(A_59)) | ~m1_subset_1(B_60, k1_zfmisc_1(A_59)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 5.19/2.04  tff(c_26, plain, (![A_25, B_26]: (k5_setfam_1(A_25, B_26)=k3_tarski(B_26) | ~m1_subset_1(B_26, k1_zfmisc_1(k1_zfmisc_1(A_25))))), inference(cnfTransformation, [status(thm)], [f_65])).
% 5.19/2.04  tff(c_2566, plain, (![A_149, B_150, C_151]: (k5_setfam_1(A_149, k7_subset_1(k1_zfmisc_1(A_149), B_150, C_151))=k3_tarski(k7_subset_1(k1_zfmisc_1(A_149), B_150, C_151)) | ~m1_subset_1(B_150, k1_zfmisc_1(k1_zfmisc_1(A_149))))), inference(resolution, [status(thm)], [c_369, c_26])).
% 5.19/2.04  tff(c_2582, plain, (![C_151]: (k5_setfam_1(u1_struct_0('#skF_1'), k7_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')), '#skF_2', C_151))=k3_tarski(k7_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')), '#skF_2', C_151)))), inference(resolution, [status(thm)], [c_32, c_2566])).
% 5.19/2.04  tff(c_2592, plain, (![C_151]: (k5_setfam_1(u1_struct_0('#skF_1'), k4_xboole_0('#skF_2', C_151))=k3_tarski(k4_xboole_0('#skF_2', C_151)))), inference(demodulation, [status(thm), theory('equality')], [c_549, c_549, c_2582])).
% 5.19/2.04  tff(c_272, plain, (![A_50, B_51]: (k5_setfam_1(A_50, B_51)=k3_tarski(B_51) | ~m1_subset_1(B_51, k1_zfmisc_1(k1_zfmisc_1(A_50))))), inference(cnfTransformation, [status(thm)], [f_65])).
% 5.19/2.04  tff(c_280, plain, (k5_setfam_1(u1_struct_0('#skF_1'), '#skF_2')=k3_tarski('#skF_2')), inference(resolution, [status(thm)], [c_32, c_272])).
% 5.19/2.04  tff(c_659, plain, (![A_77, B_78]: (m1_subset_1(k5_setfam_1(A_77, B_78), k1_zfmisc_1(A_77)) | ~m1_subset_1(B_78, k1_zfmisc_1(k1_zfmisc_1(A_77))))), inference(cnfTransformation, [status(thm)], [f_61])).
% 5.19/2.04  tff(c_22, plain, (![A_20, B_21, C_22]: (k7_subset_1(A_20, B_21, C_22)=k4_xboole_0(B_21, C_22) | ~m1_subset_1(B_21, k1_zfmisc_1(A_20)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 5.19/2.04  tff(c_1756, plain, (![A_120, B_121, C_122]: (k7_subset_1(A_120, k5_setfam_1(A_120, B_121), C_122)=k4_xboole_0(k5_setfam_1(A_120, B_121), C_122) | ~m1_subset_1(B_121, k1_zfmisc_1(k1_zfmisc_1(A_120))))), inference(resolution, [status(thm)], [c_659, c_22])).
% 5.19/2.04  tff(c_1772, plain, (![C_122]: (k7_subset_1(u1_struct_0('#skF_1'), k5_setfam_1(u1_struct_0('#skF_1'), '#skF_2'), C_122)=k4_xboole_0(k5_setfam_1(u1_struct_0('#skF_1'), '#skF_2'), C_122))), inference(resolution, [status(thm)], [c_32, c_1756])).
% 5.19/2.04  tff(c_1781, plain, (![C_122]: (k7_subset_1(u1_struct_0('#skF_1'), k3_tarski('#skF_2'), C_122)=k4_xboole_0(k3_tarski('#skF_2'), C_122))), inference(demodulation, [status(thm), theory('equality')], [c_280, c_280, c_1772])).
% 5.19/2.04  tff(c_30, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(cnfTransformation, [status(thm)], [f_76])).
% 5.19/2.04  tff(c_279, plain, (k5_setfam_1(u1_struct_0('#skF_1'), '#skF_3')=k3_tarski('#skF_3')), inference(resolution, [status(thm)], [c_30, c_272])).
% 5.19/2.04  tff(c_28, plain, (~r1_tarski(k7_subset_1(u1_struct_0('#skF_1'), k5_setfam_1(u1_struct_0('#skF_1'), '#skF_2'), k5_setfam_1(u1_struct_0('#skF_1'), '#skF_3')), k5_setfam_1(u1_struct_0('#skF_1'), k7_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')), '#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_76])).
% 5.19/2.04  tff(c_281, plain, (~r1_tarski(k7_subset_1(u1_struct_0('#skF_1'), k5_setfam_1(u1_struct_0('#skF_1'), '#skF_2'), k3_tarski('#skF_3')), k5_setfam_1(u1_struct_0('#skF_1'), k7_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')), '#skF_2', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_279, c_28])).
% 5.19/2.04  tff(c_458, plain, (~r1_tarski(k7_subset_1(u1_struct_0('#skF_1'), k3_tarski('#skF_2'), k3_tarski('#skF_3')), k5_setfam_1(u1_struct_0('#skF_1'), k7_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')), '#skF_2', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_280, c_281])).
% 5.19/2.04  tff(c_726, plain, (~r1_tarski(k7_subset_1(u1_struct_0('#skF_1'), k3_tarski('#skF_2'), k3_tarski('#skF_3')), k5_setfam_1(u1_struct_0('#skF_1'), k4_xboole_0('#skF_2', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_549, c_458])).
% 5.19/2.04  tff(c_1838, plain, (~r1_tarski(k4_xboole_0(k3_tarski('#skF_2'), k3_tarski('#skF_3')), k5_setfam_1(u1_struct_0('#skF_1'), k4_xboole_0('#skF_2', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_1781, c_726])).
% 5.19/2.04  tff(c_6025, plain, (~r1_tarski(k4_xboole_0(k3_tarski('#skF_2'), k3_tarski('#skF_3')), k3_tarski(k4_xboole_0('#skF_2', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_2592, c_1838])).
% 5.19/2.04  tff(c_6028, plain, (~r1_tarski(k3_tarski('#skF_2'), k2_xboole_0(k3_tarski('#skF_3'), k3_tarski(k4_xboole_0('#skF_2', '#skF_3'))))), inference(resolution, [status(thm)], [c_14, c_6025])).
% 5.19/2.04  tff(c_6032, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_316, c_12, c_18, c_6028])).
% 5.19/2.04  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.19/2.04  
% 5.19/2.04  Inference rules
% 5.19/2.04  ----------------------
% 5.19/2.04  #Ref     : 0
% 5.19/2.04  #Sup     : 1488
% 5.19/2.04  #Fact    : 0
% 5.19/2.04  #Define  : 0
% 5.19/2.04  #Split   : 0
% 5.19/2.04  #Chain   : 0
% 5.19/2.04  #Close   : 0
% 5.19/2.04  
% 5.19/2.04  Ordering : KBO
% 5.19/2.04  
% 5.19/2.04  Simplification rules
% 5.19/2.04  ----------------------
% 5.19/2.04  #Subsume      : 69
% 5.19/2.04  #Demod        : 1341
% 5.19/2.04  #Tautology    : 925
% 5.19/2.04  #SimpNegUnit  : 0
% 5.19/2.04  #BackRed      : 6
% 5.19/2.04  
% 5.19/2.04  #Partial instantiations: 0
% 5.19/2.04  #Strategies tried      : 1
% 5.19/2.04  
% 5.19/2.04  Timing (in seconds)
% 5.19/2.04  ----------------------
% 5.19/2.04  Preprocessing        : 0.31
% 5.19/2.04  Parsing              : 0.16
% 5.19/2.04  CNF conversion       : 0.02
% 5.19/2.04  Main loop            : 0.97
% 5.19/2.04  Inferencing          : 0.27
% 5.19/2.04  Reduction            : 0.45
% 5.19/2.04  Demodulation         : 0.38
% 5.19/2.04  BG Simplification    : 0.03
% 5.19/2.04  Subsumption          : 0.15
% 5.19/2.04  Abstraction          : 0.07
% 5.19/2.04  MUC search           : 0.00
% 5.19/2.04  Cooper               : 0.00
% 5.19/2.04  Total                : 1.31
% 5.19/2.04  Index Insertion      : 0.00
% 5.19/2.04  Index Deletion       : 0.00
% 5.19/2.04  Index Matching       : 0.00
% 5.19/2.04  BG Taut test         : 0.00
%------------------------------------------------------------------------------
