%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:22:36 EST 2020

% Result     : Theorem 3.31s
% Output     : CNFRefutation 3.31s
% Verified   : 
% Statistics : Number of formulae       :   59 (  87 expanded)
%              Number of leaves         :   26 (  41 expanded)
%              Depth                    :    9
%              Number of atoms          :   59 ( 122 expanded)
%              Number of equality atoms :   20 (  34 expanded)
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

tff(f_41,axiom,(
    ! [A,B] : k3_tarski(k2_xboole_0(A,B)) = k2_xboole_0(k3_tarski(A),k3_tarski(B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t96_zfmisc_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_35,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_33,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k2_xboole_0(B,C))
     => r1_tarski(k4_xboole_0(A,B),C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_xboole_1)).

tff(f_68,negated_conjecture,(
    ~ ! [A] :
        ( l1_struct_0(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
               => r1_tarski(k7_subset_1(u1_struct_0(A),k5_setfam_1(u1_struct_0(A),B),k5_setfam_1(u1_struct_0(A),C)),k5_setfam_1(u1_struct_0(A),k7_subset_1(k1_zfmisc_1(u1_struct_0(A)),B,C))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_tops_2)).

tff(f_57,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => k5_setfam_1(A,B) = k3_tarski(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k5_setfam_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => m1_subset_1(k5_setfam_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_setfam_1)).

tff(f_49,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k7_subset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_subset_1)).

tff(c_119,plain,(
    ! [A_42,B_43] : k2_xboole_0(k3_tarski(A_42),k3_tarski(B_43)) = k3_tarski(k2_xboole_0(A_42,B_43)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_30,plain,(
    ! [B_30,A_31] : k2_xboole_0(B_30,A_31) = k2_xboole_0(A_31,B_30) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_8,plain,(
    ! [A_8,B_9] : r1_tarski(A_8,k2_xboole_0(A_8,B_9)) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_45,plain,(
    ! [A_31,B_30] : r1_tarski(A_31,k2_xboole_0(B_30,A_31)) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_8])).

tff(c_131,plain,(
    ! [B_43,A_42] : r1_tarski(k3_tarski(B_43),k3_tarski(k2_xboole_0(A_42,B_43))) ),
    inference(superposition,[status(thm),theory(equality)],[c_119,c_45])).

tff(c_4,plain,(
    ! [A_3,B_4] : k2_xboole_0(A_3,k4_xboole_0(B_4,A_3)) = k2_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_12,plain,(
    ! [A_12,B_13] : k2_xboole_0(k3_tarski(A_12),k3_tarski(B_13)) = k3_tarski(k2_xboole_0(A_12,B_13)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_6,plain,(
    ! [A_5,B_6,C_7] :
      ( r1_tarski(k4_xboole_0(A_5,B_6),C_7)
      | ~ r1_tarski(A_5,k2_xboole_0(B_6,C_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_26,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_184,plain,(
    ! [A_51,B_52] :
      ( k5_setfam_1(A_51,B_52) = k3_tarski(B_52)
      | ~ m1_subset_1(B_52,k1_zfmisc_1(k1_zfmisc_1(A_51))) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_192,plain,(
    k5_setfam_1(u1_struct_0('#skF_1'),'#skF_2') = k3_tarski('#skF_2') ),
    inference(resolution,[status(thm)],[c_26,c_184])).

tff(c_18,plain,(
    ! [A_20,B_21] :
      ( m1_subset_1(k5_setfam_1(A_20,B_21),k1_zfmisc_1(A_20))
      | ~ m1_subset_1(B_21,k1_zfmisc_1(k1_zfmisc_1(A_20))) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_473,plain,(
    ! [A_66,B_67,C_68] :
      ( k7_subset_1(A_66,B_67,C_68) = k4_xboole_0(B_67,C_68)
      | ~ m1_subset_1(B_67,k1_zfmisc_1(A_66)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_657,plain,(
    ! [A_85,B_86,C_87] :
      ( k7_subset_1(A_85,k5_setfam_1(A_85,B_86),C_87) = k4_xboole_0(k5_setfam_1(A_85,B_86),C_87)
      | ~ m1_subset_1(B_86,k1_zfmisc_1(k1_zfmisc_1(A_85))) ) ),
    inference(resolution,[status(thm)],[c_18,c_473])).

tff(c_671,plain,(
    ! [C_87] : k7_subset_1(u1_struct_0('#skF_1'),k5_setfam_1(u1_struct_0('#skF_1'),'#skF_2'),C_87) = k4_xboole_0(k5_setfam_1(u1_struct_0('#skF_1'),'#skF_2'),C_87) ),
    inference(resolution,[status(thm)],[c_26,c_657])).

tff(c_680,plain,(
    ! [C_87] : k7_subset_1(u1_struct_0('#skF_1'),k3_tarski('#skF_2'),C_87) = k4_xboole_0(k3_tarski('#skF_2'),C_87) ),
    inference(demodulation,[status(thm),theory(equality)],[c_192,c_192,c_671])).

tff(c_515,plain,(
    ! [C_71] : k7_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')),'#skF_2',C_71) = k4_xboole_0('#skF_2',C_71) ),
    inference(resolution,[status(thm)],[c_26,c_473])).

tff(c_14,plain,(
    ! [A_14,B_15,C_16] :
      ( m1_subset_1(k7_subset_1(A_14,B_15,C_16),k1_zfmisc_1(A_14))
      | ~ m1_subset_1(B_15,k1_zfmisc_1(A_14)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_521,plain,(
    ! [C_71] :
      ( m1_subset_1(k4_xboole_0('#skF_2',C_71),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))
      | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_515,c_14])).

tff(c_529,plain,(
    ! [C_72] : m1_subset_1(k4_xboole_0('#skF_2',C_72),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_521])).

tff(c_20,plain,(
    ! [A_22,B_23] :
      ( k5_setfam_1(A_22,B_23) = k3_tarski(B_23)
      | ~ m1_subset_1(B_23,k1_zfmisc_1(k1_zfmisc_1(A_22))) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_536,plain,(
    ! [C_72] : k5_setfam_1(u1_struct_0('#skF_1'),k4_xboole_0('#skF_2',C_72)) = k3_tarski(k4_xboole_0('#skF_2',C_72)) ),
    inference(resolution,[status(thm)],[c_529,c_20])).

tff(c_491,plain,(
    ! [C_68] : k7_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')),'#skF_2',C_68) = k4_xboole_0('#skF_2',C_68) ),
    inference(resolution,[status(thm)],[c_26,c_473])).

tff(c_24,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_191,plain,(
    k5_setfam_1(u1_struct_0('#skF_1'),'#skF_3') = k3_tarski('#skF_3') ),
    inference(resolution,[status(thm)],[c_24,c_184])).

tff(c_22,plain,(
    ~ r1_tarski(k7_subset_1(u1_struct_0('#skF_1'),k5_setfam_1(u1_struct_0('#skF_1'),'#skF_2'),k5_setfam_1(u1_struct_0('#skF_1'),'#skF_3')),k5_setfam_1(u1_struct_0('#skF_1'),k7_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')),'#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_193,plain,(
    ~ r1_tarski(k7_subset_1(u1_struct_0('#skF_1'),k5_setfam_1(u1_struct_0('#skF_1'),'#skF_2'),k3_tarski('#skF_3')),k5_setfam_1(u1_struct_0('#skF_1'),k7_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')),'#skF_2','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_191,c_22])).

tff(c_391,plain,(
    ~ r1_tarski(k7_subset_1(u1_struct_0('#skF_1'),k3_tarski('#skF_2'),k3_tarski('#skF_3')),k5_setfam_1(u1_struct_0('#skF_1'),k7_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')),'#skF_2','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_192,c_193])).

tff(c_514,plain,(
    ~ r1_tarski(k7_subset_1(u1_struct_0('#skF_1'),k3_tarski('#skF_2'),k3_tarski('#skF_3')),k5_setfam_1(u1_struct_0('#skF_1'),k4_xboole_0('#skF_2','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_491,c_391])).

tff(c_577,plain,(
    ~ r1_tarski(k7_subset_1(u1_struct_0('#skF_1'),k3_tarski('#skF_2'),k3_tarski('#skF_3')),k3_tarski(k4_xboole_0('#skF_2','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_536,c_514])).

tff(c_1352,plain,(
    ~ r1_tarski(k4_xboole_0(k3_tarski('#skF_2'),k3_tarski('#skF_3')),k3_tarski(k4_xboole_0('#skF_2','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_680,c_577])).

tff(c_1355,plain,(
    ~ r1_tarski(k3_tarski('#skF_2'),k2_xboole_0(k3_tarski('#skF_3'),k3_tarski(k4_xboole_0('#skF_2','#skF_3')))) ),
    inference(resolution,[status(thm)],[c_6,c_1352])).

tff(c_1359,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_131,c_4,c_12,c_1355])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.09/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.09/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n010.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 11:47:29 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.31/1.49  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.31/1.50  
% 3.31/1.50  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.31/1.50  %$ r1_tarski > m1_subset_1 > l1_struct_0 > k7_subset_1 > k5_setfam_1 > k4_xboole_0 > k2_xboole_0 > #nlpp > u1_struct_0 > k3_tarski > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1
% 3.31/1.50  
% 3.31/1.50  %Foreground sorts:
% 3.31/1.50  
% 3.31/1.50  
% 3.31/1.50  %Background operators:
% 3.31/1.50  
% 3.31/1.50  
% 3.31/1.50  %Foreground operators:
% 3.31/1.50  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.31/1.50  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.31/1.50  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.31/1.50  tff('#skF_2', type, '#skF_2': $i).
% 3.31/1.50  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 3.31/1.50  tff('#skF_3', type, '#skF_3': $i).
% 3.31/1.50  tff('#skF_1', type, '#skF_1': $i).
% 3.31/1.50  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.31/1.50  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 3.31/1.50  tff(k5_setfam_1, type, k5_setfam_1: ($i * $i) > $i).
% 3.31/1.50  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.31/1.50  tff(k3_tarski, type, k3_tarski: $i > $i).
% 3.31/1.50  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.31/1.50  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.31/1.50  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.31/1.50  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.31/1.50  
% 3.31/1.51  tff(f_41, axiom, (![A, B]: (k3_tarski(k2_xboole_0(A, B)) = k2_xboole_0(k3_tarski(A), k3_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t96_zfmisc_1)).
% 3.31/1.51  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 3.31/1.51  tff(f_35, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 3.31/1.51  tff(f_29, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 3.31/1.51  tff(f_33, axiom, (![A, B, C]: (r1_tarski(A, k2_xboole_0(B, C)) => r1_tarski(k4_xboole_0(A, B), C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_xboole_1)).
% 3.31/1.51  tff(f_68, negated_conjecture, ~(![A]: (l1_struct_0(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => r1_tarski(k7_subset_1(u1_struct_0(A), k5_setfam_1(u1_struct_0(A), B), k5_setfam_1(u1_struct_0(A), C)), k5_setfam_1(u1_struct_0(A), k7_subset_1(k1_zfmisc_1(u1_struct_0(A)), B, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_tops_2)).
% 3.31/1.51  tff(f_57, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (k5_setfam_1(A, B) = k3_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k5_setfam_1)).
% 3.31/1.51  tff(f_53, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => m1_subset_1(k5_setfam_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k5_setfam_1)).
% 3.31/1.51  tff(f_49, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 3.31/1.51  tff(f_45, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k7_subset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_subset_1)).
% 3.31/1.51  tff(c_119, plain, (![A_42, B_43]: (k2_xboole_0(k3_tarski(A_42), k3_tarski(B_43))=k3_tarski(k2_xboole_0(A_42, B_43)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.31/1.51  tff(c_30, plain, (![B_30, A_31]: (k2_xboole_0(B_30, A_31)=k2_xboole_0(A_31, B_30))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.31/1.51  tff(c_8, plain, (![A_8, B_9]: (r1_tarski(A_8, k2_xboole_0(A_8, B_9)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.31/1.51  tff(c_45, plain, (![A_31, B_30]: (r1_tarski(A_31, k2_xboole_0(B_30, A_31)))), inference(superposition, [status(thm), theory('equality')], [c_30, c_8])).
% 3.31/1.51  tff(c_131, plain, (![B_43, A_42]: (r1_tarski(k3_tarski(B_43), k3_tarski(k2_xboole_0(A_42, B_43))))), inference(superposition, [status(thm), theory('equality')], [c_119, c_45])).
% 3.31/1.51  tff(c_4, plain, (![A_3, B_4]: (k2_xboole_0(A_3, k4_xboole_0(B_4, A_3))=k2_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.31/1.51  tff(c_12, plain, (![A_12, B_13]: (k2_xboole_0(k3_tarski(A_12), k3_tarski(B_13))=k3_tarski(k2_xboole_0(A_12, B_13)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.31/1.51  tff(c_6, plain, (![A_5, B_6, C_7]: (r1_tarski(k4_xboole_0(A_5, B_6), C_7) | ~r1_tarski(A_5, k2_xboole_0(B_6, C_7)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.31/1.51  tff(c_26, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.31/1.51  tff(c_184, plain, (![A_51, B_52]: (k5_setfam_1(A_51, B_52)=k3_tarski(B_52) | ~m1_subset_1(B_52, k1_zfmisc_1(k1_zfmisc_1(A_51))))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.31/1.51  tff(c_192, plain, (k5_setfam_1(u1_struct_0('#skF_1'), '#skF_2')=k3_tarski('#skF_2')), inference(resolution, [status(thm)], [c_26, c_184])).
% 3.31/1.51  tff(c_18, plain, (![A_20, B_21]: (m1_subset_1(k5_setfam_1(A_20, B_21), k1_zfmisc_1(A_20)) | ~m1_subset_1(B_21, k1_zfmisc_1(k1_zfmisc_1(A_20))))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.31/1.51  tff(c_473, plain, (![A_66, B_67, C_68]: (k7_subset_1(A_66, B_67, C_68)=k4_xboole_0(B_67, C_68) | ~m1_subset_1(B_67, k1_zfmisc_1(A_66)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.31/1.51  tff(c_657, plain, (![A_85, B_86, C_87]: (k7_subset_1(A_85, k5_setfam_1(A_85, B_86), C_87)=k4_xboole_0(k5_setfam_1(A_85, B_86), C_87) | ~m1_subset_1(B_86, k1_zfmisc_1(k1_zfmisc_1(A_85))))), inference(resolution, [status(thm)], [c_18, c_473])).
% 3.31/1.51  tff(c_671, plain, (![C_87]: (k7_subset_1(u1_struct_0('#skF_1'), k5_setfam_1(u1_struct_0('#skF_1'), '#skF_2'), C_87)=k4_xboole_0(k5_setfam_1(u1_struct_0('#skF_1'), '#skF_2'), C_87))), inference(resolution, [status(thm)], [c_26, c_657])).
% 3.31/1.51  tff(c_680, plain, (![C_87]: (k7_subset_1(u1_struct_0('#skF_1'), k3_tarski('#skF_2'), C_87)=k4_xboole_0(k3_tarski('#skF_2'), C_87))), inference(demodulation, [status(thm), theory('equality')], [c_192, c_192, c_671])).
% 3.31/1.51  tff(c_515, plain, (![C_71]: (k7_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')), '#skF_2', C_71)=k4_xboole_0('#skF_2', C_71))), inference(resolution, [status(thm)], [c_26, c_473])).
% 3.31/1.51  tff(c_14, plain, (![A_14, B_15, C_16]: (m1_subset_1(k7_subset_1(A_14, B_15, C_16), k1_zfmisc_1(A_14)) | ~m1_subset_1(B_15, k1_zfmisc_1(A_14)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.31/1.51  tff(c_521, plain, (![C_71]: (m1_subset_1(k4_xboole_0('#skF_2', C_71), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) | ~m1_subset_1('#skF_2', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))))), inference(superposition, [status(thm), theory('equality')], [c_515, c_14])).
% 3.31/1.51  tff(c_529, plain, (![C_72]: (m1_subset_1(k4_xboole_0('#skF_2', C_72), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_521])).
% 3.31/1.51  tff(c_20, plain, (![A_22, B_23]: (k5_setfam_1(A_22, B_23)=k3_tarski(B_23) | ~m1_subset_1(B_23, k1_zfmisc_1(k1_zfmisc_1(A_22))))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.31/1.51  tff(c_536, plain, (![C_72]: (k5_setfam_1(u1_struct_0('#skF_1'), k4_xboole_0('#skF_2', C_72))=k3_tarski(k4_xboole_0('#skF_2', C_72)))), inference(resolution, [status(thm)], [c_529, c_20])).
% 3.31/1.51  tff(c_491, plain, (![C_68]: (k7_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')), '#skF_2', C_68)=k4_xboole_0('#skF_2', C_68))), inference(resolution, [status(thm)], [c_26, c_473])).
% 3.31/1.51  tff(c_24, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.31/1.51  tff(c_191, plain, (k5_setfam_1(u1_struct_0('#skF_1'), '#skF_3')=k3_tarski('#skF_3')), inference(resolution, [status(thm)], [c_24, c_184])).
% 3.31/1.51  tff(c_22, plain, (~r1_tarski(k7_subset_1(u1_struct_0('#skF_1'), k5_setfam_1(u1_struct_0('#skF_1'), '#skF_2'), k5_setfam_1(u1_struct_0('#skF_1'), '#skF_3')), k5_setfam_1(u1_struct_0('#skF_1'), k7_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')), '#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.31/1.51  tff(c_193, plain, (~r1_tarski(k7_subset_1(u1_struct_0('#skF_1'), k5_setfam_1(u1_struct_0('#skF_1'), '#skF_2'), k3_tarski('#skF_3')), k5_setfam_1(u1_struct_0('#skF_1'), k7_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')), '#skF_2', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_191, c_22])).
% 3.31/1.51  tff(c_391, plain, (~r1_tarski(k7_subset_1(u1_struct_0('#skF_1'), k3_tarski('#skF_2'), k3_tarski('#skF_3')), k5_setfam_1(u1_struct_0('#skF_1'), k7_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')), '#skF_2', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_192, c_193])).
% 3.31/1.51  tff(c_514, plain, (~r1_tarski(k7_subset_1(u1_struct_0('#skF_1'), k3_tarski('#skF_2'), k3_tarski('#skF_3')), k5_setfam_1(u1_struct_0('#skF_1'), k4_xboole_0('#skF_2', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_491, c_391])).
% 3.31/1.51  tff(c_577, plain, (~r1_tarski(k7_subset_1(u1_struct_0('#skF_1'), k3_tarski('#skF_2'), k3_tarski('#skF_3')), k3_tarski(k4_xboole_0('#skF_2', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_536, c_514])).
% 3.31/1.51  tff(c_1352, plain, (~r1_tarski(k4_xboole_0(k3_tarski('#skF_2'), k3_tarski('#skF_3')), k3_tarski(k4_xboole_0('#skF_2', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_680, c_577])).
% 3.31/1.51  tff(c_1355, plain, (~r1_tarski(k3_tarski('#skF_2'), k2_xboole_0(k3_tarski('#skF_3'), k3_tarski(k4_xboole_0('#skF_2', '#skF_3'))))), inference(resolution, [status(thm)], [c_6, c_1352])).
% 3.31/1.51  tff(c_1359, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_131, c_4, c_12, c_1355])).
% 3.31/1.51  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.31/1.51  
% 3.31/1.51  Inference rules
% 3.31/1.51  ----------------------
% 3.31/1.51  #Ref     : 0
% 3.31/1.51  #Sup     : 353
% 3.31/1.51  #Fact    : 0
% 3.31/1.51  #Define  : 0
% 3.31/1.51  #Split   : 0
% 3.31/1.51  #Chain   : 0
% 3.31/1.51  #Close   : 0
% 3.31/1.51  
% 3.31/1.51  Ordering : KBO
% 3.31/1.51  
% 3.31/1.51  Simplification rules
% 3.31/1.51  ----------------------
% 3.31/1.51  #Subsume      : 2
% 3.31/1.51  #Demod        : 156
% 3.31/1.51  #Tautology    : 158
% 3.31/1.51  #SimpNegUnit  : 0
% 3.31/1.51  #BackRed      : 3
% 3.31/1.51  
% 3.31/1.51  #Partial instantiations: 0
% 3.31/1.51  #Strategies tried      : 1
% 3.31/1.51  
% 3.31/1.51  Timing (in seconds)
% 3.31/1.51  ----------------------
% 3.31/1.51  Preprocessing        : 0.28
% 3.31/1.51  Parsing              : 0.15
% 3.31/1.51  CNF conversion       : 0.02
% 3.31/1.51  Main loop            : 0.47
% 3.31/1.51  Inferencing          : 0.14
% 3.31/1.51  Reduction            : 0.20
% 3.31/1.51  Demodulation         : 0.17
% 3.31/1.51  BG Simplification    : 0.02
% 3.31/1.51  Subsumption          : 0.08
% 3.31/1.51  Abstraction          : 0.03
% 3.31/1.52  MUC search           : 0.00
% 3.31/1.52  Cooper               : 0.00
% 3.31/1.52  Total                : 0.78
% 3.31/1.52  Index Insertion      : 0.00
% 3.31/1.52  Index Deletion       : 0.00
% 3.31/1.52  Index Matching       : 0.00
% 3.31/1.52  BG Taut test         : 0.00
%------------------------------------------------------------------------------
