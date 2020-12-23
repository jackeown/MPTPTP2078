%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:22:36 EST 2020

% Result     : Theorem 5.59s
% Output     : CNFRefutation 5.85s
% Verified   : 
% Statistics : Number of formulae       :   59 (  88 expanded)
%              Number of leaves         :   27 (  42 expanded)
%              Depth                    :    9
%              Number of atoms          :   61 ( 124 expanded)
%              Number of equality atoms :   17 (  32 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > m1_subset_1 > l1_struct_0 > k7_subset_1 > k5_setfam_1 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > u1_struct_0 > k3_tarski > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

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

tff(f_43,axiom,(
    ! [A,B] : k3_tarski(k2_xboole_0(A,B)) = k2_xboole_0(k3_tarski(A),k3_tarski(B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t96_zfmisc_1)).

tff(f_29,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k4_xboole_0(A,B),C)
     => r1_tarski(A,k2_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k2_xboole_0(B,C))
     => r1_tarski(k4_xboole_0(A,B),C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_xboole_1)).

tff(f_70,negated_conjecture,(
    ~ ! [A] :
        ( l1_struct_0(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
               => r1_tarski(k7_subset_1(u1_struct_0(A),k5_setfam_1(u1_struct_0(A),B),k5_setfam_1(u1_struct_0(A),C)),k5_setfam_1(u1_struct_0(A),k7_subset_1(k1_zfmisc_1(u1_struct_0(A)),B,C))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_tops_2)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

tff(f_47,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k7_subset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_subset_1)).

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

tff(c_14,plain,(
    ! [A_15,B_16] : k2_xboole_0(k3_tarski(A_15),k3_tarski(B_16)) = k3_tarski(k2_xboole_0(A_15,B_16)) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_4,plain,(
    ! [A_3,B_4] : r1_tarski(k4_xboole_0(A_3,B_4),A_3) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_259,plain,(
    ! [A_50,B_51,C_52] :
      ( r1_tarski(A_50,k2_xboole_0(B_51,C_52))
      | ~ r1_tarski(k4_xboole_0(A_50,B_51),C_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_268,plain,(
    ! [A_53,B_54] : r1_tarski(A_53,k2_xboole_0(B_54,A_53)) ),
    inference(resolution,[status(thm)],[c_4,c_259])).

tff(c_278,plain,(
    ! [B_16,A_15] : r1_tarski(k3_tarski(B_16),k3_tarski(k2_xboole_0(A_15,B_16))) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_268])).

tff(c_6,plain,(
    ! [A_5,B_6] : k2_xboole_0(A_5,k4_xboole_0(B_6,A_5)) = k2_xboole_0(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_8,plain,(
    ! [A_7,B_8,C_9] :
      ( r1_tarski(k4_xboole_0(A_7,B_8),C_9)
      | ~ r1_tarski(A_7,k2_xboole_0(B_8,C_9)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_28,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_334,plain,(
    ! [A_59,B_60,C_61] :
      ( k7_subset_1(A_59,B_60,C_61) = k4_xboole_0(B_60,C_61)
      | ~ m1_subset_1(B_60,k1_zfmisc_1(A_59)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_340,plain,(
    ! [C_61] : k7_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')),'#skF_2',C_61) = k4_xboole_0('#skF_2',C_61) ),
    inference(resolution,[status(thm)],[c_28,c_334])).

tff(c_532,plain,(
    ! [A_76,B_77,C_78] :
      ( m1_subset_1(k7_subset_1(A_76,B_77,C_78),k1_zfmisc_1(A_76))
      | ~ m1_subset_1(B_77,k1_zfmisc_1(A_76)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_541,plain,(
    ! [C_61] :
      ( m1_subset_1(k4_xboole_0('#skF_2',C_61),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))
      | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_340,c_532])).

tff(c_551,plain,(
    ! [C_79] : m1_subset_1(k4_xboole_0('#skF_2',C_79),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_541])).

tff(c_22,plain,(
    ! [A_25,B_26] :
      ( k5_setfam_1(A_25,B_26) = k3_tarski(B_26)
      | ~ m1_subset_1(B_26,k1_zfmisc_1(k1_zfmisc_1(A_25))) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_558,plain,(
    ! [C_79] : k5_setfam_1(u1_struct_0('#skF_1'),k4_xboole_0('#skF_2',C_79)) = k3_tarski(k4_xboole_0('#skF_2',C_79)) ),
    inference(resolution,[status(thm)],[c_551,c_22])).

tff(c_239,plain,(
    ! [A_45,B_46] :
      ( k5_setfam_1(A_45,B_46) = k3_tarski(B_46)
      | ~ m1_subset_1(B_46,k1_zfmisc_1(k1_zfmisc_1(A_45))) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_247,plain,(
    k5_setfam_1(u1_struct_0('#skF_1'),'#skF_2') = k3_tarski('#skF_2') ),
    inference(resolution,[status(thm)],[c_28,c_239])).

tff(c_444,plain,(
    ! [A_69,B_70] :
      ( m1_subset_1(k5_setfam_1(A_69,B_70),k1_zfmisc_1(A_69))
      | ~ m1_subset_1(B_70,k1_zfmisc_1(k1_zfmisc_1(A_69))) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_18,plain,(
    ! [A_20,B_21,C_22] :
      ( k7_subset_1(A_20,B_21,C_22) = k4_xboole_0(B_21,C_22)
      | ~ m1_subset_1(B_21,k1_zfmisc_1(A_20)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_1149,plain,(
    ! [A_115,B_116,C_117] :
      ( k7_subset_1(A_115,k5_setfam_1(A_115,B_116),C_117) = k4_xboole_0(k5_setfam_1(A_115,B_116),C_117)
      | ~ m1_subset_1(B_116,k1_zfmisc_1(k1_zfmisc_1(A_115))) ) ),
    inference(resolution,[status(thm)],[c_444,c_18])).

tff(c_1163,plain,(
    ! [C_117] : k7_subset_1(u1_struct_0('#skF_1'),k5_setfam_1(u1_struct_0('#skF_1'),'#skF_2'),C_117) = k4_xboole_0(k5_setfam_1(u1_struct_0('#skF_1'),'#skF_2'),C_117) ),
    inference(resolution,[status(thm)],[c_28,c_1149])).

tff(c_1172,plain,(
    ! [C_117] : k7_subset_1(u1_struct_0('#skF_1'),k3_tarski('#skF_2'),C_117) = k4_xboole_0(k3_tarski('#skF_2'),C_117) ),
    inference(demodulation,[status(thm),theory(equality)],[c_247,c_247,c_1163])).

tff(c_26,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_246,plain,(
    k5_setfam_1(u1_struct_0('#skF_1'),'#skF_3') = k3_tarski('#skF_3') ),
    inference(resolution,[status(thm)],[c_26,c_239])).

tff(c_24,plain,(
    ~ r1_tarski(k7_subset_1(u1_struct_0('#skF_1'),k5_setfam_1(u1_struct_0('#skF_1'),'#skF_2'),k5_setfam_1(u1_struct_0('#skF_1'),'#skF_3')),k5_setfam_1(u1_struct_0('#skF_1'),k7_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')),'#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_248,plain,(
    ~ r1_tarski(k7_subset_1(u1_struct_0('#skF_1'),k5_setfam_1(u1_struct_0('#skF_1'),'#skF_2'),k3_tarski('#skF_3')),k5_setfam_1(u1_struct_0('#skF_1'),k7_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')),'#skF_2','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_246,c_24])).

tff(c_258,plain,(
    ~ r1_tarski(k7_subset_1(u1_struct_0('#skF_1'),k3_tarski('#skF_2'),k3_tarski('#skF_3')),k5_setfam_1(u1_struct_0('#skF_1'),k7_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')),'#skF_2','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_247,c_248])).

tff(c_470,plain,(
    ~ r1_tarski(k7_subset_1(u1_struct_0('#skF_1'),k3_tarski('#skF_2'),k3_tarski('#skF_3')),k5_setfam_1(u1_struct_0('#skF_1'),k4_xboole_0('#skF_2','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_340,c_258])).

tff(c_1217,plain,(
    ~ r1_tarski(k4_xboole_0(k3_tarski('#skF_2'),k3_tarski('#skF_3')),k5_setfam_1(u1_struct_0('#skF_1'),k4_xboole_0('#skF_2','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1172,c_470])).

tff(c_2374,plain,(
    ~ r1_tarski(k4_xboole_0(k3_tarski('#skF_2'),k3_tarski('#skF_3')),k3_tarski(k4_xboole_0('#skF_2','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_558,c_1217])).

tff(c_2377,plain,(
    ~ r1_tarski(k3_tarski('#skF_2'),k2_xboole_0(k3_tarski('#skF_3'),k3_tarski(k4_xboole_0('#skF_2','#skF_3')))) ),
    inference(resolution,[status(thm)],[c_8,c_2374])).

tff(c_2381,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_278,c_6,c_14,c_2377])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.11  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.10/0.31  % Computer   : n013.cluster.edu
% 0.10/0.31  % Model      : x86_64 x86_64
% 0.10/0.31  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.10/0.31  % Memory     : 8042.1875MB
% 0.10/0.31  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.10/0.32  % CPULimit   : 60
% 0.10/0.32  % DateTime   : Tue Dec  1 10:42:39 EST 2020
% 0.10/0.32  % CPUTime    : 
% 0.10/0.32  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.59/2.65  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.59/2.66  
% 5.59/2.66  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.59/2.67  %$ r1_tarski > m1_subset_1 > l1_struct_0 > k7_subset_1 > k5_setfam_1 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > u1_struct_0 > k3_tarski > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1
% 5.59/2.67  
% 5.59/2.67  %Foreground sorts:
% 5.59/2.67  
% 5.59/2.67  
% 5.59/2.67  %Background operators:
% 5.59/2.67  
% 5.59/2.67  
% 5.59/2.67  %Foreground operators:
% 5.59/2.67  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.59/2.67  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 5.59/2.67  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.59/2.67  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 5.59/2.67  tff('#skF_2', type, '#skF_2': $i).
% 5.59/2.67  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 5.59/2.67  tff('#skF_3', type, '#skF_3': $i).
% 5.59/2.67  tff('#skF_1', type, '#skF_1': $i).
% 5.59/2.67  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.59/2.67  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 5.59/2.67  tff(k5_setfam_1, type, k5_setfam_1: ($i * $i) > $i).
% 5.59/2.67  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.59/2.67  tff(k3_tarski, type, k3_tarski: $i > $i).
% 5.59/2.67  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.59/2.67  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 5.59/2.67  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 5.59/2.67  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.59/2.67  
% 5.85/2.68  tff(f_43, axiom, (![A, B]: (k3_tarski(k2_xboole_0(A, B)) = k2_xboole_0(k3_tarski(A), k3_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t96_zfmisc_1)).
% 5.85/2.68  tff(f_29, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 5.85/2.68  tff(f_39, axiom, (![A, B, C]: (r1_tarski(k4_xboole_0(A, B), C) => r1_tarski(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_xboole_1)).
% 5.85/2.68  tff(f_31, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 5.85/2.68  tff(f_35, axiom, (![A, B, C]: (r1_tarski(A, k2_xboole_0(B, C)) => r1_tarski(k4_xboole_0(A, B), C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_xboole_1)).
% 5.85/2.68  tff(f_70, negated_conjecture, ~(![A]: (l1_struct_0(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => r1_tarski(k7_subset_1(u1_struct_0(A), k5_setfam_1(u1_struct_0(A), B), k5_setfam_1(u1_struct_0(A), C)), k5_setfam_1(u1_struct_0(A), k7_subset_1(k1_zfmisc_1(u1_struct_0(A)), B, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_tops_2)).
% 5.85/2.68  tff(f_51, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 5.85/2.68  tff(f_47, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k7_subset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_subset_1)).
% 5.85/2.68  tff(f_59, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (k5_setfam_1(A, B) = k3_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k5_setfam_1)).
% 5.85/2.68  tff(f_55, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => m1_subset_1(k5_setfam_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k5_setfam_1)).
% 5.85/2.68  tff(c_14, plain, (![A_15, B_16]: (k2_xboole_0(k3_tarski(A_15), k3_tarski(B_16))=k3_tarski(k2_xboole_0(A_15, B_16)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 5.85/2.68  tff(c_4, plain, (![A_3, B_4]: (r1_tarski(k4_xboole_0(A_3, B_4), A_3))), inference(cnfTransformation, [status(thm)], [f_29])).
% 5.85/2.68  tff(c_259, plain, (![A_50, B_51, C_52]: (r1_tarski(A_50, k2_xboole_0(B_51, C_52)) | ~r1_tarski(k4_xboole_0(A_50, B_51), C_52))), inference(cnfTransformation, [status(thm)], [f_39])).
% 5.85/2.68  tff(c_268, plain, (![A_53, B_54]: (r1_tarski(A_53, k2_xboole_0(B_54, A_53)))), inference(resolution, [status(thm)], [c_4, c_259])).
% 5.85/2.68  tff(c_278, plain, (![B_16, A_15]: (r1_tarski(k3_tarski(B_16), k3_tarski(k2_xboole_0(A_15, B_16))))), inference(superposition, [status(thm), theory('equality')], [c_14, c_268])).
% 5.85/2.68  tff(c_6, plain, (![A_5, B_6]: (k2_xboole_0(A_5, k4_xboole_0(B_6, A_5))=k2_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.85/2.68  tff(c_8, plain, (![A_7, B_8, C_9]: (r1_tarski(k4_xboole_0(A_7, B_8), C_9) | ~r1_tarski(A_7, k2_xboole_0(B_8, C_9)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 5.85/2.68  tff(c_28, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(cnfTransformation, [status(thm)], [f_70])).
% 5.85/2.68  tff(c_334, plain, (![A_59, B_60, C_61]: (k7_subset_1(A_59, B_60, C_61)=k4_xboole_0(B_60, C_61) | ~m1_subset_1(B_60, k1_zfmisc_1(A_59)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 5.85/2.68  tff(c_340, plain, (![C_61]: (k7_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')), '#skF_2', C_61)=k4_xboole_0('#skF_2', C_61))), inference(resolution, [status(thm)], [c_28, c_334])).
% 5.85/2.68  tff(c_532, plain, (![A_76, B_77, C_78]: (m1_subset_1(k7_subset_1(A_76, B_77, C_78), k1_zfmisc_1(A_76)) | ~m1_subset_1(B_77, k1_zfmisc_1(A_76)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 5.85/2.68  tff(c_541, plain, (![C_61]: (m1_subset_1(k4_xboole_0('#skF_2', C_61), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) | ~m1_subset_1('#skF_2', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))))), inference(superposition, [status(thm), theory('equality')], [c_340, c_532])).
% 5.85/2.68  tff(c_551, plain, (![C_79]: (m1_subset_1(k4_xboole_0('#skF_2', C_79), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_541])).
% 5.85/2.68  tff(c_22, plain, (![A_25, B_26]: (k5_setfam_1(A_25, B_26)=k3_tarski(B_26) | ~m1_subset_1(B_26, k1_zfmisc_1(k1_zfmisc_1(A_25))))), inference(cnfTransformation, [status(thm)], [f_59])).
% 5.85/2.68  tff(c_558, plain, (![C_79]: (k5_setfam_1(u1_struct_0('#skF_1'), k4_xboole_0('#skF_2', C_79))=k3_tarski(k4_xboole_0('#skF_2', C_79)))), inference(resolution, [status(thm)], [c_551, c_22])).
% 5.85/2.68  tff(c_239, plain, (![A_45, B_46]: (k5_setfam_1(A_45, B_46)=k3_tarski(B_46) | ~m1_subset_1(B_46, k1_zfmisc_1(k1_zfmisc_1(A_45))))), inference(cnfTransformation, [status(thm)], [f_59])).
% 5.85/2.68  tff(c_247, plain, (k5_setfam_1(u1_struct_0('#skF_1'), '#skF_2')=k3_tarski('#skF_2')), inference(resolution, [status(thm)], [c_28, c_239])).
% 5.85/2.68  tff(c_444, plain, (![A_69, B_70]: (m1_subset_1(k5_setfam_1(A_69, B_70), k1_zfmisc_1(A_69)) | ~m1_subset_1(B_70, k1_zfmisc_1(k1_zfmisc_1(A_69))))), inference(cnfTransformation, [status(thm)], [f_55])).
% 5.85/2.68  tff(c_18, plain, (![A_20, B_21, C_22]: (k7_subset_1(A_20, B_21, C_22)=k4_xboole_0(B_21, C_22) | ~m1_subset_1(B_21, k1_zfmisc_1(A_20)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 5.85/2.68  tff(c_1149, plain, (![A_115, B_116, C_117]: (k7_subset_1(A_115, k5_setfam_1(A_115, B_116), C_117)=k4_xboole_0(k5_setfam_1(A_115, B_116), C_117) | ~m1_subset_1(B_116, k1_zfmisc_1(k1_zfmisc_1(A_115))))), inference(resolution, [status(thm)], [c_444, c_18])).
% 5.85/2.68  tff(c_1163, plain, (![C_117]: (k7_subset_1(u1_struct_0('#skF_1'), k5_setfam_1(u1_struct_0('#skF_1'), '#skF_2'), C_117)=k4_xboole_0(k5_setfam_1(u1_struct_0('#skF_1'), '#skF_2'), C_117))), inference(resolution, [status(thm)], [c_28, c_1149])).
% 5.85/2.68  tff(c_1172, plain, (![C_117]: (k7_subset_1(u1_struct_0('#skF_1'), k3_tarski('#skF_2'), C_117)=k4_xboole_0(k3_tarski('#skF_2'), C_117))), inference(demodulation, [status(thm), theory('equality')], [c_247, c_247, c_1163])).
% 5.85/2.69  tff(c_26, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(cnfTransformation, [status(thm)], [f_70])).
% 5.85/2.69  tff(c_246, plain, (k5_setfam_1(u1_struct_0('#skF_1'), '#skF_3')=k3_tarski('#skF_3')), inference(resolution, [status(thm)], [c_26, c_239])).
% 5.85/2.69  tff(c_24, plain, (~r1_tarski(k7_subset_1(u1_struct_0('#skF_1'), k5_setfam_1(u1_struct_0('#skF_1'), '#skF_2'), k5_setfam_1(u1_struct_0('#skF_1'), '#skF_3')), k5_setfam_1(u1_struct_0('#skF_1'), k7_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')), '#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_70])).
% 5.85/2.69  tff(c_248, plain, (~r1_tarski(k7_subset_1(u1_struct_0('#skF_1'), k5_setfam_1(u1_struct_0('#skF_1'), '#skF_2'), k3_tarski('#skF_3')), k5_setfam_1(u1_struct_0('#skF_1'), k7_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')), '#skF_2', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_246, c_24])).
% 5.85/2.69  tff(c_258, plain, (~r1_tarski(k7_subset_1(u1_struct_0('#skF_1'), k3_tarski('#skF_2'), k3_tarski('#skF_3')), k5_setfam_1(u1_struct_0('#skF_1'), k7_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')), '#skF_2', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_247, c_248])).
% 5.85/2.69  tff(c_470, plain, (~r1_tarski(k7_subset_1(u1_struct_0('#skF_1'), k3_tarski('#skF_2'), k3_tarski('#skF_3')), k5_setfam_1(u1_struct_0('#skF_1'), k4_xboole_0('#skF_2', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_340, c_258])).
% 5.85/2.69  tff(c_1217, plain, (~r1_tarski(k4_xboole_0(k3_tarski('#skF_2'), k3_tarski('#skF_3')), k5_setfam_1(u1_struct_0('#skF_1'), k4_xboole_0('#skF_2', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_1172, c_470])).
% 5.85/2.69  tff(c_2374, plain, (~r1_tarski(k4_xboole_0(k3_tarski('#skF_2'), k3_tarski('#skF_3')), k3_tarski(k4_xboole_0('#skF_2', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_558, c_1217])).
% 5.85/2.69  tff(c_2377, plain, (~r1_tarski(k3_tarski('#skF_2'), k2_xboole_0(k3_tarski('#skF_3'), k3_tarski(k4_xboole_0('#skF_2', '#skF_3'))))), inference(resolution, [status(thm)], [c_8, c_2374])).
% 5.85/2.69  tff(c_2381, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_278, c_6, c_14, c_2377])).
% 5.85/2.69  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.85/2.69  
% 5.85/2.69  Inference rules
% 5.85/2.69  ----------------------
% 5.85/2.69  #Ref     : 0
% 5.85/2.69  #Sup     : 624
% 5.85/2.69  #Fact    : 0
% 5.85/2.69  #Define  : 0
% 5.85/2.69  #Split   : 0
% 5.85/2.69  #Chain   : 0
% 5.85/2.69  #Close   : 0
% 5.85/2.69  
% 5.85/2.69  Ordering : KBO
% 5.85/2.69  
% 5.85/2.69  Simplification rules
% 5.85/2.69  ----------------------
% 5.85/2.69  #Subsume      : 4
% 5.85/2.69  #Demod        : 273
% 5.85/2.69  #Tautology    : 202
% 5.85/2.69  #SimpNegUnit  : 0
% 5.85/2.69  #BackRed      : 3
% 5.85/2.69  
% 5.85/2.69  #Partial instantiations: 0
% 5.85/2.69  #Strategies tried      : 1
% 5.85/2.69  
% 5.85/2.69  Timing (in seconds)
% 5.85/2.69  ----------------------
% 5.85/2.69  Preprocessing        : 0.56
% 5.85/2.69  Parsing              : 0.33
% 5.85/2.69  CNF conversion       : 0.03
% 5.85/2.69  Main loop            : 1.22
% 5.85/2.69  Inferencing          : 0.36
% 5.85/2.69  Reduction            : 0.55
% 5.85/2.69  Demodulation         : 0.48
% 5.85/2.69  BG Simplification    : 0.05
% 5.85/2.69  Subsumption          : 0.20
% 5.85/2.69  Abstraction          : 0.06
% 5.85/2.69  MUC search           : 0.00
% 5.85/2.69  Cooper               : 0.00
% 5.85/2.69  Total                : 1.83
% 5.85/2.69  Index Insertion      : 0.00
% 5.85/2.69  Index Deletion       : 0.00
% 5.85/2.69  Index Matching       : 0.00
% 5.85/2.69  BG Taut test         : 0.00
%------------------------------------------------------------------------------
