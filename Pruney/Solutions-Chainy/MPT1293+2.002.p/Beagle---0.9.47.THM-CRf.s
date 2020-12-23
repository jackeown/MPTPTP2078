%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:22:35 EST 2020

% Result     : Theorem 3.46s
% Output     : CNFRefutation 3.46s
% Verified   : 
% Statistics : Number of formulae       :   65 (  89 expanded)
%              Number of leaves         :   28 (  42 expanded)
%              Depth                    :    9
%              Number of atoms          :   64 ( 118 expanded)
%              Number of equality atoms :   23 (  35 expanded)
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

tff(f_35,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_37,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_39,axiom,(
    ! [A,B] : k3_tarski(k2_xboole_0(A,B)) = k2_xboole_0(k3_tarski(A),k3_tarski(B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t96_zfmisc_1)).

tff(f_33,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k2_xboole_0(B,C))
     => r1_tarski(k4_xboole_0(A,B),C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_xboole_1)).

tff(f_66,negated_conjecture,(
    ~ ! [A] :
        ( l1_struct_0(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
               => r1_tarski(k7_subset_1(u1_struct_0(A),k5_setfam_1(u1_struct_0(A),B),k5_setfam_1(u1_struct_0(A),C)),k5_setfam_1(u1_struct_0(A),k7_subset_1(k1_zfmisc_1(u1_struct_0(A)),B,C))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_tops_2)).

tff(f_55,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => k5_setfam_1(A,B) = k3_tarski(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k5_setfam_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => m1_subset_1(k5_setfam_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_setfam_1)).

tff(f_47,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k7_subset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_subset_1)).

tff(c_8,plain,(
    ! [B_9,A_8] : k2_tarski(B_9,A_8) = k2_tarski(A_8,B_9) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_63,plain,(
    ! [A_32,B_33] : k3_tarski(k2_tarski(A_32,B_33)) = k2_xboole_0(A_32,B_33) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_78,plain,(
    ! [B_34,A_35] : k3_tarski(k2_tarski(B_34,A_35)) = k2_xboole_0(A_35,B_34) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_63])).

tff(c_10,plain,(
    ! [A_10,B_11] : k3_tarski(k2_tarski(A_10,B_11)) = k2_xboole_0(A_10,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_84,plain,(
    ! [B_34,A_35] : k2_xboole_0(B_34,A_35) = k2_xboole_0(A_35,B_34) ),
    inference(superposition,[status(thm),theory(equality)],[c_78,c_10])).

tff(c_177,plain,(
    ! [A_44,B_45] : k2_xboole_0(k3_tarski(A_44),k3_tarski(B_45)) = k3_tarski(k2_xboole_0(A_44,B_45)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_6,plain,(
    ! [A_6,B_7] : r1_tarski(A_6,k2_xboole_0(A_6,B_7)) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_219,plain,(
    ! [A_46,B_47] : r1_tarski(k3_tarski(A_46),k3_tarski(k2_xboole_0(A_46,B_47))) ),
    inference(superposition,[status(thm),theory(equality)],[c_177,c_6])).

tff(c_228,plain,(
    ! [A_35,B_34] : r1_tarski(k3_tarski(A_35),k3_tarski(k2_xboole_0(B_34,A_35))) ),
    inference(superposition,[status(thm),theory(equality)],[c_84,c_219])).

tff(c_2,plain,(
    ! [A_1,B_2] : k2_xboole_0(A_1,k4_xboole_0(B_2,A_1)) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_12,plain,(
    ! [A_12,B_13] : k2_xboole_0(k3_tarski(A_12),k3_tarski(B_13)) = k3_tarski(k2_xboole_0(A_12,B_13)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_4,plain,(
    ! [A_3,B_4,C_5] :
      ( r1_tarski(k4_xboole_0(A_3,B_4),C_5)
      | ~ r1_tarski(A_3,k2_xboole_0(B_4,C_5)) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_26,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_366,plain,(
    ! [A_59,B_60] :
      ( k5_setfam_1(A_59,B_60) = k3_tarski(B_60)
      | ~ m1_subset_1(B_60,k1_zfmisc_1(k1_zfmisc_1(A_59))) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_374,plain,(
    k5_setfam_1(u1_struct_0('#skF_1'),'#skF_2') = k3_tarski('#skF_2') ),
    inference(resolution,[status(thm)],[c_26,c_366])).

tff(c_585,plain,(
    ! [A_70,B_71] :
      ( m1_subset_1(k5_setfam_1(A_70,B_71),k1_zfmisc_1(A_70))
      | ~ m1_subset_1(B_71,k1_zfmisc_1(k1_zfmisc_1(A_70))) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_592,plain,
    ( m1_subset_1(k3_tarski('#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ),
    inference(superposition,[status(thm),theory(equality)],[c_374,c_585])).

tff(c_598,plain,(
    m1_subset_1(k3_tarski('#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_592])).

tff(c_629,plain,(
    ! [A_74,B_75,C_76] :
      ( k7_subset_1(A_74,B_75,C_76) = k4_xboole_0(B_75,C_76)
      | ~ m1_subset_1(B_75,k1_zfmisc_1(A_74)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_643,plain,(
    ! [C_76] : k7_subset_1(u1_struct_0('#skF_1'),k3_tarski('#skF_2'),C_76) = k4_xboole_0(k3_tarski('#skF_2'),C_76) ),
    inference(resolution,[status(thm)],[c_598,c_629])).

tff(c_671,plain,(
    ! [C_79] : k7_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')),'#skF_2',C_79) = k4_xboole_0('#skF_2',C_79) ),
    inference(resolution,[status(thm)],[c_26,c_629])).

tff(c_14,plain,(
    ! [A_14,B_15,C_16] :
      ( m1_subset_1(k7_subset_1(A_14,B_15,C_16),k1_zfmisc_1(A_14))
      | ~ m1_subset_1(B_15,k1_zfmisc_1(A_14)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_677,plain,(
    ! [C_79] :
      ( m1_subset_1(k4_xboole_0('#skF_2',C_79),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))
      | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_671,c_14])).

tff(c_685,plain,(
    ! [C_80] : m1_subset_1(k4_xboole_0('#skF_2',C_80),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_677])).

tff(c_20,plain,(
    ! [A_22,B_23] :
      ( k5_setfam_1(A_22,B_23) = k3_tarski(B_23)
      | ~ m1_subset_1(B_23,k1_zfmisc_1(k1_zfmisc_1(A_22))) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_692,plain,(
    ! [C_80] : k5_setfam_1(u1_struct_0('#skF_1'),k4_xboole_0('#skF_2',C_80)) = k3_tarski(k4_xboole_0('#skF_2',C_80)) ),
    inference(resolution,[status(thm)],[c_685,c_20])).

tff(c_647,plain,(
    ! [C_76] : k7_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')),'#skF_2',C_76) = k4_xboole_0('#skF_2',C_76) ),
    inference(resolution,[status(thm)],[c_26,c_629])).

tff(c_24,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_373,plain,(
    k5_setfam_1(u1_struct_0('#skF_1'),'#skF_3') = k3_tarski('#skF_3') ),
    inference(resolution,[status(thm)],[c_24,c_366])).

tff(c_22,plain,(
    ~ r1_tarski(k7_subset_1(u1_struct_0('#skF_1'),k5_setfam_1(u1_struct_0('#skF_1'),'#skF_2'),k5_setfam_1(u1_struct_0('#skF_1'),'#skF_3')),k5_setfam_1(u1_struct_0('#skF_1'),k7_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')),'#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_375,plain,(
    ~ r1_tarski(k7_subset_1(u1_struct_0('#skF_1'),k5_setfam_1(u1_struct_0('#skF_1'),'#skF_2'),k3_tarski('#skF_3')),k5_setfam_1(u1_struct_0('#skF_1'),k7_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')),'#skF_2','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_373,c_22])).

tff(c_513,plain,(
    ~ r1_tarski(k7_subset_1(u1_struct_0('#skF_1'),k3_tarski('#skF_2'),k3_tarski('#skF_3')),k5_setfam_1(u1_struct_0('#skF_1'),k7_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')),'#skF_2','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_374,c_375])).

tff(c_670,plain,(
    ~ r1_tarski(k7_subset_1(u1_struct_0('#skF_1'),k3_tarski('#skF_2'),k3_tarski('#skF_3')),k5_setfam_1(u1_struct_0('#skF_1'),k4_xboole_0('#skF_2','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_647,c_513])).

tff(c_1165,plain,(
    ~ r1_tarski(k7_subset_1(u1_struct_0('#skF_1'),k3_tarski('#skF_2'),k3_tarski('#skF_3')),k3_tarski(k4_xboole_0('#skF_2','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_692,c_670])).

tff(c_1300,plain,(
    ~ r1_tarski(k4_xboole_0(k3_tarski('#skF_2'),k3_tarski('#skF_3')),k3_tarski(k4_xboole_0('#skF_2','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_643,c_1165])).

tff(c_1303,plain,(
    ~ r1_tarski(k3_tarski('#skF_2'),k2_xboole_0(k3_tarski('#skF_3'),k3_tarski(k4_xboole_0('#skF_2','#skF_3')))) ),
    inference(resolution,[status(thm)],[c_4,c_1300])).

tff(c_1307,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_228,c_2,c_12,c_1303])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n010.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 09:53:14 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.46/1.57  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.46/1.58  
% 3.46/1.58  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.46/1.58  %$ r1_tarski > m1_subset_1 > l1_struct_0 > k7_subset_1 > k5_setfam_1 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > u1_struct_0 > k3_tarski > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1
% 3.46/1.58  
% 3.46/1.58  %Foreground sorts:
% 3.46/1.58  
% 3.46/1.58  
% 3.46/1.58  %Background operators:
% 3.46/1.58  
% 3.46/1.58  
% 3.46/1.58  %Foreground operators:
% 3.46/1.58  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.46/1.58  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.46/1.58  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.46/1.58  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.46/1.58  tff('#skF_2', type, '#skF_2': $i).
% 3.46/1.58  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 3.46/1.58  tff('#skF_3', type, '#skF_3': $i).
% 3.46/1.58  tff('#skF_1', type, '#skF_1': $i).
% 3.46/1.58  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.46/1.58  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 3.46/1.58  tff(k5_setfam_1, type, k5_setfam_1: ($i * $i) > $i).
% 3.46/1.58  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.46/1.58  tff(k3_tarski, type, k3_tarski: $i > $i).
% 3.46/1.58  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.46/1.58  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.46/1.58  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.46/1.58  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.46/1.58  
% 3.46/1.59  tff(f_35, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 3.46/1.59  tff(f_37, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 3.46/1.59  tff(f_39, axiom, (![A, B]: (k3_tarski(k2_xboole_0(A, B)) = k2_xboole_0(k3_tarski(A), k3_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t96_zfmisc_1)).
% 3.46/1.59  tff(f_33, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 3.46/1.59  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_xboole_1)).
% 3.46/1.59  tff(f_31, axiom, (![A, B, C]: (r1_tarski(A, k2_xboole_0(B, C)) => r1_tarski(k4_xboole_0(A, B), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_xboole_1)).
% 3.46/1.59  tff(f_66, negated_conjecture, ~(![A]: (l1_struct_0(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => r1_tarski(k7_subset_1(u1_struct_0(A), k5_setfam_1(u1_struct_0(A), B), k5_setfam_1(u1_struct_0(A), C)), k5_setfam_1(u1_struct_0(A), k7_subset_1(k1_zfmisc_1(u1_struct_0(A)), B, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_tops_2)).
% 3.46/1.59  tff(f_55, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (k5_setfam_1(A, B) = k3_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k5_setfam_1)).
% 3.46/1.59  tff(f_51, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => m1_subset_1(k5_setfam_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k5_setfam_1)).
% 3.46/1.59  tff(f_47, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 3.46/1.59  tff(f_43, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k7_subset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k7_subset_1)).
% 3.46/1.59  tff(c_8, plain, (![B_9, A_8]: (k2_tarski(B_9, A_8)=k2_tarski(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.46/1.59  tff(c_63, plain, (![A_32, B_33]: (k3_tarski(k2_tarski(A_32, B_33))=k2_xboole_0(A_32, B_33))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.46/1.59  tff(c_78, plain, (![B_34, A_35]: (k3_tarski(k2_tarski(B_34, A_35))=k2_xboole_0(A_35, B_34))), inference(superposition, [status(thm), theory('equality')], [c_8, c_63])).
% 3.46/1.59  tff(c_10, plain, (![A_10, B_11]: (k3_tarski(k2_tarski(A_10, B_11))=k2_xboole_0(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.46/1.59  tff(c_84, plain, (![B_34, A_35]: (k2_xboole_0(B_34, A_35)=k2_xboole_0(A_35, B_34))), inference(superposition, [status(thm), theory('equality')], [c_78, c_10])).
% 3.46/1.59  tff(c_177, plain, (![A_44, B_45]: (k2_xboole_0(k3_tarski(A_44), k3_tarski(B_45))=k3_tarski(k2_xboole_0(A_44, B_45)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.46/1.59  tff(c_6, plain, (![A_6, B_7]: (r1_tarski(A_6, k2_xboole_0(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.46/1.59  tff(c_219, plain, (![A_46, B_47]: (r1_tarski(k3_tarski(A_46), k3_tarski(k2_xboole_0(A_46, B_47))))), inference(superposition, [status(thm), theory('equality')], [c_177, c_6])).
% 3.46/1.59  tff(c_228, plain, (![A_35, B_34]: (r1_tarski(k3_tarski(A_35), k3_tarski(k2_xboole_0(B_34, A_35))))), inference(superposition, [status(thm), theory('equality')], [c_84, c_219])).
% 3.46/1.59  tff(c_2, plain, (![A_1, B_2]: (k2_xboole_0(A_1, k4_xboole_0(B_2, A_1))=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.46/1.59  tff(c_12, plain, (![A_12, B_13]: (k2_xboole_0(k3_tarski(A_12), k3_tarski(B_13))=k3_tarski(k2_xboole_0(A_12, B_13)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.46/1.59  tff(c_4, plain, (![A_3, B_4, C_5]: (r1_tarski(k4_xboole_0(A_3, B_4), C_5) | ~r1_tarski(A_3, k2_xboole_0(B_4, C_5)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.46/1.59  tff(c_26, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.46/1.59  tff(c_366, plain, (![A_59, B_60]: (k5_setfam_1(A_59, B_60)=k3_tarski(B_60) | ~m1_subset_1(B_60, k1_zfmisc_1(k1_zfmisc_1(A_59))))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.46/1.59  tff(c_374, plain, (k5_setfam_1(u1_struct_0('#skF_1'), '#skF_2')=k3_tarski('#skF_2')), inference(resolution, [status(thm)], [c_26, c_366])).
% 3.46/1.59  tff(c_585, plain, (![A_70, B_71]: (m1_subset_1(k5_setfam_1(A_70, B_71), k1_zfmisc_1(A_70)) | ~m1_subset_1(B_71, k1_zfmisc_1(k1_zfmisc_1(A_70))))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.46/1.59  tff(c_592, plain, (m1_subset_1(k3_tarski('#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1('#skF_2', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(superposition, [status(thm), theory('equality')], [c_374, c_585])).
% 3.46/1.59  tff(c_598, plain, (m1_subset_1(k3_tarski('#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_592])).
% 3.46/1.59  tff(c_629, plain, (![A_74, B_75, C_76]: (k7_subset_1(A_74, B_75, C_76)=k4_xboole_0(B_75, C_76) | ~m1_subset_1(B_75, k1_zfmisc_1(A_74)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.46/1.59  tff(c_643, plain, (![C_76]: (k7_subset_1(u1_struct_0('#skF_1'), k3_tarski('#skF_2'), C_76)=k4_xboole_0(k3_tarski('#skF_2'), C_76))), inference(resolution, [status(thm)], [c_598, c_629])).
% 3.46/1.59  tff(c_671, plain, (![C_79]: (k7_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')), '#skF_2', C_79)=k4_xboole_0('#skF_2', C_79))), inference(resolution, [status(thm)], [c_26, c_629])).
% 3.46/1.59  tff(c_14, plain, (![A_14, B_15, C_16]: (m1_subset_1(k7_subset_1(A_14, B_15, C_16), k1_zfmisc_1(A_14)) | ~m1_subset_1(B_15, k1_zfmisc_1(A_14)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.46/1.59  tff(c_677, plain, (![C_79]: (m1_subset_1(k4_xboole_0('#skF_2', C_79), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) | ~m1_subset_1('#skF_2', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))))), inference(superposition, [status(thm), theory('equality')], [c_671, c_14])).
% 3.46/1.59  tff(c_685, plain, (![C_80]: (m1_subset_1(k4_xboole_0('#skF_2', C_80), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_677])).
% 3.46/1.59  tff(c_20, plain, (![A_22, B_23]: (k5_setfam_1(A_22, B_23)=k3_tarski(B_23) | ~m1_subset_1(B_23, k1_zfmisc_1(k1_zfmisc_1(A_22))))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.46/1.59  tff(c_692, plain, (![C_80]: (k5_setfam_1(u1_struct_0('#skF_1'), k4_xboole_0('#skF_2', C_80))=k3_tarski(k4_xboole_0('#skF_2', C_80)))), inference(resolution, [status(thm)], [c_685, c_20])).
% 3.46/1.59  tff(c_647, plain, (![C_76]: (k7_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')), '#skF_2', C_76)=k4_xboole_0('#skF_2', C_76))), inference(resolution, [status(thm)], [c_26, c_629])).
% 3.46/1.59  tff(c_24, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.46/1.59  tff(c_373, plain, (k5_setfam_1(u1_struct_0('#skF_1'), '#skF_3')=k3_tarski('#skF_3')), inference(resolution, [status(thm)], [c_24, c_366])).
% 3.46/1.59  tff(c_22, plain, (~r1_tarski(k7_subset_1(u1_struct_0('#skF_1'), k5_setfam_1(u1_struct_0('#skF_1'), '#skF_2'), k5_setfam_1(u1_struct_0('#skF_1'), '#skF_3')), k5_setfam_1(u1_struct_0('#skF_1'), k7_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')), '#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.46/1.59  tff(c_375, plain, (~r1_tarski(k7_subset_1(u1_struct_0('#skF_1'), k5_setfam_1(u1_struct_0('#skF_1'), '#skF_2'), k3_tarski('#skF_3')), k5_setfam_1(u1_struct_0('#skF_1'), k7_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')), '#skF_2', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_373, c_22])).
% 3.46/1.59  tff(c_513, plain, (~r1_tarski(k7_subset_1(u1_struct_0('#skF_1'), k3_tarski('#skF_2'), k3_tarski('#skF_3')), k5_setfam_1(u1_struct_0('#skF_1'), k7_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')), '#skF_2', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_374, c_375])).
% 3.46/1.59  tff(c_670, plain, (~r1_tarski(k7_subset_1(u1_struct_0('#skF_1'), k3_tarski('#skF_2'), k3_tarski('#skF_3')), k5_setfam_1(u1_struct_0('#skF_1'), k4_xboole_0('#skF_2', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_647, c_513])).
% 3.46/1.59  tff(c_1165, plain, (~r1_tarski(k7_subset_1(u1_struct_0('#skF_1'), k3_tarski('#skF_2'), k3_tarski('#skF_3')), k3_tarski(k4_xboole_0('#skF_2', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_692, c_670])).
% 3.46/1.59  tff(c_1300, plain, (~r1_tarski(k4_xboole_0(k3_tarski('#skF_2'), k3_tarski('#skF_3')), k3_tarski(k4_xboole_0('#skF_2', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_643, c_1165])).
% 3.46/1.59  tff(c_1303, plain, (~r1_tarski(k3_tarski('#skF_2'), k2_xboole_0(k3_tarski('#skF_3'), k3_tarski(k4_xboole_0('#skF_2', '#skF_3'))))), inference(resolution, [status(thm)], [c_4, c_1300])).
% 3.46/1.59  tff(c_1307, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_228, c_2, c_12, c_1303])).
% 3.46/1.59  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.46/1.59  
% 3.46/1.59  Inference rules
% 3.46/1.59  ----------------------
% 3.46/1.59  #Ref     : 0
% 3.46/1.59  #Sup     : 343
% 3.46/1.59  #Fact    : 0
% 3.46/1.59  #Define  : 0
% 3.46/1.59  #Split   : 0
% 3.46/1.59  #Chain   : 0
% 3.46/1.59  #Close   : 0
% 3.46/1.59  
% 3.46/1.59  Ordering : KBO
% 3.46/1.59  
% 3.46/1.59  Simplification rules
% 3.46/1.59  ----------------------
% 3.46/1.59  #Subsume      : 2
% 3.46/1.59  #Demod        : 123
% 3.46/1.59  #Tautology    : 139
% 3.46/1.59  #SimpNegUnit  : 0
% 3.46/1.59  #BackRed      : 3
% 3.46/1.59  
% 3.46/1.59  #Partial instantiations: 0
% 3.46/1.59  #Strategies tried      : 1
% 3.46/1.59  
% 3.46/1.59  Timing (in seconds)
% 3.46/1.59  ----------------------
% 3.46/1.59  Preprocessing        : 0.31
% 3.46/1.59  Parsing              : 0.17
% 3.46/1.59  CNF conversion       : 0.02
% 3.46/1.59  Main loop            : 0.50
% 3.46/1.59  Inferencing          : 0.15
% 3.46/1.59  Reduction            : 0.21
% 3.46/1.59  Demodulation         : 0.18
% 3.46/1.59  BG Simplification    : 0.02
% 3.46/1.59  Subsumption          : 0.08
% 3.46/1.59  Abstraction          : 0.03
% 3.46/1.59  MUC search           : 0.00
% 3.46/1.59  Cooper               : 0.00
% 3.46/1.60  Total                : 0.84
% 3.46/1.60  Index Insertion      : 0.00
% 3.46/1.60  Index Deletion       : 0.00
% 3.46/1.60  Index Matching       : 0.00
% 3.46/1.60  BG Taut test         : 0.00
%------------------------------------------------------------------------------
