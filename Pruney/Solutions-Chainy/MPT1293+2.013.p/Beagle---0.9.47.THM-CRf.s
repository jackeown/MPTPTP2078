%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:22:36 EST 2020

% Result     : Theorem 3.80s
% Output     : CNFRefutation 3.80s
% Verified   : 
% Statistics : Number of formulae       :   60 (  88 expanded)
%              Number of leaves         :   27 (  42 expanded)
%              Depth                    :    9
%              Number of atoms          :   59 ( 122 expanded)
%              Number of equality atoms :   20 (  34 expanded)
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

tff(f_39,axiom,(
    ! [A,B] : k3_tarski(k2_xboole_0(A,B)) = k2_xboole_0(k3_tarski(A),k3_tarski(B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t96_zfmisc_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_35,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_33,axiom,(
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

tff(c_127,plain,(
    ! [A_42,B_43] : k2_xboole_0(k3_tarski(A_42),k3_tarski(B_43)) = k3_tarski(k2_xboole_0(A_42,B_43)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_30,plain,(
    ! [B_30,A_31] : k2_xboole_0(B_30,A_31) = k2_xboole_0(A_31,B_30) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_8,plain,(
    ! [A_8,B_9] : r1_tarski(A_8,k2_xboole_0(A_8,B_9)) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_45,plain,(
    ! [A_31,B_30] : r1_tarski(A_31,k2_xboole_0(B_30,A_31)) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_8])).

tff(c_139,plain,(
    ! [B_43,A_42] : r1_tarski(k3_tarski(B_43),k3_tarski(k2_xboole_0(A_42,B_43))) ),
    inference(superposition,[status(thm),theory(equality)],[c_127,c_45])).

tff(c_4,plain,(
    ! [A_3,B_4] : k2_xboole_0(A_3,k4_xboole_0(B_4,A_3)) = k2_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_12,plain,(
    ! [A_12,B_13] : k2_xboole_0(k3_tarski(A_12),k3_tarski(B_13)) = k3_tarski(k2_xboole_0(A_12,B_13)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_6,plain,(
    ! [A_5,B_6,C_7] :
      ( r1_tarski(k4_xboole_0(A_5,B_6),C_7)
      | ~ r1_tarski(A_5,k2_xboole_0(B_6,C_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_26,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_529,plain,(
    ! [A_70,B_71,C_72] :
      ( k7_subset_1(A_70,B_71,C_72) = k4_xboole_0(B_71,C_72)
      | ~ m1_subset_1(B_71,k1_zfmisc_1(A_70)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_571,plain,(
    ! [C_75] : k7_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')),'#skF_2',C_75) = k4_xboole_0('#skF_2',C_75) ),
    inference(resolution,[status(thm)],[c_26,c_529])).

tff(c_14,plain,(
    ! [A_14,B_15,C_16] :
      ( m1_subset_1(k7_subset_1(A_14,B_15,C_16),k1_zfmisc_1(A_14))
      | ~ m1_subset_1(B_15,k1_zfmisc_1(A_14)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_577,plain,(
    ! [C_75] :
      ( m1_subset_1(k4_xboole_0('#skF_2',C_75),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))
      | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_571,c_14])).

tff(c_585,plain,(
    ! [C_76] : m1_subset_1(k4_xboole_0('#skF_2',C_76),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_577])).

tff(c_20,plain,(
    ! [A_22,B_23] :
      ( k5_setfam_1(A_22,B_23) = k3_tarski(B_23)
      | ~ m1_subset_1(B_23,k1_zfmisc_1(k1_zfmisc_1(A_22))) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_592,plain,(
    ! [C_76] : k5_setfam_1(u1_struct_0('#skF_1'),k4_xboole_0('#skF_2',C_76)) = k3_tarski(k4_xboole_0('#skF_2',C_76)) ),
    inference(resolution,[status(thm)],[c_585,c_20])).

tff(c_204,plain,(
    ! [A_51,B_52] :
      ( k5_setfam_1(A_51,B_52) = k3_tarski(B_52)
      | ~ m1_subset_1(B_52,k1_zfmisc_1(k1_zfmisc_1(A_51))) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_212,plain,(
    k5_setfam_1(u1_struct_0('#skF_1'),'#skF_2') = k3_tarski('#skF_2') ),
    inference(resolution,[status(thm)],[c_26,c_204])).

tff(c_18,plain,(
    ! [A_20,B_21] :
      ( m1_subset_1(k5_setfam_1(A_20,B_21),k1_zfmisc_1(A_20))
      | ~ m1_subset_1(B_21,k1_zfmisc_1(k1_zfmisc_1(A_20))) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_1006,plain,(
    ! [A_99,B_100,C_101] :
      ( k7_subset_1(A_99,k5_setfam_1(A_99,B_100),C_101) = k4_xboole_0(k5_setfam_1(A_99,B_100),C_101)
      | ~ m1_subset_1(B_100,k1_zfmisc_1(k1_zfmisc_1(A_99))) ) ),
    inference(resolution,[status(thm)],[c_18,c_529])).

tff(c_1020,plain,(
    ! [C_101] : k7_subset_1(u1_struct_0('#skF_1'),k5_setfam_1(u1_struct_0('#skF_1'),'#skF_2'),C_101) = k4_xboole_0(k5_setfam_1(u1_struct_0('#skF_1'),'#skF_2'),C_101) ),
    inference(resolution,[status(thm)],[c_26,c_1006])).

tff(c_1029,plain,(
    ! [C_101] : k7_subset_1(u1_struct_0('#skF_1'),k3_tarski('#skF_2'),C_101) = k4_xboole_0(k3_tarski('#skF_2'),C_101) ),
    inference(demodulation,[status(thm),theory(equality)],[c_212,c_212,c_1020])).

tff(c_547,plain,(
    ! [C_72] : k7_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')),'#skF_2',C_72) = k4_xboole_0('#skF_2',C_72) ),
    inference(resolution,[status(thm)],[c_26,c_529])).

tff(c_24,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_211,plain,(
    k5_setfam_1(u1_struct_0('#skF_1'),'#skF_3') = k3_tarski('#skF_3') ),
    inference(resolution,[status(thm)],[c_24,c_204])).

tff(c_22,plain,(
    ~ r1_tarski(k7_subset_1(u1_struct_0('#skF_1'),k5_setfam_1(u1_struct_0('#skF_1'),'#skF_2'),k5_setfam_1(u1_struct_0('#skF_1'),'#skF_3')),k5_setfam_1(u1_struct_0('#skF_1'),k7_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')),'#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_213,plain,(
    ~ r1_tarski(k7_subset_1(u1_struct_0('#skF_1'),k5_setfam_1(u1_struct_0('#skF_1'),'#skF_2'),k3_tarski('#skF_3')),k5_setfam_1(u1_struct_0('#skF_1'),k7_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')),'#skF_2','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_211,c_22])).

tff(c_413,plain,(
    ~ r1_tarski(k7_subset_1(u1_struct_0('#skF_1'),k3_tarski('#skF_2'),k3_tarski('#skF_3')),k5_setfam_1(u1_struct_0('#skF_1'),k7_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')),'#skF_2','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_212,c_213])).

tff(c_570,plain,(
    ~ r1_tarski(k7_subset_1(u1_struct_0('#skF_1'),k3_tarski('#skF_2'),k3_tarski('#skF_3')),k5_setfam_1(u1_struct_0('#skF_1'),k4_xboole_0('#skF_2','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_547,c_413])).

tff(c_1048,plain,(
    ~ r1_tarski(k4_xboole_0(k3_tarski('#skF_2'),k3_tarski('#skF_3')),k5_setfam_1(u1_struct_0('#skF_1'),k4_xboole_0('#skF_2','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1029,c_570])).

tff(c_1630,plain,(
    ~ r1_tarski(k4_xboole_0(k3_tarski('#skF_2'),k3_tarski('#skF_3')),k3_tarski(k4_xboole_0('#skF_2','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_592,c_1048])).

tff(c_1633,plain,(
    ~ r1_tarski(k3_tarski('#skF_2'),k2_xboole_0(k3_tarski('#skF_3'),k3_tarski(k4_xboole_0('#skF_2','#skF_3')))) ),
    inference(resolution,[status(thm)],[c_6,c_1630])).

tff(c_1637,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_139,c_4,c_12,c_1633])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:06:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.80/1.63  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.80/1.64  
% 3.80/1.64  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.80/1.64  %$ r1_tarski > m1_subset_1 > l1_struct_0 > k7_subset_1 > k5_setfam_1 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > u1_struct_0 > k3_tarski > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1
% 3.80/1.64  
% 3.80/1.64  %Foreground sorts:
% 3.80/1.64  
% 3.80/1.64  
% 3.80/1.64  %Background operators:
% 3.80/1.64  
% 3.80/1.64  
% 3.80/1.64  %Foreground operators:
% 3.80/1.64  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.80/1.64  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.80/1.64  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.80/1.64  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.80/1.64  tff('#skF_2', type, '#skF_2': $i).
% 3.80/1.64  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 3.80/1.64  tff('#skF_3', type, '#skF_3': $i).
% 3.80/1.64  tff('#skF_1', type, '#skF_1': $i).
% 3.80/1.64  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.80/1.64  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 3.80/1.64  tff(k5_setfam_1, type, k5_setfam_1: ($i * $i) > $i).
% 3.80/1.64  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.80/1.64  tff(k3_tarski, type, k3_tarski: $i > $i).
% 3.80/1.64  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.80/1.64  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.80/1.64  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.80/1.64  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.80/1.64  
% 3.80/1.65  tff(f_39, axiom, (![A, B]: (k3_tarski(k2_xboole_0(A, B)) = k2_xboole_0(k3_tarski(A), k3_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t96_zfmisc_1)).
% 3.80/1.65  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 3.80/1.65  tff(f_35, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 3.80/1.65  tff(f_29, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_xboole_1)).
% 3.80/1.65  tff(f_33, axiom, (![A, B, C]: (r1_tarski(A, k2_xboole_0(B, C)) => r1_tarski(k4_xboole_0(A, B), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_xboole_1)).
% 3.80/1.65  tff(f_66, negated_conjecture, ~(![A]: (l1_struct_0(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => r1_tarski(k7_subset_1(u1_struct_0(A), k5_setfam_1(u1_struct_0(A), B), k5_setfam_1(u1_struct_0(A), C)), k5_setfam_1(u1_struct_0(A), k7_subset_1(k1_zfmisc_1(u1_struct_0(A)), B, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_tops_2)).
% 3.80/1.65  tff(f_47, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 3.80/1.65  tff(f_43, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k7_subset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k7_subset_1)).
% 3.80/1.65  tff(f_55, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (k5_setfam_1(A, B) = k3_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k5_setfam_1)).
% 3.80/1.65  tff(f_51, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => m1_subset_1(k5_setfam_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k5_setfam_1)).
% 3.80/1.65  tff(c_127, plain, (![A_42, B_43]: (k2_xboole_0(k3_tarski(A_42), k3_tarski(B_43))=k3_tarski(k2_xboole_0(A_42, B_43)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.80/1.65  tff(c_30, plain, (![B_30, A_31]: (k2_xboole_0(B_30, A_31)=k2_xboole_0(A_31, B_30))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.80/1.65  tff(c_8, plain, (![A_8, B_9]: (r1_tarski(A_8, k2_xboole_0(A_8, B_9)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.80/1.65  tff(c_45, plain, (![A_31, B_30]: (r1_tarski(A_31, k2_xboole_0(B_30, A_31)))), inference(superposition, [status(thm), theory('equality')], [c_30, c_8])).
% 3.80/1.65  tff(c_139, plain, (![B_43, A_42]: (r1_tarski(k3_tarski(B_43), k3_tarski(k2_xboole_0(A_42, B_43))))), inference(superposition, [status(thm), theory('equality')], [c_127, c_45])).
% 3.80/1.65  tff(c_4, plain, (![A_3, B_4]: (k2_xboole_0(A_3, k4_xboole_0(B_4, A_3))=k2_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.80/1.65  tff(c_12, plain, (![A_12, B_13]: (k2_xboole_0(k3_tarski(A_12), k3_tarski(B_13))=k3_tarski(k2_xboole_0(A_12, B_13)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.80/1.65  tff(c_6, plain, (![A_5, B_6, C_7]: (r1_tarski(k4_xboole_0(A_5, B_6), C_7) | ~r1_tarski(A_5, k2_xboole_0(B_6, C_7)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.80/1.65  tff(c_26, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.80/1.65  tff(c_529, plain, (![A_70, B_71, C_72]: (k7_subset_1(A_70, B_71, C_72)=k4_xboole_0(B_71, C_72) | ~m1_subset_1(B_71, k1_zfmisc_1(A_70)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.80/1.65  tff(c_571, plain, (![C_75]: (k7_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')), '#skF_2', C_75)=k4_xboole_0('#skF_2', C_75))), inference(resolution, [status(thm)], [c_26, c_529])).
% 3.80/1.65  tff(c_14, plain, (![A_14, B_15, C_16]: (m1_subset_1(k7_subset_1(A_14, B_15, C_16), k1_zfmisc_1(A_14)) | ~m1_subset_1(B_15, k1_zfmisc_1(A_14)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.80/1.65  tff(c_577, plain, (![C_75]: (m1_subset_1(k4_xboole_0('#skF_2', C_75), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) | ~m1_subset_1('#skF_2', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))))), inference(superposition, [status(thm), theory('equality')], [c_571, c_14])).
% 3.80/1.65  tff(c_585, plain, (![C_76]: (m1_subset_1(k4_xboole_0('#skF_2', C_76), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_577])).
% 3.80/1.65  tff(c_20, plain, (![A_22, B_23]: (k5_setfam_1(A_22, B_23)=k3_tarski(B_23) | ~m1_subset_1(B_23, k1_zfmisc_1(k1_zfmisc_1(A_22))))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.80/1.65  tff(c_592, plain, (![C_76]: (k5_setfam_1(u1_struct_0('#skF_1'), k4_xboole_0('#skF_2', C_76))=k3_tarski(k4_xboole_0('#skF_2', C_76)))), inference(resolution, [status(thm)], [c_585, c_20])).
% 3.80/1.65  tff(c_204, plain, (![A_51, B_52]: (k5_setfam_1(A_51, B_52)=k3_tarski(B_52) | ~m1_subset_1(B_52, k1_zfmisc_1(k1_zfmisc_1(A_51))))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.80/1.65  tff(c_212, plain, (k5_setfam_1(u1_struct_0('#skF_1'), '#skF_2')=k3_tarski('#skF_2')), inference(resolution, [status(thm)], [c_26, c_204])).
% 3.80/1.65  tff(c_18, plain, (![A_20, B_21]: (m1_subset_1(k5_setfam_1(A_20, B_21), k1_zfmisc_1(A_20)) | ~m1_subset_1(B_21, k1_zfmisc_1(k1_zfmisc_1(A_20))))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.80/1.65  tff(c_1006, plain, (![A_99, B_100, C_101]: (k7_subset_1(A_99, k5_setfam_1(A_99, B_100), C_101)=k4_xboole_0(k5_setfam_1(A_99, B_100), C_101) | ~m1_subset_1(B_100, k1_zfmisc_1(k1_zfmisc_1(A_99))))), inference(resolution, [status(thm)], [c_18, c_529])).
% 3.80/1.65  tff(c_1020, plain, (![C_101]: (k7_subset_1(u1_struct_0('#skF_1'), k5_setfam_1(u1_struct_0('#skF_1'), '#skF_2'), C_101)=k4_xboole_0(k5_setfam_1(u1_struct_0('#skF_1'), '#skF_2'), C_101))), inference(resolution, [status(thm)], [c_26, c_1006])).
% 3.80/1.65  tff(c_1029, plain, (![C_101]: (k7_subset_1(u1_struct_0('#skF_1'), k3_tarski('#skF_2'), C_101)=k4_xboole_0(k3_tarski('#skF_2'), C_101))), inference(demodulation, [status(thm), theory('equality')], [c_212, c_212, c_1020])).
% 3.80/1.65  tff(c_547, plain, (![C_72]: (k7_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')), '#skF_2', C_72)=k4_xboole_0('#skF_2', C_72))), inference(resolution, [status(thm)], [c_26, c_529])).
% 3.80/1.65  tff(c_24, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.80/1.65  tff(c_211, plain, (k5_setfam_1(u1_struct_0('#skF_1'), '#skF_3')=k3_tarski('#skF_3')), inference(resolution, [status(thm)], [c_24, c_204])).
% 3.80/1.65  tff(c_22, plain, (~r1_tarski(k7_subset_1(u1_struct_0('#skF_1'), k5_setfam_1(u1_struct_0('#skF_1'), '#skF_2'), k5_setfam_1(u1_struct_0('#skF_1'), '#skF_3')), k5_setfam_1(u1_struct_0('#skF_1'), k7_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')), '#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.80/1.65  tff(c_213, plain, (~r1_tarski(k7_subset_1(u1_struct_0('#skF_1'), k5_setfam_1(u1_struct_0('#skF_1'), '#skF_2'), k3_tarski('#skF_3')), k5_setfam_1(u1_struct_0('#skF_1'), k7_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')), '#skF_2', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_211, c_22])).
% 3.80/1.65  tff(c_413, plain, (~r1_tarski(k7_subset_1(u1_struct_0('#skF_1'), k3_tarski('#skF_2'), k3_tarski('#skF_3')), k5_setfam_1(u1_struct_0('#skF_1'), k7_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')), '#skF_2', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_212, c_213])).
% 3.80/1.65  tff(c_570, plain, (~r1_tarski(k7_subset_1(u1_struct_0('#skF_1'), k3_tarski('#skF_2'), k3_tarski('#skF_3')), k5_setfam_1(u1_struct_0('#skF_1'), k4_xboole_0('#skF_2', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_547, c_413])).
% 3.80/1.65  tff(c_1048, plain, (~r1_tarski(k4_xboole_0(k3_tarski('#skF_2'), k3_tarski('#skF_3')), k5_setfam_1(u1_struct_0('#skF_1'), k4_xboole_0('#skF_2', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_1029, c_570])).
% 3.80/1.65  tff(c_1630, plain, (~r1_tarski(k4_xboole_0(k3_tarski('#skF_2'), k3_tarski('#skF_3')), k3_tarski(k4_xboole_0('#skF_2', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_592, c_1048])).
% 3.80/1.65  tff(c_1633, plain, (~r1_tarski(k3_tarski('#skF_2'), k2_xboole_0(k3_tarski('#skF_3'), k3_tarski(k4_xboole_0('#skF_2', '#skF_3'))))), inference(resolution, [status(thm)], [c_6, c_1630])).
% 3.80/1.65  tff(c_1637, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_139, c_4, c_12, c_1633])).
% 3.80/1.65  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.80/1.65  
% 3.80/1.65  Inference rules
% 3.80/1.65  ----------------------
% 3.80/1.65  #Ref     : 0
% 3.80/1.65  #Sup     : 435
% 3.80/1.65  #Fact    : 0
% 3.80/1.65  #Define  : 0
% 3.80/1.65  #Split   : 0
% 3.80/1.65  #Chain   : 0
% 3.80/1.65  #Close   : 0
% 3.80/1.65  
% 3.80/1.65  Ordering : KBO
% 3.80/1.65  
% 3.80/1.65  Simplification rules
% 3.80/1.65  ----------------------
% 3.80/1.65  #Subsume      : 2
% 3.80/1.65  #Demod        : 158
% 3.80/1.65  #Tautology    : 164
% 3.80/1.65  #SimpNegUnit  : 0
% 3.80/1.65  #BackRed      : 3
% 3.80/1.65  
% 3.80/1.65  #Partial instantiations: 0
% 3.80/1.65  #Strategies tried      : 1
% 3.80/1.65  
% 3.80/1.65  Timing (in seconds)
% 3.80/1.65  ----------------------
% 3.80/1.66  Preprocessing        : 0.30
% 3.80/1.66  Parsing              : 0.16
% 3.80/1.66  CNF conversion       : 0.02
% 3.80/1.66  Main loop            : 0.59
% 3.80/1.66  Inferencing          : 0.17
% 3.80/1.66  Reduction            : 0.26
% 3.80/1.66  Demodulation         : 0.22
% 3.80/1.66  BG Simplification    : 0.03
% 3.80/1.66  Subsumption          : 0.09
% 3.80/1.66  Abstraction          : 0.03
% 3.80/1.66  MUC search           : 0.00
% 3.80/1.66  Cooper               : 0.00
% 3.80/1.66  Total                : 0.91
% 3.80/1.66  Index Insertion      : 0.00
% 3.80/1.66  Index Deletion       : 0.00
% 3.80/1.66  Index Matching       : 0.00
% 3.80/1.66  BG Taut test         : 0.00
%------------------------------------------------------------------------------
