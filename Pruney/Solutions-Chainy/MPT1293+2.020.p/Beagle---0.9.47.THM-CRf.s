%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:22:37 EST 2020

% Result     : Theorem 4.69s
% Output     : CNFRefutation 4.81s
% Verified   : 
% Statistics : Number of formulae       :   64 (  85 expanded)
%              Number of leaves         :   28 (  40 expanded)
%              Depth                    :    9
%              Number of atoms          :   69 ( 116 expanded)
%              Number of equality atoms :   22 (  29 expanded)
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

tff(f_45,axiom,(
    ! [A,B] : k3_tarski(k2_xboole_0(A,B)) = k2_xboole_0(k3_tarski(A),k3_tarski(B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t96_zfmisc_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_39,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k2_xboole_0(B,C))
     => r1_tarski(k4_xboole_0(A,B),C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_xboole_1)).

tff(f_70,negated_conjecture,(
    ~ ! [A] :
        ( l1_struct_0(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
               => r1_tarski(k7_subset_1(u1_struct_0(A),k5_setfam_1(u1_struct_0(A),B),k5_setfam_1(u1_struct_0(A),C)),k5_setfam_1(u1_struct_0(A),k7_subset_1(k1_zfmisc_1(u1_struct_0(A)),B,C))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_tops_2)).

tff(f_59,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_47,axiom,(
    ! [A] : k3_tarski(k1_zfmisc_1(A)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t99_zfmisc_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => r1_tarski(k3_tarski(A),k3_tarski(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_zfmisc_1)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(k4_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t109_xboole_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => k5_setfam_1(A,B) = k3_tarski(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k5_setfam_1)).

tff(c_153,plain,(
    ! [A_51,B_52] : k2_xboole_0(k3_tarski(A_51),k3_tarski(B_52)) = k3_tarski(k2_xboole_0(A_51,B_52)) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_43,plain,(
    ! [B_32,A_33] : k2_xboole_0(B_32,A_33) = k2_xboole_0(A_33,B_32) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_10,plain,(
    ! [A_11,B_12] : r1_tarski(A_11,k2_xboole_0(A_11,B_12)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_58,plain,(
    ! [A_33,B_32] : r1_tarski(A_33,k2_xboole_0(B_32,A_33)) ),
    inference(superposition,[status(thm),theory(equality)],[c_43,c_10])).

tff(c_165,plain,(
    ! [B_52,A_51] : r1_tarski(k3_tarski(B_52),k3_tarski(k2_xboole_0(A_51,B_52))) ),
    inference(superposition,[status(thm),theory(equality)],[c_153,c_58])).

tff(c_6,plain,(
    ! [A_6,B_7] : k2_xboole_0(A_6,k4_xboole_0(B_7,A_6)) = k2_xboole_0(A_6,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_14,plain,(
    ! [A_15,B_16] : k2_xboole_0(k3_tarski(A_15),k3_tarski(B_16)) = k3_tarski(k2_xboole_0(A_15,B_16)) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_8,plain,(
    ! [A_8,B_9,C_10] :
      ( r1_tarski(k4_xboole_0(A_8,B_9),C_10)
      | ~ r1_tarski(A_8,k2_xboole_0(B_9,C_10)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_30,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_92,plain,(
    ! [A_36,B_37] :
      ( r1_tarski(A_36,B_37)
      | ~ m1_subset_1(A_36,k1_zfmisc_1(B_37)) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_100,plain,(
    r1_tarski('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_30,c_92])).

tff(c_16,plain,(
    ! [A_17] : k3_tarski(k1_zfmisc_1(A_17)) = A_17 ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_146,plain,(
    ! [A_49,B_50] :
      ( r1_tarski(k3_tarski(A_49),k3_tarski(B_50))
      | ~ r1_tarski(A_49,B_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_152,plain,(
    ! [A_49,A_17] :
      ( r1_tarski(k3_tarski(A_49),A_17)
      | ~ r1_tarski(A_49,k1_zfmisc_1(A_17)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_146])).

tff(c_24,plain,(
    ! [A_23,B_24] :
      ( m1_subset_1(A_23,k1_zfmisc_1(B_24))
      | ~ r1_tarski(A_23,B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_584,plain,(
    ! [A_78,B_79,C_80] :
      ( k7_subset_1(A_78,B_79,C_80) = k4_xboole_0(B_79,C_80)
      | ~ m1_subset_1(B_79,k1_zfmisc_1(A_78)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_979,plain,(
    ! [B_93,A_94,C_95] :
      ( k7_subset_1(B_93,A_94,C_95) = k4_xboole_0(A_94,C_95)
      | ~ r1_tarski(A_94,B_93) ) ),
    inference(resolution,[status(thm)],[c_24,c_584])).

tff(c_3437,plain,(
    ! [A_177,A_178,C_179] :
      ( k7_subset_1(A_177,k3_tarski(A_178),C_179) = k4_xboole_0(k3_tarski(A_178),C_179)
      | ~ r1_tarski(A_178,k1_zfmisc_1(A_177)) ) ),
    inference(resolution,[status(thm)],[c_152,c_979])).

tff(c_3454,plain,(
    ! [C_179] : k7_subset_1(u1_struct_0('#skF_1'),k3_tarski('#skF_2'),C_179) = k4_xboole_0(k3_tarski('#skF_2'),C_179) ),
    inference(resolution,[status(thm)],[c_100,c_3437])).

tff(c_4,plain,(
    ! [A_3,C_5,B_4] :
      ( r1_tarski(k4_xboole_0(A_3,C_5),B_4)
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_243,plain,(
    ! [A_59,B_60] :
      ( k5_setfam_1(A_59,B_60) = k3_tarski(B_60)
      | ~ m1_subset_1(B_60,k1_zfmisc_1(k1_zfmisc_1(A_59))) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_595,plain,(
    ! [A_81,A_82] :
      ( k5_setfam_1(A_81,A_82) = k3_tarski(A_82)
      | ~ r1_tarski(A_82,k1_zfmisc_1(A_81)) ) ),
    inference(resolution,[status(thm)],[c_24,c_243])).

tff(c_3209,plain,(
    ! [A_167,A_168,C_169] :
      ( k5_setfam_1(A_167,k4_xboole_0(A_168,C_169)) = k3_tarski(k4_xboole_0(A_168,C_169))
      | ~ r1_tarski(A_168,k1_zfmisc_1(A_167)) ) ),
    inference(resolution,[status(thm)],[c_4,c_595])).

tff(c_3226,plain,(
    ! [C_169] : k5_setfam_1(u1_struct_0('#skF_1'),k4_xboole_0('#skF_2',C_169)) = k3_tarski(k4_xboole_0('#skF_2',C_169)) ),
    inference(resolution,[status(thm)],[c_100,c_3209])).

tff(c_593,plain,(
    ! [C_80] : k7_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')),'#skF_2',C_80) = k4_xboole_0('#skF_2',C_80) ),
    inference(resolution,[status(thm)],[c_30,c_584])).

tff(c_256,plain,(
    k5_setfam_1(u1_struct_0('#skF_1'),'#skF_2') = k3_tarski('#skF_2') ),
    inference(resolution,[status(thm)],[c_30,c_243])).

tff(c_28,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_255,plain,(
    k5_setfam_1(u1_struct_0('#skF_1'),'#skF_3') = k3_tarski('#skF_3') ),
    inference(resolution,[status(thm)],[c_28,c_243])).

tff(c_26,plain,(
    ~ r1_tarski(k7_subset_1(u1_struct_0('#skF_1'),k5_setfam_1(u1_struct_0('#skF_1'),'#skF_2'),k5_setfam_1(u1_struct_0('#skF_1'),'#skF_3')),k5_setfam_1(u1_struct_0('#skF_1'),k7_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')),'#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_257,plain,(
    ~ r1_tarski(k7_subset_1(u1_struct_0('#skF_1'),k5_setfam_1(u1_struct_0('#skF_1'),'#skF_2'),k3_tarski('#skF_3')),k5_setfam_1(u1_struct_0('#skF_1'),k7_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')),'#skF_2','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_255,c_26])).

tff(c_277,plain,(
    ~ r1_tarski(k7_subset_1(u1_struct_0('#skF_1'),k3_tarski('#skF_2'),k3_tarski('#skF_3')),k5_setfam_1(u1_struct_0('#skF_1'),k7_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')),'#skF_2','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_256,c_257])).

tff(c_706,plain,(
    ~ r1_tarski(k7_subset_1(u1_struct_0('#skF_1'),k3_tarski('#skF_2'),k3_tarski('#skF_3')),k5_setfam_1(u1_struct_0('#skF_1'),k4_xboole_0('#skF_2','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_593,c_277])).

tff(c_3228,plain,(
    ~ r1_tarski(k7_subset_1(u1_struct_0('#skF_1'),k3_tarski('#skF_2'),k3_tarski('#skF_3')),k3_tarski(k4_xboole_0('#skF_2','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3226,c_706])).

tff(c_3456,plain,(
    ~ r1_tarski(k4_xboole_0(k3_tarski('#skF_2'),k3_tarski('#skF_3')),k3_tarski(k4_xboole_0('#skF_2','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3454,c_3228])).

tff(c_3477,plain,(
    ~ r1_tarski(k3_tarski('#skF_2'),k2_xboole_0(k3_tarski('#skF_3'),k3_tarski(k4_xboole_0('#skF_2','#skF_3')))) ),
    inference(resolution,[status(thm)],[c_8,c_3456])).

tff(c_3484,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_165,c_6,c_14,c_3477])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n019.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 09:33:37 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.69/1.94  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.69/1.95  
% 4.69/1.95  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.69/1.95  %$ r1_tarski > m1_subset_1 > l1_struct_0 > k7_subset_1 > k5_setfam_1 > k4_xboole_0 > k2_xboole_0 > #nlpp > u1_struct_0 > k3_tarski > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1
% 4.69/1.95  
% 4.69/1.95  %Foreground sorts:
% 4.69/1.95  
% 4.69/1.95  
% 4.69/1.95  %Background operators:
% 4.69/1.95  
% 4.69/1.95  
% 4.69/1.95  %Foreground operators:
% 4.69/1.95  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.69/1.95  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.69/1.95  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.69/1.95  tff('#skF_2', type, '#skF_2': $i).
% 4.69/1.95  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 4.69/1.95  tff('#skF_3', type, '#skF_3': $i).
% 4.69/1.95  tff('#skF_1', type, '#skF_1': $i).
% 4.69/1.95  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.69/1.95  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 4.69/1.95  tff(k5_setfam_1, type, k5_setfam_1: ($i * $i) > $i).
% 4.69/1.95  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.69/1.95  tff(k3_tarski, type, k3_tarski: $i > $i).
% 4.69/1.95  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.69/1.95  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.69/1.95  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 4.69/1.95  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.69/1.95  
% 4.81/1.97  tff(f_45, axiom, (![A, B]: (k3_tarski(k2_xboole_0(A, B)) = k2_xboole_0(k3_tarski(A), k3_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t96_zfmisc_1)).
% 4.81/1.97  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 4.81/1.97  tff(f_39, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 4.81/1.97  tff(f_33, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_xboole_1)).
% 4.81/1.97  tff(f_37, axiom, (![A, B, C]: (r1_tarski(A, k2_xboole_0(B, C)) => r1_tarski(k4_xboole_0(A, B), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_xboole_1)).
% 4.81/1.97  tff(f_70, negated_conjecture, ~(![A]: (l1_struct_0(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => r1_tarski(k7_subset_1(u1_struct_0(A), k5_setfam_1(u1_struct_0(A), B), k5_setfam_1(u1_struct_0(A), C)), k5_setfam_1(u1_struct_0(A), k7_subset_1(k1_zfmisc_1(u1_struct_0(A)), B, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_tops_2)).
% 4.81/1.97  tff(f_59, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 4.81/1.97  tff(f_47, axiom, (![A]: (k3_tarski(k1_zfmisc_1(A)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t99_zfmisc_1)).
% 4.81/1.97  tff(f_43, axiom, (![A, B]: (r1_tarski(A, B) => r1_tarski(k3_tarski(A), k3_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t95_zfmisc_1)).
% 4.81/1.97  tff(f_51, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 4.81/1.97  tff(f_31, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(k4_xboole_0(A, C), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t109_xboole_1)).
% 4.81/1.97  tff(f_55, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (k5_setfam_1(A, B) = k3_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k5_setfam_1)).
% 4.81/1.97  tff(c_153, plain, (![A_51, B_52]: (k2_xboole_0(k3_tarski(A_51), k3_tarski(B_52))=k3_tarski(k2_xboole_0(A_51, B_52)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 4.81/1.97  tff(c_43, plain, (![B_32, A_33]: (k2_xboole_0(B_32, A_33)=k2_xboole_0(A_33, B_32))), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.81/1.97  tff(c_10, plain, (![A_11, B_12]: (r1_tarski(A_11, k2_xboole_0(A_11, B_12)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.81/1.97  tff(c_58, plain, (![A_33, B_32]: (r1_tarski(A_33, k2_xboole_0(B_32, A_33)))), inference(superposition, [status(thm), theory('equality')], [c_43, c_10])).
% 4.81/1.97  tff(c_165, plain, (![B_52, A_51]: (r1_tarski(k3_tarski(B_52), k3_tarski(k2_xboole_0(A_51, B_52))))), inference(superposition, [status(thm), theory('equality')], [c_153, c_58])).
% 4.81/1.97  tff(c_6, plain, (![A_6, B_7]: (k2_xboole_0(A_6, k4_xboole_0(B_7, A_6))=k2_xboole_0(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.81/1.97  tff(c_14, plain, (![A_15, B_16]: (k2_xboole_0(k3_tarski(A_15), k3_tarski(B_16))=k3_tarski(k2_xboole_0(A_15, B_16)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 4.81/1.97  tff(c_8, plain, (![A_8, B_9, C_10]: (r1_tarski(k4_xboole_0(A_8, B_9), C_10) | ~r1_tarski(A_8, k2_xboole_0(B_9, C_10)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.81/1.97  tff(c_30, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(cnfTransformation, [status(thm)], [f_70])).
% 4.81/1.97  tff(c_92, plain, (![A_36, B_37]: (r1_tarski(A_36, B_37) | ~m1_subset_1(A_36, k1_zfmisc_1(B_37)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 4.81/1.97  tff(c_100, plain, (r1_tarski('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_30, c_92])).
% 4.81/1.97  tff(c_16, plain, (![A_17]: (k3_tarski(k1_zfmisc_1(A_17))=A_17)), inference(cnfTransformation, [status(thm)], [f_47])).
% 4.81/1.97  tff(c_146, plain, (![A_49, B_50]: (r1_tarski(k3_tarski(A_49), k3_tarski(B_50)) | ~r1_tarski(A_49, B_50))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.81/1.97  tff(c_152, plain, (![A_49, A_17]: (r1_tarski(k3_tarski(A_49), A_17) | ~r1_tarski(A_49, k1_zfmisc_1(A_17)))), inference(superposition, [status(thm), theory('equality')], [c_16, c_146])).
% 4.81/1.97  tff(c_24, plain, (![A_23, B_24]: (m1_subset_1(A_23, k1_zfmisc_1(B_24)) | ~r1_tarski(A_23, B_24))), inference(cnfTransformation, [status(thm)], [f_59])).
% 4.81/1.97  tff(c_584, plain, (![A_78, B_79, C_80]: (k7_subset_1(A_78, B_79, C_80)=k4_xboole_0(B_79, C_80) | ~m1_subset_1(B_79, k1_zfmisc_1(A_78)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 4.81/1.97  tff(c_979, plain, (![B_93, A_94, C_95]: (k7_subset_1(B_93, A_94, C_95)=k4_xboole_0(A_94, C_95) | ~r1_tarski(A_94, B_93))), inference(resolution, [status(thm)], [c_24, c_584])).
% 4.81/1.97  tff(c_3437, plain, (![A_177, A_178, C_179]: (k7_subset_1(A_177, k3_tarski(A_178), C_179)=k4_xboole_0(k3_tarski(A_178), C_179) | ~r1_tarski(A_178, k1_zfmisc_1(A_177)))), inference(resolution, [status(thm)], [c_152, c_979])).
% 4.81/1.97  tff(c_3454, plain, (![C_179]: (k7_subset_1(u1_struct_0('#skF_1'), k3_tarski('#skF_2'), C_179)=k4_xboole_0(k3_tarski('#skF_2'), C_179))), inference(resolution, [status(thm)], [c_100, c_3437])).
% 4.81/1.97  tff(c_4, plain, (![A_3, C_5, B_4]: (r1_tarski(k4_xboole_0(A_3, C_5), B_4) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.81/1.97  tff(c_243, plain, (![A_59, B_60]: (k5_setfam_1(A_59, B_60)=k3_tarski(B_60) | ~m1_subset_1(B_60, k1_zfmisc_1(k1_zfmisc_1(A_59))))), inference(cnfTransformation, [status(thm)], [f_55])).
% 4.81/1.97  tff(c_595, plain, (![A_81, A_82]: (k5_setfam_1(A_81, A_82)=k3_tarski(A_82) | ~r1_tarski(A_82, k1_zfmisc_1(A_81)))), inference(resolution, [status(thm)], [c_24, c_243])).
% 4.81/1.97  tff(c_3209, plain, (![A_167, A_168, C_169]: (k5_setfam_1(A_167, k4_xboole_0(A_168, C_169))=k3_tarski(k4_xboole_0(A_168, C_169)) | ~r1_tarski(A_168, k1_zfmisc_1(A_167)))), inference(resolution, [status(thm)], [c_4, c_595])).
% 4.81/1.97  tff(c_3226, plain, (![C_169]: (k5_setfam_1(u1_struct_0('#skF_1'), k4_xboole_0('#skF_2', C_169))=k3_tarski(k4_xboole_0('#skF_2', C_169)))), inference(resolution, [status(thm)], [c_100, c_3209])).
% 4.81/1.97  tff(c_593, plain, (![C_80]: (k7_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')), '#skF_2', C_80)=k4_xboole_0('#skF_2', C_80))), inference(resolution, [status(thm)], [c_30, c_584])).
% 4.81/1.97  tff(c_256, plain, (k5_setfam_1(u1_struct_0('#skF_1'), '#skF_2')=k3_tarski('#skF_2')), inference(resolution, [status(thm)], [c_30, c_243])).
% 4.81/1.97  tff(c_28, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(cnfTransformation, [status(thm)], [f_70])).
% 4.81/1.97  tff(c_255, plain, (k5_setfam_1(u1_struct_0('#skF_1'), '#skF_3')=k3_tarski('#skF_3')), inference(resolution, [status(thm)], [c_28, c_243])).
% 4.81/1.97  tff(c_26, plain, (~r1_tarski(k7_subset_1(u1_struct_0('#skF_1'), k5_setfam_1(u1_struct_0('#skF_1'), '#skF_2'), k5_setfam_1(u1_struct_0('#skF_1'), '#skF_3')), k5_setfam_1(u1_struct_0('#skF_1'), k7_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')), '#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_70])).
% 4.81/1.97  tff(c_257, plain, (~r1_tarski(k7_subset_1(u1_struct_0('#skF_1'), k5_setfam_1(u1_struct_0('#skF_1'), '#skF_2'), k3_tarski('#skF_3')), k5_setfam_1(u1_struct_0('#skF_1'), k7_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')), '#skF_2', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_255, c_26])).
% 4.81/1.97  tff(c_277, plain, (~r1_tarski(k7_subset_1(u1_struct_0('#skF_1'), k3_tarski('#skF_2'), k3_tarski('#skF_3')), k5_setfam_1(u1_struct_0('#skF_1'), k7_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')), '#skF_2', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_256, c_257])).
% 4.81/1.97  tff(c_706, plain, (~r1_tarski(k7_subset_1(u1_struct_0('#skF_1'), k3_tarski('#skF_2'), k3_tarski('#skF_3')), k5_setfam_1(u1_struct_0('#skF_1'), k4_xboole_0('#skF_2', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_593, c_277])).
% 4.81/1.97  tff(c_3228, plain, (~r1_tarski(k7_subset_1(u1_struct_0('#skF_1'), k3_tarski('#skF_2'), k3_tarski('#skF_3')), k3_tarski(k4_xboole_0('#skF_2', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_3226, c_706])).
% 4.81/1.97  tff(c_3456, plain, (~r1_tarski(k4_xboole_0(k3_tarski('#skF_2'), k3_tarski('#skF_3')), k3_tarski(k4_xboole_0('#skF_2', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_3454, c_3228])).
% 4.81/1.97  tff(c_3477, plain, (~r1_tarski(k3_tarski('#skF_2'), k2_xboole_0(k3_tarski('#skF_3'), k3_tarski(k4_xboole_0('#skF_2', '#skF_3'))))), inference(resolution, [status(thm)], [c_8, c_3456])).
% 4.81/1.97  tff(c_3484, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_165, c_6, c_14, c_3477])).
% 4.81/1.97  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.81/1.97  
% 4.81/1.97  Inference rules
% 4.81/1.97  ----------------------
% 4.81/1.97  #Ref     : 0
% 4.81/1.97  #Sup     : 930
% 4.81/1.97  #Fact    : 0
% 4.81/1.97  #Define  : 0
% 4.81/1.97  #Split   : 0
% 4.81/1.97  #Chain   : 0
% 4.81/1.97  #Close   : 0
% 4.81/1.97  
% 4.81/1.97  Ordering : KBO
% 4.81/1.97  
% 4.81/1.97  Simplification rules
% 4.81/1.97  ----------------------
% 4.81/1.97  #Subsume      : 16
% 4.81/1.97  #Demod        : 466
% 4.81/1.97  #Tautology    : 381
% 4.81/1.97  #SimpNegUnit  : 0
% 4.81/1.97  #BackRed      : 6
% 4.81/1.97  
% 4.81/1.97  #Partial instantiations: 0
% 4.81/1.97  #Strategies tried      : 1
% 4.81/1.97  
% 4.81/1.97  Timing (in seconds)
% 4.81/1.97  ----------------------
% 4.81/1.97  Preprocessing        : 0.30
% 4.81/1.97  Parsing              : 0.16
% 4.81/1.97  CNF conversion       : 0.02
% 4.81/1.97  Main loop            : 0.82
% 4.81/1.97  Inferencing          : 0.22
% 4.81/1.97  Reduction            : 0.38
% 4.81/1.97  Demodulation         : 0.32
% 4.81/1.97  BG Simplification    : 0.03
% 4.81/1.97  Subsumption          : 0.13
% 4.81/1.97  Abstraction          : 0.04
% 4.81/1.97  MUC search           : 0.00
% 4.81/1.97  Cooper               : 0.00
% 4.81/1.97  Total                : 1.16
% 4.81/1.97  Index Insertion      : 0.00
% 4.81/1.97  Index Deletion       : 0.00
% 4.81/1.97  Index Matching       : 0.00
% 4.81/1.97  BG Taut test         : 0.00
%------------------------------------------------------------------------------
