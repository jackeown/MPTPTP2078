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

% Result     : Theorem 7.93s
% Output     : CNFRefutation 8.26s
% Verified   : 
% Statistics : Number of formulae       :   61 (  83 expanded)
%              Number of leaves         :   28 (  40 expanded)
%              Depth                    :    9
%              Number of atoms          :   65 ( 114 expanded)
%              Number of equality atoms :   15 (  26 expanded)
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

tff(f_47,axiom,(
    ! [A,B] : k3_tarski(k2_xboole_0(A,B)) = k2_xboole_0(k3_tarski(A),k3_tarski(B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t96_zfmisc_1)).

tff(f_33,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k4_xboole_0(A,B),C)
     => r1_tarski(A,k2_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_74,negated_conjecture,(
    ~ ! [A] :
        ( l1_struct_0(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
               => r1_tarski(k7_subset_1(u1_struct_0(A),k5_setfam_1(u1_struct_0(A),B),k5_setfam_1(u1_struct_0(A),C)),k5_setfam_1(u1_struct_0(A),k7_subset_1(k1_zfmisc_1(u1_struct_0(A)),B,C))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_tops_2)).

tff(f_63,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(k4_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t109_xboole_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => k5_setfam_1(A,B) = k3_tarski(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k5_setfam_1)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k2_xboole_0(B,C))
     => r1_tarski(k4_xboole_0(A,B),C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_xboole_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => m1_subset_1(k5_setfam_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_setfam_1)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

tff(c_16,plain,(
    ! [A_18,B_19] : k2_xboole_0(k3_tarski(A_18),k3_tarski(B_19)) = k3_tarski(k2_xboole_0(A_18,B_19)) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_6,plain,(
    ! [A_6,B_7] : r1_tarski(k4_xboole_0(A_6,B_7),A_6) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_257,plain,(
    ! [A_57,B_58,C_59] :
      ( r1_tarski(A_57,k2_xboole_0(B_58,C_59))
      | ~ r1_tarski(k4_xboole_0(A_57,B_58),C_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_270,plain,(
    ! [A_60,B_61] : r1_tarski(A_60,k2_xboole_0(B_61,A_60)) ),
    inference(resolution,[status(thm)],[c_6,c_257])).

tff(c_280,plain,(
    ! [B_19,A_18] : r1_tarski(k3_tarski(B_19),k3_tarski(k2_xboole_0(A_18,B_19))) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_270])).

tff(c_8,plain,(
    ! [A_8,B_9] : k2_xboole_0(A_8,k4_xboole_0(B_9,A_8)) = k2_xboole_0(A_8,B_9) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_32,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_70,plain,(
    ! [A_39,B_40] :
      ( r1_tarski(A_39,B_40)
      | ~ m1_subset_1(A_39,k1_zfmisc_1(B_40)) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_82,plain,(
    r1_tarski('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_32,c_70])).

tff(c_4,plain,(
    ! [A_3,C_5,B_4] :
      ( r1_tarski(k4_xboole_0(A_3,C_5),B_4)
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_26,plain,(
    ! [A_27,B_28] :
      ( m1_subset_1(A_27,k1_zfmisc_1(B_28))
      | ~ r1_tarski(A_27,B_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_383,plain,(
    ! [A_68,B_69] :
      ( k5_setfam_1(A_68,B_69) = k3_tarski(B_69)
      | ~ m1_subset_1(B_69,k1_zfmisc_1(k1_zfmisc_1(A_68))) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_606,plain,(
    ! [A_90,A_91] :
      ( k5_setfam_1(A_90,A_91) = k3_tarski(A_91)
      | ~ r1_tarski(A_91,k1_zfmisc_1(A_90)) ) ),
    inference(resolution,[status(thm)],[c_26,c_383])).

tff(c_7367,plain,(
    ! [A_388,A_389,C_390] :
      ( k5_setfam_1(A_388,k4_xboole_0(A_389,C_390)) = k3_tarski(k4_xboole_0(A_389,C_390))
      | ~ r1_tarski(A_389,k1_zfmisc_1(A_388)) ) ),
    inference(resolution,[status(thm)],[c_4,c_606])).

tff(c_7391,plain,(
    ! [C_390] : k5_setfam_1(u1_struct_0('#skF_1'),k4_xboole_0('#skF_2',C_390)) = k3_tarski(k4_xboole_0('#skF_2',C_390)) ),
    inference(resolution,[status(thm)],[c_82,c_7367])).

tff(c_10,plain,(
    ! [A_10,B_11,C_12] :
      ( r1_tarski(k4_xboole_0(A_10,B_11),C_12)
      | ~ r1_tarski(A_10,k2_xboole_0(B_11,C_12)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_396,plain,(
    k5_setfam_1(u1_struct_0('#skF_1'),'#skF_2') = k3_tarski('#skF_2') ),
    inference(resolution,[status(thm)],[c_32,c_383])).

tff(c_475,plain,(
    ! [A_76,B_77] :
      ( m1_subset_1(k5_setfam_1(A_76,B_77),k1_zfmisc_1(A_76))
      | ~ m1_subset_1(B_77,k1_zfmisc_1(k1_zfmisc_1(A_76))) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_485,plain,
    ( m1_subset_1(k3_tarski('#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ),
    inference(superposition,[status(thm),theory(equality)],[c_396,c_475])).

tff(c_492,plain,(
    m1_subset_1(k3_tarski('#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_485])).

tff(c_533,plain,(
    ! [A_80,B_81,C_82] :
      ( k7_subset_1(A_80,B_81,C_82) = k4_xboole_0(B_81,C_82)
      | ~ m1_subset_1(B_81,k1_zfmisc_1(A_80)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_547,plain,(
    ! [C_82] : k7_subset_1(u1_struct_0('#skF_1'),k3_tarski('#skF_2'),C_82) = k4_xboole_0(k3_tarski('#skF_2'),C_82) ),
    inference(resolution,[status(thm)],[c_492,c_533])).

tff(c_551,plain,(
    ! [C_82] : k7_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')),'#skF_2',C_82) = k4_xboole_0('#skF_2',C_82) ),
    inference(resolution,[status(thm)],[c_32,c_533])).

tff(c_30,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_395,plain,(
    k5_setfam_1(u1_struct_0('#skF_1'),'#skF_3') = k3_tarski('#skF_3') ),
    inference(resolution,[status(thm)],[c_30,c_383])).

tff(c_28,plain,(
    ~ r1_tarski(k7_subset_1(u1_struct_0('#skF_1'),k5_setfam_1(u1_struct_0('#skF_1'),'#skF_2'),k5_setfam_1(u1_struct_0('#skF_1'),'#skF_3')),k5_setfam_1(u1_struct_0('#skF_1'),k7_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')),'#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_397,plain,(
    ~ r1_tarski(k7_subset_1(u1_struct_0('#skF_1'),k5_setfam_1(u1_struct_0('#skF_1'),'#skF_2'),k3_tarski('#skF_3')),k5_setfam_1(u1_struct_0('#skF_1'),k7_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')),'#skF_2','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_395,c_28])).

tff(c_426,plain,(
    ~ r1_tarski(k7_subset_1(u1_struct_0('#skF_1'),k3_tarski('#skF_2'),k3_tarski('#skF_3')),k5_setfam_1(u1_struct_0('#skF_1'),k7_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')),'#skF_2','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_396,c_397])).

tff(c_575,plain,(
    ~ r1_tarski(k7_subset_1(u1_struct_0('#skF_1'),k3_tarski('#skF_2'),k3_tarski('#skF_3')),k5_setfam_1(u1_struct_0('#skF_1'),k4_xboole_0('#skF_2','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_551,c_426])).

tff(c_891,plain,(
    ~ r1_tarski(k4_xboole_0(k3_tarski('#skF_2'),k3_tarski('#skF_3')),k5_setfam_1(u1_struct_0('#skF_1'),k4_xboole_0('#skF_2','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_547,c_575])).

tff(c_1298,plain,(
    ~ r1_tarski(k3_tarski('#skF_2'),k2_xboole_0(k3_tarski('#skF_3'),k5_setfam_1(u1_struct_0('#skF_1'),k4_xboole_0('#skF_2','#skF_3')))) ),
    inference(resolution,[status(thm)],[c_10,c_891])).

tff(c_7394,plain,(
    ~ r1_tarski(k3_tarski('#skF_2'),k2_xboole_0(k3_tarski('#skF_3'),k3_tarski(k4_xboole_0('#skF_2','#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7391,c_1298])).

tff(c_7399,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_280,c_8,c_16,c_7394])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:38:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.93/3.03  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.93/3.04  
% 7.93/3.04  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.93/3.04  %$ r1_tarski > m1_subset_1 > l1_struct_0 > k7_subset_1 > k5_setfam_1 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > u1_struct_0 > k3_tarski > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1
% 7.93/3.04  
% 7.93/3.04  %Foreground sorts:
% 7.93/3.04  
% 7.93/3.04  
% 7.93/3.04  %Background operators:
% 7.93/3.04  
% 7.93/3.04  
% 7.93/3.04  %Foreground operators:
% 7.93/3.04  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.93/3.04  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 7.93/3.04  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.93/3.04  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 7.93/3.04  tff('#skF_2', type, '#skF_2': $i).
% 7.93/3.04  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 7.93/3.04  tff('#skF_3', type, '#skF_3': $i).
% 7.93/3.04  tff('#skF_1', type, '#skF_1': $i).
% 7.93/3.04  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 7.93/3.04  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 7.93/3.04  tff(k5_setfam_1, type, k5_setfam_1: ($i * $i) > $i).
% 7.93/3.04  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.93/3.04  tff(k3_tarski, type, k3_tarski: $i > $i).
% 7.93/3.04  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.93/3.04  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 7.93/3.04  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 7.93/3.04  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 7.93/3.04  
% 8.26/3.05  tff(f_47, axiom, (![A, B]: (k3_tarski(k2_xboole_0(A, B)) = k2_xboole_0(k3_tarski(A), k3_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t96_zfmisc_1)).
% 8.26/3.05  tff(f_33, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 8.26/3.05  tff(f_43, axiom, (![A, B, C]: (r1_tarski(k4_xboole_0(A, B), C) => r1_tarski(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_xboole_1)).
% 8.26/3.05  tff(f_35, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_xboole_1)).
% 8.26/3.05  tff(f_74, negated_conjecture, ~(![A]: (l1_struct_0(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => r1_tarski(k7_subset_1(u1_struct_0(A), k5_setfam_1(u1_struct_0(A), B), k5_setfam_1(u1_struct_0(A), C)), k5_setfam_1(u1_struct_0(A), k7_subset_1(k1_zfmisc_1(u1_struct_0(A)), B, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_tops_2)).
% 8.26/3.05  tff(f_63, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 8.26/3.05  tff(f_31, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(k4_xboole_0(A, C), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t109_xboole_1)).
% 8.26/3.05  tff(f_59, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (k5_setfam_1(A, B) = k3_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k5_setfam_1)).
% 8.26/3.05  tff(f_39, axiom, (![A, B, C]: (r1_tarski(A, k2_xboole_0(B, C)) => r1_tarski(k4_xboole_0(A, B), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_xboole_1)).
% 8.26/3.05  tff(f_55, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => m1_subset_1(k5_setfam_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k5_setfam_1)).
% 8.26/3.05  tff(f_51, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 8.26/3.05  tff(c_16, plain, (![A_18, B_19]: (k2_xboole_0(k3_tarski(A_18), k3_tarski(B_19))=k3_tarski(k2_xboole_0(A_18, B_19)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 8.26/3.05  tff(c_6, plain, (![A_6, B_7]: (r1_tarski(k4_xboole_0(A_6, B_7), A_6))), inference(cnfTransformation, [status(thm)], [f_33])).
% 8.26/3.05  tff(c_257, plain, (![A_57, B_58, C_59]: (r1_tarski(A_57, k2_xboole_0(B_58, C_59)) | ~r1_tarski(k4_xboole_0(A_57, B_58), C_59))), inference(cnfTransformation, [status(thm)], [f_43])).
% 8.26/3.05  tff(c_270, plain, (![A_60, B_61]: (r1_tarski(A_60, k2_xboole_0(B_61, A_60)))), inference(resolution, [status(thm)], [c_6, c_257])).
% 8.26/3.05  tff(c_280, plain, (![B_19, A_18]: (r1_tarski(k3_tarski(B_19), k3_tarski(k2_xboole_0(A_18, B_19))))), inference(superposition, [status(thm), theory('equality')], [c_16, c_270])).
% 8.26/3.05  tff(c_8, plain, (![A_8, B_9]: (k2_xboole_0(A_8, k4_xboole_0(B_9, A_8))=k2_xboole_0(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_35])).
% 8.26/3.05  tff(c_32, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 8.26/3.05  tff(c_70, plain, (![A_39, B_40]: (r1_tarski(A_39, B_40) | ~m1_subset_1(A_39, k1_zfmisc_1(B_40)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 8.26/3.05  tff(c_82, plain, (r1_tarski('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_32, c_70])).
% 8.26/3.05  tff(c_4, plain, (![A_3, C_5, B_4]: (r1_tarski(k4_xboole_0(A_3, C_5), B_4) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 8.26/3.05  tff(c_26, plain, (![A_27, B_28]: (m1_subset_1(A_27, k1_zfmisc_1(B_28)) | ~r1_tarski(A_27, B_28))), inference(cnfTransformation, [status(thm)], [f_63])).
% 8.26/3.05  tff(c_383, plain, (![A_68, B_69]: (k5_setfam_1(A_68, B_69)=k3_tarski(B_69) | ~m1_subset_1(B_69, k1_zfmisc_1(k1_zfmisc_1(A_68))))), inference(cnfTransformation, [status(thm)], [f_59])).
% 8.26/3.05  tff(c_606, plain, (![A_90, A_91]: (k5_setfam_1(A_90, A_91)=k3_tarski(A_91) | ~r1_tarski(A_91, k1_zfmisc_1(A_90)))), inference(resolution, [status(thm)], [c_26, c_383])).
% 8.26/3.05  tff(c_7367, plain, (![A_388, A_389, C_390]: (k5_setfam_1(A_388, k4_xboole_0(A_389, C_390))=k3_tarski(k4_xboole_0(A_389, C_390)) | ~r1_tarski(A_389, k1_zfmisc_1(A_388)))), inference(resolution, [status(thm)], [c_4, c_606])).
% 8.26/3.05  tff(c_7391, plain, (![C_390]: (k5_setfam_1(u1_struct_0('#skF_1'), k4_xboole_0('#skF_2', C_390))=k3_tarski(k4_xboole_0('#skF_2', C_390)))), inference(resolution, [status(thm)], [c_82, c_7367])).
% 8.26/3.05  tff(c_10, plain, (![A_10, B_11, C_12]: (r1_tarski(k4_xboole_0(A_10, B_11), C_12) | ~r1_tarski(A_10, k2_xboole_0(B_11, C_12)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 8.26/3.05  tff(c_396, plain, (k5_setfam_1(u1_struct_0('#skF_1'), '#skF_2')=k3_tarski('#skF_2')), inference(resolution, [status(thm)], [c_32, c_383])).
% 8.26/3.05  tff(c_475, plain, (![A_76, B_77]: (m1_subset_1(k5_setfam_1(A_76, B_77), k1_zfmisc_1(A_76)) | ~m1_subset_1(B_77, k1_zfmisc_1(k1_zfmisc_1(A_76))))), inference(cnfTransformation, [status(thm)], [f_55])).
% 8.26/3.05  tff(c_485, plain, (m1_subset_1(k3_tarski('#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1('#skF_2', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(superposition, [status(thm), theory('equality')], [c_396, c_475])).
% 8.26/3.05  tff(c_492, plain, (m1_subset_1(k3_tarski('#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_485])).
% 8.26/3.05  tff(c_533, plain, (![A_80, B_81, C_82]: (k7_subset_1(A_80, B_81, C_82)=k4_xboole_0(B_81, C_82) | ~m1_subset_1(B_81, k1_zfmisc_1(A_80)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 8.26/3.05  tff(c_547, plain, (![C_82]: (k7_subset_1(u1_struct_0('#skF_1'), k3_tarski('#skF_2'), C_82)=k4_xboole_0(k3_tarski('#skF_2'), C_82))), inference(resolution, [status(thm)], [c_492, c_533])).
% 8.26/3.05  tff(c_551, plain, (![C_82]: (k7_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')), '#skF_2', C_82)=k4_xboole_0('#skF_2', C_82))), inference(resolution, [status(thm)], [c_32, c_533])).
% 8.26/3.05  tff(c_30, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 8.26/3.05  tff(c_395, plain, (k5_setfam_1(u1_struct_0('#skF_1'), '#skF_3')=k3_tarski('#skF_3')), inference(resolution, [status(thm)], [c_30, c_383])).
% 8.26/3.05  tff(c_28, plain, (~r1_tarski(k7_subset_1(u1_struct_0('#skF_1'), k5_setfam_1(u1_struct_0('#skF_1'), '#skF_2'), k5_setfam_1(u1_struct_0('#skF_1'), '#skF_3')), k5_setfam_1(u1_struct_0('#skF_1'), k7_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')), '#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_74])).
% 8.26/3.05  tff(c_397, plain, (~r1_tarski(k7_subset_1(u1_struct_0('#skF_1'), k5_setfam_1(u1_struct_0('#skF_1'), '#skF_2'), k3_tarski('#skF_3')), k5_setfam_1(u1_struct_0('#skF_1'), k7_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')), '#skF_2', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_395, c_28])).
% 8.26/3.05  tff(c_426, plain, (~r1_tarski(k7_subset_1(u1_struct_0('#skF_1'), k3_tarski('#skF_2'), k3_tarski('#skF_3')), k5_setfam_1(u1_struct_0('#skF_1'), k7_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')), '#skF_2', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_396, c_397])).
% 8.26/3.05  tff(c_575, plain, (~r1_tarski(k7_subset_1(u1_struct_0('#skF_1'), k3_tarski('#skF_2'), k3_tarski('#skF_3')), k5_setfam_1(u1_struct_0('#skF_1'), k4_xboole_0('#skF_2', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_551, c_426])).
% 8.26/3.05  tff(c_891, plain, (~r1_tarski(k4_xboole_0(k3_tarski('#skF_2'), k3_tarski('#skF_3')), k5_setfam_1(u1_struct_0('#skF_1'), k4_xboole_0('#skF_2', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_547, c_575])).
% 8.26/3.05  tff(c_1298, plain, (~r1_tarski(k3_tarski('#skF_2'), k2_xboole_0(k3_tarski('#skF_3'), k5_setfam_1(u1_struct_0('#skF_1'), k4_xboole_0('#skF_2', '#skF_3'))))), inference(resolution, [status(thm)], [c_10, c_891])).
% 8.26/3.05  tff(c_7394, plain, (~r1_tarski(k3_tarski('#skF_2'), k2_xboole_0(k3_tarski('#skF_3'), k3_tarski(k4_xboole_0('#skF_2', '#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_7391, c_1298])).
% 8.26/3.05  tff(c_7399, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_280, c_8, c_16, c_7394])).
% 8.26/3.05  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.26/3.05  
% 8.26/3.05  Inference rules
% 8.26/3.05  ----------------------
% 8.26/3.05  #Ref     : 0
% 8.26/3.05  #Sup     : 1983
% 8.26/3.05  #Fact    : 0
% 8.26/3.05  #Define  : 0
% 8.26/3.05  #Split   : 0
% 8.26/3.05  #Chain   : 0
% 8.26/3.05  #Close   : 0
% 8.26/3.05  
% 8.26/3.05  Ordering : KBO
% 8.26/3.05  
% 8.26/3.05  Simplification rules
% 8.26/3.05  ----------------------
% 8.26/3.05  #Subsume      : 27
% 8.26/3.05  #Demod        : 840
% 8.26/3.05  #Tautology    : 539
% 8.26/3.05  #SimpNegUnit  : 0
% 8.26/3.05  #BackRed      : 6
% 8.26/3.05  
% 8.26/3.05  #Partial instantiations: 0
% 8.26/3.05  #Strategies tried      : 1
% 8.26/3.05  
% 8.26/3.05  Timing (in seconds)
% 8.26/3.05  ----------------------
% 8.26/3.05  Preprocessing        : 0.35
% 8.26/3.05  Parsing              : 0.18
% 8.26/3.05  CNF conversion       : 0.02
% 8.26/3.05  Main loop            : 1.83
% 8.26/3.05  Inferencing          : 0.40
% 8.26/3.05  Reduction            : 0.91
% 8.26/3.05  Demodulation         : 0.80
% 8.26/3.05  BG Simplification    : 0.06
% 8.26/3.05  Subsumption          : 0.35
% 8.26/3.05  Abstraction          : 0.07
% 8.26/3.06  MUC search           : 0.00
% 8.26/3.06  Cooper               : 0.00
% 8.26/3.06  Total                : 2.21
% 8.26/3.06  Index Insertion      : 0.00
% 8.26/3.06  Index Deletion       : 0.00
% 8.26/3.06  Index Matching       : 0.00
% 8.26/3.06  BG Taut test         : 0.00
%------------------------------------------------------------------------------
