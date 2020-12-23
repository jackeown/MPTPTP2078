%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:22:36 EST 2020

% Result     : Theorem 8.33s
% Output     : CNFRefutation 8.49s
% Verified   : 
% Statistics : Number of formulae       :   62 (  86 expanded)
%              Number of leaves         :   28 (  41 expanded)
%              Depth                    :    9
%              Number of atoms          :   68 ( 119 expanded)
%              Number of equality atoms :   16 (  29 expanded)
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

tff(f_51,axiom,(
    ! [A,B] : k3_tarski(k2_xboole_0(A,B)) = k2_xboole_0(k3_tarski(A),k3_tarski(B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t96_zfmisc_1)).

tff(f_39,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_47,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k4_xboole_0(A,B),C)
     => r1_tarski(A,k2_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_xboole_1)).

tff(f_78,negated_conjecture,(
    ~ ! [A] :
        ( l1_struct_0(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
               => r1_tarski(k7_subset_1(u1_struct_0(A),k5_setfam_1(u1_struct_0(A),B),k5_setfam_1(u1_struct_0(A),C)),k5_setfam_1(u1_struct_0(A),k7_subset_1(k1_zfmisc_1(u1_struct_0(A)),B,C))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_tops_2)).

tff(f_67,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(k4_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t109_xboole_1)).

tff(f_63,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => k5_setfam_1(A,B) = k3_tarski(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k5_setfam_1)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k2_xboole_0(B,C))
     => r1_tarski(k4_xboole_0(A,B),C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_xboole_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => m1_subset_1(k5_setfam_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_setfam_1)).

tff(f_55,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

tff(c_20,plain,(
    ! [A_18,B_19] : k2_xboole_0(k3_tarski(A_18),k3_tarski(B_19)) = k3_tarski(k2_xboole_0(A_18,B_19)) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_12,plain,(
    ! [A_8,B_9] : k2_xboole_0(A_8,k4_xboole_0(B_9,A_8)) = k2_xboole_0(A_8,B_9) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_8,plain,(
    ! [B_4] : r1_tarski(B_4,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_331,plain,(
    ! [A_60,B_61,C_62] :
      ( r1_tarski(A_60,k2_xboole_0(B_61,C_62))
      | ~ r1_tarski(k4_xboole_0(A_60,B_61),C_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_338,plain,(
    ! [A_60,B_61] : r1_tarski(A_60,k2_xboole_0(B_61,k4_xboole_0(A_60,B_61))) ),
    inference(resolution,[status(thm)],[c_8,c_331])).

tff(c_342,plain,(
    ! [A_63,B_64] : r1_tarski(A_63,k2_xboole_0(B_64,A_63)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_338])).

tff(c_354,plain,(
    ! [B_19,A_18] : r1_tarski(k3_tarski(B_19),k3_tarski(k2_xboole_0(A_18,B_19))) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_342])).

tff(c_36,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_75,plain,(
    ! [A_38,B_39] :
      ( r1_tarski(A_38,B_39)
      | ~ m1_subset_1(A_38,k1_zfmisc_1(B_39)) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_87,plain,(
    r1_tarski('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_36,c_75])).

tff(c_10,plain,(
    ! [A_5,C_7,B_6] :
      ( r1_tarski(k4_xboole_0(A_5,C_7),B_6)
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_30,plain,(
    ! [A_27,B_28] :
      ( m1_subset_1(A_27,k1_zfmisc_1(B_28))
      | ~ r1_tarski(A_27,B_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_150,plain,(
    ! [A_51,B_52] :
      ( k5_setfam_1(A_51,B_52) = k3_tarski(B_52)
      | ~ m1_subset_1(B_52,k1_zfmisc_1(k1_zfmisc_1(A_51))) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_300,plain,(
    ! [A_57,A_58] :
      ( k5_setfam_1(A_57,A_58) = k3_tarski(A_58)
      | ~ r1_tarski(A_58,k1_zfmisc_1(A_57)) ) ),
    inference(resolution,[status(thm)],[c_30,c_150])).

tff(c_8707,plain,(
    ! [A_368,A_369,C_370] :
      ( k5_setfam_1(A_368,k4_xboole_0(A_369,C_370)) = k3_tarski(k4_xboole_0(A_369,C_370))
      | ~ r1_tarski(A_369,k1_zfmisc_1(A_368)) ) ),
    inference(resolution,[status(thm)],[c_10,c_300])).

tff(c_8735,plain,(
    ! [C_370] : k5_setfam_1(u1_struct_0('#skF_1'),k4_xboole_0('#skF_2',C_370)) = k3_tarski(k4_xboole_0('#skF_2',C_370)) ),
    inference(resolution,[status(thm)],[c_87,c_8707])).

tff(c_14,plain,(
    ! [A_10,B_11,C_12] :
      ( r1_tarski(k4_xboole_0(A_10,B_11),C_12)
      | ~ r1_tarski(A_10,k2_xboole_0(B_11,C_12)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_163,plain,(
    k5_setfam_1(u1_struct_0('#skF_1'),'#skF_2') = k3_tarski('#skF_2') ),
    inference(resolution,[status(thm)],[c_36,c_150])).

tff(c_562,plain,(
    ! [A_80,B_81] :
      ( m1_subset_1(k5_setfam_1(A_80,B_81),k1_zfmisc_1(A_80))
      | ~ m1_subset_1(B_81,k1_zfmisc_1(k1_zfmisc_1(A_80))) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_575,plain,
    ( m1_subset_1(k3_tarski('#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ),
    inference(superposition,[status(thm),theory(equality)],[c_163,c_562])).

tff(c_582,plain,(
    m1_subset_1(k3_tarski('#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_575])).

tff(c_655,plain,(
    ! [A_87,B_88,C_89] :
      ( k7_subset_1(A_87,B_88,C_89) = k4_xboole_0(B_88,C_89)
      | ~ m1_subset_1(B_88,k1_zfmisc_1(A_87)) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_669,plain,(
    ! [C_89] : k7_subset_1(u1_struct_0('#skF_1'),k3_tarski('#skF_2'),C_89) = k4_xboole_0(k3_tarski('#skF_2'),C_89) ),
    inference(resolution,[status(thm)],[c_582,c_655])).

tff(c_673,plain,(
    ! [C_89] : k7_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')),'#skF_2',C_89) = k4_xboole_0('#skF_2',C_89) ),
    inference(resolution,[status(thm)],[c_36,c_655])).

tff(c_34,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_162,plain,(
    k5_setfam_1(u1_struct_0('#skF_1'),'#skF_3') = k3_tarski('#skF_3') ),
    inference(resolution,[status(thm)],[c_34,c_150])).

tff(c_32,plain,(
    ~ r1_tarski(k7_subset_1(u1_struct_0('#skF_1'),k5_setfam_1(u1_struct_0('#skF_1'),'#skF_2'),k5_setfam_1(u1_struct_0('#skF_1'),'#skF_3')),k5_setfam_1(u1_struct_0('#skF_1'),k7_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')),'#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_164,plain,(
    ~ r1_tarski(k7_subset_1(u1_struct_0('#skF_1'),k5_setfam_1(u1_struct_0('#skF_1'),'#skF_2'),k3_tarski('#skF_3')),k5_setfam_1(u1_struct_0('#skF_1'),k7_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')),'#skF_2','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_162,c_32])).

tff(c_210,plain,(
    ~ r1_tarski(k7_subset_1(u1_struct_0('#skF_1'),k3_tarski('#skF_2'),k3_tarski('#skF_3')),k5_setfam_1(u1_struct_0('#skF_1'),k7_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')),'#skF_2','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_163,c_164])).

tff(c_708,plain,(
    ~ r1_tarski(k7_subset_1(u1_struct_0('#skF_1'),k3_tarski('#skF_2'),k3_tarski('#skF_3')),k5_setfam_1(u1_struct_0('#skF_1'),k4_xboole_0('#skF_2','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_673,c_210])).

tff(c_1106,plain,(
    ~ r1_tarski(k4_xboole_0(k3_tarski('#skF_2'),k3_tarski('#skF_3')),k5_setfam_1(u1_struct_0('#skF_1'),k4_xboole_0('#skF_2','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_669,c_708])).

tff(c_1562,plain,(
    ~ r1_tarski(k3_tarski('#skF_2'),k2_xboole_0(k3_tarski('#skF_3'),k5_setfam_1(u1_struct_0('#skF_1'),k4_xboole_0('#skF_2','#skF_3')))) ),
    inference(resolution,[status(thm)],[c_14,c_1106])).

tff(c_8738,plain,(
    ~ r1_tarski(k3_tarski('#skF_2'),k2_xboole_0(k3_tarski('#skF_3'),k3_tarski(k4_xboole_0('#skF_2','#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8735,c_1562])).

tff(c_8743,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_354,c_12,c_20,c_8738])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:49:08 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.33/2.99  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.33/2.99  
% 8.33/2.99  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.33/2.99  %$ r1_tarski > m1_subset_1 > l1_struct_0 > k7_subset_1 > k5_setfam_1 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > u1_struct_0 > k3_tarski > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1
% 8.33/2.99  
% 8.33/2.99  %Foreground sorts:
% 8.33/2.99  
% 8.33/2.99  
% 8.33/2.99  %Background operators:
% 8.33/2.99  
% 8.33/2.99  
% 8.33/2.99  %Foreground operators:
% 8.33/2.99  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.33/2.99  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 8.33/2.99  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 8.33/2.99  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 8.33/2.99  tff('#skF_2', type, '#skF_2': $i).
% 8.33/2.99  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 8.33/2.99  tff('#skF_3', type, '#skF_3': $i).
% 8.33/2.99  tff('#skF_1', type, '#skF_1': $i).
% 8.33/2.99  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 8.33/2.99  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 8.33/2.99  tff(k5_setfam_1, type, k5_setfam_1: ($i * $i) > $i).
% 8.33/2.99  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.33/2.99  tff(k3_tarski, type, k3_tarski: $i > $i).
% 8.33/2.99  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.33/2.99  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 8.33/2.99  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 8.33/2.99  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 8.33/2.99  
% 8.49/3.01  tff(f_51, axiom, (![A, B]: (k3_tarski(k2_xboole_0(A, B)) = k2_xboole_0(k3_tarski(A), k3_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t96_zfmisc_1)).
% 8.49/3.01  tff(f_39, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_xboole_1)).
% 8.49/3.01  tff(f_33, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 8.49/3.01  tff(f_47, axiom, (![A, B, C]: (r1_tarski(k4_xboole_0(A, B), C) => r1_tarski(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_xboole_1)).
% 8.49/3.01  tff(f_78, negated_conjecture, ~(![A]: (l1_struct_0(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => r1_tarski(k7_subset_1(u1_struct_0(A), k5_setfam_1(u1_struct_0(A), B), k5_setfam_1(u1_struct_0(A), C)), k5_setfam_1(u1_struct_0(A), k7_subset_1(k1_zfmisc_1(u1_struct_0(A)), B, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_tops_2)).
% 8.49/3.01  tff(f_67, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 8.49/3.01  tff(f_37, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(k4_xboole_0(A, C), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t109_xboole_1)).
% 8.49/3.01  tff(f_63, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (k5_setfam_1(A, B) = k3_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k5_setfam_1)).
% 8.49/3.01  tff(f_43, axiom, (![A, B, C]: (r1_tarski(A, k2_xboole_0(B, C)) => r1_tarski(k4_xboole_0(A, B), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_xboole_1)).
% 8.49/3.01  tff(f_59, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => m1_subset_1(k5_setfam_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k5_setfam_1)).
% 8.49/3.01  tff(f_55, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 8.49/3.01  tff(c_20, plain, (![A_18, B_19]: (k2_xboole_0(k3_tarski(A_18), k3_tarski(B_19))=k3_tarski(k2_xboole_0(A_18, B_19)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 8.49/3.01  tff(c_12, plain, (![A_8, B_9]: (k2_xboole_0(A_8, k4_xboole_0(B_9, A_8))=k2_xboole_0(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_39])).
% 8.49/3.01  tff(c_8, plain, (![B_4]: (r1_tarski(B_4, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 8.49/3.01  tff(c_331, plain, (![A_60, B_61, C_62]: (r1_tarski(A_60, k2_xboole_0(B_61, C_62)) | ~r1_tarski(k4_xboole_0(A_60, B_61), C_62))), inference(cnfTransformation, [status(thm)], [f_47])).
% 8.49/3.01  tff(c_338, plain, (![A_60, B_61]: (r1_tarski(A_60, k2_xboole_0(B_61, k4_xboole_0(A_60, B_61))))), inference(resolution, [status(thm)], [c_8, c_331])).
% 8.49/3.01  tff(c_342, plain, (![A_63, B_64]: (r1_tarski(A_63, k2_xboole_0(B_64, A_63)))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_338])).
% 8.49/3.01  tff(c_354, plain, (![B_19, A_18]: (r1_tarski(k3_tarski(B_19), k3_tarski(k2_xboole_0(A_18, B_19))))), inference(superposition, [status(thm), theory('equality')], [c_20, c_342])).
% 8.49/3.01  tff(c_36, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(cnfTransformation, [status(thm)], [f_78])).
% 8.49/3.01  tff(c_75, plain, (![A_38, B_39]: (r1_tarski(A_38, B_39) | ~m1_subset_1(A_38, k1_zfmisc_1(B_39)))), inference(cnfTransformation, [status(thm)], [f_67])).
% 8.49/3.01  tff(c_87, plain, (r1_tarski('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_36, c_75])).
% 8.49/3.01  tff(c_10, plain, (![A_5, C_7, B_6]: (r1_tarski(k4_xboole_0(A_5, C_7), B_6) | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_37])).
% 8.49/3.01  tff(c_30, plain, (![A_27, B_28]: (m1_subset_1(A_27, k1_zfmisc_1(B_28)) | ~r1_tarski(A_27, B_28))), inference(cnfTransformation, [status(thm)], [f_67])).
% 8.49/3.01  tff(c_150, plain, (![A_51, B_52]: (k5_setfam_1(A_51, B_52)=k3_tarski(B_52) | ~m1_subset_1(B_52, k1_zfmisc_1(k1_zfmisc_1(A_51))))), inference(cnfTransformation, [status(thm)], [f_63])).
% 8.49/3.01  tff(c_300, plain, (![A_57, A_58]: (k5_setfam_1(A_57, A_58)=k3_tarski(A_58) | ~r1_tarski(A_58, k1_zfmisc_1(A_57)))), inference(resolution, [status(thm)], [c_30, c_150])).
% 8.49/3.01  tff(c_8707, plain, (![A_368, A_369, C_370]: (k5_setfam_1(A_368, k4_xboole_0(A_369, C_370))=k3_tarski(k4_xboole_0(A_369, C_370)) | ~r1_tarski(A_369, k1_zfmisc_1(A_368)))), inference(resolution, [status(thm)], [c_10, c_300])).
% 8.49/3.01  tff(c_8735, plain, (![C_370]: (k5_setfam_1(u1_struct_0('#skF_1'), k4_xboole_0('#skF_2', C_370))=k3_tarski(k4_xboole_0('#skF_2', C_370)))), inference(resolution, [status(thm)], [c_87, c_8707])).
% 8.49/3.01  tff(c_14, plain, (![A_10, B_11, C_12]: (r1_tarski(k4_xboole_0(A_10, B_11), C_12) | ~r1_tarski(A_10, k2_xboole_0(B_11, C_12)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 8.49/3.01  tff(c_163, plain, (k5_setfam_1(u1_struct_0('#skF_1'), '#skF_2')=k3_tarski('#skF_2')), inference(resolution, [status(thm)], [c_36, c_150])).
% 8.49/3.01  tff(c_562, plain, (![A_80, B_81]: (m1_subset_1(k5_setfam_1(A_80, B_81), k1_zfmisc_1(A_80)) | ~m1_subset_1(B_81, k1_zfmisc_1(k1_zfmisc_1(A_80))))), inference(cnfTransformation, [status(thm)], [f_59])).
% 8.49/3.01  tff(c_575, plain, (m1_subset_1(k3_tarski('#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1('#skF_2', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(superposition, [status(thm), theory('equality')], [c_163, c_562])).
% 8.49/3.01  tff(c_582, plain, (m1_subset_1(k3_tarski('#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_575])).
% 8.49/3.01  tff(c_655, plain, (![A_87, B_88, C_89]: (k7_subset_1(A_87, B_88, C_89)=k4_xboole_0(B_88, C_89) | ~m1_subset_1(B_88, k1_zfmisc_1(A_87)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 8.49/3.01  tff(c_669, plain, (![C_89]: (k7_subset_1(u1_struct_0('#skF_1'), k3_tarski('#skF_2'), C_89)=k4_xboole_0(k3_tarski('#skF_2'), C_89))), inference(resolution, [status(thm)], [c_582, c_655])).
% 8.49/3.01  tff(c_673, plain, (![C_89]: (k7_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')), '#skF_2', C_89)=k4_xboole_0('#skF_2', C_89))), inference(resolution, [status(thm)], [c_36, c_655])).
% 8.49/3.01  tff(c_34, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(cnfTransformation, [status(thm)], [f_78])).
% 8.49/3.01  tff(c_162, plain, (k5_setfam_1(u1_struct_0('#skF_1'), '#skF_3')=k3_tarski('#skF_3')), inference(resolution, [status(thm)], [c_34, c_150])).
% 8.49/3.01  tff(c_32, plain, (~r1_tarski(k7_subset_1(u1_struct_0('#skF_1'), k5_setfam_1(u1_struct_0('#skF_1'), '#skF_2'), k5_setfam_1(u1_struct_0('#skF_1'), '#skF_3')), k5_setfam_1(u1_struct_0('#skF_1'), k7_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')), '#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_78])).
% 8.49/3.01  tff(c_164, plain, (~r1_tarski(k7_subset_1(u1_struct_0('#skF_1'), k5_setfam_1(u1_struct_0('#skF_1'), '#skF_2'), k3_tarski('#skF_3')), k5_setfam_1(u1_struct_0('#skF_1'), k7_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')), '#skF_2', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_162, c_32])).
% 8.49/3.01  tff(c_210, plain, (~r1_tarski(k7_subset_1(u1_struct_0('#skF_1'), k3_tarski('#skF_2'), k3_tarski('#skF_3')), k5_setfam_1(u1_struct_0('#skF_1'), k7_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')), '#skF_2', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_163, c_164])).
% 8.49/3.01  tff(c_708, plain, (~r1_tarski(k7_subset_1(u1_struct_0('#skF_1'), k3_tarski('#skF_2'), k3_tarski('#skF_3')), k5_setfam_1(u1_struct_0('#skF_1'), k4_xboole_0('#skF_2', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_673, c_210])).
% 8.49/3.01  tff(c_1106, plain, (~r1_tarski(k4_xboole_0(k3_tarski('#skF_2'), k3_tarski('#skF_3')), k5_setfam_1(u1_struct_0('#skF_1'), k4_xboole_0('#skF_2', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_669, c_708])).
% 8.49/3.01  tff(c_1562, plain, (~r1_tarski(k3_tarski('#skF_2'), k2_xboole_0(k3_tarski('#skF_3'), k5_setfam_1(u1_struct_0('#skF_1'), k4_xboole_0('#skF_2', '#skF_3'))))), inference(resolution, [status(thm)], [c_14, c_1106])).
% 8.49/3.01  tff(c_8738, plain, (~r1_tarski(k3_tarski('#skF_2'), k2_xboole_0(k3_tarski('#skF_3'), k3_tarski(k4_xboole_0('#skF_2', '#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_8735, c_1562])).
% 8.49/3.01  tff(c_8743, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_354, c_12, c_20, c_8738])).
% 8.49/3.01  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.49/3.01  
% 8.49/3.01  Inference rules
% 8.49/3.01  ----------------------
% 8.49/3.01  #Ref     : 0
% 8.49/3.01  #Sup     : 2313
% 8.49/3.01  #Fact    : 0
% 8.49/3.01  #Define  : 0
% 8.49/3.01  #Split   : 4
% 8.49/3.01  #Chain   : 0
% 8.49/3.01  #Close   : 0
% 8.49/3.01  
% 8.49/3.01  Ordering : KBO
% 8.49/3.01  
% 8.49/3.01  Simplification rules
% 8.49/3.01  ----------------------
% 8.49/3.01  #Subsume      : 44
% 8.49/3.01  #Demod        : 1071
% 8.49/3.01  #Tautology    : 512
% 8.49/3.01  #SimpNegUnit  : 0
% 8.49/3.01  #BackRed      : 6
% 8.49/3.01  
% 8.49/3.01  #Partial instantiations: 0
% 8.49/3.01  #Strategies tried      : 1
% 8.49/3.01  
% 8.49/3.01  Timing (in seconds)
% 8.49/3.01  ----------------------
% 8.49/3.01  Preprocessing        : 0.30
% 8.49/3.01  Parsing              : 0.15
% 8.49/3.01  CNF conversion       : 0.02
% 8.49/3.01  Main loop            : 1.94
% 8.49/3.01  Inferencing          : 0.41
% 8.49/3.01  Reduction            : 0.99
% 8.49/3.01  Demodulation         : 0.87
% 8.49/3.01  BG Simplification    : 0.06
% 8.49/3.01  Subsumption          : 0.36
% 8.49/3.01  Abstraction          : 0.08
% 8.49/3.01  MUC search           : 0.00
% 8.49/3.01  Cooper               : 0.00
% 8.49/3.01  Total                : 2.27
% 8.49/3.01  Index Insertion      : 0.00
% 8.49/3.01  Index Deletion       : 0.00
% 8.49/3.01  Index Matching       : 0.00
% 8.49/3.01  BG Taut test         : 0.00
%------------------------------------------------------------------------------
