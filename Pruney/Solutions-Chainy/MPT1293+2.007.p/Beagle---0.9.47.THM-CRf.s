%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:22:35 EST 2020

% Result     : Theorem 3.59s
% Output     : CNFRefutation 3.95s
% Verified   : 
% Statistics : Number of formulae       :   61 (  86 expanded)
%              Number of leaves         :   27 (  41 expanded)
%              Depth                    :    9
%              Number of atoms          :   65 ( 119 expanded)
%              Number of equality atoms :   17 (  30 expanded)
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t96_zfmisc_1)).

tff(f_35,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k4_xboole_0(A,B),C)
     => r1_tarski(A,k2_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_xboole_1)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k2_xboole_0(B,C))
     => r1_tarski(k4_xboole_0(A,B),C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_xboole_1)).

tff(f_78,negated_conjecture,(
    ~ ! [A] :
        ( l1_struct_0(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
               => r1_tarski(k7_subset_1(u1_struct_0(A),k5_setfam_1(u1_struct_0(A),B),k5_setfam_1(u1_struct_0(A),C)),k5_setfam_1(u1_struct_0(A),k7_subset_1(k1_zfmisc_1(u1_struct_0(A)),B,C))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_tops_2)).

tff(f_55,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k7_subset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_subset_1)).

tff(f_63,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => k5_setfam_1(A,B) = k3_tarski(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k5_setfam_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => m1_subset_1(k5_setfam_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_setfam_1)).

tff(c_18,plain,(
    ! [A_15,B_16] : k2_xboole_0(k3_tarski(A_15),k3_tarski(B_16)) = k3_tarski(k2_xboole_0(A_15,B_16)) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_10,plain,(
    ! [A_5,B_6] : k2_xboole_0(A_5,k4_xboole_0(B_6,A_5)) = k2_xboole_0(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_8,plain,(
    ! [B_4] : r1_tarski(B_4,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_183,plain,(
    ! [A_50,B_51,C_52] :
      ( r1_tarski(A_50,k2_xboole_0(B_51,C_52))
      | ~ r1_tarski(k4_xboole_0(A_50,B_51),C_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_187,plain,(
    ! [A_50,B_51] : r1_tarski(A_50,k2_xboole_0(B_51,k4_xboole_0(A_50,B_51))) ),
    inference(resolution,[status(thm)],[c_8,c_183])).

tff(c_190,plain,(
    ! [A_53,B_54] : r1_tarski(A_53,k2_xboole_0(B_54,A_53)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_187])).

tff(c_202,plain,(
    ! [B_16,A_15] : r1_tarski(k3_tarski(B_16),k3_tarski(k2_xboole_0(A_15,B_16))) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_190])).

tff(c_12,plain,(
    ! [A_7,B_8,C_9] :
      ( r1_tarski(k4_xboole_0(A_7,B_8),C_9)
      | ~ r1_tarski(A_7,k2_xboole_0(B_8,C_9)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_36,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_593,plain,(
    ! [A_82,B_83,C_84] :
      ( k7_subset_1(A_82,B_83,C_84) = k4_xboole_0(B_83,C_84)
      | ~ m1_subset_1(B_83,k1_zfmisc_1(A_82)) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_719,plain,(
    ! [C_92] : k7_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')),'#skF_2',C_92) = k4_xboole_0('#skF_2',C_92) ),
    inference(resolution,[status(thm)],[c_36,c_593])).

tff(c_20,plain,(
    ! [A_17,B_18,C_19] :
      ( m1_subset_1(k7_subset_1(A_17,B_18,C_19),k1_zfmisc_1(A_17))
      | ~ m1_subset_1(B_18,k1_zfmisc_1(A_17)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_725,plain,(
    ! [C_92] :
      ( m1_subset_1(k4_xboole_0('#skF_2',C_92),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))
      | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_719,c_20])).

tff(c_737,plain,(
    ! [C_93] : m1_subset_1(k4_xboole_0('#skF_2',C_93),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_725])).

tff(c_26,plain,(
    ! [A_25,B_26] :
      ( k5_setfam_1(A_25,B_26) = k3_tarski(B_26)
      | ~ m1_subset_1(B_26,k1_zfmisc_1(k1_zfmisc_1(A_25))) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_747,plain,(
    ! [C_93] : k5_setfam_1(u1_struct_0('#skF_1'),k4_xboole_0('#skF_2',C_93)) = k3_tarski(k4_xboole_0('#skF_2',C_93)) ),
    inference(resolution,[status(thm)],[c_737,c_26])).

tff(c_314,plain,(
    ! [A_63,B_64] :
      ( k5_setfam_1(A_63,B_64) = k3_tarski(B_64)
      | ~ m1_subset_1(B_64,k1_zfmisc_1(k1_zfmisc_1(A_63))) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_327,plain,(
    k5_setfam_1(u1_struct_0('#skF_1'),'#skF_2') = k3_tarski('#skF_2') ),
    inference(resolution,[status(thm)],[c_36,c_314])).

tff(c_675,plain,(
    ! [A_90,B_91] :
      ( m1_subset_1(k5_setfam_1(A_90,B_91),k1_zfmisc_1(A_90))
      | ~ m1_subset_1(B_91,k1_zfmisc_1(k1_zfmisc_1(A_90))) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_690,plain,
    ( m1_subset_1(k3_tarski('#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ),
    inference(superposition,[status(thm),theory(equality)],[c_327,c_675])).

tff(c_698,plain,(
    m1_subset_1(k3_tarski('#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_690])).

tff(c_22,plain,(
    ! [A_20,B_21,C_22] :
      ( k7_subset_1(A_20,B_21,C_22) = k4_xboole_0(B_21,C_22)
      | ~ m1_subset_1(B_21,k1_zfmisc_1(A_20)) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_706,plain,(
    ! [C_22] : k7_subset_1(u1_struct_0('#skF_1'),k3_tarski('#skF_2'),C_22) = k4_xboole_0(k3_tarski('#skF_2'),C_22) ),
    inference(resolution,[status(thm)],[c_698,c_22])).

tff(c_605,plain,(
    ! [C_84] : k7_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')),'#skF_2',C_84) = k4_xboole_0('#skF_2',C_84) ),
    inference(resolution,[status(thm)],[c_36,c_593])).

tff(c_34,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_326,plain,(
    k5_setfam_1(u1_struct_0('#skF_1'),'#skF_3') = k3_tarski('#skF_3') ),
    inference(resolution,[status(thm)],[c_34,c_314])).

tff(c_32,plain,(
    ~ r1_tarski(k7_subset_1(u1_struct_0('#skF_1'),k5_setfam_1(u1_struct_0('#skF_1'),'#skF_2'),k5_setfam_1(u1_struct_0('#skF_1'),'#skF_3')),k5_setfam_1(u1_struct_0('#skF_1'),k7_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')),'#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_328,plain,(
    ~ r1_tarski(k7_subset_1(u1_struct_0('#skF_1'),k5_setfam_1(u1_struct_0('#skF_1'),'#skF_2'),k3_tarski('#skF_3')),k5_setfam_1(u1_struct_0('#skF_1'),k7_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')),'#skF_2','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_326,c_32])).

tff(c_363,plain,(
    ~ r1_tarski(k7_subset_1(u1_struct_0('#skF_1'),k3_tarski('#skF_2'),k3_tarski('#skF_3')),k5_setfam_1(u1_struct_0('#skF_1'),k7_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')),'#skF_2','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_327,c_328])).

tff(c_718,plain,(
    ~ r1_tarski(k7_subset_1(u1_struct_0('#skF_1'),k3_tarski('#skF_2'),k3_tarski('#skF_3')),k5_setfam_1(u1_struct_0('#skF_1'),k4_xboole_0('#skF_2','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_605,c_363])).

tff(c_1477,plain,(
    ~ r1_tarski(k4_xboole_0(k3_tarski('#skF_2'),k3_tarski('#skF_3')),k5_setfam_1(u1_struct_0('#skF_1'),k4_xboole_0('#skF_2','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_706,c_718])).

tff(c_1870,plain,(
    ~ r1_tarski(k4_xboole_0(k3_tarski('#skF_2'),k3_tarski('#skF_3')),k3_tarski(k4_xboole_0('#skF_2','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_747,c_1477])).

tff(c_1873,plain,(
    ~ r1_tarski(k3_tarski('#skF_2'),k2_xboole_0(k3_tarski('#skF_3'),k3_tarski(k4_xboole_0('#skF_2','#skF_3')))) ),
    inference(resolution,[status(thm)],[c_12,c_1870])).

tff(c_1877,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_202,c_10,c_18,c_1873])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n024.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 11:07:06 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.59/1.65  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.59/1.66  
% 3.59/1.66  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.59/1.66  %$ r1_tarski > m1_subset_1 > l1_struct_0 > k7_subset_1 > k5_setfam_1 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > u1_struct_0 > k3_tarski > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1
% 3.59/1.66  
% 3.59/1.66  %Foreground sorts:
% 3.59/1.66  
% 3.59/1.66  
% 3.59/1.66  %Background operators:
% 3.59/1.66  
% 3.59/1.66  
% 3.59/1.66  %Foreground operators:
% 3.59/1.66  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.59/1.66  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.59/1.66  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.59/1.66  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.59/1.66  tff('#skF_2', type, '#skF_2': $i).
% 3.59/1.66  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 3.59/1.66  tff('#skF_3', type, '#skF_3': $i).
% 3.59/1.66  tff('#skF_1', type, '#skF_1': $i).
% 3.59/1.66  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.59/1.66  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 3.59/1.66  tff(k5_setfam_1, type, k5_setfam_1: ($i * $i) > $i).
% 3.59/1.66  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.59/1.66  tff(k3_tarski, type, k3_tarski: $i > $i).
% 3.59/1.66  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.59/1.66  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.59/1.66  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.59/1.66  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.59/1.66  
% 3.95/1.67  tff(f_47, axiom, (![A, B]: (k3_tarski(k2_xboole_0(A, B)) = k2_xboole_0(k3_tarski(A), k3_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t96_zfmisc_1)).
% 3.95/1.67  tff(f_35, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 3.95/1.67  tff(f_33, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.95/1.67  tff(f_43, axiom, (![A, B, C]: (r1_tarski(k4_xboole_0(A, B), C) => r1_tarski(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_xboole_1)).
% 3.95/1.67  tff(f_39, axiom, (![A, B, C]: (r1_tarski(A, k2_xboole_0(B, C)) => r1_tarski(k4_xboole_0(A, B), C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_xboole_1)).
% 3.95/1.67  tff(f_78, negated_conjecture, ~(![A]: (l1_struct_0(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => r1_tarski(k7_subset_1(u1_struct_0(A), k5_setfam_1(u1_struct_0(A), B), k5_setfam_1(u1_struct_0(A), C)), k5_setfam_1(u1_struct_0(A), k7_subset_1(k1_zfmisc_1(u1_struct_0(A)), B, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_tops_2)).
% 3.95/1.67  tff(f_55, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 3.95/1.67  tff(f_51, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k7_subset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_subset_1)).
% 3.95/1.67  tff(f_63, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (k5_setfam_1(A, B) = k3_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k5_setfam_1)).
% 3.95/1.67  tff(f_59, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => m1_subset_1(k5_setfam_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k5_setfam_1)).
% 3.95/1.67  tff(c_18, plain, (![A_15, B_16]: (k2_xboole_0(k3_tarski(A_15), k3_tarski(B_16))=k3_tarski(k2_xboole_0(A_15, B_16)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.95/1.67  tff(c_10, plain, (![A_5, B_6]: (k2_xboole_0(A_5, k4_xboole_0(B_6, A_5))=k2_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.95/1.67  tff(c_8, plain, (![B_4]: (r1_tarski(B_4, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.95/1.67  tff(c_183, plain, (![A_50, B_51, C_52]: (r1_tarski(A_50, k2_xboole_0(B_51, C_52)) | ~r1_tarski(k4_xboole_0(A_50, B_51), C_52))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.95/1.67  tff(c_187, plain, (![A_50, B_51]: (r1_tarski(A_50, k2_xboole_0(B_51, k4_xboole_0(A_50, B_51))))), inference(resolution, [status(thm)], [c_8, c_183])).
% 3.95/1.67  tff(c_190, plain, (![A_53, B_54]: (r1_tarski(A_53, k2_xboole_0(B_54, A_53)))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_187])).
% 3.95/1.67  tff(c_202, plain, (![B_16, A_15]: (r1_tarski(k3_tarski(B_16), k3_tarski(k2_xboole_0(A_15, B_16))))), inference(superposition, [status(thm), theory('equality')], [c_18, c_190])).
% 3.95/1.67  tff(c_12, plain, (![A_7, B_8, C_9]: (r1_tarski(k4_xboole_0(A_7, B_8), C_9) | ~r1_tarski(A_7, k2_xboole_0(B_8, C_9)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.95/1.67  tff(c_36, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.95/1.67  tff(c_593, plain, (![A_82, B_83, C_84]: (k7_subset_1(A_82, B_83, C_84)=k4_xboole_0(B_83, C_84) | ~m1_subset_1(B_83, k1_zfmisc_1(A_82)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.95/1.67  tff(c_719, plain, (![C_92]: (k7_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')), '#skF_2', C_92)=k4_xboole_0('#skF_2', C_92))), inference(resolution, [status(thm)], [c_36, c_593])).
% 3.95/1.67  tff(c_20, plain, (![A_17, B_18, C_19]: (m1_subset_1(k7_subset_1(A_17, B_18, C_19), k1_zfmisc_1(A_17)) | ~m1_subset_1(B_18, k1_zfmisc_1(A_17)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.95/1.67  tff(c_725, plain, (![C_92]: (m1_subset_1(k4_xboole_0('#skF_2', C_92), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) | ~m1_subset_1('#skF_2', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))))), inference(superposition, [status(thm), theory('equality')], [c_719, c_20])).
% 3.95/1.67  tff(c_737, plain, (![C_93]: (m1_subset_1(k4_xboole_0('#skF_2', C_93), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_725])).
% 3.95/1.67  tff(c_26, plain, (![A_25, B_26]: (k5_setfam_1(A_25, B_26)=k3_tarski(B_26) | ~m1_subset_1(B_26, k1_zfmisc_1(k1_zfmisc_1(A_25))))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.95/1.67  tff(c_747, plain, (![C_93]: (k5_setfam_1(u1_struct_0('#skF_1'), k4_xboole_0('#skF_2', C_93))=k3_tarski(k4_xboole_0('#skF_2', C_93)))), inference(resolution, [status(thm)], [c_737, c_26])).
% 3.95/1.67  tff(c_314, plain, (![A_63, B_64]: (k5_setfam_1(A_63, B_64)=k3_tarski(B_64) | ~m1_subset_1(B_64, k1_zfmisc_1(k1_zfmisc_1(A_63))))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.95/1.67  tff(c_327, plain, (k5_setfam_1(u1_struct_0('#skF_1'), '#skF_2')=k3_tarski('#skF_2')), inference(resolution, [status(thm)], [c_36, c_314])).
% 3.95/1.67  tff(c_675, plain, (![A_90, B_91]: (m1_subset_1(k5_setfam_1(A_90, B_91), k1_zfmisc_1(A_90)) | ~m1_subset_1(B_91, k1_zfmisc_1(k1_zfmisc_1(A_90))))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.95/1.67  tff(c_690, plain, (m1_subset_1(k3_tarski('#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1('#skF_2', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(superposition, [status(thm), theory('equality')], [c_327, c_675])).
% 3.95/1.67  tff(c_698, plain, (m1_subset_1(k3_tarski('#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_690])).
% 3.95/1.67  tff(c_22, plain, (![A_20, B_21, C_22]: (k7_subset_1(A_20, B_21, C_22)=k4_xboole_0(B_21, C_22) | ~m1_subset_1(B_21, k1_zfmisc_1(A_20)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.95/1.67  tff(c_706, plain, (![C_22]: (k7_subset_1(u1_struct_0('#skF_1'), k3_tarski('#skF_2'), C_22)=k4_xboole_0(k3_tarski('#skF_2'), C_22))), inference(resolution, [status(thm)], [c_698, c_22])).
% 3.95/1.67  tff(c_605, plain, (![C_84]: (k7_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')), '#skF_2', C_84)=k4_xboole_0('#skF_2', C_84))), inference(resolution, [status(thm)], [c_36, c_593])).
% 3.95/1.67  tff(c_34, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.95/1.67  tff(c_326, plain, (k5_setfam_1(u1_struct_0('#skF_1'), '#skF_3')=k3_tarski('#skF_3')), inference(resolution, [status(thm)], [c_34, c_314])).
% 3.95/1.67  tff(c_32, plain, (~r1_tarski(k7_subset_1(u1_struct_0('#skF_1'), k5_setfam_1(u1_struct_0('#skF_1'), '#skF_2'), k5_setfam_1(u1_struct_0('#skF_1'), '#skF_3')), k5_setfam_1(u1_struct_0('#skF_1'), k7_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')), '#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.95/1.67  tff(c_328, plain, (~r1_tarski(k7_subset_1(u1_struct_0('#skF_1'), k5_setfam_1(u1_struct_0('#skF_1'), '#skF_2'), k3_tarski('#skF_3')), k5_setfam_1(u1_struct_0('#skF_1'), k7_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')), '#skF_2', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_326, c_32])).
% 3.95/1.67  tff(c_363, plain, (~r1_tarski(k7_subset_1(u1_struct_0('#skF_1'), k3_tarski('#skF_2'), k3_tarski('#skF_3')), k5_setfam_1(u1_struct_0('#skF_1'), k7_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')), '#skF_2', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_327, c_328])).
% 3.95/1.67  tff(c_718, plain, (~r1_tarski(k7_subset_1(u1_struct_0('#skF_1'), k3_tarski('#skF_2'), k3_tarski('#skF_3')), k5_setfam_1(u1_struct_0('#skF_1'), k4_xboole_0('#skF_2', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_605, c_363])).
% 3.95/1.67  tff(c_1477, plain, (~r1_tarski(k4_xboole_0(k3_tarski('#skF_2'), k3_tarski('#skF_3')), k5_setfam_1(u1_struct_0('#skF_1'), k4_xboole_0('#skF_2', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_706, c_718])).
% 3.95/1.67  tff(c_1870, plain, (~r1_tarski(k4_xboole_0(k3_tarski('#skF_2'), k3_tarski('#skF_3')), k3_tarski(k4_xboole_0('#skF_2', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_747, c_1477])).
% 3.95/1.67  tff(c_1873, plain, (~r1_tarski(k3_tarski('#skF_2'), k2_xboole_0(k3_tarski('#skF_3'), k3_tarski(k4_xboole_0('#skF_2', '#skF_3'))))), inference(resolution, [status(thm)], [c_12, c_1870])).
% 3.95/1.67  tff(c_1877, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_202, c_10, c_18, c_1873])).
% 3.95/1.67  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.95/1.67  
% 3.95/1.67  Inference rules
% 3.95/1.67  ----------------------
% 3.95/1.67  #Ref     : 0
% 3.95/1.67  #Sup     : 477
% 3.95/1.67  #Fact    : 0
% 3.95/1.67  #Define  : 0
% 3.95/1.67  #Split   : 2
% 3.95/1.67  #Chain   : 0
% 3.95/1.67  #Close   : 0
% 3.95/1.67  
% 3.95/1.67  Ordering : KBO
% 3.95/1.67  
% 3.95/1.67  Simplification rules
% 3.95/1.67  ----------------------
% 3.95/1.67  #Subsume      : 6
% 3.95/1.67  #Demod        : 162
% 3.95/1.67  #Tautology    : 148
% 3.95/1.67  #SimpNegUnit  : 0
% 3.95/1.67  #BackRed      : 5
% 3.95/1.67  
% 3.95/1.67  #Partial instantiations: 0
% 3.95/1.67  #Strategies tried      : 1
% 3.95/1.67  
% 3.95/1.67  Timing (in seconds)
% 3.95/1.67  ----------------------
% 3.95/1.68  Preprocessing        : 0.31
% 3.95/1.68  Parsing              : 0.17
% 3.95/1.68  CNF conversion       : 0.02
% 3.95/1.68  Main loop            : 0.60
% 3.95/1.68  Inferencing          : 0.19
% 3.95/1.68  Reduction            : 0.25
% 3.95/1.68  Demodulation         : 0.20
% 3.95/1.68  BG Simplification    : 0.03
% 3.95/1.68  Subsumption          : 0.10
% 3.95/1.68  Abstraction          : 0.03
% 3.95/1.68  MUC search           : 0.00
% 3.95/1.68  Cooper               : 0.00
% 3.95/1.68  Total                : 0.95
% 3.95/1.68  Index Insertion      : 0.00
% 3.95/1.68  Index Deletion       : 0.00
% 3.95/1.68  Index Matching       : 0.00
% 3.95/1.68  BG Taut test         : 0.00
%------------------------------------------------------------------------------
