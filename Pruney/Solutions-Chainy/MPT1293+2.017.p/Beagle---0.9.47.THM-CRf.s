%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:22:37 EST 2020

% Result     : Theorem 3.32s
% Output     : CNFRefutation 3.70s
% Verified   : 
% Statistics : Number of formulae       :   62 (  82 expanded)
%              Number of leaves         :   27 (  39 expanded)
%              Depth                    :    9
%              Number of atoms          :   66 ( 112 expanded)
%              Number of equality atoms :   19 (  28 expanded)
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

tff(f_39,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

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
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(k4_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t109_xboole_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => k5_setfam_1(A,B) = k3_tarski(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k5_setfam_1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k2_xboole_0(B,C))
     => r1_tarski(k4_xboole_0(A,B),C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_xboole_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => m1_subset_1(k5_setfam_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_setfam_1)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

tff(c_135,plain,(
    ! [A_47,B_48] : k2_xboole_0(k3_tarski(A_47),k3_tarski(B_48)) = k3_tarski(k2_xboole_0(A_47,B_48)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_32,plain,(
    ! [B_30,A_31] : k2_xboole_0(B_30,A_31) = k2_xboole_0(A_31,B_30) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_10,plain,(
    ! [A_11,B_12] : r1_tarski(A_11,k2_xboole_0(A_11,B_12)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_47,plain,(
    ! [A_31,B_30] : r1_tarski(A_31,k2_xboole_0(B_30,A_31)) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_10])).

tff(c_147,plain,(
    ! [B_48,A_47] : r1_tarski(k3_tarski(B_48),k3_tarski(k2_xboole_0(A_47,B_48))) ),
    inference(superposition,[status(thm),theory(equality)],[c_135,c_47])).

tff(c_6,plain,(
    ! [A_6,B_7] : k2_xboole_0(A_6,k4_xboole_0(B_7,A_6)) = k2_xboole_0(A_6,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_12,plain,(
    ! [A_13,B_14] : k2_xboole_0(k3_tarski(A_13),k3_tarski(B_14)) = k3_tarski(k2_xboole_0(A_13,B_14)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_28,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_82,plain,(
    ! [A_36,B_37] :
      ( r1_tarski(A_36,B_37)
      | ~ m1_subset_1(A_36,k1_zfmisc_1(B_37)) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_94,plain,(
    r1_tarski('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_28,c_82])).

tff(c_4,plain,(
    ! [A_3,C_5,B_4] :
      ( r1_tarski(k4_xboole_0(A_3,C_5),B_4)
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_22,plain,(
    ! [A_22,B_23] :
      ( m1_subset_1(A_22,k1_zfmisc_1(B_23))
      | ~ r1_tarski(A_22,B_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_368,plain,(
    ! [A_60,B_61] :
      ( k5_setfam_1(A_60,B_61) = k3_tarski(B_61)
      | ~ m1_subset_1(B_61,k1_zfmisc_1(k1_zfmisc_1(A_60))) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_392,plain,(
    ! [A_62,A_63] :
      ( k5_setfam_1(A_62,A_63) = k3_tarski(A_63)
      | ~ r1_tarski(A_63,k1_zfmisc_1(A_62)) ) ),
    inference(resolution,[status(thm)],[c_22,c_368])).

tff(c_1523,plain,(
    ! [A_130,A_131,C_132] :
      ( k5_setfam_1(A_130,k4_xboole_0(A_131,C_132)) = k3_tarski(k4_xboole_0(A_131,C_132))
      | ~ r1_tarski(A_131,k1_zfmisc_1(A_130)) ) ),
    inference(resolution,[status(thm)],[c_4,c_392])).

tff(c_1540,plain,(
    ! [C_132] : k5_setfam_1(u1_struct_0('#skF_1'),k4_xboole_0('#skF_2',C_132)) = k3_tarski(k4_xboole_0('#skF_2',C_132)) ),
    inference(resolution,[status(thm)],[c_94,c_1523])).

tff(c_8,plain,(
    ! [A_8,B_9,C_10] :
      ( r1_tarski(k4_xboole_0(A_8,B_9),C_10)
      | ~ r1_tarski(A_8,k2_xboole_0(B_9,C_10)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_381,plain,(
    k5_setfam_1(u1_struct_0('#skF_1'),'#skF_2') = k3_tarski('#skF_2') ),
    inference(resolution,[status(thm)],[c_28,c_368])).

tff(c_547,plain,(
    ! [A_77,B_78] :
      ( m1_subset_1(k5_setfam_1(A_77,B_78),k1_zfmisc_1(A_77))
      | ~ m1_subset_1(B_78,k1_zfmisc_1(k1_zfmisc_1(A_77))) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_559,plain,
    ( m1_subset_1(k3_tarski('#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ),
    inference(superposition,[status(thm),theory(equality)],[c_381,c_547])).

tff(c_567,plain,(
    m1_subset_1(k3_tarski('#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_559])).

tff(c_14,plain,(
    ! [A_15,B_16,C_17] :
      ( k7_subset_1(A_15,B_16,C_17) = k4_xboole_0(B_16,C_17)
      | ~ m1_subset_1(B_16,k1_zfmisc_1(A_15)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_575,plain,(
    ! [C_17] : k7_subset_1(u1_struct_0('#skF_1'),k3_tarski('#skF_2'),C_17) = k4_xboole_0(k3_tarski('#skF_2'),C_17) ),
    inference(resolution,[status(thm)],[c_567,c_14])).

tff(c_445,plain,(
    ! [A_66,B_67,C_68] :
      ( k7_subset_1(A_66,B_67,C_68) = k4_xboole_0(B_67,C_68)
      | ~ m1_subset_1(B_67,k1_zfmisc_1(A_66)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_454,plain,(
    ! [C_68] : k7_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')),'#skF_2',C_68) = k4_xboole_0('#skF_2',C_68) ),
    inference(resolution,[status(thm)],[c_28,c_445])).

tff(c_26,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_380,plain,(
    k5_setfam_1(u1_struct_0('#skF_1'),'#skF_3') = k3_tarski('#skF_3') ),
    inference(resolution,[status(thm)],[c_26,c_368])).

tff(c_24,plain,(
    ~ r1_tarski(k7_subset_1(u1_struct_0('#skF_1'),k5_setfam_1(u1_struct_0('#skF_1'),'#skF_2'),k5_setfam_1(u1_struct_0('#skF_1'),'#skF_3')),k5_setfam_1(u1_struct_0('#skF_1'),k7_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')),'#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_382,plain,(
    ~ r1_tarski(k7_subset_1(u1_struct_0('#skF_1'),k5_setfam_1(u1_struct_0('#skF_1'),'#skF_2'),k3_tarski('#skF_3')),k5_setfam_1(u1_struct_0('#skF_1'),k7_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')),'#skF_2','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_380,c_24])).

tff(c_391,plain,(
    ~ r1_tarski(k7_subset_1(u1_struct_0('#skF_1'),k3_tarski('#skF_2'),k3_tarski('#skF_3')),k5_setfam_1(u1_struct_0('#skF_1'),k7_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')),'#skF_2','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_381,c_382])).

tff(c_464,plain,(
    ~ r1_tarski(k7_subset_1(u1_struct_0('#skF_1'),k3_tarski('#skF_2'),k3_tarski('#skF_3')),k5_setfam_1(u1_struct_0('#skF_1'),k4_xboole_0('#skF_2','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_454,c_391])).

tff(c_840,plain,(
    ~ r1_tarski(k4_xboole_0(k3_tarski('#skF_2'),k3_tarski('#skF_3')),k5_setfam_1(u1_struct_0('#skF_1'),k4_xboole_0('#skF_2','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_575,c_464])).

tff(c_1136,plain,(
    ~ r1_tarski(k3_tarski('#skF_2'),k2_xboole_0(k3_tarski('#skF_3'),k5_setfam_1(u1_struct_0('#skF_1'),k4_xboole_0('#skF_2','#skF_3')))) ),
    inference(resolution,[status(thm)],[c_8,c_840])).

tff(c_1542,plain,(
    ~ r1_tarski(k3_tarski('#skF_2'),k2_xboole_0(k3_tarski('#skF_3'),k3_tarski(k4_xboole_0('#skF_2','#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1540,c_1136])).

tff(c_1547,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_147,c_6,c_12,c_1542])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n005.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:19:02 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.32/1.64  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.70/1.65  
% 3.70/1.65  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.70/1.65  %$ r1_tarski > m1_subset_1 > l1_struct_0 > k7_subset_1 > k5_setfam_1 > k4_xboole_0 > k2_xboole_0 > #nlpp > u1_struct_0 > k3_tarski > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1
% 3.70/1.65  
% 3.70/1.65  %Foreground sorts:
% 3.70/1.65  
% 3.70/1.65  
% 3.70/1.65  %Background operators:
% 3.70/1.65  
% 3.70/1.65  
% 3.70/1.65  %Foreground operators:
% 3.70/1.65  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.70/1.65  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.70/1.65  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.70/1.65  tff('#skF_2', type, '#skF_2': $i).
% 3.70/1.65  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 3.70/1.65  tff('#skF_3', type, '#skF_3': $i).
% 3.70/1.65  tff('#skF_1', type, '#skF_1': $i).
% 3.70/1.65  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.70/1.65  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 3.70/1.65  tff(k5_setfam_1, type, k5_setfam_1: ($i * $i) > $i).
% 3.70/1.65  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.70/1.65  tff(k3_tarski, type, k3_tarski: $i > $i).
% 3.70/1.65  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.70/1.65  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.70/1.65  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.70/1.65  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.70/1.65  
% 3.70/1.66  tff(f_41, axiom, (![A, B]: (k3_tarski(k2_xboole_0(A, B)) = k2_xboole_0(k3_tarski(A), k3_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t96_zfmisc_1)).
% 3.70/1.66  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 3.70/1.66  tff(f_39, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 3.70/1.66  tff(f_33, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 3.70/1.66  tff(f_68, negated_conjecture, ~(![A]: (l1_struct_0(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => r1_tarski(k7_subset_1(u1_struct_0(A), k5_setfam_1(u1_struct_0(A), B), k5_setfam_1(u1_struct_0(A), C)), k5_setfam_1(u1_struct_0(A), k7_subset_1(k1_zfmisc_1(u1_struct_0(A)), B, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_tops_2)).
% 3.70/1.66  tff(f_57, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 3.70/1.66  tff(f_31, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(k4_xboole_0(A, C), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t109_xboole_1)).
% 3.70/1.66  tff(f_53, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (k5_setfam_1(A, B) = k3_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k5_setfam_1)).
% 3.70/1.66  tff(f_37, axiom, (![A, B, C]: (r1_tarski(A, k2_xboole_0(B, C)) => r1_tarski(k4_xboole_0(A, B), C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_xboole_1)).
% 3.70/1.66  tff(f_49, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => m1_subset_1(k5_setfam_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k5_setfam_1)).
% 3.70/1.66  tff(f_45, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 3.70/1.66  tff(c_135, plain, (![A_47, B_48]: (k2_xboole_0(k3_tarski(A_47), k3_tarski(B_48))=k3_tarski(k2_xboole_0(A_47, B_48)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.70/1.66  tff(c_32, plain, (![B_30, A_31]: (k2_xboole_0(B_30, A_31)=k2_xboole_0(A_31, B_30))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.70/1.66  tff(c_10, plain, (![A_11, B_12]: (r1_tarski(A_11, k2_xboole_0(A_11, B_12)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.70/1.66  tff(c_47, plain, (![A_31, B_30]: (r1_tarski(A_31, k2_xboole_0(B_30, A_31)))), inference(superposition, [status(thm), theory('equality')], [c_32, c_10])).
% 3.70/1.66  tff(c_147, plain, (![B_48, A_47]: (r1_tarski(k3_tarski(B_48), k3_tarski(k2_xboole_0(A_47, B_48))))), inference(superposition, [status(thm), theory('equality')], [c_135, c_47])).
% 3.70/1.66  tff(c_6, plain, (![A_6, B_7]: (k2_xboole_0(A_6, k4_xboole_0(B_7, A_6))=k2_xboole_0(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.70/1.66  tff(c_12, plain, (![A_13, B_14]: (k2_xboole_0(k3_tarski(A_13), k3_tarski(B_14))=k3_tarski(k2_xboole_0(A_13, B_14)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.70/1.66  tff(c_28, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.70/1.66  tff(c_82, plain, (![A_36, B_37]: (r1_tarski(A_36, B_37) | ~m1_subset_1(A_36, k1_zfmisc_1(B_37)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.70/1.66  tff(c_94, plain, (r1_tarski('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_28, c_82])).
% 3.70/1.66  tff(c_4, plain, (![A_3, C_5, B_4]: (r1_tarski(k4_xboole_0(A_3, C_5), B_4) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.70/1.66  tff(c_22, plain, (![A_22, B_23]: (m1_subset_1(A_22, k1_zfmisc_1(B_23)) | ~r1_tarski(A_22, B_23))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.70/1.66  tff(c_368, plain, (![A_60, B_61]: (k5_setfam_1(A_60, B_61)=k3_tarski(B_61) | ~m1_subset_1(B_61, k1_zfmisc_1(k1_zfmisc_1(A_60))))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.70/1.66  tff(c_392, plain, (![A_62, A_63]: (k5_setfam_1(A_62, A_63)=k3_tarski(A_63) | ~r1_tarski(A_63, k1_zfmisc_1(A_62)))), inference(resolution, [status(thm)], [c_22, c_368])).
% 3.70/1.66  tff(c_1523, plain, (![A_130, A_131, C_132]: (k5_setfam_1(A_130, k4_xboole_0(A_131, C_132))=k3_tarski(k4_xboole_0(A_131, C_132)) | ~r1_tarski(A_131, k1_zfmisc_1(A_130)))), inference(resolution, [status(thm)], [c_4, c_392])).
% 3.70/1.66  tff(c_1540, plain, (![C_132]: (k5_setfam_1(u1_struct_0('#skF_1'), k4_xboole_0('#skF_2', C_132))=k3_tarski(k4_xboole_0('#skF_2', C_132)))), inference(resolution, [status(thm)], [c_94, c_1523])).
% 3.70/1.66  tff(c_8, plain, (![A_8, B_9, C_10]: (r1_tarski(k4_xboole_0(A_8, B_9), C_10) | ~r1_tarski(A_8, k2_xboole_0(B_9, C_10)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.70/1.66  tff(c_381, plain, (k5_setfam_1(u1_struct_0('#skF_1'), '#skF_2')=k3_tarski('#skF_2')), inference(resolution, [status(thm)], [c_28, c_368])).
% 3.70/1.66  tff(c_547, plain, (![A_77, B_78]: (m1_subset_1(k5_setfam_1(A_77, B_78), k1_zfmisc_1(A_77)) | ~m1_subset_1(B_78, k1_zfmisc_1(k1_zfmisc_1(A_77))))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.70/1.66  tff(c_559, plain, (m1_subset_1(k3_tarski('#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1('#skF_2', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(superposition, [status(thm), theory('equality')], [c_381, c_547])).
% 3.70/1.66  tff(c_567, plain, (m1_subset_1(k3_tarski('#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_559])).
% 3.70/1.66  tff(c_14, plain, (![A_15, B_16, C_17]: (k7_subset_1(A_15, B_16, C_17)=k4_xboole_0(B_16, C_17) | ~m1_subset_1(B_16, k1_zfmisc_1(A_15)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.70/1.66  tff(c_575, plain, (![C_17]: (k7_subset_1(u1_struct_0('#skF_1'), k3_tarski('#skF_2'), C_17)=k4_xboole_0(k3_tarski('#skF_2'), C_17))), inference(resolution, [status(thm)], [c_567, c_14])).
% 3.70/1.66  tff(c_445, plain, (![A_66, B_67, C_68]: (k7_subset_1(A_66, B_67, C_68)=k4_xboole_0(B_67, C_68) | ~m1_subset_1(B_67, k1_zfmisc_1(A_66)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.70/1.66  tff(c_454, plain, (![C_68]: (k7_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')), '#skF_2', C_68)=k4_xboole_0('#skF_2', C_68))), inference(resolution, [status(thm)], [c_28, c_445])).
% 3.70/1.66  tff(c_26, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.70/1.66  tff(c_380, plain, (k5_setfam_1(u1_struct_0('#skF_1'), '#skF_3')=k3_tarski('#skF_3')), inference(resolution, [status(thm)], [c_26, c_368])).
% 3.70/1.66  tff(c_24, plain, (~r1_tarski(k7_subset_1(u1_struct_0('#skF_1'), k5_setfam_1(u1_struct_0('#skF_1'), '#skF_2'), k5_setfam_1(u1_struct_0('#skF_1'), '#skF_3')), k5_setfam_1(u1_struct_0('#skF_1'), k7_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')), '#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.70/1.66  tff(c_382, plain, (~r1_tarski(k7_subset_1(u1_struct_0('#skF_1'), k5_setfam_1(u1_struct_0('#skF_1'), '#skF_2'), k3_tarski('#skF_3')), k5_setfam_1(u1_struct_0('#skF_1'), k7_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')), '#skF_2', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_380, c_24])).
% 3.70/1.66  tff(c_391, plain, (~r1_tarski(k7_subset_1(u1_struct_0('#skF_1'), k3_tarski('#skF_2'), k3_tarski('#skF_3')), k5_setfam_1(u1_struct_0('#skF_1'), k7_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')), '#skF_2', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_381, c_382])).
% 3.70/1.66  tff(c_464, plain, (~r1_tarski(k7_subset_1(u1_struct_0('#skF_1'), k3_tarski('#skF_2'), k3_tarski('#skF_3')), k5_setfam_1(u1_struct_0('#skF_1'), k4_xboole_0('#skF_2', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_454, c_391])).
% 3.70/1.66  tff(c_840, plain, (~r1_tarski(k4_xboole_0(k3_tarski('#skF_2'), k3_tarski('#skF_3')), k5_setfam_1(u1_struct_0('#skF_1'), k4_xboole_0('#skF_2', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_575, c_464])).
% 3.70/1.66  tff(c_1136, plain, (~r1_tarski(k3_tarski('#skF_2'), k2_xboole_0(k3_tarski('#skF_3'), k5_setfam_1(u1_struct_0('#skF_1'), k4_xboole_0('#skF_2', '#skF_3'))))), inference(resolution, [status(thm)], [c_8, c_840])).
% 3.70/1.66  tff(c_1542, plain, (~r1_tarski(k3_tarski('#skF_2'), k2_xboole_0(k3_tarski('#skF_3'), k3_tarski(k4_xboole_0('#skF_2', '#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_1540, c_1136])).
% 3.70/1.66  tff(c_1547, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_147, c_6, c_12, c_1542])).
% 3.70/1.66  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.70/1.66  
% 3.70/1.66  Inference rules
% 3.70/1.66  ----------------------
% 3.70/1.66  #Ref     : 0
% 3.70/1.66  #Sup     : 405
% 3.70/1.66  #Fact    : 0
% 3.70/1.66  #Define  : 0
% 3.70/1.66  #Split   : 0
% 3.70/1.66  #Chain   : 0
% 3.70/1.66  #Close   : 0
% 3.70/1.66  
% 3.70/1.66  Ordering : KBO
% 3.70/1.66  
% 3.70/1.66  Simplification rules
% 3.70/1.66  ----------------------
% 3.70/1.66  #Subsume      : 2
% 3.70/1.66  #Demod        : 173
% 3.70/1.66  #Tautology    : 196
% 3.70/1.66  #SimpNegUnit  : 0
% 3.70/1.66  #BackRed      : 6
% 3.70/1.66  
% 3.70/1.66  #Partial instantiations: 0
% 3.70/1.66  #Strategies tried      : 1
% 3.70/1.66  
% 3.70/1.66  Timing (in seconds)
% 3.70/1.66  ----------------------
% 3.70/1.67  Preprocessing        : 0.32
% 3.70/1.67  Parsing              : 0.18
% 3.70/1.67  CNF conversion       : 0.02
% 3.70/1.67  Main loop            : 0.53
% 3.70/1.67  Inferencing          : 0.16
% 3.70/1.67  Reduction            : 0.23
% 3.70/1.67  Demodulation         : 0.19
% 3.70/1.67  BG Simplification    : 0.02
% 3.70/1.67  Subsumption          : 0.08
% 3.70/1.67  Abstraction          : 0.03
% 3.70/1.67  MUC search           : 0.00
% 3.70/1.67  Cooper               : 0.00
% 3.70/1.67  Total                : 0.89
% 3.70/1.67  Index Insertion      : 0.00
% 3.70/1.67  Index Deletion       : 0.00
% 3.70/1.67  Index Matching       : 0.00
% 3.70/1.67  BG Taut test         : 0.00
%------------------------------------------------------------------------------
