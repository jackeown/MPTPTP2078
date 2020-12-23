%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:22:37 EST 2020

% Result     : Theorem 13.24s
% Output     : CNFRefutation 13.34s
% Verified   : 
% Statistics : Number of formulae       :   63 (  92 expanded)
%              Number of leaves         :   28 (  43 expanded)
%              Depth                    :    9
%              Number of atoms          :   74 ( 134 expanded)
%              Number of equality atoms :   18 (  29 expanded)
%              Maximal formula depth    :    8 (   4 average)
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

tff(f_51,axiom,(
    ! [A,B] : k3_tarski(k2_xboole_0(A,B)) = k2_xboole_0(k3_tarski(A),k3_tarski(B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t96_zfmisc_1)).

tff(f_35,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k4_xboole_0(A,B),C)
     => r1_tarski(A,k2_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_41,axiom,(
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

tff(f_65,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_53,axiom,(
    ! [A] : k3_tarski(k1_zfmisc_1(A)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t99_zfmisc_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => r1_tarski(k3_tarski(A),k3_tarski(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_zfmisc_1)).

tff(f_57,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

tff(f_33,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_61,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => k5_setfam_1(A,B) = k3_tarski(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k5_setfam_1)).

tff(c_16,plain,(
    ! [A_18,B_19] : k2_xboole_0(k3_tarski(A_18),k3_tarski(B_19)) = k3_tarski(k2_xboole_0(A_18,B_19)) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_6,plain,(
    ! [A_6,B_7] : r1_tarski(k4_xboole_0(A_6,B_7),A_6) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_830,plain,(
    ! [A_93,B_94,C_95] :
      ( r1_tarski(A_93,k2_xboole_0(B_94,C_95))
      | ~ r1_tarski(k4_xboole_0(A_93,B_94),C_95) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_857,plain,(
    ! [A_96,B_97] : r1_tarski(A_96,k2_xboole_0(B_97,A_96)) ),
    inference(resolution,[status(thm)],[c_6,c_830])).

tff(c_875,plain,(
    ! [B_19,A_18] : r1_tarski(k3_tarski(B_19),k3_tarski(k2_xboole_0(A_18,B_19))) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_857])).

tff(c_8,plain,(
    ! [A_8,B_9] : k2_xboole_0(A_8,k4_xboole_0(B_9,A_8)) = k2_xboole_0(A_8,B_9) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_10,plain,(
    ! [A_10,B_11,C_12] :
      ( r1_tarski(k4_xboole_0(A_10,B_11),C_12)
      | ~ r1_tarski(A_10,k2_xboole_0(B_11,C_12)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_32,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_78,plain,(
    ! [A_37,B_38] :
      ( r1_tarski(A_37,B_38)
      | ~ m1_subset_1(A_37,k1_zfmisc_1(B_38)) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_86,plain,(
    r1_tarski('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_32,c_78])).

tff(c_18,plain,(
    ! [A_20] : k3_tarski(k1_zfmisc_1(A_20)) = A_20 ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_92,plain,(
    ! [A_41,B_42] :
      ( r1_tarski(k3_tarski(A_41),k3_tarski(B_42))
      | ~ r1_tarski(A_41,B_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_98,plain,(
    ! [A_41,A_20] :
      ( r1_tarski(k3_tarski(A_41),A_20)
      | ~ r1_tarski(A_41,k1_zfmisc_1(A_20)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_92])).

tff(c_26,plain,(
    ! [A_26,B_27] :
      ( m1_subset_1(A_26,k1_zfmisc_1(B_27))
      | ~ r1_tarski(A_26,B_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_1140,plain,(
    ! [A_108,B_109,C_110] :
      ( k7_subset_1(A_108,B_109,C_110) = k4_xboole_0(B_109,C_110)
      | ~ m1_subset_1(B_109,k1_zfmisc_1(A_108)) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_1518,plain,(
    ! [B_136,A_137,C_138] :
      ( k7_subset_1(B_136,A_137,C_138) = k4_xboole_0(A_137,C_138)
      | ~ r1_tarski(A_137,B_136) ) ),
    inference(resolution,[status(thm)],[c_26,c_1140])).

tff(c_10096,plain,(
    ! [A_460,A_461,C_462] :
      ( k7_subset_1(A_460,k3_tarski(A_461),C_462) = k4_xboole_0(k3_tarski(A_461),C_462)
      | ~ r1_tarski(A_461,k1_zfmisc_1(A_460)) ) ),
    inference(resolution,[status(thm)],[c_98,c_1518])).

tff(c_10256,plain,(
    ! [C_462] : k7_subset_1(u1_struct_0('#skF_1'),k3_tarski('#skF_2'),C_462) = k4_xboole_0(k3_tarski('#skF_2'),C_462) ),
    inference(resolution,[status(thm)],[c_86,c_10096])).

tff(c_1149,plain,(
    ! [C_110] : k7_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')),'#skF_2',C_110) = k4_xboole_0('#skF_2',C_110) ),
    inference(resolution,[status(thm)],[c_32,c_1140])).

tff(c_113,plain,(
    ! [A_49,C_50,B_51] :
      ( r1_tarski(A_49,C_50)
      | ~ r1_tarski(B_51,C_50)
      | ~ r1_tarski(A_49,B_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_126,plain,(
    ! [A_49] :
      ( r1_tarski(A_49,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ r1_tarski(A_49,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_86,c_113])).

tff(c_502,plain,(
    ! [A_76,B_77] :
      ( k5_setfam_1(A_76,B_77) = k3_tarski(B_77)
      | ~ m1_subset_1(B_77,k1_zfmisc_1(k1_zfmisc_1(A_76))) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_525,plain,(
    ! [A_78,A_79] :
      ( k5_setfam_1(A_78,A_79) = k3_tarski(A_79)
      | ~ r1_tarski(A_79,k1_zfmisc_1(A_78)) ) ),
    inference(resolution,[status(thm)],[c_26,c_502])).

tff(c_762,plain,(
    ! [A_91] :
      ( k5_setfam_1(u1_struct_0('#skF_1'),A_91) = k3_tarski(A_91)
      | ~ r1_tarski(A_91,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_126,c_525])).

tff(c_515,plain,(
    k5_setfam_1(u1_struct_0('#skF_1'),'#skF_2') = k3_tarski('#skF_2') ),
    inference(resolution,[status(thm)],[c_32,c_502])).

tff(c_30,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_514,plain,(
    k5_setfam_1(u1_struct_0('#skF_1'),'#skF_3') = k3_tarski('#skF_3') ),
    inference(resolution,[status(thm)],[c_30,c_502])).

tff(c_28,plain,(
    ~ r1_tarski(k7_subset_1(u1_struct_0('#skF_1'),k5_setfam_1(u1_struct_0('#skF_1'),'#skF_2'),k5_setfam_1(u1_struct_0('#skF_1'),'#skF_3')),k5_setfam_1(u1_struct_0('#skF_1'),k7_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')),'#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_516,plain,(
    ~ r1_tarski(k7_subset_1(u1_struct_0('#skF_1'),k5_setfam_1(u1_struct_0('#skF_1'),'#skF_2'),k3_tarski('#skF_3')),k5_setfam_1(u1_struct_0('#skF_1'),k7_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')),'#skF_2','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_514,c_28])).

tff(c_559,plain,(
    ~ r1_tarski(k7_subset_1(u1_struct_0('#skF_1'),k3_tarski('#skF_2'),k3_tarski('#skF_3')),k5_setfam_1(u1_struct_0('#skF_1'),k7_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')),'#skF_2','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_515,c_516])).

tff(c_768,plain,
    ( ~ r1_tarski(k7_subset_1(u1_struct_0('#skF_1'),k3_tarski('#skF_2'),k3_tarski('#skF_3')),k3_tarski(k7_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')),'#skF_2','#skF_3')))
    | ~ r1_tarski(k7_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')),'#skF_2','#skF_3'),'#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_762,c_559])).

tff(c_2451,plain,(
    ~ r1_tarski(k7_subset_1(u1_struct_0('#skF_1'),k3_tarski('#skF_2'),k3_tarski('#skF_3')),k3_tarski(k4_xboole_0('#skF_2','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_1149,c_1149,c_768])).

tff(c_10518,plain,(
    ~ r1_tarski(k4_xboole_0(k3_tarski('#skF_2'),k3_tarski('#skF_3')),k3_tarski(k4_xboole_0('#skF_2','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10256,c_2451])).

tff(c_26198,plain,(
    ~ r1_tarski(k3_tarski('#skF_2'),k2_xboole_0(k3_tarski('#skF_3'),k3_tarski(k4_xboole_0('#skF_2','#skF_3')))) ),
    inference(resolution,[status(thm)],[c_10,c_10518])).

tff(c_26206,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_875,c_8,c_16,c_26198])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n008.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 13:37:45 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 13.24/6.20  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 13.24/6.20  
% 13.24/6.20  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 13.24/6.20  %$ r1_tarski > m1_subset_1 > l1_struct_0 > k7_subset_1 > k5_setfam_1 > k4_xboole_0 > k2_xboole_0 > #nlpp > u1_struct_0 > k3_tarski > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1
% 13.24/6.20  
% 13.24/6.20  %Foreground sorts:
% 13.24/6.20  
% 13.24/6.20  
% 13.24/6.20  %Background operators:
% 13.24/6.20  
% 13.24/6.20  
% 13.24/6.20  %Foreground operators:
% 13.24/6.20  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 13.24/6.20  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 13.24/6.20  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 13.24/6.20  tff('#skF_2', type, '#skF_2': $i).
% 13.24/6.20  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 13.24/6.20  tff('#skF_3', type, '#skF_3': $i).
% 13.24/6.20  tff('#skF_1', type, '#skF_1': $i).
% 13.24/6.20  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 13.24/6.20  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 13.24/6.20  tff(k5_setfam_1, type, k5_setfam_1: ($i * $i) > $i).
% 13.24/6.20  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 13.24/6.20  tff(k3_tarski, type, k3_tarski: $i > $i).
% 13.24/6.20  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 13.24/6.20  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 13.24/6.20  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 13.24/6.20  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 13.24/6.20  
% 13.34/6.22  tff(f_51, axiom, (![A, B]: (k3_tarski(k2_xboole_0(A, B)) = k2_xboole_0(k3_tarski(A), k3_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t96_zfmisc_1)).
% 13.34/6.22  tff(f_35, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 13.34/6.22  tff(f_45, axiom, (![A, B, C]: (r1_tarski(k4_xboole_0(A, B), C) => r1_tarski(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_xboole_1)).
% 13.34/6.22  tff(f_37, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 13.34/6.22  tff(f_41, axiom, (![A, B, C]: (r1_tarski(A, k2_xboole_0(B, C)) => r1_tarski(k4_xboole_0(A, B), C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_xboole_1)).
% 13.34/6.22  tff(f_76, negated_conjecture, ~(![A]: (l1_struct_0(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => r1_tarski(k7_subset_1(u1_struct_0(A), k5_setfam_1(u1_struct_0(A), B), k5_setfam_1(u1_struct_0(A), C)), k5_setfam_1(u1_struct_0(A), k7_subset_1(k1_zfmisc_1(u1_struct_0(A)), B, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_tops_2)).
% 13.34/6.22  tff(f_65, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 13.34/6.22  tff(f_53, axiom, (![A]: (k3_tarski(k1_zfmisc_1(A)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t99_zfmisc_1)).
% 13.34/6.22  tff(f_49, axiom, (![A, B]: (r1_tarski(A, B) => r1_tarski(k3_tarski(A), k3_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t95_zfmisc_1)).
% 13.34/6.22  tff(f_57, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 13.34/6.22  tff(f_33, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 13.34/6.22  tff(f_61, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (k5_setfam_1(A, B) = k3_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k5_setfam_1)).
% 13.34/6.22  tff(c_16, plain, (![A_18, B_19]: (k2_xboole_0(k3_tarski(A_18), k3_tarski(B_19))=k3_tarski(k2_xboole_0(A_18, B_19)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 13.34/6.22  tff(c_6, plain, (![A_6, B_7]: (r1_tarski(k4_xboole_0(A_6, B_7), A_6))), inference(cnfTransformation, [status(thm)], [f_35])).
% 13.34/6.22  tff(c_830, plain, (![A_93, B_94, C_95]: (r1_tarski(A_93, k2_xboole_0(B_94, C_95)) | ~r1_tarski(k4_xboole_0(A_93, B_94), C_95))), inference(cnfTransformation, [status(thm)], [f_45])).
% 13.34/6.22  tff(c_857, plain, (![A_96, B_97]: (r1_tarski(A_96, k2_xboole_0(B_97, A_96)))), inference(resolution, [status(thm)], [c_6, c_830])).
% 13.34/6.22  tff(c_875, plain, (![B_19, A_18]: (r1_tarski(k3_tarski(B_19), k3_tarski(k2_xboole_0(A_18, B_19))))), inference(superposition, [status(thm), theory('equality')], [c_16, c_857])).
% 13.34/6.22  tff(c_8, plain, (![A_8, B_9]: (k2_xboole_0(A_8, k4_xboole_0(B_9, A_8))=k2_xboole_0(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_37])).
% 13.34/6.22  tff(c_10, plain, (![A_10, B_11, C_12]: (r1_tarski(k4_xboole_0(A_10, B_11), C_12) | ~r1_tarski(A_10, k2_xboole_0(B_11, C_12)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 13.34/6.22  tff(c_32, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(cnfTransformation, [status(thm)], [f_76])).
% 13.34/6.22  tff(c_78, plain, (![A_37, B_38]: (r1_tarski(A_37, B_38) | ~m1_subset_1(A_37, k1_zfmisc_1(B_38)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 13.34/6.22  tff(c_86, plain, (r1_tarski('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_32, c_78])).
% 13.34/6.22  tff(c_18, plain, (![A_20]: (k3_tarski(k1_zfmisc_1(A_20))=A_20)), inference(cnfTransformation, [status(thm)], [f_53])).
% 13.34/6.22  tff(c_92, plain, (![A_41, B_42]: (r1_tarski(k3_tarski(A_41), k3_tarski(B_42)) | ~r1_tarski(A_41, B_42))), inference(cnfTransformation, [status(thm)], [f_49])).
% 13.34/6.22  tff(c_98, plain, (![A_41, A_20]: (r1_tarski(k3_tarski(A_41), A_20) | ~r1_tarski(A_41, k1_zfmisc_1(A_20)))), inference(superposition, [status(thm), theory('equality')], [c_18, c_92])).
% 13.34/6.22  tff(c_26, plain, (![A_26, B_27]: (m1_subset_1(A_26, k1_zfmisc_1(B_27)) | ~r1_tarski(A_26, B_27))), inference(cnfTransformation, [status(thm)], [f_65])).
% 13.34/6.22  tff(c_1140, plain, (![A_108, B_109, C_110]: (k7_subset_1(A_108, B_109, C_110)=k4_xboole_0(B_109, C_110) | ~m1_subset_1(B_109, k1_zfmisc_1(A_108)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 13.34/6.22  tff(c_1518, plain, (![B_136, A_137, C_138]: (k7_subset_1(B_136, A_137, C_138)=k4_xboole_0(A_137, C_138) | ~r1_tarski(A_137, B_136))), inference(resolution, [status(thm)], [c_26, c_1140])).
% 13.34/6.22  tff(c_10096, plain, (![A_460, A_461, C_462]: (k7_subset_1(A_460, k3_tarski(A_461), C_462)=k4_xboole_0(k3_tarski(A_461), C_462) | ~r1_tarski(A_461, k1_zfmisc_1(A_460)))), inference(resolution, [status(thm)], [c_98, c_1518])).
% 13.34/6.22  tff(c_10256, plain, (![C_462]: (k7_subset_1(u1_struct_0('#skF_1'), k3_tarski('#skF_2'), C_462)=k4_xboole_0(k3_tarski('#skF_2'), C_462))), inference(resolution, [status(thm)], [c_86, c_10096])).
% 13.34/6.22  tff(c_1149, plain, (![C_110]: (k7_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')), '#skF_2', C_110)=k4_xboole_0('#skF_2', C_110))), inference(resolution, [status(thm)], [c_32, c_1140])).
% 13.34/6.22  tff(c_113, plain, (![A_49, C_50, B_51]: (r1_tarski(A_49, C_50) | ~r1_tarski(B_51, C_50) | ~r1_tarski(A_49, B_51))), inference(cnfTransformation, [status(thm)], [f_33])).
% 13.34/6.22  tff(c_126, plain, (![A_49]: (r1_tarski(A_49, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~r1_tarski(A_49, '#skF_2'))), inference(resolution, [status(thm)], [c_86, c_113])).
% 13.34/6.22  tff(c_502, plain, (![A_76, B_77]: (k5_setfam_1(A_76, B_77)=k3_tarski(B_77) | ~m1_subset_1(B_77, k1_zfmisc_1(k1_zfmisc_1(A_76))))), inference(cnfTransformation, [status(thm)], [f_61])).
% 13.34/6.22  tff(c_525, plain, (![A_78, A_79]: (k5_setfam_1(A_78, A_79)=k3_tarski(A_79) | ~r1_tarski(A_79, k1_zfmisc_1(A_78)))), inference(resolution, [status(thm)], [c_26, c_502])).
% 13.34/6.22  tff(c_762, plain, (![A_91]: (k5_setfam_1(u1_struct_0('#skF_1'), A_91)=k3_tarski(A_91) | ~r1_tarski(A_91, '#skF_2'))), inference(resolution, [status(thm)], [c_126, c_525])).
% 13.34/6.22  tff(c_515, plain, (k5_setfam_1(u1_struct_0('#skF_1'), '#skF_2')=k3_tarski('#skF_2')), inference(resolution, [status(thm)], [c_32, c_502])).
% 13.34/6.22  tff(c_30, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(cnfTransformation, [status(thm)], [f_76])).
% 13.34/6.22  tff(c_514, plain, (k5_setfam_1(u1_struct_0('#skF_1'), '#skF_3')=k3_tarski('#skF_3')), inference(resolution, [status(thm)], [c_30, c_502])).
% 13.34/6.22  tff(c_28, plain, (~r1_tarski(k7_subset_1(u1_struct_0('#skF_1'), k5_setfam_1(u1_struct_0('#skF_1'), '#skF_2'), k5_setfam_1(u1_struct_0('#skF_1'), '#skF_3')), k5_setfam_1(u1_struct_0('#skF_1'), k7_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')), '#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_76])).
% 13.34/6.22  tff(c_516, plain, (~r1_tarski(k7_subset_1(u1_struct_0('#skF_1'), k5_setfam_1(u1_struct_0('#skF_1'), '#skF_2'), k3_tarski('#skF_3')), k5_setfam_1(u1_struct_0('#skF_1'), k7_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')), '#skF_2', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_514, c_28])).
% 13.34/6.22  tff(c_559, plain, (~r1_tarski(k7_subset_1(u1_struct_0('#skF_1'), k3_tarski('#skF_2'), k3_tarski('#skF_3')), k5_setfam_1(u1_struct_0('#skF_1'), k7_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')), '#skF_2', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_515, c_516])).
% 13.34/6.22  tff(c_768, plain, (~r1_tarski(k7_subset_1(u1_struct_0('#skF_1'), k3_tarski('#skF_2'), k3_tarski('#skF_3')), k3_tarski(k7_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')), '#skF_2', '#skF_3'))) | ~r1_tarski(k7_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')), '#skF_2', '#skF_3'), '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_762, c_559])).
% 13.34/6.22  tff(c_2451, plain, (~r1_tarski(k7_subset_1(u1_struct_0('#skF_1'), k3_tarski('#skF_2'), k3_tarski('#skF_3')), k3_tarski(k4_xboole_0('#skF_2', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_1149, c_1149, c_768])).
% 13.34/6.22  tff(c_10518, plain, (~r1_tarski(k4_xboole_0(k3_tarski('#skF_2'), k3_tarski('#skF_3')), k3_tarski(k4_xboole_0('#skF_2', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_10256, c_2451])).
% 13.34/6.22  tff(c_26198, plain, (~r1_tarski(k3_tarski('#skF_2'), k2_xboole_0(k3_tarski('#skF_3'), k3_tarski(k4_xboole_0('#skF_2', '#skF_3'))))), inference(resolution, [status(thm)], [c_10, c_10518])).
% 13.34/6.22  tff(c_26206, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_875, c_8, c_16, c_26198])).
% 13.34/6.22  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 13.34/6.22  
% 13.34/6.22  Inference rules
% 13.34/6.22  ----------------------
% 13.34/6.22  #Ref     : 0
% 13.34/6.22  #Sup     : 6920
% 13.34/6.22  #Fact    : 0
% 13.34/6.22  #Define  : 0
% 13.34/6.22  #Split   : 2
% 13.34/6.22  #Chain   : 0
% 13.34/6.22  #Close   : 0
% 13.34/6.22  
% 13.34/6.22  Ordering : KBO
% 13.34/6.22  
% 13.34/6.22  Simplification rules
% 13.34/6.22  ----------------------
% 13.34/6.22  #Subsume      : 212
% 13.34/6.22  #Demod        : 1904
% 13.34/6.22  #Tautology    : 1674
% 13.34/6.22  #SimpNegUnit  : 0
% 13.34/6.22  #BackRed      : 4
% 13.34/6.22  
% 13.34/6.22  #Partial instantiations: 0
% 13.34/6.22  #Strategies tried      : 1
% 13.34/6.22  
% 13.34/6.22  Timing (in seconds)
% 13.34/6.22  ----------------------
% 13.34/6.22  Preprocessing        : 0.32
% 13.34/6.22  Parsing              : 0.17
% 13.34/6.22  CNF conversion       : 0.02
% 13.34/6.22  Main loop            : 5.15
% 13.34/6.22  Inferencing          : 0.76
% 13.34/6.22  Reduction            : 2.57
% 13.34/6.22  Demodulation         : 2.29
% 13.34/6.22  BG Simplification    : 0.12
% 13.34/6.22  Subsumption          : 1.40
% 13.34/6.22  Abstraction          : 0.15
% 13.34/6.22  MUC search           : 0.00
% 13.34/6.22  Cooper               : 0.00
% 13.34/6.22  Total                : 5.50
% 13.34/6.22  Index Insertion      : 0.00
% 13.34/6.22  Index Deletion       : 0.00
% 13.34/6.22  Index Matching       : 0.00
% 13.34/6.22  BG Taut test         : 0.00
%------------------------------------------------------------------------------
