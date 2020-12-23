%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:22:37 EST 2020

% Result     : Theorem 6.92s
% Output     : CNFRefutation 7.02s
% Verified   : 
% Statistics : Number of formulae       :   65 (  90 expanded)
%              Number of leaves         :   29 (  43 expanded)
%              Depth                    :    9
%              Number of atoms          :   72 ( 128 expanded)
%              Number of equality atoms :   18 (  30 expanded)
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

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_43,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k2_xboole_0(B,C))
     => r1_tarski(k4_xboole_0(A,B),C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_xboole_1)).

tff(f_74,negated_conjecture,(
    ~ ! [A] :
        ( l1_struct_0(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
               => r1_tarski(k7_subset_1(u1_struct_0(A),k5_setfam_1(u1_struct_0(A),B),k5_setfam_1(u1_struct_0(A),C)),k5_setfam_1(u1_struct_0(A),k7_subset_1(k1_zfmisc_1(u1_struct_0(A)),B,C))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_tops_2)).

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

tff(f_51,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

tff(f_35,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_63,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_33,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

tff(c_219,plain,(
    ! [A_69,B_70] : k2_xboole_0(k3_tarski(A_69),k3_tarski(B_70)) = k3_tarski(k2_xboole_0(A_69,B_70)) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_37,plain,(
    ! [B_36,A_37] : k2_xboole_0(B_36,A_37) = k2_xboole_0(A_37,B_36) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_12,plain,(
    ! [A_13,B_14] : r1_tarski(A_13,k2_xboole_0(A_13,B_14)) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_52,plain,(
    ! [A_37,B_36] : r1_tarski(A_37,k2_xboole_0(B_36,A_37)) ),
    inference(superposition,[status(thm),theory(equality)],[c_37,c_12])).

tff(c_237,plain,(
    ! [B_70,A_69] : r1_tarski(k3_tarski(B_70),k3_tarski(k2_xboole_0(A_69,B_70))) ),
    inference(superposition,[status(thm),theory(equality)],[c_219,c_52])).

tff(c_8,plain,(
    ! [A_8,B_9] : k2_xboole_0(A_8,k4_xboole_0(B_9,A_8)) = k2_xboole_0(A_8,B_9) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_16,plain,(
    ! [A_17,B_18] : k2_xboole_0(k3_tarski(A_17),k3_tarski(B_18)) = k3_tarski(k2_xboole_0(A_17,B_18)) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_10,plain,(
    ! [A_10,B_11,C_12] :
      ( r1_tarski(k4_xboole_0(A_10,B_11),C_12)
      | ~ r1_tarski(A_10,k2_xboole_0(B_11,C_12)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_32,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_532,plain,(
    ! [A_81,B_82] :
      ( k5_setfam_1(A_81,B_82) = k3_tarski(B_82)
      | ~ m1_subset_1(B_82,k1_zfmisc_1(k1_zfmisc_1(A_81))) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_545,plain,(
    k5_setfam_1(u1_struct_0('#skF_1'),'#skF_2') = k3_tarski('#skF_2') ),
    inference(resolution,[status(thm)],[c_32,c_532])).

tff(c_1000,plain,(
    ! [A_115,B_116] :
      ( m1_subset_1(k5_setfam_1(A_115,B_116),k1_zfmisc_1(A_115))
      | ~ m1_subset_1(B_116,k1_zfmisc_1(k1_zfmisc_1(A_115))) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_1018,plain,
    ( m1_subset_1(k3_tarski('#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ),
    inference(superposition,[status(thm),theory(equality)],[c_545,c_1000])).

tff(c_1026,plain,(
    m1_subset_1(k3_tarski('#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_1018])).

tff(c_18,plain,(
    ! [A_19,B_20,C_21] :
      ( k7_subset_1(A_19,B_20,C_21) = k4_xboole_0(B_20,C_21)
      | ~ m1_subset_1(B_20,k1_zfmisc_1(A_19)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_1034,plain,(
    ! [C_21] : k7_subset_1(u1_struct_0('#skF_1'),k3_tarski('#skF_2'),C_21) = k4_xboole_0(k3_tarski('#skF_2'),C_21) ),
    inference(resolution,[status(thm)],[c_1026,c_18])).

tff(c_6,plain,(
    ! [A_6,B_7] : r1_tarski(k4_xboole_0(A_6,B_7),A_6) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_802,plain,(
    ! [A_98,B_99,C_100] :
      ( k7_subset_1(A_98,B_99,C_100) = k4_xboole_0(B_99,C_100)
      | ~ m1_subset_1(B_99,k1_zfmisc_1(A_98)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_811,plain,(
    ! [C_100] : k7_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')),'#skF_2',C_100) = k4_xboole_0('#skF_2',C_100) ),
    inference(resolution,[status(thm)],[c_32,c_802])).

tff(c_96,plain,(
    ! [A_44,B_45] :
      ( r1_tarski(A_44,B_45)
      | ~ m1_subset_1(A_44,k1_zfmisc_1(B_45)) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_108,plain,(
    r1_tarski('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_32,c_96])).

tff(c_125,plain,(
    ! [A_48,C_49,B_50] :
      ( r1_tarski(A_48,C_49)
      | ~ r1_tarski(B_50,C_49)
      | ~ r1_tarski(A_48,B_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_136,plain,(
    ! [A_48] :
      ( r1_tarski(A_48,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ r1_tarski(A_48,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_108,c_125])).

tff(c_26,plain,(
    ! [A_26,B_27] :
      ( m1_subset_1(A_26,k1_zfmisc_1(B_27))
      | ~ r1_tarski(A_26,B_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_557,plain,(
    ! [A_83,A_84] :
      ( k5_setfam_1(A_83,A_84) = k3_tarski(A_84)
      | ~ r1_tarski(A_84,k1_zfmisc_1(A_83)) ) ),
    inference(resolution,[status(thm)],[c_26,c_532])).

tff(c_735,plain,(
    ! [A_95] :
      ( k5_setfam_1(u1_struct_0('#skF_1'),A_95) = k3_tarski(A_95)
      | ~ r1_tarski(A_95,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_136,c_557])).

tff(c_30,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_544,plain,(
    k5_setfam_1(u1_struct_0('#skF_1'),'#skF_3') = k3_tarski('#skF_3') ),
    inference(resolution,[status(thm)],[c_30,c_532])).

tff(c_28,plain,(
    ~ r1_tarski(k7_subset_1(u1_struct_0('#skF_1'),k5_setfam_1(u1_struct_0('#skF_1'),'#skF_2'),k5_setfam_1(u1_struct_0('#skF_1'),'#skF_3')),k5_setfam_1(u1_struct_0('#skF_1'),k7_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')),'#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_546,plain,(
    ~ r1_tarski(k7_subset_1(u1_struct_0('#skF_1'),k5_setfam_1(u1_struct_0('#skF_1'),'#skF_2'),k3_tarski('#skF_3')),k5_setfam_1(u1_struct_0('#skF_1'),k7_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')),'#skF_2','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_544,c_28])).

tff(c_555,plain,(
    ~ r1_tarski(k7_subset_1(u1_struct_0('#skF_1'),k3_tarski('#skF_2'),k3_tarski('#skF_3')),k5_setfam_1(u1_struct_0('#skF_1'),k7_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')),'#skF_2','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_545,c_546])).

tff(c_744,plain,
    ( ~ r1_tarski(k7_subset_1(u1_struct_0('#skF_1'),k3_tarski('#skF_2'),k3_tarski('#skF_3')),k3_tarski(k7_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')),'#skF_2','#skF_3')))
    | ~ r1_tarski(k7_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')),'#skF_2','#skF_3'),'#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_735,c_555])).

tff(c_2057,plain,(
    ~ r1_tarski(k7_subset_1(u1_struct_0('#skF_1'),k3_tarski('#skF_2'),k3_tarski('#skF_3')),k3_tarski(k4_xboole_0('#skF_2','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_811,c_811,c_744])).

tff(c_2058,plain,(
    ~ r1_tarski(k4_xboole_0(k3_tarski('#skF_2'),k3_tarski('#skF_3')),k3_tarski(k4_xboole_0('#skF_2','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1034,c_2057])).

tff(c_5378,plain,(
    ~ r1_tarski(k3_tarski('#skF_2'),k2_xboole_0(k3_tarski('#skF_3'),k3_tarski(k4_xboole_0('#skF_2','#skF_3')))) ),
    inference(resolution,[status(thm)],[c_10,c_2058])).

tff(c_5382,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_237,c_8,c_16,c_5378])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n004.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 12:59:23 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.92/2.81  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.99/2.81  
% 6.99/2.81  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.99/2.81  %$ r1_tarski > m1_subset_1 > l1_struct_0 > k7_subset_1 > k5_setfam_1 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > u1_struct_0 > k3_tarski > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1
% 6.99/2.81  
% 6.99/2.81  %Foreground sorts:
% 6.99/2.81  
% 6.99/2.81  
% 6.99/2.81  %Background operators:
% 6.99/2.81  
% 6.99/2.81  
% 6.99/2.81  %Foreground operators:
% 6.99/2.81  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.99/2.81  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 6.99/2.81  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.99/2.81  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 6.99/2.81  tff('#skF_2', type, '#skF_2': $i).
% 6.99/2.81  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 6.99/2.81  tff('#skF_3', type, '#skF_3': $i).
% 6.99/2.81  tff('#skF_1', type, '#skF_1': $i).
% 6.99/2.81  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 6.99/2.81  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 6.99/2.81  tff(k5_setfam_1, type, k5_setfam_1: ($i * $i) > $i).
% 6.99/2.81  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.99/2.81  tff(k3_tarski, type, k3_tarski: $i > $i).
% 6.99/2.81  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.99/2.81  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 6.99/2.81  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 6.99/2.81  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 6.99/2.81  
% 7.02/2.83  tff(f_47, axiom, (![A, B]: (k3_tarski(k2_xboole_0(A, B)) = k2_xboole_0(k3_tarski(A), k3_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t96_zfmisc_1)).
% 7.02/2.83  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 7.02/2.83  tff(f_43, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 7.02/2.83  tff(f_37, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 7.02/2.83  tff(f_41, axiom, (![A, B, C]: (r1_tarski(A, k2_xboole_0(B, C)) => r1_tarski(k4_xboole_0(A, B), C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_xboole_1)).
% 7.02/2.83  tff(f_74, negated_conjecture, ~(![A]: (l1_struct_0(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => r1_tarski(k7_subset_1(u1_struct_0(A), k5_setfam_1(u1_struct_0(A), B), k5_setfam_1(u1_struct_0(A), C)), k5_setfam_1(u1_struct_0(A), k7_subset_1(k1_zfmisc_1(u1_struct_0(A)), B, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_tops_2)).
% 7.02/2.83  tff(f_59, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (k5_setfam_1(A, B) = k3_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k5_setfam_1)).
% 7.02/2.83  tff(f_55, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => m1_subset_1(k5_setfam_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k5_setfam_1)).
% 7.02/2.83  tff(f_51, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 7.02/2.83  tff(f_35, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 7.02/2.83  tff(f_63, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 7.02/2.83  tff(f_33, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 7.02/2.83  tff(c_219, plain, (![A_69, B_70]: (k2_xboole_0(k3_tarski(A_69), k3_tarski(B_70))=k3_tarski(k2_xboole_0(A_69, B_70)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 7.02/2.83  tff(c_37, plain, (![B_36, A_37]: (k2_xboole_0(B_36, A_37)=k2_xboole_0(A_37, B_36))), inference(cnfTransformation, [status(thm)], [f_27])).
% 7.02/2.83  tff(c_12, plain, (![A_13, B_14]: (r1_tarski(A_13, k2_xboole_0(A_13, B_14)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 7.02/2.83  tff(c_52, plain, (![A_37, B_36]: (r1_tarski(A_37, k2_xboole_0(B_36, A_37)))), inference(superposition, [status(thm), theory('equality')], [c_37, c_12])).
% 7.02/2.83  tff(c_237, plain, (![B_70, A_69]: (r1_tarski(k3_tarski(B_70), k3_tarski(k2_xboole_0(A_69, B_70))))), inference(superposition, [status(thm), theory('equality')], [c_219, c_52])).
% 7.02/2.83  tff(c_8, plain, (![A_8, B_9]: (k2_xboole_0(A_8, k4_xboole_0(B_9, A_8))=k2_xboole_0(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_37])).
% 7.02/2.83  tff(c_16, plain, (![A_17, B_18]: (k2_xboole_0(k3_tarski(A_17), k3_tarski(B_18))=k3_tarski(k2_xboole_0(A_17, B_18)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 7.02/2.83  tff(c_10, plain, (![A_10, B_11, C_12]: (r1_tarski(k4_xboole_0(A_10, B_11), C_12) | ~r1_tarski(A_10, k2_xboole_0(B_11, C_12)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 7.02/2.83  tff(c_32, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 7.02/2.83  tff(c_532, plain, (![A_81, B_82]: (k5_setfam_1(A_81, B_82)=k3_tarski(B_82) | ~m1_subset_1(B_82, k1_zfmisc_1(k1_zfmisc_1(A_81))))), inference(cnfTransformation, [status(thm)], [f_59])).
% 7.02/2.83  tff(c_545, plain, (k5_setfam_1(u1_struct_0('#skF_1'), '#skF_2')=k3_tarski('#skF_2')), inference(resolution, [status(thm)], [c_32, c_532])).
% 7.02/2.83  tff(c_1000, plain, (![A_115, B_116]: (m1_subset_1(k5_setfam_1(A_115, B_116), k1_zfmisc_1(A_115)) | ~m1_subset_1(B_116, k1_zfmisc_1(k1_zfmisc_1(A_115))))), inference(cnfTransformation, [status(thm)], [f_55])).
% 7.02/2.83  tff(c_1018, plain, (m1_subset_1(k3_tarski('#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1('#skF_2', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(superposition, [status(thm), theory('equality')], [c_545, c_1000])).
% 7.02/2.83  tff(c_1026, plain, (m1_subset_1(k3_tarski('#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_1018])).
% 7.02/2.83  tff(c_18, plain, (![A_19, B_20, C_21]: (k7_subset_1(A_19, B_20, C_21)=k4_xboole_0(B_20, C_21) | ~m1_subset_1(B_20, k1_zfmisc_1(A_19)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 7.02/2.83  tff(c_1034, plain, (![C_21]: (k7_subset_1(u1_struct_0('#skF_1'), k3_tarski('#skF_2'), C_21)=k4_xboole_0(k3_tarski('#skF_2'), C_21))), inference(resolution, [status(thm)], [c_1026, c_18])).
% 7.02/2.83  tff(c_6, plain, (![A_6, B_7]: (r1_tarski(k4_xboole_0(A_6, B_7), A_6))), inference(cnfTransformation, [status(thm)], [f_35])).
% 7.02/2.83  tff(c_802, plain, (![A_98, B_99, C_100]: (k7_subset_1(A_98, B_99, C_100)=k4_xboole_0(B_99, C_100) | ~m1_subset_1(B_99, k1_zfmisc_1(A_98)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 7.02/2.83  tff(c_811, plain, (![C_100]: (k7_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')), '#skF_2', C_100)=k4_xboole_0('#skF_2', C_100))), inference(resolution, [status(thm)], [c_32, c_802])).
% 7.02/2.83  tff(c_96, plain, (![A_44, B_45]: (r1_tarski(A_44, B_45) | ~m1_subset_1(A_44, k1_zfmisc_1(B_45)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 7.02/2.83  tff(c_108, plain, (r1_tarski('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_32, c_96])).
% 7.02/2.83  tff(c_125, plain, (![A_48, C_49, B_50]: (r1_tarski(A_48, C_49) | ~r1_tarski(B_50, C_49) | ~r1_tarski(A_48, B_50))), inference(cnfTransformation, [status(thm)], [f_33])).
% 7.02/2.83  tff(c_136, plain, (![A_48]: (r1_tarski(A_48, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~r1_tarski(A_48, '#skF_2'))), inference(resolution, [status(thm)], [c_108, c_125])).
% 7.02/2.83  tff(c_26, plain, (![A_26, B_27]: (m1_subset_1(A_26, k1_zfmisc_1(B_27)) | ~r1_tarski(A_26, B_27))), inference(cnfTransformation, [status(thm)], [f_63])).
% 7.02/2.83  tff(c_557, plain, (![A_83, A_84]: (k5_setfam_1(A_83, A_84)=k3_tarski(A_84) | ~r1_tarski(A_84, k1_zfmisc_1(A_83)))), inference(resolution, [status(thm)], [c_26, c_532])).
% 7.02/2.83  tff(c_735, plain, (![A_95]: (k5_setfam_1(u1_struct_0('#skF_1'), A_95)=k3_tarski(A_95) | ~r1_tarski(A_95, '#skF_2'))), inference(resolution, [status(thm)], [c_136, c_557])).
% 7.02/2.83  tff(c_30, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 7.02/2.83  tff(c_544, plain, (k5_setfam_1(u1_struct_0('#skF_1'), '#skF_3')=k3_tarski('#skF_3')), inference(resolution, [status(thm)], [c_30, c_532])).
% 7.02/2.83  tff(c_28, plain, (~r1_tarski(k7_subset_1(u1_struct_0('#skF_1'), k5_setfam_1(u1_struct_0('#skF_1'), '#skF_2'), k5_setfam_1(u1_struct_0('#skF_1'), '#skF_3')), k5_setfam_1(u1_struct_0('#skF_1'), k7_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')), '#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_74])).
% 7.02/2.83  tff(c_546, plain, (~r1_tarski(k7_subset_1(u1_struct_0('#skF_1'), k5_setfam_1(u1_struct_0('#skF_1'), '#skF_2'), k3_tarski('#skF_3')), k5_setfam_1(u1_struct_0('#skF_1'), k7_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')), '#skF_2', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_544, c_28])).
% 7.02/2.83  tff(c_555, plain, (~r1_tarski(k7_subset_1(u1_struct_0('#skF_1'), k3_tarski('#skF_2'), k3_tarski('#skF_3')), k5_setfam_1(u1_struct_0('#skF_1'), k7_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')), '#skF_2', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_545, c_546])).
% 7.02/2.83  tff(c_744, plain, (~r1_tarski(k7_subset_1(u1_struct_0('#skF_1'), k3_tarski('#skF_2'), k3_tarski('#skF_3')), k3_tarski(k7_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')), '#skF_2', '#skF_3'))) | ~r1_tarski(k7_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')), '#skF_2', '#skF_3'), '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_735, c_555])).
% 7.02/2.83  tff(c_2057, plain, (~r1_tarski(k7_subset_1(u1_struct_0('#skF_1'), k3_tarski('#skF_2'), k3_tarski('#skF_3')), k3_tarski(k4_xboole_0('#skF_2', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_811, c_811, c_744])).
% 7.02/2.83  tff(c_2058, plain, (~r1_tarski(k4_xboole_0(k3_tarski('#skF_2'), k3_tarski('#skF_3')), k3_tarski(k4_xboole_0('#skF_2', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_1034, c_2057])).
% 7.02/2.83  tff(c_5378, plain, (~r1_tarski(k3_tarski('#skF_2'), k2_xboole_0(k3_tarski('#skF_3'), k3_tarski(k4_xboole_0('#skF_2', '#skF_3'))))), inference(resolution, [status(thm)], [c_10, c_2058])).
% 7.02/2.83  tff(c_5382, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_237, c_8, c_16, c_5378])).
% 7.02/2.83  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.02/2.83  
% 7.02/2.83  Inference rules
% 7.02/2.83  ----------------------
% 7.02/2.83  #Ref     : 0
% 7.02/2.83  #Sup     : 1474
% 7.02/2.83  #Fact    : 0
% 7.02/2.83  #Define  : 0
% 7.02/2.83  #Split   : 3
% 7.02/2.83  #Chain   : 0
% 7.02/2.83  #Close   : 0
% 7.02/2.83  
% 7.02/2.83  Ordering : KBO
% 7.02/2.83  
% 7.02/2.83  Simplification rules
% 7.02/2.83  ----------------------
% 7.02/2.83  #Subsume      : 56
% 7.02/2.83  #Demod        : 330
% 7.02/2.83  #Tautology    : 379
% 7.02/2.83  #SimpNegUnit  : 0
% 7.02/2.83  #BackRed      : 4
% 7.02/2.83  
% 7.02/2.83  #Partial instantiations: 0
% 7.02/2.83  #Strategies tried      : 1
% 7.02/2.83  
% 7.02/2.83  Timing (in seconds)
% 7.02/2.83  ----------------------
% 7.02/2.83  Preprocessing        : 0.49
% 7.02/2.83  Parsing              : 0.25
% 7.02/2.83  CNF conversion       : 0.03
% 7.02/2.83  Main loop            : 1.46
% 7.02/2.83  Inferencing          : 0.39
% 7.02/2.83  Reduction            : 0.64
% 7.02/2.83  Demodulation         : 0.53
% 7.02/2.83  BG Simplification    : 0.06
% 7.02/2.83  Subsumption          : 0.27
% 7.02/2.83  Abstraction          : 0.06
% 7.02/2.83  MUC search           : 0.00
% 7.02/2.83  Cooper               : 0.00
% 7.02/2.83  Total                : 1.98
% 7.02/2.83  Index Insertion      : 0.00
% 7.02/2.83  Index Deletion       : 0.00
% 7.02/2.83  Index Matching       : 0.00
% 7.02/2.83  BG Taut test         : 0.00
%------------------------------------------------------------------------------
