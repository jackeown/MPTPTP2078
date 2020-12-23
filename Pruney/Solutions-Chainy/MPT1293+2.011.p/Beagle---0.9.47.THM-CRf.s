%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:22:36 EST 2020

% Result     : Theorem 7.99s
% Output     : CNFRefutation 7.99s
% Verified   : 
% Statistics : Number of formulae       :   64 (  88 expanded)
%              Number of leaves         :   28 (  41 expanded)
%              Depth                    :    9
%              Number of atoms          :   73 ( 123 expanded)
%              Number of equality atoms :   20 (  30 expanded)
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

tff(f_53,axiom,(
    ! [A,B] : k3_tarski(k2_xboole_0(A,B)) = k2_xboole_0(k3_tarski(A),k3_tarski(B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t96_zfmisc_1)).

tff(f_39,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_47,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k4_xboole_0(A,B),C)
     => r1_tarski(A,k2_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_xboole_1)).

tff(f_78,negated_conjecture,(
    ~ ! [A] :
        ( l1_struct_0(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
               => r1_tarski(k7_subset_1(u1_struct_0(A),k5_setfam_1(u1_struct_0(A),B),k5_setfam_1(u1_struct_0(A),C)),k5_setfam_1(u1_struct_0(A),k7_subset_1(k1_zfmisc_1(u1_struct_0(A)),B,C))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_tops_2)).

tff(f_67,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(k4_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t109_xboole_1)).

tff(f_63,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => k5_setfam_1(A,B) = k3_tarski(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k5_setfam_1)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k2_xboole_0(B,C))
     => r1_tarski(k4_xboole_0(A,B),C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_xboole_1)).

tff(f_55,axiom,(
    ! [A] : k3_tarski(k1_zfmisc_1(A)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t99_zfmisc_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => r1_tarski(k3_tarski(A),k3_tarski(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_zfmisc_1)).

tff(f_59,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

tff(c_20,plain,(
    ! [A_18,B_19] : k2_xboole_0(k3_tarski(A_18),k3_tarski(B_19)) = k3_tarski(k2_xboole_0(A_18,B_19)) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_12,plain,(
    ! [A_8,B_9] : k2_xboole_0(A_8,k4_xboole_0(B_9,A_8)) = k2_xboole_0(A_8,B_9) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_8,plain,(
    ! [B_4] : r1_tarski(B_4,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_686,plain,(
    ! [A_77,B_78,C_79] :
      ( r1_tarski(A_77,k2_xboole_0(B_78,C_79))
      | ~ r1_tarski(k4_xboole_0(A_77,B_78),C_79) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_696,plain,(
    ! [A_77,B_78] : r1_tarski(A_77,k2_xboole_0(B_78,k4_xboole_0(A_77,B_78))) ),
    inference(resolution,[status(thm)],[c_8,c_686])).

tff(c_701,plain,(
    ! [A_80,B_81] : r1_tarski(A_80,k2_xboole_0(B_81,A_80)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_696])).

tff(c_717,plain,(
    ! [B_19,A_18] : r1_tarski(k3_tarski(B_19),k3_tarski(k2_xboole_0(A_18,B_19))) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_701])).

tff(c_36,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_83,plain,(
    ! [A_36,B_37] :
      ( r1_tarski(A_36,B_37)
      | ~ m1_subset_1(A_36,k1_zfmisc_1(B_37)) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_91,plain,(
    r1_tarski('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_36,c_83])).

tff(c_10,plain,(
    ! [A_5,C_7,B_6] :
      ( r1_tarski(k4_xboole_0(A_5,C_7),B_6)
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_30,plain,(
    ! [A_26,B_27] :
      ( m1_subset_1(A_26,k1_zfmisc_1(B_27))
      | ~ r1_tarski(A_26,B_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_378,plain,(
    ! [A_63,B_64] :
      ( k5_setfam_1(A_63,B_64) = k3_tarski(B_64)
      | ~ m1_subset_1(B_64,k1_zfmisc_1(k1_zfmisc_1(A_63))) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_472,plain,(
    ! [A_67,A_68] :
      ( k5_setfam_1(A_67,A_68) = k3_tarski(A_68)
      | ~ r1_tarski(A_68,k1_zfmisc_1(A_67)) ) ),
    inference(resolution,[status(thm)],[c_30,c_378])).

tff(c_8167,plain,(
    ! [A_350,A_351,C_352] :
      ( k5_setfam_1(A_350,k4_xboole_0(A_351,C_352)) = k3_tarski(k4_xboole_0(A_351,C_352))
      | ~ r1_tarski(A_351,k1_zfmisc_1(A_350)) ) ),
    inference(resolution,[status(thm)],[c_10,c_472])).

tff(c_8187,plain,(
    ! [C_352] : k5_setfam_1(u1_struct_0('#skF_1'),k4_xboole_0('#skF_2',C_352)) = k3_tarski(k4_xboole_0('#skF_2',C_352)) ),
    inference(resolution,[status(thm)],[c_91,c_8167])).

tff(c_14,plain,(
    ! [A_10,B_11,C_12] :
      ( r1_tarski(k4_xboole_0(A_10,B_11),C_12)
      | ~ r1_tarski(A_10,k2_xboole_0(B_11,C_12)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_22,plain,(
    ! [A_20] : k3_tarski(k1_zfmisc_1(A_20)) = A_20 ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_119,plain,(
    ! [A_44,B_45] :
      ( r1_tarski(k3_tarski(A_44),k3_tarski(B_45))
      | ~ r1_tarski(A_44,B_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_127,plain,(
    ! [A_44,A_20] :
      ( r1_tarski(k3_tarski(A_44),A_20)
      | ~ r1_tarski(A_44,k1_zfmisc_1(A_20)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_119])).

tff(c_765,plain,(
    ! [A_84,B_85,C_86] :
      ( k7_subset_1(A_84,B_85,C_86) = k4_xboole_0(B_85,C_86)
      | ~ m1_subset_1(B_85,k1_zfmisc_1(A_84)) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_1190,plain,(
    ! [B_115,A_116,C_117] :
      ( k7_subset_1(B_115,A_116,C_117) = k4_xboole_0(A_116,C_117)
      | ~ r1_tarski(A_116,B_115) ) ),
    inference(resolution,[status(thm)],[c_30,c_765])).

tff(c_7598,plain,(
    ! [A_331,A_332,C_333] :
      ( k7_subset_1(A_331,k3_tarski(A_332),C_333) = k4_xboole_0(k3_tarski(A_332),C_333)
      | ~ r1_tarski(A_332,k1_zfmisc_1(A_331)) ) ),
    inference(resolution,[status(thm)],[c_127,c_1190])).

tff(c_7618,plain,(
    ! [C_333] : k7_subset_1(u1_struct_0('#skF_1'),k3_tarski('#skF_2'),C_333) = k4_xboole_0(k3_tarski('#skF_2'),C_333) ),
    inference(resolution,[status(thm)],[c_91,c_7598])).

tff(c_774,plain,(
    ! [C_86] : k7_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')),'#skF_2',C_86) = k4_xboole_0('#skF_2',C_86) ),
    inference(resolution,[status(thm)],[c_36,c_765])).

tff(c_391,plain,(
    k5_setfam_1(u1_struct_0('#skF_1'),'#skF_2') = k3_tarski('#skF_2') ),
    inference(resolution,[status(thm)],[c_36,c_378])).

tff(c_34,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_390,plain,(
    k5_setfam_1(u1_struct_0('#skF_1'),'#skF_3') = k3_tarski('#skF_3') ),
    inference(resolution,[status(thm)],[c_34,c_378])).

tff(c_32,plain,(
    ~ r1_tarski(k7_subset_1(u1_struct_0('#skF_1'),k5_setfam_1(u1_struct_0('#skF_1'),'#skF_2'),k5_setfam_1(u1_struct_0('#skF_1'),'#skF_3')),k5_setfam_1(u1_struct_0('#skF_1'),k7_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')),'#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_392,plain,(
    ~ r1_tarski(k7_subset_1(u1_struct_0('#skF_1'),k5_setfam_1(u1_struct_0('#skF_1'),'#skF_2'),k3_tarski('#skF_3')),k5_setfam_1(u1_struct_0('#skF_1'),k7_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')),'#skF_2','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_390,c_32])).

tff(c_402,plain,(
    ~ r1_tarski(k7_subset_1(u1_struct_0('#skF_1'),k3_tarski('#skF_2'),k3_tarski('#skF_3')),k5_setfam_1(u1_struct_0('#skF_1'),k7_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')),'#skF_2','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_391,c_392])).

tff(c_1064,plain,(
    ~ r1_tarski(k7_subset_1(u1_struct_0('#skF_1'),k3_tarski('#skF_2'),k3_tarski('#skF_3')),k5_setfam_1(u1_struct_0('#skF_1'),k4_xboole_0('#skF_2','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_774,c_402])).

tff(c_7622,plain,(
    ~ r1_tarski(k4_xboole_0(k3_tarski('#skF_2'),k3_tarski('#skF_3')),k5_setfam_1(u1_struct_0('#skF_1'),k4_xboole_0('#skF_2','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7618,c_1064])).

tff(c_7648,plain,(
    ~ r1_tarski(k3_tarski('#skF_2'),k2_xboole_0(k3_tarski('#skF_3'),k5_setfam_1(u1_struct_0('#skF_1'),k4_xboole_0('#skF_2','#skF_3')))) ),
    inference(resolution,[status(thm)],[c_14,c_7622])).

tff(c_8191,plain,(
    ~ r1_tarski(k3_tarski('#skF_2'),k2_xboole_0(k3_tarski('#skF_3'),k3_tarski(k4_xboole_0('#skF_2','#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8187,c_7648])).

tff(c_8198,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_717,c_12,c_20,c_8191])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:15:46 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.99/2.93  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.99/2.93  
% 7.99/2.93  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.99/2.94  %$ r1_tarski > m1_subset_1 > l1_struct_0 > k7_subset_1 > k5_setfam_1 > k4_xboole_0 > k2_xboole_0 > #nlpp > u1_struct_0 > k3_tarski > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1
% 7.99/2.94  
% 7.99/2.94  %Foreground sorts:
% 7.99/2.94  
% 7.99/2.94  
% 7.99/2.94  %Background operators:
% 7.99/2.94  
% 7.99/2.94  
% 7.99/2.94  %Foreground operators:
% 7.99/2.94  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.99/2.94  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 7.99/2.94  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.99/2.94  tff('#skF_2', type, '#skF_2': $i).
% 7.99/2.94  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 7.99/2.94  tff('#skF_3', type, '#skF_3': $i).
% 7.99/2.94  tff('#skF_1', type, '#skF_1': $i).
% 7.99/2.94  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 7.99/2.94  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 7.99/2.94  tff(k5_setfam_1, type, k5_setfam_1: ($i * $i) > $i).
% 7.99/2.94  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.99/2.94  tff(k3_tarski, type, k3_tarski: $i > $i).
% 7.99/2.94  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.99/2.94  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 7.99/2.94  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 7.99/2.94  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 7.99/2.94  
% 7.99/2.95  tff(f_53, axiom, (![A, B]: (k3_tarski(k2_xboole_0(A, B)) = k2_xboole_0(k3_tarski(A), k3_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t96_zfmisc_1)).
% 7.99/2.95  tff(f_39, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 7.99/2.95  tff(f_33, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 7.99/2.95  tff(f_47, axiom, (![A, B, C]: (r1_tarski(k4_xboole_0(A, B), C) => r1_tarski(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_xboole_1)).
% 7.99/2.95  tff(f_78, negated_conjecture, ~(![A]: (l1_struct_0(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => r1_tarski(k7_subset_1(u1_struct_0(A), k5_setfam_1(u1_struct_0(A), B), k5_setfam_1(u1_struct_0(A), C)), k5_setfam_1(u1_struct_0(A), k7_subset_1(k1_zfmisc_1(u1_struct_0(A)), B, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_tops_2)).
% 7.99/2.95  tff(f_67, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 7.99/2.95  tff(f_37, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(k4_xboole_0(A, C), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t109_xboole_1)).
% 7.99/2.95  tff(f_63, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (k5_setfam_1(A, B) = k3_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k5_setfam_1)).
% 7.99/2.95  tff(f_43, axiom, (![A, B, C]: (r1_tarski(A, k2_xboole_0(B, C)) => r1_tarski(k4_xboole_0(A, B), C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_xboole_1)).
% 7.99/2.95  tff(f_55, axiom, (![A]: (k3_tarski(k1_zfmisc_1(A)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t99_zfmisc_1)).
% 7.99/2.95  tff(f_51, axiom, (![A, B]: (r1_tarski(A, B) => r1_tarski(k3_tarski(A), k3_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t95_zfmisc_1)).
% 7.99/2.95  tff(f_59, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 7.99/2.95  tff(c_20, plain, (![A_18, B_19]: (k2_xboole_0(k3_tarski(A_18), k3_tarski(B_19))=k3_tarski(k2_xboole_0(A_18, B_19)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 7.99/2.95  tff(c_12, plain, (![A_8, B_9]: (k2_xboole_0(A_8, k4_xboole_0(B_9, A_8))=k2_xboole_0(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_39])).
% 7.99/2.95  tff(c_8, plain, (![B_4]: (r1_tarski(B_4, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 7.99/2.95  tff(c_686, plain, (![A_77, B_78, C_79]: (r1_tarski(A_77, k2_xboole_0(B_78, C_79)) | ~r1_tarski(k4_xboole_0(A_77, B_78), C_79))), inference(cnfTransformation, [status(thm)], [f_47])).
% 7.99/2.95  tff(c_696, plain, (![A_77, B_78]: (r1_tarski(A_77, k2_xboole_0(B_78, k4_xboole_0(A_77, B_78))))), inference(resolution, [status(thm)], [c_8, c_686])).
% 7.99/2.95  tff(c_701, plain, (![A_80, B_81]: (r1_tarski(A_80, k2_xboole_0(B_81, A_80)))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_696])).
% 7.99/2.95  tff(c_717, plain, (![B_19, A_18]: (r1_tarski(k3_tarski(B_19), k3_tarski(k2_xboole_0(A_18, B_19))))), inference(superposition, [status(thm), theory('equality')], [c_20, c_701])).
% 7.99/2.95  tff(c_36, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(cnfTransformation, [status(thm)], [f_78])).
% 7.99/2.95  tff(c_83, plain, (![A_36, B_37]: (r1_tarski(A_36, B_37) | ~m1_subset_1(A_36, k1_zfmisc_1(B_37)))), inference(cnfTransformation, [status(thm)], [f_67])).
% 7.99/2.95  tff(c_91, plain, (r1_tarski('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_36, c_83])).
% 7.99/2.95  tff(c_10, plain, (![A_5, C_7, B_6]: (r1_tarski(k4_xboole_0(A_5, C_7), B_6) | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_37])).
% 7.99/2.95  tff(c_30, plain, (![A_26, B_27]: (m1_subset_1(A_26, k1_zfmisc_1(B_27)) | ~r1_tarski(A_26, B_27))), inference(cnfTransformation, [status(thm)], [f_67])).
% 7.99/2.95  tff(c_378, plain, (![A_63, B_64]: (k5_setfam_1(A_63, B_64)=k3_tarski(B_64) | ~m1_subset_1(B_64, k1_zfmisc_1(k1_zfmisc_1(A_63))))), inference(cnfTransformation, [status(thm)], [f_63])).
% 7.99/2.95  tff(c_472, plain, (![A_67, A_68]: (k5_setfam_1(A_67, A_68)=k3_tarski(A_68) | ~r1_tarski(A_68, k1_zfmisc_1(A_67)))), inference(resolution, [status(thm)], [c_30, c_378])).
% 7.99/2.95  tff(c_8167, plain, (![A_350, A_351, C_352]: (k5_setfam_1(A_350, k4_xboole_0(A_351, C_352))=k3_tarski(k4_xboole_0(A_351, C_352)) | ~r1_tarski(A_351, k1_zfmisc_1(A_350)))), inference(resolution, [status(thm)], [c_10, c_472])).
% 7.99/2.95  tff(c_8187, plain, (![C_352]: (k5_setfam_1(u1_struct_0('#skF_1'), k4_xboole_0('#skF_2', C_352))=k3_tarski(k4_xboole_0('#skF_2', C_352)))), inference(resolution, [status(thm)], [c_91, c_8167])).
% 7.99/2.95  tff(c_14, plain, (![A_10, B_11, C_12]: (r1_tarski(k4_xboole_0(A_10, B_11), C_12) | ~r1_tarski(A_10, k2_xboole_0(B_11, C_12)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 7.99/2.95  tff(c_22, plain, (![A_20]: (k3_tarski(k1_zfmisc_1(A_20))=A_20)), inference(cnfTransformation, [status(thm)], [f_55])).
% 7.99/2.95  tff(c_119, plain, (![A_44, B_45]: (r1_tarski(k3_tarski(A_44), k3_tarski(B_45)) | ~r1_tarski(A_44, B_45))), inference(cnfTransformation, [status(thm)], [f_51])).
% 7.99/2.95  tff(c_127, plain, (![A_44, A_20]: (r1_tarski(k3_tarski(A_44), A_20) | ~r1_tarski(A_44, k1_zfmisc_1(A_20)))), inference(superposition, [status(thm), theory('equality')], [c_22, c_119])).
% 7.99/2.95  tff(c_765, plain, (![A_84, B_85, C_86]: (k7_subset_1(A_84, B_85, C_86)=k4_xboole_0(B_85, C_86) | ~m1_subset_1(B_85, k1_zfmisc_1(A_84)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 7.99/2.95  tff(c_1190, plain, (![B_115, A_116, C_117]: (k7_subset_1(B_115, A_116, C_117)=k4_xboole_0(A_116, C_117) | ~r1_tarski(A_116, B_115))), inference(resolution, [status(thm)], [c_30, c_765])).
% 7.99/2.95  tff(c_7598, plain, (![A_331, A_332, C_333]: (k7_subset_1(A_331, k3_tarski(A_332), C_333)=k4_xboole_0(k3_tarski(A_332), C_333) | ~r1_tarski(A_332, k1_zfmisc_1(A_331)))), inference(resolution, [status(thm)], [c_127, c_1190])).
% 7.99/2.95  tff(c_7618, plain, (![C_333]: (k7_subset_1(u1_struct_0('#skF_1'), k3_tarski('#skF_2'), C_333)=k4_xboole_0(k3_tarski('#skF_2'), C_333))), inference(resolution, [status(thm)], [c_91, c_7598])).
% 7.99/2.95  tff(c_774, plain, (![C_86]: (k7_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')), '#skF_2', C_86)=k4_xboole_0('#skF_2', C_86))), inference(resolution, [status(thm)], [c_36, c_765])).
% 7.99/2.95  tff(c_391, plain, (k5_setfam_1(u1_struct_0('#skF_1'), '#skF_2')=k3_tarski('#skF_2')), inference(resolution, [status(thm)], [c_36, c_378])).
% 7.99/2.95  tff(c_34, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(cnfTransformation, [status(thm)], [f_78])).
% 7.99/2.95  tff(c_390, plain, (k5_setfam_1(u1_struct_0('#skF_1'), '#skF_3')=k3_tarski('#skF_3')), inference(resolution, [status(thm)], [c_34, c_378])).
% 7.99/2.95  tff(c_32, plain, (~r1_tarski(k7_subset_1(u1_struct_0('#skF_1'), k5_setfam_1(u1_struct_0('#skF_1'), '#skF_2'), k5_setfam_1(u1_struct_0('#skF_1'), '#skF_3')), k5_setfam_1(u1_struct_0('#skF_1'), k7_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')), '#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_78])).
% 7.99/2.95  tff(c_392, plain, (~r1_tarski(k7_subset_1(u1_struct_0('#skF_1'), k5_setfam_1(u1_struct_0('#skF_1'), '#skF_2'), k3_tarski('#skF_3')), k5_setfam_1(u1_struct_0('#skF_1'), k7_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')), '#skF_2', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_390, c_32])).
% 7.99/2.95  tff(c_402, plain, (~r1_tarski(k7_subset_1(u1_struct_0('#skF_1'), k3_tarski('#skF_2'), k3_tarski('#skF_3')), k5_setfam_1(u1_struct_0('#skF_1'), k7_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')), '#skF_2', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_391, c_392])).
% 7.99/2.95  tff(c_1064, plain, (~r1_tarski(k7_subset_1(u1_struct_0('#skF_1'), k3_tarski('#skF_2'), k3_tarski('#skF_3')), k5_setfam_1(u1_struct_0('#skF_1'), k4_xboole_0('#skF_2', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_774, c_402])).
% 7.99/2.95  tff(c_7622, plain, (~r1_tarski(k4_xboole_0(k3_tarski('#skF_2'), k3_tarski('#skF_3')), k5_setfam_1(u1_struct_0('#skF_1'), k4_xboole_0('#skF_2', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_7618, c_1064])).
% 7.99/2.95  tff(c_7648, plain, (~r1_tarski(k3_tarski('#skF_2'), k2_xboole_0(k3_tarski('#skF_3'), k5_setfam_1(u1_struct_0('#skF_1'), k4_xboole_0('#skF_2', '#skF_3'))))), inference(resolution, [status(thm)], [c_14, c_7622])).
% 7.99/2.95  tff(c_8191, plain, (~r1_tarski(k3_tarski('#skF_2'), k2_xboole_0(k3_tarski('#skF_3'), k3_tarski(k4_xboole_0('#skF_2', '#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_8187, c_7648])).
% 7.99/2.95  tff(c_8198, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_717, c_12, c_20, c_8191])).
% 7.99/2.95  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.99/2.95  
% 7.99/2.95  Inference rules
% 7.99/2.95  ----------------------
% 7.99/2.95  #Ref     : 0
% 7.99/2.95  #Sup     : 2167
% 7.99/2.95  #Fact    : 0
% 7.99/2.95  #Define  : 0
% 7.99/2.95  #Split   : 2
% 7.99/2.95  #Chain   : 0
% 7.99/2.95  #Close   : 0
% 7.99/2.95  
% 7.99/2.95  Ordering : KBO
% 7.99/2.95  
% 7.99/2.95  Simplification rules
% 7.99/2.95  ----------------------
% 7.99/2.95  #Subsume      : 104
% 7.99/2.95  #Demod        : 917
% 7.99/2.95  #Tautology    : 581
% 7.99/2.95  #SimpNegUnit  : 0
% 7.99/2.95  #BackRed      : 8
% 7.99/2.95  
% 7.99/2.95  #Partial instantiations: 0
% 7.99/2.95  #Strategies tried      : 1
% 7.99/2.95  
% 7.99/2.95  Timing (in seconds)
% 7.99/2.95  ----------------------
% 7.99/2.95  Preprocessing        : 0.32
% 7.99/2.95  Parsing              : 0.18
% 7.99/2.95  CNF conversion       : 0.02
% 7.99/2.95  Main loop            : 1.83
% 7.99/2.95  Inferencing          : 0.38
% 7.99/2.95  Reduction            : 0.87
% 7.99/2.95  Demodulation         : 0.76
% 7.99/2.95  BG Simplification    : 0.07
% 7.99/2.95  Subsumption          : 0.40
% 7.99/2.95  Abstraction          : 0.07
% 7.99/2.95  MUC search           : 0.00
% 7.99/2.95  Cooper               : 0.00
% 7.99/2.95  Total                : 2.19
% 7.99/2.95  Index Insertion      : 0.00
% 7.99/2.95  Index Deletion       : 0.00
% 7.99/2.95  Index Matching       : 0.00
% 7.99/2.95  BG Taut test         : 0.00
%------------------------------------------------------------------------------
