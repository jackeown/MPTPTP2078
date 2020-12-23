%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:22:35 EST 2020

% Result     : Theorem 4.27s
% Output     : CNFRefutation 4.27s
% Verified   : 
% Statistics : Number of formulae       :   69 (  95 expanded)
%              Number of leaves         :   30 (  45 expanded)
%              Depth                    :    8
%              Number of atoms          :   76 ( 133 expanded)
%              Number of equality atoms :   23 (  36 expanded)
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

tff(f_43,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_45,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_47,axiom,(
    ! [A,B] : k3_tarski(k2_xboole_0(A,B)) = k2_xboole_0(k3_tarski(A),k3_tarski(B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t96_zfmisc_1)).

tff(f_41,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k2_xboole_0(B,C))
     => r1_tarski(k4_xboole_0(A,B),C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_74,negated_conjecture,(
    ~ ! [A] :
        ( l1_struct_0(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
               => r1_tarski(k7_subset_1(u1_struct_0(A),k5_setfam_1(u1_struct_0(A),B),k5_setfam_1(u1_struct_0(A),C)),k5_setfam_1(u1_struct_0(A),k7_subset_1(k1_zfmisc_1(u1_struct_0(A)),B,C))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_tops_2)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => k5_setfam_1(A,B) = k3_tarski(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k5_setfam_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => m1_subset_1(k5_setfam_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_setfam_1)).

tff(f_63,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

tff(c_12,plain,(
    ! [B_14,A_13] : k2_tarski(B_14,A_13) = k2_tarski(A_13,B_14) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_79,plain,(
    ! [A_40,B_41] : k3_tarski(k2_tarski(A_40,B_41)) = k2_xboole_0(A_40,B_41) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_99,plain,(
    ! [B_44,A_45] : k3_tarski(k2_tarski(B_44,A_45)) = k2_xboole_0(A_45,B_44) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_79])).

tff(c_14,plain,(
    ! [A_15,B_16] : k3_tarski(k2_tarski(A_15,B_16)) = k2_xboole_0(A_15,B_16) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_105,plain,(
    ! [B_44,A_45] : k2_xboole_0(B_44,A_45) = k2_xboole_0(A_45,B_44) ),
    inference(superposition,[status(thm),theory(equality)],[c_99,c_14])).

tff(c_188,plain,(
    ! [A_52,B_53] : k2_xboole_0(k3_tarski(A_52),k3_tarski(B_53)) = k3_tarski(k2_xboole_0(A_52,B_53)) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_10,plain,(
    ! [A_11,B_12] : r1_tarski(A_11,k2_xboole_0(A_11,B_12)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_227,plain,(
    ! [A_54,B_55] : r1_tarski(k3_tarski(A_54),k3_tarski(k2_xboole_0(A_54,B_55))) ),
    inference(superposition,[status(thm),theory(equality)],[c_188,c_10])).

tff(c_236,plain,(
    ! [A_45,B_44] : r1_tarski(k3_tarski(A_45),k3_tarski(k2_xboole_0(B_44,A_45))) ),
    inference(superposition,[status(thm),theory(equality)],[c_105,c_227])).

tff(c_6,plain,(
    ! [A_6,B_7] : k2_xboole_0(A_6,k4_xboole_0(B_7,A_6)) = k2_xboole_0(A_6,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_16,plain,(
    ! [A_17,B_18] : k2_xboole_0(k3_tarski(A_17),k3_tarski(B_18)) = k3_tarski(k2_xboole_0(A_17,B_18)) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_8,plain,(
    ! [A_8,B_9,C_10] :
      ( r1_tarski(k4_xboole_0(A_8,B_9),C_10)
      | ~ r1_tarski(A_8,k2_xboole_0(B_9,C_10)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_4,plain,(
    ! [A_4,B_5] : r1_tarski(k4_xboole_0(A_4,B_5),A_4) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_32,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_798,plain,(
    ! [A_100,B_101,C_102] :
      ( k7_subset_1(A_100,B_101,C_102) = k4_xboole_0(B_101,C_102)
      | ~ m1_subset_1(B_101,k1_zfmisc_1(A_100)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_807,plain,(
    ! [C_102] : k7_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')),'#skF_2',C_102) = k4_xboole_0('#skF_2',C_102) ),
    inference(resolution,[status(thm)],[c_32,c_798])).

tff(c_382,plain,(
    ! [A_79,B_80] :
      ( k5_setfam_1(A_79,B_80) = k3_tarski(B_80)
      | ~ m1_subset_1(B_80,k1_zfmisc_1(k1_zfmisc_1(A_79))) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_395,plain,(
    k5_setfam_1(u1_struct_0('#skF_1'),'#skF_2') = k3_tarski('#skF_2') ),
    inference(resolution,[status(thm)],[c_32,c_382])).

tff(c_969,plain,(
    ! [A_113,B_114] :
      ( m1_subset_1(k5_setfam_1(A_113,B_114),k1_zfmisc_1(A_113))
      | ~ m1_subset_1(B_114,k1_zfmisc_1(k1_zfmisc_1(A_113))) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_987,plain,
    ( m1_subset_1(k3_tarski('#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ),
    inference(superposition,[status(thm),theory(equality)],[c_395,c_969])).

tff(c_995,plain,(
    m1_subset_1(k3_tarski('#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_987])).

tff(c_18,plain,(
    ! [A_19,B_20,C_21] :
      ( k7_subset_1(A_19,B_20,C_21) = k4_xboole_0(B_20,C_21)
      | ~ m1_subset_1(B_20,k1_zfmisc_1(A_19)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_1003,plain,(
    ! [C_21] : k7_subset_1(u1_struct_0('#skF_1'),k3_tarski('#skF_2'),C_21) = k4_xboole_0(k3_tarski('#skF_2'),C_21) ),
    inference(resolution,[status(thm)],[c_995,c_18])).

tff(c_70,plain,(
    ! [A_38,B_39] :
      ( r1_tarski(A_38,B_39)
      | ~ m1_subset_1(A_38,k1_zfmisc_1(B_39)) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_78,plain,(
    r1_tarski('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_32,c_70])).

tff(c_283,plain,(
    ! [A_60,C_61,B_62] :
      ( r1_tarski(A_60,C_61)
      | ~ r1_tarski(B_62,C_61)
      | ~ r1_tarski(A_60,B_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_304,plain,(
    ! [A_60] :
      ( r1_tarski(A_60,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ r1_tarski(A_60,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_78,c_283])).

tff(c_26,plain,(
    ! [A_26,B_27] :
      ( m1_subset_1(A_26,k1_zfmisc_1(B_27))
      | ~ r1_tarski(A_26,B_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_406,plain,(
    ! [A_81,A_82] :
      ( k5_setfam_1(A_81,A_82) = k3_tarski(A_82)
      | ~ r1_tarski(A_82,k1_zfmisc_1(A_81)) ) ),
    inference(resolution,[status(thm)],[c_26,c_382])).

tff(c_719,plain,(
    ! [A_97] :
      ( k5_setfam_1(u1_struct_0('#skF_1'),A_97) = k3_tarski(A_97)
      | ~ r1_tarski(A_97,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_304,c_406])).

tff(c_30,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_394,plain,(
    k5_setfam_1(u1_struct_0('#skF_1'),'#skF_3') = k3_tarski('#skF_3') ),
    inference(resolution,[status(thm)],[c_30,c_382])).

tff(c_28,plain,(
    ~ r1_tarski(k7_subset_1(u1_struct_0('#skF_1'),k5_setfam_1(u1_struct_0('#skF_1'),'#skF_2'),k5_setfam_1(u1_struct_0('#skF_1'),'#skF_3')),k5_setfam_1(u1_struct_0('#skF_1'),k7_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')),'#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_396,plain,(
    ~ r1_tarski(k7_subset_1(u1_struct_0('#skF_1'),k5_setfam_1(u1_struct_0('#skF_1'),'#skF_2'),k3_tarski('#skF_3')),k5_setfam_1(u1_struct_0('#skF_1'),k7_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')),'#skF_2','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_394,c_28])).

tff(c_405,plain,(
    ~ r1_tarski(k7_subset_1(u1_struct_0('#skF_1'),k3_tarski('#skF_2'),k3_tarski('#skF_3')),k5_setfam_1(u1_struct_0('#skF_1'),k7_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')),'#skF_2','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_395,c_396])).

tff(c_728,plain,
    ( ~ r1_tarski(k7_subset_1(u1_struct_0('#skF_1'),k3_tarski('#skF_2'),k3_tarski('#skF_3')),k3_tarski(k7_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')),'#skF_2','#skF_3')))
    | ~ r1_tarski(k7_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')),'#skF_2','#skF_3'),'#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_719,c_405])).

tff(c_2198,plain,(
    ~ r1_tarski(k4_xboole_0(k3_tarski('#skF_2'),k3_tarski('#skF_3')),k3_tarski(k4_xboole_0('#skF_2','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_807,c_1003,c_807,c_728])).

tff(c_2201,plain,(
    ~ r1_tarski(k3_tarski('#skF_2'),k2_xboole_0(k3_tarski('#skF_3'),k3_tarski(k4_xboole_0('#skF_2','#skF_3')))) ),
    inference(resolution,[status(thm)],[c_8,c_2198])).

tff(c_2205,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_236,c_6,c_16,c_2201])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:41:11 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.27/1.73  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.27/1.73  
% 4.27/1.73  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.27/1.74  %$ r1_tarski > m1_subset_1 > l1_struct_0 > k7_subset_1 > k5_setfam_1 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > u1_struct_0 > k3_tarski > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1
% 4.27/1.74  
% 4.27/1.74  %Foreground sorts:
% 4.27/1.74  
% 4.27/1.74  
% 4.27/1.74  %Background operators:
% 4.27/1.74  
% 4.27/1.74  
% 4.27/1.74  %Foreground operators:
% 4.27/1.74  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.27/1.74  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.27/1.74  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.27/1.74  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.27/1.74  tff('#skF_2', type, '#skF_2': $i).
% 4.27/1.74  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 4.27/1.74  tff('#skF_3', type, '#skF_3': $i).
% 4.27/1.74  tff('#skF_1', type, '#skF_1': $i).
% 4.27/1.74  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.27/1.74  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 4.27/1.74  tff(k5_setfam_1, type, k5_setfam_1: ($i * $i) > $i).
% 4.27/1.74  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.27/1.74  tff(k3_tarski, type, k3_tarski: $i > $i).
% 4.27/1.74  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.27/1.74  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.27/1.74  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 4.27/1.74  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.27/1.74  
% 4.27/1.75  tff(f_43, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 4.27/1.75  tff(f_45, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 4.27/1.75  tff(f_47, axiom, (![A, B]: (k3_tarski(k2_xboole_0(A, B)) = k2_xboole_0(k3_tarski(A), k3_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t96_zfmisc_1)).
% 4.27/1.75  tff(f_41, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 4.27/1.75  tff(f_35, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_xboole_1)).
% 4.27/1.75  tff(f_39, axiom, (![A, B, C]: (r1_tarski(A, k2_xboole_0(B, C)) => r1_tarski(k4_xboole_0(A, B), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_xboole_1)).
% 4.27/1.75  tff(f_33, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 4.27/1.75  tff(f_74, negated_conjecture, ~(![A]: (l1_struct_0(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => r1_tarski(k7_subset_1(u1_struct_0(A), k5_setfam_1(u1_struct_0(A), B), k5_setfam_1(u1_struct_0(A), C)), k5_setfam_1(u1_struct_0(A), k7_subset_1(k1_zfmisc_1(u1_struct_0(A)), B, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_tops_2)).
% 4.27/1.75  tff(f_51, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 4.27/1.75  tff(f_59, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (k5_setfam_1(A, B) = k3_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k5_setfam_1)).
% 4.27/1.75  tff(f_55, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => m1_subset_1(k5_setfam_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k5_setfam_1)).
% 4.27/1.75  tff(f_63, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 4.27/1.75  tff(f_31, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 4.27/1.75  tff(c_12, plain, (![B_14, A_13]: (k2_tarski(B_14, A_13)=k2_tarski(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.27/1.75  tff(c_79, plain, (![A_40, B_41]: (k3_tarski(k2_tarski(A_40, B_41))=k2_xboole_0(A_40, B_41))), inference(cnfTransformation, [status(thm)], [f_45])).
% 4.27/1.75  tff(c_99, plain, (![B_44, A_45]: (k3_tarski(k2_tarski(B_44, A_45))=k2_xboole_0(A_45, B_44))), inference(superposition, [status(thm), theory('equality')], [c_12, c_79])).
% 4.27/1.75  tff(c_14, plain, (![A_15, B_16]: (k3_tarski(k2_tarski(A_15, B_16))=k2_xboole_0(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_45])).
% 4.27/1.75  tff(c_105, plain, (![B_44, A_45]: (k2_xboole_0(B_44, A_45)=k2_xboole_0(A_45, B_44))), inference(superposition, [status(thm), theory('equality')], [c_99, c_14])).
% 4.27/1.75  tff(c_188, plain, (![A_52, B_53]: (k2_xboole_0(k3_tarski(A_52), k3_tarski(B_53))=k3_tarski(k2_xboole_0(A_52, B_53)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 4.27/1.75  tff(c_10, plain, (![A_11, B_12]: (r1_tarski(A_11, k2_xboole_0(A_11, B_12)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.27/1.75  tff(c_227, plain, (![A_54, B_55]: (r1_tarski(k3_tarski(A_54), k3_tarski(k2_xboole_0(A_54, B_55))))), inference(superposition, [status(thm), theory('equality')], [c_188, c_10])).
% 4.27/1.75  tff(c_236, plain, (![A_45, B_44]: (r1_tarski(k3_tarski(A_45), k3_tarski(k2_xboole_0(B_44, A_45))))), inference(superposition, [status(thm), theory('equality')], [c_105, c_227])).
% 4.27/1.75  tff(c_6, plain, (![A_6, B_7]: (k2_xboole_0(A_6, k4_xboole_0(B_7, A_6))=k2_xboole_0(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.27/1.75  tff(c_16, plain, (![A_17, B_18]: (k2_xboole_0(k3_tarski(A_17), k3_tarski(B_18))=k3_tarski(k2_xboole_0(A_17, B_18)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 4.27/1.75  tff(c_8, plain, (![A_8, B_9, C_10]: (r1_tarski(k4_xboole_0(A_8, B_9), C_10) | ~r1_tarski(A_8, k2_xboole_0(B_9, C_10)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.27/1.75  tff(c_4, plain, (![A_4, B_5]: (r1_tarski(k4_xboole_0(A_4, B_5), A_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.27/1.75  tff(c_32, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 4.27/1.75  tff(c_798, plain, (![A_100, B_101, C_102]: (k7_subset_1(A_100, B_101, C_102)=k4_xboole_0(B_101, C_102) | ~m1_subset_1(B_101, k1_zfmisc_1(A_100)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 4.27/1.75  tff(c_807, plain, (![C_102]: (k7_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')), '#skF_2', C_102)=k4_xboole_0('#skF_2', C_102))), inference(resolution, [status(thm)], [c_32, c_798])).
% 4.27/1.75  tff(c_382, plain, (![A_79, B_80]: (k5_setfam_1(A_79, B_80)=k3_tarski(B_80) | ~m1_subset_1(B_80, k1_zfmisc_1(k1_zfmisc_1(A_79))))), inference(cnfTransformation, [status(thm)], [f_59])).
% 4.27/1.75  tff(c_395, plain, (k5_setfam_1(u1_struct_0('#skF_1'), '#skF_2')=k3_tarski('#skF_2')), inference(resolution, [status(thm)], [c_32, c_382])).
% 4.27/1.75  tff(c_969, plain, (![A_113, B_114]: (m1_subset_1(k5_setfam_1(A_113, B_114), k1_zfmisc_1(A_113)) | ~m1_subset_1(B_114, k1_zfmisc_1(k1_zfmisc_1(A_113))))), inference(cnfTransformation, [status(thm)], [f_55])).
% 4.27/1.75  tff(c_987, plain, (m1_subset_1(k3_tarski('#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1('#skF_2', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(superposition, [status(thm), theory('equality')], [c_395, c_969])).
% 4.27/1.75  tff(c_995, plain, (m1_subset_1(k3_tarski('#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_987])).
% 4.27/1.75  tff(c_18, plain, (![A_19, B_20, C_21]: (k7_subset_1(A_19, B_20, C_21)=k4_xboole_0(B_20, C_21) | ~m1_subset_1(B_20, k1_zfmisc_1(A_19)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 4.27/1.75  tff(c_1003, plain, (![C_21]: (k7_subset_1(u1_struct_0('#skF_1'), k3_tarski('#skF_2'), C_21)=k4_xboole_0(k3_tarski('#skF_2'), C_21))), inference(resolution, [status(thm)], [c_995, c_18])).
% 4.27/1.75  tff(c_70, plain, (![A_38, B_39]: (r1_tarski(A_38, B_39) | ~m1_subset_1(A_38, k1_zfmisc_1(B_39)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 4.27/1.75  tff(c_78, plain, (r1_tarski('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_32, c_70])).
% 4.27/1.75  tff(c_283, plain, (![A_60, C_61, B_62]: (r1_tarski(A_60, C_61) | ~r1_tarski(B_62, C_61) | ~r1_tarski(A_60, B_62))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.27/1.75  tff(c_304, plain, (![A_60]: (r1_tarski(A_60, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~r1_tarski(A_60, '#skF_2'))), inference(resolution, [status(thm)], [c_78, c_283])).
% 4.27/1.75  tff(c_26, plain, (![A_26, B_27]: (m1_subset_1(A_26, k1_zfmisc_1(B_27)) | ~r1_tarski(A_26, B_27))), inference(cnfTransformation, [status(thm)], [f_63])).
% 4.27/1.75  tff(c_406, plain, (![A_81, A_82]: (k5_setfam_1(A_81, A_82)=k3_tarski(A_82) | ~r1_tarski(A_82, k1_zfmisc_1(A_81)))), inference(resolution, [status(thm)], [c_26, c_382])).
% 4.27/1.75  tff(c_719, plain, (![A_97]: (k5_setfam_1(u1_struct_0('#skF_1'), A_97)=k3_tarski(A_97) | ~r1_tarski(A_97, '#skF_2'))), inference(resolution, [status(thm)], [c_304, c_406])).
% 4.27/1.75  tff(c_30, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 4.27/1.75  tff(c_394, plain, (k5_setfam_1(u1_struct_0('#skF_1'), '#skF_3')=k3_tarski('#skF_3')), inference(resolution, [status(thm)], [c_30, c_382])).
% 4.27/1.75  tff(c_28, plain, (~r1_tarski(k7_subset_1(u1_struct_0('#skF_1'), k5_setfam_1(u1_struct_0('#skF_1'), '#skF_2'), k5_setfam_1(u1_struct_0('#skF_1'), '#skF_3')), k5_setfam_1(u1_struct_0('#skF_1'), k7_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')), '#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_74])).
% 4.27/1.75  tff(c_396, plain, (~r1_tarski(k7_subset_1(u1_struct_0('#skF_1'), k5_setfam_1(u1_struct_0('#skF_1'), '#skF_2'), k3_tarski('#skF_3')), k5_setfam_1(u1_struct_0('#skF_1'), k7_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')), '#skF_2', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_394, c_28])).
% 4.27/1.75  tff(c_405, plain, (~r1_tarski(k7_subset_1(u1_struct_0('#skF_1'), k3_tarski('#skF_2'), k3_tarski('#skF_3')), k5_setfam_1(u1_struct_0('#skF_1'), k7_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')), '#skF_2', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_395, c_396])).
% 4.27/1.75  tff(c_728, plain, (~r1_tarski(k7_subset_1(u1_struct_0('#skF_1'), k3_tarski('#skF_2'), k3_tarski('#skF_3')), k3_tarski(k7_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')), '#skF_2', '#skF_3'))) | ~r1_tarski(k7_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')), '#skF_2', '#skF_3'), '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_719, c_405])).
% 4.27/1.75  tff(c_2198, plain, (~r1_tarski(k4_xboole_0(k3_tarski('#skF_2'), k3_tarski('#skF_3')), k3_tarski(k4_xboole_0('#skF_2', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_807, c_1003, c_807, c_728])).
% 4.27/1.75  tff(c_2201, plain, (~r1_tarski(k3_tarski('#skF_2'), k2_xboole_0(k3_tarski('#skF_3'), k3_tarski(k4_xboole_0('#skF_2', '#skF_3'))))), inference(resolution, [status(thm)], [c_8, c_2198])).
% 4.27/1.75  tff(c_2205, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_236, c_6, c_16, c_2201])).
% 4.27/1.75  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.27/1.75  
% 4.27/1.75  Inference rules
% 4.27/1.75  ----------------------
% 4.27/1.75  #Ref     : 0
% 4.27/1.75  #Sup     : 602
% 4.27/1.75  #Fact    : 0
% 4.27/1.75  #Define  : 0
% 4.27/1.75  #Split   : 1
% 4.27/1.75  #Chain   : 0
% 4.27/1.75  #Close   : 0
% 4.27/1.75  
% 4.27/1.75  Ordering : KBO
% 4.27/1.75  
% 4.27/1.75  Simplification rules
% 4.27/1.75  ----------------------
% 4.27/1.75  #Subsume      : 22
% 4.27/1.75  #Demod        : 146
% 4.27/1.75  #Tautology    : 192
% 4.27/1.75  #SimpNegUnit  : 0
% 4.27/1.75  #BackRed      : 3
% 4.27/1.75  
% 4.27/1.75  #Partial instantiations: 0
% 4.27/1.75  #Strategies tried      : 1
% 4.27/1.75  
% 4.27/1.75  Timing (in seconds)
% 4.27/1.75  ----------------------
% 4.27/1.75  Preprocessing        : 0.30
% 4.27/1.75  Parsing              : 0.17
% 4.27/1.75  CNF conversion       : 0.02
% 4.27/1.75  Main loop            : 0.67
% 4.27/1.75  Inferencing          : 0.19
% 4.27/1.75  Reduction            : 0.27
% 4.27/1.75  Demodulation         : 0.22
% 4.27/1.75  BG Simplification    : 0.03
% 4.27/1.75  Subsumption          : 0.13
% 4.27/1.75  Abstraction          : 0.03
% 4.27/1.75  MUC search           : 0.00
% 4.27/1.75  Cooper               : 0.00
% 4.27/1.75  Total                : 1.00
% 4.27/1.75  Index Insertion      : 0.00
% 4.27/1.75  Index Deletion       : 0.00
% 4.27/1.75  Index Matching       : 0.00
% 4.27/1.75  BG Taut test         : 0.00
%------------------------------------------------------------------------------
