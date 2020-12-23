%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:22:35 EST 2020

% Result     : Theorem 5.74s
% Output     : CNFRefutation 5.74s
% Verified   : 
% Statistics : Number of formulae       :   69 ( 100 expanded)
%              Number of leaves         :   28 (  46 expanded)
%              Depth                    :    9
%              Number of atoms          :   80 ( 140 expanded)
%              Number of equality atoms :   24 (  40 expanded)
%              Maximal formula depth    :    9 (   3 average)
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

tff(f_37,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_39,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_35,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_41,axiom,(
    ! [A,B] : k3_tarski(k2_xboole_0(A,B)) = k2_xboole_0(k3_tarski(A),k3_tarski(B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t96_zfmisc_1)).

tff(f_29,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_74,negated_conjecture,(
    ~ ! [A] :
        ( l1_struct_0(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
               => r1_tarski(k7_subset_1(u1_struct_0(A),k5_setfam_1(u1_struct_0(A),B),k5_setfam_1(u1_struct_0(A),C)),k5_setfam_1(u1_struct_0(A),k7_subset_1(k1_zfmisc_1(u1_struct_0(A)),B,C))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_tops_2)).

tff(f_33,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k2_xboole_0(B,C))
     => r1_tarski(k4_xboole_0(A,B),C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_xboole_1)).

tff(f_63,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
         => ! [C] :
              ( r1_tarski(C,B)
             => m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_tops_2)).

tff(f_53,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => k5_setfam_1(A,B) = k3_tarski(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k5_setfam_1)).

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

tff(c_10,plain,(
    ! [B_11,A_10] : k2_tarski(B_11,A_10) = k2_tarski(A_10,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_66,plain,(
    ! [A_40,B_41] : k3_tarski(k2_tarski(A_40,B_41)) = k2_xboole_0(A_40,B_41) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_81,plain,(
    ! [B_42,A_43] : k3_tarski(k2_tarski(B_42,A_43)) = k2_xboole_0(A_43,B_42) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_66])).

tff(c_12,plain,(
    ! [A_12,B_13] : k3_tarski(k2_tarski(A_12,B_13)) = k2_xboole_0(A_12,B_13) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_104,plain,(
    ! [B_44,A_45] : k2_xboole_0(B_44,A_45) = k2_xboole_0(A_45,B_44) ),
    inference(superposition,[status(thm),theory(equality)],[c_81,c_12])).

tff(c_8,plain,(
    ! [A_8,B_9] : r1_tarski(A_8,k2_xboole_0(A_8,B_9)) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_119,plain,(
    ! [A_45,B_44] : r1_tarski(A_45,k2_xboole_0(B_44,A_45)) ),
    inference(superposition,[status(thm),theory(equality)],[c_104,c_8])).

tff(c_87,plain,(
    ! [B_42,A_43] : k2_xboole_0(B_42,A_43) = k2_xboole_0(A_43,B_42) ),
    inference(superposition,[status(thm),theory(equality)],[c_81,c_12])).

tff(c_170,plain,(
    ! [A_50,B_51] : k2_xboole_0(k3_tarski(A_50),k3_tarski(B_51)) = k3_tarski(k2_xboole_0(A_50,B_51)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_209,plain,(
    ! [A_52,B_53] : r1_tarski(k3_tarski(A_52),k3_tarski(k2_xboole_0(A_52,B_53))) ),
    inference(superposition,[status(thm),theory(equality)],[c_170,c_8])).

tff(c_218,plain,(
    ! [A_43,B_42] : r1_tarski(k3_tarski(A_43),k3_tarski(k2_xboole_0(B_42,A_43))) ),
    inference(superposition,[status(thm),theory(equality)],[c_87,c_209])).

tff(c_4,plain,(
    ! [A_3,B_4] : k2_xboole_0(A_3,k4_xboole_0(B_4,A_3)) = k2_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_14,plain,(
    ! [A_14,B_15] : k2_xboole_0(k3_tarski(A_14),k3_tarski(B_15)) = k3_tarski(k2_xboole_0(A_14,B_15)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_30,plain,(
    l1_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_28,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_6,plain,(
    ! [A_5,B_6,C_7] :
      ( r1_tarski(k4_xboole_0(A_5,B_6),C_7)
      | ~ r1_tarski(A_5,k2_xboole_0(B_6,C_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_690,plain,(
    ! [C_87,A_88,B_89] :
      ( m1_subset_1(C_87,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_88))))
      | ~ r1_tarski(C_87,B_89)
      | ~ m1_subset_1(B_89,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_88))))
      | ~ l1_struct_0(A_88) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_2178,plain,(
    ! [A_154,B_155,A_156,C_157] :
      ( m1_subset_1(k4_xboole_0(A_154,B_155),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_156))))
      | ~ m1_subset_1(C_157,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_156))))
      | ~ l1_struct_0(A_156)
      | ~ r1_tarski(A_154,k2_xboole_0(B_155,C_157)) ) ),
    inference(resolution,[status(thm)],[c_6,c_690])).

tff(c_2187,plain,(
    ! [A_154,B_155] :
      ( m1_subset_1(k4_xboole_0(A_154,B_155),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))
      | ~ l1_struct_0('#skF_1')
      | ~ r1_tarski(A_154,k2_xboole_0(B_155,'#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_28,c_2178])).

tff(c_2502,plain,(
    ! [A_167,B_168] :
      ( m1_subset_1(k4_xboole_0(A_167,B_168),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))
      | ~ r1_tarski(A_167,k2_xboole_0(B_168,'#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_2187])).

tff(c_20,plain,(
    ! [A_21,B_22] :
      ( k5_setfam_1(A_21,B_22) = k3_tarski(B_22)
      | ~ m1_subset_1(B_22,k1_zfmisc_1(k1_zfmisc_1(A_21))) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_4133,plain,(
    ! [A_199,B_200] :
      ( k5_setfam_1(u1_struct_0('#skF_1'),k4_xboole_0(A_199,B_200)) = k3_tarski(k4_xboole_0(A_199,B_200))
      | ~ r1_tarski(A_199,k2_xboole_0(B_200,'#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_2502,c_20])).

tff(c_251,plain,(
    ! [A_56,B_57] :
      ( k5_setfam_1(A_56,B_57) = k3_tarski(B_57)
      | ~ m1_subset_1(B_57,k1_zfmisc_1(k1_zfmisc_1(A_56))) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_259,plain,(
    k5_setfam_1(u1_struct_0('#skF_1'),'#skF_2') = k3_tarski('#skF_2') ),
    inference(resolution,[status(thm)],[c_28,c_251])).

tff(c_610,plain,(
    ! [A_80,B_81] :
      ( m1_subset_1(k5_setfam_1(A_80,B_81),k1_zfmisc_1(A_80))
      | ~ m1_subset_1(B_81,k1_zfmisc_1(k1_zfmisc_1(A_80))) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_619,plain,
    ( m1_subset_1(k3_tarski('#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ),
    inference(superposition,[status(thm),theory(equality)],[c_259,c_610])).

tff(c_626,plain,(
    m1_subset_1(k3_tarski('#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_619])).

tff(c_16,plain,(
    ! [A_16,B_17,C_18] :
      ( k7_subset_1(A_16,B_17,C_18) = k4_xboole_0(B_17,C_18)
      | ~ m1_subset_1(B_17,k1_zfmisc_1(A_16)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_631,plain,(
    ! [C_18] : k7_subset_1(u1_struct_0('#skF_1'),k3_tarski('#skF_2'),C_18) = k4_xboole_0(k3_tarski('#skF_2'),C_18) ),
    inference(resolution,[status(thm)],[c_626,c_16])).

tff(c_520,plain,(
    ! [A_71,B_72,C_73] :
      ( k7_subset_1(A_71,B_72,C_73) = k4_xboole_0(B_72,C_73)
      | ~ m1_subset_1(B_72,k1_zfmisc_1(A_71)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_526,plain,(
    ! [C_73] : k7_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')),'#skF_2',C_73) = k4_xboole_0('#skF_2',C_73) ),
    inference(resolution,[status(thm)],[c_28,c_520])).

tff(c_26,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_258,plain,(
    k5_setfam_1(u1_struct_0('#skF_1'),'#skF_3') = k3_tarski('#skF_3') ),
    inference(resolution,[status(thm)],[c_26,c_251])).

tff(c_24,plain,(
    ~ r1_tarski(k7_subset_1(u1_struct_0('#skF_1'),k5_setfam_1(u1_struct_0('#skF_1'),'#skF_2'),k5_setfam_1(u1_struct_0('#skF_1'),'#skF_3')),k5_setfam_1(u1_struct_0('#skF_1'),k7_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')),'#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_260,plain,(
    ~ r1_tarski(k7_subset_1(u1_struct_0('#skF_1'),k5_setfam_1(u1_struct_0('#skF_1'),'#skF_2'),k3_tarski('#skF_3')),k5_setfam_1(u1_struct_0('#skF_1'),k7_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')),'#skF_2','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_258,c_24])).

tff(c_387,plain,(
    ~ r1_tarski(k7_subset_1(u1_struct_0('#skF_1'),k3_tarski('#skF_2'),k3_tarski('#skF_3')),k5_setfam_1(u1_struct_0('#skF_1'),k7_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')),'#skF_2','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_259,c_260])).

tff(c_536,plain,(
    ~ r1_tarski(k7_subset_1(u1_struct_0('#skF_1'),k3_tarski('#skF_2'),k3_tarski('#skF_3')),k5_setfam_1(u1_struct_0('#skF_1'),k4_xboole_0('#skF_2','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_526,c_387])).

tff(c_771,plain,(
    ~ r1_tarski(k4_xboole_0(k3_tarski('#skF_2'),k3_tarski('#skF_3')),k5_setfam_1(u1_struct_0('#skF_1'),k4_xboole_0('#skF_2','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_631,c_536])).

tff(c_1071,plain,(
    ~ r1_tarski(k3_tarski('#skF_2'),k2_xboole_0(k3_tarski('#skF_3'),k5_setfam_1(u1_struct_0('#skF_1'),k4_xboole_0('#skF_2','#skF_3')))) ),
    inference(resolution,[status(thm)],[c_6,c_771])).

tff(c_4142,plain,
    ( ~ r1_tarski(k3_tarski('#skF_2'),k2_xboole_0(k3_tarski('#skF_3'),k3_tarski(k4_xboole_0('#skF_2','#skF_3'))))
    | ~ r1_tarski('#skF_2',k2_xboole_0('#skF_3','#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_4133,c_1071])).

tff(c_4159,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_119,c_218,c_4,c_14,c_4142])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n007.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:38:36 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.74/2.17  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.74/2.18  
% 5.74/2.18  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.74/2.18  %$ r1_tarski > m1_subset_1 > l1_struct_0 > k7_subset_1 > k5_setfam_1 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > u1_struct_0 > k3_tarski > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1
% 5.74/2.18  
% 5.74/2.18  %Foreground sorts:
% 5.74/2.18  
% 5.74/2.18  
% 5.74/2.18  %Background operators:
% 5.74/2.18  
% 5.74/2.18  
% 5.74/2.18  %Foreground operators:
% 5.74/2.18  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.74/2.18  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 5.74/2.18  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.74/2.18  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 5.74/2.18  tff('#skF_2', type, '#skF_2': $i).
% 5.74/2.18  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 5.74/2.18  tff('#skF_3', type, '#skF_3': $i).
% 5.74/2.18  tff('#skF_1', type, '#skF_1': $i).
% 5.74/2.18  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.74/2.18  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 5.74/2.18  tff(k5_setfam_1, type, k5_setfam_1: ($i * $i) > $i).
% 5.74/2.18  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.74/2.18  tff(k3_tarski, type, k3_tarski: $i > $i).
% 5.74/2.18  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.74/2.18  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 5.74/2.18  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 5.74/2.18  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.74/2.18  
% 5.74/2.19  tff(f_37, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 5.74/2.19  tff(f_39, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 5.74/2.19  tff(f_35, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 5.74/2.19  tff(f_41, axiom, (![A, B]: (k3_tarski(k2_xboole_0(A, B)) = k2_xboole_0(k3_tarski(A), k3_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t96_zfmisc_1)).
% 5.74/2.19  tff(f_29, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 5.74/2.19  tff(f_74, negated_conjecture, ~(![A]: (l1_struct_0(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => r1_tarski(k7_subset_1(u1_struct_0(A), k5_setfam_1(u1_struct_0(A), B), k5_setfam_1(u1_struct_0(A), C)), k5_setfam_1(u1_struct_0(A), k7_subset_1(k1_zfmisc_1(u1_struct_0(A)), B, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_tops_2)).
% 5.74/2.19  tff(f_33, axiom, (![A, B, C]: (r1_tarski(A, k2_xboole_0(B, C)) => r1_tarski(k4_xboole_0(A, B), C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_xboole_1)).
% 5.74/2.19  tff(f_63, axiom, (![A]: (l1_struct_0(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => (![C]: (r1_tarski(C, B) => m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_tops_2)).
% 5.74/2.19  tff(f_53, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (k5_setfam_1(A, B) = k3_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k5_setfam_1)).
% 5.74/2.19  tff(f_49, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => m1_subset_1(k5_setfam_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k5_setfam_1)).
% 5.74/2.19  tff(f_45, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 5.74/2.19  tff(c_10, plain, (![B_11, A_10]: (k2_tarski(B_11, A_10)=k2_tarski(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_37])).
% 5.74/2.19  tff(c_66, plain, (![A_40, B_41]: (k3_tarski(k2_tarski(A_40, B_41))=k2_xboole_0(A_40, B_41))), inference(cnfTransformation, [status(thm)], [f_39])).
% 5.74/2.19  tff(c_81, plain, (![B_42, A_43]: (k3_tarski(k2_tarski(B_42, A_43))=k2_xboole_0(A_43, B_42))), inference(superposition, [status(thm), theory('equality')], [c_10, c_66])).
% 5.74/2.19  tff(c_12, plain, (![A_12, B_13]: (k3_tarski(k2_tarski(A_12, B_13))=k2_xboole_0(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_39])).
% 5.74/2.19  tff(c_104, plain, (![B_44, A_45]: (k2_xboole_0(B_44, A_45)=k2_xboole_0(A_45, B_44))), inference(superposition, [status(thm), theory('equality')], [c_81, c_12])).
% 5.74/2.19  tff(c_8, plain, (![A_8, B_9]: (r1_tarski(A_8, k2_xboole_0(A_8, B_9)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 5.74/2.19  tff(c_119, plain, (![A_45, B_44]: (r1_tarski(A_45, k2_xboole_0(B_44, A_45)))), inference(superposition, [status(thm), theory('equality')], [c_104, c_8])).
% 5.74/2.19  tff(c_87, plain, (![B_42, A_43]: (k2_xboole_0(B_42, A_43)=k2_xboole_0(A_43, B_42))), inference(superposition, [status(thm), theory('equality')], [c_81, c_12])).
% 5.74/2.19  tff(c_170, plain, (![A_50, B_51]: (k2_xboole_0(k3_tarski(A_50), k3_tarski(B_51))=k3_tarski(k2_xboole_0(A_50, B_51)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 5.74/2.19  tff(c_209, plain, (![A_52, B_53]: (r1_tarski(k3_tarski(A_52), k3_tarski(k2_xboole_0(A_52, B_53))))), inference(superposition, [status(thm), theory('equality')], [c_170, c_8])).
% 5.74/2.19  tff(c_218, plain, (![A_43, B_42]: (r1_tarski(k3_tarski(A_43), k3_tarski(k2_xboole_0(B_42, A_43))))), inference(superposition, [status(thm), theory('equality')], [c_87, c_209])).
% 5.74/2.19  tff(c_4, plain, (![A_3, B_4]: (k2_xboole_0(A_3, k4_xboole_0(B_4, A_3))=k2_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 5.74/2.19  tff(c_14, plain, (![A_14, B_15]: (k2_xboole_0(k3_tarski(A_14), k3_tarski(B_15))=k3_tarski(k2_xboole_0(A_14, B_15)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 5.74/2.19  tff(c_30, plain, (l1_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_74])).
% 5.74/2.19  tff(c_28, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 5.74/2.19  tff(c_6, plain, (![A_5, B_6, C_7]: (r1_tarski(k4_xboole_0(A_5, B_6), C_7) | ~r1_tarski(A_5, k2_xboole_0(B_6, C_7)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 5.74/2.19  tff(c_690, plain, (![C_87, A_88, B_89]: (m1_subset_1(C_87, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_88)))) | ~r1_tarski(C_87, B_89) | ~m1_subset_1(B_89, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_88)))) | ~l1_struct_0(A_88))), inference(cnfTransformation, [status(thm)], [f_63])).
% 5.74/2.19  tff(c_2178, plain, (![A_154, B_155, A_156, C_157]: (m1_subset_1(k4_xboole_0(A_154, B_155), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_156)))) | ~m1_subset_1(C_157, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_156)))) | ~l1_struct_0(A_156) | ~r1_tarski(A_154, k2_xboole_0(B_155, C_157)))), inference(resolution, [status(thm)], [c_6, c_690])).
% 5.74/2.19  tff(c_2187, plain, (![A_154, B_155]: (m1_subset_1(k4_xboole_0(A_154, B_155), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) | ~l1_struct_0('#skF_1') | ~r1_tarski(A_154, k2_xboole_0(B_155, '#skF_2')))), inference(resolution, [status(thm)], [c_28, c_2178])).
% 5.74/2.19  tff(c_2502, plain, (![A_167, B_168]: (m1_subset_1(k4_xboole_0(A_167, B_168), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) | ~r1_tarski(A_167, k2_xboole_0(B_168, '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_2187])).
% 5.74/2.19  tff(c_20, plain, (![A_21, B_22]: (k5_setfam_1(A_21, B_22)=k3_tarski(B_22) | ~m1_subset_1(B_22, k1_zfmisc_1(k1_zfmisc_1(A_21))))), inference(cnfTransformation, [status(thm)], [f_53])).
% 5.74/2.19  tff(c_4133, plain, (![A_199, B_200]: (k5_setfam_1(u1_struct_0('#skF_1'), k4_xboole_0(A_199, B_200))=k3_tarski(k4_xboole_0(A_199, B_200)) | ~r1_tarski(A_199, k2_xboole_0(B_200, '#skF_2')))), inference(resolution, [status(thm)], [c_2502, c_20])).
% 5.74/2.19  tff(c_251, plain, (![A_56, B_57]: (k5_setfam_1(A_56, B_57)=k3_tarski(B_57) | ~m1_subset_1(B_57, k1_zfmisc_1(k1_zfmisc_1(A_56))))), inference(cnfTransformation, [status(thm)], [f_53])).
% 5.74/2.19  tff(c_259, plain, (k5_setfam_1(u1_struct_0('#skF_1'), '#skF_2')=k3_tarski('#skF_2')), inference(resolution, [status(thm)], [c_28, c_251])).
% 5.74/2.19  tff(c_610, plain, (![A_80, B_81]: (m1_subset_1(k5_setfam_1(A_80, B_81), k1_zfmisc_1(A_80)) | ~m1_subset_1(B_81, k1_zfmisc_1(k1_zfmisc_1(A_80))))), inference(cnfTransformation, [status(thm)], [f_49])).
% 5.74/2.19  tff(c_619, plain, (m1_subset_1(k3_tarski('#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1('#skF_2', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(superposition, [status(thm), theory('equality')], [c_259, c_610])).
% 5.74/2.19  tff(c_626, plain, (m1_subset_1(k3_tarski('#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_619])).
% 5.74/2.19  tff(c_16, plain, (![A_16, B_17, C_18]: (k7_subset_1(A_16, B_17, C_18)=k4_xboole_0(B_17, C_18) | ~m1_subset_1(B_17, k1_zfmisc_1(A_16)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 5.74/2.19  tff(c_631, plain, (![C_18]: (k7_subset_1(u1_struct_0('#skF_1'), k3_tarski('#skF_2'), C_18)=k4_xboole_0(k3_tarski('#skF_2'), C_18))), inference(resolution, [status(thm)], [c_626, c_16])).
% 5.74/2.19  tff(c_520, plain, (![A_71, B_72, C_73]: (k7_subset_1(A_71, B_72, C_73)=k4_xboole_0(B_72, C_73) | ~m1_subset_1(B_72, k1_zfmisc_1(A_71)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 5.74/2.19  tff(c_526, plain, (![C_73]: (k7_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')), '#skF_2', C_73)=k4_xboole_0('#skF_2', C_73))), inference(resolution, [status(thm)], [c_28, c_520])).
% 5.74/2.19  tff(c_26, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 5.74/2.19  tff(c_258, plain, (k5_setfam_1(u1_struct_0('#skF_1'), '#skF_3')=k3_tarski('#skF_3')), inference(resolution, [status(thm)], [c_26, c_251])).
% 5.74/2.19  tff(c_24, plain, (~r1_tarski(k7_subset_1(u1_struct_0('#skF_1'), k5_setfam_1(u1_struct_0('#skF_1'), '#skF_2'), k5_setfam_1(u1_struct_0('#skF_1'), '#skF_3')), k5_setfam_1(u1_struct_0('#skF_1'), k7_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')), '#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_74])).
% 5.74/2.19  tff(c_260, plain, (~r1_tarski(k7_subset_1(u1_struct_0('#skF_1'), k5_setfam_1(u1_struct_0('#skF_1'), '#skF_2'), k3_tarski('#skF_3')), k5_setfam_1(u1_struct_0('#skF_1'), k7_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')), '#skF_2', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_258, c_24])).
% 5.74/2.19  tff(c_387, plain, (~r1_tarski(k7_subset_1(u1_struct_0('#skF_1'), k3_tarski('#skF_2'), k3_tarski('#skF_3')), k5_setfam_1(u1_struct_0('#skF_1'), k7_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')), '#skF_2', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_259, c_260])).
% 5.74/2.19  tff(c_536, plain, (~r1_tarski(k7_subset_1(u1_struct_0('#skF_1'), k3_tarski('#skF_2'), k3_tarski('#skF_3')), k5_setfam_1(u1_struct_0('#skF_1'), k4_xboole_0('#skF_2', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_526, c_387])).
% 5.74/2.19  tff(c_771, plain, (~r1_tarski(k4_xboole_0(k3_tarski('#skF_2'), k3_tarski('#skF_3')), k5_setfam_1(u1_struct_0('#skF_1'), k4_xboole_0('#skF_2', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_631, c_536])).
% 5.74/2.19  tff(c_1071, plain, (~r1_tarski(k3_tarski('#skF_2'), k2_xboole_0(k3_tarski('#skF_3'), k5_setfam_1(u1_struct_0('#skF_1'), k4_xboole_0('#skF_2', '#skF_3'))))), inference(resolution, [status(thm)], [c_6, c_771])).
% 5.74/2.19  tff(c_4142, plain, (~r1_tarski(k3_tarski('#skF_2'), k2_xboole_0(k3_tarski('#skF_3'), k3_tarski(k4_xboole_0('#skF_2', '#skF_3')))) | ~r1_tarski('#skF_2', k2_xboole_0('#skF_3', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_4133, c_1071])).
% 5.74/2.19  tff(c_4159, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_119, c_218, c_4, c_14, c_4142])).
% 5.74/2.19  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.74/2.19  
% 5.74/2.19  Inference rules
% 5.74/2.19  ----------------------
% 5.74/2.19  #Ref     : 0
% 5.74/2.19  #Sup     : 1158
% 5.74/2.19  #Fact    : 0
% 5.74/2.19  #Define  : 0
% 5.74/2.19  #Split   : 0
% 5.74/2.19  #Chain   : 0
% 5.74/2.19  #Close   : 0
% 5.74/2.19  
% 5.74/2.19  Ordering : KBO
% 5.74/2.19  
% 5.74/2.19  Simplification rules
% 5.74/2.19  ----------------------
% 5.74/2.19  #Subsume      : 10
% 5.74/2.19  #Demod        : 472
% 5.74/2.19  #Tautology    : 361
% 5.74/2.19  #SimpNegUnit  : 0
% 5.74/2.19  #BackRed      : 3
% 5.74/2.19  
% 5.74/2.19  #Partial instantiations: 0
% 5.74/2.19  #Strategies tried      : 1
% 5.74/2.19  
% 5.74/2.19  Timing (in seconds)
% 5.74/2.19  ----------------------
% 5.74/2.20  Preprocessing        : 0.31
% 5.74/2.20  Parsing              : 0.16
% 5.74/2.20  CNF conversion       : 0.02
% 5.74/2.20  Main loop            : 1.11
% 5.74/2.20  Inferencing          : 0.25
% 5.74/2.20  Reduction            : 0.57
% 5.74/2.20  Demodulation         : 0.50
% 5.74/2.20  BG Simplification    : 0.04
% 5.74/2.20  Subsumption          : 0.17
% 5.74/2.20  Abstraction          : 0.05
% 5.74/2.20  MUC search           : 0.00
% 5.74/2.20  Cooper               : 0.00
% 5.74/2.20  Total                : 1.45
% 5.74/2.20  Index Insertion      : 0.00
% 5.74/2.20  Index Deletion       : 0.00
% 5.74/2.20  Index Matching       : 0.00
% 5.74/2.20  BG Taut test         : 0.00
%------------------------------------------------------------------------------
