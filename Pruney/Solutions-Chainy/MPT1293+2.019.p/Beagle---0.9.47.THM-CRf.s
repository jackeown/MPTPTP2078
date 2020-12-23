%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:22:37 EST 2020

% Result     : Theorem 11.10s
% Output     : CNFRefutation 11.10s
% Verified   : 
% Statistics : Number of formulae       :   73 ( 103 expanded)
%              Number of leaves         :   29 (  47 expanded)
%              Depth                    :   10
%              Number of atoms          :   88 ( 144 expanded)
%              Number of equality atoms :   25 (  40 expanded)
%              Maximal formula depth    :    9 (   4 average)
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

tff(f_45,axiom,(
    ! [A,B] : k3_tarski(k2_xboole_0(A,B)) = k2_xboole_0(k3_tarski(A),k3_tarski(B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t96_zfmisc_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_37,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k2_xboole_0(B,C))
     => r1_tarski(k4_xboole_0(A,B),C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_xboole_1)).

tff(f_80,negated_conjecture,(
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
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_47,axiom,(
    ! [A] : k3_tarski(k1_zfmisc_1(A)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t99_zfmisc_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => r1_tarski(k3_tarski(A),k3_tarski(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_zfmisc_1)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

tff(f_69,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
         => ! [C] :
              ( r1_tarski(C,B)
             => m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_tops_2)).

tff(f_55,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => k5_setfam_1(A,B) = k3_tarski(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k5_setfam_1)).

tff(c_220,plain,(
    ! [A_66,B_67] : k2_xboole_0(k3_tarski(A_66),k3_tarski(B_67)) = k3_tarski(k2_xboole_0(A_66,B_67)) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_48,plain,(
    ! [B_42,A_43] : k2_xboole_0(B_42,A_43) = k2_xboole_0(A_43,B_42) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_10,plain,(
    ! [A_10,B_11] : r1_tarski(A_10,k2_xboole_0(A_10,B_11)) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_63,plain,(
    ! [A_43,B_42] : r1_tarski(A_43,k2_xboole_0(B_42,A_43)) ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_10])).

tff(c_232,plain,(
    ! [B_67,A_66] : r1_tarski(k3_tarski(B_67),k3_tarski(k2_xboole_0(A_66,B_67))) ),
    inference(superposition,[status(thm),theory(equality)],[c_220,c_63])).

tff(c_6,plain,(
    ! [A_5,B_6] : k2_xboole_0(A_5,k4_xboole_0(B_6,A_5)) = k2_xboole_0(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_377,plain,(
    ! [B_81,A_82] : k2_xboole_0(k3_tarski(B_81),k3_tarski(A_82)) = k3_tarski(k2_xboole_0(A_82,B_81)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_220])).

tff(c_16,plain,(
    ! [A_16,B_17] : k2_xboole_0(k3_tarski(A_16),k3_tarski(B_17)) = k3_tarski(k2_xboole_0(A_16,B_17)) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_389,plain,(
    ! [B_81,A_82] : k3_tarski(k2_xboole_0(B_81,A_82)) = k3_tarski(k2_xboole_0(A_82,B_81)) ),
    inference(superposition,[status(thm),theory(equality)],[c_377,c_16])).

tff(c_256,plain,(
    ! [B_67,A_66] : k2_xboole_0(k3_tarski(B_67),k3_tarski(A_66)) = k3_tarski(k2_xboole_0(A_66,B_67)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_220])).

tff(c_8,plain,(
    ! [A_7,B_8,C_9] :
      ( r1_tarski(k4_xboole_0(A_7,B_8),C_9)
      | ~ r1_tarski(A_7,k2_xboole_0(B_8,C_9)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_34,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_98,plain,(
    ! [A_48,B_49] :
      ( r1_tarski(A_48,B_49)
      | ~ m1_subset_1(A_48,k1_zfmisc_1(B_49)) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_109,plain,(
    r1_tarski('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_34,c_98])).

tff(c_18,plain,(
    ! [A_18] : k3_tarski(k1_zfmisc_1(A_18)) = A_18 ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_159,plain,(
    ! [A_58,B_59] :
      ( r1_tarski(k3_tarski(A_58),k3_tarski(B_59))
      | ~ r1_tarski(A_58,B_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_171,plain,(
    ! [A_58,A_18] :
      ( r1_tarski(k3_tarski(A_58),A_18)
      | ~ r1_tarski(A_58,k1_zfmisc_1(A_18)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_159])).

tff(c_26,plain,(
    ! [A_24,B_25] :
      ( m1_subset_1(A_24,k1_zfmisc_1(B_25))
      | ~ r1_tarski(A_24,B_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_735,plain,(
    ! [A_91,B_92,C_93] :
      ( k7_subset_1(A_91,B_92,C_93) = k4_xboole_0(B_92,C_93)
      | ~ m1_subset_1(B_92,k1_zfmisc_1(A_91)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_1198,plain,(
    ! [B_112,A_113,C_114] :
      ( k7_subset_1(B_112,A_113,C_114) = k4_xboole_0(A_113,C_114)
      | ~ r1_tarski(A_113,B_112) ) ),
    inference(resolution,[status(thm)],[c_26,c_735])).

tff(c_17125,plain,(
    ! [A_426,A_427,C_428] :
      ( k7_subset_1(A_426,k3_tarski(A_427),C_428) = k4_xboole_0(k3_tarski(A_427),C_428)
      | ~ r1_tarski(A_427,k1_zfmisc_1(A_426)) ) ),
    inference(resolution,[status(thm)],[c_171,c_1198])).

tff(c_17151,plain,(
    ! [C_428] : k7_subset_1(u1_struct_0('#skF_1'),k3_tarski('#skF_2'),C_428) = k4_xboole_0(k3_tarski('#skF_2'),C_428) ),
    inference(resolution,[status(thm)],[c_109,c_17125])).

tff(c_36,plain,(
    l1_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_1022,plain,(
    ! [C_102,A_103,B_104] :
      ( m1_subset_1(C_102,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_103))))
      | ~ r1_tarski(C_102,B_104)
      | ~ m1_subset_1(B_104,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_103))))
      | ~ l1_struct_0(A_103) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_3061,plain,(
    ! [A_189,B_190,A_191,C_192] :
      ( m1_subset_1(k4_xboole_0(A_189,B_190),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_191))))
      | ~ m1_subset_1(C_192,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_191))))
      | ~ l1_struct_0(A_191)
      | ~ r1_tarski(A_189,k2_xboole_0(B_190,C_192)) ) ),
    inference(resolution,[status(thm)],[c_8,c_1022])).

tff(c_3068,plain,(
    ! [A_189,B_190] :
      ( m1_subset_1(k4_xboole_0(A_189,B_190),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))
      | ~ l1_struct_0('#skF_1')
      | ~ r1_tarski(A_189,k2_xboole_0(B_190,'#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_34,c_3061])).

tff(c_3082,plain,(
    ! [A_193,B_194] :
      ( m1_subset_1(k4_xboole_0(A_193,B_194),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))
      | ~ r1_tarski(A_193,k2_xboole_0(B_194,'#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_3068])).

tff(c_22,plain,(
    ! [A_22,B_23] :
      ( k5_setfam_1(A_22,B_23) = k3_tarski(B_23)
      | ~ m1_subset_1(B_23,k1_zfmisc_1(k1_zfmisc_1(A_22))) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_5441,plain,(
    ! [A_261,B_262] :
      ( k5_setfam_1(u1_struct_0('#skF_1'),k4_xboole_0(A_261,B_262)) = k3_tarski(k4_xboole_0(A_261,B_262))
      | ~ r1_tarski(A_261,k2_xboole_0(B_262,'#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_3082,c_22])).

tff(c_743,plain,(
    ! [C_93] : k7_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')),'#skF_2',C_93) = k4_xboole_0('#skF_2',C_93) ),
    inference(resolution,[status(thm)],[c_34,c_735])).

tff(c_32,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_446,plain,(
    ! [A_83,B_84] :
      ( k5_setfam_1(A_83,B_84) = k3_tarski(B_84)
      | ~ m1_subset_1(B_84,k1_zfmisc_1(k1_zfmisc_1(A_83))) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_459,plain,(
    k5_setfam_1(u1_struct_0('#skF_1'),'#skF_3') = k3_tarski('#skF_3') ),
    inference(resolution,[status(thm)],[c_32,c_446])).

tff(c_458,plain,(
    k5_setfam_1(u1_struct_0('#skF_1'),'#skF_2') = k3_tarski('#skF_2') ),
    inference(resolution,[status(thm)],[c_34,c_446])).

tff(c_30,plain,(
    ~ r1_tarski(k7_subset_1(u1_struct_0('#skF_1'),k5_setfam_1(u1_struct_0('#skF_1'),'#skF_2'),k5_setfam_1(u1_struct_0('#skF_1'),'#skF_3')),k5_setfam_1(u1_struct_0('#skF_1'),k7_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')),'#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_460,plain,(
    ~ r1_tarski(k7_subset_1(u1_struct_0('#skF_1'),k3_tarski('#skF_2'),k5_setfam_1(u1_struct_0('#skF_1'),'#skF_3')),k5_setfam_1(u1_struct_0('#skF_1'),k7_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')),'#skF_2','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_458,c_30])).

tff(c_628,plain,(
    ~ r1_tarski(k7_subset_1(u1_struct_0('#skF_1'),k3_tarski('#skF_2'),k3_tarski('#skF_3')),k5_setfam_1(u1_struct_0('#skF_1'),k7_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')),'#skF_2','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_459,c_460])).

tff(c_746,plain,(
    ~ r1_tarski(k7_subset_1(u1_struct_0('#skF_1'),k3_tarski('#skF_2'),k3_tarski('#skF_3')),k5_setfam_1(u1_struct_0('#skF_1'),k4_xboole_0('#skF_2','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_743,c_628])).

tff(c_5454,plain,
    ( ~ r1_tarski(k7_subset_1(u1_struct_0('#skF_1'),k3_tarski('#skF_2'),k3_tarski('#skF_3')),k3_tarski(k4_xboole_0('#skF_2','#skF_3')))
    | ~ r1_tarski('#skF_2',k2_xboole_0('#skF_3','#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_5441,c_746])).

tff(c_5469,plain,(
    ~ r1_tarski(k7_subset_1(u1_struct_0('#skF_1'),k3_tarski('#skF_2'),k3_tarski('#skF_3')),k3_tarski(k4_xboole_0('#skF_2','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_63,c_5454])).

tff(c_17162,plain,(
    ~ r1_tarski(k4_xboole_0(k3_tarski('#skF_2'),k3_tarski('#skF_3')),k3_tarski(k4_xboole_0('#skF_2','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_17151,c_5469])).

tff(c_17175,plain,(
    ~ r1_tarski(k3_tarski('#skF_2'),k2_xboole_0(k3_tarski('#skF_3'),k3_tarski(k4_xboole_0('#skF_2','#skF_3')))) ),
    inference(resolution,[status(thm)],[c_8,c_17162])).

tff(c_17179,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_232,c_6,c_389,c_256,c_17175])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n010.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 11:31:29 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 11.10/4.36  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.10/4.37  
% 11.10/4.37  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.10/4.37  %$ r1_tarski > m1_subset_1 > l1_struct_0 > k7_subset_1 > k5_setfam_1 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > u1_struct_0 > k3_tarski > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1
% 11.10/4.37  
% 11.10/4.37  %Foreground sorts:
% 11.10/4.37  
% 11.10/4.37  
% 11.10/4.37  %Background operators:
% 11.10/4.37  
% 11.10/4.37  
% 11.10/4.37  %Foreground operators:
% 11.10/4.37  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 11.10/4.37  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 11.10/4.37  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 11.10/4.37  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 11.10/4.37  tff('#skF_2', type, '#skF_2': $i).
% 11.10/4.37  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 11.10/4.37  tff('#skF_3', type, '#skF_3': $i).
% 11.10/4.37  tff('#skF_1', type, '#skF_1': $i).
% 11.10/4.37  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 11.10/4.37  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 11.10/4.37  tff(k5_setfam_1, type, k5_setfam_1: ($i * $i) > $i).
% 11.10/4.37  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 11.10/4.37  tff(k3_tarski, type, k3_tarski: $i > $i).
% 11.10/4.37  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 11.10/4.37  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 11.10/4.37  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 11.10/4.37  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 11.10/4.37  
% 11.10/4.38  tff(f_45, axiom, (![A, B]: (k3_tarski(k2_xboole_0(A, B)) = k2_xboole_0(k3_tarski(A), k3_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t96_zfmisc_1)).
% 11.10/4.38  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 11.10/4.38  tff(f_37, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 11.10/4.38  tff(f_31, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 11.10/4.38  tff(f_35, axiom, (![A, B, C]: (r1_tarski(A, k2_xboole_0(B, C)) => r1_tarski(k4_xboole_0(A, B), C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_xboole_1)).
% 11.10/4.38  tff(f_80, negated_conjecture, ~(![A]: (l1_struct_0(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => r1_tarski(k7_subset_1(u1_struct_0(A), k5_setfam_1(u1_struct_0(A), B), k5_setfam_1(u1_struct_0(A), C)), k5_setfam_1(u1_struct_0(A), k7_subset_1(k1_zfmisc_1(u1_struct_0(A)), B, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_tops_2)).
% 11.10/4.38  tff(f_59, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 11.10/4.38  tff(f_47, axiom, (![A]: (k3_tarski(k1_zfmisc_1(A)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t99_zfmisc_1)).
% 11.10/4.38  tff(f_43, axiom, (![A, B]: (r1_tarski(A, B) => r1_tarski(k3_tarski(A), k3_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t95_zfmisc_1)).
% 11.10/4.38  tff(f_51, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 11.10/4.38  tff(f_69, axiom, (![A]: (l1_struct_0(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => (![C]: (r1_tarski(C, B) => m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_tops_2)).
% 11.10/4.38  tff(f_55, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (k5_setfam_1(A, B) = k3_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k5_setfam_1)).
% 11.10/4.38  tff(c_220, plain, (![A_66, B_67]: (k2_xboole_0(k3_tarski(A_66), k3_tarski(B_67))=k3_tarski(k2_xboole_0(A_66, B_67)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 11.10/4.38  tff(c_48, plain, (![B_42, A_43]: (k2_xboole_0(B_42, A_43)=k2_xboole_0(A_43, B_42))), inference(cnfTransformation, [status(thm)], [f_27])).
% 11.10/4.38  tff(c_10, plain, (![A_10, B_11]: (r1_tarski(A_10, k2_xboole_0(A_10, B_11)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 11.10/4.38  tff(c_63, plain, (![A_43, B_42]: (r1_tarski(A_43, k2_xboole_0(B_42, A_43)))), inference(superposition, [status(thm), theory('equality')], [c_48, c_10])).
% 11.10/4.38  tff(c_232, plain, (![B_67, A_66]: (r1_tarski(k3_tarski(B_67), k3_tarski(k2_xboole_0(A_66, B_67))))), inference(superposition, [status(thm), theory('equality')], [c_220, c_63])).
% 11.10/4.38  tff(c_6, plain, (![A_5, B_6]: (k2_xboole_0(A_5, k4_xboole_0(B_6, A_5))=k2_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_31])).
% 11.10/4.38  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 11.10/4.38  tff(c_377, plain, (![B_81, A_82]: (k2_xboole_0(k3_tarski(B_81), k3_tarski(A_82))=k3_tarski(k2_xboole_0(A_82, B_81)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_220])).
% 11.10/4.38  tff(c_16, plain, (![A_16, B_17]: (k2_xboole_0(k3_tarski(A_16), k3_tarski(B_17))=k3_tarski(k2_xboole_0(A_16, B_17)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 11.10/4.38  tff(c_389, plain, (![B_81, A_82]: (k3_tarski(k2_xboole_0(B_81, A_82))=k3_tarski(k2_xboole_0(A_82, B_81)))), inference(superposition, [status(thm), theory('equality')], [c_377, c_16])).
% 11.10/4.38  tff(c_256, plain, (![B_67, A_66]: (k2_xboole_0(k3_tarski(B_67), k3_tarski(A_66))=k3_tarski(k2_xboole_0(A_66, B_67)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_220])).
% 11.10/4.38  tff(c_8, plain, (![A_7, B_8, C_9]: (r1_tarski(k4_xboole_0(A_7, B_8), C_9) | ~r1_tarski(A_7, k2_xboole_0(B_8, C_9)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 11.10/4.38  tff(c_34, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(cnfTransformation, [status(thm)], [f_80])).
% 11.10/4.38  tff(c_98, plain, (![A_48, B_49]: (r1_tarski(A_48, B_49) | ~m1_subset_1(A_48, k1_zfmisc_1(B_49)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 11.10/4.38  tff(c_109, plain, (r1_tarski('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_34, c_98])).
% 11.10/4.38  tff(c_18, plain, (![A_18]: (k3_tarski(k1_zfmisc_1(A_18))=A_18)), inference(cnfTransformation, [status(thm)], [f_47])).
% 11.10/4.38  tff(c_159, plain, (![A_58, B_59]: (r1_tarski(k3_tarski(A_58), k3_tarski(B_59)) | ~r1_tarski(A_58, B_59))), inference(cnfTransformation, [status(thm)], [f_43])).
% 11.10/4.38  tff(c_171, plain, (![A_58, A_18]: (r1_tarski(k3_tarski(A_58), A_18) | ~r1_tarski(A_58, k1_zfmisc_1(A_18)))), inference(superposition, [status(thm), theory('equality')], [c_18, c_159])).
% 11.10/4.38  tff(c_26, plain, (![A_24, B_25]: (m1_subset_1(A_24, k1_zfmisc_1(B_25)) | ~r1_tarski(A_24, B_25))), inference(cnfTransformation, [status(thm)], [f_59])).
% 11.10/4.38  tff(c_735, plain, (![A_91, B_92, C_93]: (k7_subset_1(A_91, B_92, C_93)=k4_xboole_0(B_92, C_93) | ~m1_subset_1(B_92, k1_zfmisc_1(A_91)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 11.10/4.38  tff(c_1198, plain, (![B_112, A_113, C_114]: (k7_subset_1(B_112, A_113, C_114)=k4_xboole_0(A_113, C_114) | ~r1_tarski(A_113, B_112))), inference(resolution, [status(thm)], [c_26, c_735])).
% 11.10/4.38  tff(c_17125, plain, (![A_426, A_427, C_428]: (k7_subset_1(A_426, k3_tarski(A_427), C_428)=k4_xboole_0(k3_tarski(A_427), C_428) | ~r1_tarski(A_427, k1_zfmisc_1(A_426)))), inference(resolution, [status(thm)], [c_171, c_1198])).
% 11.10/4.38  tff(c_17151, plain, (![C_428]: (k7_subset_1(u1_struct_0('#skF_1'), k3_tarski('#skF_2'), C_428)=k4_xboole_0(k3_tarski('#skF_2'), C_428))), inference(resolution, [status(thm)], [c_109, c_17125])).
% 11.10/4.38  tff(c_36, plain, (l1_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_80])).
% 11.10/4.38  tff(c_1022, plain, (![C_102, A_103, B_104]: (m1_subset_1(C_102, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_103)))) | ~r1_tarski(C_102, B_104) | ~m1_subset_1(B_104, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_103)))) | ~l1_struct_0(A_103))), inference(cnfTransformation, [status(thm)], [f_69])).
% 11.10/4.38  tff(c_3061, plain, (![A_189, B_190, A_191, C_192]: (m1_subset_1(k4_xboole_0(A_189, B_190), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_191)))) | ~m1_subset_1(C_192, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_191)))) | ~l1_struct_0(A_191) | ~r1_tarski(A_189, k2_xboole_0(B_190, C_192)))), inference(resolution, [status(thm)], [c_8, c_1022])).
% 11.10/4.38  tff(c_3068, plain, (![A_189, B_190]: (m1_subset_1(k4_xboole_0(A_189, B_190), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) | ~l1_struct_0('#skF_1') | ~r1_tarski(A_189, k2_xboole_0(B_190, '#skF_2')))), inference(resolution, [status(thm)], [c_34, c_3061])).
% 11.10/4.38  tff(c_3082, plain, (![A_193, B_194]: (m1_subset_1(k4_xboole_0(A_193, B_194), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) | ~r1_tarski(A_193, k2_xboole_0(B_194, '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_3068])).
% 11.10/4.38  tff(c_22, plain, (![A_22, B_23]: (k5_setfam_1(A_22, B_23)=k3_tarski(B_23) | ~m1_subset_1(B_23, k1_zfmisc_1(k1_zfmisc_1(A_22))))), inference(cnfTransformation, [status(thm)], [f_55])).
% 11.10/4.38  tff(c_5441, plain, (![A_261, B_262]: (k5_setfam_1(u1_struct_0('#skF_1'), k4_xboole_0(A_261, B_262))=k3_tarski(k4_xboole_0(A_261, B_262)) | ~r1_tarski(A_261, k2_xboole_0(B_262, '#skF_2')))), inference(resolution, [status(thm)], [c_3082, c_22])).
% 11.10/4.38  tff(c_743, plain, (![C_93]: (k7_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')), '#skF_2', C_93)=k4_xboole_0('#skF_2', C_93))), inference(resolution, [status(thm)], [c_34, c_735])).
% 11.10/4.38  tff(c_32, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(cnfTransformation, [status(thm)], [f_80])).
% 11.10/4.38  tff(c_446, plain, (![A_83, B_84]: (k5_setfam_1(A_83, B_84)=k3_tarski(B_84) | ~m1_subset_1(B_84, k1_zfmisc_1(k1_zfmisc_1(A_83))))), inference(cnfTransformation, [status(thm)], [f_55])).
% 11.10/4.38  tff(c_459, plain, (k5_setfam_1(u1_struct_0('#skF_1'), '#skF_3')=k3_tarski('#skF_3')), inference(resolution, [status(thm)], [c_32, c_446])).
% 11.10/4.38  tff(c_458, plain, (k5_setfam_1(u1_struct_0('#skF_1'), '#skF_2')=k3_tarski('#skF_2')), inference(resolution, [status(thm)], [c_34, c_446])).
% 11.10/4.38  tff(c_30, plain, (~r1_tarski(k7_subset_1(u1_struct_0('#skF_1'), k5_setfam_1(u1_struct_0('#skF_1'), '#skF_2'), k5_setfam_1(u1_struct_0('#skF_1'), '#skF_3')), k5_setfam_1(u1_struct_0('#skF_1'), k7_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')), '#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_80])).
% 11.10/4.38  tff(c_460, plain, (~r1_tarski(k7_subset_1(u1_struct_0('#skF_1'), k3_tarski('#skF_2'), k5_setfam_1(u1_struct_0('#skF_1'), '#skF_3')), k5_setfam_1(u1_struct_0('#skF_1'), k7_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')), '#skF_2', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_458, c_30])).
% 11.10/4.38  tff(c_628, plain, (~r1_tarski(k7_subset_1(u1_struct_0('#skF_1'), k3_tarski('#skF_2'), k3_tarski('#skF_3')), k5_setfam_1(u1_struct_0('#skF_1'), k7_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')), '#skF_2', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_459, c_460])).
% 11.10/4.38  tff(c_746, plain, (~r1_tarski(k7_subset_1(u1_struct_0('#skF_1'), k3_tarski('#skF_2'), k3_tarski('#skF_3')), k5_setfam_1(u1_struct_0('#skF_1'), k4_xboole_0('#skF_2', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_743, c_628])).
% 11.10/4.38  tff(c_5454, plain, (~r1_tarski(k7_subset_1(u1_struct_0('#skF_1'), k3_tarski('#skF_2'), k3_tarski('#skF_3')), k3_tarski(k4_xboole_0('#skF_2', '#skF_3'))) | ~r1_tarski('#skF_2', k2_xboole_0('#skF_3', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_5441, c_746])).
% 11.10/4.38  tff(c_5469, plain, (~r1_tarski(k7_subset_1(u1_struct_0('#skF_1'), k3_tarski('#skF_2'), k3_tarski('#skF_3')), k3_tarski(k4_xboole_0('#skF_2', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_63, c_5454])).
% 11.10/4.38  tff(c_17162, plain, (~r1_tarski(k4_xboole_0(k3_tarski('#skF_2'), k3_tarski('#skF_3')), k3_tarski(k4_xboole_0('#skF_2', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_17151, c_5469])).
% 11.10/4.38  tff(c_17175, plain, (~r1_tarski(k3_tarski('#skF_2'), k2_xboole_0(k3_tarski('#skF_3'), k3_tarski(k4_xboole_0('#skF_2', '#skF_3'))))), inference(resolution, [status(thm)], [c_8, c_17162])).
% 11.10/4.38  tff(c_17179, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_232, c_6, c_389, c_256, c_17175])).
% 11.10/4.38  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.10/4.38  
% 11.10/4.38  Inference rules
% 11.10/4.38  ----------------------
% 11.10/4.38  #Ref     : 0
% 11.10/4.38  #Sup     : 4801
% 11.10/4.38  #Fact    : 0
% 11.10/4.38  #Define  : 0
% 11.10/4.38  #Split   : 2
% 11.10/4.38  #Chain   : 0
% 11.10/4.38  #Close   : 0
% 11.10/4.38  
% 11.10/4.38  Ordering : KBO
% 11.10/4.38  
% 11.10/4.38  Simplification rules
% 11.10/4.38  ----------------------
% 11.10/4.38  #Subsume      : 161
% 11.10/4.38  #Demod        : 2101
% 11.10/4.38  #Tautology    : 1256
% 11.10/4.38  #SimpNegUnit  : 0
% 11.10/4.38  #BackRed      : 6
% 11.10/4.38  
% 11.10/4.38  #Partial instantiations: 0
% 11.10/4.38  #Strategies tried      : 1
% 11.10/4.38  
% 11.10/4.38  Timing (in seconds)
% 11.10/4.38  ----------------------
% 11.10/4.39  Preprocessing        : 0.32
% 11.10/4.39  Parsing              : 0.17
% 11.10/4.39  CNF conversion       : 0.02
% 11.10/4.39  Main loop            : 3.28
% 11.10/4.39  Inferencing          : 0.58
% 11.10/4.39  Reduction            : 1.83
% 11.10/4.39  Demodulation         : 1.64
% 11.10/4.39  BG Simplification    : 0.10
% 11.10/4.39  Subsumption          : 0.61
% 11.10/4.39  Abstraction          : 0.11
% 11.10/4.39  MUC search           : 0.00
% 11.10/4.39  Cooper               : 0.00
% 11.10/4.39  Total                : 3.63
% 11.10/4.39  Index Insertion      : 0.00
% 11.10/4.39  Index Deletion       : 0.00
% 11.10/4.39  Index Matching       : 0.00
% 11.10/4.39  BG Taut test         : 0.00
%------------------------------------------------------------------------------
