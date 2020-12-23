%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:20:38 EST 2020

% Result     : Theorem 12.81s
% Output     : CNFRefutation 12.81s
% Verified   : 
% Statistics : Number of formulae       :   52 ( 147 expanded)
%              Number of leaves         :   22 (  63 expanded)
%              Depth                    :   11
%              Number of atoms          :   84 ( 311 expanded)
%              Number of equality atoms :   10 (  42 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > m1_subset_1 > l1_pre_topc > k4_subset_1 > k2_xboole_0 > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k4_subset_1,type,(
    k4_subset_1: ( $i * $i * $i ) > $i )).

tff(k1_tops_1,type,(
    k1_tops_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_76,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => r1_tarski(k4_subset_1(u1_struct_0(A),k1_tops_1(A,B),k1_tops_1(A,C)),k1_tops_1(A,k4_subset_1(u1_struct_0(A),B,C))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_tops_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_47,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => m1_subset_1(k4_subset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_subset_1)).

tff(f_29,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_65,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( r1_tarski(B,C)
               => r1_tarski(k1_tops_1(A,B),k1_tops_1(A,C)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_tops_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(C,B) )
     => r1_tarski(k2_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_xboole_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k1_tops_1(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_tops_1)).

tff(c_22,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_20,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_18,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_81,plain,(
    ! [A_38,B_39,C_40] :
      ( k4_subset_1(A_38,B_39,C_40) = k2_xboole_0(B_39,C_40)
      | ~ m1_subset_1(C_40,k1_zfmisc_1(A_38))
      | ~ m1_subset_1(B_39,k1_zfmisc_1(A_38)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_91,plain,(
    ! [B_41] :
      ( k4_subset_1(u1_struct_0('#skF_1'),B_41,'#skF_3') = k2_xboole_0(B_41,'#skF_3')
      | ~ m1_subset_1(B_41,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(resolution,[status(thm)],[c_18,c_81])).

tff(c_101,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_2','#skF_3') = k2_xboole_0('#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_20,c_91])).

tff(c_107,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_2','#skF_3') = k2_xboole_0('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_101])).

tff(c_131,plain,(
    ! [A_43,B_44,C_45] :
      ( m1_subset_1(k4_subset_1(A_43,B_44,C_45),k1_zfmisc_1(A_43))
      | ~ m1_subset_1(C_45,k1_zfmisc_1(A_43))
      | ~ m1_subset_1(B_44,k1_zfmisc_1(A_43)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_144,plain,
    ( m1_subset_1(k2_xboole_0('#skF_3','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_107,c_131])).

tff(c_154,plain,(
    m1_subset_1(k2_xboole_0('#skF_3','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_18,c_144])).

tff(c_24,plain,(
    ! [B_29,A_30] : k2_xboole_0(B_29,A_30) = k2_xboole_0(A_30,B_29) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_4,plain,(
    ! [A_3,B_4] : r1_tarski(A_3,k2_xboole_0(A_3,B_4)) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_39,plain,(
    ! [A_30,B_29] : r1_tarski(A_30,k2_xboole_0(B_29,A_30)) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_4])).

tff(c_14,plain,(
    ! [A_16,B_20,C_22] :
      ( r1_tarski(k1_tops_1(A_16,B_20),k1_tops_1(A_16,C_22))
      | ~ r1_tarski(B_20,C_22)
      | ~ m1_subset_1(C_22,k1_zfmisc_1(u1_struct_0(A_16)))
      | ~ m1_subset_1(B_20,k1_zfmisc_1(u1_struct_0(A_16)))
      | ~ l1_pre_topc(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_6,plain,(
    ! [A_5,C_7,B_6] :
      ( r1_tarski(k2_xboole_0(A_5,C_7),B_6)
      | ~ r1_tarski(C_7,B_6)
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_12,plain,(
    ! [A_14,B_15] :
      ( m1_subset_1(k1_tops_1(A_14,B_15),k1_zfmisc_1(u1_struct_0(A_14)))
      | ~ m1_subset_1(B_15,k1_zfmisc_1(u1_struct_0(A_14)))
      | ~ l1_pre_topc(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_345,plain,(
    ! [A_49,B_50,B_51] :
      ( k4_subset_1(u1_struct_0(A_49),B_50,k1_tops_1(A_49,B_51)) = k2_xboole_0(B_50,k1_tops_1(A_49,B_51))
      | ~ m1_subset_1(B_50,k1_zfmisc_1(u1_struct_0(A_49)))
      | ~ m1_subset_1(B_51,k1_zfmisc_1(u1_struct_0(A_49)))
      | ~ l1_pre_topc(A_49) ) ),
    inference(resolution,[status(thm)],[c_12,c_81])).

tff(c_2657,plain,(
    ! [A_68,B_69,B_70] :
      ( k4_subset_1(u1_struct_0(A_68),k1_tops_1(A_68,B_69),k1_tops_1(A_68,B_70)) = k2_xboole_0(k1_tops_1(A_68,B_69),k1_tops_1(A_68,B_70))
      | ~ m1_subset_1(B_70,k1_zfmisc_1(u1_struct_0(A_68)))
      | ~ m1_subset_1(B_69,k1_zfmisc_1(u1_struct_0(A_68)))
      | ~ l1_pre_topc(A_68) ) ),
    inference(resolution,[status(thm)],[c_12,c_345])).

tff(c_16,plain,(
    ~ r1_tarski(k4_subset_1(u1_struct_0('#skF_1'),k1_tops_1('#skF_1','#skF_2'),k1_tops_1('#skF_1','#skF_3')),k1_tops_1('#skF_1',k4_subset_1(u1_struct_0('#skF_1'),'#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_110,plain,(
    ~ r1_tarski(k4_subset_1(u1_struct_0('#skF_1'),k1_tops_1('#skF_1','#skF_2'),k1_tops_1('#skF_1','#skF_3')),k1_tops_1('#skF_1',k2_xboole_0('#skF_3','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_107,c_16])).

tff(c_2679,plain,
    ( ~ r1_tarski(k2_xboole_0(k1_tops_1('#skF_1','#skF_2'),k1_tops_1('#skF_1','#skF_3')),k1_tops_1('#skF_1',k2_xboole_0('#skF_3','#skF_2')))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_2657,c_110])).

tff(c_2696,plain,(
    ~ r1_tarski(k2_xboole_0(k1_tops_1('#skF_1','#skF_3'),k1_tops_1('#skF_1','#skF_2')),k1_tops_1('#skF_1',k2_xboole_0('#skF_3','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_20,c_18,c_2,c_2679])).

tff(c_2738,plain,
    ( ~ r1_tarski(k1_tops_1('#skF_1','#skF_2'),k1_tops_1('#skF_1',k2_xboole_0('#skF_3','#skF_2')))
    | ~ r1_tarski(k1_tops_1('#skF_1','#skF_3'),k1_tops_1('#skF_1',k2_xboole_0('#skF_3','#skF_2'))) ),
    inference(resolution,[status(thm)],[c_6,c_2696])).

tff(c_14048,plain,(
    ~ r1_tarski(k1_tops_1('#skF_1','#skF_3'),k1_tops_1('#skF_1',k2_xboole_0('#skF_3','#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_2738])).

tff(c_14051,plain,
    ( ~ r1_tarski('#skF_3',k2_xboole_0('#skF_3','#skF_2'))
    | ~ m1_subset_1(k2_xboole_0('#skF_3','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_14,c_14048])).

tff(c_14055,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_18,c_154,c_4,c_14051])).

tff(c_14056,plain,(
    ~ r1_tarski(k1_tops_1('#skF_1','#skF_2'),k1_tops_1('#skF_1',k2_xboole_0('#skF_3','#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_2738])).

tff(c_14060,plain,
    ( ~ r1_tarski('#skF_2',k2_xboole_0('#skF_3','#skF_2'))
    | ~ m1_subset_1(k2_xboole_0('#skF_3','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_14,c_14056])).

tff(c_14064,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_20,c_154,c_39,c_14060])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n003.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 15:19:42 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 12.81/4.75  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 12.81/4.75  
% 12.81/4.75  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 12.81/4.75  %$ r1_tarski > m1_subset_1 > l1_pre_topc > k4_subset_1 > k2_xboole_0 > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1
% 12.81/4.75  
% 12.81/4.75  %Foreground sorts:
% 12.81/4.75  
% 12.81/4.75  
% 12.81/4.75  %Background operators:
% 12.81/4.75  
% 12.81/4.75  
% 12.81/4.75  %Foreground operators:
% 12.81/4.75  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 12.81/4.75  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 12.81/4.75  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 12.81/4.75  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 12.81/4.75  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 12.81/4.75  tff('#skF_2', type, '#skF_2': $i).
% 12.81/4.75  tff('#skF_3', type, '#skF_3': $i).
% 12.81/4.75  tff('#skF_1', type, '#skF_1': $i).
% 12.81/4.75  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 12.81/4.75  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 12.81/4.75  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 12.81/4.75  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 12.81/4.75  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 12.81/4.75  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 12.81/4.75  
% 12.81/4.77  tff(f_76, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => r1_tarski(k4_subset_1(u1_struct_0(A), k1_tops_1(A, B), k1_tops_1(A, C)), k1_tops_1(A, k4_subset_1(u1_struct_0(A), B, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_tops_1)).
% 12.81/4.77  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 12.81/4.77  tff(f_47, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 12.81/4.77  tff(f_41, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => m1_subset_1(k4_subset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k4_subset_1)).
% 12.81/4.77  tff(f_29, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 12.81/4.77  tff(f_65, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (r1_tarski(B, C) => r1_tarski(k1_tops_1(A, B), k1_tops_1(A, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_tops_1)).
% 12.81/4.77  tff(f_35, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(C, B)) => r1_tarski(k2_xboole_0(A, C), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_xboole_1)).
% 12.81/4.77  tff(f_53, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k1_tops_1(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_tops_1)).
% 12.81/4.77  tff(c_22, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_76])).
% 12.81/4.77  tff(c_20, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_76])).
% 12.81/4.77  tff(c_18, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_76])).
% 12.81/4.77  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 12.81/4.77  tff(c_81, plain, (![A_38, B_39, C_40]: (k4_subset_1(A_38, B_39, C_40)=k2_xboole_0(B_39, C_40) | ~m1_subset_1(C_40, k1_zfmisc_1(A_38)) | ~m1_subset_1(B_39, k1_zfmisc_1(A_38)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 12.81/4.77  tff(c_91, plain, (![B_41]: (k4_subset_1(u1_struct_0('#skF_1'), B_41, '#skF_3')=k2_xboole_0(B_41, '#skF_3') | ~m1_subset_1(B_41, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(resolution, [status(thm)], [c_18, c_81])).
% 12.81/4.77  tff(c_101, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', '#skF_3')=k2_xboole_0('#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_20, c_91])).
% 12.81/4.77  tff(c_107, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', '#skF_3')=k2_xboole_0('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_101])).
% 12.81/4.77  tff(c_131, plain, (![A_43, B_44, C_45]: (m1_subset_1(k4_subset_1(A_43, B_44, C_45), k1_zfmisc_1(A_43)) | ~m1_subset_1(C_45, k1_zfmisc_1(A_43)) | ~m1_subset_1(B_44, k1_zfmisc_1(A_43)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 12.81/4.77  tff(c_144, plain, (m1_subset_1(k2_xboole_0('#skF_3', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_107, c_131])).
% 12.81/4.77  tff(c_154, plain, (m1_subset_1(k2_xboole_0('#skF_3', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_18, c_144])).
% 12.81/4.77  tff(c_24, plain, (![B_29, A_30]: (k2_xboole_0(B_29, A_30)=k2_xboole_0(A_30, B_29))), inference(cnfTransformation, [status(thm)], [f_27])).
% 12.81/4.77  tff(c_4, plain, (![A_3, B_4]: (r1_tarski(A_3, k2_xboole_0(A_3, B_4)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 12.81/4.77  tff(c_39, plain, (![A_30, B_29]: (r1_tarski(A_30, k2_xboole_0(B_29, A_30)))), inference(superposition, [status(thm), theory('equality')], [c_24, c_4])).
% 12.81/4.77  tff(c_14, plain, (![A_16, B_20, C_22]: (r1_tarski(k1_tops_1(A_16, B_20), k1_tops_1(A_16, C_22)) | ~r1_tarski(B_20, C_22) | ~m1_subset_1(C_22, k1_zfmisc_1(u1_struct_0(A_16))) | ~m1_subset_1(B_20, k1_zfmisc_1(u1_struct_0(A_16))) | ~l1_pre_topc(A_16))), inference(cnfTransformation, [status(thm)], [f_65])).
% 12.81/4.77  tff(c_6, plain, (![A_5, C_7, B_6]: (r1_tarski(k2_xboole_0(A_5, C_7), B_6) | ~r1_tarski(C_7, B_6) | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_35])).
% 12.81/4.77  tff(c_12, plain, (![A_14, B_15]: (m1_subset_1(k1_tops_1(A_14, B_15), k1_zfmisc_1(u1_struct_0(A_14))) | ~m1_subset_1(B_15, k1_zfmisc_1(u1_struct_0(A_14))) | ~l1_pre_topc(A_14))), inference(cnfTransformation, [status(thm)], [f_53])).
% 12.81/4.77  tff(c_345, plain, (![A_49, B_50, B_51]: (k4_subset_1(u1_struct_0(A_49), B_50, k1_tops_1(A_49, B_51))=k2_xboole_0(B_50, k1_tops_1(A_49, B_51)) | ~m1_subset_1(B_50, k1_zfmisc_1(u1_struct_0(A_49))) | ~m1_subset_1(B_51, k1_zfmisc_1(u1_struct_0(A_49))) | ~l1_pre_topc(A_49))), inference(resolution, [status(thm)], [c_12, c_81])).
% 12.81/4.77  tff(c_2657, plain, (![A_68, B_69, B_70]: (k4_subset_1(u1_struct_0(A_68), k1_tops_1(A_68, B_69), k1_tops_1(A_68, B_70))=k2_xboole_0(k1_tops_1(A_68, B_69), k1_tops_1(A_68, B_70)) | ~m1_subset_1(B_70, k1_zfmisc_1(u1_struct_0(A_68))) | ~m1_subset_1(B_69, k1_zfmisc_1(u1_struct_0(A_68))) | ~l1_pre_topc(A_68))), inference(resolution, [status(thm)], [c_12, c_345])).
% 12.81/4.77  tff(c_16, plain, (~r1_tarski(k4_subset_1(u1_struct_0('#skF_1'), k1_tops_1('#skF_1', '#skF_2'), k1_tops_1('#skF_1', '#skF_3')), k1_tops_1('#skF_1', k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_76])).
% 12.81/4.77  tff(c_110, plain, (~r1_tarski(k4_subset_1(u1_struct_0('#skF_1'), k1_tops_1('#skF_1', '#skF_2'), k1_tops_1('#skF_1', '#skF_3')), k1_tops_1('#skF_1', k2_xboole_0('#skF_3', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_107, c_16])).
% 12.81/4.77  tff(c_2679, plain, (~r1_tarski(k2_xboole_0(k1_tops_1('#skF_1', '#skF_2'), k1_tops_1('#skF_1', '#skF_3')), k1_tops_1('#skF_1', k2_xboole_0('#skF_3', '#skF_2'))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_2657, c_110])).
% 12.81/4.77  tff(c_2696, plain, (~r1_tarski(k2_xboole_0(k1_tops_1('#skF_1', '#skF_3'), k1_tops_1('#skF_1', '#skF_2')), k1_tops_1('#skF_1', k2_xboole_0('#skF_3', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_20, c_18, c_2, c_2679])).
% 12.81/4.77  tff(c_2738, plain, (~r1_tarski(k1_tops_1('#skF_1', '#skF_2'), k1_tops_1('#skF_1', k2_xboole_0('#skF_3', '#skF_2'))) | ~r1_tarski(k1_tops_1('#skF_1', '#skF_3'), k1_tops_1('#skF_1', k2_xboole_0('#skF_3', '#skF_2')))), inference(resolution, [status(thm)], [c_6, c_2696])).
% 12.81/4.77  tff(c_14048, plain, (~r1_tarski(k1_tops_1('#skF_1', '#skF_3'), k1_tops_1('#skF_1', k2_xboole_0('#skF_3', '#skF_2')))), inference(splitLeft, [status(thm)], [c_2738])).
% 12.81/4.77  tff(c_14051, plain, (~r1_tarski('#skF_3', k2_xboole_0('#skF_3', '#skF_2')) | ~m1_subset_1(k2_xboole_0('#skF_3', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_14, c_14048])).
% 12.81/4.77  tff(c_14055, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_22, c_18, c_154, c_4, c_14051])).
% 12.81/4.77  tff(c_14056, plain, (~r1_tarski(k1_tops_1('#skF_1', '#skF_2'), k1_tops_1('#skF_1', k2_xboole_0('#skF_3', '#skF_2')))), inference(splitRight, [status(thm)], [c_2738])).
% 12.81/4.77  tff(c_14060, plain, (~r1_tarski('#skF_2', k2_xboole_0('#skF_3', '#skF_2')) | ~m1_subset_1(k2_xboole_0('#skF_3', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_14, c_14056])).
% 12.81/4.77  tff(c_14064, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_22, c_20, c_154, c_39, c_14060])).
% 12.81/4.77  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 12.81/4.77  
% 12.81/4.77  Inference rules
% 12.81/4.77  ----------------------
% 12.81/4.77  #Ref     : 0
% 12.81/4.77  #Sup     : 3025
% 12.81/4.77  #Fact    : 0
% 12.81/4.77  #Define  : 0
% 12.81/4.77  #Split   : 3
% 12.81/4.77  #Chain   : 0
% 12.81/4.77  #Close   : 0
% 12.81/4.77  
% 12.81/4.77  Ordering : KBO
% 12.81/4.77  
% 12.81/4.77  Simplification rules
% 12.81/4.77  ----------------------
% 12.81/4.77  #Subsume      : 24
% 12.81/4.77  #Demod        : 6222
% 12.81/4.77  #Tautology    : 423
% 12.81/4.77  #SimpNegUnit  : 0
% 12.81/4.77  #BackRed      : 2
% 12.81/4.77  
% 12.81/4.77  #Partial instantiations: 0
% 12.81/4.77  #Strategies tried      : 1
% 12.81/4.77  
% 12.81/4.77  Timing (in seconds)
% 12.81/4.77  ----------------------
% 12.91/4.77  Preprocessing        : 0.30
% 12.91/4.77  Parsing              : 0.16
% 12.91/4.77  CNF conversion       : 0.02
% 12.91/4.77  Main loop            : 3.71
% 12.91/4.77  Inferencing          : 0.64
% 12.91/4.77  Reduction            : 2.05
% 12.91/4.77  Demodulation         : 1.80
% 12.91/4.77  BG Simplification    : 0.10
% 12.91/4.77  Subsumption          : 0.79
% 12.91/4.77  Abstraction          : 0.20
% 12.91/4.77  MUC search           : 0.00
% 12.91/4.77  Cooper               : 0.00
% 12.91/4.77  Total                : 4.04
% 12.91/4.77  Index Insertion      : 0.00
% 12.91/4.77  Index Deletion       : 0.00
% 12.91/4.77  Index Matching       : 0.00
% 12.91/4.77  BG Taut test         : 0.00
%------------------------------------------------------------------------------
