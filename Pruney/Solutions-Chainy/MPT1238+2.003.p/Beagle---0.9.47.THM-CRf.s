%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:20:37 EST 2020

% Result     : Theorem 18.29s
% Output     : CNFRefutation 18.29s
% Verified   : 
% Statistics : Number of formulae       :   61 ( 173 expanded)
%              Number of leaves         :   25 (  73 expanded)
%              Depth                    :   11
%              Number of atoms          :   92 ( 335 expanded)
%              Number of equality atoms :   17 (  66 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > m1_subset_1 > l1_pre_topc > k4_subset_1 > k2_xboole_0 > k2_tarski > k1_tops_1 > #nlpp > u1_struct_0 > k3_tarski > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

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

tff(f_78,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => r1_tarski(k4_subset_1(u1_struct_0(A),k1_tops_1(A,B),k1_tops_1(A,C)),k1_tops_1(A,k4_subset_1(u1_struct_0(A),B,C))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_tops_1)).

tff(f_49,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => m1_subset_1(k4_subset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_subset_1)).

tff(f_35,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_37,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_27,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_67,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( r1_tarski(B,C)
               => r1_tarski(k1_tops_1(A,B),k1_tops_1(A,C)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_tops_1)).

tff(f_33,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(C,B) )
     => r1_tarski(k2_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_xboole_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k1_tops_1(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_tops_1)).

tff(c_24,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_22,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_20,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_155,plain,(
    ! [A_46,B_47,C_48] :
      ( k4_subset_1(A_46,B_47,C_48) = k2_xboole_0(B_47,C_48)
      | ~ m1_subset_1(C_48,k1_zfmisc_1(A_46))
      | ~ m1_subset_1(B_47,k1_zfmisc_1(A_46)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_189,plain,(
    ! [B_50] :
      ( k4_subset_1(u1_struct_0('#skF_1'),B_50,'#skF_2') = k2_xboole_0(B_50,'#skF_2')
      | ~ m1_subset_1(B_50,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(resolution,[status(thm)],[c_22,c_155])).

tff(c_203,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_3','#skF_2') = k2_xboole_0('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_20,c_189])).

tff(c_211,plain,(
    ! [A_51,B_52,C_53] :
      ( m1_subset_1(k4_subset_1(A_51,B_52,C_53),k1_zfmisc_1(A_51))
      | ~ m1_subset_1(C_53,k1_zfmisc_1(A_51))
      | ~ m1_subset_1(B_52,k1_zfmisc_1(A_51)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_227,plain,
    ( m1_subset_1(k2_xboole_0('#skF_3','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_203,c_211])).

tff(c_242,plain,(
    m1_subset_1(k2_xboole_0('#skF_3','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_22,c_227])).

tff(c_6,plain,(
    ! [B_7,A_6] : k2_tarski(B_7,A_6) = k2_tarski(A_6,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_59,plain,(
    ! [A_33,B_34] : k3_tarski(k2_tarski(A_33,B_34)) = k2_xboole_0(A_33,B_34) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_74,plain,(
    ! [B_35,A_36] : k3_tarski(k2_tarski(B_35,A_36)) = k2_xboole_0(A_36,B_35) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_59])).

tff(c_8,plain,(
    ! [A_8,B_9] : k3_tarski(k2_tarski(A_8,B_9)) = k2_xboole_0(A_8,B_9) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_97,plain,(
    ! [B_37,A_38] : k2_xboole_0(B_37,A_38) = k2_xboole_0(A_38,B_37) ),
    inference(superposition,[status(thm),theory(equality)],[c_74,c_8])).

tff(c_2,plain,(
    ! [A_1,B_2] : r1_tarski(A_1,k2_xboole_0(A_1,B_2)) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_112,plain,(
    ! [A_38,B_37] : r1_tarski(A_38,k2_xboole_0(B_37,A_38)) ),
    inference(superposition,[status(thm),theory(equality)],[c_97,c_2])).

tff(c_16,plain,(
    ! [A_18,B_22,C_24] :
      ( r1_tarski(k1_tops_1(A_18,B_22),k1_tops_1(A_18,C_24))
      | ~ r1_tarski(B_22,C_24)
      | ~ m1_subset_1(C_24,k1_zfmisc_1(u1_struct_0(A_18)))
      | ~ m1_subset_1(B_22,k1_zfmisc_1(u1_struct_0(A_18)))
      | ~ l1_pre_topc(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_4,plain,(
    ! [A_3,C_5,B_4] :
      ( r1_tarski(k2_xboole_0(A_3,C_5),B_4)
      | ~ r1_tarski(C_5,B_4)
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_80,plain,(
    ! [B_35,A_36] : k2_xboole_0(B_35,A_36) = k2_xboole_0(A_36,B_35) ),
    inference(superposition,[status(thm),theory(equality)],[c_74,c_8])).

tff(c_14,plain,(
    ! [A_16,B_17] :
      ( m1_subset_1(k1_tops_1(A_16,B_17),k1_zfmisc_1(u1_struct_0(A_16)))
      | ~ m1_subset_1(B_17,k1_zfmisc_1(u1_struct_0(A_16)))
      | ~ l1_pre_topc(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_354,plain,(
    ! [A_57,B_58,B_59] :
      ( k4_subset_1(u1_struct_0(A_57),B_58,k1_tops_1(A_57,B_59)) = k2_xboole_0(B_58,k1_tops_1(A_57,B_59))
      | ~ m1_subset_1(B_58,k1_zfmisc_1(u1_struct_0(A_57)))
      | ~ m1_subset_1(B_59,k1_zfmisc_1(u1_struct_0(A_57)))
      | ~ l1_pre_topc(A_57) ) ),
    inference(resolution,[status(thm)],[c_14,c_155])).

tff(c_2597,plain,(
    ! [A_76,B_77,B_78] :
      ( k4_subset_1(u1_struct_0(A_76),k1_tops_1(A_76,B_77),k1_tops_1(A_76,B_78)) = k2_xboole_0(k1_tops_1(A_76,B_77),k1_tops_1(A_76,B_78))
      | ~ m1_subset_1(B_78,k1_zfmisc_1(u1_struct_0(A_76)))
      | ~ m1_subset_1(B_77,k1_zfmisc_1(u1_struct_0(A_76)))
      | ~ l1_pre_topc(A_76) ) ),
    inference(resolution,[status(thm)],[c_14,c_354])).

tff(c_165,plain,(
    ! [B_49] :
      ( k4_subset_1(u1_struct_0('#skF_1'),B_49,'#skF_3') = k2_xboole_0(B_49,'#skF_3')
      | ~ m1_subset_1(B_49,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(resolution,[status(thm)],[c_20,c_155])).

tff(c_175,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_2','#skF_3') = k2_xboole_0('#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_22,c_165])).

tff(c_181,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_2','#skF_3') = k2_xboole_0('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_175])).

tff(c_18,plain,(
    ~ r1_tarski(k4_subset_1(u1_struct_0('#skF_1'),k1_tops_1('#skF_1','#skF_2'),k1_tops_1('#skF_1','#skF_3')),k1_tops_1('#skF_1',k4_subset_1(u1_struct_0('#skF_1'),'#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_184,plain,(
    ~ r1_tarski(k4_subset_1(u1_struct_0('#skF_1'),k1_tops_1('#skF_1','#skF_2'),k1_tops_1('#skF_1','#skF_3')),k1_tops_1('#skF_1',k2_xboole_0('#skF_3','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_181,c_18])).

tff(c_2619,plain,
    ( ~ r1_tarski(k2_xboole_0(k1_tops_1('#skF_1','#skF_2'),k1_tops_1('#skF_1','#skF_3')),k1_tops_1('#skF_1',k2_xboole_0('#skF_3','#skF_2')))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_2597,c_184])).

tff(c_2636,plain,(
    ~ r1_tarski(k2_xboole_0(k1_tops_1('#skF_1','#skF_3'),k1_tops_1('#skF_1','#skF_2')),k1_tops_1('#skF_1',k2_xboole_0('#skF_3','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_22,c_20,c_80,c_2619])).

tff(c_2678,plain,
    ( ~ r1_tarski(k1_tops_1('#skF_1','#skF_2'),k1_tops_1('#skF_1',k2_xboole_0('#skF_3','#skF_2')))
    | ~ r1_tarski(k1_tops_1('#skF_1','#skF_3'),k1_tops_1('#skF_1',k2_xboole_0('#skF_3','#skF_2'))) ),
    inference(resolution,[status(thm)],[c_4,c_2636])).

tff(c_31282,plain,(
    ~ r1_tarski(k1_tops_1('#skF_1','#skF_3'),k1_tops_1('#skF_1',k2_xboole_0('#skF_3','#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_2678])).

tff(c_31424,plain,
    ( ~ r1_tarski('#skF_3',k2_xboole_0('#skF_3','#skF_2'))
    | ~ m1_subset_1(k2_xboole_0('#skF_3','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_16,c_31282])).

tff(c_31428,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_20,c_242,c_2,c_31424])).

tff(c_31429,plain,(
    ~ r1_tarski(k1_tops_1('#skF_1','#skF_2'),k1_tops_1('#skF_1',k2_xboole_0('#skF_3','#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_2678])).

tff(c_31433,plain,
    ( ~ r1_tarski('#skF_2',k2_xboole_0('#skF_3','#skF_2'))
    | ~ m1_subset_1(k2_xboole_0('#skF_3','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_16,c_31429])).

tff(c_31437,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_22,c_242,c_112,c_31433])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n013.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 18:41:09 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 18.29/9.15  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 18.29/9.15  
% 18.29/9.15  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 18.29/9.15  %$ r1_tarski > m1_subset_1 > l1_pre_topc > k4_subset_1 > k2_xboole_0 > k2_tarski > k1_tops_1 > #nlpp > u1_struct_0 > k3_tarski > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1
% 18.29/9.15  
% 18.29/9.15  %Foreground sorts:
% 18.29/9.15  
% 18.29/9.15  
% 18.29/9.15  %Background operators:
% 18.29/9.15  
% 18.29/9.15  
% 18.29/9.15  %Foreground operators:
% 18.29/9.15  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 18.29/9.15  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 18.29/9.15  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 18.29/9.15  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 18.29/9.15  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 18.29/9.15  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 18.29/9.15  tff('#skF_2', type, '#skF_2': $i).
% 18.29/9.15  tff('#skF_3', type, '#skF_3': $i).
% 18.29/9.15  tff('#skF_1', type, '#skF_1': $i).
% 18.29/9.15  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 18.29/9.15  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 18.29/9.15  tff(k3_tarski, type, k3_tarski: $i > $i).
% 18.29/9.15  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 18.29/9.15  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 18.29/9.15  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 18.29/9.15  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 18.29/9.15  
% 18.29/9.17  tff(f_78, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => r1_tarski(k4_subset_1(u1_struct_0(A), k1_tops_1(A, B), k1_tops_1(A, C)), k1_tops_1(A, k4_subset_1(u1_struct_0(A), B, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_tops_1)).
% 18.29/9.17  tff(f_49, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 18.29/9.17  tff(f_43, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => m1_subset_1(k4_subset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k4_subset_1)).
% 18.29/9.17  tff(f_35, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 18.29/9.17  tff(f_37, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 18.29/9.17  tff(f_27, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 18.29/9.17  tff(f_67, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (r1_tarski(B, C) => r1_tarski(k1_tops_1(A, B), k1_tops_1(A, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_tops_1)).
% 18.29/9.17  tff(f_33, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(C, B)) => r1_tarski(k2_xboole_0(A, C), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_xboole_1)).
% 18.29/9.17  tff(f_55, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k1_tops_1(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_tops_1)).
% 18.29/9.17  tff(c_24, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_78])).
% 18.29/9.17  tff(c_22, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_78])).
% 18.29/9.17  tff(c_20, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_78])).
% 18.29/9.17  tff(c_155, plain, (![A_46, B_47, C_48]: (k4_subset_1(A_46, B_47, C_48)=k2_xboole_0(B_47, C_48) | ~m1_subset_1(C_48, k1_zfmisc_1(A_46)) | ~m1_subset_1(B_47, k1_zfmisc_1(A_46)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 18.29/9.17  tff(c_189, plain, (![B_50]: (k4_subset_1(u1_struct_0('#skF_1'), B_50, '#skF_2')=k2_xboole_0(B_50, '#skF_2') | ~m1_subset_1(B_50, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(resolution, [status(thm)], [c_22, c_155])).
% 18.29/9.17  tff(c_203, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_3', '#skF_2')=k2_xboole_0('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_20, c_189])).
% 18.29/9.17  tff(c_211, plain, (![A_51, B_52, C_53]: (m1_subset_1(k4_subset_1(A_51, B_52, C_53), k1_zfmisc_1(A_51)) | ~m1_subset_1(C_53, k1_zfmisc_1(A_51)) | ~m1_subset_1(B_52, k1_zfmisc_1(A_51)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 18.29/9.17  tff(c_227, plain, (m1_subset_1(k2_xboole_0('#skF_3', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_203, c_211])).
% 18.29/9.17  tff(c_242, plain, (m1_subset_1(k2_xboole_0('#skF_3', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_22, c_227])).
% 18.29/9.17  tff(c_6, plain, (![B_7, A_6]: (k2_tarski(B_7, A_6)=k2_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_35])).
% 18.29/9.17  tff(c_59, plain, (![A_33, B_34]: (k3_tarski(k2_tarski(A_33, B_34))=k2_xboole_0(A_33, B_34))), inference(cnfTransformation, [status(thm)], [f_37])).
% 18.29/9.17  tff(c_74, plain, (![B_35, A_36]: (k3_tarski(k2_tarski(B_35, A_36))=k2_xboole_0(A_36, B_35))), inference(superposition, [status(thm), theory('equality')], [c_6, c_59])).
% 18.29/9.17  tff(c_8, plain, (![A_8, B_9]: (k3_tarski(k2_tarski(A_8, B_9))=k2_xboole_0(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_37])).
% 18.29/9.17  tff(c_97, plain, (![B_37, A_38]: (k2_xboole_0(B_37, A_38)=k2_xboole_0(A_38, B_37))), inference(superposition, [status(thm), theory('equality')], [c_74, c_8])).
% 18.29/9.17  tff(c_2, plain, (![A_1, B_2]: (r1_tarski(A_1, k2_xboole_0(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_27])).
% 18.29/9.17  tff(c_112, plain, (![A_38, B_37]: (r1_tarski(A_38, k2_xboole_0(B_37, A_38)))), inference(superposition, [status(thm), theory('equality')], [c_97, c_2])).
% 18.29/9.17  tff(c_16, plain, (![A_18, B_22, C_24]: (r1_tarski(k1_tops_1(A_18, B_22), k1_tops_1(A_18, C_24)) | ~r1_tarski(B_22, C_24) | ~m1_subset_1(C_24, k1_zfmisc_1(u1_struct_0(A_18))) | ~m1_subset_1(B_22, k1_zfmisc_1(u1_struct_0(A_18))) | ~l1_pre_topc(A_18))), inference(cnfTransformation, [status(thm)], [f_67])).
% 18.29/9.17  tff(c_4, plain, (![A_3, C_5, B_4]: (r1_tarski(k2_xboole_0(A_3, C_5), B_4) | ~r1_tarski(C_5, B_4) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 18.29/9.17  tff(c_80, plain, (![B_35, A_36]: (k2_xboole_0(B_35, A_36)=k2_xboole_0(A_36, B_35))), inference(superposition, [status(thm), theory('equality')], [c_74, c_8])).
% 18.29/9.17  tff(c_14, plain, (![A_16, B_17]: (m1_subset_1(k1_tops_1(A_16, B_17), k1_zfmisc_1(u1_struct_0(A_16))) | ~m1_subset_1(B_17, k1_zfmisc_1(u1_struct_0(A_16))) | ~l1_pre_topc(A_16))), inference(cnfTransformation, [status(thm)], [f_55])).
% 18.29/9.17  tff(c_354, plain, (![A_57, B_58, B_59]: (k4_subset_1(u1_struct_0(A_57), B_58, k1_tops_1(A_57, B_59))=k2_xboole_0(B_58, k1_tops_1(A_57, B_59)) | ~m1_subset_1(B_58, k1_zfmisc_1(u1_struct_0(A_57))) | ~m1_subset_1(B_59, k1_zfmisc_1(u1_struct_0(A_57))) | ~l1_pre_topc(A_57))), inference(resolution, [status(thm)], [c_14, c_155])).
% 18.29/9.17  tff(c_2597, plain, (![A_76, B_77, B_78]: (k4_subset_1(u1_struct_0(A_76), k1_tops_1(A_76, B_77), k1_tops_1(A_76, B_78))=k2_xboole_0(k1_tops_1(A_76, B_77), k1_tops_1(A_76, B_78)) | ~m1_subset_1(B_78, k1_zfmisc_1(u1_struct_0(A_76))) | ~m1_subset_1(B_77, k1_zfmisc_1(u1_struct_0(A_76))) | ~l1_pre_topc(A_76))), inference(resolution, [status(thm)], [c_14, c_354])).
% 18.29/9.17  tff(c_165, plain, (![B_49]: (k4_subset_1(u1_struct_0('#skF_1'), B_49, '#skF_3')=k2_xboole_0(B_49, '#skF_3') | ~m1_subset_1(B_49, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(resolution, [status(thm)], [c_20, c_155])).
% 18.29/9.17  tff(c_175, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', '#skF_3')=k2_xboole_0('#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_22, c_165])).
% 18.29/9.17  tff(c_181, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', '#skF_3')=k2_xboole_0('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_80, c_175])).
% 18.29/9.17  tff(c_18, plain, (~r1_tarski(k4_subset_1(u1_struct_0('#skF_1'), k1_tops_1('#skF_1', '#skF_2'), k1_tops_1('#skF_1', '#skF_3')), k1_tops_1('#skF_1', k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_78])).
% 18.29/9.17  tff(c_184, plain, (~r1_tarski(k4_subset_1(u1_struct_0('#skF_1'), k1_tops_1('#skF_1', '#skF_2'), k1_tops_1('#skF_1', '#skF_3')), k1_tops_1('#skF_1', k2_xboole_0('#skF_3', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_181, c_18])).
% 18.29/9.17  tff(c_2619, plain, (~r1_tarski(k2_xboole_0(k1_tops_1('#skF_1', '#skF_2'), k1_tops_1('#skF_1', '#skF_3')), k1_tops_1('#skF_1', k2_xboole_0('#skF_3', '#skF_2'))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_2597, c_184])).
% 18.29/9.17  tff(c_2636, plain, (~r1_tarski(k2_xboole_0(k1_tops_1('#skF_1', '#skF_3'), k1_tops_1('#skF_1', '#skF_2')), k1_tops_1('#skF_1', k2_xboole_0('#skF_3', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_22, c_20, c_80, c_2619])).
% 18.29/9.17  tff(c_2678, plain, (~r1_tarski(k1_tops_1('#skF_1', '#skF_2'), k1_tops_1('#skF_1', k2_xboole_0('#skF_3', '#skF_2'))) | ~r1_tarski(k1_tops_1('#skF_1', '#skF_3'), k1_tops_1('#skF_1', k2_xboole_0('#skF_3', '#skF_2')))), inference(resolution, [status(thm)], [c_4, c_2636])).
% 18.29/9.17  tff(c_31282, plain, (~r1_tarski(k1_tops_1('#skF_1', '#skF_3'), k1_tops_1('#skF_1', k2_xboole_0('#skF_3', '#skF_2')))), inference(splitLeft, [status(thm)], [c_2678])).
% 18.29/9.17  tff(c_31424, plain, (~r1_tarski('#skF_3', k2_xboole_0('#skF_3', '#skF_2')) | ~m1_subset_1(k2_xboole_0('#skF_3', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_16, c_31282])).
% 18.29/9.17  tff(c_31428, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_24, c_20, c_242, c_2, c_31424])).
% 18.29/9.17  tff(c_31429, plain, (~r1_tarski(k1_tops_1('#skF_1', '#skF_2'), k1_tops_1('#skF_1', k2_xboole_0('#skF_3', '#skF_2')))), inference(splitRight, [status(thm)], [c_2678])).
% 18.29/9.17  tff(c_31433, plain, (~r1_tarski('#skF_2', k2_xboole_0('#skF_3', '#skF_2')) | ~m1_subset_1(k2_xboole_0('#skF_3', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_16, c_31429])).
% 18.29/9.17  tff(c_31437, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_24, c_22, c_242, c_112, c_31433])).
% 18.29/9.17  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 18.29/9.17  
% 18.29/9.17  Inference rules
% 18.29/9.17  ----------------------
% 18.29/9.17  #Ref     : 0
% 18.29/9.17  #Sup     : 6640
% 18.29/9.17  #Fact    : 0
% 18.29/9.17  #Define  : 0
% 18.29/9.17  #Split   : 3
% 18.29/9.17  #Chain   : 0
% 18.29/9.17  #Close   : 0
% 18.29/9.17  
% 18.29/9.17  Ordering : KBO
% 18.29/9.17  
% 18.29/9.17  Simplification rules
% 18.29/9.17  ----------------------
% 18.29/9.17  #Subsume      : 33
% 18.29/9.17  #Demod        : 13337
% 18.29/9.17  #Tautology    : 638
% 18.29/9.17  #SimpNegUnit  : 0
% 18.29/9.17  #BackRed      : 2
% 18.29/9.17  
% 18.29/9.17  #Partial instantiations: 0
% 18.29/9.17  #Strategies tried      : 1
% 18.29/9.17  
% 18.29/9.17  Timing (in seconds)
% 18.29/9.17  ----------------------
% 18.29/9.17  Preprocessing        : 0.29
% 18.29/9.17  Parsing              : 0.16
% 18.29/9.17  CNF conversion       : 0.02
% 18.29/9.17  Main loop            : 8.13
% 18.29/9.17  Inferencing          : 1.04
% 18.29/9.17  Reduction            : 4.73
% 18.29/9.17  Demodulation         : 4.25
% 18.29/9.17  BG Simplification    : 0.16
% 18.29/9.17  Subsumption          : 1.90
% 18.29/9.17  Abstraction          : 0.36
% 18.29/9.17  MUC search           : 0.00
% 18.29/9.17  Cooper               : 0.00
% 18.29/9.17  Total                : 8.45
% 18.29/9.17  Index Insertion      : 0.00
% 18.29/9.17  Index Deletion       : 0.00
% 18.29/9.17  Index Matching       : 0.00
% 18.29/9.17  BG Taut test         : 0.00
%------------------------------------------------------------------------------
