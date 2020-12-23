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
% DateTime   : Thu Dec  3 10:19:04 EST 2020

% Result     : Theorem 11.81s
% Output     : CNFRefutation 11.81s
% Verified   : 
% Statistics : Number of formulae       :   70 ( 175 expanded)
%              Number of leaves         :   23 (  69 expanded)
%              Depth                    :   13
%              Number of atoms          :  110 ( 321 expanded)
%              Number of equality atoms :   10 (  38 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > m1_subset_1 > l1_pre_topc > k9_subset_1 > k3_xboole_0 > k2_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_78,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => r1_tarski(k2_pre_topc(A,k9_subset_1(u1_struct_0(A),B,C)),k9_subset_1(u1_struct_0(A),k2_pre_topc(A,B),k2_pre_topc(A,C))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_pre_topc)).

tff(f_49,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_29,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(A,C) )
     => r1_tarski(A,k3_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_xboole_1)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_67,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( r1_tarski(B,C)
               => r1_tarski(k2_pre_topc(A,B),k2_pre_topc(A,C)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_pre_topc)).

tff(f_55,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_pre_topc(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_pre_topc)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(c_22,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_67,plain,(
    ! [A_33,B_34] :
      ( r1_tarski(A_33,B_34)
      | ~ m1_subset_1(A_33,k1_zfmisc_1(B_34)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_74,plain,(
    r1_tarski('#skF_3',u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_22,c_67])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_28,plain,(
    ! [B_31,A_32] : k3_xboole_0(B_31,A_32) = k3_xboole_0(A_32,B_31) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_4,plain,(
    ! [A_3,B_4] : r1_tarski(k3_xboole_0(A_3,B_4),A_3) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_46,plain,(
    ! [A_32,B_31] : r1_tarski(k3_xboole_0(A_32,B_31),B_31) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_4])).

tff(c_112,plain,(
    ! [A_44,B_45,C_46] :
      ( r1_tarski(A_44,k3_xboole_0(B_45,C_46))
      | ~ r1_tarski(A_44,C_46)
      | ~ r1_tarski(A_44,B_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_8,plain,(
    ! [A_8,C_10,B_9] :
      ( r1_tarski(A_8,C_10)
      | ~ r1_tarski(B_9,C_10)
      | ~ r1_tarski(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_1012,plain,(
    ! [A_128,B_129,C_130,A_131] :
      ( r1_tarski(A_128,k3_xboole_0(B_129,C_130))
      | ~ r1_tarski(A_128,A_131)
      | ~ r1_tarski(A_131,C_130)
      | ~ r1_tarski(A_131,B_129) ) ),
    inference(resolution,[status(thm)],[c_112,c_8])).

tff(c_3039,plain,(
    ! [A_182,B_183,B_184,C_185] :
      ( r1_tarski(k3_xboole_0(A_182,B_183),k3_xboole_0(B_184,C_185))
      | ~ r1_tarski(B_183,C_185)
      | ~ r1_tarski(B_183,B_184) ) ),
    inference(resolution,[status(thm)],[c_46,c_1012])).

tff(c_91,plain,(
    ! [A_39,C_40,B_41] :
      ( r1_tarski(A_39,C_40)
      | ~ r1_tarski(B_41,C_40)
      | ~ r1_tarski(A_39,B_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_122,plain,(
    ! [A_47,A_48,B_49] :
      ( r1_tarski(A_47,A_48)
      | ~ r1_tarski(A_47,k3_xboole_0(A_48,B_49)) ) ),
    inference(resolution,[status(thm)],[c_4,c_91])).

tff(c_135,plain,(
    ! [A_47,B_2,A_1] :
      ( r1_tarski(A_47,B_2)
      | ~ r1_tarski(A_47,k3_xboole_0(A_1,B_2)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_122])).

tff(c_3875,plain,(
    ! [A_193,B_194,C_195,B_196] :
      ( r1_tarski(k3_xboole_0(A_193,B_194),C_195)
      | ~ r1_tarski(B_194,C_195)
      | ~ r1_tarski(B_194,B_196) ) ),
    inference(resolution,[status(thm)],[c_3039,c_135])).

tff(c_4038,plain,(
    ! [A_199,C_200] :
      ( r1_tarski(k3_xboole_0(A_199,'#skF_3'),C_200)
      | ~ r1_tarski('#skF_3',C_200) ) ),
    inference(resolution,[status(thm)],[c_74,c_3875])).

tff(c_4093,plain,(
    ! [A_1,C_200] :
      ( r1_tarski(k3_xboole_0('#skF_3',A_1),C_200)
      | ~ r1_tarski('#skF_3',C_200) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_4038])).

tff(c_14,plain,(
    ! [A_14,B_15] :
      ( m1_subset_1(A_14,k1_zfmisc_1(B_15))
      | ~ r1_tarski(A_14,B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_26,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_24,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_18,plain,(
    ! [A_18,B_22,C_24] :
      ( r1_tarski(k2_pre_topc(A_18,B_22),k2_pre_topc(A_18,C_24))
      | ~ r1_tarski(B_22,C_24)
      | ~ m1_subset_1(C_24,k1_zfmisc_1(u1_struct_0(A_18)))
      | ~ m1_subset_1(B_22,k1_zfmisc_1(u1_struct_0(A_18)))
      | ~ l1_pre_topc(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_6,plain,(
    ! [A_5,B_6,C_7] :
      ( r1_tarski(A_5,k3_xboole_0(B_6,C_7))
      | ~ r1_tarski(A_5,C_7)
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_397,plain,(
    ! [A_76,B_77] :
      ( m1_subset_1(k2_pre_topc(A_76,B_77),k1_zfmisc_1(u1_struct_0(A_76)))
      | ~ m1_subset_1(B_77,k1_zfmisc_1(u1_struct_0(A_76)))
      | ~ l1_pre_topc(A_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_10,plain,(
    ! [A_11,B_12,C_13] :
      ( k9_subset_1(A_11,B_12,C_13) = k3_xboole_0(B_12,C_13)
      | ~ m1_subset_1(C_13,k1_zfmisc_1(A_11)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_1199,plain,(
    ! [A_138,B_139,B_140] :
      ( k9_subset_1(u1_struct_0(A_138),B_139,k2_pre_topc(A_138,B_140)) = k3_xboole_0(B_139,k2_pre_topc(A_138,B_140))
      | ~ m1_subset_1(B_140,k1_zfmisc_1(u1_struct_0(A_138)))
      | ~ l1_pre_topc(A_138) ) ),
    inference(resolution,[status(thm)],[c_397,c_10])).

tff(c_1206,plain,(
    ! [B_139] :
      ( k9_subset_1(u1_struct_0('#skF_1'),B_139,k2_pre_topc('#skF_1','#skF_3')) = k3_xboole_0(B_139,k2_pre_topc('#skF_1','#skF_3'))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_22,c_1199])).

tff(c_1213,plain,(
    ! [B_139] : k9_subset_1(u1_struct_0('#skF_1'),B_139,k2_pre_topc('#skF_1','#skF_3')) = k3_xboole_0(B_139,k2_pre_topc('#skF_1','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_1206])).

tff(c_282,plain,(
    ! [A_64,B_65,C_66] :
      ( k9_subset_1(A_64,B_65,C_66) = k3_xboole_0(B_65,C_66)
      | ~ m1_subset_1(C_66,k1_zfmisc_1(A_64)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_290,plain,(
    ! [B_65] : k9_subset_1(u1_struct_0('#skF_1'),B_65,'#skF_3') = k3_xboole_0(B_65,'#skF_3') ),
    inference(resolution,[status(thm)],[c_22,c_282])).

tff(c_20,plain,(
    ~ r1_tarski(k2_pre_topc('#skF_1',k9_subset_1(u1_struct_0('#skF_1'),'#skF_2','#skF_3')),k9_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2'),k2_pre_topc('#skF_1','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_295,plain,(
    ~ r1_tarski(k2_pre_topc('#skF_1',k3_xboole_0('#skF_2','#skF_3')),k9_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2'),k2_pre_topc('#skF_1','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_290,c_20])).

tff(c_296,plain,(
    ~ r1_tarski(k2_pre_topc('#skF_1',k3_xboole_0('#skF_3','#skF_2')),k9_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2'),k2_pre_topc('#skF_1','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_295])).

tff(c_1580,plain,(
    ~ r1_tarski(k2_pre_topc('#skF_1',k3_xboole_0('#skF_3','#skF_2')),k3_xboole_0(k2_pre_topc('#skF_1','#skF_2'),k2_pre_topc('#skF_1','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1213,c_296])).

tff(c_1581,plain,(
    ~ r1_tarski(k2_pre_topc('#skF_1',k3_xboole_0('#skF_3','#skF_2')),k3_xboole_0(k2_pre_topc('#skF_1','#skF_3'),k2_pre_topc('#skF_1','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_1580])).

tff(c_2334,plain,
    ( ~ r1_tarski(k2_pre_topc('#skF_1',k3_xboole_0('#skF_3','#skF_2')),k2_pre_topc('#skF_1','#skF_2'))
    | ~ r1_tarski(k2_pre_topc('#skF_1',k3_xboole_0('#skF_3','#skF_2')),k2_pre_topc('#skF_1','#skF_3')) ),
    inference(resolution,[status(thm)],[c_6,c_1581])).

tff(c_14435,plain,(
    ~ r1_tarski(k2_pre_topc('#skF_1',k3_xboole_0('#skF_3','#skF_2')),k2_pre_topc('#skF_1','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_2334])).

tff(c_14438,plain,
    ( ~ r1_tarski(k3_xboole_0('#skF_3','#skF_2'),'#skF_3')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_subset_1(k3_xboole_0('#skF_3','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_18,c_14435])).

tff(c_14441,plain,(
    ~ m1_subset_1(k3_xboole_0('#skF_3','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_22,c_4,c_14438])).

tff(c_14445,plain,(
    ~ r1_tarski(k3_xboole_0('#skF_3','#skF_2'),u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_14,c_14441])).

tff(c_14448,plain,(
    ~ r1_tarski('#skF_3',u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_4093,c_14445])).

tff(c_14473,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_14448])).

tff(c_14474,plain,(
    ~ r1_tarski(k2_pre_topc('#skF_1',k3_xboole_0('#skF_3','#skF_2')),k2_pre_topc('#skF_1','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_2334])).

tff(c_14483,plain,
    ( ~ r1_tarski(k3_xboole_0('#skF_3','#skF_2'),'#skF_2')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_subset_1(k3_xboole_0('#skF_3','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_18,c_14474])).

tff(c_14486,plain,(
    ~ m1_subset_1(k3_xboole_0('#skF_3','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_24,c_46,c_14483])).

tff(c_14490,plain,(
    ~ r1_tarski(k3_xboole_0('#skF_3','#skF_2'),u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_14,c_14486])).

tff(c_14493,plain,(
    ~ r1_tarski('#skF_3',u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_4093,c_14490])).

tff(c_14518,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_14493])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n004.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 09:35:38 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 11.81/3.91  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.81/3.91  
% 11.81/3.91  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.81/3.91  %$ r1_tarski > m1_subset_1 > l1_pre_topc > k9_subset_1 > k3_xboole_0 > k2_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1
% 11.81/3.91  
% 11.81/3.91  %Foreground sorts:
% 11.81/3.91  
% 11.81/3.91  
% 11.81/3.91  %Background operators:
% 11.81/3.91  
% 11.81/3.91  
% 11.81/3.91  %Foreground operators:
% 11.81/3.91  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 11.81/3.91  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 11.81/3.91  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 11.81/3.91  tff('#skF_2', type, '#skF_2': $i).
% 11.81/3.91  tff('#skF_3', type, '#skF_3': $i).
% 11.81/3.91  tff('#skF_1', type, '#skF_1': $i).
% 11.81/3.91  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 11.81/3.91  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 11.81/3.91  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 11.81/3.91  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 11.81/3.91  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 11.81/3.91  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 11.81/3.91  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 11.81/3.91  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 11.81/3.91  
% 11.81/3.93  tff(f_78, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => r1_tarski(k2_pre_topc(A, k9_subset_1(u1_struct_0(A), B, C)), k9_subset_1(u1_struct_0(A), k2_pre_topc(A, B), k2_pre_topc(A, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t51_pre_topc)).
% 11.81/3.93  tff(f_49, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 11.81/3.93  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 11.81/3.93  tff(f_29, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 11.81/3.93  tff(f_35, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(A, C)) => r1_tarski(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t19_xboole_1)).
% 11.81/3.93  tff(f_41, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 11.81/3.93  tff(f_67, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (r1_tarski(B, C) => r1_tarski(k2_pre_topc(A, B), k2_pre_topc(A, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_pre_topc)).
% 11.81/3.93  tff(f_55, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_pre_topc(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_pre_topc)).
% 11.81/3.93  tff(f_45, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 11.81/3.93  tff(c_22, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_78])).
% 11.81/3.93  tff(c_67, plain, (![A_33, B_34]: (r1_tarski(A_33, B_34) | ~m1_subset_1(A_33, k1_zfmisc_1(B_34)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 11.81/3.93  tff(c_74, plain, (r1_tarski('#skF_3', u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_22, c_67])).
% 11.81/3.93  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 11.81/3.93  tff(c_28, plain, (![B_31, A_32]: (k3_xboole_0(B_31, A_32)=k3_xboole_0(A_32, B_31))), inference(cnfTransformation, [status(thm)], [f_27])).
% 11.81/3.93  tff(c_4, plain, (![A_3, B_4]: (r1_tarski(k3_xboole_0(A_3, B_4), A_3))), inference(cnfTransformation, [status(thm)], [f_29])).
% 11.81/3.93  tff(c_46, plain, (![A_32, B_31]: (r1_tarski(k3_xboole_0(A_32, B_31), B_31))), inference(superposition, [status(thm), theory('equality')], [c_28, c_4])).
% 11.81/3.93  tff(c_112, plain, (![A_44, B_45, C_46]: (r1_tarski(A_44, k3_xboole_0(B_45, C_46)) | ~r1_tarski(A_44, C_46) | ~r1_tarski(A_44, B_45))), inference(cnfTransformation, [status(thm)], [f_35])).
% 11.81/3.93  tff(c_8, plain, (![A_8, C_10, B_9]: (r1_tarski(A_8, C_10) | ~r1_tarski(B_9, C_10) | ~r1_tarski(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_41])).
% 11.81/3.93  tff(c_1012, plain, (![A_128, B_129, C_130, A_131]: (r1_tarski(A_128, k3_xboole_0(B_129, C_130)) | ~r1_tarski(A_128, A_131) | ~r1_tarski(A_131, C_130) | ~r1_tarski(A_131, B_129))), inference(resolution, [status(thm)], [c_112, c_8])).
% 11.81/3.93  tff(c_3039, plain, (![A_182, B_183, B_184, C_185]: (r1_tarski(k3_xboole_0(A_182, B_183), k3_xboole_0(B_184, C_185)) | ~r1_tarski(B_183, C_185) | ~r1_tarski(B_183, B_184))), inference(resolution, [status(thm)], [c_46, c_1012])).
% 11.81/3.93  tff(c_91, plain, (![A_39, C_40, B_41]: (r1_tarski(A_39, C_40) | ~r1_tarski(B_41, C_40) | ~r1_tarski(A_39, B_41))), inference(cnfTransformation, [status(thm)], [f_41])).
% 11.81/3.93  tff(c_122, plain, (![A_47, A_48, B_49]: (r1_tarski(A_47, A_48) | ~r1_tarski(A_47, k3_xboole_0(A_48, B_49)))), inference(resolution, [status(thm)], [c_4, c_91])).
% 11.81/3.93  tff(c_135, plain, (![A_47, B_2, A_1]: (r1_tarski(A_47, B_2) | ~r1_tarski(A_47, k3_xboole_0(A_1, B_2)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_122])).
% 11.81/3.93  tff(c_3875, plain, (![A_193, B_194, C_195, B_196]: (r1_tarski(k3_xboole_0(A_193, B_194), C_195) | ~r1_tarski(B_194, C_195) | ~r1_tarski(B_194, B_196))), inference(resolution, [status(thm)], [c_3039, c_135])).
% 11.81/3.93  tff(c_4038, plain, (![A_199, C_200]: (r1_tarski(k3_xboole_0(A_199, '#skF_3'), C_200) | ~r1_tarski('#skF_3', C_200))), inference(resolution, [status(thm)], [c_74, c_3875])).
% 11.81/3.93  tff(c_4093, plain, (![A_1, C_200]: (r1_tarski(k3_xboole_0('#skF_3', A_1), C_200) | ~r1_tarski('#skF_3', C_200))), inference(superposition, [status(thm), theory('equality')], [c_2, c_4038])).
% 11.81/3.93  tff(c_14, plain, (![A_14, B_15]: (m1_subset_1(A_14, k1_zfmisc_1(B_15)) | ~r1_tarski(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_49])).
% 11.81/3.93  tff(c_26, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_78])).
% 11.81/3.93  tff(c_24, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_78])).
% 11.81/3.93  tff(c_18, plain, (![A_18, B_22, C_24]: (r1_tarski(k2_pre_topc(A_18, B_22), k2_pre_topc(A_18, C_24)) | ~r1_tarski(B_22, C_24) | ~m1_subset_1(C_24, k1_zfmisc_1(u1_struct_0(A_18))) | ~m1_subset_1(B_22, k1_zfmisc_1(u1_struct_0(A_18))) | ~l1_pre_topc(A_18))), inference(cnfTransformation, [status(thm)], [f_67])).
% 11.81/3.93  tff(c_6, plain, (![A_5, B_6, C_7]: (r1_tarski(A_5, k3_xboole_0(B_6, C_7)) | ~r1_tarski(A_5, C_7) | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_35])).
% 11.81/3.93  tff(c_397, plain, (![A_76, B_77]: (m1_subset_1(k2_pre_topc(A_76, B_77), k1_zfmisc_1(u1_struct_0(A_76))) | ~m1_subset_1(B_77, k1_zfmisc_1(u1_struct_0(A_76))) | ~l1_pre_topc(A_76))), inference(cnfTransformation, [status(thm)], [f_55])).
% 11.81/3.93  tff(c_10, plain, (![A_11, B_12, C_13]: (k9_subset_1(A_11, B_12, C_13)=k3_xboole_0(B_12, C_13) | ~m1_subset_1(C_13, k1_zfmisc_1(A_11)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 11.81/3.93  tff(c_1199, plain, (![A_138, B_139, B_140]: (k9_subset_1(u1_struct_0(A_138), B_139, k2_pre_topc(A_138, B_140))=k3_xboole_0(B_139, k2_pre_topc(A_138, B_140)) | ~m1_subset_1(B_140, k1_zfmisc_1(u1_struct_0(A_138))) | ~l1_pre_topc(A_138))), inference(resolution, [status(thm)], [c_397, c_10])).
% 11.81/3.93  tff(c_1206, plain, (![B_139]: (k9_subset_1(u1_struct_0('#skF_1'), B_139, k2_pre_topc('#skF_1', '#skF_3'))=k3_xboole_0(B_139, k2_pre_topc('#skF_1', '#skF_3')) | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_22, c_1199])).
% 11.81/3.93  tff(c_1213, plain, (![B_139]: (k9_subset_1(u1_struct_0('#skF_1'), B_139, k2_pre_topc('#skF_1', '#skF_3'))=k3_xboole_0(B_139, k2_pre_topc('#skF_1', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_1206])).
% 11.81/3.93  tff(c_282, plain, (![A_64, B_65, C_66]: (k9_subset_1(A_64, B_65, C_66)=k3_xboole_0(B_65, C_66) | ~m1_subset_1(C_66, k1_zfmisc_1(A_64)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 11.81/3.93  tff(c_290, plain, (![B_65]: (k9_subset_1(u1_struct_0('#skF_1'), B_65, '#skF_3')=k3_xboole_0(B_65, '#skF_3'))), inference(resolution, [status(thm)], [c_22, c_282])).
% 11.81/3.93  tff(c_20, plain, (~r1_tarski(k2_pre_topc('#skF_1', k9_subset_1(u1_struct_0('#skF_1'), '#skF_2', '#skF_3')), k9_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_2'), k2_pre_topc('#skF_1', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_78])).
% 11.81/3.93  tff(c_295, plain, (~r1_tarski(k2_pre_topc('#skF_1', k3_xboole_0('#skF_2', '#skF_3')), k9_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_2'), k2_pre_topc('#skF_1', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_290, c_20])).
% 11.81/3.93  tff(c_296, plain, (~r1_tarski(k2_pre_topc('#skF_1', k3_xboole_0('#skF_3', '#skF_2')), k9_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_2'), k2_pre_topc('#skF_1', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_295])).
% 11.81/3.93  tff(c_1580, plain, (~r1_tarski(k2_pre_topc('#skF_1', k3_xboole_0('#skF_3', '#skF_2')), k3_xboole_0(k2_pre_topc('#skF_1', '#skF_2'), k2_pre_topc('#skF_1', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_1213, c_296])).
% 11.81/3.93  tff(c_1581, plain, (~r1_tarski(k2_pre_topc('#skF_1', k3_xboole_0('#skF_3', '#skF_2')), k3_xboole_0(k2_pre_topc('#skF_1', '#skF_3'), k2_pre_topc('#skF_1', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_1580])).
% 11.81/3.93  tff(c_2334, plain, (~r1_tarski(k2_pre_topc('#skF_1', k3_xboole_0('#skF_3', '#skF_2')), k2_pre_topc('#skF_1', '#skF_2')) | ~r1_tarski(k2_pre_topc('#skF_1', k3_xboole_0('#skF_3', '#skF_2')), k2_pre_topc('#skF_1', '#skF_3'))), inference(resolution, [status(thm)], [c_6, c_1581])).
% 11.81/3.93  tff(c_14435, plain, (~r1_tarski(k2_pre_topc('#skF_1', k3_xboole_0('#skF_3', '#skF_2')), k2_pre_topc('#skF_1', '#skF_3'))), inference(splitLeft, [status(thm)], [c_2334])).
% 11.81/3.93  tff(c_14438, plain, (~r1_tarski(k3_xboole_0('#skF_3', '#skF_2'), '#skF_3') | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1(k3_xboole_0('#skF_3', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_18, c_14435])).
% 11.81/3.93  tff(c_14441, plain, (~m1_subset_1(k3_xboole_0('#skF_3', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_22, c_4, c_14438])).
% 11.81/3.93  tff(c_14445, plain, (~r1_tarski(k3_xboole_0('#skF_3', '#skF_2'), u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_14, c_14441])).
% 11.81/3.93  tff(c_14448, plain, (~r1_tarski('#skF_3', u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_4093, c_14445])).
% 11.81/3.93  tff(c_14473, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_74, c_14448])).
% 11.81/3.93  tff(c_14474, plain, (~r1_tarski(k2_pre_topc('#skF_1', k3_xboole_0('#skF_3', '#skF_2')), k2_pre_topc('#skF_1', '#skF_2'))), inference(splitRight, [status(thm)], [c_2334])).
% 11.81/3.93  tff(c_14483, plain, (~r1_tarski(k3_xboole_0('#skF_3', '#skF_2'), '#skF_2') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1(k3_xboole_0('#skF_3', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_18, c_14474])).
% 11.81/3.93  tff(c_14486, plain, (~m1_subset_1(k3_xboole_0('#skF_3', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_24, c_46, c_14483])).
% 11.81/3.93  tff(c_14490, plain, (~r1_tarski(k3_xboole_0('#skF_3', '#skF_2'), u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_14, c_14486])).
% 11.81/3.93  tff(c_14493, plain, (~r1_tarski('#skF_3', u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_4093, c_14490])).
% 11.81/3.93  tff(c_14518, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_74, c_14493])).
% 11.81/3.93  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.81/3.93  
% 11.81/3.93  Inference rules
% 11.81/3.93  ----------------------
% 11.81/3.93  #Ref     : 0
% 11.81/3.93  #Sup     : 3767
% 11.81/3.93  #Fact    : 0
% 11.81/3.93  #Define  : 0
% 11.81/3.93  #Split   : 15
% 11.81/3.93  #Chain   : 0
% 11.81/3.93  #Close   : 0
% 11.81/3.93  
% 11.81/3.93  Ordering : KBO
% 11.81/3.93  
% 11.81/3.93  Simplification rules
% 11.81/3.93  ----------------------
% 11.81/3.93  #Subsume      : 1706
% 11.81/3.93  #Demod        : 472
% 11.81/3.93  #Tautology    : 454
% 11.81/3.93  #SimpNegUnit  : 12
% 11.81/3.93  #BackRed      : 10
% 11.81/3.93  
% 11.81/3.93  #Partial instantiations: 0
% 11.81/3.93  #Strategies tried      : 1
% 11.81/3.93  
% 11.81/3.93  Timing (in seconds)
% 11.81/3.93  ----------------------
% 11.81/3.93  Preprocessing        : 0.30
% 11.81/3.93  Parsing              : 0.17
% 11.81/3.93  CNF conversion       : 0.02
% 11.81/3.93  Main loop            : 2.88
% 11.81/3.93  Inferencing          : 0.61
% 11.81/3.93  Reduction            : 1.30
% 11.81/3.93  Demodulation         : 1.11
% 11.81/3.93  BG Simplification    : 0.07
% 11.81/3.93  Subsumption          : 0.71
% 11.81/3.93  Abstraction          : 0.09
% 11.81/3.93  MUC search           : 0.00
% 11.81/3.93  Cooper               : 0.00
% 11.81/3.93  Total                : 3.21
% 11.81/3.93  Index Insertion      : 0.00
% 11.81/3.93  Index Deletion       : 0.00
% 11.81/3.93  Index Matching       : 0.00
% 11.81/3.93  BG Taut test         : 0.00
%------------------------------------------------------------------------------
