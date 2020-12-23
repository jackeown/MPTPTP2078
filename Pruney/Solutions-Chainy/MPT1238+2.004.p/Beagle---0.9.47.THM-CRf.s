%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:20:38 EST 2020

% Result     : Theorem 3.13s
% Output     : CNFRefutation 3.30s
% Verified   : 
% Statistics : Number of formulae       :   75 ( 233 expanded)
%              Number of leaves         :   25 (  90 expanded)
%              Depth                    :   15
%              Number of atoms          :  112 ( 433 expanded)
%              Number of equality atoms :   17 (  89 expanded)
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

tff(f_76,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => r1_tarski(k4_subset_1(u1_struct_0(A),k1_tops_1(A,B),k1_tops_1(A,C)),k1_tops_1(A,k4_subset_1(u1_struct_0(A),B,C))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_tops_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_33,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(C,B) )
     => r1_tarski(k2_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_37,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_27,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_65,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( r1_tarski(B,C)
               => r1_tarski(k1_tops_1(A,B),k1_tops_1(A,C)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_tops_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k1_tops_1(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_tops_1)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(c_22,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_61,plain,(
    ! [A_32,B_33] :
      ( r1_tarski(A_32,B_33)
      | ~ m1_subset_1(A_32,k1_zfmisc_1(B_33)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_68,plain,(
    r1_tarski('#skF_3',u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_22,c_61])).

tff(c_24,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_69,plain,(
    r1_tarski('#skF_2',u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_24,c_61])).

tff(c_4,plain,(
    ! [A_3,C_5,B_4] :
      ( r1_tarski(k2_xboole_0(A_3,C_5),B_4)
      | ~ r1_tarski(C_5,B_4)
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_14,plain,(
    ! [A_13,B_14] :
      ( m1_subset_1(A_13,k1_zfmisc_1(B_14))
      | ~ r1_tarski(A_13,B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_26,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_6,plain,(
    ! [B_7,A_6] : k2_tarski(B_7,A_6) = k2_tarski(A_6,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_75,plain,(
    ! [A_36,B_37] : k3_tarski(k2_tarski(A_36,B_37)) = k2_xboole_0(A_36,B_37) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_90,plain,(
    ! [B_38,A_39] : k3_tarski(k2_tarski(B_38,A_39)) = k2_xboole_0(A_39,B_38) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_75])).

tff(c_8,plain,(
    ! [A_8,B_9] : k3_tarski(k2_tarski(A_8,B_9)) = k2_xboole_0(A_8,B_9) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_113,plain,(
    ! [B_40,A_41] : k2_xboole_0(B_40,A_41) = k2_xboole_0(A_41,B_40) ),
    inference(superposition,[status(thm),theory(equality)],[c_90,c_8])).

tff(c_2,plain,(
    ! [A_1,B_2] : r1_tarski(A_1,k2_xboole_0(A_1,B_2)) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_128,plain,(
    ! [A_41,B_40] : r1_tarski(A_41,k2_xboole_0(B_40,A_41)) ),
    inference(superposition,[status(thm),theory(equality)],[c_113,c_2])).

tff(c_18,plain,(
    ! [A_17,B_21,C_23] :
      ( r1_tarski(k1_tops_1(A_17,B_21),k1_tops_1(A_17,C_23))
      | ~ r1_tarski(B_21,C_23)
      | ~ m1_subset_1(C_23,k1_zfmisc_1(u1_struct_0(A_17)))
      | ~ m1_subset_1(B_21,k1_zfmisc_1(u1_struct_0(A_17)))
      | ~ l1_pre_topc(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_170,plain,(
    ! [A_47,B_48] :
      ( m1_subset_1(k1_tops_1(A_47,B_48),k1_zfmisc_1(u1_struct_0(A_47)))
      | ~ m1_subset_1(B_48,k1_zfmisc_1(u1_struct_0(A_47)))
      | ~ l1_pre_topc(A_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_12,plain,(
    ! [A_13,B_14] :
      ( r1_tarski(A_13,B_14)
      | ~ m1_subset_1(A_13,k1_zfmisc_1(B_14)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_174,plain,(
    ! [A_47,B_48] :
      ( r1_tarski(k1_tops_1(A_47,B_48),u1_struct_0(A_47))
      | ~ m1_subset_1(B_48,k1_zfmisc_1(u1_struct_0(A_47)))
      | ~ l1_pre_topc(A_47) ) ),
    inference(resolution,[status(thm)],[c_170,c_12])).

tff(c_96,plain,(
    ! [B_38,A_39] : k2_xboole_0(B_38,A_39) = k2_xboole_0(A_39,B_38) ),
    inference(superposition,[status(thm),theory(equality)],[c_90,c_8])).

tff(c_16,plain,(
    ! [A_15,B_16] :
      ( m1_subset_1(k1_tops_1(A_15,B_16),k1_zfmisc_1(u1_struct_0(A_15)))
      | ~ m1_subset_1(B_16,k1_zfmisc_1(u1_struct_0(A_15)))
      | ~ l1_pre_topc(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_175,plain,(
    ! [A_49,B_50,C_51] :
      ( k4_subset_1(A_49,B_50,C_51) = k2_xboole_0(B_50,C_51)
      | ~ m1_subset_1(C_51,k1_zfmisc_1(A_49))
      | ~ m1_subset_1(B_50,k1_zfmisc_1(A_49)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_375,plain,(
    ! [A_69,B_70,B_71] :
      ( k4_subset_1(u1_struct_0(A_69),B_70,k1_tops_1(A_69,B_71)) = k2_xboole_0(B_70,k1_tops_1(A_69,B_71))
      | ~ m1_subset_1(B_70,k1_zfmisc_1(u1_struct_0(A_69)))
      | ~ m1_subset_1(B_71,k1_zfmisc_1(u1_struct_0(A_69)))
      | ~ l1_pre_topc(A_69) ) ),
    inference(resolution,[status(thm)],[c_16,c_175])).

tff(c_832,plain,(
    ! [A_102,A_103,B_104] :
      ( k4_subset_1(u1_struct_0(A_102),A_103,k1_tops_1(A_102,B_104)) = k2_xboole_0(A_103,k1_tops_1(A_102,B_104))
      | ~ m1_subset_1(B_104,k1_zfmisc_1(u1_struct_0(A_102)))
      | ~ l1_pre_topc(A_102)
      | ~ r1_tarski(A_103,u1_struct_0(A_102)) ) ),
    inference(resolution,[status(thm)],[c_14,c_375])).

tff(c_839,plain,(
    ! [A_103] :
      ( k4_subset_1(u1_struct_0('#skF_1'),A_103,k1_tops_1('#skF_1','#skF_3')) = k2_xboole_0(A_103,k1_tops_1('#skF_1','#skF_3'))
      | ~ l1_pre_topc('#skF_1')
      | ~ r1_tarski(A_103,u1_struct_0('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_22,c_832])).

tff(c_850,plain,(
    ! [A_105] :
      ( k4_subset_1(u1_struct_0('#skF_1'),A_105,k1_tops_1('#skF_1','#skF_3')) = k2_xboole_0(A_105,k1_tops_1('#skF_1','#skF_3'))
      | ~ r1_tarski(A_105,u1_struct_0('#skF_1')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_839])).

tff(c_189,plain,(
    ! [B_54] :
      ( k4_subset_1(u1_struct_0('#skF_1'),B_54,'#skF_3') = k2_xboole_0(B_54,'#skF_3')
      | ~ m1_subset_1(B_54,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(resolution,[status(thm)],[c_22,c_175])).

tff(c_203,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_2','#skF_3') = k2_xboole_0('#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_24,c_189])).

tff(c_210,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_2','#skF_3') = k2_xboole_0('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_203])).

tff(c_20,plain,(
    ~ r1_tarski(k4_subset_1(u1_struct_0('#skF_1'),k1_tops_1('#skF_1','#skF_2'),k1_tops_1('#skF_1','#skF_3')),k1_tops_1('#skF_1',k4_subset_1(u1_struct_0('#skF_1'),'#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_213,plain,(
    ~ r1_tarski(k4_subset_1(u1_struct_0('#skF_1'),k1_tops_1('#skF_1','#skF_2'),k1_tops_1('#skF_1','#skF_3')),k1_tops_1('#skF_1',k2_xboole_0('#skF_3','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_210,c_20])).

tff(c_870,plain,
    ( ~ r1_tarski(k2_xboole_0(k1_tops_1('#skF_1','#skF_2'),k1_tops_1('#skF_1','#skF_3')),k1_tops_1('#skF_1',k2_xboole_0('#skF_3','#skF_2')))
    | ~ r1_tarski(k1_tops_1('#skF_1','#skF_2'),u1_struct_0('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_850,c_213])).

tff(c_901,plain,
    ( ~ r1_tarski(k2_xboole_0(k1_tops_1('#skF_1','#skF_3'),k1_tops_1('#skF_1','#skF_2')),k1_tops_1('#skF_1',k2_xboole_0('#skF_3','#skF_2')))
    | ~ r1_tarski(k1_tops_1('#skF_1','#skF_2'),u1_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_870])).

tff(c_991,plain,(
    ~ r1_tarski(k1_tops_1('#skF_1','#skF_2'),u1_struct_0('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_901])).

tff(c_994,plain,
    ( ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_174,c_991])).

tff(c_998,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_24,c_994])).

tff(c_999,plain,(
    ~ r1_tarski(k2_xboole_0(k1_tops_1('#skF_1','#skF_3'),k1_tops_1('#skF_1','#skF_2')),k1_tops_1('#skF_1',k2_xboole_0('#skF_3','#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_901])).

tff(c_1045,plain,
    ( ~ r1_tarski(k1_tops_1('#skF_1','#skF_2'),k1_tops_1('#skF_1',k2_xboole_0('#skF_3','#skF_2')))
    | ~ r1_tarski(k1_tops_1('#skF_1','#skF_3'),k1_tops_1('#skF_1',k2_xboole_0('#skF_3','#skF_2'))) ),
    inference(resolution,[status(thm)],[c_4,c_999])).

tff(c_1202,plain,(
    ~ r1_tarski(k1_tops_1('#skF_1','#skF_3'),k1_tops_1('#skF_1',k2_xboole_0('#skF_3','#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_1045])).

tff(c_1205,plain,
    ( ~ r1_tarski('#skF_3',k2_xboole_0('#skF_3','#skF_2'))
    | ~ m1_subset_1(k2_xboole_0('#skF_3','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_18,c_1202])).

tff(c_1208,plain,(
    ~ m1_subset_1(k2_xboole_0('#skF_3','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_22,c_2,c_1205])).

tff(c_1212,plain,(
    ~ r1_tarski(k2_xboole_0('#skF_3','#skF_2'),u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_14,c_1208])).

tff(c_1215,plain,
    ( ~ r1_tarski('#skF_2',u1_struct_0('#skF_1'))
    | ~ r1_tarski('#skF_3',u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_4,c_1212])).

tff(c_1219,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_69,c_1215])).

tff(c_1220,plain,(
    ~ r1_tarski(k1_tops_1('#skF_1','#skF_2'),k1_tops_1('#skF_1',k2_xboole_0('#skF_3','#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_1045])).

tff(c_1224,plain,
    ( ~ r1_tarski('#skF_2',k2_xboole_0('#skF_3','#skF_2'))
    | ~ m1_subset_1(k2_xboole_0('#skF_3','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_18,c_1220])).

tff(c_1227,plain,(
    ~ m1_subset_1(k2_xboole_0('#skF_3','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_24,c_128,c_1224])).

tff(c_1301,plain,(
    ~ r1_tarski(k2_xboole_0('#skF_3','#skF_2'),u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_14,c_1227])).

tff(c_1304,plain,
    ( ~ r1_tarski('#skF_2',u1_struct_0('#skF_1'))
    | ~ r1_tarski('#skF_3',u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_4,c_1301])).

tff(c_1308,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_69,c_1304])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n022.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 13:05:56 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.13/1.50  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.30/1.50  
% 3.30/1.50  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.30/1.51  %$ r1_tarski > m1_subset_1 > l1_pre_topc > k4_subset_1 > k2_xboole_0 > k2_tarski > k1_tops_1 > #nlpp > u1_struct_0 > k3_tarski > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1
% 3.30/1.51  
% 3.30/1.51  %Foreground sorts:
% 3.30/1.51  
% 3.30/1.51  
% 3.30/1.51  %Background operators:
% 3.30/1.51  
% 3.30/1.51  
% 3.30/1.51  %Foreground operators:
% 3.30/1.51  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.30/1.51  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.30/1.51  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.30/1.51  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.30/1.51  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 3.30/1.51  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 3.30/1.51  tff('#skF_2', type, '#skF_2': $i).
% 3.30/1.51  tff('#skF_3', type, '#skF_3': $i).
% 3.30/1.51  tff('#skF_1', type, '#skF_1': $i).
% 3.30/1.51  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.30/1.51  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.30/1.51  tff(k3_tarski, type, k3_tarski: $i > $i).
% 3.30/1.51  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.30/1.51  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.30/1.51  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.30/1.51  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.30/1.51  
% 3.30/1.52  tff(f_76, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => r1_tarski(k4_subset_1(u1_struct_0(A), k1_tops_1(A, B), k1_tops_1(A, C)), k1_tops_1(A, k4_subset_1(u1_struct_0(A), B, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_tops_1)).
% 3.30/1.52  tff(f_47, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 3.30/1.52  tff(f_33, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(C, B)) => r1_tarski(k2_xboole_0(A, C), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_xboole_1)).
% 3.30/1.52  tff(f_35, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 3.30/1.52  tff(f_37, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 3.30/1.52  tff(f_27, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 3.30/1.52  tff(f_65, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (r1_tarski(B, C) => r1_tarski(k1_tops_1(A, B), k1_tops_1(A, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_tops_1)).
% 3.30/1.52  tff(f_53, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k1_tops_1(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_tops_1)).
% 3.30/1.52  tff(f_43, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 3.30/1.52  tff(c_22, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.30/1.52  tff(c_61, plain, (![A_32, B_33]: (r1_tarski(A_32, B_33) | ~m1_subset_1(A_32, k1_zfmisc_1(B_33)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.30/1.52  tff(c_68, plain, (r1_tarski('#skF_3', u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_22, c_61])).
% 3.30/1.52  tff(c_24, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.30/1.52  tff(c_69, plain, (r1_tarski('#skF_2', u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_24, c_61])).
% 3.30/1.52  tff(c_4, plain, (![A_3, C_5, B_4]: (r1_tarski(k2_xboole_0(A_3, C_5), B_4) | ~r1_tarski(C_5, B_4) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.30/1.52  tff(c_14, plain, (![A_13, B_14]: (m1_subset_1(A_13, k1_zfmisc_1(B_14)) | ~r1_tarski(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.30/1.52  tff(c_26, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.30/1.52  tff(c_6, plain, (![B_7, A_6]: (k2_tarski(B_7, A_6)=k2_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.30/1.52  tff(c_75, plain, (![A_36, B_37]: (k3_tarski(k2_tarski(A_36, B_37))=k2_xboole_0(A_36, B_37))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.30/1.52  tff(c_90, plain, (![B_38, A_39]: (k3_tarski(k2_tarski(B_38, A_39))=k2_xboole_0(A_39, B_38))), inference(superposition, [status(thm), theory('equality')], [c_6, c_75])).
% 3.30/1.52  tff(c_8, plain, (![A_8, B_9]: (k3_tarski(k2_tarski(A_8, B_9))=k2_xboole_0(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.30/1.52  tff(c_113, plain, (![B_40, A_41]: (k2_xboole_0(B_40, A_41)=k2_xboole_0(A_41, B_40))), inference(superposition, [status(thm), theory('equality')], [c_90, c_8])).
% 3.30/1.52  tff(c_2, plain, (![A_1, B_2]: (r1_tarski(A_1, k2_xboole_0(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.30/1.52  tff(c_128, plain, (![A_41, B_40]: (r1_tarski(A_41, k2_xboole_0(B_40, A_41)))), inference(superposition, [status(thm), theory('equality')], [c_113, c_2])).
% 3.30/1.52  tff(c_18, plain, (![A_17, B_21, C_23]: (r1_tarski(k1_tops_1(A_17, B_21), k1_tops_1(A_17, C_23)) | ~r1_tarski(B_21, C_23) | ~m1_subset_1(C_23, k1_zfmisc_1(u1_struct_0(A_17))) | ~m1_subset_1(B_21, k1_zfmisc_1(u1_struct_0(A_17))) | ~l1_pre_topc(A_17))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.30/1.52  tff(c_170, plain, (![A_47, B_48]: (m1_subset_1(k1_tops_1(A_47, B_48), k1_zfmisc_1(u1_struct_0(A_47))) | ~m1_subset_1(B_48, k1_zfmisc_1(u1_struct_0(A_47))) | ~l1_pre_topc(A_47))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.30/1.52  tff(c_12, plain, (![A_13, B_14]: (r1_tarski(A_13, B_14) | ~m1_subset_1(A_13, k1_zfmisc_1(B_14)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.30/1.52  tff(c_174, plain, (![A_47, B_48]: (r1_tarski(k1_tops_1(A_47, B_48), u1_struct_0(A_47)) | ~m1_subset_1(B_48, k1_zfmisc_1(u1_struct_0(A_47))) | ~l1_pre_topc(A_47))), inference(resolution, [status(thm)], [c_170, c_12])).
% 3.30/1.52  tff(c_96, plain, (![B_38, A_39]: (k2_xboole_0(B_38, A_39)=k2_xboole_0(A_39, B_38))), inference(superposition, [status(thm), theory('equality')], [c_90, c_8])).
% 3.30/1.52  tff(c_16, plain, (![A_15, B_16]: (m1_subset_1(k1_tops_1(A_15, B_16), k1_zfmisc_1(u1_struct_0(A_15))) | ~m1_subset_1(B_16, k1_zfmisc_1(u1_struct_0(A_15))) | ~l1_pre_topc(A_15))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.30/1.52  tff(c_175, plain, (![A_49, B_50, C_51]: (k4_subset_1(A_49, B_50, C_51)=k2_xboole_0(B_50, C_51) | ~m1_subset_1(C_51, k1_zfmisc_1(A_49)) | ~m1_subset_1(B_50, k1_zfmisc_1(A_49)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.30/1.52  tff(c_375, plain, (![A_69, B_70, B_71]: (k4_subset_1(u1_struct_0(A_69), B_70, k1_tops_1(A_69, B_71))=k2_xboole_0(B_70, k1_tops_1(A_69, B_71)) | ~m1_subset_1(B_70, k1_zfmisc_1(u1_struct_0(A_69))) | ~m1_subset_1(B_71, k1_zfmisc_1(u1_struct_0(A_69))) | ~l1_pre_topc(A_69))), inference(resolution, [status(thm)], [c_16, c_175])).
% 3.30/1.52  tff(c_832, plain, (![A_102, A_103, B_104]: (k4_subset_1(u1_struct_0(A_102), A_103, k1_tops_1(A_102, B_104))=k2_xboole_0(A_103, k1_tops_1(A_102, B_104)) | ~m1_subset_1(B_104, k1_zfmisc_1(u1_struct_0(A_102))) | ~l1_pre_topc(A_102) | ~r1_tarski(A_103, u1_struct_0(A_102)))), inference(resolution, [status(thm)], [c_14, c_375])).
% 3.30/1.52  tff(c_839, plain, (![A_103]: (k4_subset_1(u1_struct_0('#skF_1'), A_103, k1_tops_1('#skF_1', '#skF_3'))=k2_xboole_0(A_103, k1_tops_1('#skF_1', '#skF_3')) | ~l1_pre_topc('#skF_1') | ~r1_tarski(A_103, u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_22, c_832])).
% 3.30/1.52  tff(c_850, plain, (![A_105]: (k4_subset_1(u1_struct_0('#skF_1'), A_105, k1_tops_1('#skF_1', '#skF_3'))=k2_xboole_0(A_105, k1_tops_1('#skF_1', '#skF_3')) | ~r1_tarski(A_105, u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_839])).
% 3.30/1.52  tff(c_189, plain, (![B_54]: (k4_subset_1(u1_struct_0('#skF_1'), B_54, '#skF_3')=k2_xboole_0(B_54, '#skF_3') | ~m1_subset_1(B_54, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(resolution, [status(thm)], [c_22, c_175])).
% 3.30/1.52  tff(c_203, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', '#skF_3')=k2_xboole_0('#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_24, c_189])).
% 3.30/1.52  tff(c_210, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', '#skF_3')=k2_xboole_0('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_96, c_203])).
% 3.30/1.52  tff(c_20, plain, (~r1_tarski(k4_subset_1(u1_struct_0('#skF_1'), k1_tops_1('#skF_1', '#skF_2'), k1_tops_1('#skF_1', '#skF_3')), k1_tops_1('#skF_1', k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.30/1.52  tff(c_213, plain, (~r1_tarski(k4_subset_1(u1_struct_0('#skF_1'), k1_tops_1('#skF_1', '#skF_2'), k1_tops_1('#skF_1', '#skF_3')), k1_tops_1('#skF_1', k2_xboole_0('#skF_3', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_210, c_20])).
% 3.30/1.52  tff(c_870, plain, (~r1_tarski(k2_xboole_0(k1_tops_1('#skF_1', '#skF_2'), k1_tops_1('#skF_1', '#skF_3')), k1_tops_1('#skF_1', k2_xboole_0('#skF_3', '#skF_2'))) | ~r1_tarski(k1_tops_1('#skF_1', '#skF_2'), u1_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_850, c_213])).
% 3.30/1.52  tff(c_901, plain, (~r1_tarski(k2_xboole_0(k1_tops_1('#skF_1', '#skF_3'), k1_tops_1('#skF_1', '#skF_2')), k1_tops_1('#skF_1', k2_xboole_0('#skF_3', '#skF_2'))) | ~r1_tarski(k1_tops_1('#skF_1', '#skF_2'), u1_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_96, c_870])).
% 3.30/1.52  tff(c_991, plain, (~r1_tarski(k1_tops_1('#skF_1', '#skF_2'), u1_struct_0('#skF_1'))), inference(splitLeft, [status(thm)], [c_901])).
% 3.30/1.52  tff(c_994, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_174, c_991])).
% 3.30/1.52  tff(c_998, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_26, c_24, c_994])).
% 3.30/1.52  tff(c_999, plain, (~r1_tarski(k2_xboole_0(k1_tops_1('#skF_1', '#skF_3'), k1_tops_1('#skF_1', '#skF_2')), k1_tops_1('#skF_1', k2_xboole_0('#skF_3', '#skF_2')))), inference(splitRight, [status(thm)], [c_901])).
% 3.30/1.52  tff(c_1045, plain, (~r1_tarski(k1_tops_1('#skF_1', '#skF_2'), k1_tops_1('#skF_1', k2_xboole_0('#skF_3', '#skF_2'))) | ~r1_tarski(k1_tops_1('#skF_1', '#skF_3'), k1_tops_1('#skF_1', k2_xboole_0('#skF_3', '#skF_2')))), inference(resolution, [status(thm)], [c_4, c_999])).
% 3.30/1.52  tff(c_1202, plain, (~r1_tarski(k1_tops_1('#skF_1', '#skF_3'), k1_tops_1('#skF_1', k2_xboole_0('#skF_3', '#skF_2')))), inference(splitLeft, [status(thm)], [c_1045])).
% 3.30/1.52  tff(c_1205, plain, (~r1_tarski('#skF_3', k2_xboole_0('#skF_3', '#skF_2')) | ~m1_subset_1(k2_xboole_0('#skF_3', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_18, c_1202])).
% 3.30/1.52  tff(c_1208, plain, (~m1_subset_1(k2_xboole_0('#skF_3', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_22, c_2, c_1205])).
% 3.30/1.52  tff(c_1212, plain, (~r1_tarski(k2_xboole_0('#skF_3', '#skF_2'), u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_14, c_1208])).
% 3.30/1.52  tff(c_1215, plain, (~r1_tarski('#skF_2', u1_struct_0('#skF_1')) | ~r1_tarski('#skF_3', u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_4, c_1212])).
% 3.30/1.52  tff(c_1219, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_68, c_69, c_1215])).
% 3.30/1.52  tff(c_1220, plain, (~r1_tarski(k1_tops_1('#skF_1', '#skF_2'), k1_tops_1('#skF_1', k2_xboole_0('#skF_3', '#skF_2')))), inference(splitRight, [status(thm)], [c_1045])).
% 3.30/1.52  tff(c_1224, plain, (~r1_tarski('#skF_2', k2_xboole_0('#skF_3', '#skF_2')) | ~m1_subset_1(k2_xboole_0('#skF_3', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_18, c_1220])).
% 3.30/1.52  tff(c_1227, plain, (~m1_subset_1(k2_xboole_0('#skF_3', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_24, c_128, c_1224])).
% 3.30/1.52  tff(c_1301, plain, (~r1_tarski(k2_xboole_0('#skF_3', '#skF_2'), u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_14, c_1227])).
% 3.30/1.52  tff(c_1304, plain, (~r1_tarski('#skF_2', u1_struct_0('#skF_1')) | ~r1_tarski('#skF_3', u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_4, c_1301])).
% 3.30/1.52  tff(c_1308, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_68, c_69, c_1304])).
% 3.30/1.52  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.30/1.52  
% 3.30/1.52  Inference rules
% 3.30/1.52  ----------------------
% 3.30/1.52  #Ref     : 0
% 3.30/1.52  #Sup     : 281
% 3.30/1.52  #Fact    : 0
% 3.30/1.52  #Define  : 0
% 3.30/1.52  #Split   : 2
% 3.30/1.52  #Chain   : 0
% 3.30/1.52  #Close   : 0
% 3.30/1.52  
% 3.30/1.52  Ordering : KBO
% 3.30/1.52  
% 3.30/1.52  Simplification rules
% 3.30/1.52  ----------------------
% 3.30/1.52  #Subsume      : 42
% 3.30/1.52  #Demod        : 184
% 3.30/1.52  #Tautology    : 157
% 3.30/1.52  #SimpNegUnit  : 0
% 3.30/1.52  #BackRed      : 1
% 3.30/1.52  
% 3.30/1.52  #Partial instantiations: 0
% 3.30/1.52  #Strategies tried      : 1
% 3.30/1.52  
% 3.30/1.52  Timing (in seconds)
% 3.30/1.52  ----------------------
% 3.30/1.52  Preprocessing        : 0.29
% 3.30/1.52  Parsing              : 0.16
% 3.30/1.52  CNF conversion       : 0.02
% 3.30/1.52  Main loop            : 0.46
% 3.30/1.52  Inferencing          : 0.16
% 3.30/1.52  Reduction            : 0.17
% 3.30/1.52  Demodulation         : 0.13
% 3.30/1.52  BG Simplification    : 0.02
% 3.30/1.52  Subsumption          : 0.08
% 3.30/1.52  Abstraction          : 0.02
% 3.30/1.52  MUC search           : 0.00
% 3.30/1.53  Cooper               : 0.00
% 3.30/1.53  Total                : 0.78
% 3.30/1.53  Index Insertion      : 0.00
% 3.30/1.53  Index Deletion       : 0.00
% 3.30/1.53  Index Matching       : 0.00
% 3.30/1.53  BG Taut test         : 0.00
%------------------------------------------------------------------------------
