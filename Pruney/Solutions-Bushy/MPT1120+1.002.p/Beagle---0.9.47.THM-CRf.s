%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1120+1.002 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:37:26 EST 2020

% Result     : Theorem 4.83s
% Output     : CNFRefutation 4.83s
% Verified   : 
% Statistics : Number of formulae       :   66 ( 183 expanded)
%              Number of leaves         :   23 (  72 expanded)
%              Depth                    :   10
%              Number of atoms          :   97 ( 335 expanded)
%              Number of equality atoms :   15 (  54 expanded)
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

tff(f_77,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => r1_tarski(k2_pre_topc(A,k9_subset_1(u1_struct_0(A),B,C)),k9_subset_1(u1_struct_0(A),k2_pre_topc(A,B),k2_pre_topc(A,C))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_pre_topc)).

tff(f_42,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(f_34,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => m1_subset_1(k9_subset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k9_subset_1)).

tff(f_44,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_54,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_38,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k9_subset_1)).

tff(f_66,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( r1_tarski(B,C)
               => r1_tarski(k2_pre_topc(A,B),k2_pre_topc(A,C)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_pre_topc)).

tff(f_50,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(A,C) )
     => r1_tarski(A,k3_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_xboole_1)).

tff(f_30,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_pre_topc(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_pre_topc)).

tff(c_26,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_22,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_86,plain,(
    ! [A_45,B_46,C_47] :
      ( k9_subset_1(A_45,B_46,C_47) = k3_xboole_0(B_46,C_47)
      | ~ m1_subset_1(C_47,k1_zfmisc_1(A_45)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_108,plain,(
    ! [B_51] : k9_subset_1(u1_struct_0('#skF_1'),B_51,'#skF_3') = k3_xboole_0(B_51,'#skF_3') ),
    inference(resolution,[status(thm)],[c_22,c_86])).

tff(c_4,plain,(
    ! [A_3,B_4,C_5] :
      ( m1_subset_1(k9_subset_1(A_3,B_4,C_5),k1_zfmisc_1(A_3))
      | ~ m1_subset_1(C_5,k1_zfmisc_1(A_3)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_114,plain,(
    ! [B_51] :
      ( m1_subset_1(k3_xboole_0(B_51,'#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_108,c_4])).

tff(c_128,plain,(
    ! [B_51] : m1_subset_1(k3_xboole_0(B_51,'#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_114])).

tff(c_10,plain,(
    ! [A_12,B_13] : r1_tarski(k3_xboole_0(A_12,B_13),A_12) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_16,plain,(
    ! [A_17,B_18] :
      ( m1_subset_1(A_17,k1_zfmisc_1(B_18))
      | ~ r1_tarski(A_17,B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_42,plain,(
    ! [A_36,B_37,C_38] :
      ( k9_subset_1(A_36,B_37,B_37) = B_37
      | ~ m1_subset_1(C_38,k1_zfmisc_1(A_36)) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_62,plain,(
    ! [B_40,B_41,A_42] :
      ( k9_subset_1(B_40,B_41,B_41) = B_41
      | ~ r1_tarski(A_42,B_40) ) ),
    inference(resolution,[status(thm)],[c_16,c_42])).

tff(c_73,plain,(
    ! [A_12,B_41] : k9_subset_1(A_12,B_41,B_41) = B_41 ),
    inference(resolution,[status(thm)],[c_10,c_62])).

tff(c_118,plain,(
    k3_xboole_0('#skF_3','#skF_3') = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_108,c_73])).

tff(c_133,plain,(
    r1_tarski('#skF_3','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_118,c_10])).

tff(c_205,plain,(
    ! [B_60,B_61,A_62] :
      ( k9_subset_1(B_60,B_61,A_62) = k3_xboole_0(B_61,A_62)
      | ~ r1_tarski(A_62,B_60) ) ),
    inference(resolution,[status(thm)],[c_16,c_86])).

tff(c_226,plain,(
    ! [B_61] : k9_subset_1('#skF_3',B_61,'#skF_3') = k3_xboole_0(B_61,'#skF_3') ),
    inference(resolution,[status(thm)],[c_133,c_205])).

tff(c_96,plain,(
    ! [A_48,B_49,C_50] :
      ( m1_subset_1(k9_subset_1(A_48,B_49,C_50),k1_zfmisc_1(A_48))
      | ~ m1_subset_1(C_50,k1_zfmisc_1(A_48)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_14,plain,(
    ! [A_17,B_18] :
      ( r1_tarski(A_17,B_18)
      | ~ m1_subset_1(A_17,k1_zfmisc_1(B_18)) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_276,plain,(
    ! [A_65,B_66,C_67] :
      ( r1_tarski(k9_subset_1(A_65,B_66,C_67),A_65)
      | ~ m1_subset_1(C_67,k1_zfmisc_1(A_65)) ) ),
    inference(resolution,[status(thm)],[c_96,c_14])).

tff(c_281,plain,(
    ! [B_61] :
      ( r1_tarski(k3_xboole_0(B_61,'#skF_3'),'#skF_3')
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_226,c_276])).

tff(c_299,plain,(
    ~ m1_subset_1('#skF_3',k1_zfmisc_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_281])).

tff(c_310,plain,(
    ~ r1_tarski('#skF_3','#skF_3') ),
    inference(resolution,[status(thm)],[c_16,c_299])).

tff(c_314,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_133,c_310])).

tff(c_315,plain,(
    ! [B_61] : r1_tarski(k3_xboole_0(B_61,'#skF_3'),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_281])).

tff(c_18,plain,(
    ! [A_19,B_23,C_25] :
      ( r1_tarski(k2_pre_topc(A_19,B_23),k2_pre_topc(A_19,C_25))
      | ~ r1_tarski(B_23,C_25)
      | ~ m1_subset_1(C_25,k1_zfmisc_1(u1_struct_0(A_19)))
      | ~ m1_subset_1(B_23,k1_zfmisc_1(u1_struct_0(A_19)))
      | ~ l1_pre_topc(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_24,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_12,plain,(
    ! [A_14,B_15,C_16] :
      ( r1_tarski(A_14,k3_xboole_0(B_15,C_16))
      | ~ r1_tarski(A_14,C_16)
      | ~ r1_tarski(A_14,B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_402,plain,(
    ! [A_77,B_78] :
      ( m1_subset_1(k2_pre_topc(A_77,B_78),k1_zfmisc_1(u1_struct_0(A_77)))
      | ~ m1_subset_1(B_78,k1_zfmisc_1(u1_struct_0(A_77)))
      | ~ l1_pre_topc(A_77) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_8,plain,(
    ! [A_9,B_10,C_11] :
      ( k9_subset_1(A_9,B_10,C_11) = k3_xboole_0(B_10,C_11)
      | ~ m1_subset_1(C_11,k1_zfmisc_1(A_9)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_1118,plain,(
    ! [A_135,B_136,B_137] :
      ( k9_subset_1(u1_struct_0(A_135),B_136,k2_pre_topc(A_135,B_137)) = k3_xboole_0(B_136,k2_pre_topc(A_135,B_137))
      | ~ m1_subset_1(B_137,k1_zfmisc_1(u1_struct_0(A_135)))
      | ~ l1_pre_topc(A_135) ) ),
    inference(resolution,[status(thm)],[c_402,c_8])).

tff(c_1138,plain,(
    ! [B_136] :
      ( k9_subset_1(u1_struct_0('#skF_1'),B_136,k2_pre_topc('#skF_1','#skF_3')) = k3_xboole_0(B_136,k2_pre_topc('#skF_1','#skF_3'))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_22,c_1118])).

tff(c_1161,plain,(
    ! [B_136] : k9_subset_1(u1_struct_0('#skF_1'),B_136,k2_pre_topc('#skF_1','#skF_3')) = k3_xboole_0(B_136,k2_pre_topc('#skF_1','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_1138])).

tff(c_94,plain,(
    ! [B_46] : k9_subset_1(u1_struct_0('#skF_1'),B_46,'#skF_3') = k3_xboole_0(B_46,'#skF_3') ),
    inference(resolution,[status(thm)],[c_22,c_86])).

tff(c_20,plain,(
    ~ r1_tarski(k2_pre_topc('#skF_1',k9_subset_1(u1_struct_0('#skF_1'),'#skF_2','#skF_3')),k9_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2'),k2_pre_topc('#skF_1','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_107,plain,(
    ~ r1_tarski(k2_pre_topc('#skF_1',k3_xboole_0('#skF_2','#skF_3')),k9_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2'),k2_pre_topc('#skF_1','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_20])).

tff(c_1165,plain,(
    ~ r1_tarski(k2_pre_topc('#skF_1',k3_xboole_0('#skF_2','#skF_3')),k3_xboole_0(k2_pre_topc('#skF_1','#skF_2'),k2_pre_topc('#skF_1','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1161,c_107])).

tff(c_1308,plain,
    ( ~ r1_tarski(k2_pre_topc('#skF_1',k3_xboole_0('#skF_2','#skF_3')),k2_pre_topc('#skF_1','#skF_3'))
    | ~ r1_tarski(k2_pre_topc('#skF_1',k3_xboole_0('#skF_2','#skF_3')),k2_pre_topc('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_12,c_1165])).

tff(c_2746,plain,(
    ~ r1_tarski(k2_pre_topc('#skF_1',k3_xboole_0('#skF_2','#skF_3')),k2_pre_topc('#skF_1','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_1308])).

tff(c_2861,plain,
    ( ~ r1_tarski(k3_xboole_0('#skF_2','#skF_3'),'#skF_2')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_subset_1(k3_xboole_0('#skF_2','#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_18,c_2746])).

tff(c_2865,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_128,c_24,c_10,c_2861])).

tff(c_2866,plain,(
    ~ r1_tarski(k2_pre_topc('#skF_1',k3_xboole_0('#skF_2','#skF_3')),k2_pre_topc('#skF_1','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_1308])).

tff(c_2982,plain,
    ( ~ r1_tarski(k3_xboole_0('#skF_2','#skF_3'),'#skF_3')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_subset_1(k3_xboole_0('#skF_2','#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_18,c_2866])).

tff(c_2986,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_128,c_22,c_315,c_2982])).

%------------------------------------------------------------------------------
