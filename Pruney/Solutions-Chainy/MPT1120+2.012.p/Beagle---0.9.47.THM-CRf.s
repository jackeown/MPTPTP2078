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
% DateTime   : Thu Dec  3 10:19:04 EST 2020

% Result     : Theorem 5.81s
% Output     : CNFRefutation 5.81s
% Verified   : 
% Statistics : Number of formulae       :   76 ( 190 expanded)
%              Number of leaves         :   25 (  75 expanded)
%              Depth                    :   11
%              Number of atoms          :  120 ( 381 expanded)
%              Number of equality atoms :   16 (  53 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > m1_subset_1 > l1_pre_topc > k9_subset_1 > k3_xboole_0 > k2_tarski > k2_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_setfam_1 > #skF_2 > #skF_3 > #skF_1

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

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_55,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_84,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => r1_tarski(k2_pre_topc(A,k9_subset_1(u1_struct_0(A),B,C)),k9_subset_1(u1_struct_0(A),k2_pre_topc(A,B),k2_pre_topc(A,C))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_pre_topc)).

tff(f_49,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => m1_subset_1(k9_subset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k9_subset_1)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(A,C) )
     => r1_tarski(A,k3_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_xboole_1)).

tff(f_73,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( r1_tarski(B,C)
               => r1_tarski(k2_pre_topc(A,B),k2_pre_topc(A,C)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_pre_topc)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(k3_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t108_xboole_1)).

tff(f_61,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_pre_topc(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_pre_topc)).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_20,plain,(
    ! [A_17,B_18] :
      ( m1_subset_1(A_17,k1_zfmisc_1(B_18))
      | ~ r1_tarski(A_17,B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_28,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_35,plain,(
    ! [A_33,B_34] :
      ( r1_tarski(A_33,B_34)
      | ~ m1_subset_1(A_33,k1_zfmisc_1(B_34)) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_42,plain,(
    r1_tarski('#skF_3',u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_28,c_35])).

tff(c_90,plain,(
    ! [A_53,B_54,C_55] :
      ( k9_subset_1(A_53,B_54,C_55) = k3_xboole_0(B_54,C_55)
      | ~ m1_subset_1(C_55,k1_zfmisc_1(A_53)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_176,plain,(
    ! [B_64,B_65,A_66] :
      ( k9_subset_1(B_64,B_65,A_66) = k3_xboole_0(B_65,A_66)
      | ~ r1_tarski(A_66,B_64) ) ),
    inference(resolution,[status(thm)],[c_20,c_90])).

tff(c_203,plain,(
    ! [B_67,B_68] : k9_subset_1(B_67,B_68,B_67) = k3_xboole_0(B_68,B_67) ),
    inference(resolution,[status(thm)],[c_6,c_176])).

tff(c_77,plain,(
    ! [A_44,B_45,C_46] :
      ( m1_subset_1(k9_subset_1(A_44,B_45,C_46),k1_zfmisc_1(A_44))
      | ~ m1_subset_1(C_46,k1_zfmisc_1(A_44)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_18,plain,(
    ! [A_17,B_18] :
      ( r1_tarski(A_17,B_18)
      | ~ m1_subset_1(A_17,k1_zfmisc_1(B_18)) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_81,plain,(
    ! [A_44,B_45,C_46] :
      ( r1_tarski(k9_subset_1(A_44,B_45,C_46),A_44)
      | ~ m1_subset_1(C_46,k1_zfmisc_1(A_44)) ) ),
    inference(resolution,[status(thm)],[c_77,c_18])).

tff(c_209,plain,(
    ! [B_68,B_67] :
      ( r1_tarski(k3_xboole_0(B_68,B_67),B_67)
      | ~ m1_subset_1(B_67,k1_zfmisc_1(B_67)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_203,c_81])).

tff(c_86,plain,(
    ! [A_50,B_51,C_52] :
      ( r1_tarski(A_50,k3_xboole_0(B_51,C_52))
      | ~ r1_tarski(A_50,C_52)
      | ~ r1_tarski(A_50,B_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_357,plain,(
    ! [B_95,C_96,A_97] :
      ( k3_xboole_0(B_95,C_96) = A_97
      | ~ r1_tarski(k3_xboole_0(B_95,C_96),A_97)
      | ~ r1_tarski(A_97,C_96)
      | ~ r1_tarski(A_97,B_95) ) ),
    inference(resolution,[status(thm)],[c_86,c_2])).

tff(c_366,plain,(
    ! [B_68,B_67] :
      ( k3_xboole_0(B_68,B_67) = B_67
      | ~ r1_tarski(B_67,B_67)
      | ~ r1_tarski(B_67,B_68)
      | ~ m1_subset_1(B_67,k1_zfmisc_1(B_67)) ) ),
    inference(resolution,[status(thm)],[c_209,c_357])).

tff(c_395,plain,(
    ! [B_98,B_99] :
      ( k3_xboole_0(B_98,B_99) = B_99
      | ~ r1_tarski(B_99,B_98)
      | ~ m1_subset_1(B_99,k1_zfmisc_1(B_99)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_366])).

tff(c_433,plain,
    ( k3_xboole_0(u1_struct_0('#skF_1'),'#skF_3') = '#skF_3'
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_42,c_395])).

tff(c_633,plain,(
    ~ m1_subset_1('#skF_3',k1_zfmisc_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_433])).

tff(c_675,plain,(
    ~ r1_tarski('#skF_3','#skF_3') ),
    inference(resolution,[status(thm)],[c_20,c_633])).

tff(c_679,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_675])).

tff(c_681,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_433])).

tff(c_32,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_104,plain,(
    ! [B_56] : k9_subset_1(u1_struct_0('#skF_1'),B_56,'#skF_3') = k3_xboole_0(B_56,'#skF_3') ),
    inference(resolution,[status(thm)],[c_28,c_90])).

tff(c_12,plain,(
    ! [A_9,B_10,C_11] :
      ( m1_subset_1(k9_subset_1(A_9,B_10,C_11),k1_zfmisc_1(A_9))
      | ~ m1_subset_1(C_11,k1_zfmisc_1(A_9)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_113,plain,(
    ! [B_56] :
      ( m1_subset_1(k3_xboole_0(B_56,'#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_104,c_12])).

tff(c_121,plain,(
    ! [B_56] : m1_subset_1(k3_xboole_0(B_56,'#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_113])).

tff(c_24,plain,(
    ! [A_21,B_25,C_27] :
      ( r1_tarski(k2_pre_topc(A_21,B_25),k2_pre_topc(A_21,C_27))
      | ~ r1_tarski(B_25,C_27)
      | ~ m1_subset_1(C_27,k1_zfmisc_1(u1_struct_0(A_21)))
      | ~ m1_subset_1(B_25,k1_zfmisc_1(u1_struct_0(A_21)))
      | ~ l1_pre_topc(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_8,plain,(
    ! [A_3,C_5,B_4] :
      ( r1_tarski(k3_xboole_0(A_3,C_5),B_4)
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_30,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_10,plain,(
    ! [A_6,B_7,C_8] :
      ( r1_tarski(A_6,k3_xboole_0(B_7,C_8))
      | ~ r1_tarski(A_6,C_8)
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_159,plain,(
    ! [A_61,B_62] :
      ( m1_subset_1(k2_pre_topc(A_61,B_62),k1_zfmisc_1(u1_struct_0(A_61)))
      | ~ m1_subset_1(B_62,k1_zfmisc_1(u1_struct_0(A_61)))
      | ~ l1_pre_topc(A_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_14,plain,(
    ! [A_12,B_13,C_14] :
      ( k9_subset_1(A_12,B_13,C_14) = k3_xboole_0(B_13,C_14)
      | ~ m1_subset_1(C_14,k1_zfmisc_1(A_12)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_1352,plain,(
    ! [A_131,B_132,B_133] :
      ( k9_subset_1(u1_struct_0(A_131),B_132,k2_pre_topc(A_131,B_133)) = k3_xboole_0(B_132,k2_pre_topc(A_131,B_133))
      | ~ m1_subset_1(B_133,k1_zfmisc_1(u1_struct_0(A_131)))
      | ~ l1_pre_topc(A_131) ) ),
    inference(resolution,[status(thm)],[c_159,c_14])).

tff(c_1373,plain,(
    ! [B_132] :
      ( k9_subset_1(u1_struct_0('#skF_1'),B_132,k2_pre_topc('#skF_1','#skF_3')) = k3_xboole_0(B_132,k2_pre_topc('#skF_1','#skF_3'))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_28,c_1352])).

tff(c_1394,plain,(
    ! [B_132] : k9_subset_1(u1_struct_0('#skF_1'),B_132,k2_pre_topc('#skF_1','#skF_3')) = k3_xboole_0(B_132,k2_pre_topc('#skF_1','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_1373])).

tff(c_101,plain,(
    ! [B_54] : k9_subset_1(u1_struct_0('#skF_1'),B_54,'#skF_3') = k3_xboole_0(B_54,'#skF_3') ),
    inference(resolution,[status(thm)],[c_28,c_90])).

tff(c_26,plain,(
    ~ r1_tarski(k2_pre_topc('#skF_1',k9_subset_1(u1_struct_0('#skF_1'),'#skF_2','#skF_3')),k9_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2'),k2_pre_topc('#skF_1','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_103,plain,(
    ~ r1_tarski(k2_pre_topc('#skF_1',k3_xboole_0('#skF_2','#skF_3')),k9_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2'),k2_pre_topc('#skF_1','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_101,c_26])).

tff(c_1601,plain,(
    ~ r1_tarski(k2_pre_topc('#skF_1',k3_xboole_0('#skF_2','#skF_3')),k3_xboole_0(k2_pre_topc('#skF_1','#skF_2'),k2_pre_topc('#skF_1','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1394,c_103])).

tff(c_2389,plain,
    ( ~ r1_tarski(k2_pre_topc('#skF_1',k3_xboole_0('#skF_2','#skF_3')),k2_pre_topc('#skF_1','#skF_3'))
    | ~ r1_tarski(k2_pre_topc('#skF_1',k3_xboole_0('#skF_2','#skF_3')),k2_pre_topc('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_10,c_1601])).

tff(c_4394,plain,(
    ~ r1_tarski(k2_pre_topc('#skF_1',k3_xboole_0('#skF_2','#skF_3')),k2_pre_topc('#skF_1','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_2389])).

tff(c_4746,plain,
    ( ~ r1_tarski(k3_xboole_0('#skF_2','#skF_3'),'#skF_2')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_subset_1(k3_xboole_0('#skF_2','#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_24,c_4394])).

tff(c_4749,plain,(
    ~ r1_tarski(k3_xboole_0('#skF_2','#skF_3'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_121,c_30,c_4746])).

tff(c_4752,plain,(
    ~ r1_tarski('#skF_2','#skF_2') ),
    inference(resolution,[status(thm)],[c_8,c_4749])).

tff(c_4756,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_4752])).

tff(c_4757,plain,(
    ~ r1_tarski(k2_pre_topc('#skF_1',k3_xboole_0('#skF_2','#skF_3')),k2_pre_topc('#skF_1','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_2389])).

tff(c_5110,plain,
    ( ~ r1_tarski(k3_xboole_0('#skF_2','#skF_3'),'#skF_3')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_subset_1(k3_xboole_0('#skF_2','#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_24,c_4757])).

tff(c_5113,plain,(
    ~ r1_tarski(k3_xboole_0('#skF_2','#skF_3'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_121,c_28,c_5110])).

tff(c_5116,plain,(
    ~ m1_subset_1('#skF_3',k1_zfmisc_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_209,c_5113])).

tff(c_5123,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_681,c_5116])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n013.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 11:03:24 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.81/2.09  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.81/2.09  
% 5.81/2.09  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.81/2.09  %$ r1_tarski > m1_subset_1 > l1_pre_topc > k9_subset_1 > k3_xboole_0 > k2_tarski > k2_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_setfam_1 > #skF_2 > #skF_3 > #skF_1
% 5.81/2.09  
% 5.81/2.09  %Foreground sorts:
% 5.81/2.09  
% 5.81/2.09  
% 5.81/2.09  %Background operators:
% 5.81/2.09  
% 5.81/2.09  
% 5.81/2.09  %Foreground operators:
% 5.81/2.09  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.81/2.09  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 5.81/2.09  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.81/2.09  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 5.81/2.09  tff('#skF_2', type, '#skF_2': $i).
% 5.81/2.09  tff('#skF_3', type, '#skF_3': $i).
% 5.81/2.09  tff('#skF_1', type, '#skF_1': $i).
% 5.81/2.09  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.81/2.09  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.81/2.09  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.81/2.09  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 5.81/2.09  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 5.81/2.09  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 5.81/2.09  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 5.81/2.09  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.81/2.09  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 5.81/2.10  
% 5.81/2.11  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 5.81/2.11  tff(f_55, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 5.81/2.11  tff(f_84, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => r1_tarski(k2_pre_topc(A, k9_subset_1(u1_struct_0(A), B, C)), k9_subset_1(u1_struct_0(A), k2_pre_topc(A, B), k2_pre_topc(A, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t51_pre_topc)).
% 5.81/2.11  tff(f_49, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 5.81/2.11  tff(f_45, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => m1_subset_1(k9_subset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k9_subset_1)).
% 5.81/2.11  tff(f_41, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(A, C)) => r1_tarski(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t19_xboole_1)).
% 5.81/2.11  tff(f_73, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (r1_tarski(B, C) => r1_tarski(k2_pre_topc(A, B), k2_pre_topc(A, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_pre_topc)).
% 5.81/2.11  tff(f_35, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(k3_xboole_0(A, C), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t108_xboole_1)).
% 5.81/2.11  tff(f_61, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_pre_topc(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_pre_topc)).
% 5.81/2.11  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.81/2.11  tff(c_20, plain, (![A_17, B_18]: (m1_subset_1(A_17, k1_zfmisc_1(B_18)) | ~r1_tarski(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_55])).
% 5.81/2.11  tff(c_28, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_84])).
% 5.81/2.11  tff(c_35, plain, (![A_33, B_34]: (r1_tarski(A_33, B_34) | ~m1_subset_1(A_33, k1_zfmisc_1(B_34)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 5.81/2.11  tff(c_42, plain, (r1_tarski('#skF_3', u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_28, c_35])).
% 5.81/2.11  tff(c_90, plain, (![A_53, B_54, C_55]: (k9_subset_1(A_53, B_54, C_55)=k3_xboole_0(B_54, C_55) | ~m1_subset_1(C_55, k1_zfmisc_1(A_53)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 5.81/2.11  tff(c_176, plain, (![B_64, B_65, A_66]: (k9_subset_1(B_64, B_65, A_66)=k3_xboole_0(B_65, A_66) | ~r1_tarski(A_66, B_64))), inference(resolution, [status(thm)], [c_20, c_90])).
% 5.81/2.11  tff(c_203, plain, (![B_67, B_68]: (k9_subset_1(B_67, B_68, B_67)=k3_xboole_0(B_68, B_67))), inference(resolution, [status(thm)], [c_6, c_176])).
% 5.81/2.11  tff(c_77, plain, (![A_44, B_45, C_46]: (m1_subset_1(k9_subset_1(A_44, B_45, C_46), k1_zfmisc_1(A_44)) | ~m1_subset_1(C_46, k1_zfmisc_1(A_44)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 5.81/2.11  tff(c_18, plain, (![A_17, B_18]: (r1_tarski(A_17, B_18) | ~m1_subset_1(A_17, k1_zfmisc_1(B_18)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 5.81/2.11  tff(c_81, plain, (![A_44, B_45, C_46]: (r1_tarski(k9_subset_1(A_44, B_45, C_46), A_44) | ~m1_subset_1(C_46, k1_zfmisc_1(A_44)))), inference(resolution, [status(thm)], [c_77, c_18])).
% 5.81/2.11  tff(c_209, plain, (![B_68, B_67]: (r1_tarski(k3_xboole_0(B_68, B_67), B_67) | ~m1_subset_1(B_67, k1_zfmisc_1(B_67)))), inference(superposition, [status(thm), theory('equality')], [c_203, c_81])).
% 5.81/2.11  tff(c_86, plain, (![A_50, B_51, C_52]: (r1_tarski(A_50, k3_xboole_0(B_51, C_52)) | ~r1_tarski(A_50, C_52) | ~r1_tarski(A_50, B_51))), inference(cnfTransformation, [status(thm)], [f_41])).
% 5.81/2.11  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.81/2.11  tff(c_357, plain, (![B_95, C_96, A_97]: (k3_xboole_0(B_95, C_96)=A_97 | ~r1_tarski(k3_xboole_0(B_95, C_96), A_97) | ~r1_tarski(A_97, C_96) | ~r1_tarski(A_97, B_95))), inference(resolution, [status(thm)], [c_86, c_2])).
% 5.81/2.11  tff(c_366, plain, (![B_68, B_67]: (k3_xboole_0(B_68, B_67)=B_67 | ~r1_tarski(B_67, B_67) | ~r1_tarski(B_67, B_68) | ~m1_subset_1(B_67, k1_zfmisc_1(B_67)))), inference(resolution, [status(thm)], [c_209, c_357])).
% 5.81/2.11  tff(c_395, plain, (![B_98, B_99]: (k3_xboole_0(B_98, B_99)=B_99 | ~r1_tarski(B_99, B_98) | ~m1_subset_1(B_99, k1_zfmisc_1(B_99)))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_366])).
% 5.81/2.11  tff(c_433, plain, (k3_xboole_0(u1_struct_0('#skF_1'), '#skF_3')='#skF_3' | ~m1_subset_1('#skF_3', k1_zfmisc_1('#skF_3'))), inference(resolution, [status(thm)], [c_42, c_395])).
% 5.81/2.11  tff(c_633, plain, (~m1_subset_1('#skF_3', k1_zfmisc_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_433])).
% 5.81/2.11  tff(c_675, plain, (~r1_tarski('#skF_3', '#skF_3')), inference(resolution, [status(thm)], [c_20, c_633])).
% 5.81/2.11  tff(c_679, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_675])).
% 5.81/2.11  tff(c_681, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_3'))), inference(splitRight, [status(thm)], [c_433])).
% 5.81/2.11  tff(c_32, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_84])).
% 5.81/2.11  tff(c_104, plain, (![B_56]: (k9_subset_1(u1_struct_0('#skF_1'), B_56, '#skF_3')=k3_xboole_0(B_56, '#skF_3'))), inference(resolution, [status(thm)], [c_28, c_90])).
% 5.81/2.11  tff(c_12, plain, (![A_9, B_10, C_11]: (m1_subset_1(k9_subset_1(A_9, B_10, C_11), k1_zfmisc_1(A_9)) | ~m1_subset_1(C_11, k1_zfmisc_1(A_9)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 5.81/2.11  tff(c_113, plain, (![B_56]: (m1_subset_1(k3_xboole_0(B_56, '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(superposition, [status(thm), theory('equality')], [c_104, c_12])).
% 5.81/2.11  tff(c_121, plain, (![B_56]: (m1_subset_1(k3_xboole_0(B_56, '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_113])).
% 5.81/2.11  tff(c_24, plain, (![A_21, B_25, C_27]: (r1_tarski(k2_pre_topc(A_21, B_25), k2_pre_topc(A_21, C_27)) | ~r1_tarski(B_25, C_27) | ~m1_subset_1(C_27, k1_zfmisc_1(u1_struct_0(A_21))) | ~m1_subset_1(B_25, k1_zfmisc_1(u1_struct_0(A_21))) | ~l1_pre_topc(A_21))), inference(cnfTransformation, [status(thm)], [f_73])).
% 5.81/2.11  tff(c_8, plain, (![A_3, C_5, B_4]: (r1_tarski(k3_xboole_0(A_3, C_5), B_4) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 5.81/2.11  tff(c_30, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_84])).
% 5.81/2.11  tff(c_10, plain, (![A_6, B_7, C_8]: (r1_tarski(A_6, k3_xboole_0(B_7, C_8)) | ~r1_tarski(A_6, C_8) | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_41])).
% 5.81/2.11  tff(c_159, plain, (![A_61, B_62]: (m1_subset_1(k2_pre_topc(A_61, B_62), k1_zfmisc_1(u1_struct_0(A_61))) | ~m1_subset_1(B_62, k1_zfmisc_1(u1_struct_0(A_61))) | ~l1_pre_topc(A_61))), inference(cnfTransformation, [status(thm)], [f_61])).
% 5.81/2.11  tff(c_14, plain, (![A_12, B_13, C_14]: (k9_subset_1(A_12, B_13, C_14)=k3_xboole_0(B_13, C_14) | ~m1_subset_1(C_14, k1_zfmisc_1(A_12)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 5.81/2.11  tff(c_1352, plain, (![A_131, B_132, B_133]: (k9_subset_1(u1_struct_0(A_131), B_132, k2_pre_topc(A_131, B_133))=k3_xboole_0(B_132, k2_pre_topc(A_131, B_133)) | ~m1_subset_1(B_133, k1_zfmisc_1(u1_struct_0(A_131))) | ~l1_pre_topc(A_131))), inference(resolution, [status(thm)], [c_159, c_14])).
% 5.81/2.11  tff(c_1373, plain, (![B_132]: (k9_subset_1(u1_struct_0('#skF_1'), B_132, k2_pre_topc('#skF_1', '#skF_3'))=k3_xboole_0(B_132, k2_pre_topc('#skF_1', '#skF_3')) | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_28, c_1352])).
% 5.81/2.11  tff(c_1394, plain, (![B_132]: (k9_subset_1(u1_struct_0('#skF_1'), B_132, k2_pre_topc('#skF_1', '#skF_3'))=k3_xboole_0(B_132, k2_pre_topc('#skF_1', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_1373])).
% 5.81/2.11  tff(c_101, plain, (![B_54]: (k9_subset_1(u1_struct_0('#skF_1'), B_54, '#skF_3')=k3_xboole_0(B_54, '#skF_3'))), inference(resolution, [status(thm)], [c_28, c_90])).
% 5.81/2.11  tff(c_26, plain, (~r1_tarski(k2_pre_topc('#skF_1', k9_subset_1(u1_struct_0('#skF_1'), '#skF_2', '#skF_3')), k9_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_2'), k2_pre_topc('#skF_1', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_84])).
% 5.81/2.11  tff(c_103, plain, (~r1_tarski(k2_pre_topc('#skF_1', k3_xboole_0('#skF_2', '#skF_3')), k9_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_2'), k2_pre_topc('#skF_1', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_101, c_26])).
% 5.81/2.11  tff(c_1601, plain, (~r1_tarski(k2_pre_topc('#skF_1', k3_xboole_0('#skF_2', '#skF_3')), k3_xboole_0(k2_pre_topc('#skF_1', '#skF_2'), k2_pre_topc('#skF_1', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_1394, c_103])).
% 5.81/2.11  tff(c_2389, plain, (~r1_tarski(k2_pre_topc('#skF_1', k3_xboole_0('#skF_2', '#skF_3')), k2_pre_topc('#skF_1', '#skF_3')) | ~r1_tarski(k2_pre_topc('#skF_1', k3_xboole_0('#skF_2', '#skF_3')), k2_pre_topc('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_10, c_1601])).
% 5.81/2.11  tff(c_4394, plain, (~r1_tarski(k2_pre_topc('#skF_1', k3_xboole_0('#skF_2', '#skF_3')), k2_pre_topc('#skF_1', '#skF_2'))), inference(splitLeft, [status(thm)], [c_2389])).
% 5.81/2.11  tff(c_4746, plain, (~r1_tarski(k3_xboole_0('#skF_2', '#skF_3'), '#skF_2') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1(k3_xboole_0('#skF_2', '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_24, c_4394])).
% 5.81/2.11  tff(c_4749, plain, (~r1_tarski(k3_xboole_0('#skF_2', '#skF_3'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_121, c_30, c_4746])).
% 5.81/2.11  tff(c_4752, plain, (~r1_tarski('#skF_2', '#skF_2')), inference(resolution, [status(thm)], [c_8, c_4749])).
% 5.81/2.11  tff(c_4756, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_4752])).
% 5.81/2.11  tff(c_4757, plain, (~r1_tarski(k2_pre_topc('#skF_1', k3_xboole_0('#skF_2', '#skF_3')), k2_pre_topc('#skF_1', '#skF_3'))), inference(splitRight, [status(thm)], [c_2389])).
% 5.81/2.11  tff(c_5110, plain, (~r1_tarski(k3_xboole_0('#skF_2', '#skF_3'), '#skF_3') | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1(k3_xboole_0('#skF_2', '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_24, c_4757])).
% 5.81/2.11  tff(c_5113, plain, (~r1_tarski(k3_xboole_0('#skF_2', '#skF_3'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_121, c_28, c_5110])).
% 5.81/2.11  tff(c_5116, plain, (~m1_subset_1('#skF_3', k1_zfmisc_1('#skF_3'))), inference(resolution, [status(thm)], [c_209, c_5113])).
% 5.81/2.11  tff(c_5123, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_681, c_5116])).
% 5.81/2.11  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.81/2.11  
% 5.81/2.11  Inference rules
% 5.81/2.11  ----------------------
% 5.81/2.11  #Ref     : 0
% 5.81/2.11  #Sup     : 1249
% 5.81/2.11  #Fact    : 0
% 5.81/2.11  #Define  : 0
% 5.81/2.11  #Split   : 9
% 5.81/2.11  #Chain   : 0
% 5.81/2.11  #Close   : 0
% 5.81/2.11  
% 5.81/2.11  Ordering : KBO
% 5.81/2.11  
% 5.81/2.11  Simplification rules
% 5.81/2.11  ----------------------
% 5.81/2.11  #Subsume      : 291
% 5.81/2.11  #Demod        : 663
% 5.81/2.11  #Tautology    : 533
% 5.81/2.11  #SimpNegUnit  : 0
% 5.81/2.11  #BackRed      : 2
% 5.81/2.11  
% 5.81/2.11  #Partial instantiations: 0
% 5.81/2.11  #Strategies tried      : 1
% 5.81/2.11  
% 5.81/2.11  Timing (in seconds)
% 5.81/2.11  ----------------------
% 5.97/2.11  Preprocessing        : 0.32
% 5.97/2.11  Parsing              : 0.17
% 5.97/2.11  CNF conversion       : 0.02
% 5.97/2.11  Main loop            : 1.04
% 5.97/2.11  Inferencing          : 0.32
% 5.97/2.11  Reduction            : 0.39
% 5.97/2.11  Demodulation         : 0.28
% 5.97/2.11  BG Simplification    : 0.04
% 5.97/2.11  Subsumption          : 0.22
% 5.97/2.11  Abstraction          : 0.06
% 5.97/2.11  MUC search           : 0.00
% 5.97/2.11  Cooper               : 0.00
% 5.97/2.11  Total                : 1.39
% 5.97/2.11  Index Insertion      : 0.00
% 5.97/2.11  Index Deletion       : 0.00
% 5.97/2.11  Index Matching       : 0.00
% 5.97/2.12  BG Taut test         : 0.00
%------------------------------------------------------------------------------
