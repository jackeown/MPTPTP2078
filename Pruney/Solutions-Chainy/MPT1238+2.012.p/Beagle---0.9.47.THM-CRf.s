%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:20:38 EST 2020

% Result     : Theorem 3.13s
% Output     : CNFRefutation 3.48s
% Verified   : 
% Statistics : Number of formulae       :   68 ( 189 expanded)
%              Number of leaves         :   22 (  74 expanded)
%              Depth                    :   15
%              Number of atoms          :  107 ( 391 expanded)
%              Number of equality atoms :   12 (  47 expanded)
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

tff(f_74,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => r1_tarski(k4_subset_1(u1_struct_0(A),k1_tops_1(A,B),k1_tops_1(A,C)),k1_tops_1(A,k4_subset_1(u1_struct_0(A),B,C))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_tops_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(C,B) )
     => r1_tarski(k2_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_29,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_63,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( r1_tarski(B,C)
               => r1_tarski(k1_tops_1(A,B),k1_tops_1(A,C)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_tops_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k1_tops_1(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_tops_1)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(c_20,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_65,plain,(
    ! [A_30,B_31] :
      ( r1_tarski(A_30,B_31)
      | ~ m1_subset_1(A_30,k1_zfmisc_1(B_31)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_72,plain,(
    r1_tarski('#skF_3',u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_20,c_65])).

tff(c_22,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_73,plain,(
    r1_tarski('#skF_2',u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_22,c_65])).

tff(c_6,plain,(
    ! [A_5,C_7,B_6] :
      ( r1_tarski(k2_xboole_0(A_5,C_7),B_6)
      | ~ r1_tarski(C_7,B_6)
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_12,plain,(
    ! [A_11,B_12] :
      ( m1_subset_1(A_11,k1_zfmisc_1(B_12))
      | ~ r1_tarski(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_24,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_26,plain,(
    ! [B_28,A_29] : k2_xboole_0(B_28,A_29) = k2_xboole_0(A_29,B_28) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_4,plain,(
    ! [A_3,B_4] : r1_tarski(A_3,k2_xboole_0(A_3,B_4)) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_44,plain,(
    ! [B_28,A_29] : r1_tarski(B_28,k2_xboole_0(A_29,B_28)) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_4])).

tff(c_16,plain,(
    ! [A_15,B_19,C_21] :
      ( r1_tarski(k1_tops_1(A_15,B_19),k1_tops_1(A_15,C_21))
      | ~ r1_tarski(B_19,C_21)
      | ~ m1_subset_1(C_21,k1_zfmisc_1(u1_struct_0(A_15)))
      | ~ m1_subset_1(B_19,k1_zfmisc_1(u1_struct_0(A_15)))
      | ~ l1_pre_topc(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_96,plain,(
    ! [A_39,B_40] :
      ( m1_subset_1(k1_tops_1(A_39,B_40),k1_zfmisc_1(u1_struct_0(A_39)))
      | ~ m1_subset_1(B_40,k1_zfmisc_1(u1_struct_0(A_39)))
      | ~ l1_pre_topc(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_10,plain,(
    ! [A_11,B_12] :
      ( r1_tarski(A_11,B_12)
      | ~ m1_subset_1(A_11,k1_zfmisc_1(B_12)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_100,plain,(
    ! [A_39,B_40] :
      ( r1_tarski(k1_tops_1(A_39,B_40),u1_struct_0(A_39))
      | ~ m1_subset_1(B_40,k1_zfmisc_1(u1_struct_0(A_39)))
      | ~ l1_pre_topc(A_39) ) ),
    inference(resolution,[status(thm)],[c_96,c_10])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_14,plain,(
    ! [A_13,B_14] :
      ( m1_subset_1(k1_tops_1(A_13,B_14),k1_zfmisc_1(u1_struct_0(A_13)))
      | ~ m1_subset_1(B_14,k1_zfmisc_1(u1_struct_0(A_13)))
      | ~ l1_pre_topc(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_102,plain,(
    ! [A_43,B_44,C_45] :
      ( k4_subset_1(A_43,B_44,C_45) = k2_xboole_0(B_44,C_45)
      | ~ m1_subset_1(C_45,k1_zfmisc_1(A_43))
      | ~ m1_subset_1(B_44,k1_zfmisc_1(A_43)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_386,plain,(
    ! [A_70,B_71,B_72] :
      ( k4_subset_1(u1_struct_0(A_70),B_71,k1_tops_1(A_70,B_72)) = k2_xboole_0(B_71,k1_tops_1(A_70,B_72))
      | ~ m1_subset_1(B_71,k1_zfmisc_1(u1_struct_0(A_70)))
      | ~ m1_subset_1(B_72,k1_zfmisc_1(u1_struct_0(A_70)))
      | ~ l1_pre_topc(A_70) ) ),
    inference(resolution,[status(thm)],[c_14,c_102])).

tff(c_773,plain,(
    ! [A_96,A_97,B_98] :
      ( k4_subset_1(u1_struct_0(A_96),A_97,k1_tops_1(A_96,B_98)) = k2_xboole_0(A_97,k1_tops_1(A_96,B_98))
      | ~ m1_subset_1(B_98,k1_zfmisc_1(u1_struct_0(A_96)))
      | ~ l1_pre_topc(A_96)
      | ~ r1_tarski(A_97,u1_struct_0(A_96)) ) ),
    inference(resolution,[status(thm)],[c_12,c_386])).

tff(c_780,plain,(
    ! [A_97] :
      ( k4_subset_1(u1_struct_0('#skF_1'),A_97,k1_tops_1('#skF_1','#skF_3')) = k2_xboole_0(A_97,k1_tops_1('#skF_1','#skF_3'))
      | ~ l1_pre_topc('#skF_1')
      | ~ r1_tarski(A_97,u1_struct_0('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_20,c_773])).

tff(c_791,plain,(
    ! [A_99] :
      ( k4_subset_1(u1_struct_0('#skF_1'),A_99,k1_tops_1('#skF_1','#skF_3')) = k2_xboole_0(A_99,k1_tops_1('#skF_1','#skF_3'))
      | ~ r1_tarski(A_99,u1_struct_0('#skF_1')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_780])).

tff(c_115,plain,(
    ! [B_46] :
      ( k4_subset_1(u1_struct_0('#skF_1'),B_46,'#skF_3') = k2_xboole_0(B_46,'#skF_3')
      | ~ m1_subset_1(B_46,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(resolution,[status(thm)],[c_20,c_102])).

tff(c_129,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_2','#skF_3') = k2_xboole_0('#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_22,c_115])).

tff(c_136,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_2','#skF_3') = k2_xboole_0('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_129])).

tff(c_18,plain,(
    ~ r1_tarski(k4_subset_1(u1_struct_0('#skF_1'),k1_tops_1('#skF_1','#skF_2'),k1_tops_1('#skF_1','#skF_3')),k1_tops_1('#skF_1',k4_subset_1(u1_struct_0('#skF_1'),'#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_139,plain,(
    ~ r1_tarski(k4_subset_1(u1_struct_0('#skF_1'),k1_tops_1('#skF_1','#skF_2'),k1_tops_1('#skF_1','#skF_3')),k1_tops_1('#skF_1',k2_xboole_0('#skF_3','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_136,c_18])).

tff(c_811,plain,
    ( ~ r1_tarski(k2_xboole_0(k1_tops_1('#skF_1','#skF_2'),k1_tops_1('#skF_1','#skF_3')),k1_tops_1('#skF_1',k2_xboole_0('#skF_3','#skF_2')))
    | ~ r1_tarski(k1_tops_1('#skF_1','#skF_2'),u1_struct_0('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_791,c_139])).

tff(c_842,plain,
    ( ~ r1_tarski(k2_xboole_0(k1_tops_1('#skF_1','#skF_3'),k1_tops_1('#skF_1','#skF_2')),k1_tops_1('#skF_1',k2_xboole_0('#skF_3','#skF_2')))
    | ~ r1_tarski(k1_tops_1('#skF_1','#skF_2'),u1_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_811])).

tff(c_917,plain,(
    ~ r1_tarski(k1_tops_1('#skF_1','#skF_2'),u1_struct_0('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_842])).

tff(c_941,plain,
    ( ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_100,c_917])).

tff(c_945,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_22,c_941])).

tff(c_946,plain,(
    ~ r1_tarski(k2_xboole_0(k1_tops_1('#skF_1','#skF_3'),k1_tops_1('#skF_1','#skF_2')),k1_tops_1('#skF_1',k2_xboole_0('#skF_3','#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_842])).

tff(c_974,plain,
    ( ~ r1_tarski(k1_tops_1('#skF_1','#skF_2'),k1_tops_1('#skF_1',k2_xboole_0('#skF_3','#skF_2')))
    | ~ r1_tarski(k1_tops_1('#skF_1','#skF_3'),k1_tops_1('#skF_1',k2_xboole_0('#skF_3','#skF_2'))) ),
    inference(resolution,[status(thm)],[c_6,c_946])).

tff(c_975,plain,(
    ~ r1_tarski(k1_tops_1('#skF_1','#skF_3'),k1_tops_1('#skF_1',k2_xboole_0('#skF_3','#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_974])).

tff(c_978,plain,
    ( ~ r1_tarski('#skF_3',k2_xboole_0('#skF_3','#skF_2'))
    | ~ m1_subset_1(k2_xboole_0('#skF_3','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_16,c_975])).

tff(c_981,plain,(
    ~ m1_subset_1(k2_xboole_0('#skF_3','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_20,c_4,c_978])).

tff(c_1003,plain,(
    ~ r1_tarski(k2_xboole_0('#skF_3','#skF_2'),u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_12,c_981])).

tff(c_1006,plain,
    ( ~ r1_tarski('#skF_2',u1_struct_0('#skF_1'))
    | ~ r1_tarski('#skF_3',u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_6,c_1003])).

tff(c_1010,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_73,c_1006])).

tff(c_1011,plain,(
    ~ r1_tarski(k1_tops_1('#skF_1','#skF_2'),k1_tops_1('#skF_1',k2_xboole_0('#skF_3','#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_974])).

tff(c_1015,plain,
    ( ~ r1_tarski('#skF_2',k2_xboole_0('#skF_3','#skF_2'))
    | ~ m1_subset_1(k2_xboole_0('#skF_3','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_16,c_1011])).

tff(c_1018,plain,(
    ~ m1_subset_1(k2_xboole_0('#skF_3','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_22,c_44,c_1015])).

tff(c_1043,plain,(
    ~ r1_tarski(k2_xboole_0('#skF_3','#skF_2'),u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_12,c_1018])).

tff(c_1046,plain,
    ( ~ r1_tarski('#skF_2',u1_struct_0('#skF_1'))
    | ~ r1_tarski('#skF_3',u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_6,c_1043])).

tff(c_1050,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_73,c_1046])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:48:38 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.13/1.69  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.48/1.70  
% 3.48/1.70  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.48/1.70  %$ r1_tarski > m1_subset_1 > l1_pre_topc > k4_subset_1 > k2_xboole_0 > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1
% 3.48/1.70  
% 3.48/1.70  %Foreground sorts:
% 3.48/1.70  
% 3.48/1.70  
% 3.48/1.70  %Background operators:
% 3.48/1.70  
% 3.48/1.70  
% 3.48/1.70  %Foreground operators:
% 3.48/1.70  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.48/1.70  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.48/1.70  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.48/1.70  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 3.48/1.70  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 3.48/1.70  tff('#skF_2', type, '#skF_2': $i).
% 3.48/1.70  tff('#skF_3', type, '#skF_3': $i).
% 3.48/1.70  tff('#skF_1', type, '#skF_1': $i).
% 3.48/1.70  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.48/1.70  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.48/1.70  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.48/1.70  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.48/1.70  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.48/1.70  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.48/1.70  
% 3.48/1.72  tff(f_74, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => r1_tarski(k4_subset_1(u1_struct_0(A), k1_tops_1(A, B), k1_tops_1(A, C)), k1_tops_1(A, k4_subset_1(u1_struct_0(A), B, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_tops_1)).
% 3.48/1.72  tff(f_45, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 3.48/1.72  tff(f_35, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(C, B)) => r1_tarski(k2_xboole_0(A, C), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_xboole_1)).
% 3.48/1.72  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 3.48/1.72  tff(f_29, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 3.48/1.72  tff(f_63, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (r1_tarski(B, C) => r1_tarski(k1_tops_1(A, B), k1_tops_1(A, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_tops_1)).
% 3.48/1.72  tff(f_51, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k1_tops_1(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_tops_1)).
% 3.48/1.72  tff(f_41, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 3.48/1.72  tff(c_20, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.48/1.72  tff(c_65, plain, (![A_30, B_31]: (r1_tarski(A_30, B_31) | ~m1_subset_1(A_30, k1_zfmisc_1(B_31)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.48/1.72  tff(c_72, plain, (r1_tarski('#skF_3', u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_20, c_65])).
% 3.48/1.72  tff(c_22, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.48/1.72  tff(c_73, plain, (r1_tarski('#skF_2', u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_22, c_65])).
% 3.48/1.72  tff(c_6, plain, (![A_5, C_7, B_6]: (r1_tarski(k2_xboole_0(A_5, C_7), B_6) | ~r1_tarski(C_7, B_6) | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.48/1.72  tff(c_12, plain, (![A_11, B_12]: (m1_subset_1(A_11, k1_zfmisc_1(B_12)) | ~r1_tarski(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.48/1.72  tff(c_24, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.48/1.72  tff(c_26, plain, (![B_28, A_29]: (k2_xboole_0(B_28, A_29)=k2_xboole_0(A_29, B_28))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.48/1.72  tff(c_4, plain, (![A_3, B_4]: (r1_tarski(A_3, k2_xboole_0(A_3, B_4)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.48/1.72  tff(c_44, plain, (![B_28, A_29]: (r1_tarski(B_28, k2_xboole_0(A_29, B_28)))), inference(superposition, [status(thm), theory('equality')], [c_26, c_4])).
% 3.48/1.72  tff(c_16, plain, (![A_15, B_19, C_21]: (r1_tarski(k1_tops_1(A_15, B_19), k1_tops_1(A_15, C_21)) | ~r1_tarski(B_19, C_21) | ~m1_subset_1(C_21, k1_zfmisc_1(u1_struct_0(A_15))) | ~m1_subset_1(B_19, k1_zfmisc_1(u1_struct_0(A_15))) | ~l1_pre_topc(A_15))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.48/1.72  tff(c_96, plain, (![A_39, B_40]: (m1_subset_1(k1_tops_1(A_39, B_40), k1_zfmisc_1(u1_struct_0(A_39))) | ~m1_subset_1(B_40, k1_zfmisc_1(u1_struct_0(A_39))) | ~l1_pre_topc(A_39))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.48/1.72  tff(c_10, plain, (![A_11, B_12]: (r1_tarski(A_11, B_12) | ~m1_subset_1(A_11, k1_zfmisc_1(B_12)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.48/1.72  tff(c_100, plain, (![A_39, B_40]: (r1_tarski(k1_tops_1(A_39, B_40), u1_struct_0(A_39)) | ~m1_subset_1(B_40, k1_zfmisc_1(u1_struct_0(A_39))) | ~l1_pre_topc(A_39))), inference(resolution, [status(thm)], [c_96, c_10])).
% 3.48/1.72  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.48/1.72  tff(c_14, plain, (![A_13, B_14]: (m1_subset_1(k1_tops_1(A_13, B_14), k1_zfmisc_1(u1_struct_0(A_13))) | ~m1_subset_1(B_14, k1_zfmisc_1(u1_struct_0(A_13))) | ~l1_pre_topc(A_13))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.48/1.72  tff(c_102, plain, (![A_43, B_44, C_45]: (k4_subset_1(A_43, B_44, C_45)=k2_xboole_0(B_44, C_45) | ~m1_subset_1(C_45, k1_zfmisc_1(A_43)) | ~m1_subset_1(B_44, k1_zfmisc_1(A_43)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.48/1.72  tff(c_386, plain, (![A_70, B_71, B_72]: (k4_subset_1(u1_struct_0(A_70), B_71, k1_tops_1(A_70, B_72))=k2_xboole_0(B_71, k1_tops_1(A_70, B_72)) | ~m1_subset_1(B_71, k1_zfmisc_1(u1_struct_0(A_70))) | ~m1_subset_1(B_72, k1_zfmisc_1(u1_struct_0(A_70))) | ~l1_pre_topc(A_70))), inference(resolution, [status(thm)], [c_14, c_102])).
% 3.48/1.72  tff(c_773, plain, (![A_96, A_97, B_98]: (k4_subset_1(u1_struct_0(A_96), A_97, k1_tops_1(A_96, B_98))=k2_xboole_0(A_97, k1_tops_1(A_96, B_98)) | ~m1_subset_1(B_98, k1_zfmisc_1(u1_struct_0(A_96))) | ~l1_pre_topc(A_96) | ~r1_tarski(A_97, u1_struct_0(A_96)))), inference(resolution, [status(thm)], [c_12, c_386])).
% 3.48/1.72  tff(c_780, plain, (![A_97]: (k4_subset_1(u1_struct_0('#skF_1'), A_97, k1_tops_1('#skF_1', '#skF_3'))=k2_xboole_0(A_97, k1_tops_1('#skF_1', '#skF_3')) | ~l1_pre_topc('#skF_1') | ~r1_tarski(A_97, u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_20, c_773])).
% 3.48/1.72  tff(c_791, plain, (![A_99]: (k4_subset_1(u1_struct_0('#skF_1'), A_99, k1_tops_1('#skF_1', '#skF_3'))=k2_xboole_0(A_99, k1_tops_1('#skF_1', '#skF_3')) | ~r1_tarski(A_99, u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_780])).
% 3.48/1.72  tff(c_115, plain, (![B_46]: (k4_subset_1(u1_struct_0('#skF_1'), B_46, '#skF_3')=k2_xboole_0(B_46, '#skF_3') | ~m1_subset_1(B_46, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(resolution, [status(thm)], [c_20, c_102])).
% 3.48/1.72  tff(c_129, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', '#skF_3')=k2_xboole_0('#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_22, c_115])).
% 3.48/1.72  tff(c_136, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', '#skF_3')=k2_xboole_0('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_129])).
% 3.48/1.72  tff(c_18, plain, (~r1_tarski(k4_subset_1(u1_struct_0('#skF_1'), k1_tops_1('#skF_1', '#skF_2'), k1_tops_1('#skF_1', '#skF_3')), k1_tops_1('#skF_1', k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.48/1.72  tff(c_139, plain, (~r1_tarski(k4_subset_1(u1_struct_0('#skF_1'), k1_tops_1('#skF_1', '#skF_2'), k1_tops_1('#skF_1', '#skF_3')), k1_tops_1('#skF_1', k2_xboole_0('#skF_3', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_136, c_18])).
% 3.48/1.72  tff(c_811, plain, (~r1_tarski(k2_xboole_0(k1_tops_1('#skF_1', '#skF_2'), k1_tops_1('#skF_1', '#skF_3')), k1_tops_1('#skF_1', k2_xboole_0('#skF_3', '#skF_2'))) | ~r1_tarski(k1_tops_1('#skF_1', '#skF_2'), u1_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_791, c_139])).
% 3.48/1.72  tff(c_842, plain, (~r1_tarski(k2_xboole_0(k1_tops_1('#skF_1', '#skF_3'), k1_tops_1('#skF_1', '#skF_2')), k1_tops_1('#skF_1', k2_xboole_0('#skF_3', '#skF_2'))) | ~r1_tarski(k1_tops_1('#skF_1', '#skF_2'), u1_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_811])).
% 3.48/1.72  tff(c_917, plain, (~r1_tarski(k1_tops_1('#skF_1', '#skF_2'), u1_struct_0('#skF_1'))), inference(splitLeft, [status(thm)], [c_842])).
% 3.48/1.72  tff(c_941, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_100, c_917])).
% 3.48/1.72  tff(c_945, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_24, c_22, c_941])).
% 3.48/1.72  tff(c_946, plain, (~r1_tarski(k2_xboole_0(k1_tops_1('#skF_1', '#skF_3'), k1_tops_1('#skF_1', '#skF_2')), k1_tops_1('#skF_1', k2_xboole_0('#skF_3', '#skF_2')))), inference(splitRight, [status(thm)], [c_842])).
% 3.48/1.72  tff(c_974, plain, (~r1_tarski(k1_tops_1('#skF_1', '#skF_2'), k1_tops_1('#skF_1', k2_xboole_0('#skF_3', '#skF_2'))) | ~r1_tarski(k1_tops_1('#skF_1', '#skF_3'), k1_tops_1('#skF_1', k2_xboole_0('#skF_3', '#skF_2')))), inference(resolution, [status(thm)], [c_6, c_946])).
% 3.48/1.72  tff(c_975, plain, (~r1_tarski(k1_tops_1('#skF_1', '#skF_3'), k1_tops_1('#skF_1', k2_xboole_0('#skF_3', '#skF_2')))), inference(splitLeft, [status(thm)], [c_974])).
% 3.48/1.72  tff(c_978, plain, (~r1_tarski('#skF_3', k2_xboole_0('#skF_3', '#skF_2')) | ~m1_subset_1(k2_xboole_0('#skF_3', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_16, c_975])).
% 3.48/1.72  tff(c_981, plain, (~m1_subset_1(k2_xboole_0('#skF_3', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_20, c_4, c_978])).
% 3.48/1.72  tff(c_1003, plain, (~r1_tarski(k2_xboole_0('#skF_3', '#skF_2'), u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_12, c_981])).
% 3.48/1.72  tff(c_1006, plain, (~r1_tarski('#skF_2', u1_struct_0('#skF_1')) | ~r1_tarski('#skF_3', u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_6, c_1003])).
% 3.48/1.72  tff(c_1010, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_72, c_73, c_1006])).
% 3.48/1.72  tff(c_1011, plain, (~r1_tarski(k1_tops_1('#skF_1', '#skF_2'), k1_tops_1('#skF_1', k2_xboole_0('#skF_3', '#skF_2')))), inference(splitRight, [status(thm)], [c_974])).
% 3.48/1.72  tff(c_1015, plain, (~r1_tarski('#skF_2', k2_xboole_0('#skF_3', '#skF_2')) | ~m1_subset_1(k2_xboole_0('#skF_3', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_16, c_1011])).
% 3.48/1.72  tff(c_1018, plain, (~m1_subset_1(k2_xboole_0('#skF_3', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_22, c_44, c_1015])).
% 3.48/1.72  tff(c_1043, plain, (~r1_tarski(k2_xboole_0('#skF_3', '#skF_2'), u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_12, c_1018])).
% 3.48/1.72  tff(c_1046, plain, (~r1_tarski('#skF_2', u1_struct_0('#skF_1')) | ~r1_tarski('#skF_3', u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_6, c_1043])).
% 3.48/1.72  tff(c_1050, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_72, c_73, c_1046])).
% 3.48/1.72  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.48/1.72  
% 3.48/1.72  Inference rules
% 3.48/1.72  ----------------------
% 3.48/1.72  #Ref     : 0
% 3.48/1.72  #Sup     : 235
% 3.48/1.72  #Fact    : 0
% 3.48/1.72  #Define  : 0
% 3.48/1.72  #Split   : 2
% 3.48/1.72  #Chain   : 0
% 3.48/1.72  #Close   : 0
% 3.48/1.72  
% 3.48/1.72  Ordering : KBO
% 3.48/1.72  
% 3.48/1.72  Simplification rules
% 3.48/1.72  ----------------------
% 3.48/1.72  #Subsume      : 39
% 3.48/1.72  #Demod        : 108
% 3.48/1.72  #Tautology    : 112
% 3.48/1.72  #SimpNegUnit  : 0
% 3.48/1.72  #BackRed      : 1
% 3.48/1.72  
% 3.48/1.72  #Partial instantiations: 0
% 3.48/1.72  #Strategies tried      : 1
% 3.48/1.72  
% 3.48/1.72  Timing (in seconds)
% 3.48/1.72  ----------------------
% 3.48/1.72  Preprocessing        : 0.38
% 3.48/1.72  Parsing              : 0.20
% 3.48/1.72  CNF conversion       : 0.02
% 3.48/1.72  Main loop            : 0.47
% 3.48/1.72  Inferencing          : 0.17
% 3.48/1.72  Reduction            : 0.16
% 3.48/1.72  Demodulation         : 0.13
% 3.48/1.72  BG Simplification    : 0.02
% 3.48/1.72  Subsumption          : 0.08
% 3.48/1.72  Abstraction          : 0.03
% 3.48/1.72  MUC search           : 0.00
% 3.48/1.72  Cooper               : 0.00
% 3.48/1.72  Total                : 0.89
% 3.48/1.72  Index Insertion      : 0.00
% 3.48/1.72  Index Deletion       : 0.00
% 3.48/1.72  Index Matching       : 0.00
% 3.48/1.72  BG Taut test         : 0.00
%------------------------------------------------------------------------------
