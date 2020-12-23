%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1289+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:37:43 EST 2020

% Result     : Theorem 26.79s
% Output     : CNFRefutation 27.27s
% Verified   : 
% Statistics : Number of formulae       :  370 (12879 expanded)
%              Number of leaves         :   24 (4397 expanded)
%              Depth                    :   33
%              Number of atoms          :  977 (36036 expanded)
%              Number of equality atoms :   32 (3287 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_tops_1 > r1_tarski > m1_subset_1 > l1_pre_topc > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(v4_tops_1,type,(
    v4_tops_1: ( $i * $i ) > $o )).

tff(k1_tops_1,type,(
    k1_tops_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_115,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v4_tops_1(B,A)
             => ( v4_tops_1(k1_tops_1(A,B),A)
                & v4_tops_1(k2_pre_topc(A,B),A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t111_tops_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_pre_topc(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_pre_topc)).

tff(f_59,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => k2_pre_topc(A,k2_pre_topc(A,B)) = k2_pre_topc(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',projectivity_k2_pre_topc)).

tff(f_72,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => r1_tarski(k1_tops_1(A,B),B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_tops_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k1_tops_1(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_tops_1)).

tff(f_103,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( r1_tarski(B,C)
               => r1_tarski(k2_pre_topc(A,B),k2_pre_topc(A,C)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_pre_topc)).

tff(f_53,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => k1_tops_1(A,k1_tops_1(A,B)) = k1_tops_1(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',projectivity_k1_tops_1)).

tff(f_79,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => r1_tarski(B,k2_pre_topc(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_pre_topc)).

tff(f_91,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( r1_tarski(B,C)
               => r1_tarski(k1_tops_1(A,B),k1_tops_1(A,C)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_tops_1)).

tff(f_35,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v4_tops_1(B,A)
          <=> ( r1_tarski(k1_tops_1(A,k2_pre_topc(A,B)),B)
              & r1_tarski(B,k2_pre_topc(A,k1_tops_1(A,B))) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_tops_1)).

tff(f_65,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

tff(c_32,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_30,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_10,plain,(
    ! [A_6,B_7] :
      ( m1_subset_1(k2_pre_topc(A_6,B_7),k1_zfmisc_1(u1_struct_0(A_6)))
      | ~ m1_subset_1(B_7,k1_zfmisc_1(u1_struct_0(A_6)))
      | ~ l1_pre_topc(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_86259,plain,(
    ! [A_1030,B_1031] :
      ( k2_pre_topc(A_1030,k2_pre_topc(A_1030,B_1031)) = k2_pre_topc(A_1030,B_1031)
      | ~ m1_subset_1(B_1031,k1_zfmisc_1(u1_struct_0(A_1030)))
      | ~ l1_pre_topc(A_1030) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_86265,plain,
    ( k2_pre_topc('#skF_1',k2_pre_topc('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_30,c_86259])).

tff(c_86270,plain,(
    k2_pre_topc('#skF_1',k2_pre_topc('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_86265])).

tff(c_86231,plain,(
    ! [A_1026,B_1027] :
      ( m1_subset_1(k2_pre_topc(A_1026,B_1027),k1_zfmisc_1(u1_struct_0(A_1026)))
      | ~ m1_subset_1(B_1027,k1_zfmisc_1(u1_struct_0(A_1026)))
      | ~ l1_pre_topc(A_1026) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_18,plain,(
    ! [A_15,B_17] :
      ( r1_tarski(k1_tops_1(A_15,B_17),B_17)
      | ~ m1_subset_1(B_17,k1_zfmisc_1(u1_struct_0(A_15)))
      | ~ l1_pre_topc(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_86634,plain,(
    ! [A_1051,B_1052] :
      ( r1_tarski(k1_tops_1(A_1051,k2_pre_topc(A_1051,B_1052)),k2_pre_topc(A_1051,B_1052))
      | ~ m1_subset_1(B_1052,k1_zfmisc_1(u1_struct_0(A_1051)))
      | ~ l1_pre_topc(A_1051) ) ),
    inference(resolution,[status(thm)],[c_86231,c_18])).

tff(c_86651,plain,
    ( r1_tarski(k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2')),k2_pre_topc('#skF_1',k2_pre_topc('#skF_1','#skF_2')))
    | ~ m1_subset_1(k2_pre_topc('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_86270,c_86634])).

tff(c_86664,plain,
    ( r1_tarski(k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2')),k2_pre_topc('#skF_1','#skF_2'))
    | ~ m1_subset_1(k2_pre_topc('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_86270,c_86651])).

tff(c_86671,plain,(
    ~ m1_subset_1(k2_pre_topc('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_86664])).

tff(c_86704,plain,
    ( ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_10,c_86671])).

tff(c_86708,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_86704])).

tff(c_86710,plain,(
    m1_subset_1(k2_pre_topc('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_86664])).

tff(c_8,plain,(
    ! [A_4,B_5] :
      ( m1_subset_1(k1_tops_1(A_4,B_5),k1_zfmisc_1(u1_struct_0(A_4)))
      | ~ m1_subset_1(B_5,k1_zfmisc_1(u1_struct_0(A_4)))
      | ~ l1_pre_topc(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_24,plain,(
    ! [A_28,B_32,C_34] :
      ( r1_tarski(k2_pre_topc(A_28,B_32),k2_pre_topc(A_28,C_34))
      | ~ r1_tarski(B_32,C_34)
      | ~ m1_subset_1(C_34,k1_zfmisc_1(u1_struct_0(A_28)))
      | ~ m1_subset_1(B_32,k1_zfmisc_1(u1_struct_0(A_28)))
      | ~ l1_pre_topc(A_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_26,plain,
    ( ~ v4_tops_1(k2_pre_topc('#skF_1','#skF_2'),'#skF_1')
    | ~ v4_tops_1(k1_tops_1('#skF_1','#skF_2'),'#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_34,plain,(
    ~ v4_tops_1(k1_tops_1('#skF_1','#skF_2'),'#skF_1') ),
    inference(splitLeft,[status(thm)],[c_26])).

tff(c_84,plain,(
    ! [A_51,B_52] :
      ( k1_tops_1(A_51,k1_tops_1(A_51,B_52)) = k1_tops_1(A_51,B_52)
      | ~ m1_subset_1(B_52,k1_zfmisc_1(u1_struct_0(A_51)))
      | ~ l1_pre_topc(A_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_90,plain,
    ( k1_tops_1('#skF_1',k1_tops_1('#skF_1','#skF_2')) = k1_tops_1('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_30,c_84])).

tff(c_95,plain,(
    k1_tops_1('#skF_1',k1_tops_1('#skF_1','#skF_2')) = k1_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_90])).

tff(c_77,plain,(
    ! [A_49,B_50] :
      ( m1_subset_1(k1_tops_1(A_49,B_50),k1_zfmisc_1(u1_struct_0(A_49)))
      | ~ m1_subset_1(B_50,k1_zfmisc_1(u1_struct_0(A_49)))
      | ~ l1_pre_topc(A_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_20,plain,(
    ! [B_20,A_18] :
      ( r1_tarski(B_20,k2_pre_topc(A_18,B_20))
      | ~ m1_subset_1(B_20,k1_zfmisc_1(u1_struct_0(A_18)))
      | ~ l1_pre_topc(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_324,plain,(
    ! [A_70,B_71] :
      ( r1_tarski(k1_tops_1(A_70,B_71),k2_pre_topc(A_70,k1_tops_1(A_70,B_71)))
      | ~ m1_subset_1(B_71,k1_zfmisc_1(u1_struct_0(A_70)))
      | ~ l1_pre_topc(A_70) ) ),
    inference(resolution,[status(thm)],[c_77,c_20])).

tff(c_333,plain,
    ( r1_tarski(k1_tops_1('#skF_1','#skF_2'),k2_pre_topc('#skF_1',k1_tops_1('#skF_1',k1_tops_1('#skF_1','#skF_2'))))
    | ~ m1_subset_1(k1_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_95,c_324])).

tff(c_341,plain,
    ( r1_tarski(k1_tops_1('#skF_1','#skF_2'),k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')))
    | ~ m1_subset_1(k1_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_95,c_333])).

tff(c_460,plain,(
    ~ m1_subset_1(k1_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_341])).

tff(c_463,plain,
    ( ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_8,c_460])).

tff(c_467,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_463])).

tff(c_469,plain,(
    m1_subset_1(k1_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_341])).

tff(c_468,plain,(
    r1_tarski(k1_tops_1('#skF_1','#skF_2'),k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_341])).

tff(c_22,plain,(
    ! [A_21,B_25,C_27] :
      ( r1_tarski(k1_tops_1(A_21,B_25),k1_tops_1(A_21,C_27))
      | ~ r1_tarski(B_25,C_27)
      | ~ m1_subset_1(C_27,k1_zfmisc_1(u1_struct_0(A_21)))
      | ~ m1_subset_1(B_25,k1_zfmisc_1(u1_struct_0(A_21)))
      | ~ l1_pre_topc(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_711,plain,(
    ! [B_81,A_82] :
      ( v4_tops_1(B_81,A_82)
      | ~ r1_tarski(B_81,k2_pre_topc(A_82,k1_tops_1(A_82,B_81)))
      | ~ r1_tarski(k1_tops_1(A_82,k2_pre_topc(A_82,B_81)),B_81)
      | ~ m1_subset_1(B_81,k1_zfmisc_1(u1_struct_0(A_82)))
      | ~ l1_pre_topc(A_82) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_21997,plain,(
    ! [A_414,C_415] :
      ( v4_tops_1(k1_tops_1(A_414,C_415),A_414)
      | ~ r1_tarski(k1_tops_1(A_414,C_415),k2_pre_topc(A_414,k1_tops_1(A_414,k1_tops_1(A_414,C_415))))
      | ~ m1_subset_1(k1_tops_1(A_414,C_415),k1_zfmisc_1(u1_struct_0(A_414)))
      | ~ r1_tarski(k2_pre_topc(A_414,k1_tops_1(A_414,C_415)),C_415)
      | ~ m1_subset_1(C_415,k1_zfmisc_1(u1_struct_0(A_414)))
      | ~ m1_subset_1(k2_pre_topc(A_414,k1_tops_1(A_414,C_415)),k1_zfmisc_1(u1_struct_0(A_414)))
      | ~ l1_pre_topc(A_414) ) ),
    inference(resolution,[status(thm)],[c_22,c_711])).

tff(c_22052,plain,
    ( v4_tops_1(k1_tops_1('#skF_1','#skF_2'),'#skF_1')
    | ~ r1_tarski(k1_tops_1('#skF_1','#skF_2'),k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')))
    | ~ m1_subset_1(k1_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ r1_tarski(k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')),'#skF_2')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_subset_1(k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_95,c_21997])).

tff(c_22090,plain,
    ( v4_tops_1(k1_tops_1('#skF_1','#skF_2'),'#skF_1')
    | ~ r1_tarski(k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')),'#skF_2')
    | ~ m1_subset_1(k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_469,c_468,c_22052])).

tff(c_22091,plain,
    ( ~ r1_tarski(k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')),'#skF_2')
    | ~ m1_subset_1(k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_22090])).

tff(c_22092,plain,(
    ~ m1_subset_1(k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_22091])).

tff(c_22095,plain,
    ( ~ m1_subset_1(k1_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_10,c_22092])).

tff(c_22099,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_469,c_22095])).

tff(c_22101,plain,(
    m1_subset_1(k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_22091])).

tff(c_126,plain,(
    ! [A_55,B_56] :
      ( r1_tarski(k1_tops_1(A_55,k1_tops_1(A_55,B_56)),k1_tops_1(A_55,B_56))
      | ~ m1_subset_1(B_56,k1_zfmisc_1(u1_struct_0(A_55)))
      | ~ l1_pre_topc(A_55) ) ),
    inference(resolution,[status(thm)],[c_77,c_18])).

tff(c_140,plain,
    ( r1_tarski(k1_tops_1('#skF_1','#skF_2'),k1_tops_1('#skF_1','#skF_2'))
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_95,c_126])).

tff(c_152,plain,(
    r1_tarski(k1_tops_1('#skF_1','#skF_2'),k1_tops_1('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_140])).

tff(c_105,plain,(
    ! [A_53,B_54] :
      ( k2_pre_topc(A_53,k2_pre_topc(A_53,B_54)) = k2_pre_topc(A_53,B_54)
      | ~ m1_subset_1(B_54,k1_zfmisc_1(u1_struct_0(A_53)))
      | ~ l1_pre_topc(A_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_111,plain,
    ( k2_pre_topc('#skF_1',k2_pre_topc('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_30,c_105])).

tff(c_116,plain,(
    k2_pre_topc('#skF_1',k2_pre_topc('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_111])).

tff(c_70,plain,(
    ! [A_47,B_48] :
      ( m1_subset_1(k2_pre_topc(A_47,B_48),k1_zfmisc_1(u1_struct_0(A_47)))
      | ~ m1_subset_1(B_48,k1_zfmisc_1(u1_struct_0(A_47)))
      | ~ l1_pre_topc(A_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_284,plain,(
    ! [A_66,B_67] :
      ( r1_tarski(k1_tops_1(A_66,k2_pre_topc(A_66,B_67)),k2_pre_topc(A_66,B_67))
      | ~ m1_subset_1(B_67,k1_zfmisc_1(u1_struct_0(A_66)))
      | ~ l1_pre_topc(A_66) ) ),
    inference(resolution,[status(thm)],[c_70,c_18])).

tff(c_296,plain,
    ( r1_tarski(k1_tops_1('#skF_1',k2_pre_topc('#skF_1',k2_pre_topc('#skF_1','#skF_2'))),k2_pre_topc('#skF_1','#skF_2'))
    | ~ m1_subset_1(k2_pre_topc('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_116,c_284])).

tff(c_303,plain,
    ( r1_tarski(k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2')),k2_pre_topc('#skF_1','#skF_2'))
    | ~ m1_subset_1(k2_pre_topc('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_116,c_296])).

tff(c_344,plain,(
    ~ m1_subset_1(k2_pre_topc('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_303])).

tff(c_347,plain,
    ( ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_10,c_344])).

tff(c_351,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_347])).

tff(c_353,plain,(
    m1_subset_1(k2_pre_topc('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_303])).

tff(c_14,plain,(
    ! [A_10,B_11] :
      ( k2_pre_topc(A_10,k2_pre_topc(A_10,B_11)) = k2_pre_topc(A_10,B_11)
      | ~ m1_subset_1(B_11,k1_zfmisc_1(u1_struct_0(A_10)))
      | ~ l1_pre_topc(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_471,plain,
    ( k2_pre_topc('#skF_1',k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2'))) = k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2'))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_469,c_14])).

tff(c_480,plain,(
    k2_pre_topc('#skF_1',k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2'))) = k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_471])).

tff(c_35,plain,(
    ! [B_39,A_40] :
      ( r1_tarski(B_39,k2_pre_topc(A_40,B_39))
      | ~ m1_subset_1(B_39,k1_zfmisc_1(u1_struct_0(A_40)))
      | ~ l1_pre_topc(A_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_37,plain,
    ( r1_tarski('#skF_2',k2_pre_topc('#skF_1','#skF_2'))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_30,c_35])).

tff(c_40,plain,(
    r1_tarski('#skF_2',k2_pre_topc('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_37])).

tff(c_513,plain,(
    ! [A_76,B_77,C_78] :
      ( r1_tarski(k2_pre_topc(A_76,B_77),k2_pre_topc(A_76,C_78))
      | ~ r1_tarski(B_77,C_78)
      | ~ m1_subset_1(C_78,k1_zfmisc_1(u1_struct_0(A_76)))
      | ~ m1_subset_1(B_77,k1_zfmisc_1(u1_struct_0(A_76)))
      | ~ l1_pre_topc(A_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_16,plain,(
    ! [A_12,C_14,B_13] :
      ( r1_tarski(A_12,C_14)
      | ~ r1_tarski(B_13,C_14)
      | ~ r1_tarski(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_20875,plain,(
    ! [A_385,A_386,C_387,B_388] :
      ( r1_tarski(A_385,k2_pre_topc(A_386,C_387))
      | ~ r1_tarski(A_385,k2_pre_topc(A_386,B_388))
      | ~ r1_tarski(B_388,C_387)
      | ~ m1_subset_1(C_387,k1_zfmisc_1(u1_struct_0(A_386)))
      | ~ m1_subset_1(B_388,k1_zfmisc_1(u1_struct_0(A_386)))
      | ~ l1_pre_topc(A_386) ) ),
    inference(resolution,[status(thm)],[c_513,c_16])).

tff(c_20946,plain,(
    ! [A_385,C_387] :
      ( r1_tarski(A_385,k2_pre_topc('#skF_1',C_387))
      | ~ r1_tarski(A_385,k2_pre_topc('#skF_1','#skF_2'))
      | ~ r1_tarski(k2_pre_topc('#skF_1','#skF_2'),C_387)
      | ~ m1_subset_1(C_387,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ m1_subset_1(k2_pre_topc('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_116,c_20875])).

tff(c_21193,plain,(
    ! [A_392,C_393] :
      ( r1_tarski(A_392,k2_pre_topc('#skF_1',C_393))
      | ~ r1_tarski(A_392,k2_pre_topc('#skF_1','#skF_2'))
      | ~ r1_tarski(k2_pre_topc('#skF_1','#skF_2'),C_393)
      | ~ m1_subset_1(C_393,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_353,c_20946])).

tff(c_21260,plain,(
    ! [C_393] :
      ( r1_tarski('#skF_2',k2_pre_topc('#skF_1',C_393))
      | ~ r1_tarski(k2_pre_topc('#skF_1','#skF_2'),C_393)
      | ~ m1_subset_1(C_393,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(resolution,[status(thm)],[c_40,c_21193])).

tff(c_22108,plain,
    ( r1_tarski('#skF_2',k2_pre_topc('#skF_1',k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2'))))
    | ~ r1_tarski(k2_pre_topc('#skF_1','#skF_2'),k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2'))) ),
    inference(resolution,[status(thm)],[c_22101,c_21260])).

tff(c_22139,plain,
    ( r1_tarski('#skF_2',k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')))
    | ~ r1_tarski(k2_pre_topc('#skF_1','#skF_2'),k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_480,c_22108])).

tff(c_22282,plain,(
    ~ r1_tarski(k2_pre_topc('#skF_1','#skF_2'),k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_22139])).

tff(c_293,plain,
    ( r1_tarski(k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2')),k2_pre_topc('#skF_1',k2_pre_topc('#skF_1','#skF_2')))
    | ~ m1_subset_1(k2_pre_topc('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_116,c_284])).

tff(c_301,plain,
    ( r1_tarski(k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2')),k2_pre_topc('#skF_1','#skF_2'))
    | ~ m1_subset_1(k2_pre_topc('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_116,c_293])).

tff(c_354,plain,(
    ~ m1_subset_1(k2_pre_topc('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_301])).

tff(c_376,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_353,c_354])).

tff(c_377,plain,(
    r1_tarski(k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2')),k2_pre_topc('#skF_1','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_301])).

tff(c_732,plain,
    ( v4_tops_1(k2_pre_topc('#skF_1','#skF_2'),'#skF_1')
    | ~ r1_tarski(k2_pre_topc('#skF_1','#skF_2'),k2_pre_topc('#skF_1',k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2'))))
    | ~ r1_tarski(k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2')),k2_pre_topc('#skF_1','#skF_2'))
    | ~ m1_subset_1(k2_pre_topc('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_116,c_711])).

tff(c_744,plain,
    ( v4_tops_1(k2_pre_topc('#skF_1','#skF_2'),'#skF_1')
    | ~ r1_tarski(k2_pre_topc('#skF_1','#skF_2'),k2_pre_topc('#skF_1',k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_353,c_377,c_732])).

tff(c_818,plain,(
    ~ r1_tarski(k2_pre_topc('#skF_1','#skF_2'),k2_pre_topc('#skF_1',k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2')))) ),
    inference(splitLeft,[status(thm)],[c_744])).

tff(c_821,plain,
    ( ~ r1_tarski('#skF_2',k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2')))
    | ~ m1_subset_1(k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2')),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_24,c_818])).

tff(c_827,plain,
    ( ~ r1_tarski('#skF_2',k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2')))
    | ~ m1_subset_1(k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2')),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_821])).

tff(c_831,plain,(
    ~ m1_subset_1(k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2')),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_827])).

tff(c_834,plain,
    ( ~ m1_subset_1(k2_pre_topc('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_8,c_831])).

tff(c_838,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_353,c_834])).

tff(c_840,plain,(
    m1_subset_1(k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2')),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_827])).

tff(c_869,plain,
    ( k2_pre_topc('#skF_1',k2_pre_topc('#skF_1',k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2')))) = k2_pre_topc('#skF_1',k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_840,c_14])).

tff(c_883,plain,(
    k2_pre_topc('#skF_1',k2_pre_topc('#skF_1',k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2')))) = k2_pre_topc('#skF_1',k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_869])).

tff(c_76,plain,(
    ! [A_47,B_48] :
      ( r1_tarski(k2_pre_topc(A_47,B_48),k2_pre_topc(A_47,k2_pre_topc(A_47,B_48)))
      | ~ m1_subset_1(B_48,k1_zfmisc_1(u1_struct_0(A_47)))
      | ~ l1_pre_topc(A_47) ) ),
    inference(resolution,[status(thm)],[c_70,c_20])).

tff(c_958,plain,
    ( r1_tarski(k2_pre_topc('#skF_1',k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2'))),k2_pre_topc('#skF_1',k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2'))))
    | ~ m1_subset_1(k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2')),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_883,c_76])).

tff(c_981,plain,(
    r1_tarski(k2_pre_topc('#skF_1',k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2'))),k2_pre_topc('#skF_1',k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_840,c_958])).

tff(c_525,plain,(
    ! [B_77] :
      ( r1_tarski(k2_pre_topc('#skF_1',B_77),k2_pre_topc('#skF_1','#skF_2'))
      | ~ r1_tarski(B_77,k2_pre_topc('#skF_1','#skF_2'))
      | ~ m1_subset_1(k2_pre_topc('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ m1_subset_1(B_77,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_116,c_513])).

tff(c_907,plain,(
    ! [B_87] :
      ( r1_tarski(k2_pre_topc('#skF_1',B_87),k2_pre_topc('#skF_1','#skF_2'))
      | ~ r1_tarski(B_87,k2_pre_topc('#skF_1','#skF_2'))
      | ~ m1_subset_1(B_87,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_353,c_525])).

tff(c_1848,plain,(
    ! [A_125,B_126] :
      ( r1_tarski(A_125,k2_pre_topc('#skF_1','#skF_2'))
      | ~ r1_tarski(A_125,k2_pre_topc('#skF_1',B_126))
      | ~ r1_tarski(B_126,k2_pre_topc('#skF_1','#skF_2'))
      | ~ m1_subset_1(B_126,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(resolution,[status(thm)],[c_907,c_16])).

tff(c_1865,plain,
    ( r1_tarski(k2_pre_topc('#skF_1',k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2'))),k2_pre_topc('#skF_1','#skF_2'))
    | ~ r1_tarski(k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2')),k2_pre_topc('#skF_1','#skF_2'))
    | ~ m1_subset_1(k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2')),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_981,c_1848])).

tff(c_1933,plain,(
    r1_tarski(k2_pre_topc('#skF_1',k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2'))),k2_pre_topc('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_840,c_377,c_1865])).

tff(c_875,plain,
    ( r1_tarski(k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2')),k2_pre_topc('#skF_1',k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2'))))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_840,c_20])).

tff(c_892,plain,(
    r1_tarski(k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2')),k2_pre_topc('#skF_1',k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_875])).

tff(c_12,plain,(
    ! [A_8,B_9] :
      ( k1_tops_1(A_8,k1_tops_1(A_8,B_9)) = k1_tops_1(A_8,B_9)
      | ~ m1_subset_1(B_9,k1_zfmisc_1(u1_struct_0(A_8)))
      | ~ l1_pre_topc(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_382,plain,
    ( k1_tops_1('#skF_1',k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2'))) = k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2'))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_353,c_12])).

tff(c_392,plain,(
    k1_tops_1('#skF_1',k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2'))) = k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_382])).

tff(c_3105,plain,(
    ! [A_154,C_155] :
      ( v4_tops_1(k1_tops_1(A_154,C_155),A_154)
      | ~ r1_tarski(k1_tops_1(A_154,C_155),k2_pre_topc(A_154,k1_tops_1(A_154,k1_tops_1(A_154,C_155))))
      | ~ m1_subset_1(k1_tops_1(A_154,C_155),k1_zfmisc_1(u1_struct_0(A_154)))
      | ~ r1_tarski(k2_pre_topc(A_154,k1_tops_1(A_154,C_155)),C_155)
      | ~ m1_subset_1(C_155,k1_zfmisc_1(u1_struct_0(A_154)))
      | ~ m1_subset_1(k2_pre_topc(A_154,k1_tops_1(A_154,C_155)),k1_zfmisc_1(u1_struct_0(A_154)))
      | ~ l1_pre_topc(A_154) ) ),
    inference(resolution,[status(thm)],[c_22,c_711])).

tff(c_3143,plain,
    ( v4_tops_1(k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2')),'#skF_1')
    | ~ r1_tarski(k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2')),k2_pre_topc('#skF_1',k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2'))))
    | ~ m1_subset_1(k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2')),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ r1_tarski(k2_pre_topc('#skF_1',k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2'))),k2_pre_topc('#skF_1','#skF_2'))
    | ~ m1_subset_1(k2_pre_topc('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_subset_1(k2_pre_topc('#skF_1',k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2'))),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_392,c_3105])).

tff(c_3181,plain,
    ( v4_tops_1(k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2')),'#skF_1')
    | ~ m1_subset_1(k2_pre_topc('#skF_1',k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2'))),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_353,c_1933,c_840,c_892,c_3143])).

tff(c_4204,plain,(
    ~ m1_subset_1(k2_pre_topc('#skF_1',k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2'))),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_3181])).

tff(c_4367,plain,
    ( ~ m1_subset_1(k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2')),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_10,c_4204])).

tff(c_4371,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_840,c_4367])).

tff(c_4373,plain,(
    m1_subset_1(k2_pre_topc('#skF_1',k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2'))),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_3181])).

tff(c_56,plain,(
    ! [A_44,B_45] :
      ( r1_tarski(k1_tops_1(A_44,B_45),B_45)
      | ~ m1_subset_1(B_45,k1_zfmisc_1(u1_struct_0(A_44)))
      | ~ l1_pre_topc(A_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_58,plain,
    ( r1_tarski(k1_tops_1('#skF_1','#skF_2'),'#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_30,c_56])).

tff(c_61,plain,(
    r1_tarski(k1_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_58])).

tff(c_44,plain,(
    ! [A_41] :
      ( r1_tarski(A_41,k2_pre_topc('#skF_1','#skF_2'))
      | ~ r1_tarski(A_41,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_40,c_16])).

tff(c_47,plain,(
    ! [A_12,A_41] :
      ( r1_tarski(A_12,k2_pre_topc('#skF_1','#skF_2'))
      | ~ r1_tarski(A_12,A_41)
      | ~ r1_tarski(A_41,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_44,c_16])).

tff(c_159,plain,
    ( r1_tarski(k1_tops_1('#skF_1','#skF_2'),k2_pre_topc('#skF_1','#skF_2'))
    | ~ r1_tarski(k1_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_152,c_47])).

tff(c_166,plain,(
    r1_tarski(k1_tops_1('#skF_1','#skF_2'),k2_pre_topc('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_61,c_159])).

tff(c_411,plain,(
    ! [A_72,B_73,C_74] :
      ( r1_tarski(k1_tops_1(A_72,B_73),k1_tops_1(A_72,C_74))
      | ~ r1_tarski(B_73,C_74)
      | ~ m1_subset_1(C_74,k1_zfmisc_1(u1_struct_0(A_72)))
      | ~ m1_subset_1(B_73,k1_zfmisc_1(u1_struct_0(A_72)))
      | ~ l1_pre_topc(A_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_2103,plain,(
    ! [A_128,A_129,C_130,B_131] :
      ( r1_tarski(A_128,k1_tops_1(A_129,C_130))
      | ~ r1_tarski(A_128,k1_tops_1(A_129,B_131))
      | ~ r1_tarski(B_131,C_130)
      | ~ m1_subset_1(C_130,k1_zfmisc_1(u1_struct_0(A_129)))
      | ~ m1_subset_1(B_131,k1_zfmisc_1(u1_struct_0(A_129)))
      | ~ l1_pre_topc(A_129) ) ),
    inference(resolution,[status(thm)],[c_411,c_16])).

tff(c_2120,plain,(
    ! [A_128,C_130] :
      ( r1_tarski(A_128,k1_tops_1('#skF_1',C_130))
      | ~ r1_tarski(A_128,k1_tops_1('#skF_1','#skF_2'))
      | ~ r1_tarski(k1_tops_1('#skF_1','#skF_2'),C_130)
      | ~ m1_subset_1(C_130,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ m1_subset_1(k1_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_95,c_2103])).

tff(c_2249,plain,(
    ! [A_133,C_134] :
      ( r1_tarski(A_133,k1_tops_1('#skF_1',C_134))
      | ~ r1_tarski(A_133,k1_tops_1('#skF_1','#skF_2'))
      | ~ r1_tarski(k1_tops_1('#skF_1','#skF_2'),C_134)
      | ~ m1_subset_1(C_134,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_469,c_2120])).

tff(c_2265,plain,(
    ! [C_134] :
      ( r1_tarski(k1_tops_1('#skF_1','#skF_2'),k1_tops_1('#skF_1',C_134))
      | ~ r1_tarski(k1_tops_1('#skF_1','#skF_2'),C_134)
      | ~ m1_subset_1(C_134,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(resolution,[status(thm)],[c_152,c_2249])).

tff(c_28,plain,(
    v4_tops_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_4,plain,(
    ! [B_3,A_1] :
      ( r1_tarski(B_3,k2_pre_topc(A_1,k1_tops_1(A_1,B_3)))
      | ~ v4_tops_1(B_3,A_1)
      | ~ m1_subset_1(B_3,k1_zfmisc_1(u1_struct_0(A_1)))
      | ~ l1_pre_topc(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_3156,plain,
    ( v4_tops_1(k1_tops_1('#skF_1','#skF_2'),'#skF_1')
    | ~ r1_tarski(k1_tops_1('#skF_1','#skF_2'),k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')))
    | ~ m1_subset_1(k1_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ r1_tarski(k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')),'#skF_2')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_subset_1(k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_95,c_3105])).

tff(c_3190,plain,
    ( v4_tops_1(k1_tops_1('#skF_1','#skF_2'),'#skF_1')
    | ~ r1_tarski(k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')),'#skF_2')
    | ~ m1_subset_1(k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_469,c_468,c_3156])).

tff(c_3191,plain,
    ( ~ r1_tarski(k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')),'#skF_2')
    | ~ m1_subset_1(k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_3190])).

tff(c_3192,plain,(
    ~ m1_subset_1(k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_3191])).

tff(c_3195,plain,
    ( ~ m1_subset_1(k1_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_10,c_3192])).

tff(c_3199,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_469,c_3195])).

tff(c_3201,plain,(
    m1_subset_1(k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_3191])).

tff(c_246,plain,(
    ! [A_64,B_65] :
      ( r1_tarski(k2_pre_topc(A_64,B_65),k2_pre_topc(A_64,k2_pre_topc(A_64,B_65)))
      | ~ m1_subset_1(B_65,k1_zfmisc_1(u1_struct_0(A_64)))
      | ~ l1_pre_topc(A_64) ) ),
    inference(resolution,[status(thm)],[c_70,c_20])).

tff(c_261,plain,
    ( r1_tarski(k2_pre_topc('#skF_1','#skF_2'),k2_pre_topc('#skF_1','#skF_2'))
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_116,c_246])).

tff(c_270,plain,(
    r1_tarski(k2_pre_topc('#skF_1','#skF_2'),k2_pre_topc('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_261])).

tff(c_2504,plain,(
    ! [A_139,A_140,C_141,B_142] :
      ( r1_tarski(A_139,k2_pre_topc(A_140,C_141))
      | ~ r1_tarski(A_139,k2_pre_topc(A_140,B_142))
      | ~ r1_tarski(B_142,C_141)
      | ~ m1_subset_1(C_141,k1_zfmisc_1(u1_struct_0(A_140)))
      | ~ m1_subset_1(B_142,k1_zfmisc_1(u1_struct_0(A_140)))
      | ~ l1_pre_topc(A_140) ) ),
    inference(resolution,[status(thm)],[c_513,c_16])).

tff(c_2553,plain,(
    ! [C_141] :
      ( r1_tarski(k2_pre_topc('#skF_1','#skF_2'),k2_pre_topc('#skF_1',C_141))
      | ~ r1_tarski('#skF_2',C_141)
      | ~ m1_subset_1(C_141,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_270,c_2504])).

tff(c_2679,plain,(
    ! [C_144] :
      ( r1_tarski(k2_pre_topc('#skF_1','#skF_2'),k2_pre_topc('#skF_1',C_144))
      | ~ r1_tarski('#skF_2',C_144)
      | ~ m1_subset_1(C_144,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_2553])).

tff(c_997,plain,(
    ! [A_88] :
      ( r1_tarski(A_88,k2_pre_topc('#skF_1',k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2'))))
      | ~ r1_tarski(A_88,k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2'))) ) ),
    inference(resolution,[status(thm)],[c_892,c_16])).

tff(c_1018,plain,(
    ! [A_12,A_88] :
      ( r1_tarski(A_12,k2_pre_topc('#skF_1',k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2'))))
      | ~ r1_tarski(A_12,A_88)
      | ~ r1_tarski(A_88,k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2'))) ) ),
    inference(resolution,[status(thm)],[c_997,c_16])).

tff(c_2693,plain,(
    ! [C_144] :
      ( r1_tarski(k2_pre_topc('#skF_1','#skF_2'),k2_pre_topc('#skF_1',k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2'))))
      | ~ r1_tarski(k2_pre_topc('#skF_1',C_144),k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2')))
      | ~ r1_tarski('#skF_2',C_144)
      | ~ m1_subset_1(C_144,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(resolution,[status(thm)],[c_2679,c_1018])).

tff(c_3651,plain,(
    ! [C_162] :
      ( ~ r1_tarski(k2_pre_topc('#skF_1',C_162),k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2')))
      | ~ r1_tarski('#skF_2',C_162)
      | ~ m1_subset_1(C_162,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_818,c_2693])).

tff(c_3657,plain,
    ( ~ r1_tarski(k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')),k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2')))
    | ~ r1_tarski('#skF_2',k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')))
    | ~ m1_subset_1(k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_480,c_3651])).

tff(c_3662,plain,
    ( ~ r1_tarski(k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')),k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2')))
    | ~ r1_tarski('#skF_2',k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3201,c_3657])).

tff(c_4756,plain,(
    ~ r1_tarski('#skF_2',k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_3662])).

tff(c_4771,plain,
    ( ~ v4_tops_1('#skF_2','#skF_1')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_4,c_4756])).

tff(c_4785,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_28,c_4771])).

tff(c_4787,plain,(
    r1_tarski('#skF_2',k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_3662])).

tff(c_528,plain,(
    ! [A_12,A_76,C_78,B_77] :
      ( r1_tarski(A_12,k2_pre_topc(A_76,C_78))
      | ~ r1_tarski(A_12,k2_pre_topc(A_76,B_77))
      | ~ r1_tarski(B_77,C_78)
      | ~ m1_subset_1(C_78,k1_zfmisc_1(u1_struct_0(A_76)))
      | ~ m1_subset_1(B_77,k1_zfmisc_1(u1_struct_0(A_76)))
      | ~ l1_pre_topc(A_76) ) ),
    inference(resolution,[status(thm)],[c_513,c_16])).

tff(c_4858,plain,(
    ! [C_78] :
      ( r1_tarski('#skF_2',k2_pre_topc('#skF_1',C_78))
      | ~ r1_tarski(k1_tops_1('#skF_1','#skF_2'),C_78)
      | ~ m1_subset_1(C_78,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ m1_subset_1(k1_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_4787,c_528])).

tff(c_5442,plain,(
    ! [C_191] :
      ( r1_tarski('#skF_2',k2_pre_topc('#skF_1',C_191))
      | ~ r1_tarski(k1_tops_1('#skF_1','#skF_2'),C_191)
      | ~ m1_subset_1(C_191,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_469,c_4858])).

tff(c_5474,plain,
    ( r1_tarski('#skF_2',k2_pre_topc('#skF_1',k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2'))))
    | ~ r1_tarski(k1_tops_1('#skF_1','#skF_2'),k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2'))) ),
    inference(resolution,[status(thm)],[c_840,c_5442])).

tff(c_6176,plain,(
    ~ r1_tarski(k1_tops_1('#skF_1','#skF_2'),k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_5474])).

tff(c_6283,plain,
    ( ~ r1_tarski(k1_tops_1('#skF_1','#skF_2'),k2_pre_topc('#skF_1','#skF_2'))
    | ~ m1_subset_1(k2_pre_topc('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_2265,c_6176])).

tff(c_6293,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_353,c_166,c_6283])).

tff(c_6294,plain,(
    r1_tarski('#skF_2',k2_pre_topc('#skF_1',k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2')))) ),
    inference(splitRight,[status(thm)],[c_5474])).

tff(c_4040,plain,(
    ! [A_169,C_170] :
      ( r1_tarski(A_169,k2_pre_topc('#skF_1',C_170))
      | ~ r1_tarski(A_169,k2_pre_topc('#skF_1','#skF_2'))
      | ~ r1_tarski('#skF_2',C_170)
      | ~ m1_subset_1(C_170,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(resolution,[status(thm)],[c_2679,c_16])).

tff(c_11043,plain,(
    ! [C_255] :
      ( r1_tarski(k2_pre_topc('#skF_1',k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2'))),k2_pre_topc('#skF_1',C_255))
      | ~ r1_tarski('#skF_2',C_255)
      | ~ m1_subset_1(C_255,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(resolution,[status(thm)],[c_1933,c_4040])).

tff(c_11109,plain,
    ( r1_tarski(k2_pre_topc('#skF_1',k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2'))),k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')))
    | ~ r1_tarski('#skF_2',k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')))
    | ~ m1_subset_1(k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_480,c_11043])).

tff(c_11160,plain,(
    r1_tarski(k2_pre_topc('#skF_1',k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2'))),k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3201,c_4787,c_11109])).

tff(c_2625,plain,(
    ! [C_141] :
      ( r1_tarski(k2_pre_topc('#skF_1','#skF_2'),k2_pre_topc('#skF_1',C_141))
      | ~ r1_tarski('#skF_2',C_141)
      | ~ m1_subset_1(C_141,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_2553])).

tff(c_82,plain,(
    ! [A_49,B_50] :
      ( r1_tarski(k1_tops_1(A_49,k1_tops_1(A_49,B_50)),k1_tops_1(A_49,B_50))
      | ~ m1_subset_1(B_50,k1_zfmisc_1(u1_struct_0(A_49)))
      | ~ l1_pre_topc(A_49) ) ),
    inference(resolution,[status(thm)],[c_77,c_18])).

tff(c_562,plain,
    ( r1_tarski(k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2')),k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2')))
    | ~ m1_subset_1(k2_pre_topc('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_392,c_82])).

tff(c_588,plain,(
    r1_tarski(k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2')),k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_353,c_562])).

tff(c_6295,plain,(
    r1_tarski(k1_tops_1('#skF_1','#skF_2'),k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_5474])).

tff(c_6348,plain,
    ( r1_tarski(k1_tops_1('#skF_1','#skF_2'),k2_pre_topc('#skF_1',k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2'))))
    | ~ r1_tarski(k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2')),k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2'))) ),
    inference(resolution,[status(thm)],[c_6295,c_1018])).

tff(c_6383,plain,(
    r1_tarski(k1_tops_1('#skF_1','#skF_2'),k2_pre_topc('#skF_1',k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_588,c_6348])).

tff(c_634,plain,
    ( r1_tarski(k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')),k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')))
    | ~ m1_subset_1(k1_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_480,c_76])).

tff(c_655,plain,(
    r1_tarski(k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')),k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_469,c_634])).

tff(c_2536,plain,(
    ! [C_141] :
      ( r1_tarski(k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')),k2_pre_topc('#skF_1',C_141))
      | ~ r1_tarski(k1_tops_1('#skF_1','#skF_2'),C_141)
      | ~ m1_subset_1(C_141,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ m1_subset_1(k1_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_655,c_2504])).

tff(c_10157,plain,(
    ! [C_246] :
      ( r1_tarski(k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')),k2_pre_topc('#skF_1',C_246))
      | ~ r1_tarski(k1_tops_1('#skF_1','#skF_2'),C_246)
      | ~ m1_subset_1(C_246,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_469,c_2536])).

tff(c_10216,plain,
    ( r1_tarski(k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')),k2_pre_topc('#skF_1',k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2'))))
    | ~ r1_tarski(k1_tops_1('#skF_1','#skF_2'),k2_pre_topc('#skF_1',k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2'))))
    | ~ m1_subset_1(k2_pre_topc('#skF_1',k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2'))),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_883,c_10157])).

tff(c_10268,plain,(
    r1_tarski(k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')),k2_pre_topc('#skF_1',k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4373,c_6383,c_10216])).

tff(c_10668,plain,(
    ! [A_249] :
      ( r1_tarski(A_249,k2_pre_topc('#skF_1',k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2'))))
      | ~ r1_tarski(A_249,k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2'))) ) ),
    inference(resolution,[status(thm)],[c_10268,c_16])).

tff(c_18291,plain,(
    ! [A_329,A_330] :
      ( r1_tarski(A_329,k2_pre_topc('#skF_1',k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2'))))
      | ~ r1_tarski(A_329,A_330)
      | ~ r1_tarski(A_330,k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2'))) ) ),
    inference(resolution,[status(thm)],[c_10668,c_16])).

tff(c_18445,plain,(
    ! [C_141] :
      ( r1_tarski(k2_pre_topc('#skF_1','#skF_2'),k2_pre_topc('#skF_1',k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2'))))
      | ~ r1_tarski(k2_pre_topc('#skF_1',C_141),k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')))
      | ~ r1_tarski('#skF_2',C_141)
      | ~ m1_subset_1(C_141,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(resolution,[status(thm)],[c_2625,c_18291])).

tff(c_18780,plain,(
    ! [C_331] :
      ( ~ r1_tarski(k2_pre_topc('#skF_1',C_331),k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')))
      | ~ r1_tarski('#skF_2',C_331)
      | ~ m1_subset_1(C_331,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_818,c_18445])).

tff(c_18847,plain,
    ( ~ r1_tarski(k2_pre_topc('#skF_1',k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2'))),k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')))
    | ~ r1_tarski('#skF_2',k2_pre_topc('#skF_1',k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2'))))
    | ~ m1_subset_1(k2_pre_topc('#skF_1',k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2'))),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_883,c_18780])).

tff(c_18912,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4373,c_6294,c_11160,c_18847])).

tff(c_18913,plain,(
    v4_tops_1(k2_pre_topc('#skF_1','#skF_2'),'#skF_1') ),
    inference(splitRight,[status(thm)],[c_744])).

tff(c_304,plain,(
    ! [A_68,B_69] :
      ( r1_tarski(k1_tops_1(A_68,k2_pre_topc(A_68,B_69)),B_69)
      | ~ v4_tops_1(B_69,A_68)
      | ~ m1_subset_1(B_69,k1_zfmisc_1(u1_struct_0(A_68)))
      | ~ l1_pre_topc(A_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_19918,plain,(
    ! [A_364,B_365,A_366] :
      ( r1_tarski(A_364,B_365)
      | ~ r1_tarski(A_364,k1_tops_1(A_366,k2_pre_topc(A_366,B_365)))
      | ~ v4_tops_1(B_365,A_366)
      | ~ m1_subset_1(B_365,k1_zfmisc_1(u1_struct_0(A_366)))
      | ~ l1_pre_topc(A_366) ) ),
    inference(resolution,[status(thm)],[c_304,c_16])).

tff(c_19927,plain,
    ( r1_tarski(k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2')),'#skF_2')
    | ~ v4_tops_1('#skF_2','#skF_1')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_588,c_19918])).

tff(c_19949,plain,(
    r1_tarski(k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2')),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_28,c_19927])).

tff(c_20934,plain,(
    ! [C_387] :
      ( r1_tarski(k2_pre_topc('#skF_1','#skF_2'),k2_pre_topc('#skF_1',C_387))
      | ~ r1_tarski('#skF_2',C_387)
      | ~ m1_subset_1(C_387,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_270,c_20875])).

tff(c_21021,plain,(
    ! [C_387] :
      ( r1_tarski(k2_pre_topc('#skF_1','#skF_2'),k2_pre_topc('#skF_1',C_387))
      | ~ r1_tarski('#skF_2',C_387)
      | ~ m1_subset_1(C_387,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_20934])).

tff(c_21261,plain,(
    ! [C_394] :
      ( r1_tarski('#skF_2',k2_pre_topc('#skF_1',C_394))
      | ~ r1_tarski(k2_pre_topc('#skF_1','#skF_2'),C_394)
      | ~ m1_subset_1(C_394,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(resolution,[status(thm)],[c_40,c_21193])).

tff(c_21275,plain,(
    ! [B_7] :
      ( r1_tarski('#skF_2',k2_pre_topc('#skF_1',k2_pre_topc('#skF_1',B_7)))
      | ~ r1_tarski(k2_pre_topc('#skF_1','#skF_2'),k2_pre_topc('#skF_1',B_7))
      | ~ m1_subset_1(B_7,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_10,c_21261])).

tff(c_22998,plain,(
    ! [B_431] :
      ( r1_tarski('#skF_2',k2_pre_topc('#skF_1',k2_pre_topc('#skF_1',B_431)))
      | ~ r1_tarski(k2_pre_topc('#skF_1','#skF_2'),k2_pre_topc('#skF_1',B_431))
      | ~ m1_subset_1(B_431,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_21275])).

tff(c_23355,plain,(
    ! [C_434] :
      ( r1_tarski('#skF_2',k2_pre_topc('#skF_1',k2_pre_topc('#skF_1',C_434)))
      | ~ r1_tarski('#skF_2',C_434)
      | ~ m1_subset_1(C_434,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(resolution,[status(thm)],[c_21021,c_22998])).

tff(c_23604,plain,(
    ! [A_437,C_438] :
      ( r1_tarski(A_437,k2_pre_topc('#skF_1',k2_pre_topc('#skF_1',C_438)))
      | ~ r1_tarski(A_437,'#skF_2')
      | ~ r1_tarski('#skF_2',C_438)
      | ~ m1_subset_1(C_438,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(resolution,[status(thm)],[c_23355,c_16])).

tff(c_29753,plain,(
    ! [A_519,C_520,A_521] :
      ( r1_tarski(A_519,k2_pre_topc('#skF_1',k2_pre_topc('#skF_1',C_520)))
      | ~ r1_tarski(A_519,A_521)
      | ~ r1_tarski(A_521,'#skF_2')
      | ~ r1_tarski('#skF_2',C_520)
      | ~ m1_subset_1(C_520,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(resolution,[status(thm)],[c_23604,c_16])).

tff(c_29905,plain,(
    ! [C_520] :
      ( r1_tarski(k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2')),k2_pre_topc('#skF_1',k2_pre_topc('#skF_1',C_520)))
      | ~ r1_tarski(k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2')),'#skF_2')
      | ~ r1_tarski('#skF_2',C_520)
      | ~ m1_subset_1(C_520,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(resolution,[status(thm)],[c_588,c_29753])).

tff(c_30539,plain,(
    ! [C_525] :
      ( r1_tarski(k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2')),k2_pre_topc('#skF_1',k2_pre_topc('#skF_1',C_525)))
      | ~ r1_tarski('#skF_2',C_525)
      | ~ m1_subset_1(C_525,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_19949,c_29905])).

tff(c_30614,plain,
    ( r1_tarski(k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2')),k2_pre_topc('#skF_1',k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2'))))
    | ~ r1_tarski('#skF_2',k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')))
    | ~ m1_subset_1(k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_480,c_30539])).

tff(c_30670,plain,
    ( r1_tarski(k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2')),k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')))
    | ~ r1_tarski('#skF_2',k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22101,c_480,c_30614])).

tff(c_30677,plain,(
    ~ r1_tarski('#skF_2',k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_30670])).

tff(c_30701,plain,
    ( ~ v4_tops_1('#skF_2','#skF_1')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_4,c_30677])).

tff(c_30724,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_28,c_30701])).

tff(c_30725,plain,(
    r1_tarski(k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2')),k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_30670])).

tff(c_38751,plain,(
    ! [B_617,A_618,C_619] :
      ( r1_tarski(B_617,k2_pre_topc(A_618,C_619))
      | ~ r1_tarski(k1_tops_1(A_618,B_617),C_619)
      | ~ m1_subset_1(C_619,k1_zfmisc_1(u1_struct_0(A_618)))
      | ~ m1_subset_1(k1_tops_1(A_618,B_617),k1_zfmisc_1(u1_struct_0(A_618)))
      | ~ v4_tops_1(B_617,A_618)
      | ~ m1_subset_1(B_617,k1_zfmisc_1(u1_struct_0(A_618)))
      | ~ l1_pre_topc(A_618) ) ),
    inference(resolution,[status(thm)],[c_4,c_20875])).

tff(c_38801,plain,
    ( r1_tarski(k2_pre_topc('#skF_1','#skF_2'),k2_pre_topc('#skF_1',k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2'))))
    | ~ m1_subset_1(k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_subset_1(k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2')),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ v4_tops_1(k2_pre_topc('#skF_1','#skF_2'),'#skF_1')
    | ~ m1_subset_1(k2_pre_topc('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_30725,c_38751])).

tff(c_39031,plain,
    ( r1_tarski(k2_pre_topc('#skF_1','#skF_2'),k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')))
    | ~ m1_subset_1(k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2')),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_353,c_18913,c_22101,c_480,c_38801])).

tff(c_39032,plain,(
    ~ m1_subset_1(k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2')),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(negUnitSimplification,[status(thm)],[c_22282,c_39031])).

tff(c_39213,plain,
    ( ~ m1_subset_1(k2_pre_topc('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_8,c_39032])).

tff(c_39217,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_353,c_39213])).

tff(c_39219,plain,(
    r1_tarski(k2_pre_topc('#skF_1','#skF_2'),k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_22139])).

tff(c_21484,plain,(
    ! [A_400,A_401,C_402,B_403] :
      ( r1_tarski(A_400,k1_tops_1(A_401,C_402))
      | ~ r1_tarski(A_400,k1_tops_1(A_401,B_403))
      | ~ r1_tarski(B_403,C_402)
      | ~ m1_subset_1(C_402,k1_zfmisc_1(u1_struct_0(A_401)))
      | ~ m1_subset_1(B_403,k1_zfmisc_1(u1_struct_0(A_401)))
      | ~ l1_pre_topc(A_401) ) ),
    inference(resolution,[status(thm)],[c_411,c_16])).

tff(c_52682,plain,(
    ! [A_782,B_783,C_784,C_785] :
      ( r1_tarski(k1_tops_1(A_782,B_783),k1_tops_1(A_782,C_784))
      | ~ r1_tarski(C_785,C_784)
      | ~ m1_subset_1(C_784,k1_zfmisc_1(u1_struct_0(A_782)))
      | ~ r1_tarski(B_783,C_785)
      | ~ m1_subset_1(C_785,k1_zfmisc_1(u1_struct_0(A_782)))
      | ~ m1_subset_1(B_783,k1_zfmisc_1(u1_struct_0(A_782)))
      | ~ l1_pre_topc(A_782) ) ),
    inference(resolution,[status(thm)],[c_22,c_21484])).

tff(c_53463,plain,(
    ! [A_789,B_790] :
      ( r1_tarski(k1_tops_1(A_789,B_790),k1_tops_1(A_789,k2_pre_topc('#skF_1','#skF_2')))
      | ~ m1_subset_1(k2_pre_topc('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0(A_789)))
      | ~ r1_tarski(B_790,'#skF_2')
      | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0(A_789)))
      | ~ m1_subset_1(B_790,k1_zfmisc_1(u1_struct_0(A_789)))
      | ~ l1_pre_topc(A_789) ) ),
    inference(resolution,[status(thm)],[c_40,c_52682])).

tff(c_53562,plain,
    ( r1_tarski(k1_tops_1('#skF_1','#skF_2'),k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2')))
    | ~ m1_subset_1(k2_pre_topc('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ r1_tarski(k1_tops_1('#skF_1','#skF_2'),'#skF_2')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_subset_1(k1_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_95,c_53463])).

tff(c_53619,plain,(
    r1_tarski(k1_tops_1('#skF_1','#skF_2'),k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_469,c_30,c_61,c_353,c_53562])).

tff(c_53754,plain,(
    ! [A_791] :
      ( r1_tarski(A_791,k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2')))
      | ~ r1_tarski(A_791,k1_tops_1('#skF_1','#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_53619,c_16])).

tff(c_433,plain,(
    ! [A_12,A_72,C_74,B_73] :
      ( r1_tarski(A_12,k1_tops_1(A_72,C_74))
      | ~ r1_tarski(A_12,k1_tops_1(A_72,B_73))
      | ~ r1_tarski(B_73,C_74)
      | ~ m1_subset_1(C_74,k1_zfmisc_1(u1_struct_0(A_72)))
      | ~ m1_subset_1(B_73,k1_zfmisc_1(u1_struct_0(A_72)))
      | ~ l1_pre_topc(A_72) ) ),
    inference(resolution,[status(thm)],[c_411,c_16])).

tff(c_53799,plain,(
    ! [A_791,C_74] :
      ( r1_tarski(A_791,k1_tops_1('#skF_1',C_74))
      | ~ r1_tarski(k2_pre_topc('#skF_1','#skF_2'),C_74)
      | ~ m1_subset_1(C_74,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ m1_subset_1(k2_pre_topc('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1')
      | ~ r1_tarski(A_791,k1_tops_1('#skF_1','#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_53754,c_433])).

tff(c_57116,plain,(
    ! [A_825,C_826] :
      ( r1_tarski(A_825,k1_tops_1('#skF_1',C_826))
      | ~ r1_tarski(k2_pre_topc('#skF_1','#skF_2'),C_826)
      | ~ m1_subset_1(C_826,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ r1_tarski(A_825,k1_tops_1('#skF_1','#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_353,c_53799])).

tff(c_57118,plain,(
    ! [A_825] :
      ( r1_tarski(A_825,k1_tops_1('#skF_1',k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2'))))
      | ~ r1_tarski(k2_pre_topc('#skF_1','#skF_2'),k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')))
      | ~ r1_tarski(A_825,k1_tops_1('#skF_1','#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_22101,c_57116])).

tff(c_57146,plain,(
    ! [A_827] :
      ( r1_tarski(A_827,k1_tops_1('#skF_1',k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2'))))
      | ~ r1_tarski(A_827,k1_tops_1('#skF_1','#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_39219,c_57118])).

tff(c_57506,plain,(
    ! [A_832,A_833] :
      ( r1_tarski(A_832,k1_tops_1('#skF_1',k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2'))))
      | ~ r1_tarski(A_832,A_833)
      | ~ r1_tarski(A_833,k1_tops_1('#skF_1','#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_57146,c_16])).

tff(c_57770,plain,
    ( r1_tarski(k1_tops_1('#skF_1','#skF_2'),k1_tops_1('#skF_1',k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2'))))
    | ~ r1_tarski(k1_tops_1('#skF_1','#skF_2'),k1_tops_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_152,c_57506])).

tff(c_57916,plain,(
    r1_tarski(k1_tops_1('#skF_1','#skF_2'),k1_tops_1('#skF_1',k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_152,c_57770])).

tff(c_18915,plain,(
    ! [B_332] :
      ( r1_tarski(k2_pre_topc('#skF_1',B_332),k2_pre_topc('#skF_1','#skF_2'))
      | ~ r1_tarski(B_332,k2_pre_topc('#skF_1','#skF_2'))
      | ~ m1_subset_1(B_332,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_353,c_525])).

tff(c_20389,plain,(
    ! [A_380,B_381] :
      ( r1_tarski(A_380,k2_pre_topc('#skF_1','#skF_2'))
      | ~ r1_tarski(A_380,k2_pre_topc('#skF_1',B_381))
      | ~ r1_tarski(B_381,k2_pre_topc('#skF_1','#skF_2'))
      | ~ m1_subset_1(B_381,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(resolution,[status(thm)],[c_18915,c_16])).

tff(c_20426,plain,
    ( r1_tarski(k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')),k2_pre_topc('#skF_1','#skF_2'))
    | ~ r1_tarski(k1_tops_1('#skF_1','#skF_2'),k2_pre_topc('#skF_1','#skF_2'))
    | ~ m1_subset_1(k1_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_655,c_20389])).

tff(c_20511,plain,(
    r1_tarski(k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')),k2_pre_topc('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_469,c_166,c_20426])).

tff(c_19988,plain,(
    ! [A_367] :
      ( r1_tarski(A_367,'#skF_2')
      | ~ r1_tarski(A_367,k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2'))) ) ),
    inference(resolution,[status(thm)],[c_19949,c_16])).

tff(c_19995,plain,(
    ! [B_25] :
      ( r1_tarski(k1_tops_1('#skF_1',B_25),'#skF_2')
      | ~ r1_tarski(B_25,k2_pre_topc('#skF_1','#skF_2'))
      | ~ m1_subset_1(k2_pre_topc('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ m1_subset_1(B_25,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_22,c_19988])).

tff(c_20008,plain,(
    ! [B_25] :
      ( r1_tarski(k1_tops_1('#skF_1',B_25),'#skF_2')
      | ~ r1_tarski(B_25,k2_pre_topc('#skF_1','#skF_2'))
      | ~ m1_subset_1(B_25,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_353,c_19995])).

tff(c_22114,plain,
    ( r1_tarski(k1_tops_1('#skF_1',k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2'))),'#skF_2')
    | ~ r1_tarski(k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')),k2_pre_topc('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_22101,c_20008])).

tff(c_22144,plain,(
    r1_tarski(k1_tops_1('#skF_1',k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2'))),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20511,c_22114])).

tff(c_20917,plain,(
    ! [C_387] :
      ( r1_tarski(k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')),k2_pre_topc('#skF_1',C_387))
      | ~ r1_tarski(k1_tops_1('#skF_1','#skF_2'),C_387)
      | ~ m1_subset_1(C_387,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ m1_subset_1(k1_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_655,c_20875])).

tff(c_21006,plain,(
    ! [C_387] :
      ( r1_tarski(k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')),k2_pre_topc('#skF_1',C_387))
      | ~ r1_tarski(k1_tops_1('#skF_1','#skF_2'),C_387)
      | ~ m1_subset_1(C_387,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_469,c_20917])).

tff(c_182,plain,(
    ! [B_58,A_59] :
      ( r1_tarski(B_58,k2_pre_topc(A_59,k1_tops_1(A_59,B_58)))
      | ~ v4_tops_1(B_58,A_59)
      | ~ m1_subset_1(B_58,k1_zfmisc_1(u1_struct_0(A_59)))
      | ~ l1_pre_topc(A_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_20290,plain,(
    ! [A_376,A_377,B_378] :
      ( r1_tarski(A_376,k2_pre_topc(A_377,k1_tops_1(A_377,B_378)))
      | ~ r1_tarski(A_376,B_378)
      | ~ v4_tops_1(B_378,A_377)
      | ~ m1_subset_1(B_378,k1_zfmisc_1(u1_struct_0(A_377)))
      | ~ l1_pre_topc(A_377) ) ),
    inference(resolution,[status(thm)],[c_182,c_16])).

tff(c_2,plain,(
    ! [B_3,A_1] :
      ( v4_tops_1(B_3,A_1)
      | ~ r1_tarski(B_3,k2_pre_topc(A_1,k1_tops_1(A_1,B_3)))
      | ~ r1_tarski(k1_tops_1(A_1,k2_pre_topc(A_1,B_3)),B_3)
      | ~ m1_subset_1(B_3,k1_zfmisc_1(u1_struct_0(A_1)))
      | ~ l1_pre_topc(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_65303,plain,(
    ! [A_885,B_886,A_887] :
      ( v4_tops_1(k2_pre_topc(A_885,k1_tops_1(A_885,B_886)),A_887)
      | ~ r1_tarski(k2_pre_topc(A_885,k1_tops_1(A_885,B_886)),k2_pre_topc(A_887,k1_tops_1(A_887,k2_pre_topc(A_885,k1_tops_1(A_885,B_886)))))
      | ~ m1_subset_1(k2_pre_topc(A_885,k1_tops_1(A_885,B_886)),k1_zfmisc_1(u1_struct_0(A_887)))
      | ~ l1_pre_topc(A_887)
      | ~ r1_tarski(k1_tops_1(A_887,k2_pre_topc(A_887,k2_pre_topc(A_885,k1_tops_1(A_885,B_886)))),B_886)
      | ~ v4_tops_1(B_886,A_885)
      | ~ m1_subset_1(B_886,k1_zfmisc_1(u1_struct_0(A_885)))
      | ~ l1_pre_topc(A_885) ) ),
    inference(resolution,[status(thm)],[c_20290,c_2])).

tff(c_65375,plain,
    ( v4_tops_1(k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')),'#skF_1')
    | ~ m1_subset_1(k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ r1_tarski(k1_tops_1('#skF_1',k2_pre_topc('#skF_1',k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')))),'#skF_2')
    | ~ v4_tops_1('#skF_2','#skF_1')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1')
    | ~ r1_tarski(k1_tops_1('#skF_1','#skF_2'),k1_tops_1('#skF_1',k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2'))))
    | ~ m1_subset_1(k1_tops_1('#skF_1',k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2'))),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_21006,c_65303])).

tff(c_65445,plain,
    ( v4_tops_1(k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')),'#skF_1')
    | ~ m1_subset_1(k1_tops_1('#skF_1',k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2'))),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_57916,c_32,c_30,c_28,c_22144,c_480,c_22101,c_65375])).

tff(c_65465,plain,(
    ~ m1_subset_1(k1_tops_1('#skF_1',k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2'))),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_65445])).

tff(c_65468,plain,
    ( ~ m1_subset_1(k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_8,c_65465])).

tff(c_65472,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_22101,c_65468])).

tff(c_65474,plain,(
    m1_subset_1(k1_tops_1('#skF_1',k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2'))),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_65445])).

tff(c_19307,plain,(
    ! [A_342,B_343] :
      ( k1_tops_1(A_342,k1_tops_1(A_342,k2_pre_topc(A_342,B_343))) = k1_tops_1(A_342,k2_pre_topc(A_342,B_343))
      | ~ m1_subset_1(B_343,k1_zfmisc_1(u1_struct_0(A_342)))
      | ~ l1_pre_topc(A_342) ) ),
    inference(resolution,[status(thm)],[c_10,c_84])).

tff(c_19309,plain,
    ( k1_tops_1('#skF_1',k1_tops_1('#skF_1',k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')))) = k1_tops_1('#skF_1',k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_469,c_19307])).

tff(c_19320,plain,(
    k1_tops_1('#skF_1',k1_tops_1('#skF_1',k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')))) = k1_tops_1('#skF_1',k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_19309])).

tff(c_21503,plain,(
    ! [A_400,C_402] :
      ( r1_tarski(A_400,k1_tops_1('#skF_1',C_402))
      | ~ r1_tarski(A_400,k1_tops_1('#skF_1','#skF_2'))
      | ~ r1_tarski(k1_tops_1('#skF_1','#skF_2'),C_402)
      | ~ m1_subset_1(C_402,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ m1_subset_1(k1_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_95,c_21484])).

tff(c_40081,plain,(
    ! [A_629,C_630] :
      ( r1_tarski(A_629,k1_tops_1('#skF_1',C_630))
      | ~ r1_tarski(A_629,k1_tops_1('#skF_1','#skF_2'))
      | ~ r1_tarski(k1_tops_1('#skF_1','#skF_2'),C_630)
      | ~ m1_subset_1(C_630,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_469,c_21503])).

tff(c_40090,plain,(
    ! [B_25,C_630] :
      ( r1_tarski(k1_tops_1('#skF_1',B_25),k1_tops_1('#skF_1',C_630))
      | ~ r1_tarski(k1_tops_1('#skF_1','#skF_2'),C_630)
      | ~ m1_subset_1(C_630,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ r1_tarski(B_25,'#skF_2')
      | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ m1_subset_1(B_25,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_22,c_40081])).

tff(c_85323,plain,(
    ! [B_1013,C_1014] :
      ( r1_tarski(k1_tops_1('#skF_1',B_1013),k1_tops_1('#skF_1',C_1014))
      | ~ r1_tarski(k1_tops_1('#skF_1','#skF_2'),C_1014)
      | ~ m1_subset_1(C_1014,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ r1_tarski(B_1013,'#skF_2')
      | ~ m1_subset_1(B_1013,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_40090])).

tff(c_85561,plain,(
    ! [B_1013] :
      ( r1_tarski(k1_tops_1('#skF_1',B_1013),k1_tops_1('#skF_1','#skF_2'))
      | ~ r1_tarski(k1_tops_1('#skF_1','#skF_2'),k1_tops_1('#skF_1','#skF_2'))
      | ~ m1_subset_1(k1_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ r1_tarski(B_1013,'#skF_2')
      | ~ m1_subset_1(B_1013,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_95,c_85323])).

tff(c_85703,plain,(
    ! [B_1015] :
      ( r1_tarski(k1_tops_1('#skF_1',B_1015),k1_tops_1('#skF_1','#skF_2'))
      | ~ r1_tarski(B_1015,'#skF_2')
      | ~ m1_subset_1(B_1015,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_469,c_152,c_85561])).

tff(c_85825,plain,
    ( r1_tarski(k1_tops_1('#skF_1',k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2'))),k1_tops_1('#skF_1','#skF_2'))
    | ~ r1_tarski(k1_tops_1('#skF_1',k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2'))),'#skF_2')
    | ~ m1_subset_1(k1_tops_1('#skF_1',k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2'))),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_19320,c_85703])).

tff(c_85968,plain,(
    r1_tarski(k1_tops_1('#skF_1',k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2'))),k1_tops_1('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_65474,c_22144,c_85825])).

tff(c_86060,plain,
    ( v4_tops_1(k1_tops_1('#skF_1','#skF_2'),'#skF_1')
    | ~ r1_tarski(k1_tops_1('#skF_1','#skF_2'),k2_pre_topc('#skF_1',k1_tops_1('#skF_1',k1_tops_1('#skF_1','#skF_2'))))
    | ~ m1_subset_1(k1_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_85968,c_2])).

tff(c_86184,plain,(
    v4_tops_1(k1_tops_1('#skF_1','#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_469,c_468,c_95,c_86060])).

tff(c_86186,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_86184])).

tff(c_86187,plain,(
    ~ v4_tops_1(k2_pre_topc('#skF_1','#skF_2'),'#skF_1') ),
    inference(splitRight,[status(thm)],[c_26])).

tff(c_86709,plain,(
    r1_tarski(k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2')),k2_pre_topc('#skF_1','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_86664])).

tff(c_87068,plain,(
    ! [B_1066,A_1067] :
      ( v4_tops_1(B_1066,A_1067)
      | ~ r1_tarski(B_1066,k2_pre_topc(A_1067,k1_tops_1(A_1067,B_1066)))
      | ~ r1_tarski(k1_tops_1(A_1067,k2_pre_topc(A_1067,B_1066)),B_1066)
      | ~ m1_subset_1(B_1066,k1_zfmisc_1(u1_struct_0(A_1067)))
      | ~ l1_pre_topc(A_1067) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_87097,plain,
    ( v4_tops_1(k2_pre_topc('#skF_1','#skF_2'),'#skF_1')
    | ~ r1_tarski(k2_pre_topc('#skF_1','#skF_2'),k2_pre_topc('#skF_1',k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2'))))
    | ~ r1_tarski(k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2')),k2_pre_topc('#skF_1','#skF_2'))
    | ~ m1_subset_1(k2_pre_topc('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_86270,c_87068])).

tff(c_87116,plain,
    ( v4_tops_1(k2_pre_topc('#skF_1','#skF_2'),'#skF_1')
    | ~ r1_tarski(k2_pre_topc('#skF_1','#skF_2'),k2_pre_topc('#skF_1',k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_86710,c_86709,c_87097])).

tff(c_87117,plain,(
    ~ r1_tarski(k2_pre_topc('#skF_1','#skF_2'),k2_pre_topc('#skF_1',k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2')))) ),
    inference(negUnitSimplification,[status(thm)],[c_86187,c_87116])).

tff(c_87121,plain,
    ( ~ r1_tarski('#skF_2',k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2')))
    | ~ m1_subset_1(k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2')),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_24,c_87117])).

tff(c_87127,plain,
    ( ~ r1_tarski('#skF_2',k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2')))
    | ~ m1_subset_1(k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2')),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_87121])).

tff(c_87131,plain,(
    ~ m1_subset_1(k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2')),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_87127])).

tff(c_87134,plain,
    ( ~ m1_subset_1(k2_pre_topc('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_8,c_87131])).

tff(c_87138,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_86710,c_87134])).

tff(c_87140,plain,(
    m1_subset_1(k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2')),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_87127])).

tff(c_87148,plain,
    ( k2_pre_topc('#skF_1',k2_pre_topc('#skF_1',k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2')))) = k2_pre_topc('#skF_1',k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_87140,c_14])).

tff(c_87161,plain,(
    k2_pre_topc('#skF_1',k2_pre_topc('#skF_1',k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2')))) = k2_pre_topc('#skF_1',k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_87148])).

tff(c_86400,plain,(
    ! [A_1041,B_1042] :
      ( r1_tarski(k2_pre_topc(A_1041,B_1042),k2_pre_topc(A_1041,k2_pre_topc(A_1041,B_1042)))
      | ~ m1_subset_1(B_1042,k1_zfmisc_1(u1_struct_0(A_1041)))
      | ~ l1_pre_topc(A_1041) ) ),
    inference(resolution,[status(thm)],[c_86231,c_20])).

tff(c_86415,plain,
    ( r1_tarski(k2_pre_topc('#skF_1','#skF_2'),k2_pre_topc('#skF_1','#skF_2'))
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_86270,c_86400])).

tff(c_86424,plain,(
    r1_tarski(k2_pre_topc('#skF_1','#skF_2'),k2_pre_topc('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_86415])).

tff(c_86529,plain,(
    ! [A_1045,B_1046,C_1047] :
      ( r1_tarski(k2_pre_topc(A_1045,B_1046),k2_pre_topc(A_1045,C_1047))
      | ~ r1_tarski(B_1046,C_1047)
      | ~ m1_subset_1(C_1047,k1_zfmisc_1(u1_struct_0(A_1045)))
      | ~ m1_subset_1(B_1046,k1_zfmisc_1(u1_struct_0(A_1045)))
      | ~ l1_pre_topc(A_1045) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_88642,plain,(
    ! [A_1119,A_1120,C_1121,B_1122] :
      ( r1_tarski(A_1119,k2_pre_topc(A_1120,C_1121))
      | ~ r1_tarski(A_1119,k2_pre_topc(A_1120,B_1122))
      | ~ r1_tarski(B_1122,C_1121)
      | ~ m1_subset_1(C_1121,k1_zfmisc_1(u1_struct_0(A_1120)))
      | ~ m1_subset_1(B_1122,k1_zfmisc_1(u1_struct_0(A_1120)))
      | ~ l1_pre_topc(A_1120) ) ),
    inference(resolution,[status(thm)],[c_86529,c_16])).

tff(c_88684,plain,(
    ! [C_1121] :
      ( r1_tarski(k2_pre_topc('#skF_1','#skF_2'),k2_pre_topc('#skF_1',C_1121))
      | ~ r1_tarski('#skF_2',C_1121)
      | ~ m1_subset_1(C_1121,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_86424,c_88642])).

tff(c_89086,plain,(
    ! [C_1127] :
      ( r1_tarski(k2_pre_topc('#skF_1','#skF_2'),k2_pre_topc('#skF_1',C_1127))
      | ~ r1_tarski('#skF_2',C_1127)
      | ~ m1_subset_1(C_1127,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_88684])).

tff(c_89114,plain,
    ( r1_tarski(k2_pre_topc('#skF_1','#skF_2'),k2_pre_topc('#skF_1',k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2'))))
    | ~ r1_tarski('#skF_2',k2_pre_topc('#skF_1',k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2'))))
    | ~ m1_subset_1(k2_pre_topc('#skF_1',k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2'))),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_87161,c_89086])).

tff(c_89144,plain,
    ( ~ r1_tarski('#skF_2',k2_pre_topc('#skF_1',k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2'))))
    | ~ m1_subset_1(k2_pre_topc('#skF_1',k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2'))),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(negUnitSimplification,[status(thm)],[c_87117,c_89114])).

tff(c_89847,plain,(
    ~ m1_subset_1(k2_pre_topc('#skF_1',k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2'))),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_89144])).

tff(c_89850,plain,
    ( ~ m1_subset_1(k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2')),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_10,c_89847])).

tff(c_89854,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_87140,c_89850])).

tff(c_89855,plain,(
    ~ r1_tarski('#skF_2',k2_pre_topc('#skF_1',k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2')))) ),
    inference(splitRight,[status(thm)],[c_89144])).

tff(c_86238,plain,(
    ! [A_1028,B_1029] :
      ( k1_tops_1(A_1028,k1_tops_1(A_1028,B_1029)) = k1_tops_1(A_1028,B_1029)
      | ~ m1_subset_1(B_1029,k1_zfmisc_1(u1_struct_0(A_1028)))
      | ~ l1_pre_topc(A_1028) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_86244,plain,
    ( k1_tops_1('#skF_1',k1_tops_1('#skF_1','#skF_2')) = k1_tops_1('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_30,c_86238])).

tff(c_86249,plain,(
    k1_tops_1('#skF_1',k1_tops_1('#skF_1','#skF_2')) = k1_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_86244])).

tff(c_86208,plain,(
    ! [A_1021,B_1022] :
      ( m1_subset_1(k1_tops_1(A_1021,B_1022),k1_zfmisc_1(u1_struct_0(A_1021)))
      | ~ m1_subset_1(B_1022,k1_zfmisc_1(u1_struct_0(A_1021)))
      | ~ l1_pre_topc(A_1021) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_86292,plain,(
    ! [A_1034,B_1035] :
      ( r1_tarski(k1_tops_1(A_1034,B_1035),k2_pre_topc(A_1034,k1_tops_1(A_1034,B_1035)))
      | ~ m1_subset_1(B_1035,k1_zfmisc_1(u1_struct_0(A_1034)))
      | ~ l1_pre_topc(A_1034) ) ),
    inference(resolution,[status(thm)],[c_86208,c_20])).

tff(c_86302,plain,
    ( r1_tarski(k1_tops_1('#skF_1',k1_tops_1('#skF_1','#skF_2')),k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')))
    | ~ m1_subset_1(k1_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_86249,c_86292])).

tff(c_86308,plain,
    ( r1_tarski(k1_tops_1('#skF_1','#skF_2'),k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')))
    | ~ m1_subset_1(k1_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_86249,c_86302])).

tff(c_86458,plain,(
    ~ m1_subset_1(k1_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_86308])).

tff(c_86461,plain,
    ( ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_8,c_86458])).

tff(c_86465,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_86461])).

tff(c_86467,plain,(
    m1_subset_1(k1_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_86308])).

tff(c_89856,plain,(
    m1_subset_1(k2_pre_topc('#skF_1',k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2'))),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_89144])).

tff(c_86199,plain,(
    ! [B_1019,A_1020] :
      ( r1_tarski(B_1019,k2_pre_topc(A_1020,B_1019))
      | ~ m1_subset_1(B_1019,k1_zfmisc_1(u1_struct_0(A_1020)))
      | ~ l1_pre_topc(A_1020) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_86201,plain,
    ( r1_tarski('#skF_2',k2_pre_topc('#skF_1','#skF_2'))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_30,c_86199])).

tff(c_86204,plain,(
    r1_tarski('#skF_2',k2_pre_topc('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_86201])).

tff(c_86309,plain,(
    ! [A_1036,B_1037] :
      ( r1_tarski(k1_tops_1(A_1036,k1_tops_1(A_1036,B_1037)),k1_tops_1(A_1036,B_1037))
      | ~ m1_subset_1(B_1037,k1_zfmisc_1(u1_struct_0(A_1036)))
      | ~ l1_pre_topc(A_1036) ) ),
    inference(resolution,[status(thm)],[c_86208,c_18])).

tff(c_86323,plain,
    ( r1_tarski(k1_tops_1('#skF_1','#skF_2'),k1_tops_1('#skF_1','#skF_2'))
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_86249,c_86309])).

tff(c_86335,plain,(
    r1_tarski(k1_tops_1('#skF_1','#skF_2'),k1_tops_1('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_86323])).

tff(c_86835,plain,(
    ! [A_1057,B_1058,C_1059] :
      ( r1_tarski(k1_tops_1(A_1057,B_1058),k1_tops_1(A_1057,C_1059))
      | ~ r1_tarski(B_1058,C_1059)
      | ~ m1_subset_1(C_1059,k1_zfmisc_1(u1_struct_0(A_1057)))
      | ~ m1_subset_1(B_1058,k1_zfmisc_1(u1_struct_0(A_1057)))
      | ~ l1_pre_topc(A_1057) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_89147,plain,(
    ! [A_1128,A_1129,C_1130,B_1131] :
      ( r1_tarski(A_1128,k1_tops_1(A_1129,C_1130))
      | ~ r1_tarski(A_1128,k1_tops_1(A_1129,B_1131))
      | ~ r1_tarski(B_1131,C_1130)
      | ~ m1_subset_1(C_1130,k1_zfmisc_1(u1_struct_0(A_1129)))
      | ~ m1_subset_1(B_1131,k1_zfmisc_1(u1_struct_0(A_1129)))
      | ~ l1_pre_topc(A_1129) ) ),
    inference(resolution,[status(thm)],[c_86835,c_16])).

tff(c_89166,plain,(
    ! [C_1130] :
      ( r1_tarski(k1_tops_1('#skF_1','#skF_2'),k1_tops_1('#skF_1',C_1130))
      | ~ r1_tarski('#skF_2',C_1130)
      | ~ m1_subset_1(C_1130,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_86335,c_89147])).

tff(c_89191,plain,(
    ! [C_1130] :
      ( r1_tarski(k1_tops_1('#skF_1','#skF_2'),k1_tops_1('#skF_1',C_1130))
      | ~ r1_tarski('#skF_2',C_1130)
      | ~ m1_subset_1(C_1130,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_89166])).

tff(c_86466,plain,(
    r1_tarski(k1_tops_1('#skF_1','#skF_2'),k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_86308])).

tff(c_88682,plain,(
    ! [C_1121] :
      ( r1_tarski(k1_tops_1('#skF_1','#skF_2'),k2_pre_topc('#skF_1',C_1121))
      | ~ r1_tarski(k1_tops_1('#skF_1','#skF_2'),C_1121)
      | ~ m1_subset_1(C_1121,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ m1_subset_1(k1_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_86466,c_88642])).

tff(c_88751,plain,(
    ! [C_1121] :
      ( r1_tarski(k1_tops_1('#skF_1','#skF_2'),k2_pre_topc('#skF_1',C_1121))
      | ~ r1_tarski(k1_tops_1('#skF_1','#skF_2'),C_1121)
      | ~ m1_subset_1(C_1121,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_86467,c_88682])).

tff(c_86860,plain,(
    ! [C_1059] :
      ( r1_tarski(k1_tops_1('#skF_1','#skF_2'),k1_tops_1('#skF_1',C_1059))
      | ~ r1_tarski(k1_tops_1('#skF_1','#skF_2'),C_1059)
      | ~ m1_subset_1(C_1059,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ m1_subset_1(k1_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_86249,c_86835])).

tff(c_86879,plain,(
    ! [C_1059] :
      ( r1_tarski(k1_tops_1('#skF_1','#skF_2'),k1_tops_1('#skF_1',C_1059))
      | ~ r1_tarski(k1_tops_1('#skF_1','#skF_2'),C_1059)
      | ~ m1_subset_1(C_1059,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_86467,c_86860])).

tff(c_86236,plain,(
    ! [A_1026,B_1027] :
      ( r1_tarski(k2_pre_topc(A_1026,B_1027),k2_pre_topc(A_1026,k2_pre_topc(A_1026,B_1027)))
      | ~ m1_subset_1(B_1027,k1_zfmisc_1(u1_struct_0(A_1026)))
      | ~ l1_pre_topc(A_1026) ) ),
    inference(resolution,[status(thm)],[c_86231,c_20])).

tff(c_87212,plain,
    ( r1_tarski(k2_pre_topc('#skF_1',k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2'))),k2_pre_topc('#skF_1',k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2'))))
    | ~ m1_subset_1(k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2')),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_87161,c_86236])).

tff(c_87235,plain,(
    r1_tarski(k2_pre_topc('#skF_1',k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2'))),k2_pre_topc('#skF_1',k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_87140,c_87212])).

tff(c_86547,plain,(
    ! [B_1046] :
      ( r1_tarski(k2_pre_topc('#skF_1',B_1046),k2_pre_topc('#skF_1','#skF_2'))
      | ~ r1_tarski(B_1046,k2_pre_topc('#skF_1','#skF_2'))
      | ~ m1_subset_1(k2_pre_topc('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ m1_subset_1(B_1046,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_86270,c_86529])).

tff(c_86558,plain,(
    ! [B_1046] :
      ( r1_tarski(k2_pre_topc('#skF_1',B_1046),k2_pre_topc('#skF_1','#skF_2'))
      | ~ r1_tarski(B_1046,k2_pre_topc('#skF_1','#skF_2'))
      | ~ m1_subset_1(k2_pre_topc('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ m1_subset_1(B_1046,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_86547])).

tff(c_87953,plain,(
    ! [B_1100] :
      ( r1_tarski(k2_pre_topc('#skF_1',B_1100),k2_pre_topc('#skF_1','#skF_2'))
      | ~ r1_tarski(B_1100,k2_pre_topc('#skF_1','#skF_2'))
      | ~ m1_subset_1(B_1100,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_86710,c_86558])).

tff(c_88492,plain,(
    ! [A_1117,B_1118] :
      ( r1_tarski(A_1117,k2_pre_topc('#skF_1','#skF_2'))
      | ~ r1_tarski(A_1117,k2_pre_topc('#skF_1',B_1118))
      | ~ r1_tarski(B_1118,k2_pre_topc('#skF_1','#skF_2'))
      | ~ m1_subset_1(B_1118,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(resolution,[status(thm)],[c_87953,c_16])).

tff(c_88515,plain,
    ( r1_tarski(k2_pre_topc('#skF_1',k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2'))),k2_pre_topc('#skF_1','#skF_2'))
    | ~ r1_tarski(k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2')),k2_pre_topc('#skF_1','#skF_2'))
    | ~ m1_subset_1(k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2')),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_87235,c_88492])).

tff(c_88590,plain,(
    r1_tarski(k2_pre_topc('#skF_1',k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2'))),k2_pre_topc('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_87140,c_86709,c_88515])).

tff(c_87152,plain,
    ( r1_tarski(k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2')),k2_pre_topc('#skF_1',k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2'))))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_87140,c_20])).

tff(c_87167,plain,(
    r1_tarski(k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2')),k2_pre_topc('#skF_1',k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_87152])).

tff(c_86714,plain,
    ( k1_tops_1('#skF_1',k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2'))) = k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2'))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_86710,c_12])).

tff(c_86724,plain,(
    k1_tops_1('#skF_1',k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2'))) = k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_86714])).

tff(c_89634,plain,(
    ! [A_1142,C_1143] :
      ( v4_tops_1(k1_tops_1(A_1142,C_1143),A_1142)
      | ~ r1_tarski(k1_tops_1(A_1142,C_1143),k2_pre_topc(A_1142,k1_tops_1(A_1142,k1_tops_1(A_1142,C_1143))))
      | ~ m1_subset_1(k1_tops_1(A_1142,C_1143),k1_zfmisc_1(u1_struct_0(A_1142)))
      | ~ r1_tarski(k2_pre_topc(A_1142,k1_tops_1(A_1142,C_1143)),C_1143)
      | ~ m1_subset_1(C_1143,k1_zfmisc_1(u1_struct_0(A_1142)))
      | ~ m1_subset_1(k2_pre_topc(A_1142,k1_tops_1(A_1142,C_1143)),k1_zfmisc_1(u1_struct_0(A_1142)))
      | ~ l1_pre_topc(A_1142) ) ),
    inference(resolution,[status(thm)],[c_22,c_87068])).

tff(c_89672,plain,
    ( v4_tops_1(k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2')),'#skF_1')
    | ~ r1_tarski(k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2')),k2_pre_topc('#skF_1',k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2'))))
    | ~ m1_subset_1(k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2')),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ r1_tarski(k2_pre_topc('#skF_1',k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2'))),k2_pre_topc('#skF_1','#skF_2'))
    | ~ m1_subset_1(k2_pre_topc('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_subset_1(k2_pre_topc('#skF_1',k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2'))),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_86724,c_89634])).

tff(c_89708,plain,
    ( v4_tops_1(k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2')),'#skF_1')
    | ~ m1_subset_1(k2_pre_topc('#skF_1',k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2'))),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_86710,c_88590,c_87140,c_87167,c_89672])).

tff(c_90670,plain,(
    v4_tops_1(k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2')),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_89856,c_89708])).

tff(c_87391,plain,(
    ! [A_1075,B_1076] :
      ( k1_tops_1(A_1075,k1_tops_1(A_1075,k2_pre_topc(A_1075,B_1076))) = k1_tops_1(A_1075,k2_pre_topc(A_1075,B_1076))
      | ~ m1_subset_1(B_1076,k1_zfmisc_1(u1_struct_0(A_1075)))
      | ~ l1_pre_topc(A_1075) ) ),
    inference(resolution,[status(thm)],[c_10,c_86238])).

tff(c_87393,plain,
    ( k1_tops_1('#skF_1',k1_tops_1('#skF_1',k2_pre_topc('#skF_1',k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2'))))) = k1_tops_1('#skF_1',k2_pre_topc('#skF_1',k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2'))))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_87140,c_87391])).

tff(c_87406,plain,(
    k1_tops_1('#skF_1',k1_tops_1('#skF_1',k2_pre_topc('#skF_1',k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2'))))) = k1_tops_1('#skF_1',k2_pre_topc('#skF_1',k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_87393])).

tff(c_86214,plain,(
    ! [A_1021,B_1022] :
      ( r1_tarski(k1_tops_1(A_1021,k1_tops_1(A_1021,B_1022)),k1_tops_1(A_1021,B_1022))
      | ~ m1_subset_1(B_1022,k1_zfmisc_1(u1_struct_0(A_1021)))
      | ~ l1_pre_topc(A_1021) ) ),
    inference(resolution,[status(thm)],[c_86208,c_18])).

tff(c_94201,plain,
    ( r1_tarski(k1_tops_1('#skF_1',k2_pre_topc('#skF_1',k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2')))),k1_tops_1('#skF_1',k2_pre_topc('#skF_1',k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2')))))
    | ~ m1_subset_1(k2_pre_topc('#skF_1',k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2'))),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_87406,c_86214])).

tff(c_94286,plain,(
    r1_tarski(k1_tops_1('#skF_1',k2_pre_topc('#skF_1',k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2')))),k1_tops_1('#skF_1',k2_pre_topc('#skF_1',k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2'))))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_89856,c_94201])).

tff(c_86425,plain,(
    ! [A_1043,B_1044] :
      ( r1_tarski(k1_tops_1(A_1043,k2_pre_topc(A_1043,B_1044)),B_1044)
      | ~ v4_tops_1(B_1044,A_1043)
      | ~ m1_subset_1(B_1044,k1_zfmisc_1(u1_struct_0(A_1043)))
      | ~ l1_pre_topc(A_1043) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_86442,plain,(
    ! [A_12,B_1044,A_1043] :
      ( r1_tarski(A_12,B_1044)
      | ~ r1_tarski(A_12,k1_tops_1(A_1043,k2_pre_topc(A_1043,B_1044)))
      | ~ v4_tops_1(B_1044,A_1043)
      | ~ m1_subset_1(B_1044,k1_zfmisc_1(u1_struct_0(A_1043)))
      | ~ l1_pre_topc(A_1043) ) ),
    inference(resolution,[status(thm)],[c_86425,c_16])).

tff(c_94315,plain,
    ( r1_tarski(k1_tops_1('#skF_1',k2_pre_topc('#skF_1',k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2')))),k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2')))
    | ~ v4_tops_1(k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2')),'#skF_1')
    | ~ m1_subset_1(k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2')),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_94286,c_86442])).

tff(c_94341,plain,(
    r1_tarski(k1_tops_1('#skF_1',k2_pre_topc('#skF_1',k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2')))),k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_87140,c_90670,c_94315])).

tff(c_94415,plain,(
    ! [A_1201] :
      ( r1_tarski(A_1201,k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2')))
      | ~ r1_tarski(A_1201,k1_tops_1('#skF_1',k2_pre_topc('#skF_1',k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2'))))) ) ),
    inference(resolution,[status(thm)],[c_94341,c_16])).

tff(c_94430,plain,
    ( r1_tarski(k1_tops_1('#skF_1','#skF_2'),k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2')))
    | ~ r1_tarski(k1_tops_1('#skF_1','#skF_2'),k2_pre_topc('#skF_1',k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2'))))
    | ~ m1_subset_1(k2_pre_topc('#skF_1',k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2'))),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_86879,c_94415])).

tff(c_94453,plain,
    ( r1_tarski(k1_tops_1('#skF_1','#skF_2'),k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2')))
    | ~ r1_tarski(k1_tops_1('#skF_1','#skF_2'),k2_pre_topc('#skF_1',k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_89856,c_94430])).

tff(c_96583,plain,(
    ~ r1_tarski(k1_tops_1('#skF_1','#skF_2'),k2_pre_topc('#skF_1',k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2')))) ),
    inference(splitLeft,[status(thm)],[c_94453])).

tff(c_96598,plain,
    ( ~ r1_tarski(k1_tops_1('#skF_1','#skF_2'),k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2')))
    | ~ m1_subset_1(k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2')),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_88751,c_96583])).

tff(c_96625,plain,(
    ~ r1_tarski(k1_tops_1('#skF_1','#skF_2'),k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_87140,c_96598])).

tff(c_96638,plain,
    ( ~ r1_tarski('#skF_2',k2_pre_topc('#skF_1','#skF_2'))
    | ~ m1_subset_1(k2_pre_topc('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_89191,c_96625])).

tff(c_96648,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_86710,c_86204,c_96638])).

tff(c_96650,plain,(
    r1_tarski(k1_tops_1('#skF_1','#skF_2'),k2_pre_topc('#skF_1',k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2')))) ),
    inference(splitRight,[status(thm)],[c_94453])).

tff(c_102773,plain,(
    ! [B_1303,A_1304,C_1305] :
      ( r1_tarski(B_1303,k2_pre_topc(A_1304,C_1305))
      | ~ r1_tarski(k1_tops_1(A_1304,B_1303),C_1305)
      | ~ m1_subset_1(C_1305,k1_zfmisc_1(u1_struct_0(A_1304)))
      | ~ m1_subset_1(k1_tops_1(A_1304,B_1303),k1_zfmisc_1(u1_struct_0(A_1304)))
      | ~ v4_tops_1(B_1303,A_1304)
      | ~ m1_subset_1(B_1303,k1_zfmisc_1(u1_struct_0(A_1304)))
      | ~ l1_pre_topc(A_1304) ) ),
    inference(resolution,[status(thm)],[c_4,c_88642])).

tff(c_102823,plain,
    ( r1_tarski('#skF_2',k2_pre_topc('#skF_1',k2_pre_topc('#skF_1',k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2')))))
    | ~ m1_subset_1(k2_pre_topc('#skF_1',k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2'))),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_subset_1(k1_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ v4_tops_1('#skF_2','#skF_1')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_96650,c_102773])).

tff(c_103031,plain,(
    r1_tarski('#skF_2',k2_pre_topc('#skF_1',k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_28,c_86467,c_89856,c_87161,c_102823])).

tff(c_103033,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_89855,c_103031])).

%------------------------------------------------------------------------------
