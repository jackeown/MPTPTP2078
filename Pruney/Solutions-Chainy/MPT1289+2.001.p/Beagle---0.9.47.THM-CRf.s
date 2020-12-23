%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:22:27 EST 2020

% Result     : Theorem 45.26s
% Output     : CNFRefutation 45.62s
% Verified   : 
% Statistics : Number of formulae       :  264 (8136 expanded)
%              Number of leaves         :   25 (2732 expanded)
%              Depth                    :   28
%              Number of atoms          :  676 (22136 expanded)
%              Number of equality atoms :   53 (1650 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    5 (   2 average)

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

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_119,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v4_tops_1(B,A)
             => ( v4_tops_1(k1_tops_1(A,B),A)
                & v4_tops_1(k2_pre_topc(A,B),A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t111_tops_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_pre_topc(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_pre_topc)).

tff(f_53,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => k2_pre_topc(A,k2_pre_topc(A,B)) = k2_pre_topc(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',projectivity_k2_pre_topc)).

tff(f_95,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => r1_tarski(k1_tops_1(A,B),B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_tops_1)).

tff(f_82,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k1_tops_1(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_tops_1)).

tff(f_65,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( r1_tarski(B,C)
               => r1_tarski(k2_pre_topc(A,B),k2_pre_topc(A,C)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_pre_topc)).

tff(f_76,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v4_tops_1(B,A)
          <=> ( r1_tarski(k1_tops_1(A,k2_pre_topc(A,B)),B)
              & r1_tarski(B,k2_pre_topc(A,k1_tops_1(A,B))) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_tops_1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_88,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => k1_tops_1(A,k1_tops_1(A,B)) = k1_tops_1(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',projectivity_k1_tops_1)).

tff(f_107,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( r1_tarski(B,C)
               => r1_tarski(k1_tops_1(A,B),k1_tops_1(A,C)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_tops_1)).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_40,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_38,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_14,plain,(
    ! [A_8,B_9] :
      ( m1_subset_1(k2_pre_topc(A_8,B_9),k1_zfmisc_1(u1_struct_0(A_8)))
      | ~ m1_subset_1(B_9,k1_zfmisc_1(u1_struct_0(A_8)))
      | ~ l1_pre_topc(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_225,plain,(
    ! [A_69,B_70] :
      ( k2_pre_topc(A_69,k2_pre_topc(A_69,B_70)) = k2_pre_topc(A_69,B_70)
      | ~ m1_subset_1(B_70,k1_zfmisc_1(u1_struct_0(A_69)))
      | ~ l1_pre_topc(A_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_234,plain,
    ( k2_pre_topc('#skF_1',k2_pre_topc('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_38,c_225])).

tff(c_240,plain,(
    k2_pre_topc('#skF_1',k2_pre_topc('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_234])).

tff(c_186,plain,(
    ! [A_61,B_62] :
      ( m1_subset_1(k2_pre_topc(A_61,B_62),k1_zfmisc_1(u1_struct_0(A_61)))
      | ~ m1_subset_1(B_62,k1_zfmisc_1(u1_struct_0(A_61)))
      | ~ l1_pre_topc(A_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_30,plain,(
    ! [A_26,B_28] :
      ( r1_tarski(k1_tops_1(A_26,B_28),B_28)
      | ~ m1_subset_1(B_28,k1_zfmisc_1(u1_struct_0(A_26)))
      | ~ l1_pre_topc(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_732,plain,(
    ! [A_89,B_90] :
      ( r1_tarski(k1_tops_1(A_89,k2_pre_topc(A_89,B_90)),k2_pre_topc(A_89,B_90))
      | ~ m1_subset_1(B_90,k1_zfmisc_1(u1_struct_0(A_89)))
      | ~ l1_pre_topc(A_89) ) ),
    inference(resolution,[status(thm)],[c_186,c_30])).

tff(c_759,plain,
    ( r1_tarski(k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2')),k2_pre_topc('#skF_1',k2_pre_topc('#skF_1','#skF_2')))
    | ~ m1_subset_1(k2_pre_topc('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_240,c_732])).

tff(c_775,plain,
    ( r1_tarski(k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2')),k2_pre_topc('#skF_1','#skF_2'))
    | ~ m1_subset_1(k2_pre_topc('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_240,c_759])).

tff(c_804,plain,(
    ~ m1_subset_1(k2_pre_topc('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_775])).

tff(c_807,plain,
    ( ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_14,c_804])).

tff(c_814,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_807])).

tff(c_816,plain,(
    m1_subset_1(k2_pre_topc('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_775])).

tff(c_26,plain,(
    ! [A_22,B_23] :
      ( m1_subset_1(k1_tops_1(A_22,B_23),k1_zfmisc_1(u1_struct_0(A_22)))
      | ~ m1_subset_1(B_23,k1_zfmisc_1(u1_struct_0(A_22)))
      | ~ l1_pre_topc(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_90,plain,(
    ! [A_50,B_51] :
      ( r1_tarski(k1_tops_1(A_50,B_51),B_51)
      | ~ m1_subset_1(B_51,k1_zfmisc_1(u1_struct_0(A_50)))
      | ~ l1_pre_topc(A_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_95,plain,
    ( r1_tarski(k1_tops_1('#skF_1','#skF_2'),'#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_38,c_90])).

tff(c_99,plain,(
    r1_tarski(k1_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_95])).

tff(c_18,plain,(
    ! [A_12,B_16,C_18] :
      ( r1_tarski(k2_pre_topc(A_12,B_16),k2_pre_topc(A_12,C_18))
      | ~ r1_tarski(B_16,C_18)
      | ~ m1_subset_1(C_18,k1_zfmisc_1(u1_struct_0(A_12)))
      | ~ m1_subset_1(B_16,k1_zfmisc_1(u1_struct_0(A_12)))
      | ~ l1_pre_topc(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_36,plain,(
    v4_tops_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_866,plain,(
    ! [B_94,A_95] :
      ( r1_tarski(B_94,k2_pre_topc(A_95,k1_tops_1(A_95,B_94)))
      | ~ v4_tops_1(B_94,A_95)
      | ~ m1_subset_1(B_94,k1_zfmisc_1(u1_struct_0(A_95)))
      | ~ l1_pre_topc(A_95) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_8,plain,(
    ! [A_3,C_5,B_4] :
      ( r1_tarski(A_3,C_5)
      | ~ r1_tarski(B_4,C_5)
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_888,plain,(
    ! [A_3,A_95,B_94] :
      ( r1_tarski(A_3,k2_pre_topc(A_95,k1_tops_1(A_95,B_94)))
      | ~ r1_tarski(A_3,B_94)
      | ~ v4_tops_1(B_94,A_95)
      | ~ m1_subset_1(B_94,k1_zfmisc_1(u1_struct_0(A_95)))
      | ~ l1_pre_topc(A_95) ) ),
    inference(resolution,[status(thm)],[c_866,c_8])).

tff(c_43,plain,(
    ! [A_38,B_39] :
      ( r1_tarski(A_38,B_39)
      | ~ m1_subset_1(A_38,k1_zfmisc_1(B_39)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_47,plain,(
    r1_tarski('#skF_2',u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_38,c_43])).

tff(c_65,plain,(
    ! [A_44,C_45,B_46] :
      ( r1_tarski(A_44,C_45)
      | ~ r1_tarski(B_46,C_45)
      | ~ r1_tarski(A_44,B_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_72,plain,(
    ! [A_47] :
      ( r1_tarski(A_47,u1_struct_0('#skF_1'))
      | ~ r1_tarski(A_47,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_47,c_65])).

tff(c_77,plain,(
    ! [A_3,A_47] :
      ( r1_tarski(A_3,u1_struct_0('#skF_1'))
      | ~ r1_tarski(A_3,A_47)
      | ~ r1_tarski(A_47,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_72,c_8])).

tff(c_101,plain,
    ( r1_tarski(k1_tops_1('#skF_1','#skF_2'),u1_struct_0('#skF_1'))
    | ~ r1_tarski('#skF_2','#skF_2') ),
    inference(resolution,[status(thm)],[c_99,c_77])).

tff(c_108,plain,(
    r1_tarski(k1_tops_1('#skF_1','#skF_2'),u1_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_101])).

tff(c_12,plain,(
    ! [A_6,B_7] :
      ( m1_subset_1(A_6,k1_zfmisc_1(B_7))
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_255,plain,(
    ! [A_71,A_72] :
      ( k2_pre_topc(A_71,k2_pre_topc(A_71,A_72)) = k2_pre_topc(A_71,A_72)
      | ~ l1_pre_topc(A_71)
      | ~ r1_tarski(A_72,u1_struct_0(A_71)) ) ),
    inference(resolution,[status(thm)],[c_12,c_225])).

tff(c_264,plain,
    ( k2_pre_topc('#skF_1',k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2'))) = k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2'))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_108,c_255])).

tff(c_277,plain,(
    k2_pre_topc('#skF_1',k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2'))) = k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_264])).

tff(c_192,plain,(
    ! [A_61,B_62] :
      ( r1_tarski(k1_tops_1(A_61,k2_pre_topc(A_61,B_62)),k2_pre_topc(A_61,B_62))
      | ~ m1_subset_1(B_62,k1_zfmisc_1(u1_struct_0(A_61)))
      | ~ l1_pre_topc(A_61) ) ),
    inference(resolution,[status(thm)],[c_186,c_30])).

tff(c_10,plain,(
    ! [A_6,B_7] :
      ( r1_tarski(A_6,B_7)
      | ~ m1_subset_1(A_6,k1_zfmisc_1(B_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_206,plain,(
    ! [A_64,B_65] :
      ( r1_tarski(k2_pre_topc(A_64,B_65),u1_struct_0(A_64))
      | ~ m1_subset_1(B_65,k1_zfmisc_1(u1_struct_0(A_64)))
      | ~ l1_pre_topc(A_64) ) ),
    inference(resolution,[status(thm)],[c_186,c_10])).

tff(c_1620,plain,(
    ! [A_117,A_118,B_119] :
      ( r1_tarski(A_117,u1_struct_0(A_118))
      | ~ r1_tarski(A_117,k2_pre_topc(A_118,B_119))
      | ~ m1_subset_1(B_119,k1_zfmisc_1(u1_struct_0(A_118)))
      | ~ l1_pre_topc(A_118) ) ),
    inference(resolution,[status(thm)],[c_206,c_8])).

tff(c_1666,plain,(
    ! [A_120,B_121] :
      ( r1_tarski(k1_tops_1(A_120,k2_pre_topc(A_120,B_121)),u1_struct_0(A_120))
      | ~ m1_subset_1(B_121,k1_zfmisc_1(u1_struct_0(A_120)))
      | ~ l1_pre_topc(A_120) ) ),
    inference(resolution,[status(thm)],[c_192,c_1620])).

tff(c_1683,plain,
    ( r1_tarski(k1_tops_1('#skF_1',k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2'))),u1_struct_0('#skF_1'))
    | ~ m1_subset_1(k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_277,c_1666])).

tff(c_1700,plain,
    ( r1_tarski(k1_tops_1('#skF_1',k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2'))),u1_struct_0('#skF_1'))
    | ~ m1_subset_1(k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_1683])).

tff(c_5631,plain,(
    ~ m1_subset_1(k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_1700])).

tff(c_5634,plain,
    ( ~ m1_subset_1(k1_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_14,c_5631])).

tff(c_5640,plain,(
    ~ m1_subset_1(k1_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_5634])).

tff(c_5646,plain,
    ( ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_26,c_5640])).

tff(c_5653,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_5646])).

tff(c_5655,plain,(
    m1_subset_1(k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_1700])).

tff(c_815,plain,(
    r1_tarski(k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2')),k2_pre_topc('#skF_1','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_775])).

tff(c_1298,plain,(
    ! [A_105,B_106,C_107] :
      ( r1_tarski(k2_pre_topc(A_105,B_106),k2_pre_topc(A_105,C_107))
      | ~ r1_tarski(B_106,C_107)
      | ~ m1_subset_1(C_107,k1_zfmisc_1(u1_struct_0(A_105)))
      | ~ m1_subset_1(B_106,k1_zfmisc_1(u1_struct_0(A_105)))
      | ~ l1_pre_topc(A_105) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_6014,plain,(
    ! [A_232,A_233,C_234,B_235] :
      ( r1_tarski(A_232,k2_pre_topc(A_233,C_234))
      | ~ r1_tarski(A_232,k2_pre_topc(A_233,B_235))
      | ~ r1_tarski(B_235,C_234)
      | ~ m1_subset_1(C_234,k1_zfmisc_1(u1_struct_0(A_233)))
      | ~ m1_subset_1(B_235,k1_zfmisc_1(u1_struct_0(A_233)))
      | ~ l1_pre_topc(A_233) ) ),
    inference(resolution,[status(thm)],[c_1298,c_8])).

tff(c_6044,plain,(
    ! [C_234] :
      ( r1_tarski(k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2')),k2_pre_topc('#skF_1',C_234))
      | ~ r1_tarski('#skF_2',C_234)
      | ~ m1_subset_1(C_234,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_815,c_6014])).

tff(c_6495,plain,(
    ! [C_239] :
      ( r1_tarski(k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2')),k2_pre_topc('#skF_1',C_239))
      | ~ r1_tarski('#skF_2',C_239)
      | ~ m1_subset_1(C_239,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_6044])).

tff(c_6539,plain,
    ( r1_tarski(k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2')),k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')))
    | ~ r1_tarski('#skF_2',k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')))
    | ~ m1_subset_1(k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_277,c_6495])).

tff(c_6579,plain,
    ( r1_tarski(k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2')),k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')))
    | ~ r1_tarski('#skF_2',k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5655,c_6539])).

tff(c_6584,plain,(
    ~ r1_tarski('#skF_2',k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_6579])).

tff(c_6587,plain,
    ( ~ r1_tarski('#skF_2','#skF_2')
    | ~ v4_tops_1('#skF_2','#skF_1')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_888,c_6584])).

tff(c_6594,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_36,c_6,c_6587])).

tff(c_6596,plain,(
    r1_tarski('#skF_2',k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_6579])).

tff(c_1332,plain,(
    ! [B_106] :
      ( r1_tarski(k2_pre_topc('#skF_1',B_106),k2_pre_topc('#skF_1','#skF_2'))
      | ~ r1_tarski(B_106,k2_pre_topc('#skF_1','#skF_2'))
      | ~ m1_subset_1(k2_pre_topc('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ m1_subset_1(B_106,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_240,c_1298])).

tff(c_1350,plain,(
    ! [B_106] :
      ( r1_tarski(k2_pre_topc('#skF_1',B_106),k2_pre_topc('#skF_1','#skF_2'))
      | ~ r1_tarski(B_106,k2_pre_topc('#skF_1','#skF_2'))
      | ~ m1_subset_1(B_106,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_816,c_1332])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_6636,plain,(
    ! [A_240,C_241,B_242] :
      ( k2_pre_topc(A_240,C_241) = k2_pre_topc(A_240,B_242)
      | ~ r1_tarski(k2_pre_topc(A_240,C_241),k2_pre_topc(A_240,B_242))
      | ~ r1_tarski(B_242,C_241)
      | ~ m1_subset_1(C_241,k1_zfmisc_1(u1_struct_0(A_240)))
      | ~ m1_subset_1(B_242,k1_zfmisc_1(u1_struct_0(A_240)))
      | ~ l1_pre_topc(A_240) ) ),
    inference(resolution,[status(thm)],[c_1298,c_2])).

tff(c_6661,plain,(
    ! [B_106] :
      ( k2_pre_topc('#skF_1',B_106) = k2_pre_topc('#skF_1','#skF_2')
      | ~ r1_tarski('#skF_2',B_106)
      | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1')
      | ~ r1_tarski(B_106,k2_pre_topc('#skF_1','#skF_2'))
      | ~ m1_subset_1(B_106,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(resolution,[status(thm)],[c_1350,c_6636])).

tff(c_8560,plain,(
    ! [B_270] :
      ( k2_pre_topc('#skF_1',B_270) = k2_pre_topc('#skF_1','#skF_2')
      | ~ r1_tarski('#skF_2',B_270)
      | ~ r1_tarski(B_270,k2_pre_topc('#skF_1','#skF_2'))
      | ~ m1_subset_1(B_270,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_6661])).

tff(c_8563,plain,
    ( k2_pre_topc('#skF_1',k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2'))) = k2_pre_topc('#skF_1','#skF_2')
    | ~ r1_tarski('#skF_2',k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')))
    | ~ r1_tarski(k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')),k2_pre_topc('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_5655,c_8560])).

tff(c_8587,plain,
    ( k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2')
    | ~ r1_tarski(k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')),k2_pre_topc('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6596,c_277,c_8563])).

tff(c_8605,plain,(
    ~ r1_tarski(k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')),k2_pre_topc('#skF_1','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_8587])).

tff(c_8611,plain,
    ( ~ r1_tarski(k1_tops_1('#skF_1','#skF_2'),'#skF_2')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_subset_1(k1_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_18,c_8605])).

tff(c_8615,plain,(
    ~ m1_subset_1(k1_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_99,c_8611])).

tff(c_8618,plain,
    ( ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_26,c_8615])).

tff(c_8625,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_8618])).

tff(c_8626,plain,(
    k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_8587])).

tff(c_6739,plain,(
    ! [A_243] :
      ( r1_tarski(A_243,k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')))
      | ~ r1_tarski(A_243,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_6596,c_8])).

tff(c_6848,plain,(
    ! [A_244,A_245] :
      ( r1_tarski(A_244,k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')))
      | ~ r1_tarski(A_244,A_245)
      | ~ r1_tarski(A_245,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_6739,c_8])).

tff(c_6958,plain,
    ( r1_tarski(k1_tops_1('#skF_1','#skF_2'),k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')))
    | ~ r1_tarski('#skF_2','#skF_2') ),
    inference(resolution,[status(thm)],[c_99,c_6848])).

tff(c_7039,plain,(
    r1_tarski(k1_tops_1('#skF_1','#skF_2'),k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_6958])).

tff(c_8638,plain,(
    r1_tarski(k1_tops_1('#skF_1','#skF_2'),k2_pre_topc('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8626,c_7039])).

tff(c_34,plain,
    ( ~ v4_tops_1(k2_pre_topc('#skF_1','#skF_2'),'#skF_1')
    | ~ v4_tops_1(k1_tops_1('#skF_1','#skF_2'),'#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_64,plain,(
    ~ v4_tops_1(k1_tops_1('#skF_1','#skF_2'),'#skF_1') ),
    inference(splitLeft,[status(thm)],[c_34])).

tff(c_285,plain,(
    ! [A_73,B_74] :
      ( k1_tops_1(A_73,k1_tops_1(A_73,B_74)) = k1_tops_1(A_73,B_74)
      | ~ m1_subset_1(B_74,k1_zfmisc_1(u1_struct_0(A_73)))
      | ~ l1_pre_topc(A_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_294,plain,
    ( k1_tops_1('#skF_1',k1_tops_1('#skF_1','#skF_2')) = k1_tops_1('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_38,c_285])).

tff(c_300,plain,(
    k1_tops_1('#skF_1',k1_tops_1('#skF_1','#skF_2')) = k1_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_294])).

tff(c_20,plain,(
    ! [B_21,A_19] :
      ( v4_tops_1(B_21,A_19)
      | ~ r1_tarski(B_21,k2_pre_topc(A_19,k1_tops_1(A_19,B_21)))
      | ~ r1_tarski(k1_tops_1(A_19,k2_pre_topc(A_19,B_21)),B_21)
      | ~ m1_subset_1(B_21,k1_zfmisc_1(u1_struct_0(A_19)))
      | ~ l1_pre_topc(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_8758,plain,
    ( v4_tops_1(k1_tops_1('#skF_1','#skF_2'),'#skF_1')
    | ~ r1_tarski(k1_tops_1('#skF_1','#skF_2'),k2_pre_topc('#skF_1',k1_tops_1('#skF_1',k1_tops_1('#skF_1','#skF_2'))))
    | ~ r1_tarski(k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2')),k1_tops_1('#skF_1','#skF_2'))
    | ~ m1_subset_1(k1_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_8626,c_20])).

tff(c_8852,plain,
    ( v4_tops_1(k1_tops_1('#skF_1','#skF_2'),'#skF_1')
    | ~ r1_tarski(k1_tops_1('#skF_1','#skF_2'),k2_pre_topc('#skF_1','#skF_2'))
    | ~ r1_tarski(k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2')),k1_tops_1('#skF_1','#skF_2'))
    | ~ m1_subset_1(k1_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_8626,c_300,c_8758])).

tff(c_8853,plain,
    ( ~ r1_tarski(k1_tops_1('#skF_1','#skF_2'),k2_pre_topc('#skF_1','#skF_2'))
    | ~ r1_tarski(k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2')),k1_tops_1('#skF_1','#skF_2'))
    | ~ m1_subset_1(k1_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_8852])).

tff(c_9361,plain,
    ( ~ r1_tarski(k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2')),k1_tops_1('#skF_1','#skF_2'))
    | ~ m1_subset_1(k1_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8638,c_8853])).

tff(c_9362,plain,(
    ~ m1_subset_1(k1_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_9361])).

tff(c_9365,plain,
    ( ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_26,c_9362])).

tff(c_9372,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_9365])).

tff(c_9374,plain,(
    m1_subset_1(k1_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_9361])).

tff(c_1017,plain,(
    ! [A_99,B_100,C_101] :
      ( r1_tarski(k1_tops_1(A_99,B_100),k1_tops_1(A_99,C_101))
      | ~ r1_tarski(B_100,C_101)
      | ~ m1_subset_1(C_101,k1_zfmisc_1(u1_struct_0(A_99)))
      | ~ m1_subset_1(B_100,k1_zfmisc_1(u1_struct_0(A_99)))
      | ~ l1_pre_topc(A_99) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_1062,plain,(
    ! [C_101] :
      ( r1_tarski(k1_tops_1('#skF_1','#skF_2'),k1_tops_1('#skF_1',C_101))
      | ~ r1_tarski(k1_tops_1('#skF_1','#skF_2'),C_101)
      | ~ m1_subset_1(C_101,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ m1_subset_1(k1_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_300,c_1017])).

tff(c_1089,plain,(
    ! [C_101] :
      ( r1_tarski(k1_tops_1('#skF_1','#skF_2'),k1_tops_1('#skF_1',C_101))
      | ~ r1_tarski(k1_tops_1('#skF_1','#skF_2'),C_101)
      | ~ m1_subset_1(C_101,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ m1_subset_1(k1_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_1062])).

tff(c_27179,plain,(
    ! [C_101] :
      ( r1_tarski(k1_tops_1('#skF_1','#skF_2'),k1_tops_1('#skF_1',C_101))
      | ~ r1_tarski(k1_tops_1('#skF_1','#skF_2'),C_101)
      | ~ m1_subset_1(C_101,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9374,c_1089])).

tff(c_28,plain,(
    ! [A_24,B_25] :
      ( k1_tops_1(A_24,k1_tops_1(A_24,B_25)) = k1_tops_1(A_24,B_25)
      | ~ m1_subset_1(B_25,k1_zfmisc_1(u1_struct_0(A_24)))
      | ~ l1_pre_topc(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_818,plain,
    ( k1_tops_1('#skF_1',k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2'))) = k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2'))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_816,c_28])).

tff(c_828,plain,(
    k1_tops_1('#skF_1',k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2'))) = k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_818])).

tff(c_168,plain,(
    ! [A_57,B_58] :
      ( m1_subset_1(k1_tops_1(A_57,B_58),k1_zfmisc_1(u1_struct_0(A_57)))
      | ~ m1_subset_1(B_58,k1_zfmisc_1(u1_struct_0(A_57)))
      | ~ l1_pre_topc(A_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_174,plain,(
    ! [A_57,B_58] :
      ( r1_tarski(k1_tops_1(A_57,k1_tops_1(A_57,B_58)),k1_tops_1(A_57,B_58))
      | ~ m1_subset_1(B_58,k1_zfmisc_1(u1_struct_0(A_57)))
      | ~ l1_pre_topc(A_57) ) ),
    inference(resolution,[status(thm)],[c_168,c_30])).

tff(c_614,plain,(
    ! [A_85,B_86] :
      ( r1_tarski(k1_tops_1(A_85,k2_pre_topc(A_85,B_86)),B_86)
      | ~ v4_tops_1(B_86,A_85)
      | ~ m1_subset_1(B_86,k1_zfmisc_1(u1_struct_0(A_85)))
      | ~ l1_pre_topc(A_85) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_4419,plain,(
    ! [A_191,B_192,A_193] :
      ( r1_tarski(A_191,B_192)
      | ~ r1_tarski(A_191,k1_tops_1(A_193,k2_pre_topc(A_193,B_192)))
      | ~ v4_tops_1(B_192,A_193)
      | ~ m1_subset_1(B_192,k1_zfmisc_1(u1_struct_0(A_193)))
      | ~ l1_pre_topc(A_193) ) ),
    inference(resolution,[status(thm)],[c_614,c_8])).

tff(c_28386,plain,(
    ! [A_460,B_461] :
      ( r1_tarski(k1_tops_1(A_460,k1_tops_1(A_460,k2_pre_topc(A_460,B_461))),B_461)
      | ~ v4_tops_1(B_461,A_460)
      | ~ m1_subset_1(B_461,k1_zfmisc_1(u1_struct_0(A_460)))
      | ~ m1_subset_1(k2_pre_topc(A_460,B_461),k1_zfmisc_1(u1_struct_0(A_460)))
      | ~ l1_pre_topc(A_460) ) ),
    inference(resolution,[status(thm)],[c_174,c_4419])).

tff(c_28610,plain,
    ( r1_tarski(k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2')),'#skF_2')
    | ~ v4_tops_1('#skF_2','#skF_1')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_subset_1(k2_pre_topc('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_828,c_28386])).

tff(c_28694,plain,(
    r1_tarski(k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2')),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_816,c_38,c_36,c_28610])).

tff(c_1556,plain,(
    ! [B_115,A_116] :
      ( v4_tops_1(B_115,A_116)
      | ~ r1_tarski(B_115,k2_pre_topc(A_116,k1_tops_1(A_116,B_115)))
      | ~ r1_tarski(k1_tops_1(A_116,k2_pre_topc(A_116,B_115)),B_115)
      | ~ m1_subset_1(B_115,k1_zfmisc_1(u1_struct_0(A_116)))
      | ~ l1_pre_topc(A_116) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_1591,plain,
    ( v4_tops_1(k2_pre_topc('#skF_1','#skF_2'),'#skF_1')
    | ~ r1_tarski(k2_pre_topc('#skF_1','#skF_2'),k2_pre_topc('#skF_1',k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2'))))
    | ~ r1_tarski(k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2')),k2_pre_topc('#skF_1','#skF_2'))
    | ~ m1_subset_1(k2_pre_topc('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_240,c_1556])).

tff(c_1617,plain,
    ( v4_tops_1(k2_pre_topc('#skF_1','#skF_2'),'#skF_1')
    | ~ r1_tarski(k2_pre_topc('#skF_1','#skF_2'),k2_pre_topc('#skF_1',k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_816,c_815,c_1591])).

tff(c_1705,plain,(
    ~ r1_tarski(k2_pre_topc('#skF_1','#skF_2'),k2_pre_topc('#skF_1',k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2')))) ),
    inference(splitLeft,[status(thm)],[c_1617])).

tff(c_1717,plain,
    ( ~ r1_tarski('#skF_2',k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2')))
    | ~ m1_subset_1(k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2')),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_18,c_1705])).

tff(c_1724,plain,
    ( ~ r1_tarski('#skF_2',k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2')))
    | ~ m1_subset_1(k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2')),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_1717])).

tff(c_1728,plain,(
    ~ m1_subset_1(k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2')),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_1724])).

tff(c_1731,plain,
    ( ~ m1_subset_1(k2_pre_topc('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_26,c_1728])).

tff(c_1738,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_816,c_1731])).

tff(c_1740,plain,(
    m1_subset_1(k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2')),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_1724])).

tff(c_32,plain,(
    ! [A_29,B_33,C_35] :
      ( r1_tarski(k1_tops_1(A_29,B_33),k1_tops_1(A_29,C_35))
      | ~ r1_tarski(B_33,C_35)
      | ~ m1_subset_1(C_35,k1_zfmisc_1(u1_struct_0(A_29)))
      | ~ m1_subset_1(B_33,k1_zfmisc_1(u1_struct_0(A_29)))
      | ~ l1_pre_topc(A_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_7593,plain,(
    ! [A_252,C_253,B_254] :
      ( k1_tops_1(A_252,C_253) = k1_tops_1(A_252,B_254)
      | ~ r1_tarski(k1_tops_1(A_252,C_253),k1_tops_1(A_252,B_254))
      | ~ r1_tarski(B_254,C_253)
      | ~ m1_subset_1(C_253,k1_zfmisc_1(u1_struct_0(A_252)))
      | ~ m1_subset_1(B_254,k1_zfmisc_1(u1_struct_0(A_252)))
      | ~ l1_pre_topc(A_252) ) ),
    inference(resolution,[status(thm)],[c_1017,c_2])).

tff(c_7653,plain,(
    ! [C_253] :
      ( k1_tops_1('#skF_1',k1_tops_1('#skF_1','#skF_2')) = k1_tops_1('#skF_1',C_253)
      | ~ r1_tarski(k1_tops_1('#skF_1',C_253),k1_tops_1('#skF_1','#skF_2'))
      | ~ r1_tarski(k1_tops_1('#skF_1','#skF_2'),C_253)
      | ~ m1_subset_1(C_253,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ m1_subset_1(k1_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_300,c_7593])).

tff(c_7684,plain,(
    ! [C_253] :
      ( k1_tops_1('#skF_1',C_253) = k1_tops_1('#skF_1','#skF_2')
      | ~ r1_tarski(k1_tops_1('#skF_1',C_253),k1_tops_1('#skF_1','#skF_2'))
      | ~ r1_tarski(k1_tops_1('#skF_1','#skF_2'),C_253)
      | ~ m1_subset_1(C_253,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ m1_subset_1(k1_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_300,c_7653])).

tff(c_36036,plain,(
    ! [C_529] :
      ( k1_tops_1('#skF_1',C_529) = k1_tops_1('#skF_1','#skF_2')
      | ~ r1_tarski(k1_tops_1('#skF_1',C_529),k1_tops_1('#skF_1','#skF_2'))
      | ~ r1_tarski(k1_tops_1('#skF_1','#skF_2'),C_529)
      | ~ m1_subset_1(C_529,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9374,c_7684])).

tff(c_36120,plain,(
    ! [B_33] :
      ( k1_tops_1('#skF_1',B_33) = k1_tops_1('#skF_1','#skF_2')
      | ~ r1_tarski(k1_tops_1('#skF_1','#skF_2'),B_33)
      | ~ r1_tarski(B_33,'#skF_2')
      | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ m1_subset_1(B_33,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_32,c_36036])).

tff(c_83347,plain,(
    ! [B_813] :
      ( k1_tops_1('#skF_1',B_813) = k1_tops_1('#skF_1','#skF_2')
      | ~ r1_tarski(k1_tops_1('#skF_1','#skF_2'),B_813)
      | ~ r1_tarski(B_813,'#skF_2')
      | ~ m1_subset_1(B_813,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_36120])).

tff(c_83362,plain,
    ( k1_tops_1('#skF_1',k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2'))) = k1_tops_1('#skF_1','#skF_2')
    | ~ r1_tarski(k1_tops_1('#skF_1','#skF_2'),k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2')))
    | ~ r1_tarski(k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2')),'#skF_2') ),
    inference(resolution,[status(thm)],[c_1740,c_83347])).

tff(c_83395,plain,
    ( k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2')) = k1_tops_1('#skF_1','#skF_2')
    | ~ r1_tarski(k1_tops_1('#skF_1','#skF_2'),k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28694,c_828,c_83362])).

tff(c_83410,plain,(
    ~ r1_tarski(k1_tops_1('#skF_1','#skF_2'),k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_83395])).

tff(c_83440,plain,
    ( ~ r1_tarski(k1_tops_1('#skF_1','#skF_2'),k2_pre_topc('#skF_1','#skF_2'))
    | ~ m1_subset_1(k2_pre_topc('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_27179,c_83410])).

tff(c_83477,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_816,c_8638,c_83440])).

tff(c_83478,plain,(
    k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2')) = k1_tops_1('#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_83395])).

tff(c_9373,plain,(
    ~ r1_tarski(k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2')),k1_tops_1('#skF_1','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_9361])).

tff(c_83503,plain,(
    ~ r1_tarski(k1_tops_1('#skF_1','#skF_2'),k1_tops_1('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_83478,c_9373])).

tff(c_83523,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_83503])).

tff(c_83524,plain,(
    ~ v4_tops_1(k2_pre_topc('#skF_1','#skF_2'),'#skF_1') ),
    inference(splitRight,[status(thm)],[c_34])).

tff(c_83525,plain,(
    v4_tops_1(k1_tops_1('#skF_1','#skF_2'),'#skF_1') ),
    inference(splitRight,[status(thm)],[c_34])).

tff(c_83686,plain,(
    ! [A_839,B_840] :
      ( k1_tops_1(A_839,k1_tops_1(A_839,B_840)) = k1_tops_1(A_839,B_840)
      | ~ m1_subset_1(B_840,k1_zfmisc_1(u1_struct_0(A_839)))
      | ~ l1_pre_topc(A_839) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_83695,plain,
    ( k1_tops_1('#skF_1',k1_tops_1('#skF_1','#skF_2')) = k1_tops_1('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_38,c_83686])).

tff(c_83701,plain,(
    k1_tops_1('#skF_1',k1_tops_1('#skF_1','#skF_2')) = k1_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_83695])).

tff(c_84327,plain,(
    ! [B_864,A_865] :
      ( r1_tarski(B_864,k2_pre_topc(A_865,k1_tops_1(A_865,B_864)))
      | ~ v4_tops_1(B_864,A_865)
      | ~ m1_subset_1(B_864,k1_zfmisc_1(u1_struct_0(A_865)))
      | ~ l1_pre_topc(A_865) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_84346,plain,
    ( r1_tarski(k1_tops_1('#skF_1','#skF_2'),k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')))
    | ~ v4_tops_1(k1_tops_1('#skF_1','#skF_2'),'#skF_1')
    | ~ m1_subset_1(k1_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_83701,c_84327])).

tff(c_84354,plain,
    ( r1_tarski(k1_tops_1('#skF_1','#skF_2'),k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')))
    | ~ m1_subset_1(k1_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_83525,c_84346])).

tff(c_84851,plain,(
    ~ m1_subset_1(k1_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_84354])).

tff(c_84854,plain,
    ( ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_26,c_84851])).

tff(c_84861,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_84854])).

tff(c_84863,plain,(
    m1_subset_1(k1_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_84354])).

tff(c_83551,plain,(
    ! [A_820,B_821] :
      ( r1_tarski(k1_tops_1(A_820,B_821),B_821)
      | ~ m1_subset_1(B_821,k1_zfmisc_1(u1_struct_0(A_820)))
      | ~ l1_pre_topc(A_820) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_83556,plain,
    ( r1_tarski(k1_tops_1('#skF_1','#skF_2'),'#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_38,c_83551])).

tff(c_83560,plain,(
    r1_tarski(k1_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_83556])).

tff(c_85731,plain,(
    ! [A_907,B_908] :
      ( k1_tops_1(A_907,k1_tops_1(A_907,k2_pre_topc(A_907,B_908))) = k1_tops_1(A_907,k2_pre_topc(A_907,B_908))
      | ~ m1_subset_1(B_908,k1_zfmisc_1(u1_struct_0(A_907)))
      | ~ l1_pre_topc(A_907) ) ),
    inference(resolution,[status(thm)],[c_14,c_83686])).

tff(c_85735,plain,
    ( k1_tops_1('#skF_1',k1_tops_1('#skF_1',k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')))) = k1_tops_1('#skF_1',k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_84863,c_85731])).

tff(c_85752,plain,(
    k1_tops_1('#skF_1',k1_tops_1('#skF_1',k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')))) = k1_tops_1('#skF_1',k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_85735])).

tff(c_83629,plain,(
    ! [A_827,B_828] :
      ( m1_subset_1(k1_tops_1(A_827,B_828),k1_zfmisc_1(u1_struct_0(A_827)))
      | ~ m1_subset_1(B_828,k1_zfmisc_1(u1_struct_0(A_827)))
      | ~ l1_pre_topc(A_827) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_83635,plain,(
    ! [A_827,B_828] :
      ( r1_tarski(k1_tops_1(A_827,k1_tops_1(A_827,B_828)),k1_tops_1(A_827,B_828))
      | ~ m1_subset_1(B_828,k1_zfmisc_1(u1_struct_0(A_827)))
      | ~ l1_pre_topc(A_827) ) ),
    inference(resolution,[status(thm)],[c_83629,c_30])).

tff(c_83637,plain,(
    ! [A_829,B_830] :
      ( r1_tarski(k1_tops_1(A_829,B_830),u1_struct_0(A_829))
      | ~ m1_subset_1(B_830,k1_zfmisc_1(u1_struct_0(A_829)))
      | ~ l1_pre_topc(A_829) ) ),
    inference(resolution,[status(thm)],[c_83629,c_10])).

tff(c_84239,plain,(
    ! [A_861,A_862,B_863] :
      ( r1_tarski(A_861,u1_struct_0(A_862))
      | ~ r1_tarski(A_861,k1_tops_1(A_862,B_863))
      | ~ m1_subset_1(B_863,k1_zfmisc_1(u1_struct_0(A_862)))
      | ~ l1_pre_topc(A_862) ) ),
    inference(resolution,[status(thm)],[c_83637,c_8])).

tff(c_84257,plain,(
    ! [A_827,B_828] :
      ( r1_tarski(k1_tops_1(A_827,k1_tops_1(A_827,B_828)),u1_struct_0(A_827))
      | ~ m1_subset_1(B_828,k1_zfmisc_1(u1_struct_0(A_827)))
      | ~ l1_pre_topc(A_827) ) ),
    inference(resolution,[status(thm)],[c_83635,c_84239])).

tff(c_85774,plain,
    ( r1_tarski(k1_tops_1('#skF_1',k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2'))),u1_struct_0('#skF_1'))
    | ~ m1_subset_1(k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_85752,c_84257])).

tff(c_85836,plain,
    ( r1_tarski(k1_tops_1('#skF_1',k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2'))),u1_struct_0('#skF_1'))
    | ~ m1_subset_1(k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_85774])).

tff(c_89365,plain,(
    ~ m1_subset_1(k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_85836])).

tff(c_89453,plain,
    ( ~ m1_subset_1(k1_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_14,c_89365])).

tff(c_89460,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_84863,c_89453])).

tff(c_89462,plain,(
    m1_subset_1(k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_85836])).

tff(c_84862,plain,(
    r1_tarski(k1_tops_1('#skF_1','#skF_2'),k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_84354])).

tff(c_84478,plain,(
    ! [A_869,B_870,C_871] :
      ( r1_tarski(k1_tops_1(A_869,B_870),k1_tops_1(A_869,C_871))
      | ~ r1_tarski(B_870,C_871)
      | ~ m1_subset_1(C_871,k1_zfmisc_1(u1_struct_0(A_869)))
      | ~ m1_subset_1(B_870,k1_zfmisc_1(u1_struct_0(A_869)))
      | ~ l1_pre_topc(A_869) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_89770,plain,(
    ! [A_1001,A_1002,C_1003,B_1004] :
      ( r1_tarski(A_1001,k1_tops_1(A_1002,C_1003))
      | ~ r1_tarski(A_1001,k1_tops_1(A_1002,B_1004))
      | ~ r1_tarski(B_1004,C_1003)
      | ~ m1_subset_1(C_1003,k1_zfmisc_1(u1_struct_0(A_1002)))
      | ~ m1_subset_1(B_1004,k1_zfmisc_1(u1_struct_0(A_1002)))
      | ~ l1_pre_topc(A_1002) ) ),
    inference(resolution,[status(thm)],[c_84478,c_8])).

tff(c_89797,plain,(
    ! [A_1001,C_1003] :
      ( r1_tarski(A_1001,k1_tops_1('#skF_1',C_1003))
      | ~ r1_tarski(A_1001,k1_tops_1('#skF_1','#skF_2'))
      | ~ r1_tarski(k1_tops_1('#skF_1','#skF_2'),C_1003)
      | ~ m1_subset_1(C_1003,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ m1_subset_1(k1_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_83701,c_89770])).

tff(c_89830,plain,(
    ! [A_1005,C_1006] :
      ( r1_tarski(A_1005,k1_tops_1('#skF_1',C_1006))
      | ~ r1_tarski(A_1005,k1_tops_1('#skF_1','#skF_2'))
      | ~ r1_tarski(k1_tops_1('#skF_1','#skF_2'),C_1006)
      | ~ m1_subset_1(C_1006,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_84863,c_89797])).

tff(c_89842,plain,(
    ! [C_1006] :
      ( r1_tarski(k1_tops_1('#skF_1',k1_tops_1('#skF_1','#skF_2')),k1_tops_1('#skF_1',C_1006))
      | ~ r1_tarski(k1_tops_1('#skF_1','#skF_2'),C_1006)
      | ~ m1_subset_1(C_1006,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_83635,c_89830])).

tff(c_89979,plain,(
    ! [C_1009] :
      ( r1_tarski(k1_tops_1('#skF_1','#skF_2'),k1_tops_1('#skF_1',C_1009))
      | ~ r1_tarski(k1_tops_1('#skF_1','#skF_2'),C_1009)
      | ~ m1_subset_1(C_1009,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_83701,c_89842])).

tff(c_84075,plain,(
    ! [A_855,B_856] :
      ( r1_tarski(k1_tops_1(A_855,k2_pre_topc(A_855,B_856)),B_856)
      | ~ v4_tops_1(B_856,A_855)
      | ~ m1_subset_1(B_856,k1_zfmisc_1(u1_struct_0(A_855)))
      | ~ l1_pre_topc(A_855) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_84118,plain,(
    ! [A_855,B_856] :
      ( k1_tops_1(A_855,k2_pre_topc(A_855,B_856)) = B_856
      | ~ r1_tarski(B_856,k1_tops_1(A_855,k2_pre_topc(A_855,B_856)))
      | ~ v4_tops_1(B_856,A_855)
      | ~ m1_subset_1(B_856,k1_zfmisc_1(u1_struct_0(A_855)))
      | ~ l1_pre_topc(A_855) ) ),
    inference(resolution,[status(thm)],[c_84075,c_2])).

tff(c_90006,plain,
    ( k1_tops_1('#skF_1',k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2'))) = k1_tops_1('#skF_1','#skF_2')
    | ~ v4_tops_1(k1_tops_1('#skF_1','#skF_2'),'#skF_1')
    | ~ m1_subset_1(k1_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1')
    | ~ r1_tarski(k1_tops_1('#skF_1','#skF_2'),k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')))
    | ~ m1_subset_1(k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_89979,c_84118])).

tff(c_90114,plain,(
    k1_tops_1('#skF_1',k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2'))) = k1_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_89462,c_84862,c_40,c_84863,c_83525,c_90006])).

tff(c_83760,plain,(
    ! [A_843,B_844] :
      ( k2_pre_topc(A_843,k2_pre_topc(A_843,B_844)) = k2_pre_topc(A_843,B_844)
      | ~ m1_subset_1(B_844,k1_zfmisc_1(u1_struct_0(A_843)))
      | ~ l1_pre_topc(A_843) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_83769,plain,
    ( k2_pre_topc('#skF_1',k2_pre_topc('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_38,c_83760])).

tff(c_83775,plain,(
    k2_pre_topc('#skF_1',k2_pre_topc('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_83769])).

tff(c_83647,plain,(
    ! [A_831,B_832] :
      ( m1_subset_1(k2_pre_topc(A_831,B_832),k1_zfmisc_1(u1_struct_0(A_831)))
      | ~ m1_subset_1(B_832,k1_zfmisc_1(u1_struct_0(A_831)))
      | ~ l1_pre_topc(A_831) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_84193,plain,(
    ! [A_859,B_860] :
      ( r1_tarski(k1_tops_1(A_859,k2_pre_topc(A_859,B_860)),k2_pre_topc(A_859,B_860))
      | ~ m1_subset_1(B_860,k1_zfmisc_1(u1_struct_0(A_859)))
      | ~ l1_pre_topc(A_859) ) ),
    inference(resolution,[status(thm)],[c_83647,c_30])).

tff(c_84220,plain,
    ( r1_tarski(k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2')),k2_pre_topc('#skF_1',k2_pre_topc('#skF_1','#skF_2')))
    | ~ m1_subset_1(k2_pre_topc('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_83775,c_84193])).

tff(c_84236,plain,
    ( r1_tarski(k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2')),k2_pre_topc('#skF_1','#skF_2'))
    | ~ m1_subset_1(k2_pre_topc('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_83775,c_84220])).

tff(c_84265,plain,(
    ~ m1_subset_1(k2_pre_topc('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_84236])).

tff(c_84268,plain,
    ( ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_14,c_84265])).

tff(c_84275,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_84268])).

tff(c_84277,plain,(
    m1_subset_1(k2_pre_topc('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_84236])).

tff(c_84276,plain,(
    r1_tarski(k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2')),k2_pre_topc('#skF_1','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_84236])).

tff(c_84324,plain,(
    ! [A_3] :
      ( r1_tarski(A_3,k2_pre_topc('#skF_1','#skF_2'))
      | ~ r1_tarski(A_3,k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2'))) ) ),
    inference(resolution,[status(thm)],[c_84276,c_8])).

tff(c_84482,plain,(
    ! [B_870] :
      ( r1_tarski(k1_tops_1('#skF_1',B_870),k2_pre_topc('#skF_1','#skF_2'))
      | ~ r1_tarski(B_870,k2_pre_topc('#skF_1','#skF_2'))
      | ~ m1_subset_1(k2_pre_topc('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ m1_subset_1(B_870,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_84478,c_84324])).

tff(c_84529,plain,(
    ! [B_870] :
      ( r1_tarski(k1_tops_1('#skF_1',B_870),k2_pre_topc('#skF_1','#skF_2'))
      | ~ r1_tarski(B_870,k2_pre_topc('#skF_1','#skF_2'))
      | ~ m1_subset_1(B_870,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_84277,c_84482])).

tff(c_90291,plain,
    ( r1_tarski(k1_tops_1('#skF_1','#skF_2'),k2_pre_topc('#skF_1','#skF_2'))
    | ~ r1_tarski(k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')),k2_pre_topc('#skF_1','#skF_2'))
    | ~ m1_subset_1(k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_90114,c_84529])).

tff(c_90440,plain,
    ( r1_tarski(k1_tops_1('#skF_1','#skF_2'),k2_pre_topc('#skF_1','#skF_2'))
    | ~ r1_tarski(k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')),k2_pre_topc('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_89462,c_90291])).

tff(c_90493,plain,(
    ~ r1_tarski(k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')),k2_pre_topc('#skF_1','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_90440])).

tff(c_90584,plain,
    ( ~ r1_tarski(k1_tops_1('#skF_1','#skF_2'),'#skF_2')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_subset_1(k1_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_18,c_90493])).

tff(c_90591,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_84863,c_38,c_83560,c_90584])).

tff(c_90593,plain,(
    r1_tarski(k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')),k2_pre_topc('#skF_1','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_90440])).

tff(c_84349,plain,(
    ! [A_3,A_865,B_864] :
      ( r1_tarski(A_3,k2_pre_topc(A_865,k1_tops_1(A_865,B_864)))
      | ~ r1_tarski(A_3,B_864)
      | ~ v4_tops_1(B_864,A_865)
      | ~ m1_subset_1(B_864,k1_zfmisc_1(u1_struct_0(A_865)))
      | ~ l1_pre_topc(A_865) ) ),
    inference(resolution,[status(thm)],[c_84327,c_8])).

tff(c_83526,plain,(
    ! [A_814,C_815,B_816] :
      ( r1_tarski(A_814,C_815)
      | ~ r1_tarski(B_816,C_815)
      | ~ r1_tarski(A_814,B_816) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_83533,plain,(
    ! [A_817] :
      ( r1_tarski(A_817,u1_struct_0('#skF_1'))
      | ~ r1_tarski(A_817,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_47,c_83526])).

tff(c_83538,plain,(
    ! [A_3,A_817] :
      ( r1_tarski(A_3,u1_struct_0('#skF_1'))
      | ~ r1_tarski(A_3,A_817)
      | ~ r1_tarski(A_817,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_83533,c_8])).

tff(c_83562,plain,
    ( r1_tarski(k1_tops_1('#skF_1','#skF_2'),u1_struct_0('#skF_1'))
    | ~ r1_tarski('#skF_2','#skF_2') ),
    inference(resolution,[status(thm)],[c_83560,c_83538])).

tff(c_83569,plain,(
    r1_tarski(k1_tops_1('#skF_1','#skF_2'),u1_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_83562])).

tff(c_83917,plain,(
    ! [A_849,A_850] :
      ( k2_pre_topc(A_849,k2_pre_topc(A_849,A_850)) = k2_pre_topc(A_849,A_850)
      | ~ l1_pre_topc(A_849)
      | ~ r1_tarski(A_850,u1_struct_0(A_849)) ) ),
    inference(resolution,[status(thm)],[c_12,c_83760])).

tff(c_83928,plain,
    ( k2_pre_topc('#skF_1',k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2'))) = k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2'))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_83569,c_83917])).

tff(c_83944,plain,(
    k2_pre_topc('#skF_1',k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2'))) = k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_83928])).

tff(c_84759,plain,(
    ! [A_875,B_876,C_877] :
      ( r1_tarski(k2_pre_topc(A_875,B_876),k2_pre_topc(A_875,C_877))
      | ~ r1_tarski(B_876,C_877)
      | ~ m1_subset_1(C_877,k1_zfmisc_1(u1_struct_0(A_875)))
      | ~ m1_subset_1(B_876,k1_zfmisc_1(u1_struct_0(A_875)))
      | ~ l1_pre_topc(A_875) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_90953,plain,(
    ! [A_1019,A_1020,C_1021,B_1022] :
      ( r1_tarski(A_1019,k2_pre_topc(A_1020,C_1021))
      | ~ r1_tarski(A_1019,k2_pre_topc(A_1020,B_1022))
      | ~ r1_tarski(B_1022,C_1021)
      | ~ m1_subset_1(C_1021,k1_zfmisc_1(u1_struct_0(A_1020)))
      | ~ m1_subset_1(B_1022,k1_zfmisc_1(u1_struct_0(A_1020)))
      | ~ l1_pre_topc(A_1020) ) ),
    inference(resolution,[status(thm)],[c_84759,c_8])).

tff(c_90993,plain,(
    ! [C_1021] :
      ( r1_tarski(k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2')),k2_pre_topc('#skF_1',C_1021))
      | ~ r1_tarski('#skF_2',C_1021)
      | ~ m1_subset_1(C_1021,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_84276,c_90953])).

tff(c_94475,plain,(
    ! [C_1069] :
      ( r1_tarski(k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2')),k2_pre_topc('#skF_1',C_1069))
      | ~ r1_tarski('#skF_2',C_1069)
      | ~ m1_subset_1(C_1069,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_90993])).

tff(c_94534,plain,
    ( r1_tarski(k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2')),k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')))
    | ~ r1_tarski('#skF_2',k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')))
    | ~ m1_subset_1(k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_83944,c_94475])).

tff(c_94588,plain,
    ( r1_tarski(k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2')),k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')))
    | ~ r1_tarski('#skF_2',k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_89462,c_94534])).

tff(c_96932,plain,(
    ~ r1_tarski('#skF_2',k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_94588])).

tff(c_97240,plain,
    ( ~ r1_tarski('#skF_2','#skF_2')
    | ~ v4_tops_1('#skF_2','#skF_1')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_84349,c_96932])).

tff(c_97265,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_36,c_6,c_97240])).

tff(c_97267,plain,(
    r1_tarski('#skF_2',k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_94588])).

tff(c_84793,plain,(
    ! [B_876] :
      ( r1_tarski(k2_pre_topc('#skF_1',B_876),k2_pre_topc('#skF_1','#skF_2'))
      | ~ r1_tarski(B_876,k2_pre_topc('#skF_1','#skF_2'))
      | ~ m1_subset_1(k2_pre_topc('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ m1_subset_1(B_876,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_83775,c_84759])).

tff(c_84811,plain,(
    ! [B_876] :
      ( r1_tarski(k2_pre_topc('#skF_1',B_876),k2_pre_topc('#skF_1','#skF_2'))
      | ~ r1_tarski(B_876,k2_pre_topc('#skF_1','#skF_2'))
      | ~ m1_subset_1(B_876,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_84277,c_84793])).

tff(c_92800,plain,(
    ! [A_1044,C_1045,B_1046] :
      ( k2_pre_topc(A_1044,C_1045) = k2_pre_topc(A_1044,B_1046)
      | ~ r1_tarski(k2_pre_topc(A_1044,C_1045),k2_pre_topc(A_1044,B_1046))
      | ~ r1_tarski(B_1046,C_1045)
      | ~ m1_subset_1(C_1045,k1_zfmisc_1(u1_struct_0(A_1044)))
      | ~ m1_subset_1(B_1046,k1_zfmisc_1(u1_struct_0(A_1044)))
      | ~ l1_pre_topc(A_1044) ) ),
    inference(resolution,[status(thm)],[c_84759,c_2])).

tff(c_92851,plain,(
    ! [B_876] :
      ( k2_pre_topc('#skF_1',B_876) = k2_pre_topc('#skF_1','#skF_2')
      | ~ r1_tarski('#skF_2',B_876)
      | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1')
      | ~ r1_tarski(B_876,k2_pre_topc('#skF_1','#skF_2'))
      | ~ m1_subset_1(B_876,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(resolution,[status(thm)],[c_84811,c_92800])).

tff(c_154960,plain,(
    ! [B_1487] :
      ( k2_pre_topc('#skF_1',B_1487) = k2_pre_topc('#skF_1','#skF_2')
      | ~ r1_tarski('#skF_2',B_1487)
      | ~ r1_tarski(B_1487,k2_pre_topc('#skF_1','#skF_2'))
      | ~ m1_subset_1(B_1487,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_92851])).

tff(c_154972,plain,
    ( k2_pre_topc('#skF_1',k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2'))) = k2_pre_topc('#skF_1','#skF_2')
    | ~ r1_tarski('#skF_2',k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')))
    | ~ r1_tarski(k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')),k2_pre_topc('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_89462,c_154960])).

tff(c_155008,plain,(
    k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_90593,c_97267,c_83944,c_154972])).

tff(c_89505,plain,(
    r1_tarski(k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')),u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_89462,c_10])).

tff(c_84281,plain,
    ( k1_tops_1('#skF_1',k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2'))) = k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2'))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_84277,c_28])).

tff(c_84292,plain,(
    k1_tops_1('#skF_1',k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2'))) = k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_84281])).

tff(c_87854,plain,(
    ! [A_950,B_951,A_952] :
      ( r1_tarski(A_950,B_951)
      | ~ r1_tarski(A_950,k1_tops_1(A_952,k2_pre_topc(A_952,B_951)))
      | ~ v4_tops_1(B_951,A_952)
      | ~ m1_subset_1(B_951,k1_zfmisc_1(u1_struct_0(A_952)))
      | ~ l1_pre_topc(A_952) ) ),
    inference(resolution,[status(thm)],[c_84075,c_8])).

tff(c_118330,plain,(
    ! [A_1258,B_1259] :
      ( r1_tarski(k1_tops_1(A_1258,k1_tops_1(A_1258,k2_pre_topc(A_1258,B_1259))),B_1259)
      | ~ v4_tops_1(B_1259,A_1258)
      | ~ m1_subset_1(B_1259,k1_zfmisc_1(u1_struct_0(A_1258)))
      | ~ m1_subset_1(k2_pre_topc(A_1258,B_1259),k1_zfmisc_1(u1_struct_0(A_1258)))
      | ~ l1_pre_topc(A_1258) ) ),
    inference(resolution,[status(thm)],[c_83635,c_87854])).

tff(c_118570,plain,
    ( r1_tarski(k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2')),'#skF_2')
    | ~ v4_tops_1('#skF_2','#skF_1')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_subset_1(k2_pre_topc('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_84292,c_118330])).

tff(c_118664,plain,(
    r1_tarski(k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2')),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_84277,c_38,c_36,c_118570])).

tff(c_118766,plain,(
    ! [A_1260] :
      ( r1_tarski(A_1260,'#skF_2')
      | ~ r1_tarski(A_1260,k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2'))) ) ),
    inference(resolution,[status(thm)],[c_118664,c_8])).

tff(c_118804,plain,(
    ! [B_33] :
      ( r1_tarski(k1_tops_1('#skF_1',B_33),'#skF_2')
      | ~ r1_tarski(B_33,k2_pre_topc('#skF_1','#skF_2'))
      | ~ m1_subset_1(k2_pre_topc('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ m1_subset_1(B_33,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_32,c_118766])).

tff(c_119444,plain,(
    ! [B_1266] :
      ( r1_tarski(k1_tops_1('#skF_1',B_1266),'#skF_2')
      | ~ r1_tarski(B_1266,k2_pre_topc('#skF_1','#skF_2'))
      | ~ m1_subset_1(B_1266,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_84277,c_118804])).

tff(c_119502,plain,(
    ! [A_1267] :
      ( r1_tarski(k1_tops_1('#skF_1',A_1267),'#skF_2')
      | ~ r1_tarski(A_1267,k2_pre_topc('#skF_1','#skF_2'))
      | ~ r1_tarski(A_1267,u1_struct_0('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_12,c_119444])).

tff(c_97339,plain,(
    ! [A_1098] :
      ( r1_tarski(A_1098,k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')))
      | ~ r1_tarski(A_1098,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_97267,c_8])).

tff(c_97468,plain,(
    ! [A_3,A_1098] :
      ( r1_tarski(A_3,k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')))
      | ~ r1_tarski(A_3,A_1098)
      | ~ r1_tarski(A_1098,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_97339,c_8])).

tff(c_119534,plain,(
    ! [A_1267] :
      ( r1_tarski(k1_tops_1('#skF_1',A_1267),k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')))
      | ~ r1_tarski('#skF_2','#skF_2')
      | ~ r1_tarski(A_1267,k2_pre_topc('#skF_1','#skF_2'))
      | ~ r1_tarski(A_1267,u1_struct_0('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_119502,c_97468])).

tff(c_126183,plain,(
    ! [A_1322] :
      ( r1_tarski(k1_tops_1('#skF_1',A_1322),k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')))
      | ~ r1_tarski(A_1322,k2_pre_topc('#skF_1','#skF_2'))
      | ~ r1_tarski(A_1322,u1_struct_0('#skF_1')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_119534])).

tff(c_126254,plain,
    ( v4_tops_1(k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')),'#skF_1')
    | ~ r1_tarski(k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')),k2_pre_topc('#skF_1',k1_tops_1('#skF_1',k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')))))
    | ~ m1_subset_1(k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1')
    | ~ r1_tarski(k2_pre_topc('#skF_1',k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2'))),k2_pre_topc('#skF_1','#skF_2'))
    | ~ r1_tarski(k2_pre_topc('#skF_1',k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2'))),u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_126183,c_20])).

tff(c_126362,plain,(
    v4_tops_1(k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_89505,c_83944,c_90593,c_83944,c_40,c_89462,c_6,c_90114,c_126254])).

tff(c_155284,plain,(
    v4_tops_1(k2_pre_topc('#skF_1','#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_155008,c_126362])).

tff(c_155316,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_83524,c_155284])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:49:23 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 45.26/34.02  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 45.26/34.05  
% 45.26/34.05  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 45.26/34.05  %$ v4_tops_1 > r1_tarski > m1_subset_1 > l1_pre_topc > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_1
% 45.26/34.05  
% 45.26/34.05  %Foreground sorts:
% 45.26/34.05  
% 45.26/34.05  
% 45.26/34.05  %Background operators:
% 45.26/34.05  
% 45.26/34.05  
% 45.26/34.05  %Foreground operators:
% 45.26/34.05  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 45.26/34.05  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 45.26/34.05  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 45.26/34.05  tff(v4_tops_1, type, v4_tops_1: ($i * $i) > $o).
% 45.26/34.05  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 45.26/34.05  tff('#skF_2', type, '#skF_2': $i).
% 45.26/34.05  tff('#skF_1', type, '#skF_1': $i).
% 45.26/34.05  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 45.26/34.05  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 45.26/34.05  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 45.26/34.05  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 45.26/34.05  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 45.26/34.05  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 45.26/34.05  
% 45.55/34.09  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 45.55/34.09  tff(f_119, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_tops_1(B, A) => (v4_tops_1(k1_tops_1(A, B), A) & v4_tops_1(k2_pre_topc(A, B), A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t111_tops_1)).
% 45.55/34.09  tff(f_47, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_pre_topc(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_pre_topc)).
% 45.55/34.09  tff(f_53, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => (k2_pre_topc(A, k2_pre_topc(A, B)) = k2_pre_topc(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', projectivity_k2_pre_topc)).
% 45.55/34.09  tff(f_95, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => r1_tarski(k1_tops_1(A, B), B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_tops_1)).
% 45.55/34.09  tff(f_82, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k1_tops_1(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_tops_1)).
% 45.55/34.09  tff(f_65, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (r1_tarski(B, C) => r1_tarski(k2_pre_topc(A, B), k2_pre_topc(A, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_pre_topc)).
% 45.55/34.09  tff(f_76, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_tops_1(B, A) <=> (r1_tarski(k1_tops_1(A, k2_pre_topc(A, B)), B) & r1_tarski(B, k2_pre_topc(A, k1_tops_1(A, B))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d6_tops_1)).
% 45.55/34.09  tff(f_37, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 45.55/34.09  tff(f_41, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 45.55/34.09  tff(f_88, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => (k1_tops_1(A, k1_tops_1(A, B)) = k1_tops_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', projectivity_k1_tops_1)).
% 45.55/34.09  tff(f_107, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (r1_tarski(B, C) => r1_tarski(k1_tops_1(A, B), k1_tops_1(A, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_tops_1)).
% 45.55/34.09  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 45.55/34.09  tff(c_40, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_119])).
% 45.55/34.09  tff(c_38, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_119])).
% 45.55/34.09  tff(c_14, plain, (![A_8, B_9]: (m1_subset_1(k2_pre_topc(A_8, B_9), k1_zfmisc_1(u1_struct_0(A_8))) | ~m1_subset_1(B_9, k1_zfmisc_1(u1_struct_0(A_8))) | ~l1_pre_topc(A_8))), inference(cnfTransformation, [status(thm)], [f_47])).
% 45.55/34.09  tff(c_225, plain, (![A_69, B_70]: (k2_pre_topc(A_69, k2_pre_topc(A_69, B_70))=k2_pre_topc(A_69, B_70) | ~m1_subset_1(B_70, k1_zfmisc_1(u1_struct_0(A_69))) | ~l1_pre_topc(A_69))), inference(cnfTransformation, [status(thm)], [f_53])).
% 45.55/34.09  tff(c_234, plain, (k2_pre_topc('#skF_1', k2_pre_topc('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_38, c_225])).
% 45.55/34.09  tff(c_240, plain, (k2_pre_topc('#skF_1', k2_pre_topc('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_234])).
% 45.55/34.09  tff(c_186, plain, (![A_61, B_62]: (m1_subset_1(k2_pre_topc(A_61, B_62), k1_zfmisc_1(u1_struct_0(A_61))) | ~m1_subset_1(B_62, k1_zfmisc_1(u1_struct_0(A_61))) | ~l1_pre_topc(A_61))), inference(cnfTransformation, [status(thm)], [f_47])).
% 45.55/34.09  tff(c_30, plain, (![A_26, B_28]: (r1_tarski(k1_tops_1(A_26, B_28), B_28) | ~m1_subset_1(B_28, k1_zfmisc_1(u1_struct_0(A_26))) | ~l1_pre_topc(A_26))), inference(cnfTransformation, [status(thm)], [f_95])).
% 45.55/34.09  tff(c_732, plain, (![A_89, B_90]: (r1_tarski(k1_tops_1(A_89, k2_pre_topc(A_89, B_90)), k2_pre_topc(A_89, B_90)) | ~m1_subset_1(B_90, k1_zfmisc_1(u1_struct_0(A_89))) | ~l1_pre_topc(A_89))), inference(resolution, [status(thm)], [c_186, c_30])).
% 45.55/34.09  tff(c_759, plain, (r1_tarski(k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_2')), k2_pre_topc('#skF_1', k2_pre_topc('#skF_1', '#skF_2'))) | ~m1_subset_1(k2_pre_topc('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_240, c_732])).
% 45.55/34.09  tff(c_775, plain, (r1_tarski(k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_2')), k2_pre_topc('#skF_1', '#skF_2')) | ~m1_subset_1(k2_pre_topc('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_240, c_759])).
% 45.55/34.09  tff(c_804, plain, (~m1_subset_1(k2_pre_topc('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitLeft, [status(thm)], [c_775])).
% 45.55/34.09  tff(c_807, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_14, c_804])).
% 45.55/34.09  tff(c_814, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_807])).
% 45.55/34.09  tff(c_816, plain, (m1_subset_1(k2_pre_topc('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitRight, [status(thm)], [c_775])).
% 45.55/34.09  tff(c_26, plain, (![A_22, B_23]: (m1_subset_1(k1_tops_1(A_22, B_23), k1_zfmisc_1(u1_struct_0(A_22))) | ~m1_subset_1(B_23, k1_zfmisc_1(u1_struct_0(A_22))) | ~l1_pre_topc(A_22))), inference(cnfTransformation, [status(thm)], [f_82])).
% 45.55/34.09  tff(c_90, plain, (![A_50, B_51]: (r1_tarski(k1_tops_1(A_50, B_51), B_51) | ~m1_subset_1(B_51, k1_zfmisc_1(u1_struct_0(A_50))) | ~l1_pre_topc(A_50))), inference(cnfTransformation, [status(thm)], [f_95])).
% 45.55/34.09  tff(c_95, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_2'), '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_38, c_90])).
% 45.55/34.09  tff(c_99, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_95])).
% 45.55/34.09  tff(c_18, plain, (![A_12, B_16, C_18]: (r1_tarski(k2_pre_topc(A_12, B_16), k2_pre_topc(A_12, C_18)) | ~r1_tarski(B_16, C_18) | ~m1_subset_1(C_18, k1_zfmisc_1(u1_struct_0(A_12))) | ~m1_subset_1(B_16, k1_zfmisc_1(u1_struct_0(A_12))) | ~l1_pre_topc(A_12))), inference(cnfTransformation, [status(thm)], [f_65])).
% 45.55/34.09  tff(c_36, plain, (v4_tops_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_119])).
% 45.55/34.09  tff(c_866, plain, (![B_94, A_95]: (r1_tarski(B_94, k2_pre_topc(A_95, k1_tops_1(A_95, B_94))) | ~v4_tops_1(B_94, A_95) | ~m1_subset_1(B_94, k1_zfmisc_1(u1_struct_0(A_95))) | ~l1_pre_topc(A_95))), inference(cnfTransformation, [status(thm)], [f_76])).
% 45.55/34.09  tff(c_8, plain, (![A_3, C_5, B_4]: (r1_tarski(A_3, C_5) | ~r1_tarski(B_4, C_5) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_37])).
% 45.55/34.09  tff(c_888, plain, (![A_3, A_95, B_94]: (r1_tarski(A_3, k2_pre_topc(A_95, k1_tops_1(A_95, B_94))) | ~r1_tarski(A_3, B_94) | ~v4_tops_1(B_94, A_95) | ~m1_subset_1(B_94, k1_zfmisc_1(u1_struct_0(A_95))) | ~l1_pre_topc(A_95))), inference(resolution, [status(thm)], [c_866, c_8])).
% 45.55/34.09  tff(c_43, plain, (![A_38, B_39]: (r1_tarski(A_38, B_39) | ~m1_subset_1(A_38, k1_zfmisc_1(B_39)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 45.55/34.09  tff(c_47, plain, (r1_tarski('#skF_2', u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_38, c_43])).
% 45.55/34.09  tff(c_65, plain, (![A_44, C_45, B_46]: (r1_tarski(A_44, C_45) | ~r1_tarski(B_46, C_45) | ~r1_tarski(A_44, B_46))), inference(cnfTransformation, [status(thm)], [f_37])).
% 45.55/34.09  tff(c_72, plain, (![A_47]: (r1_tarski(A_47, u1_struct_0('#skF_1')) | ~r1_tarski(A_47, '#skF_2'))), inference(resolution, [status(thm)], [c_47, c_65])).
% 45.55/34.09  tff(c_77, plain, (![A_3, A_47]: (r1_tarski(A_3, u1_struct_0('#skF_1')) | ~r1_tarski(A_3, A_47) | ~r1_tarski(A_47, '#skF_2'))), inference(resolution, [status(thm)], [c_72, c_8])).
% 45.55/34.09  tff(c_101, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_2'), u1_struct_0('#skF_1')) | ~r1_tarski('#skF_2', '#skF_2')), inference(resolution, [status(thm)], [c_99, c_77])).
% 45.55/34.09  tff(c_108, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_2'), u1_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_101])).
% 45.55/34.09  tff(c_12, plain, (![A_6, B_7]: (m1_subset_1(A_6, k1_zfmisc_1(B_7)) | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_41])).
% 45.55/34.09  tff(c_255, plain, (![A_71, A_72]: (k2_pre_topc(A_71, k2_pre_topc(A_71, A_72))=k2_pre_topc(A_71, A_72) | ~l1_pre_topc(A_71) | ~r1_tarski(A_72, u1_struct_0(A_71)))), inference(resolution, [status(thm)], [c_12, c_225])).
% 45.55/34.09  tff(c_264, plain, (k2_pre_topc('#skF_1', k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2')))=k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2')) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_108, c_255])).
% 45.55/34.09  tff(c_277, plain, (k2_pre_topc('#skF_1', k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2')))=k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_264])).
% 45.55/34.09  tff(c_192, plain, (![A_61, B_62]: (r1_tarski(k1_tops_1(A_61, k2_pre_topc(A_61, B_62)), k2_pre_topc(A_61, B_62)) | ~m1_subset_1(B_62, k1_zfmisc_1(u1_struct_0(A_61))) | ~l1_pre_topc(A_61))), inference(resolution, [status(thm)], [c_186, c_30])).
% 45.55/34.09  tff(c_10, plain, (![A_6, B_7]: (r1_tarski(A_6, B_7) | ~m1_subset_1(A_6, k1_zfmisc_1(B_7)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 45.55/34.09  tff(c_206, plain, (![A_64, B_65]: (r1_tarski(k2_pre_topc(A_64, B_65), u1_struct_0(A_64)) | ~m1_subset_1(B_65, k1_zfmisc_1(u1_struct_0(A_64))) | ~l1_pre_topc(A_64))), inference(resolution, [status(thm)], [c_186, c_10])).
% 45.55/34.09  tff(c_1620, plain, (![A_117, A_118, B_119]: (r1_tarski(A_117, u1_struct_0(A_118)) | ~r1_tarski(A_117, k2_pre_topc(A_118, B_119)) | ~m1_subset_1(B_119, k1_zfmisc_1(u1_struct_0(A_118))) | ~l1_pre_topc(A_118))), inference(resolution, [status(thm)], [c_206, c_8])).
% 45.55/34.09  tff(c_1666, plain, (![A_120, B_121]: (r1_tarski(k1_tops_1(A_120, k2_pre_topc(A_120, B_121)), u1_struct_0(A_120)) | ~m1_subset_1(B_121, k1_zfmisc_1(u1_struct_0(A_120))) | ~l1_pre_topc(A_120))), inference(resolution, [status(thm)], [c_192, c_1620])).
% 45.55/34.09  tff(c_1683, plain, (r1_tarski(k1_tops_1('#skF_1', k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2'))), u1_struct_0('#skF_1')) | ~m1_subset_1(k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2')), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_277, c_1666])).
% 45.55/34.09  tff(c_1700, plain, (r1_tarski(k1_tops_1('#skF_1', k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2'))), u1_struct_0('#skF_1')) | ~m1_subset_1(k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2')), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_1683])).
% 45.55/34.09  tff(c_5631, plain, (~m1_subset_1(k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2')), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitLeft, [status(thm)], [c_1700])).
% 45.55/34.09  tff(c_5634, plain, (~m1_subset_1(k1_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_14, c_5631])).
% 45.55/34.09  tff(c_5640, plain, (~m1_subset_1(k1_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_5634])).
% 45.55/34.09  tff(c_5646, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_26, c_5640])).
% 45.55/34.09  tff(c_5653, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_5646])).
% 45.55/34.09  tff(c_5655, plain, (m1_subset_1(k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2')), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitRight, [status(thm)], [c_1700])).
% 45.55/34.09  tff(c_815, plain, (r1_tarski(k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_2')), k2_pre_topc('#skF_1', '#skF_2'))), inference(splitRight, [status(thm)], [c_775])).
% 45.55/34.09  tff(c_1298, plain, (![A_105, B_106, C_107]: (r1_tarski(k2_pre_topc(A_105, B_106), k2_pre_topc(A_105, C_107)) | ~r1_tarski(B_106, C_107) | ~m1_subset_1(C_107, k1_zfmisc_1(u1_struct_0(A_105))) | ~m1_subset_1(B_106, k1_zfmisc_1(u1_struct_0(A_105))) | ~l1_pre_topc(A_105))), inference(cnfTransformation, [status(thm)], [f_65])).
% 45.55/34.09  tff(c_6014, plain, (![A_232, A_233, C_234, B_235]: (r1_tarski(A_232, k2_pre_topc(A_233, C_234)) | ~r1_tarski(A_232, k2_pre_topc(A_233, B_235)) | ~r1_tarski(B_235, C_234) | ~m1_subset_1(C_234, k1_zfmisc_1(u1_struct_0(A_233))) | ~m1_subset_1(B_235, k1_zfmisc_1(u1_struct_0(A_233))) | ~l1_pre_topc(A_233))), inference(resolution, [status(thm)], [c_1298, c_8])).
% 45.55/34.09  tff(c_6044, plain, (![C_234]: (r1_tarski(k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_2')), k2_pre_topc('#skF_1', C_234)) | ~r1_tarski('#skF_2', C_234) | ~m1_subset_1(C_234, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_815, c_6014])).
% 45.62/34.09  tff(c_6495, plain, (![C_239]: (r1_tarski(k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_2')), k2_pre_topc('#skF_1', C_239)) | ~r1_tarski('#skF_2', C_239) | ~m1_subset_1(C_239, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_6044])).
% 45.62/34.09  tff(c_6539, plain, (r1_tarski(k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_2')), k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2'))) | ~r1_tarski('#skF_2', k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2'))) | ~m1_subset_1(k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2')), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_277, c_6495])).
% 45.62/34.09  tff(c_6579, plain, (r1_tarski(k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_2')), k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2'))) | ~r1_tarski('#skF_2', k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_5655, c_6539])).
% 45.62/34.09  tff(c_6584, plain, (~r1_tarski('#skF_2', k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2')))), inference(splitLeft, [status(thm)], [c_6579])).
% 45.62/34.09  tff(c_6587, plain, (~r1_tarski('#skF_2', '#skF_2') | ~v4_tops_1('#skF_2', '#skF_1') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_888, c_6584])).
% 45.62/34.09  tff(c_6594, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_36, c_6, c_6587])).
% 45.62/34.09  tff(c_6596, plain, (r1_tarski('#skF_2', k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2')))), inference(splitRight, [status(thm)], [c_6579])).
% 45.62/34.09  tff(c_1332, plain, (![B_106]: (r1_tarski(k2_pre_topc('#skF_1', B_106), k2_pre_topc('#skF_1', '#skF_2')) | ~r1_tarski(B_106, k2_pre_topc('#skF_1', '#skF_2')) | ~m1_subset_1(k2_pre_topc('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1(B_106, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_240, c_1298])).
% 45.62/34.09  tff(c_1350, plain, (![B_106]: (r1_tarski(k2_pre_topc('#skF_1', B_106), k2_pre_topc('#skF_1', '#skF_2')) | ~r1_tarski(B_106, k2_pre_topc('#skF_1', '#skF_2')) | ~m1_subset_1(B_106, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_816, c_1332])).
% 45.62/34.09  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 45.62/34.09  tff(c_6636, plain, (![A_240, C_241, B_242]: (k2_pre_topc(A_240, C_241)=k2_pre_topc(A_240, B_242) | ~r1_tarski(k2_pre_topc(A_240, C_241), k2_pre_topc(A_240, B_242)) | ~r1_tarski(B_242, C_241) | ~m1_subset_1(C_241, k1_zfmisc_1(u1_struct_0(A_240))) | ~m1_subset_1(B_242, k1_zfmisc_1(u1_struct_0(A_240))) | ~l1_pre_topc(A_240))), inference(resolution, [status(thm)], [c_1298, c_2])).
% 45.62/34.09  tff(c_6661, plain, (![B_106]: (k2_pre_topc('#skF_1', B_106)=k2_pre_topc('#skF_1', '#skF_2') | ~r1_tarski('#skF_2', B_106) | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1') | ~r1_tarski(B_106, k2_pre_topc('#skF_1', '#skF_2')) | ~m1_subset_1(B_106, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(resolution, [status(thm)], [c_1350, c_6636])).
% 45.62/34.09  tff(c_8560, plain, (![B_270]: (k2_pre_topc('#skF_1', B_270)=k2_pre_topc('#skF_1', '#skF_2') | ~r1_tarski('#skF_2', B_270) | ~r1_tarski(B_270, k2_pre_topc('#skF_1', '#skF_2')) | ~m1_subset_1(B_270, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_6661])).
% 45.62/34.09  tff(c_8563, plain, (k2_pre_topc('#skF_1', k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2')))=k2_pre_topc('#skF_1', '#skF_2') | ~r1_tarski('#skF_2', k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2'))) | ~r1_tarski(k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2')), k2_pre_topc('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_5655, c_8560])).
% 45.62/34.09  tff(c_8587, plain, (k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2') | ~r1_tarski(k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2')), k2_pre_topc('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_6596, c_277, c_8563])).
% 45.62/34.09  tff(c_8605, plain, (~r1_tarski(k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2')), k2_pre_topc('#skF_1', '#skF_2'))), inference(splitLeft, [status(thm)], [c_8587])).
% 45.62/34.09  tff(c_8611, plain, (~r1_tarski(k1_tops_1('#skF_1', '#skF_2'), '#skF_2') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1(k1_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_18, c_8605])).
% 45.62/34.09  tff(c_8615, plain, (~m1_subset_1(k1_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_99, c_8611])).
% 45.62/34.09  tff(c_8618, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_26, c_8615])).
% 45.62/34.09  tff(c_8625, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_8618])).
% 45.62/34.09  tff(c_8626, plain, (k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_8587])).
% 45.62/34.09  tff(c_6739, plain, (![A_243]: (r1_tarski(A_243, k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2'))) | ~r1_tarski(A_243, '#skF_2'))), inference(resolution, [status(thm)], [c_6596, c_8])).
% 45.62/34.09  tff(c_6848, plain, (![A_244, A_245]: (r1_tarski(A_244, k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2'))) | ~r1_tarski(A_244, A_245) | ~r1_tarski(A_245, '#skF_2'))), inference(resolution, [status(thm)], [c_6739, c_8])).
% 45.62/34.09  tff(c_6958, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_2'), k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2'))) | ~r1_tarski('#skF_2', '#skF_2')), inference(resolution, [status(thm)], [c_99, c_6848])).
% 45.62/34.09  tff(c_7039, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_2'), k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_6958])).
% 45.62/34.09  tff(c_8638, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_2'), k2_pre_topc('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_8626, c_7039])).
% 45.62/34.09  tff(c_34, plain, (~v4_tops_1(k2_pre_topc('#skF_1', '#skF_2'), '#skF_1') | ~v4_tops_1(k1_tops_1('#skF_1', '#skF_2'), '#skF_1')), inference(cnfTransformation, [status(thm)], [f_119])).
% 45.62/34.09  tff(c_64, plain, (~v4_tops_1(k1_tops_1('#skF_1', '#skF_2'), '#skF_1')), inference(splitLeft, [status(thm)], [c_34])).
% 45.62/34.09  tff(c_285, plain, (![A_73, B_74]: (k1_tops_1(A_73, k1_tops_1(A_73, B_74))=k1_tops_1(A_73, B_74) | ~m1_subset_1(B_74, k1_zfmisc_1(u1_struct_0(A_73))) | ~l1_pre_topc(A_73))), inference(cnfTransformation, [status(thm)], [f_88])).
% 45.62/34.09  tff(c_294, plain, (k1_tops_1('#skF_1', k1_tops_1('#skF_1', '#skF_2'))=k1_tops_1('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_38, c_285])).
% 45.62/34.09  tff(c_300, plain, (k1_tops_1('#skF_1', k1_tops_1('#skF_1', '#skF_2'))=k1_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_294])).
% 45.62/34.09  tff(c_20, plain, (![B_21, A_19]: (v4_tops_1(B_21, A_19) | ~r1_tarski(B_21, k2_pre_topc(A_19, k1_tops_1(A_19, B_21))) | ~r1_tarski(k1_tops_1(A_19, k2_pre_topc(A_19, B_21)), B_21) | ~m1_subset_1(B_21, k1_zfmisc_1(u1_struct_0(A_19))) | ~l1_pre_topc(A_19))), inference(cnfTransformation, [status(thm)], [f_76])).
% 45.62/34.09  tff(c_8758, plain, (v4_tops_1(k1_tops_1('#skF_1', '#skF_2'), '#skF_1') | ~r1_tarski(k1_tops_1('#skF_1', '#skF_2'), k2_pre_topc('#skF_1', k1_tops_1('#skF_1', k1_tops_1('#skF_1', '#skF_2')))) | ~r1_tarski(k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_2')), k1_tops_1('#skF_1', '#skF_2')) | ~m1_subset_1(k1_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_8626, c_20])).
% 45.62/34.09  tff(c_8852, plain, (v4_tops_1(k1_tops_1('#skF_1', '#skF_2'), '#skF_1') | ~r1_tarski(k1_tops_1('#skF_1', '#skF_2'), k2_pre_topc('#skF_1', '#skF_2')) | ~r1_tarski(k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_2')), k1_tops_1('#skF_1', '#skF_2')) | ~m1_subset_1(k1_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_8626, c_300, c_8758])).
% 45.62/34.09  tff(c_8853, plain, (~r1_tarski(k1_tops_1('#skF_1', '#skF_2'), k2_pre_topc('#skF_1', '#skF_2')) | ~r1_tarski(k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_2')), k1_tops_1('#skF_1', '#skF_2')) | ~m1_subset_1(k1_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(negUnitSimplification, [status(thm)], [c_64, c_8852])).
% 45.62/34.09  tff(c_9361, plain, (~r1_tarski(k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_2')), k1_tops_1('#skF_1', '#skF_2')) | ~m1_subset_1(k1_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_8638, c_8853])).
% 45.62/34.09  tff(c_9362, plain, (~m1_subset_1(k1_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitLeft, [status(thm)], [c_9361])).
% 45.62/34.09  tff(c_9365, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_26, c_9362])).
% 45.62/34.09  tff(c_9372, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_9365])).
% 45.62/34.09  tff(c_9374, plain, (m1_subset_1(k1_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitRight, [status(thm)], [c_9361])).
% 45.62/34.09  tff(c_1017, plain, (![A_99, B_100, C_101]: (r1_tarski(k1_tops_1(A_99, B_100), k1_tops_1(A_99, C_101)) | ~r1_tarski(B_100, C_101) | ~m1_subset_1(C_101, k1_zfmisc_1(u1_struct_0(A_99))) | ~m1_subset_1(B_100, k1_zfmisc_1(u1_struct_0(A_99))) | ~l1_pre_topc(A_99))), inference(cnfTransformation, [status(thm)], [f_107])).
% 45.62/34.09  tff(c_1062, plain, (![C_101]: (r1_tarski(k1_tops_1('#skF_1', '#skF_2'), k1_tops_1('#skF_1', C_101)) | ~r1_tarski(k1_tops_1('#skF_1', '#skF_2'), C_101) | ~m1_subset_1(C_101, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1(k1_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_300, c_1017])).
% 45.62/34.09  tff(c_1089, plain, (![C_101]: (r1_tarski(k1_tops_1('#skF_1', '#skF_2'), k1_tops_1('#skF_1', C_101)) | ~r1_tarski(k1_tops_1('#skF_1', '#skF_2'), C_101) | ~m1_subset_1(C_101, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1(k1_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_1062])).
% 45.62/34.09  tff(c_27179, plain, (![C_101]: (r1_tarski(k1_tops_1('#skF_1', '#skF_2'), k1_tops_1('#skF_1', C_101)) | ~r1_tarski(k1_tops_1('#skF_1', '#skF_2'), C_101) | ~m1_subset_1(C_101, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_9374, c_1089])).
% 45.62/34.09  tff(c_28, plain, (![A_24, B_25]: (k1_tops_1(A_24, k1_tops_1(A_24, B_25))=k1_tops_1(A_24, B_25) | ~m1_subset_1(B_25, k1_zfmisc_1(u1_struct_0(A_24))) | ~l1_pre_topc(A_24))), inference(cnfTransformation, [status(thm)], [f_88])).
% 45.62/34.09  tff(c_818, plain, (k1_tops_1('#skF_1', k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_2')))=k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_2')) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_816, c_28])).
% 45.62/34.09  tff(c_828, plain, (k1_tops_1('#skF_1', k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_2')))=k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_818])).
% 45.62/34.09  tff(c_168, plain, (![A_57, B_58]: (m1_subset_1(k1_tops_1(A_57, B_58), k1_zfmisc_1(u1_struct_0(A_57))) | ~m1_subset_1(B_58, k1_zfmisc_1(u1_struct_0(A_57))) | ~l1_pre_topc(A_57))), inference(cnfTransformation, [status(thm)], [f_82])).
% 45.62/34.09  tff(c_174, plain, (![A_57, B_58]: (r1_tarski(k1_tops_1(A_57, k1_tops_1(A_57, B_58)), k1_tops_1(A_57, B_58)) | ~m1_subset_1(B_58, k1_zfmisc_1(u1_struct_0(A_57))) | ~l1_pre_topc(A_57))), inference(resolution, [status(thm)], [c_168, c_30])).
% 45.62/34.09  tff(c_614, plain, (![A_85, B_86]: (r1_tarski(k1_tops_1(A_85, k2_pre_topc(A_85, B_86)), B_86) | ~v4_tops_1(B_86, A_85) | ~m1_subset_1(B_86, k1_zfmisc_1(u1_struct_0(A_85))) | ~l1_pre_topc(A_85))), inference(cnfTransformation, [status(thm)], [f_76])).
% 45.62/34.09  tff(c_4419, plain, (![A_191, B_192, A_193]: (r1_tarski(A_191, B_192) | ~r1_tarski(A_191, k1_tops_1(A_193, k2_pre_topc(A_193, B_192))) | ~v4_tops_1(B_192, A_193) | ~m1_subset_1(B_192, k1_zfmisc_1(u1_struct_0(A_193))) | ~l1_pre_topc(A_193))), inference(resolution, [status(thm)], [c_614, c_8])).
% 45.62/34.09  tff(c_28386, plain, (![A_460, B_461]: (r1_tarski(k1_tops_1(A_460, k1_tops_1(A_460, k2_pre_topc(A_460, B_461))), B_461) | ~v4_tops_1(B_461, A_460) | ~m1_subset_1(B_461, k1_zfmisc_1(u1_struct_0(A_460))) | ~m1_subset_1(k2_pre_topc(A_460, B_461), k1_zfmisc_1(u1_struct_0(A_460))) | ~l1_pre_topc(A_460))), inference(resolution, [status(thm)], [c_174, c_4419])).
% 45.62/34.09  tff(c_28610, plain, (r1_tarski(k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_2')), '#skF_2') | ~v4_tops_1('#skF_2', '#skF_1') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1(k2_pre_topc('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_828, c_28386])).
% 45.62/34.09  tff(c_28694, plain, (r1_tarski(k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_2')), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_816, c_38, c_36, c_28610])).
% 45.62/34.09  tff(c_1556, plain, (![B_115, A_116]: (v4_tops_1(B_115, A_116) | ~r1_tarski(B_115, k2_pre_topc(A_116, k1_tops_1(A_116, B_115))) | ~r1_tarski(k1_tops_1(A_116, k2_pre_topc(A_116, B_115)), B_115) | ~m1_subset_1(B_115, k1_zfmisc_1(u1_struct_0(A_116))) | ~l1_pre_topc(A_116))), inference(cnfTransformation, [status(thm)], [f_76])).
% 45.62/34.09  tff(c_1591, plain, (v4_tops_1(k2_pre_topc('#skF_1', '#skF_2'), '#skF_1') | ~r1_tarski(k2_pre_topc('#skF_1', '#skF_2'), k2_pre_topc('#skF_1', k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_2')))) | ~r1_tarski(k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_2')), k2_pre_topc('#skF_1', '#skF_2')) | ~m1_subset_1(k2_pre_topc('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_240, c_1556])).
% 45.62/34.09  tff(c_1617, plain, (v4_tops_1(k2_pre_topc('#skF_1', '#skF_2'), '#skF_1') | ~r1_tarski(k2_pre_topc('#skF_1', '#skF_2'), k2_pre_topc('#skF_1', k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_816, c_815, c_1591])).
% 45.62/34.09  tff(c_1705, plain, (~r1_tarski(k2_pre_topc('#skF_1', '#skF_2'), k2_pre_topc('#skF_1', k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_2'))))), inference(splitLeft, [status(thm)], [c_1617])).
% 45.62/34.09  tff(c_1717, plain, (~r1_tarski('#skF_2', k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_2'))) | ~m1_subset_1(k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_2')), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_18, c_1705])).
% 45.62/34.09  tff(c_1724, plain, (~r1_tarski('#skF_2', k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_2'))) | ~m1_subset_1(k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_2')), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_1717])).
% 45.62/34.09  tff(c_1728, plain, (~m1_subset_1(k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_2')), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitLeft, [status(thm)], [c_1724])).
% 45.62/34.09  tff(c_1731, plain, (~m1_subset_1(k2_pre_topc('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_26, c_1728])).
% 45.62/34.09  tff(c_1738, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_40, c_816, c_1731])).
% 45.62/34.09  tff(c_1740, plain, (m1_subset_1(k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_2')), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitRight, [status(thm)], [c_1724])).
% 45.62/34.09  tff(c_32, plain, (![A_29, B_33, C_35]: (r1_tarski(k1_tops_1(A_29, B_33), k1_tops_1(A_29, C_35)) | ~r1_tarski(B_33, C_35) | ~m1_subset_1(C_35, k1_zfmisc_1(u1_struct_0(A_29))) | ~m1_subset_1(B_33, k1_zfmisc_1(u1_struct_0(A_29))) | ~l1_pre_topc(A_29))), inference(cnfTransformation, [status(thm)], [f_107])).
% 45.62/34.09  tff(c_7593, plain, (![A_252, C_253, B_254]: (k1_tops_1(A_252, C_253)=k1_tops_1(A_252, B_254) | ~r1_tarski(k1_tops_1(A_252, C_253), k1_tops_1(A_252, B_254)) | ~r1_tarski(B_254, C_253) | ~m1_subset_1(C_253, k1_zfmisc_1(u1_struct_0(A_252))) | ~m1_subset_1(B_254, k1_zfmisc_1(u1_struct_0(A_252))) | ~l1_pre_topc(A_252))), inference(resolution, [status(thm)], [c_1017, c_2])).
% 45.62/34.09  tff(c_7653, plain, (![C_253]: (k1_tops_1('#skF_1', k1_tops_1('#skF_1', '#skF_2'))=k1_tops_1('#skF_1', C_253) | ~r1_tarski(k1_tops_1('#skF_1', C_253), k1_tops_1('#skF_1', '#skF_2')) | ~r1_tarski(k1_tops_1('#skF_1', '#skF_2'), C_253) | ~m1_subset_1(C_253, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1(k1_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_300, c_7593])).
% 45.62/34.09  tff(c_7684, plain, (![C_253]: (k1_tops_1('#skF_1', C_253)=k1_tops_1('#skF_1', '#skF_2') | ~r1_tarski(k1_tops_1('#skF_1', C_253), k1_tops_1('#skF_1', '#skF_2')) | ~r1_tarski(k1_tops_1('#skF_1', '#skF_2'), C_253) | ~m1_subset_1(C_253, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1(k1_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_300, c_7653])).
% 45.62/34.09  tff(c_36036, plain, (![C_529]: (k1_tops_1('#skF_1', C_529)=k1_tops_1('#skF_1', '#skF_2') | ~r1_tarski(k1_tops_1('#skF_1', C_529), k1_tops_1('#skF_1', '#skF_2')) | ~r1_tarski(k1_tops_1('#skF_1', '#skF_2'), C_529) | ~m1_subset_1(C_529, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_9374, c_7684])).
% 45.62/34.09  tff(c_36120, plain, (![B_33]: (k1_tops_1('#skF_1', B_33)=k1_tops_1('#skF_1', '#skF_2') | ~r1_tarski(k1_tops_1('#skF_1', '#skF_2'), B_33) | ~r1_tarski(B_33, '#skF_2') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1(B_33, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_32, c_36036])).
% 45.62/34.09  tff(c_83347, plain, (![B_813]: (k1_tops_1('#skF_1', B_813)=k1_tops_1('#skF_1', '#skF_2') | ~r1_tarski(k1_tops_1('#skF_1', '#skF_2'), B_813) | ~r1_tarski(B_813, '#skF_2') | ~m1_subset_1(B_813, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_36120])).
% 45.62/34.09  tff(c_83362, plain, (k1_tops_1('#skF_1', k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_2')))=k1_tops_1('#skF_1', '#skF_2') | ~r1_tarski(k1_tops_1('#skF_1', '#skF_2'), k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_2'))) | ~r1_tarski(k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_2')), '#skF_2')), inference(resolution, [status(thm)], [c_1740, c_83347])).
% 45.62/34.09  tff(c_83395, plain, (k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_2'))=k1_tops_1('#skF_1', '#skF_2') | ~r1_tarski(k1_tops_1('#skF_1', '#skF_2'), k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_28694, c_828, c_83362])).
% 45.62/34.09  tff(c_83410, plain, (~r1_tarski(k1_tops_1('#skF_1', '#skF_2'), k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_2')))), inference(splitLeft, [status(thm)], [c_83395])).
% 45.62/34.09  tff(c_83440, plain, (~r1_tarski(k1_tops_1('#skF_1', '#skF_2'), k2_pre_topc('#skF_1', '#skF_2')) | ~m1_subset_1(k2_pre_topc('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_27179, c_83410])).
% 45.62/34.09  tff(c_83477, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_816, c_8638, c_83440])).
% 45.62/34.09  tff(c_83478, plain, (k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_2'))=k1_tops_1('#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_83395])).
% 45.62/34.09  tff(c_9373, plain, (~r1_tarski(k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_2')), k1_tops_1('#skF_1', '#skF_2'))), inference(splitRight, [status(thm)], [c_9361])).
% 45.62/34.09  tff(c_83503, plain, (~r1_tarski(k1_tops_1('#skF_1', '#skF_2'), k1_tops_1('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_83478, c_9373])).
% 45.62/34.09  tff(c_83523, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_83503])).
% 45.62/34.09  tff(c_83524, plain, (~v4_tops_1(k2_pre_topc('#skF_1', '#skF_2'), '#skF_1')), inference(splitRight, [status(thm)], [c_34])).
% 45.62/34.09  tff(c_83525, plain, (v4_tops_1(k1_tops_1('#skF_1', '#skF_2'), '#skF_1')), inference(splitRight, [status(thm)], [c_34])).
% 45.62/34.09  tff(c_83686, plain, (![A_839, B_840]: (k1_tops_1(A_839, k1_tops_1(A_839, B_840))=k1_tops_1(A_839, B_840) | ~m1_subset_1(B_840, k1_zfmisc_1(u1_struct_0(A_839))) | ~l1_pre_topc(A_839))), inference(cnfTransformation, [status(thm)], [f_88])).
% 45.62/34.09  tff(c_83695, plain, (k1_tops_1('#skF_1', k1_tops_1('#skF_1', '#skF_2'))=k1_tops_1('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_38, c_83686])).
% 45.62/34.09  tff(c_83701, plain, (k1_tops_1('#skF_1', k1_tops_1('#skF_1', '#skF_2'))=k1_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_83695])).
% 45.62/34.09  tff(c_84327, plain, (![B_864, A_865]: (r1_tarski(B_864, k2_pre_topc(A_865, k1_tops_1(A_865, B_864))) | ~v4_tops_1(B_864, A_865) | ~m1_subset_1(B_864, k1_zfmisc_1(u1_struct_0(A_865))) | ~l1_pre_topc(A_865))), inference(cnfTransformation, [status(thm)], [f_76])).
% 45.62/34.09  tff(c_84346, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_2'), k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2'))) | ~v4_tops_1(k1_tops_1('#skF_1', '#skF_2'), '#skF_1') | ~m1_subset_1(k1_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_83701, c_84327])).
% 45.62/34.09  tff(c_84354, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_2'), k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2'))) | ~m1_subset_1(k1_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_83525, c_84346])).
% 45.62/34.09  tff(c_84851, plain, (~m1_subset_1(k1_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitLeft, [status(thm)], [c_84354])).
% 45.62/34.09  tff(c_84854, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_26, c_84851])).
% 45.62/34.09  tff(c_84861, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_84854])).
% 45.62/34.09  tff(c_84863, plain, (m1_subset_1(k1_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitRight, [status(thm)], [c_84354])).
% 45.62/34.09  tff(c_83551, plain, (![A_820, B_821]: (r1_tarski(k1_tops_1(A_820, B_821), B_821) | ~m1_subset_1(B_821, k1_zfmisc_1(u1_struct_0(A_820))) | ~l1_pre_topc(A_820))), inference(cnfTransformation, [status(thm)], [f_95])).
% 45.62/34.09  tff(c_83556, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_2'), '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_38, c_83551])).
% 45.62/34.09  tff(c_83560, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_83556])).
% 45.62/34.09  tff(c_85731, plain, (![A_907, B_908]: (k1_tops_1(A_907, k1_tops_1(A_907, k2_pre_topc(A_907, B_908)))=k1_tops_1(A_907, k2_pre_topc(A_907, B_908)) | ~m1_subset_1(B_908, k1_zfmisc_1(u1_struct_0(A_907))) | ~l1_pre_topc(A_907))), inference(resolution, [status(thm)], [c_14, c_83686])).
% 45.62/34.09  tff(c_85735, plain, (k1_tops_1('#skF_1', k1_tops_1('#skF_1', k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2'))))=k1_tops_1('#skF_1', k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2'))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_84863, c_85731])).
% 45.62/34.09  tff(c_85752, plain, (k1_tops_1('#skF_1', k1_tops_1('#skF_1', k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2'))))=k1_tops_1('#skF_1', k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_85735])).
% 45.62/34.09  tff(c_83629, plain, (![A_827, B_828]: (m1_subset_1(k1_tops_1(A_827, B_828), k1_zfmisc_1(u1_struct_0(A_827))) | ~m1_subset_1(B_828, k1_zfmisc_1(u1_struct_0(A_827))) | ~l1_pre_topc(A_827))), inference(cnfTransformation, [status(thm)], [f_82])).
% 45.62/34.09  tff(c_83635, plain, (![A_827, B_828]: (r1_tarski(k1_tops_1(A_827, k1_tops_1(A_827, B_828)), k1_tops_1(A_827, B_828)) | ~m1_subset_1(B_828, k1_zfmisc_1(u1_struct_0(A_827))) | ~l1_pre_topc(A_827))), inference(resolution, [status(thm)], [c_83629, c_30])).
% 45.62/34.09  tff(c_83637, plain, (![A_829, B_830]: (r1_tarski(k1_tops_1(A_829, B_830), u1_struct_0(A_829)) | ~m1_subset_1(B_830, k1_zfmisc_1(u1_struct_0(A_829))) | ~l1_pre_topc(A_829))), inference(resolution, [status(thm)], [c_83629, c_10])).
% 45.62/34.09  tff(c_84239, plain, (![A_861, A_862, B_863]: (r1_tarski(A_861, u1_struct_0(A_862)) | ~r1_tarski(A_861, k1_tops_1(A_862, B_863)) | ~m1_subset_1(B_863, k1_zfmisc_1(u1_struct_0(A_862))) | ~l1_pre_topc(A_862))), inference(resolution, [status(thm)], [c_83637, c_8])).
% 45.62/34.09  tff(c_84257, plain, (![A_827, B_828]: (r1_tarski(k1_tops_1(A_827, k1_tops_1(A_827, B_828)), u1_struct_0(A_827)) | ~m1_subset_1(B_828, k1_zfmisc_1(u1_struct_0(A_827))) | ~l1_pre_topc(A_827))), inference(resolution, [status(thm)], [c_83635, c_84239])).
% 45.62/34.09  tff(c_85774, plain, (r1_tarski(k1_tops_1('#skF_1', k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2'))), u1_struct_0('#skF_1')) | ~m1_subset_1(k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2')), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_85752, c_84257])).
% 45.62/34.09  tff(c_85836, plain, (r1_tarski(k1_tops_1('#skF_1', k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2'))), u1_struct_0('#skF_1')) | ~m1_subset_1(k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2')), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_85774])).
% 45.62/34.09  tff(c_89365, plain, (~m1_subset_1(k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2')), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitLeft, [status(thm)], [c_85836])).
% 45.62/34.09  tff(c_89453, plain, (~m1_subset_1(k1_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_14, c_89365])).
% 45.62/34.09  tff(c_89460, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_40, c_84863, c_89453])).
% 45.62/34.09  tff(c_89462, plain, (m1_subset_1(k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2')), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitRight, [status(thm)], [c_85836])).
% 45.62/34.09  tff(c_84862, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_2'), k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2')))), inference(splitRight, [status(thm)], [c_84354])).
% 45.62/34.09  tff(c_84478, plain, (![A_869, B_870, C_871]: (r1_tarski(k1_tops_1(A_869, B_870), k1_tops_1(A_869, C_871)) | ~r1_tarski(B_870, C_871) | ~m1_subset_1(C_871, k1_zfmisc_1(u1_struct_0(A_869))) | ~m1_subset_1(B_870, k1_zfmisc_1(u1_struct_0(A_869))) | ~l1_pre_topc(A_869))), inference(cnfTransformation, [status(thm)], [f_107])).
% 45.62/34.09  tff(c_89770, plain, (![A_1001, A_1002, C_1003, B_1004]: (r1_tarski(A_1001, k1_tops_1(A_1002, C_1003)) | ~r1_tarski(A_1001, k1_tops_1(A_1002, B_1004)) | ~r1_tarski(B_1004, C_1003) | ~m1_subset_1(C_1003, k1_zfmisc_1(u1_struct_0(A_1002))) | ~m1_subset_1(B_1004, k1_zfmisc_1(u1_struct_0(A_1002))) | ~l1_pre_topc(A_1002))), inference(resolution, [status(thm)], [c_84478, c_8])).
% 45.62/34.09  tff(c_89797, plain, (![A_1001, C_1003]: (r1_tarski(A_1001, k1_tops_1('#skF_1', C_1003)) | ~r1_tarski(A_1001, k1_tops_1('#skF_1', '#skF_2')) | ~r1_tarski(k1_tops_1('#skF_1', '#skF_2'), C_1003) | ~m1_subset_1(C_1003, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1(k1_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_83701, c_89770])).
% 45.62/34.09  tff(c_89830, plain, (![A_1005, C_1006]: (r1_tarski(A_1005, k1_tops_1('#skF_1', C_1006)) | ~r1_tarski(A_1005, k1_tops_1('#skF_1', '#skF_2')) | ~r1_tarski(k1_tops_1('#skF_1', '#skF_2'), C_1006) | ~m1_subset_1(C_1006, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_84863, c_89797])).
% 45.62/34.09  tff(c_89842, plain, (![C_1006]: (r1_tarski(k1_tops_1('#skF_1', k1_tops_1('#skF_1', '#skF_2')), k1_tops_1('#skF_1', C_1006)) | ~r1_tarski(k1_tops_1('#skF_1', '#skF_2'), C_1006) | ~m1_subset_1(C_1006, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_83635, c_89830])).
% 45.62/34.09  tff(c_89979, plain, (![C_1009]: (r1_tarski(k1_tops_1('#skF_1', '#skF_2'), k1_tops_1('#skF_1', C_1009)) | ~r1_tarski(k1_tops_1('#skF_1', '#skF_2'), C_1009) | ~m1_subset_1(C_1009, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_83701, c_89842])).
% 45.62/34.09  tff(c_84075, plain, (![A_855, B_856]: (r1_tarski(k1_tops_1(A_855, k2_pre_topc(A_855, B_856)), B_856) | ~v4_tops_1(B_856, A_855) | ~m1_subset_1(B_856, k1_zfmisc_1(u1_struct_0(A_855))) | ~l1_pre_topc(A_855))), inference(cnfTransformation, [status(thm)], [f_76])).
% 45.62/34.09  tff(c_84118, plain, (![A_855, B_856]: (k1_tops_1(A_855, k2_pre_topc(A_855, B_856))=B_856 | ~r1_tarski(B_856, k1_tops_1(A_855, k2_pre_topc(A_855, B_856))) | ~v4_tops_1(B_856, A_855) | ~m1_subset_1(B_856, k1_zfmisc_1(u1_struct_0(A_855))) | ~l1_pre_topc(A_855))), inference(resolution, [status(thm)], [c_84075, c_2])).
% 45.62/34.09  tff(c_90006, plain, (k1_tops_1('#skF_1', k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2')))=k1_tops_1('#skF_1', '#skF_2') | ~v4_tops_1(k1_tops_1('#skF_1', '#skF_2'), '#skF_1') | ~m1_subset_1(k1_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1') | ~r1_tarski(k1_tops_1('#skF_1', '#skF_2'), k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2'))) | ~m1_subset_1(k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2')), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_89979, c_84118])).
% 45.62/34.09  tff(c_90114, plain, (k1_tops_1('#skF_1', k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2')))=k1_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_89462, c_84862, c_40, c_84863, c_83525, c_90006])).
% 45.62/34.09  tff(c_83760, plain, (![A_843, B_844]: (k2_pre_topc(A_843, k2_pre_topc(A_843, B_844))=k2_pre_topc(A_843, B_844) | ~m1_subset_1(B_844, k1_zfmisc_1(u1_struct_0(A_843))) | ~l1_pre_topc(A_843))), inference(cnfTransformation, [status(thm)], [f_53])).
% 45.62/34.09  tff(c_83769, plain, (k2_pre_topc('#skF_1', k2_pre_topc('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_38, c_83760])).
% 45.62/34.09  tff(c_83775, plain, (k2_pre_topc('#skF_1', k2_pre_topc('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_83769])).
% 45.62/34.09  tff(c_83647, plain, (![A_831, B_832]: (m1_subset_1(k2_pre_topc(A_831, B_832), k1_zfmisc_1(u1_struct_0(A_831))) | ~m1_subset_1(B_832, k1_zfmisc_1(u1_struct_0(A_831))) | ~l1_pre_topc(A_831))), inference(cnfTransformation, [status(thm)], [f_47])).
% 45.62/34.09  tff(c_84193, plain, (![A_859, B_860]: (r1_tarski(k1_tops_1(A_859, k2_pre_topc(A_859, B_860)), k2_pre_topc(A_859, B_860)) | ~m1_subset_1(B_860, k1_zfmisc_1(u1_struct_0(A_859))) | ~l1_pre_topc(A_859))), inference(resolution, [status(thm)], [c_83647, c_30])).
% 45.62/34.09  tff(c_84220, plain, (r1_tarski(k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_2')), k2_pre_topc('#skF_1', k2_pre_topc('#skF_1', '#skF_2'))) | ~m1_subset_1(k2_pre_topc('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_83775, c_84193])).
% 45.62/34.09  tff(c_84236, plain, (r1_tarski(k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_2')), k2_pre_topc('#skF_1', '#skF_2')) | ~m1_subset_1(k2_pre_topc('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_83775, c_84220])).
% 45.62/34.09  tff(c_84265, plain, (~m1_subset_1(k2_pre_topc('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitLeft, [status(thm)], [c_84236])).
% 45.62/34.09  tff(c_84268, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_14, c_84265])).
% 45.62/34.09  tff(c_84275, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_84268])).
% 45.62/34.09  tff(c_84277, plain, (m1_subset_1(k2_pre_topc('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitRight, [status(thm)], [c_84236])).
% 45.62/34.09  tff(c_84276, plain, (r1_tarski(k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_2')), k2_pre_topc('#skF_1', '#skF_2'))), inference(splitRight, [status(thm)], [c_84236])).
% 45.62/34.09  tff(c_84324, plain, (![A_3]: (r1_tarski(A_3, k2_pre_topc('#skF_1', '#skF_2')) | ~r1_tarski(A_3, k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_2'))))), inference(resolution, [status(thm)], [c_84276, c_8])).
% 45.62/34.09  tff(c_84482, plain, (![B_870]: (r1_tarski(k1_tops_1('#skF_1', B_870), k2_pre_topc('#skF_1', '#skF_2')) | ~r1_tarski(B_870, k2_pre_topc('#skF_1', '#skF_2')) | ~m1_subset_1(k2_pre_topc('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1(B_870, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_84478, c_84324])).
% 45.62/34.09  tff(c_84529, plain, (![B_870]: (r1_tarski(k1_tops_1('#skF_1', B_870), k2_pre_topc('#skF_1', '#skF_2')) | ~r1_tarski(B_870, k2_pre_topc('#skF_1', '#skF_2')) | ~m1_subset_1(B_870, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_84277, c_84482])).
% 45.62/34.09  tff(c_90291, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_2'), k2_pre_topc('#skF_1', '#skF_2')) | ~r1_tarski(k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2')), k2_pre_topc('#skF_1', '#skF_2')) | ~m1_subset_1(k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2')), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_90114, c_84529])).
% 45.62/34.09  tff(c_90440, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_2'), k2_pre_topc('#skF_1', '#skF_2')) | ~r1_tarski(k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2')), k2_pre_topc('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_89462, c_90291])).
% 45.62/34.09  tff(c_90493, plain, (~r1_tarski(k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2')), k2_pre_topc('#skF_1', '#skF_2'))), inference(splitLeft, [status(thm)], [c_90440])).
% 45.62/34.09  tff(c_90584, plain, (~r1_tarski(k1_tops_1('#skF_1', '#skF_2'), '#skF_2') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1(k1_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_18, c_90493])).
% 45.62/34.09  tff(c_90591, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_40, c_84863, c_38, c_83560, c_90584])).
% 45.62/34.09  tff(c_90593, plain, (r1_tarski(k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2')), k2_pre_topc('#skF_1', '#skF_2'))), inference(splitRight, [status(thm)], [c_90440])).
% 45.62/34.09  tff(c_84349, plain, (![A_3, A_865, B_864]: (r1_tarski(A_3, k2_pre_topc(A_865, k1_tops_1(A_865, B_864))) | ~r1_tarski(A_3, B_864) | ~v4_tops_1(B_864, A_865) | ~m1_subset_1(B_864, k1_zfmisc_1(u1_struct_0(A_865))) | ~l1_pre_topc(A_865))), inference(resolution, [status(thm)], [c_84327, c_8])).
% 45.62/34.09  tff(c_83526, plain, (![A_814, C_815, B_816]: (r1_tarski(A_814, C_815) | ~r1_tarski(B_816, C_815) | ~r1_tarski(A_814, B_816))), inference(cnfTransformation, [status(thm)], [f_37])).
% 45.62/34.09  tff(c_83533, plain, (![A_817]: (r1_tarski(A_817, u1_struct_0('#skF_1')) | ~r1_tarski(A_817, '#skF_2'))), inference(resolution, [status(thm)], [c_47, c_83526])).
% 45.62/34.09  tff(c_83538, plain, (![A_3, A_817]: (r1_tarski(A_3, u1_struct_0('#skF_1')) | ~r1_tarski(A_3, A_817) | ~r1_tarski(A_817, '#skF_2'))), inference(resolution, [status(thm)], [c_83533, c_8])).
% 45.62/34.09  tff(c_83562, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_2'), u1_struct_0('#skF_1')) | ~r1_tarski('#skF_2', '#skF_2')), inference(resolution, [status(thm)], [c_83560, c_83538])).
% 45.62/34.09  tff(c_83569, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_2'), u1_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_83562])).
% 45.62/34.09  tff(c_83917, plain, (![A_849, A_850]: (k2_pre_topc(A_849, k2_pre_topc(A_849, A_850))=k2_pre_topc(A_849, A_850) | ~l1_pre_topc(A_849) | ~r1_tarski(A_850, u1_struct_0(A_849)))), inference(resolution, [status(thm)], [c_12, c_83760])).
% 45.62/34.09  tff(c_83928, plain, (k2_pre_topc('#skF_1', k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2')))=k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2')) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_83569, c_83917])).
% 45.62/34.09  tff(c_83944, plain, (k2_pre_topc('#skF_1', k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2')))=k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_83928])).
% 45.62/34.09  tff(c_84759, plain, (![A_875, B_876, C_877]: (r1_tarski(k2_pre_topc(A_875, B_876), k2_pre_topc(A_875, C_877)) | ~r1_tarski(B_876, C_877) | ~m1_subset_1(C_877, k1_zfmisc_1(u1_struct_0(A_875))) | ~m1_subset_1(B_876, k1_zfmisc_1(u1_struct_0(A_875))) | ~l1_pre_topc(A_875))), inference(cnfTransformation, [status(thm)], [f_65])).
% 45.62/34.09  tff(c_90953, plain, (![A_1019, A_1020, C_1021, B_1022]: (r1_tarski(A_1019, k2_pre_topc(A_1020, C_1021)) | ~r1_tarski(A_1019, k2_pre_topc(A_1020, B_1022)) | ~r1_tarski(B_1022, C_1021) | ~m1_subset_1(C_1021, k1_zfmisc_1(u1_struct_0(A_1020))) | ~m1_subset_1(B_1022, k1_zfmisc_1(u1_struct_0(A_1020))) | ~l1_pre_topc(A_1020))), inference(resolution, [status(thm)], [c_84759, c_8])).
% 45.62/34.09  tff(c_90993, plain, (![C_1021]: (r1_tarski(k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_2')), k2_pre_topc('#skF_1', C_1021)) | ~r1_tarski('#skF_2', C_1021) | ~m1_subset_1(C_1021, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_84276, c_90953])).
% 45.62/34.09  tff(c_94475, plain, (![C_1069]: (r1_tarski(k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_2')), k2_pre_topc('#skF_1', C_1069)) | ~r1_tarski('#skF_2', C_1069) | ~m1_subset_1(C_1069, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_90993])).
% 45.62/34.09  tff(c_94534, plain, (r1_tarski(k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_2')), k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2'))) | ~r1_tarski('#skF_2', k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2'))) | ~m1_subset_1(k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2')), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_83944, c_94475])).
% 45.62/34.09  tff(c_94588, plain, (r1_tarski(k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_2')), k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2'))) | ~r1_tarski('#skF_2', k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_89462, c_94534])).
% 45.62/34.09  tff(c_96932, plain, (~r1_tarski('#skF_2', k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2')))), inference(splitLeft, [status(thm)], [c_94588])).
% 45.62/34.09  tff(c_97240, plain, (~r1_tarski('#skF_2', '#skF_2') | ~v4_tops_1('#skF_2', '#skF_1') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_84349, c_96932])).
% 45.62/34.09  tff(c_97265, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_36, c_6, c_97240])).
% 45.62/34.09  tff(c_97267, plain, (r1_tarski('#skF_2', k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2')))), inference(splitRight, [status(thm)], [c_94588])).
% 45.62/34.09  tff(c_84793, plain, (![B_876]: (r1_tarski(k2_pre_topc('#skF_1', B_876), k2_pre_topc('#skF_1', '#skF_2')) | ~r1_tarski(B_876, k2_pre_topc('#skF_1', '#skF_2')) | ~m1_subset_1(k2_pre_topc('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1(B_876, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_83775, c_84759])).
% 45.62/34.09  tff(c_84811, plain, (![B_876]: (r1_tarski(k2_pre_topc('#skF_1', B_876), k2_pre_topc('#skF_1', '#skF_2')) | ~r1_tarski(B_876, k2_pre_topc('#skF_1', '#skF_2')) | ~m1_subset_1(B_876, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_84277, c_84793])).
% 45.62/34.09  tff(c_92800, plain, (![A_1044, C_1045, B_1046]: (k2_pre_topc(A_1044, C_1045)=k2_pre_topc(A_1044, B_1046) | ~r1_tarski(k2_pre_topc(A_1044, C_1045), k2_pre_topc(A_1044, B_1046)) | ~r1_tarski(B_1046, C_1045) | ~m1_subset_1(C_1045, k1_zfmisc_1(u1_struct_0(A_1044))) | ~m1_subset_1(B_1046, k1_zfmisc_1(u1_struct_0(A_1044))) | ~l1_pre_topc(A_1044))), inference(resolution, [status(thm)], [c_84759, c_2])).
% 45.62/34.09  tff(c_92851, plain, (![B_876]: (k2_pre_topc('#skF_1', B_876)=k2_pre_topc('#skF_1', '#skF_2') | ~r1_tarski('#skF_2', B_876) | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1') | ~r1_tarski(B_876, k2_pre_topc('#skF_1', '#skF_2')) | ~m1_subset_1(B_876, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(resolution, [status(thm)], [c_84811, c_92800])).
% 45.62/34.09  tff(c_154960, plain, (![B_1487]: (k2_pre_topc('#skF_1', B_1487)=k2_pre_topc('#skF_1', '#skF_2') | ~r1_tarski('#skF_2', B_1487) | ~r1_tarski(B_1487, k2_pre_topc('#skF_1', '#skF_2')) | ~m1_subset_1(B_1487, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_92851])).
% 45.62/34.09  tff(c_154972, plain, (k2_pre_topc('#skF_1', k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2')))=k2_pre_topc('#skF_1', '#skF_2') | ~r1_tarski('#skF_2', k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2'))) | ~r1_tarski(k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2')), k2_pre_topc('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_89462, c_154960])).
% 45.62/34.09  tff(c_155008, plain, (k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_90593, c_97267, c_83944, c_154972])).
% 45.62/34.09  tff(c_89505, plain, (r1_tarski(k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2')), u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_89462, c_10])).
% 45.62/34.09  tff(c_84281, plain, (k1_tops_1('#skF_1', k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_2')))=k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_2')) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_84277, c_28])).
% 45.62/34.09  tff(c_84292, plain, (k1_tops_1('#skF_1', k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_2')))=k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_84281])).
% 45.62/34.09  tff(c_87854, plain, (![A_950, B_951, A_952]: (r1_tarski(A_950, B_951) | ~r1_tarski(A_950, k1_tops_1(A_952, k2_pre_topc(A_952, B_951))) | ~v4_tops_1(B_951, A_952) | ~m1_subset_1(B_951, k1_zfmisc_1(u1_struct_0(A_952))) | ~l1_pre_topc(A_952))), inference(resolution, [status(thm)], [c_84075, c_8])).
% 45.62/34.09  tff(c_118330, plain, (![A_1258, B_1259]: (r1_tarski(k1_tops_1(A_1258, k1_tops_1(A_1258, k2_pre_topc(A_1258, B_1259))), B_1259) | ~v4_tops_1(B_1259, A_1258) | ~m1_subset_1(B_1259, k1_zfmisc_1(u1_struct_0(A_1258))) | ~m1_subset_1(k2_pre_topc(A_1258, B_1259), k1_zfmisc_1(u1_struct_0(A_1258))) | ~l1_pre_topc(A_1258))), inference(resolution, [status(thm)], [c_83635, c_87854])).
% 45.62/34.09  tff(c_118570, plain, (r1_tarski(k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_2')), '#skF_2') | ~v4_tops_1('#skF_2', '#skF_1') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1(k2_pre_topc('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_84292, c_118330])).
% 45.62/34.09  tff(c_118664, plain, (r1_tarski(k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_2')), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_84277, c_38, c_36, c_118570])).
% 45.62/34.09  tff(c_118766, plain, (![A_1260]: (r1_tarski(A_1260, '#skF_2') | ~r1_tarski(A_1260, k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_2'))))), inference(resolution, [status(thm)], [c_118664, c_8])).
% 45.62/34.09  tff(c_118804, plain, (![B_33]: (r1_tarski(k1_tops_1('#skF_1', B_33), '#skF_2') | ~r1_tarski(B_33, k2_pre_topc('#skF_1', '#skF_2')) | ~m1_subset_1(k2_pre_topc('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1(B_33, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_32, c_118766])).
% 45.62/34.09  tff(c_119444, plain, (![B_1266]: (r1_tarski(k1_tops_1('#skF_1', B_1266), '#skF_2') | ~r1_tarski(B_1266, k2_pre_topc('#skF_1', '#skF_2')) | ~m1_subset_1(B_1266, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_84277, c_118804])).
% 45.62/34.09  tff(c_119502, plain, (![A_1267]: (r1_tarski(k1_tops_1('#skF_1', A_1267), '#skF_2') | ~r1_tarski(A_1267, k2_pre_topc('#skF_1', '#skF_2')) | ~r1_tarski(A_1267, u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_12, c_119444])).
% 45.62/34.09  tff(c_97339, plain, (![A_1098]: (r1_tarski(A_1098, k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2'))) | ~r1_tarski(A_1098, '#skF_2'))), inference(resolution, [status(thm)], [c_97267, c_8])).
% 45.62/34.09  tff(c_97468, plain, (![A_3, A_1098]: (r1_tarski(A_3, k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2'))) | ~r1_tarski(A_3, A_1098) | ~r1_tarski(A_1098, '#skF_2'))), inference(resolution, [status(thm)], [c_97339, c_8])).
% 45.62/34.09  tff(c_119534, plain, (![A_1267]: (r1_tarski(k1_tops_1('#skF_1', A_1267), k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2'))) | ~r1_tarski('#skF_2', '#skF_2') | ~r1_tarski(A_1267, k2_pre_topc('#skF_1', '#skF_2')) | ~r1_tarski(A_1267, u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_119502, c_97468])).
% 45.62/34.09  tff(c_126183, plain, (![A_1322]: (r1_tarski(k1_tops_1('#skF_1', A_1322), k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2'))) | ~r1_tarski(A_1322, k2_pre_topc('#skF_1', '#skF_2')) | ~r1_tarski(A_1322, u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_119534])).
% 45.62/34.09  tff(c_126254, plain, (v4_tops_1(k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2')), '#skF_1') | ~r1_tarski(k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2')), k2_pre_topc('#skF_1', k1_tops_1('#skF_1', k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2'))))) | ~m1_subset_1(k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2')), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1') | ~r1_tarski(k2_pre_topc('#skF_1', k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2'))), k2_pre_topc('#skF_1', '#skF_2')) | ~r1_tarski(k2_pre_topc('#skF_1', k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2'))), u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_126183, c_20])).
% 45.62/34.09  tff(c_126362, plain, (v4_tops_1(k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2')), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_89505, c_83944, c_90593, c_83944, c_40, c_89462, c_6, c_90114, c_126254])).
% 45.62/34.09  tff(c_155284, plain, (v4_tops_1(k2_pre_topc('#skF_1', '#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_155008, c_126362])).
% 45.62/34.09  tff(c_155316, plain, $false, inference(negUnitSimplification, [status(thm)], [c_83524, c_155284])).
% 45.62/34.09  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 45.62/34.09  
% 45.62/34.09  Inference rules
% 45.62/34.09  ----------------------
% 45.62/34.09  #Ref     : 0
% 45.62/34.09  #Sup     : 35385
% 45.62/34.09  #Fact    : 0
% 45.62/34.09  #Define  : 0
% 45.62/34.09  #Split   : 76
% 45.62/34.09  #Chain   : 0
% 45.62/34.09  #Close   : 0
% 45.62/34.09  
% 45.62/34.09  Ordering : KBO
% 45.62/34.09  
% 45.62/34.09  Simplification rules
% 45.62/34.09  ----------------------
% 45.62/34.09  #Subsume      : 16232
% 45.62/34.09  #Demod        : 34319
% 45.62/34.09  #Tautology    : 5032
% 45.62/34.09  #SimpNegUnit  : 256
% 45.62/34.09  #BackRed      : 126
% 45.62/34.09  
% 45.62/34.09  #Partial instantiations: 0
% 45.62/34.09  #Strategies tried      : 1
% 45.62/34.09  
% 45.62/34.09  Timing (in seconds)
% 45.62/34.09  ----------------------
% 45.62/34.09  Preprocessing        : 0.34
% 45.62/34.09  Parsing              : 0.19
% 45.62/34.09  CNF conversion       : 0.03
% 45.62/34.09  Main loop            : 32.80
% 45.62/34.09  Inferencing          : 3.41
% 45.62/34.09  Reduction            : 8.08
% 45.62/34.09  Demodulation         : 6.17
% 45.62/34.09  BG Simplification    : 0.40
% 45.62/34.09  Subsumption          : 19.83
% 45.62/34.09  Abstraction          : 0.77
% 45.62/34.09  MUC search           : 0.00
% 45.62/34.09  Cooper               : 0.00
% 45.62/34.09  Total                : 33.23
% 45.62/34.09  Index Insertion      : 0.00
% 45.62/34.09  Index Deletion       : 0.00
% 45.62/34.09  Index Matching       : 0.00
% 45.62/34.09  BG Taut test         : 0.00
%------------------------------------------------------------------------------
