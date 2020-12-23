%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:22:28 EST 2020

% Result     : Theorem 28.60s
% Output     : CNFRefutation 28.88s
% Verified   : 
% Statistics : Number of formulae       :  270 (6961 expanded)
%              Number of leaves         :   25 (2365 expanded)
%              Depth                    :   24
%              Number of atoms          :  754 (20471 expanded)
%              Number of equality atoms :   53 (1607 expanded)
%              Maximal formula depth    :   12 (   5 average)
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

tff(f_119,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v4_tops_1(B,A)
             => ( v4_tops_1(k1_tops_1(A,B),A)
                & v4_tops_1(k2_pre_topc(A,B),A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t111_tops_1)).

tff(f_89,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k1_tops_1(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_tops_1)).

tff(f_95,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => k1_tops_1(A,k1_tops_1(A,B)) = k1_tops_1(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',projectivity_k1_tops_1)).

tff(f_60,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => r1_tarski(B,k2_pre_topc(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_pre_topc)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_41,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_47,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_pre_topc(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_pre_topc)).

tff(f_53,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => k2_pre_topc(A,k2_pre_topc(A,B)) = k2_pre_topc(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',projectivity_k2_pre_topc)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_107,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( r1_tarski(B,C)
               => r1_tarski(k1_tops_1(A,B),k1_tops_1(A,C)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_tops_1)).

tff(f_83,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v4_tops_1(B,A)
          <=> ( r1_tarski(k1_tops_1(A,k2_pre_topc(A,B)),B)
              & r1_tarski(B,k2_pre_topc(A,k1_tops_1(A,B))) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_tops_1)).

tff(f_72,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( r1_tarski(B,C)
               => r1_tarski(k2_pre_topc(A,B),k2_pre_topc(A,C)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_pre_topc)).

tff(c_40,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_38,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_28,plain,(
    ! [A_25,B_26] :
      ( m1_subset_1(k1_tops_1(A_25,B_26),k1_zfmisc_1(u1_struct_0(A_25)))
      | ~ m1_subset_1(B_26,k1_zfmisc_1(u1_struct_0(A_25)))
      | ~ l1_pre_topc(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_426,plain,(
    ! [A_81,B_82] :
      ( k1_tops_1(A_81,k1_tops_1(A_81,B_82)) = k1_tops_1(A_81,B_82)
      | ~ m1_subset_1(B_82,k1_zfmisc_1(u1_struct_0(A_81)))
      | ~ l1_pre_topc(A_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_435,plain,
    ( k1_tops_1('#skF_1',k1_tops_1('#skF_1','#skF_2')) = k1_tops_1('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_38,c_426])).

tff(c_441,plain,(
    k1_tops_1('#skF_1',k1_tops_1('#skF_1','#skF_2')) = k1_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_435])).

tff(c_194,plain,(
    ! [A_59,B_60] :
      ( m1_subset_1(k1_tops_1(A_59,B_60),k1_zfmisc_1(u1_struct_0(A_59)))
      | ~ m1_subset_1(B_60,k1_zfmisc_1(u1_struct_0(A_59)))
      | ~ l1_pre_topc(A_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_18,plain,(
    ! [B_14,A_12] :
      ( r1_tarski(B_14,k2_pre_topc(A_12,B_14))
      | ~ m1_subset_1(B_14,k1_zfmisc_1(u1_struct_0(A_12)))
      | ~ l1_pre_topc(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_1458,plain,(
    ! [A_121,B_122] :
      ( r1_tarski(k1_tops_1(A_121,B_122),k2_pre_topc(A_121,k1_tops_1(A_121,B_122)))
      | ~ m1_subset_1(B_122,k1_zfmisc_1(u1_struct_0(A_121)))
      | ~ l1_pre_topc(A_121) ) ),
    inference(resolution,[status(thm)],[c_194,c_18])).

tff(c_1487,plain,
    ( r1_tarski(k1_tops_1('#skF_1','#skF_2'),k2_pre_topc('#skF_1',k1_tops_1('#skF_1',k1_tops_1('#skF_1','#skF_2'))))
    | ~ m1_subset_1(k1_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_441,c_1458])).

tff(c_1503,plain,
    ( r1_tarski(k1_tops_1('#skF_1','#skF_2'),k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')))
    | ~ m1_subset_1(k1_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_441,c_1487])).

tff(c_1611,plain,(
    ~ m1_subset_1(k1_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_1503])).

tff(c_1627,plain,
    ( ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_28,c_1611])).

tff(c_1634,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_1627])).

tff(c_1636,plain,(
    m1_subset_1(k1_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_1503])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_12,plain,(
    ! [A_6,B_7] :
      ( m1_subset_1(A_6,k1_zfmisc_1(B_7))
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_202,plain,(
    ! [A_61,B_62] :
      ( m1_subset_1(k2_pre_topc(A_61,B_62),k1_zfmisc_1(u1_struct_0(A_61)))
      | ~ m1_subset_1(B_62,k1_zfmisc_1(u1_struct_0(A_61)))
      | ~ l1_pre_topc(A_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_10,plain,(
    ! [A_6,B_7] :
      ( r1_tarski(A_6,B_7)
      | ~ m1_subset_1(A_6,k1_zfmisc_1(B_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_209,plain,(
    ! [A_61,B_62] :
      ( r1_tarski(k2_pre_topc(A_61,B_62),u1_struct_0(A_61))
      | ~ m1_subset_1(B_62,k1_zfmisc_1(u1_struct_0(A_61)))
      | ~ l1_pre_topc(A_61) ) ),
    inference(resolution,[status(thm)],[c_202,c_10])).

tff(c_90,plain,(
    ! [B_50,A_51] :
      ( r1_tarski(B_50,k2_pre_topc(A_51,B_50))
      | ~ m1_subset_1(B_50,k1_zfmisc_1(u1_struct_0(A_51)))
      | ~ l1_pre_topc(A_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_137,plain,(
    ! [A_54,A_55] :
      ( r1_tarski(A_54,k2_pre_topc(A_55,A_54))
      | ~ l1_pre_topc(A_55)
      | ~ r1_tarski(A_54,u1_struct_0(A_55)) ) ),
    inference(resolution,[status(thm)],[c_12,c_90])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_759,plain,(
    ! [A_95,A_96] :
      ( k2_pre_topc(A_95,A_96) = A_96
      | ~ r1_tarski(k2_pre_topc(A_95,A_96),A_96)
      | ~ l1_pre_topc(A_95)
      | ~ r1_tarski(A_96,u1_struct_0(A_95)) ) ),
    inference(resolution,[status(thm)],[c_137,c_2])).

tff(c_780,plain,(
    ! [A_61] :
      ( k2_pre_topc(A_61,u1_struct_0(A_61)) = u1_struct_0(A_61)
      | ~ r1_tarski(u1_struct_0(A_61),u1_struct_0(A_61))
      | ~ m1_subset_1(u1_struct_0(A_61),k1_zfmisc_1(u1_struct_0(A_61)))
      | ~ l1_pre_topc(A_61) ) ),
    inference(resolution,[status(thm)],[c_209,c_759])).

tff(c_802,plain,(
    ! [A_97] :
      ( k2_pre_topc(A_97,u1_struct_0(A_97)) = u1_struct_0(A_97)
      | ~ m1_subset_1(u1_struct_0(A_97),k1_zfmisc_1(u1_struct_0(A_97)))
      | ~ l1_pre_topc(A_97) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_780])).

tff(c_805,plain,(
    ! [A_97] :
      ( k2_pre_topc(A_97,u1_struct_0(A_97)) = u1_struct_0(A_97)
      | ~ l1_pre_topc(A_97)
      | ~ r1_tarski(u1_struct_0(A_97),u1_struct_0(A_97)) ) ),
    inference(resolution,[status(thm)],[c_12,c_802])).

tff(c_808,plain,(
    ! [A_97] :
      ( k2_pre_topc(A_97,u1_struct_0(A_97)) = u1_struct_0(A_97)
      | ~ l1_pre_topc(A_97) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_805])).

tff(c_1506,plain,(
    ! [A_123,B_124] :
      ( r1_tarski(k2_pre_topc(A_123,B_124),k2_pre_topc(A_123,k2_pre_topc(A_123,B_124)))
      | ~ m1_subset_1(B_124,k1_zfmisc_1(u1_struct_0(A_123)))
      | ~ l1_pre_topc(A_123) ) ),
    inference(resolution,[status(thm)],[c_202,c_18])).

tff(c_1543,plain,(
    ! [A_97] :
      ( r1_tarski(u1_struct_0(A_97),k2_pre_topc(A_97,k2_pre_topc(A_97,u1_struct_0(A_97))))
      | ~ m1_subset_1(u1_struct_0(A_97),k1_zfmisc_1(u1_struct_0(A_97)))
      | ~ l1_pre_topc(A_97)
      | ~ l1_pre_topc(A_97) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_808,c_1506])).

tff(c_14,plain,(
    ! [A_8,B_9] :
      ( m1_subset_1(k2_pre_topc(A_8,B_9),k1_zfmisc_1(u1_struct_0(A_8)))
      | ~ m1_subset_1(B_9,k1_zfmisc_1(u1_struct_0(A_8)))
      | ~ l1_pre_topc(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_410,plain,(
    ! [A_79,B_80] :
      ( k2_pre_topc(A_79,k2_pre_topc(A_79,B_80)) = k2_pre_topc(A_79,B_80)
      | ~ m1_subset_1(B_80,k1_zfmisc_1(u1_struct_0(A_79)))
      | ~ l1_pre_topc(A_79) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_2281,plain,(
    ! [A_143,B_144] :
      ( k2_pre_topc(A_143,k2_pre_topc(A_143,k2_pre_topc(A_143,B_144))) = k2_pre_topc(A_143,k2_pre_topc(A_143,B_144))
      | ~ m1_subset_1(B_144,k1_zfmisc_1(u1_struct_0(A_143)))
      | ~ l1_pre_topc(A_143) ) ),
    inference(resolution,[status(thm)],[c_14,c_410])).

tff(c_2298,plain,(
    ! [A_143,A_6] :
      ( k2_pre_topc(A_143,k2_pre_topc(A_143,k2_pre_topc(A_143,A_6))) = k2_pre_topc(A_143,k2_pre_topc(A_143,A_6))
      | ~ l1_pre_topc(A_143)
      | ~ r1_tarski(A_6,u1_struct_0(A_143)) ) ),
    inference(resolution,[status(thm)],[c_12,c_2281])).

tff(c_1655,plain,(
    r1_tarski(k1_tops_1('#skF_1','#skF_2'),u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_1636,c_10])).

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

tff(c_70,plain,(
    ! [A_44] :
      ( r1_tarski(A_44,u1_struct_0('#skF_1'))
      | ~ r1_tarski(A_44,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_47,c_65])).

tff(c_8,plain,(
    ! [A_3,C_5,B_4] :
      ( r1_tarski(A_3,C_5)
      | ~ r1_tarski(B_4,C_5)
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_243,plain,(
    ! [A_67,A_68,A_69] :
      ( r1_tarski(A_67,k2_pre_topc(A_68,A_69))
      | ~ r1_tarski(A_67,A_69)
      | ~ l1_pre_topc(A_68)
      | ~ r1_tarski(A_69,u1_struct_0(A_68)) ) ),
    inference(resolution,[status(thm)],[c_137,c_8])).

tff(c_249,plain,(
    ! [A_67,A_44] :
      ( r1_tarski(A_67,k2_pre_topc('#skF_1',A_44))
      | ~ r1_tarski(A_67,A_44)
      | ~ l1_pre_topc('#skF_1')
      | ~ r1_tarski(A_44,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_70,c_243])).

tff(c_264,plain,(
    ! [A_70,A_71] :
      ( r1_tarski(A_70,k2_pre_topc('#skF_1',A_71))
      | ~ r1_tarski(A_70,A_71)
      | ~ r1_tarski(A_71,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_249])).

tff(c_285,plain,(
    ! [A_3,A_71,A_70] :
      ( r1_tarski(A_3,k2_pre_topc('#skF_1',A_71))
      | ~ r1_tarski(A_3,A_70)
      | ~ r1_tarski(A_70,A_71)
      | ~ r1_tarski(A_71,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_264,c_8])).

tff(c_2014,plain,(
    ! [A_136] :
      ( r1_tarski(k1_tops_1('#skF_1','#skF_2'),k2_pre_topc('#skF_1',A_136))
      | ~ r1_tarski(u1_struct_0('#skF_1'),A_136)
      | ~ r1_tarski(A_136,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_1655,c_285])).

tff(c_95,plain,
    ( r1_tarski('#skF_2',k2_pre_topc('#skF_1','#skF_2'))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_38,c_90])).

tff(c_99,plain,(
    r1_tarski('#skF_2',k2_pre_topc('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_95])).

tff(c_110,plain,(
    ! [A_52] :
      ( r1_tarski(A_52,k2_pre_topc('#skF_1','#skF_2'))
      | ~ r1_tarski(A_52,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_99,c_8])).

tff(c_118,plain,(
    ! [A_3,A_52] :
      ( r1_tarski(A_3,k2_pre_topc('#skF_1','#skF_2'))
      | ~ r1_tarski(A_3,A_52)
      | ~ r1_tarski(A_52,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_110,c_8])).

tff(c_2049,plain,(
    ! [A_136] :
      ( r1_tarski(k1_tops_1('#skF_1','#skF_2'),k2_pre_topc('#skF_1','#skF_2'))
      | ~ r1_tarski(k2_pre_topc('#skF_1',A_136),'#skF_2')
      | ~ r1_tarski(u1_struct_0('#skF_1'),A_136)
      | ~ r1_tarski(A_136,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_2014,c_118])).

tff(c_13874,plain,(
    ! [A_359] :
      ( ~ r1_tarski(k2_pre_topc('#skF_1',A_359),'#skF_2')
      | ~ r1_tarski(u1_struct_0('#skF_1'),A_359)
      | ~ r1_tarski(A_359,'#skF_2') ) ),
    inference(splitLeft,[status(thm)],[c_2049])).

tff(c_13882,plain,(
    ! [A_6] :
      ( ~ r1_tarski(k2_pre_topc('#skF_1',k2_pre_topc('#skF_1',A_6)),'#skF_2')
      | ~ r1_tarski(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1',k2_pre_topc('#skF_1',A_6)))
      | ~ r1_tarski(k2_pre_topc('#skF_1',k2_pre_topc('#skF_1',A_6)),'#skF_2')
      | ~ l1_pre_topc('#skF_1')
      | ~ r1_tarski(A_6,u1_struct_0('#skF_1')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2298,c_13874])).

tff(c_14900,plain,(
    ! [A_375] :
      ( ~ r1_tarski(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1',k2_pre_topc('#skF_1',A_375)))
      | ~ r1_tarski(k2_pre_topc('#skF_1',k2_pre_topc('#skF_1',A_375)),'#skF_2')
      | ~ r1_tarski(A_375,u1_struct_0('#skF_1')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_13882])).

tff(c_14912,plain,
    ( ~ r1_tarski(k2_pre_topc('#skF_1',k2_pre_topc('#skF_1',u1_struct_0('#skF_1'))),'#skF_2')
    | ~ r1_tarski(u1_struct_0('#skF_1'),u1_struct_0('#skF_1'))
    | ~ m1_subset_1(u1_struct_0('#skF_1'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_1543,c_14900])).

tff(c_14994,plain,
    ( ~ r1_tarski(k2_pre_topc('#skF_1',k2_pre_topc('#skF_1',u1_struct_0('#skF_1'))),'#skF_2')
    | ~ m1_subset_1(u1_struct_0('#skF_1'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_6,c_14912])).

tff(c_15031,plain,(
    ~ m1_subset_1(u1_struct_0('#skF_1'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_14994])).

tff(c_15034,plain,(
    ~ r1_tarski(u1_struct_0('#skF_1'),u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_12,c_15031])).

tff(c_15038,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_15034])).

tff(c_15040,plain,(
    m1_subset_1(u1_struct_0('#skF_1'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_14994])).

tff(c_32,plain,(
    ! [A_29,B_33,C_35] :
      ( r1_tarski(k1_tops_1(A_29,B_33),k1_tops_1(A_29,C_35))
      | ~ r1_tarski(B_33,C_35)
      | ~ m1_subset_1(C_35,k1_zfmisc_1(u1_struct_0(A_29)))
      | ~ m1_subset_1(B_33,k1_zfmisc_1(u1_struct_0(A_29)))
      | ~ l1_pre_topc(A_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_1716,plain,(
    ! [A_127,B_128,C_129] :
      ( r1_tarski(k1_tops_1(A_127,B_128),k1_tops_1(A_127,C_129))
      | ~ r1_tarski(B_128,C_129)
      | ~ m1_subset_1(C_129,k1_zfmisc_1(u1_struct_0(A_127)))
      | ~ m1_subset_1(B_128,k1_zfmisc_1(u1_struct_0(A_127)))
      | ~ l1_pre_topc(A_127) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_5019,plain,(
    ! [A_223,A_224,C_225,B_226] :
      ( r1_tarski(A_223,k1_tops_1(A_224,C_225))
      | ~ r1_tarski(A_223,k1_tops_1(A_224,B_226))
      | ~ r1_tarski(B_226,C_225)
      | ~ m1_subset_1(C_225,k1_zfmisc_1(u1_struct_0(A_224)))
      | ~ m1_subset_1(B_226,k1_zfmisc_1(u1_struct_0(A_224)))
      | ~ l1_pre_topc(A_224) ) ),
    inference(resolution,[status(thm)],[c_1716,c_8])).

tff(c_28099,plain,(
    ! [A_518,B_519,C_520,C_521] :
      ( r1_tarski(k1_tops_1(A_518,B_519),k1_tops_1(A_518,C_520))
      | ~ r1_tarski(C_521,C_520)
      | ~ m1_subset_1(C_520,k1_zfmisc_1(u1_struct_0(A_518)))
      | ~ r1_tarski(B_519,C_521)
      | ~ m1_subset_1(C_521,k1_zfmisc_1(u1_struct_0(A_518)))
      | ~ m1_subset_1(B_519,k1_zfmisc_1(u1_struct_0(A_518)))
      | ~ l1_pre_topc(A_518) ) ),
    inference(resolution,[status(thm)],[c_32,c_5019])).

tff(c_28341,plain,(
    ! [A_522,B_523] :
      ( r1_tarski(k1_tops_1(A_522,B_523),k1_tops_1(A_522,u1_struct_0('#skF_1')))
      | ~ m1_subset_1(u1_struct_0('#skF_1'),k1_zfmisc_1(u1_struct_0(A_522)))
      | ~ r1_tarski(B_523,'#skF_2')
      | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0(A_522)))
      | ~ m1_subset_1(B_523,k1_zfmisc_1(u1_struct_0(A_522)))
      | ~ l1_pre_topc(A_522) ) ),
    inference(resolution,[status(thm)],[c_47,c_28099])).

tff(c_28458,plain,
    ( r1_tarski(k1_tops_1('#skF_1','#skF_2'),k1_tops_1('#skF_1',u1_struct_0('#skF_1')))
    | ~ m1_subset_1(u1_struct_0('#skF_1'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ r1_tarski(k1_tops_1('#skF_1','#skF_2'),'#skF_2')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_subset_1(k1_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_441,c_28341])).

tff(c_28517,plain,
    ( r1_tarski(k1_tops_1('#skF_1','#skF_2'),k1_tops_1('#skF_1',u1_struct_0('#skF_1')))
    | ~ r1_tarski(k1_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_1636,c_38,c_15040,c_28458])).

tff(c_28518,plain,(
    ~ r1_tarski(k1_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_28517])).

tff(c_419,plain,
    ( k2_pre_topc('#skF_1',k2_pre_topc('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_38,c_410])).

tff(c_425,plain,(
    k2_pre_topc('#skF_1',k2_pre_topc('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_419])).

tff(c_223,plain,(
    ! [A_65,B_66] :
      ( r1_tarski(k2_pre_topc(A_65,B_66),u1_struct_0(A_65))
      | ~ m1_subset_1(B_66,k1_zfmisc_1(u1_struct_0(A_65)))
      | ~ l1_pre_topc(A_65) ) ),
    inference(resolution,[status(thm)],[c_202,c_10])).

tff(c_2400,plain,(
    ! [A_149,A_150,B_151] :
      ( r1_tarski(A_149,u1_struct_0(A_150))
      | ~ r1_tarski(A_149,k2_pre_topc(A_150,B_151))
      | ~ m1_subset_1(B_151,k1_zfmisc_1(u1_struct_0(A_150)))
      | ~ l1_pre_topc(A_150) ) ),
    inference(resolution,[status(thm)],[c_223,c_8])).

tff(c_2435,plain,(
    ! [A_149] :
      ( r1_tarski(A_149,u1_struct_0('#skF_1'))
      | ~ r1_tarski(A_149,k2_pre_topc('#skF_1','#skF_2'))
      | ~ m1_subset_1(k2_pre_topc('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_425,c_2400])).

tff(c_2478,plain,(
    ! [A_149] :
      ( r1_tarski(A_149,u1_struct_0('#skF_1'))
      | ~ r1_tarski(A_149,k2_pre_topc('#skF_1','#skF_2'))
      | ~ m1_subset_1(k2_pre_topc('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_2435])).

tff(c_2491,plain,(
    ~ m1_subset_1(k2_pre_topc('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_2478])).

tff(c_2494,plain,
    ( ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_14,c_2491])).

tff(c_2501,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_2494])).

tff(c_2503,plain,(
    m1_subset_1(k2_pre_topc('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_2478])).

tff(c_36,plain,(
    v4_tops_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_26,plain,(
    ! [A_22,B_24] :
      ( r1_tarski(k1_tops_1(A_22,k2_pre_topc(A_22,B_24)),B_24)
      | ~ v4_tops_1(B_24,A_22)
      | ~ m1_subset_1(B_24,k1_zfmisc_1(u1_struct_0(A_22)))
      | ~ l1_pre_topc(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_2504,plain,(
    ! [A_152,B_153] :
      ( k1_tops_1(A_152,k1_tops_1(A_152,k2_pre_topc(A_152,B_153))) = k1_tops_1(A_152,k2_pre_topc(A_152,B_153))
      | ~ m1_subset_1(B_153,k1_zfmisc_1(u1_struct_0(A_152)))
      | ~ l1_pre_topc(A_152) ) ),
    inference(resolution,[status(thm)],[c_14,c_426])).

tff(c_2515,plain,
    ( k1_tops_1('#skF_1',k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2'))) = k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2'))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_38,c_2504])).

tff(c_2524,plain,(
    k1_tops_1('#skF_1',k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2'))) = k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_2515])).

tff(c_1748,plain,(
    ! [B_128] :
      ( r1_tarski(k1_tops_1('#skF_1',B_128),k1_tops_1('#skF_1','#skF_2'))
      | ~ r1_tarski(B_128,k1_tops_1('#skF_1','#skF_2'))
      | ~ m1_subset_1(k1_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ m1_subset_1(B_128,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_441,c_1716])).

tff(c_3679,plain,(
    ! [B_184] :
      ( r1_tarski(k1_tops_1('#skF_1',B_184),k1_tops_1('#skF_1','#skF_2'))
      | ~ r1_tarski(B_184,k1_tops_1('#skF_1','#skF_2'))
      | ~ m1_subset_1(B_184,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_1636,c_1748])).

tff(c_210,plain,(
    ! [A_63,B_64] :
      ( r1_tarski(k1_tops_1(A_63,B_64),u1_struct_0(A_63))
      | ~ m1_subset_1(B_64,k1_zfmisc_1(u1_struct_0(A_63)))
      | ~ l1_pre_topc(A_63) ) ),
    inference(resolution,[status(thm)],[c_194,c_10])).

tff(c_221,plain,(
    ! [A_3,A_63,B_64] :
      ( r1_tarski(A_3,u1_struct_0(A_63))
      | ~ r1_tarski(A_3,k1_tops_1(A_63,B_64))
      | ~ m1_subset_1(B_64,k1_zfmisc_1(u1_struct_0(A_63)))
      | ~ l1_pre_topc(A_63) ) ),
    inference(resolution,[status(thm)],[c_210,c_8])).

tff(c_3683,plain,(
    ! [B_184] :
      ( r1_tarski(k1_tops_1('#skF_1',B_184),u1_struct_0('#skF_1'))
      | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1')
      | ~ r1_tarski(B_184,k1_tops_1('#skF_1','#skF_2'))
      | ~ m1_subset_1(B_184,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(resolution,[status(thm)],[c_3679,c_221])).

tff(c_3746,plain,(
    ! [B_185] :
      ( r1_tarski(k1_tops_1('#skF_1',B_185),u1_struct_0('#skF_1'))
      | ~ r1_tarski(B_185,k1_tops_1('#skF_1','#skF_2'))
      | ~ m1_subset_1(B_185,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_3683])).

tff(c_10460,plain,(
    ! [A_322,B_323] :
      ( r1_tarski(A_322,u1_struct_0('#skF_1'))
      | ~ r1_tarski(A_322,k1_tops_1('#skF_1',B_323))
      | ~ r1_tarski(B_323,k1_tops_1('#skF_1','#skF_2'))
      | ~ m1_subset_1(B_323,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(resolution,[status(thm)],[c_3746,c_8])).

tff(c_10480,plain,(
    ! [A_322] :
      ( r1_tarski(A_322,u1_struct_0('#skF_1'))
      | ~ r1_tarski(A_322,k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2')))
      | ~ r1_tarski(k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2')),k1_tops_1('#skF_1','#skF_2'))
      | ~ m1_subset_1(k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2')),k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2524,c_10460])).

tff(c_10519,plain,(
    ~ m1_subset_1(k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2')),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_10480])).

tff(c_10522,plain,
    ( ~ m1_subset_1(k2_pre_topc('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_28,c_10519])).

tff(c_10529,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_2503,c_10522])).

tff(c_10531,plain,(
    m1_subset_1(k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2')),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_10480])).

tff(c_28449,plain,
    ( r1_tarski(k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2')),k1_tops_1('#skF_1',u1_struct_0('#skF_1')))
    | ~ m1_subset_1(u1_struct_0('#skF_1'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ r1_tarski(k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2')),'#skF_2')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_subset_1(k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2')),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_2524,c_28341])).

tff(c_28513,plain,
    ( r1_tarski(k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2')),k1_tops_1('#skF_1',u1_struct_0('#skF_1')))
    | ~ r1_tarski(k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2')),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_10531,c_38,c_15040,c_28449])).

tff(c_28519,plain,(
    ~ r1_tarski(k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2')),'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_28513])).

tff(c_28522,plain,
    ( ~ v4_tops_1('#skF_2','#skF_1')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_26,c_28519])).

tff(c_28526,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_36,c_28522])).

tff(c_28528,plain,(
    r1_tarski(k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2')),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_28513])).

tff(c_28850,plain,(
    ! [A_527] :
      ( r1_tarski(A_527,'#skF_2')
      | ~ r1_tarski(A_527,k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2'))) ) ),
    inference(resolution,[status(thm)],[c_28528,c_8])).

tff(c_28858,plain,(
    ! [B_33] :
      ( r1_tarski(k1_tops_1('#skF_1',B_33),'#skF_2')
      | ~ r1_tarski(B_33,k2_pre_topc('#skF_1','#skF_2'))
      | ~ m1_subset_1(k2_pre_topc('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ m1_subset_1(B_33,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_32,c_28850])).

tff(c_29375,plain,(
    ! [B_537] :
      ( r1_tarski(k1_tops_1('#skF_1',B_537),'#skF_2')
      | ~ r1_tarski(B_537,k2_pre_topc('#skF_1','#skF_2'))
      | ~ m1_subset_1(B_537,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_2503,c_28858])).

tff(c_29405,plain,
    ( r1_tarski(k1_tops_1('#skF_1','#skF_2'),'#skF_2')
    | ~ r1_tarski('#skF_2',k2_pre_topc('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_38,c_29375])).

tff(c_29429,plain,(
    r1_tarski(k1_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_99,c_29405])).

tff(c_29431,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_28518,c_29429])).

tff(c_29433,plain,(
    r1_tarski(k1_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_28517])).

tff(c_478,plain,(
    ! [A_83,A_84] :
      ( k2_pre_topc(A_83,k2_pre_topc(A_83,A_84)) = k2_pre_topc(A_83,A_84)
      | ~ l1_pre_topc(A_83)
      | ~ r1_tarski(A_84,u1_struct_0(A_83)) ) ),
    inference(resolution,[status(thm)],[c_12,c_410])).

tff(c_484,plain,(
    ! [A_44] :
      ( k2_pre_topc('#skF_1',k2_pre_topc('#skF_1',A_44)) = k2_pre_topc('#skF_1',A_44)
      | ~ l1_pre_topc('#skF_1')
      | ~ r1_tarski(A_44,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_70,c_478])).

tff(c_494,plain,(
    ! [A_44] :
      ( k2_pre_topc('#skF_1',k2_pre_topc('#skF_1',A_44)) = k2_pre_topc('#skF_1',A_44)
      | ~ r1_tarski(A_44,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_484])).

tff(c_20,plain,(
    ! [A_15,B_19,C_21] :
      ( r1_tarski(k2_pre_topc(A_15,B_19),k2_pre_topc(A_15,C_21))
      | ~ r1_tarski(B_19,C_21)
      | ~ m1_subset_1(C_21,k1_zfmisc_1(u1_struct_0(A_15)))
      | ~ m1_subset_1(B_19,k1_zfmisc_1(u1_struct_0(A_15)))
      | ~ l1_pre_topc(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_1364,plain,(
    ! [A_118,B_119,C_120] :
      ( r1_tarski(k2_pre_topc(A_118,B_119),k2_pre_topc(A_118,C_120))
      | ~ r1_tarski(B_119,C_120)
      | ~ m1_subset_1(C_120,k1_zfmisc_1(u1_struct_0(A_118)))
      | ~ m1_subset_1(B_119,k1_zfmisc_1(u1_struct_0(A_118)))
      | ~ l1_pre_topc(A_118) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_6141,plain,(
    ! [A_242,A_243,C_244,B_245] :
      ( r1_tarski(A_242,k2_pre_topc(A_243,C_244))
      | ~ r1_tarski(A_242,k2_pre_topc(A_243,B_245))
      | ~ r1_tarski(B_245,C_244)
      | ~ m1_subset_1(C_244,k1_zfmisc_1(u1_struct_0(A_243)))
      | ~ m1_subset_1(B_245,k1_zfmisc_1(u1_struct_0(A_243)))
      | ~ l1_pre_topc(A_243) ) ),
    inference(resolution,[status(thm)],[c_1364,c_8])).

tff(c_27602,plain,(
    ! [A_511,B_512,C_513,C_514] :
      ( r1_tarski(k2_pre_topc(A_511,B_512),k2_pre_topc(A_511,C_513))
      | ~ r1_tarski(C_514,C_513)
      | ~ m1_subset_1(C_513,k1_zfmisc_1(u1_struct_0(A_511)))
      | ~ r1_tarski(B_512,C_514)
      | ~ m1_subset_1(C_514,k1_zfmisc_1(u1_struct_0(A_511)))
      | ~ m1_subset_1(B_512,k1_zfmisc_1(u1_struct_0(A_511)))
      | ~ l1_pre_topc(A_511) ) ),
    inference(resolution,[status(thm)],[c_20,c_6141])).

tff(c_33753,plain,(
    ! [A_568,B_569] :
      ( r1_tarski(k2_pre_topc(A_568,B_569),k2_pre_topc(A_568,k2_pre_topc('#skF_1','#skF_2')))
      | ~ m1_subset_1(k2_pre_topc('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0(A_568)))
      | ~ r1_tarski(B_569,'#skF_2')
      | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0(A_568)))
      | ~ m1_subset_1(B_569,k1_zfmisc_1(u1_struct_0(A_568)))
      | ~ l1_pre_topc(A_568) ) ),
    inference(resolution,[status(thm)],[c_99,c_27602])).

tff(c_33916,plain,(
    ! [B_569] :
      ( r1_tarski(k2_pre_topc('#skF_1',B_569),k2_pre_topc('#skF_1','#skF_2'))
      | ~ m1_subset_1(k2_pre_topc('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ r1_tarski(B_569,'#skF_2')
      | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ m1_subset_1(B_569,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1')
      | ~ r1_tarski('#skF_2','#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_494,c_33753])).

tff(c_34010,plain,(
    ! [B_569] :
      ( r1_tarski(k2_pre_topc('#skF_1',B_569),k2_pre_topc('#skF_1','#skF_2'))
      | ~ r1_tarski(B_569,'#skF_2')
      | ~ m1_subset_1(B_569,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_40,c_38,c_2503,c_33916])).

tff(c_34,plain,
    ( ~ v4_tops_1(k2_pre_topc('#skF_1','#skF_2'),'#skF_1')
    | ~ v4_tops_1(k1_tops_1('#skF_1','#skF_2'),'#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_64,plain,(
    ~ v4_tops_1(k1_tops_1('#skF_1','#skF_2'),'#skF_1') ),
    inference(splitLeft,[status(thm)],[c_34])).

tff(c_718,plain,(
    ! [A_93,B_94] :
      ( r1_tarski(k1_tops_1(A_93,k2_pre_topc(A_93,B_94)),B_94)
      | ~ v4_tops_1(B_94,A_93)
      | ~ m1_subset_1(B_94,k1_zfmisc_1(u1_struct_0(A_93)))
      | ~ l1_pre_topc(A_93) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_3535,plain,(
    ! [A_178,B_179,A_180] :
      ( r1_tarski(A_178,B_179)
      | ~ r1_tarski(A_178,k1_tops_1(A_180,k2_pre_topc(A_180,B_179)))
      | ~ v4_tops_1(B_179,A_180)
      | ~ m1_subset_1(B_179,k1_zfmisc_1(u1_struct_0(A_180)))
      | ~ l1_pre_topc(A_180) ) ),
    inference(resolution,[status(thm)],[c_718,c_8])).

tff(c_34771,plain,(
    ! [A_574,B_575,B_576] :
      ( r1_tarski(k1_tops_1(A_574,B_575),B_576)
      | ~ v4_tops_1(B_576,A_574)
      | ~ m1_subset_1(B_576,k1_zfmisc_1(u1_struct_0(A_574)))
      | ~ r1_tarski(B_575,k2_pre_topc(A_574,B_576))
      | ~ m1_subset_1(k2_pre_topc(A_574,B_576),k1_zfmisc_1(u1_struct_0(A_574)))
      | ~ m1_subset_1(B_575,k1_zfmisc_1(u1_struct_0(A_574)))
      | ~ l1_pre_topc(A_574) ) ),
    inference(resolution,[status(thm)],[c_32,c_3535])).

tff(c_34791,plain,(
    ! [B_575] :
      ( r1_tarski(k1_tops_1('#skF_1',B_575),'#skF_2')
      | ~ v4_tops_1('#skF_2','#skF_1')
      | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ r1_tarski(B_575,k2_pre_topc('#skF_1','#skF_2'))
      | ~ m1_subset_1(B_575,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_2503,c_34771])).

tff(c_34824,plain,(
    ! [B_577] :
      ( r1_tarski(k1_tops_1('#skF_1',B_577),'#skF_2')
      | ~ r1_tarski(B_577,k2_pre_topc('#skF_1','#skF_2'))
      | ~ m1_subset_1(B_577,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_36,c_34791])).

tff(c_34836,plain,
    ( r1_tarski(k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2')),'#skF_2')
    | ~ r1_tarski(k2_pre_topc('#skF_1','#skF_2'),k2_pre_topc('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_2503,c_34824])).

tff(c_34864,plain,(
    r1_tarski(k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2')),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_34836])).

tff(c_10599,plain,(
    r1_tarski(k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2')),u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_10531,c_10])).

tff(c_31857,plain,(
    ! [A_557,B_558] :
      ( r1_tarski(k1_tops_1(A_557,B_558),k1_tops_1(A_557,k2_pre_topc('#skF_1','#skF_2')))
      | ~ m1_subset_1(k2_pre_topc('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0(A_557)))
      | ~ r1_tarski(B_558,'#skF_2')
      | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0(A_557)))
      | ~ m1_subset_1(B_558,k1_zfmisc_1(u1_struct_0(A_557)))
      | ~ l1_pre_topc(A_557) ) ),
    inference(resolution,[status(thm)],[c_99,c_28099])).

tff(c_1745,plain,(
    ! [C_129] :
      ( r1_tarski(k1_tops_1('#skF_1','#skF_2'),k1_tops_1('#skF_1',C_129))
      | ~ r1_tarski(k1_tops_1('#skF_1','#skF_2'),C_129)
      | ~ m1_subset_1(C_129,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ m1_subset_1(k1_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_441,c_1716])).

tff(c_1761,plain,(
    ! [C_129] :
      ( r1_tarski(k1_tops_1('#skF_1','#skF_2'),k1_tops_1('#skF_1',C_129))
      | ~ r1_tarski(k1_tops_1('#skF_1','#skF_2'),C_129)
      | ~ m1_subset_1(C_129,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_1636,c_1745])).

tff(c_7748,plain,(
    ! [A_270,C_271,B_272] :
      ( k1_tops_1(A_270,C_271) = k1_tops_1(A_270,B_272)
      | ~ r1_tarski(k1_tops_1(A_270,C_271),k1_tops_1(A_270,B_272))
      | ~ r1_tarski(B_272,C_271)
      | ~ m1_subset_1(C_271,k1_zfmisc_1(u1_struct_0(A_270)))
      | ~ m1_subset_1(B_272,k1_zfmisc_1(u1_struct_0(A_270)))
      | ~ l1_pre_topc(A_270) ) ),
    inference(resolution,[status(thm)],[c_1716,c_2])).

tff(c_7775,plain,(
    ! [C_129] :
      ( k1_tops_1('#skF_1',C_129) = k1_tops_1('#skF_1','#skF_2')
      | ~ r1_tarski(C_129,'#skF_2')
      | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1')
      | ~ r1_tarski(k1_tops_1('#skF_1','#skF_2'),C_129)
      | ~ m1_subset_1(C_129,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(resolution,[status(thm)],[c_1761,c_7748])).

tff(c_9732,plain,(
    ! [C_308] :
      ( k1_tops_1('#skF_1',C_308) = k1_tops_1('#skF_1','#skF_2')
      | ~ r1_tarski(C_308,'#skF_2')
      | ~ r1_tarski(k1_tops_1('#skF_1','#skF_2'),C_308)
      | ~ m1_subset_1(C_308,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_7775])).

tff(c_9764,plain,(
    ! [A_6] :
      ( k1_tops_1('#skF_1',A_6) = k1_tops_1('#skF_1','#skF_2')
      | ~ r1_tarski(A_6,'#skF_2')
      | ~ r1_tarski(k1_tops_1('#skF_1','#skF_2'),A_6)
      | ~ r1_tarski(A_6,u1_struct_0('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_12,c_9732])).

tff(c_31903,plain,
    ( k1_tops_1('#skF_1',k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2'))) = k1_tops_1('#skF_1','#skF_2')
    | ~ r1_tarski(k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2')),'#skF_2')
    | ~ r1_tarski(k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2')),u1_struct_0('#skF_1'))
    | ~ m1_subset_1(k2_pre_topc('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ r1_tarski('#skF_2','#skF_2')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_31857,c_9764])).

tff(c_32014,plain,
    ( k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2')) = k1_tops_1('#skF_1','#skF_2')
    | ~ r1_tarski(k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2')),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_6,c_2503,c_10599,c_2524,c_31903])).

tff(c_35463,plain,(
    k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2')) = k1_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34864,c_32014])).

tff(c_1635,plain,(
    r1_tarski(k1_tops_1('#skF_1','#skF_2'),k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_1503])).

tff(c_1948,plain,(
    ! [B_134,A_135] :
      ( v4_tops_1(B_134,A_135)
      | ~ r1_tarski(B_134,k2_pre_topc(A_135,k1_tops_1(A_135,B_134)))
      | ~ r1_tarski(k1_tops_1(A_135,k2_pre_topc(A_135,B_134)),B_134)
      | ~ m1_subset_1(B_134,k1_zfmisc_1(u1_struct_0(A_135)))
      | ~ l1_pre_topc(A_135) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_2002,plain,(
    ! [A_29,C_35] :
      ( v4_tops_1(k1_tops_1(A_29,C_35),A_29)
      | ~ r1_tarski(k1_tops_1(A_29,C_35),k2_pre_topc(A_29,k1_tops_1(A_29,k1_tops_1(A_29,C_35))))
      | ~ m1_subset_1(k1_tops_1(A_29,C_35),k1_zfmisc_1(u1_struct_0(A_29)))
      | ~ r1_tarski(k2_pre_topc(A_29,k1_tops_1(A_29,C_35)),C_35)
      | ~ m1_subset_1(C_35,k1_zfmisc_1(u1_struct_0(A_29)))
      | ~ m1_subset_1(k2_pre_topc(A_29,k1_tops_1(A_29,C_35)),k1_zfmisc_1(u1_struct_0(A_29)))
      | ~ l1_pre_topc(A_29) ) ),
    inference(resolution,[status(thm)],[c_32,c_1948])).

tff(c_35617,plain,
    ( v4_tops_1(k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2')),'#skF_1')
    | ~ r1_tarski(k1_tops_1('#skF_1','#skF_2'),k2_pre_topc('#skF_1',k1_tops_1('#skF_1',k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2')))))
    | ~ m1_subset_1(k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2')),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ r1_tarski(k2_pre_topc('#skF_1',k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2'))),k2_pre_topc('#skF_1','#skF_2'))
    | ~ m1_subset_1(k2_pre_topc('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_subset_1(k2_pre_topc('#skF_1',k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2'))),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_35463,c_2002])).

tff(c_35794,plain,
    ( v4_tops_1(k1_tops_1('#skF_1','#skF_2'),'#skF_1')
    | ~ r1_tarski(k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')),k2_pre_topc('#skF_1','#skF_2'))
    | ~ m1_subset_1(k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_35463,c_2503,c_35463,c_1636,c_35463,c_1635,c_441,c_35463,c_35463,c_35617])).

tff(c_35795,plain,
    ( ~ r1_tarski(k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')),k2_pre_topc('#skF_1','#skF_2'))
    | ~ m1_subset_1(k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_35794])).

tff(c_36078,plain,(
    ~ m1_subset_1(k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_35795])).

tff(c_36081,plain,
    ( ~ m1_subset_1(k1_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_14,c_36078])).

tff(c_36088,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_1636,c_36081])).

tff(c_36089,plain,(
    ~ r1_tarski(k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')),k2_pre_topc('#skF_1','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_35795])).

tff(c_36364,plain,
    ( ~ r1_tarski(k1_tops_1('#skF_1','#skF_2'),'#skF_2')
    | ~ m1_subset_1(k1_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_34010,c_36089])).

tff(c_36386,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1636,c_29433,c_36364])).

tff(c_36387,plain,(
    ~ v4_tops_1(k2_pre_topc('#skF_1','#skF_2'),'#skF_1') ),
    inference(splitRight,[status(thm)],[c_34])).

tff(c_36388,plain,(
    v4_tops_1(k1_tops_1('#skF_1','#skF_2'),'#skF_1') ),
    inference(splitRight,[status(thm)],[c_34])).

tff(c_36611,plain,(
    ! [A_612,B_613] :
      ( k1_tops_1(A_612,k1_tops_1(A_612,B_613)) = k1_tops_1(A_612,B_613)
      | ~ m1_subset_1(B_613,k1_zfmisc_1(u1_struct_0(A_612)))
      | ~ l1_pre_topc(A_612) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_36620,plain,
    ( k1_tops_1('#skF_1',k1_tops_1('#skF_1','#skF_2')) = k1_tops_1('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_38,c_36611])).

tff(c_36626,plain,(
    k1_tops_1('#skF_1',k1_tops_1('#skF_1','#skF_2')) = k1_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_36620])).

tff(c_37200,plain,(
    ! [B_641,A_642] :
      ( r1_tarski(B_641,k2_pre_topc(A_642,k1_tops_1(A_642,B_641)))
      | ~ v4_tops_1(B_641,A_642)
      | ~ m1_subset_1(B_641,k1_zfmisc_1(u1_struct_0(A_642)))
      | ~ l1_pre_topc(A_642) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_37238,plain,
    ( r1_tarski(k1_tops_1('#skF_1','#skF_2'),k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')))
    | ~ v4_tops_1(k1_tops_1('#skF_1','#skF_2'),'#skF_1')
    | ~ m1_subset_1(k1_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_36626,c_37200])).

tff(c_37252,plain,
    ( r1_tarski(k1_tops_1('#skF_1','#skF_2'),k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')))
    | ~ m1_subset_1(k1_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_36388,c_37238])).

tff(c_37895,plain,(
    ~ m1_subset_1(k1_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_37252])).

tff(c_37898,plain,
    ( ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_28,c_37895])).

tff(c_37905,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_37898])).

tff(c_37907,plain,(
    m1_subset_1(k1_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_37252])).

tff(c_37906,plain,(
    r1_tarski(k1_tops_1('#skF_1','#skF_2'),k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_37252])).

tff(c_37501,plain,(
    ! [A_652,B_653,C_654] :
      ( r1_tarski(k1_tops_1(A_652,B_653),k1_tops_1(A_652,C_654))
      | ~ r1_tarski(B_653,C_654)
      | ~ m1_subset_1(C_654,k1_zfmisc_1(u1_struct_0(A_652)))
      | ~ m1_subset_1(B_653,k1_zfmisc_1(u1_struct_0(A_652)))
      | ~ l1_pre_topc(A_652) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_42780,plain,(
    ! [A_772,C_773,B_774] :
      ( k1_tops_1(A_772,C_773) = k1_tops_1(A_772,B_774)
      | ~ r1_tarski(k1_tops_1(A_772,C_773),k1_tops_1(A_772,B_774))
      | ~ r1_tarski(B_774,C_773)
      | ~ m1_subset_1(C_773,k1_zfmisc_1(u1_struct_0(A_772)))
      | ~ m1_subset_1(B_774,k1_zfmisc_1(u1_struct_0(A_772)))
      | ~ l1_pre_topc(A_772) ) ),
    inference(resolution,[status(thm)],[c_37501,c_2])).

tff(c_42817,plain,(
    ! [C_773] :
      ( k1_tops_1('#skF_1',k1_tops_1('#skF_1','#skF_2')) = k1_tops_1('#skF_1',C_773)
      | ~ r1_tarski(k1_tops_1('#skF_1',C_773),k1_tops_1('#skF_1','#skF_2'))
      | ~ r1_tarski(k1_tops_1('#skF_1','#skF_2'),C_773)
      | ~ m1_subset_1(C_773,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ m1_subset_1(k1_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_36626,c_42780])).

tff(c_64347,plain,(
    ! [C_1021] :
      ( k1_tops_1('#skF_1',C_1021) = k1_tops_1('#skF_1','#skF_2')
      | ~ r1_tarski(k1_tops_1('#skF_1',C_1021),k1_tops_1('#skF_1','#skF_2'))
      | ~ r1_tarski(k1_tops_1('#skF_1','#skF_2'),C_1021)
      | ~ m1_subset_1(C_1021,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_37907,c_36626,c_42817])).

tff(c_64408,plain,
    ( k1_tops_1('#skF_1',k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2'))) = k1_tops_1('#skF_1','#skF_2')
    | ~ r1_tarski(k1_tops_1('#skF_1','#skF_2'),k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')))
    | ~ m1_subset_1(k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ v4_tops_1(k1_tops_1('#skF_1','#skF_2'),'#skF_1')
    | ~ m1_subset_1(k1_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_26,c_64347])).

tff(c_64457,plain,
    ( k1_tops_1('#skF_1',k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2'))) = k1_tops_1('#skF_1','#skF_2')
    | ~ m1_subset_1(k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_37907,c_36388,c_37906,c_64408])).

tff(c_72730,plain,(
    ~ m1_subset_1(k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_64457])).

tff(c_72733,plain,
    ( ~ m1_subset_1(k1_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_14,c_72730])).

tff(c_72740,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_37907,c_72733])).

tff(c_72742,plain,(
    m1_subset_1(k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_64457])).

tff(c_72889,plain,(
    r1_tarski(k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')),u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_72742,c_10])).

tff(c_16,plain,(
    ! [A_10,B_11] :
      ( k2_pre_topc(A_10,k2_pre_topc(A_10,B_11)) = k2_pre_topc(A_10,B_11)
      | ~ m1_subset_1(B_11,k1_zfmisc_1(u1_struct_0(A_10)))
      | ~ l1_pre_topc(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_38003,plain,
    ( k2_pre_topc('#skF_1',k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2'))) = k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2'))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_37907,c_16])).

tff(c_38013,plain,(
    k2_pre_topc('#skF_1',k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2'))) = k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38003])).

tff(c_24,plain,(
    ! [B_24,A_22] :
      ( r1_tarski(B_24,k2_pre_topc(A_22,k1_tops_1(A_22,B_24)))
      | ~ v4_tops_1(B_24,A_22)
      | ~ m1_subset_1(B_24,k1_zfmisc_1(u1_struct_0(A_22)))
      | ~ l1_pre_topc(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_37908,plain,(
    ! [A_666,B_667,C_668] :
      ( r1_tarski(k2_pre_topc(A_666,B_667),k2_pre_topc(A_666,C_668))
      | ~ r1_tarski(B_667,C_668)
      | ~ m1_subset_1(C_668,k1_zfmisc_1(u1_struct_0(A_666)))
      | ~ m1_subset_1(B_667,k1_zfmisc_1(u1_struct_0(A_666)))
      | ~ l1_pre_topc(A_666) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_41655,plain,(
    ! [A_744,A_745,C_746,B_747] :
      ( r1_tarski(A_744,k2_pre_topc(A_745,C_746))
      | ~ r1_tarski(A_744,k2_pre_topc(A_745,B_747))
      | ~ r1_tarski(B_747,C_746)
      | ~ m1_subset_1(C_746,k1_zfmisc_1(u1_struct_0(A_745)))
      | ~ m1_subset_1(B_747,k1_zfmisc_1(u1_struct_0(A_745)))
      | ~ l1_pre_topc(A_745) ) ),
    inference(resolution,[status(thm)],[c_37908,c_8])).

tff(c_84698,plain,(
    ! [B_1204,A_1205,C_1206] :
      ( r1_tarski(B_1204,k2_pre_topc(A_1205,C_1206))
      | ~ r1_tarski(k1_tops_1(A_1205,B_1204),C_1206)
      | ~ m1_subset_1(C_1206,k1_zfmisc_1(u1_struct_0(A_1205)))
      | ~ m1_subset_1(k1_tops_1(A_1205,B_1204),k1_zfmisc_1(u1_struct_0(A_1205)))
      | ~ v4_tops_1(B_1204,A_1205)
      | ~ m1_subset_1(B_1204,k1_zfmisc_1(u1_struct_0(A_1205)))
      | ~ l1_pre_topc(A_1205) ) ),
    inference(resolution,[status(thm)],[c_24,c_41655])).

tff(c_84879,plain,
    ( r1_tarski('#skF_2',k2_pre_topc('#skF_1',k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2'))))
    | ~ m1_subset_1(k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_subset_1(k1_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ v4_tops_1('#skF_2','#skF_1')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_37906,c_84698])).

tff(c_85101,plain,(
    r1_tarski('#skF_2',k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_36,c_37907,c_72742,c_38013,c_84879])).

tff(c_36425,plain,(
    ! [B_591,A_592] :
      ( r1_tarski(B_591,k2_pre_topc(A_592,B_591))
      | ~ m1_subset_1(B_591,k1_zfmisc_1(u1_struct_0(A_592)))
      | ~ l1_pre_topc(A_592) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_36430,plain,
    ( r1_tarski('#skF_2',k2_pre_topc('#skF_1','#skF_2'))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_38,c_36425])).

tff(c_36434,plain,(
    r1_tarski('#skF_2',k2_pre_topc('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_36430])).

tff(c_36862,plain,(
    ! [A_625,B_626] :
      ( k2_pre_topc(A_625,k2_pre_topc(A_625,B_626)) = k2_pre_topc(A_625,B_626)
      | ~ m1_subset_1(B_626,k1_zfmisc_1(u1_struct_0(A_625)))
      | ~ l1_pre_topc(A_625) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_36871,plain,
    ( k2_pre_topc('#skF_1',k2_pre_topc('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_38,c_36862])).

tff(c_36877,plain,(
    k2_pre_topc('#skF_1',k2_pre_topc('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_36871])).

tff(c_38203,plain,(
    ! [B_671,A_672] :
      ( v4_tops_1(B_671,A_672)
      | ~ r1_tarski(B_671,k2_pre_topc(A_672,k1_tops_1(A_672,B_671)))
      | ~ r1_tarski(k1_tops_1(A_672,k2_pre_topc(A_672,B_671)),B_671)
      | ~ m1_subset_1(B_671,k1_zfmisc_1(u1_struct_0(A_672)))
      | ~ l1_pre_topc(A_672) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_38226,plain,
    ( v4_tops_1(k2_pre_topc('#skF_1','#skF_2'),'#skF_1')
    | ~ r1_tarski(k2_pre_topc('#skF_1','#skF_2'),k2_pre_topc('#skF_1',k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2'))))
    | ~ r1_tarski(k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2')),k2_pre_topc('#skF_1','#skF_2'))
    | ~ m1_subset_1(k2_pre_topc('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_36877,c_38203])).

tff(c_38257,plain,
    ( v4_tops_1(k2_pre_topc('#skF_1','#skF_2'),'#skF_1')
    | ~ r1_tarski(k2_pre_topc('#skF_1','#skF_2'),k2_pre_topc('#skF_1',k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2'))))
    | ~ r1_tarski(k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2')),k2_pre_topc('#skF_1','#skF_2'))
    | ~ m1_subset_1(k2_pre_topc('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38226])).

tff(c_38258,plain,
    ( ~ r1_tarski(k2_pre_topc('#skF_1','#skF_2'),k2_pre_topc('#skF_1',k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2'))))
    | ~ r1_tarski(k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2')),k2_pre_topc('#skF_1','#skF_2'))
    | ~ m1_subset_1(k2_pre_topc('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(negUnitSimplification,[status(thm)],[c_36387,c_38257])).

tff(c_38346,plain,(
    ~ m1_subset_1(k2_pre_topc('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_38258])).

tff(c_38349,plain,
    ( ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_14,c_38346])).

tff(c_38356,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_38349])).

tff(c_38358,plain,(
    m1_subset_1(k2_pre_topc('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_38258])).

tff(c_38377,plain,(
    r1_tarski(k2_pre_topc('#skF_1','#skF_2'),u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_38358,c_10])).

tff(c_36389,plain,(
    ! [A_584,C_585,B_586] :
      ( r1_tarski(A_584,C_585)
      | ~ r1_tarski(B_586,C_585)
      | ~ r1_tarski(A_584,B_586) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_36394,plain,(
    ! [A_584] :
      ( r1_tarski(A_584,u1_struct_0('#skF_1'))
      | ~ r1_tarski(A_584,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_47,c_36389])).

tff(c_36469,plain,(
    ! [A_596,A_597] :
      ( r1_tarski(A_596,k2_pre_topc(A_597,A_596))
      | ~ l1_pre_topc(A_597)
      | ~ r1_tarski(A_596,u1_struct_0(A_597)) ) ),
    inference(resolution,[status(thm)],[c_12,c_36425])).

tff(c_36567,plain,(
    ! [A_607,A_608,A_609] :
      ( r1_tarski(A_607,k2_pre_topc(A_608,A_609))
      | ~ r1_tarski(A_607,A_609)
      | ~ l1_pre_topc(A_608)
      | ~ r1_tarski(A_609,u1_struct_0(A_608)) ) ),
    inference(resolution,[status(thm)],[c_36469,c_8])).

tff(c_36573,plain,(
    ! [A_607,A_584] :
      ( r1_tarski(A_607,k2_pre_topc('#skF_1',A_584))
      | ~ r1_tarski(A_607,A_584)
      | ~ l1_pre_topc('#skF_1')
      | ~ r1_tarski(A_584,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_36394,c_36567])).

tff(c_36588,plain,(
    ! [A_610,A_611] :
      ( r1_tarski(A_610,k2_pre_topc('#skF_1',A_611))
      | ~ r1_tarski(A_610,A_611)
      | ~ r1_tarski(A_611,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_36573])).

tff(c_36609,plain,(
    ! [A_3,A_611,A_610] :
      ( r1_tarski(A_3,k2_pre_topc('#skF_1',A_611))
      | ~ r1_tarski(A_3,A_610)
      | ~ r1_tarski(A_610,A_611)
      | ~ r1_tarski(A_611,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_36588,c_8])).

tff(c_38422,plain,(
    ! [A_611] :
      ( r1_tarski(k2_pre_topc('#skF_1','#skF_2'),k2_pre_topc('#skF_1',A_611))
      | ~ r1_tarski(u1_struct_0('#skF_1'),A_611)
      | ~ r1_tarski(A_611,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_38377,c_36609])).

tff(c_38357,plain,
    ( ~ r1_tarski(k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2')),k2_pre_topc('#skF_1','#skF_2'))
    | ~ r1_tarski(k2_pre_topc('#skF_1','#skF_2'),k2_pre_topc('#skF_1',k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2')))) ),
    inference(splitRight,[status(thm)],[c_38258])).

tff(c_39233,plain,(
    ~ r1_tarski(k2_pre_topc('#skF_1','#skF_2'),k2_pre_topc('#skF_1',k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2')))) ),
    inference(splitLeft,[status(thm)],[c_38357])).

tff(c_39246,plain,
    ( ~ r1_tarski(u1_struct_0('#skF_1'),k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2')))
    | ~ r1_tarski(k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2')),'#skF_2') ),
    inference(resolution,[status(thm)],[c_38422,c_39233])).

tff(c_39254,plain,(
    ~ r1_tarski(k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2')),'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_39246])).

tff(c_39257,plain,
    ( ~ v4_tops_1('#skF_2','#skF_1')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_26,c_39254])).

tff(c_39261,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_36,c_39257])).

tff(c_39263,plain,(
    r1_tarski(k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2')),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_39246])).

tff(c_39397,plain,(
    ! [A_695] :
      ( r1_tarski(A_695,'#skF_2')
      | ~ r1_tarski(A_695,k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2'))) ) ),
    inference(resolution,[status(thm)],[c_39263,c_8])).

tff(c_39401,plain,(
    ! [B_33] :
      ( r1_tarski(k1_tops_1('#skF_1',B_33),'#skF_2')
      | ~ r1_tarski(B_33,k2_pre_topc('#skF_1','#skF_2'))
      | ~ m1_subset_1(k2_pre_topc('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ m1_subset_1(B_33,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_32,c_39397])).

tff(c_39712,plain,(
    ! [B_704] :
      ( r1_tarski(k1_tops_1('#skF_1',B_704),'#skF_2')
      | ~ r1_tarski(B_704,k2_pre_topc('#skF_1','#skF_2'))
      | ~ m1_subset_1(B_704,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38358,c_39401])).

tff(c_39733,plain,
    ( r1_tarski(k1_tops_1('#skF_1','#skF_2'),'#skF_2')
    | ~ r1_tarski('#skF_2',k2_pre_topc('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_38,c_39712])).

tff(c_39748,plain,(
    r1_tarski(k1_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36434,c_39733])).

tff(c_73779,plain,(
    ! [A_1128,B_1129,C_1130,C_1131] :
      ( r1_tarski(k2_pre_topc(A_1128,B_1129),k2_pre_topc(A_1128,C_1130))
      | ~ r1_tarski(C_1131,C_1130)
      | ~ m1_subset_1(C_1130,k1_zfmisc_1(u1_struct_0(A_1128)))
      | ~ r1_tarski(B_1129,C_1131)
      | ~ m1_subset_1(C_1131,k1_zfmisc_1(u1_struct_0(A_1128)))
      | ~ m1_subset_1(B_1129,k1_zfmisc_1(u1_struct_0(A_1128)))
      | ~ l1_pre_topc(A_1128) ) ),
    inference(resolution,[status(thm)],[c_20,c_41655])).

tff(c_82976,plain,(
    ! [A_1190,B_1191] :
      ( r1_tarski(k2_pre_topc(A_1190,B_1191),k2_pre_topc(A_1190,'#skF_2'))
      | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0(A_1190)))
      | ~ r1_tarski(B_1191,k1_tops_1('#skF_1','#skF_2'))
      | ~ m1_subset_1(k1_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0(A_1190)))
      | ~ m1_subset_1(B_1191,k1_zfmisc_1(u1_struct_0(A_1190)))
      | ~ l1_pre_topc(A_1190) ) ),
    inference(resolution,[status(thm)],[c_39748,c_73779])).

tff(c_82978,plain,(
    ! [B_1191] :
      ( r1_tarski(k2_pre_topc('#skF_1',B_1191),k2_pre_topc('#skF_1','#skF_2'))
      | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ r1_tarski(B_1191,k1_tops_1('#skF_1','#skF_2'))
      | ~ m1_subset_1(B_1191,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_37907,c_82976])).

tff(c_82987,plain,(
    ! [B_1191] :
      ( r1_tarski(k2_pre_topc('#skF_1',B_1191),k2_pre_topc('#skF_1','#skF_2'))
      | ~ r1_tarski(B_1191,k1_tops_1('#skF_1','#skF_2'))
      | ~ m1_subset_1(B_1191,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_82978])).

tff(c_72741,plain,(
    k1_tops_1('#skF_1',k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2'))) = k1_tops_1('#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_64457])).

tff(c_39745,plain,(
    ! [A_6] :
      ( r1_tarski(k1_tops_1('#skF_1',A_6),'#skF_2')
      | ~ r1_tarski(A_6,k2_pre_topc('#skF_1','#skF_2'))
      | ~ r1_tarski(A_6,u1_struct_0('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_12,c_39712])).

tff(c_85229,plain,(
    ! [A_1207] :
      ( r1_tarski(A_1207,k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')))
      | ~ r1_tarski(A_1207,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_85101,c_8])).

tff(c_85565,plain,(
    ! [A_1208,A_1209] :
      ( r1_tarski(A_1208,k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')))
      | ~ r1_tarski(A_1208,A_1209)
      | ~ r1_tarski(A_1209,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_85229,c_8])).

tff(c_85741,plain,(
    ! [A_6] :
      ( r1_tarski(k1_tops_1('#skF_1',A_6),k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')))
      | ~ r1_tarski('#skF_2','#skF_2')
      | ~ r1_tarski(A_6,k2_pre_topc('#skF_1','#skF_2'))
      | ~ r1_tarski(A_6,u1_struct_0('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_39745,c_85565])).

tff(c_93975,plain,(
    ! [A_1268] :
      ( r1_tarski(k1_tops_1('#skF_1',A_1268),k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')))
      | ~ r1_tarski(A_1268,k2_pre_topc('#skF_1','#skF_2'))
      | ~ r1_tarski(A_1268,u1_struct_0('#skF_1')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_85741])).

tff(c_22,plain,(
    ! [B_24,A_22] :
      ( v4_tops_1(B_24,A_22)
      | ~ r1_tarski(B_24,k2_pre_topc(A_22,k1_tops_1(A_22,B_24)))
      | ~ r1_tarski(k1_tops_1(A_22,k2_pre_topc(A_22,B_24)),B_24)
      | ~ m1_subset_1(B_24,k1_zfmisc_1(u1_struct_0(A_22)))
      | ~ l1_pre_topc(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_94057,plain,
    ( v4_tops_1(k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')),'#skF_1')
    | ~ r1_tarski(k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')),k2_pre_topc('#skF_1',k1_tops_1('#skF_1',k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')))))
    | ~ m1_subset_1(k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1')
    | ~ r1_tarski(k2_pre_topc('#skF_1',k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2'))),k2_pre_topc('#skF_1','#skF_2'))
    | ~ r1_tarski(k2_pre_topc('#skF_1',k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2'))),u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_93975,c_22])).

tff(c_94198,plain,
    ( v4_tops_1(k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')),'#skF_1')
    | ~ r1_tarski(k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')),k2_pre_topc('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72889,c_38013,c_38013,c_40,c_72742,c_6,c_72741,c_94057])).

tff(c_94239,plain,(
    ~ r1_tarski(k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')),k2_pre_topc('#skF_1','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_94198])).

tff(c_94242,plain,
    ( ~ r1_tarski(k1_tops_1('#skF_1','#skF_2'),k1_tops_1('#skF_1','#skF_2'))
    | ~ m1_subset_1(k1_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_82987,c_94239])).

tff(c_94273,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_37907,c_6,c_94242])).

tff(c_94275,plain,(
    r1_tarski(k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')),k2_pre_topc('#skF_1','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_94198])).

tff(c_43039,plain,(
    ! [A_781,C_782,B_783] :
      ( k2_pre_topc(A_781,C_782) = k2_pre_topc(A_781,B_783)
      | ~ r1_tarski(k2_pre_topc(A_781,C_782),k2_pre_topc(A_781,B_783))
      | ~ r1_tarski(B_783,C_782)
      | ~ m1_subset_1(C_782,k1_zfmisc_1(u1_struct_0(A_781)))
      | ~ m1_subset_1(B_783,k1_zfmisc_1(u1_struct_0(A_781)))
      | ~ l1_pre_topc(A_781) ) ),
    inference(resolution,[status(thm)],[c_37908,c_2])).

tff(c_43113,plain,(
    ! [B_783] :
      ( k2_pre_topc('#skF_1',k2_pre_topc('#skF_1','#skF_2')) = k2_pre_topc('#skF_1',B_783)
      | ~ r1_tarski(k2_pre_topc('#skF_1','#skF_2'),k2_pre_topc('#skF_1',B_783))
      | ~ r1_tarski(B_783,k2_pre_topc('#skF_1','#skF_2'))
      | ~ m1_subset_1(k2_pre_topc('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ m1_subset_1(B_783,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_36877,c_43039])).

tff(c_63215,plain,(
    ! [B_1015] :
      ( k2_pre_topc('#skF_1',B_1015) = k2_pre_topc('#skF_1','#skF_2')
      | ~ r1_tarski(k2_pre_topc('#skF_1','#skF_2'),k2_pre_topc('#skF_1',B_1015))
      | ~ r1_tarski(B_1015,k2_pre_topc('#skF_1','#skF_2'))
      | ~ m1_subset_1(B_1015,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38358,c_36877,c_43113])).

tff(c_63313,plain,(
    ! [C_21] :
      ( k2_pre_topc('#skF_1',C_21) = k2_pre_topc('#skF_1','#skF_2')
      | ~ r1_tarski(C_21,k2_pre_topc('#skF_1','#skF_2'))
      | ~ r1_tarski('#skF_2',C_21)
      | ~ m1_subset_1(C_21,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_20,c_63215])).

tff(c_71877,plain,(
    ! [C_1116] :
      ( k2_pre_topc('#skF_1',C_1116) = k2_pre_topc('#skF_1','#skF_2')
      | ~ r1_tarski(C_1116,k2_pre_topc('#skF_1','#skF_2'))
      | ~ r1_tarski('#skF_2',C_1116)
      | ~ m1_subset_1(C_1116,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_63313])).

tff(c_71917,plain,(
    ! [A_6] :
      ( k2_pre_topc('#skF_1',A_6) = k2_pre_topc('#skF_1','#skF_2')
      | ~ r1_tarski(A_6,k2_pre_topc('#skF_1','#skF_2'))
      | ~ r1_tarski('#skF_2',A_6)
      | ~ r1_tarski(A_6,u1_struct_0('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_12,c_71877])).

tff(c_94654,plain,
    ( k2_pre_topc('#skF_1',k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2'))) = k2_pre_topc('#skF_1','#skF_2')
    | ~ r1_tarski('#skF_2',k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')))
    | ~ r1_tarski(k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')),u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_94275,c_71917])).

tff(c_94748,plain,(
    k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72889,c_85101,c_38013,c_94654])).

tff(c_94274,plain,(
    v4_tops_1(k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')),'#skF_1') ),
    inference(splitRight,[status(thm)],[c_94198])).

tff(c_94811,plain,(
    v4_tops_1(k2_pre_topc('#skF_1','#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_94748,c_94274])).

tff(c_94848,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_36387,c_94811])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n015.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 13:37:38 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 28.60/18.99  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 28.60/19.03  
% 28.60/19.03  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 28.60/19.03  %$ v4_tops_1 > r1_tarski > m1_subset_1 > l1_pre_topc > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_1
% 28.60/19.03  
% 28.60/19.03  %Foreground sorts:
% 28.60/19.03  
% 28.60/19.03  
% 28.60/19.03  %Background operators:
% 28.60/19.03  
% 28.60/19.03  
% 28.60/19.03  %Foreground operators:
% 28.60/19.03  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 28.60/19.03  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 28.60/19.03  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 28.60/19.03  tff(v4_tops_1, type, v4_tops_1: ($i * $i) > $o).
% 28.60/19.03  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 28.60/19.03  tff('#skF_2', type, '#skF_2': $i).
% 28.60/19.03  tff('#skF_1', type, '#skF_1': $i).
% 28.60/19.03  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 28.60/19.03  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 28.60/19.03  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 28.60/19.03  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 28.60/19.03  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 28.60/19.03  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 28.60/19.03  
% 28.88/19.07  tff(f_119, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_tops_1(B, A) => (v4_tops_1(k1_tops_1(A, B), A) & v4_tops_1(k2_pre_topc(A, B), A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t111_tops_1)).
% 28.88/19.07  tff(f_89, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k1_tops_1(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_tops_1)).
% 28.88/19.07  tff(f_95, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => (k1_tops_1(A, k1_tops_1(A, B)) = k1_tops_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', projectivity_k1_tops_1)).
% 28.88/19.07  tff(f_60, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => r1_tarski(B, k2_pre_topc(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_pre_topc)).
% 28.88/19.07  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 28.88/19.07  tff(f_41, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 28.88/19.07  tff(f_47, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_pre_topc(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_pre_topc)).
% 28.88/19.07  tff(f_53, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => (k2_pre_topc(A, k2_pre_topc(A, B)) = k2_pre_topc(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', projectivity_k2_pre_topc)).
% 28.88/19.07  tff(f_37, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 28.88/19.07  tff(f_107, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (r1_tarski(B, C) => r1_tarski(k1_tops_1(A, B), k1_tops_1(A, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_tops_1)).
% 28.88/19.07  tff(f_83, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_tops_1(B, A) <=> (r1_tarski(k1_tops_1(A, k2_pre_topc(A, B)), B) & r1_tarski(B, k2_pre_topc(A, k1_tops_1(A, B))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d6_tops_1)).
% 28.88/19.07  tff(f_72, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (r1_tarski(B, C) => r1_tarski(k2_pre_topc(A, B), k2_pre_topc(A, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_pre_topc)).
% 28.88/19.07  tff(c_40, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_119])).
% 28.88/19.07  tff(c_38, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_119])).
% 28.88/19.07  tff(c_28, plain, (![A_25, B_26]: (m1_subset_1(k1_tops_1(A_25, B_26), k1_zfmisc_1(u1_struct_0(A_25))) | ~m1_subset_1(B_26, k1_zfmisc_1(u1_struct_0(A_25))) | ~l1_pre_topc(A_25))), inference(cnfTransformation, [status(thm)], [f_89])).
% 28.88/19.07  tff(c_426, plain, (![A_81, B_82]: (k1_tops_1(A_81, k1_tops_1(A_81, B_82))=k1_tops_1(A_81, B_82) | ~m1_subset_1(B_82, k1_zfmisc_1(u1_struct_0(A_81))) | ~l1_pre_topc(A_81))), inference(cnfTransformation, [status(thm)], [f_95])).
% 28.88/19.07  tff(c_435, plain, (k1_tops_1('#skF_1', k1_tops_1('#skF_1', '#skF_2'))=k1_tops_1('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_38, c_426])).
% 28.88/19.07  tff(c_441, plain, (k1_tops_1('#skF_1', k1_tops_1('#skF_1', '#skF_2'))=k1_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_435])).
% 28.88/19.07  tff(c_194, plain, (![A_59, B_60]: (m1_subset_1(k1_tops_1(A_59, B_60), k1_zfmisc_1(u1_struct_0(A_59))) | ~m1_subset_1(B_60, k1_zfmisc_1(u1_struct_0(A_59))) | ~l1_pre_topc(A_59))), inference(cnfTransformation, [status(thm)], [f_89])).
% 28.88/19.07  tff(c_18, plain, (![B_14, A_12]: (r1_tarski(B_14, k2_pre_topc(A_12, B_14)) | ~m1_subset_1(B_14, k1_zfmisc_1(u1_struct_0(A_12))) | ~l1_pre_topc(A_12))), inference(cnfTransformation, [status(thm)], [f_60])).
% 28.88/19.07  tff(c_1458, plain, (![A_121, B_122]: (r1_tarski(k1_tops_1(A_121, B_122), k2_pre_topc(A_121, k1_tops_1(A_121, B_122))) | ~m1_subset_1(B_122, k1_zfmisc_1(u1_struct_0(A_121))) | ~l1_pre_topc(A_121))), inference(resolution, [status(thm)], [c_194, c_18])).
% 28.88/19.07  tff(c_1487, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_2'), k2_pre_topc('#skF_1', k1_tops_1('#skF_1', k1_tops_1('#skF_1', '#skF_2')))) | ~m1_subset_1(k1_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_441, c_1458])).
% 28.88/19.07  tff(c_1503, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_2'), k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2'))) | ~m1_subset_1(k1_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_441, c_1487])).
% 28.88/19.07  tff(c_1611, plain, (~m1_subset_1(k1_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitLeft, [status(thm)], [c_1503])).
% 28.88/19.07  tff(c_1627, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_28, c_1611])).
% 28.88/19.07  tff(c_1634, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_1627])).
% 28.88/19.07  tff(c_1636, plain, (m1_subset_1(k1_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitRight, [status(thm)], [c_1503])).
% 28.88/19.07  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 28.88/19.07  tff(c_12, plain, (![A_6, B_7]: (m1_subset_1(A_6, k1_zfmisc_1(B_7)) | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_41])).
% 28.88/19.07  tff(c_202, plain, (![A_61, B_62]: (m1_subset_1(k2_pre_topc(A_61, B_62), k1_zfmisc_1(u1_struct_0(A_61))) | ~m1_subset_1(B_62, k1_zfmisc_1(u1_struct_0(A_61))) | ~l1_pre_topc(A_61))), inference(cnfTransformation, [status(thm)], [f_47])).
% 28.88/19.07  tff(c_10, plain, (![A_6, B_7]: (r1_tarski(A_6, B_7) | ~m1_subset_1(A_6, k1_zfmisc_1(B_7)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 28.88/19.07  tff(c_209, plain, (![A_61, B_62]: (r1_tarski(k2_pre_topc(A_61, B_62), u1_struct_0(A_61)) | ~m1_subset_1(B_62, k1_zfmisc_1(u1_struct_0(A_61))) | ~l1_pre_topc(A_61))), inference(resolution, [status(thm)], [c_202, c_10])).
% 28.88/19.07  tff(c_90, plain, (![B_50, A_51]: (r1_tarski(B_50, k2_pre_topc(A_51, B_50)) | ~m1_subset_1(B_50, k1_zfmisc_1(u1_struct_0(A_51))) | ~l1_pre_topc(A_51))), inference(cnfTransformation, [status(thm)], [f_60])).
% 28.88/19.07  tff(c_137, plain, (![A_54, A_55]: (r1_tarski(A_54, k2_pre_topc(A_55, A_54)) | ~l1_pre_topc(A_55) | ~r1_tarski(A_54, u1_struct_0(A_55)))), inference(resolution, [status(thm)], [c_12, c_90])).
% 28.88/19.07  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 28.88/19.07  tff(c_759, plain, (![A_95, A_96]: (k2_pre_topc(A_95, A_96)=A_96 | ~r1_tarski(k2_pre_topc(A_95, A_96), A_96) | ~l1_pre_topc(A_95) | ~r1_tarski(A_96, u1_struct_0(A_95)))), inference(resolution, [status(thm)], [c_137, c_2])).
% 28.88/19.07  tff(c_780, plain, (![A_61]: (k2_pre_topc(A_61, u1_struct_0(A_61))=u1_struct_0(A_61) | ~r1_tarski(u1_struct_0(A_61), u1_struct_0(A_61)) | ~m1_subset_1(u1_struct_0(A_61), k1_zfmisc_1(u1_struct_0(A_61))) | ~l1_pre_topc(A_61))), inference(resolution, [status(thm)], [c_209, c_759])).
% 28.88/19.07  tff(c_802, plain, (![A_97]: (k2_pre_topc(A_97, u1_struct_0(A_97))=u1_struct_0(A_97) | ~m1_subset_1(u1_struct_0(A_97), k1_zfmisc_1(u1_struct_0(A_97))) | ~l1_pre_topc(A_97))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_780])).
% 28.88/19.07  tff(c_805, plain, (![A_97]: (k2_pre_topc(A_97, u1_struct_0(A_97))=u1_struct_0(A_97) | ~l1_pre_topc(A_97) | ~r1_tarski(u1_struct_0(A_97), u1_struct_0(A_97)))), inference(resolution, [status(thm)], [c_12, c_802])).
% 28.88/19.07  tff(c_808, plain, (![A_97]: (k2_pre_topc(A_97, u1_struct_0(A_97))=u1_struct_0(A_97) | ~l1_pre_topc(A_97))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_805])).
% 28.88/19.07  tff(c_1506, plain, (![A_123, B_124]: (r1_tarski(k2_pre_topc(A_123, B_124), k2_pre_topc(A_123, k2_pre_topc(A_123, B_124))) | ~m1_subset_1(B_124, k1_zfmisc_1(u1_struct_0(A_123))) | ~l1_pre_topc(A_123))), inference(resolution, [status(thm)], [c_202, c_18])).
% 28.88/19.07  tff(c_1543, plain, (![A_97]: (r1_tarski(u1_struct_0(A_97), k2_pre_topc(A_97, k2_pre_topc(A_97, u1_struct_0(A_97)))) | ~m1_subset_1(u1_struct_0(A_97), k1_zfmisc_1(u1_struct_0(A_97))) | ~l1_pre_topc(A_97) | ~l1_pre_topc(A_97))), inference(superposition, [status(thm), theory('equality')], [c_808, c_1506])).
% 28.88/19.07  tff(c_14, plain, (![A_8, B_9]: (m1_subset_1(k2_pre_topc(A_8, B_9), k1_zfmisc_1(u1_struct_0(A_8))) | ~m1_subset_1(B_9, k1_zfmisc_1(u1_struct_0(A_8))) | ~l1_pre_topc(A_8))), inference(cnfTransformation, [status(thm)], [f_47])).
% 28.88/19.07  tff(c_410, plain, (![A_79, B_80]: (k2_pre_topc(A_79, k2_pre_topc(A_79, B_80))=k2_pre_topc(A_79, B_80) | ~m1_subset_1(B_80, k1_zfmisc_1(u1_struct_0(A_79))) | ~l1_pre_topc(A_79))), inference(cnfTransformation, [status(thm)], [f_53])).
% 28.88/19.07  tff(c_2281, plain, (![A_143, B_144]: (k2_pre_topc(A_143, k2_pre_topc(A_143, k2_pre_topc(A_143, B_144)))=k2_pre_topc(A_143, k2_pre_topc(A_143, B_144)) | ~m1_subset_1(B_144, k1_zfmisc_1(u1_struct_0(A_143))) | ~l1_pre_topc(A_143))), inference(resolution, [status(thm)], [c_14, c_410])).
% 28.88/19.07  tff(c_2298, plain, (![A_143, A_6]: (k2_pre_topc(A_143, k2_pre_topc(A_143, k2_pre_topc(A_143, A_6)))=k2_pre_topc(A_143, k2_pre_topc(A_143, A_6)) | ~l1_pre_topc(A_143) | ~r1_tarski(A_6, u1_struct_0(A_143)))), inference(resolution, [status(thm)], [c_12, c_2281])).
% 28.88/19.07  tff(c_1655, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_2'), u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_1636, c_10])).
% 28.88/19.07  tff(c_43, plain, (![A_38, B_39]: (r1_tarski(A_38, B_39) | ~m1_subset_1(A_38, k1_zfmisc_1(B_39)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 28.88/19.07  tff(c_47, plain, (r1_tarski('#skF_2', u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_38, c_43])).
% 28.88/19.07  tff(c_65, plain, (![A_44, C_45, B_46]: (r1_tarski(A_44, C_45) | ~r1_tarski(B_46, C_45) | ~r1_tarski(A_44, B_46))), inference(cnfTransformation, [status(thm)], [f_37])).
% 28.88/19.07  tff(c_70, plain, (![A_44]: (r1_tarski(A_44, u1_struct_0('#skF_1')) | ~r1_tarski(A_44, '#skF_2'))), inference(resolution, [status(thm)], [c_47, c_65])).
% 28.88/19.07  tff(c_8, plain, (![A_3, C_5, B_4]: (r1_tarski(A_3, C_5) | ~r1_tarski(B_4, C_5) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_37])).
% 28.88/19.07  tff(c_243, plain, (![A_67, A_68, A_69]: (r1_tarski(A_67, k2_pre_topc(A_68, A_69)) | ~r1_tarski(A_67, A_69) | ~l1_pre_topc(A_68) | ~r1_tarski(A_69, u1_struct_0(A_68)))), inference(resolution, [status(thm)], [c_137, c_8])).
% 28.88/19.07  tff(c_249, plain, (![A_67, A_44]: (r1_tarski(A_67, k2_pre_topc('#skF_1', A_44)) | ~r1_tarski(A_67, A_44) | ~l1_pre_topc('#skF_1') | ~r1_tarski(A_44, '#skF_2'))), inference(resolution, [status(thm)], [c_70, c_243])).
% 28.88/19.07  tff(c_264, plain, (![A_70, A_71]: (r1_tarski(A_70, k2_pre_topc('#skF_1', A_71)) | ~r1_tarski(A_70, A_71) | ~r1_tarski(A_71, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_249])).
% 28.88/19.07  tff(c_285, plain, (![A_3, A_71, A_70]: (r1_tarski(A_3, k2_pre_topc('#skF_1', A_71)) | ~r1_tarski(A_3, A_70) | ~r1_tarski(A_70, A_71) | ~r1_tarski(A_71, '#skF_2'))), inference(resolution, [status(thm)], [c_264, c_8])).
% 28.88/19.07  tff(c_2014, plain, (![A_136]: (r1_tarski(k1_tops_1('#skF_1', '#skF_2'), k2_pre_topc('#skF_1', A_136)) | ~r1_tarski(u1_struct_0('#skF_1'), A_136) | ~r1_tarski(A_136, '#skF_2'))), inference(resolution, [status(thm)], [c_1655, c_285])).
% 28.88/19.07  tff(c_95, plain, (r1_tarski('#skF_2', k2_pre_topc('#skF_1', '#skF_2')) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_38, c_90])).
% 28.88/19.07  tff(c_99, plain, (r1_tarski('#skF_2', k2_pre_topc('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_95])).
% 28.88/19.07  tff(c_110, plain, (![A_52]: (r1_tarski(A_52, k2_pre_topc('#skF_1', '#skF_2')) | ~r1_tarski(A_52, '#skF_2'))), inference(resolution, [status(thm)], [c_99, c_8])).
% 28.88/19.07  tff(c_118, plain, (![A_3, A_52]: (r1_tarski(A_3, k2_pre_topc('#skF_1', '#skF_2')) | ~r1_tarski(A_3, A_52) | ~r1_tarski(A_52, '#skF_2'))), inference(resolution, [status(thm)], [c_110, c_8])).
% 28.88/19.07  tff(c_2049, plain, (![A_136]: (r1_tarski(k1_tops_1('#skF_1', '#skF_2'), k2_pre_topc('#skF_1', '#skF_2')) | ~r1_tarski(k2_pre_topc('#skF_1', A_136), '#skF_2') | ~r1_tarski(u1_struct_0('#skF_1'), A_136) | ~r1_tarski(A_136, '#skF_2'))), inference(resolution, [status(thm)], [c_2014, c_118])).
% 28.88/19.07  tff(c_13874, plain, (![A_359]: (~r1_tarski(k2_pre_topc('#skF_1', A_359), '#skF_2') | ~r1_tarski(u1_struct_0('#skF_1'), A_359) | ~r1_tarski(A_359, '#skF_2'))), inference(splitLeft, [status(thm)], [c_2049])).
% 28.88/19.07  tff(c_13882, plain, (![A_6]: (~r1_tarski(k2_pre_topc('#skF_1', k2_pre_topc('#skF_1', A_6)), '#skF_2') | ~r1_tarski(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', k2_pre_topc('#skF_1', A_6))) | ~r1_tarski(k2_pre_topc('#skF_1', k2_pre_topc('#skF_1', A_6)), '#skF_2') | ~l1_pre_topc('#skF_1') | ~r1_tarski(A_6, u1_struct_0('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_2298, c_13874])).
% 28.88/19.07  tff(c_14900, plain, (![A_375]: (~r1_tarski(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', k2_pre_topc('#skF_1', A_375))) | ~r1_tarski(k2_pre_topc('#skF_1', k2_pre_topc('#skF_1', A_375)), '#skF_2') | ~r1_tarski(A_375, u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_13882])).
% 28.88/19.07  tff(c_14912, plain, (~r1_tarski(k2_pre_topc('#skF_1', k2_pre_topc('#skF_1', u1_struct_0('#skF_1'))), '#skF_2') | ~r1_tarski(u1_struct_0('#skF_1'), u1_struct_0('#skF_1')) | ~m1_subset_1(u1_struct_0('#skF_1'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_1543, c_14900])).
% 28.88/19.07  tff(c_14994, plain, (~r1_tarski(k2_pre_topc('#skF_1', k2_pre_topc('#skF_1', u1_struct_0('#skF_1'))), '#skF_2') | ~m1_subset_1(u1_struct_0('#skF_1'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_6, c_14912])).
% 28.88/19.07  tff(c_15031, plain, (~m1_subset_1(u1_struct_0('#skF_1'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitLeft, [status(thm)], [c_14994])).
% 28.88/19.07  tff(c_15034, plain, (~r1_tarski(u1_struct_0('#skF_1'), u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_12, c_15031])).
% 28.88/19.07  tff(c_15038, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_15034])).
% 28.88/19.07  tff(c_15040, plain, (m1_subset_1(u1_struct_0('#skF_1'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitRight, [status(thm)], [c_14994])).
% 28.88/19.07  tff(c_32, plain, (![A_29, B_33, C_35]: (r1_tarski(k1_tops_1(A_29, B_33), k1_tops_1(A_29, C_35)) | ~r1_tarski(B_33, C_35) | ~m1_subset_1(C_35, k1_zfmisc_1(u1_struct_0(A_29))) | ~m1_subset_1(B_33, k1_zfmisc_1(u1_struct_0(A_29))) | ~l1_pre_topc(A_29))), inference(cnfTransformation, [status(thm)], [f_107])).
% 28.88/19.07  tff(c_1716, plain, (![A_127, B_128, C_129]: (r1_tarski(k1_tops_1(A_127, B_128), k1_tops_1(A_127, C_129)) | ~r1_tarski(B_128, C_129) | ~m1_subset_1(C_129, k1_zfmisc_1(u1_struct_0(A_127))) | ~m1_subset_1(B_128, k1_zfmisc_1(u1_struct_0(A_127))) | ~l1_pre_topc(A_127))), inference(cnfTransformation, [status(thm)], [f_107])).
% 28.88/19.07  tff(c_5019, plain, (![A_223, A_224, C_225, B_226]: (r1_tarski(A_223, k1_tops_1(A_224, C_225)) | ~r1_tarski(A_223, k1_tops_1(A_224, B_226)) | ~r1_tarski(B_226, C_225) | ~m1_subset_1(C_225, k1_zfmisc_1(u1_struct_0(A_224))) | ~m1_subset_1(B_226, k1_zfmisc_1(u1_struct_0(A_224))) | ~l1_pre_topc(A_224))), inference(resolution, [status(thm)], [c_1716, c_8])).
% 28.88/19.07  tff(c_28099, plain, (![A_518, B_519, C_520, C_521]: (r1_tarski(k1_tops_1(A_518, B_519), k1_tops_1(A_518, C_520)) | ~r1_tarski(C_521, C_520) | ~m1_subset_1(C_520, k1_zfmisc_1(u1_struct_0(A_518))) | ~r1_tarski(B_519, C_521) | ~m1_subset_1(C_521, k1_zfmisc_1(u1_struct_0(A_518))) | ~m1_subset_1(B_519, k1_zfmisc_1(u1_struct_0(A_518))) | ~l1_pre_topc(A_518))), inference(resolution, [status(thm)], [c_32, c_5019])).
% 28.88/19.07  tff(c_28341, plain, (![A_522, B_523]: (r1_tarski(k1_tops_1(A_522, B_523), k1_tops_1(A_522, u1_struct_0('#skF_1'))) | ~m1_subset_1(u1_struct_0('#skF_1'), k1_zfmisc_1(u1_struct_0(A_522))) | ~r1_tarski(B_523, '#skF_2') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0(A_522))) | ~m1_subset_1(B_523, k1_zfmisc_1(u1_struct_0(A_522))) | ~l1_pre_topc(A_522))), inference(resolution, [status(thm)], [c_47, c_28099])).
% 28.88/19.07  tff(c_28458, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_2'), k1_tops_1('#skF_1', u1_struct_0('#skF_1'))) | ~m1_subset_1(u1_struct_0('#skF_1'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~r1_tarski(k1_tops_1('#skF_1', '#skF_2'), '#skF_2') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1(k1_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_441, c_28341])).
% 28.88/19.07  tff(c_28517, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_2'), k1_tops_1('#skF_1', u1_struct_0('#skF_1'))) | ~r1_tarski(k1_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_1636, c_38, c_15040, c_28458])).
% 28.88/19.07  tff(c_28518, plain, (~r1_tarski(k1_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(splitLeft, [status(thm)], [c_28517])).
% 28.88/19.07  tff(c_419, plain, (k2_pre_topc('#skF_1', k2_pre_topc('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_38, c_410])).
% 28.88/19.07  tff(c_425, plain, (k2_pre_topc('#skF_1', k2_pre_topc('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_419])).
% 28.88/19.07  tff(c_223, plain, (![A_65, B_66]: (r1_tarski(k2_pre_topc(A_65, B_66), u1_struct_0(A_65)) | ~m1_subset_1(B_66, k1_zfmisc_1(u1_struct_0(A_65))) | ~l1_pre_topc(A_65))), inference(resolution, [status(thm)], [c_202, c_10])).
% 28.88/19.07  tff(c_2400, plain, (![A_149, A_150, B_151]: (r1_tarski(A_149, u1_struct_0(A_150)) | ~r1_tarski(A_149, k2_pre_topc(A_150, B_151)) | ~m1_subset_1(B_151, k1_zfmisc_1(u1_struct_0(A_150))) | ~l1_pre_topc(A_150))), inference(resolution, [status(thm)], [c_223, c_8])).
% 28.88/19.07  tff(c_2435, plain, (![A_149]: (r1_tarski(A_149, u1_struct_0('#skF_1')) | ~r1_tarski(A_149, k2_pre_topc('#skF_1', '#skF_2')) | ~m1_subset_1(k2_pre_topc('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_425, c_2400])).
% 28.88/19.07  tff(c_2478, plain, (![A_149]: (r1_tarski(A_149, u1_struct_0('#skF_1')) | ~r1_tarski(A_149, k2_pre_topc('#skF_1', '#skF_2')) | ~m1_subset_1(k2_pre_topc('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_2435])).
% 28.88/19.07  tff(c_2491, plain, (~m1_subset_1(k2_pre_topc('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitLeft, [status(thm)], [c_2478])).
% 28.88/19.07  tff(c_2494, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_14, c_2491])).
% 28.88/19.07  tff(c_2501, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_2494])).
% 28.88/19.07  tff(c_2503, plain, (m1_subset_1(k2_pre_topc('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitRight, [status(thm)], [c_2478])).
% 28.88/19.07  tff(c_36, plain, (v4_tops_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_119])).
% 28.88/19.07  tff(c_26, plain, (![A_22, B_24]: (r1_tarski(k1_tops_1(A_22, k2_pre_topc(A_22, B_24)), B_24) | ~v4_tops_1(B_24, A_22) | ~m1_subset_1(B_24, k1_zfmisc_1(u1_struct_0(A_22))) | ~l1_pre_topc(A_22))), inference(cnfTransformation, [status(thm)], [f_83])).
% 28.88/19.07  tff(c_2504, plain, (![A_152, B_153]: (k1_tops_1(A_152, k1_tops_1(A_152, k2_pre_topc(A_152, B_153)))=k1_tops_1(A_152, k2_pre_topc(A_152, B_153)) | ~m1_subset_1(B_153, k1_zfmisc_1(u1_struct_0(A_152))) | ~l1_pre_topc(A_152))), inference(resolution, [status(thm)], [c_14, c_426])).
% 28.88/19.07  tff(c_2515, plain, (k1_tops_1('#skF_1', k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_2')))=k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_2')) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_38, c_2504])).
% 28.88/19.07  tff(c_2524, plain, (k1_tops_1('#skF_1', k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_2')))=k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_2515])).
% 28.88/19.07  tff(c_1748, plain, (![B_128]: (r1_tarski(k1_tops_1('#skF_1', B_128), k1_tops_1('#skF_1', '#skF_2')) | ~r1_tarski(B_128, k1_tops_1('#skF_1', '#skF_2')) | ~m1_subset_1(k1_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1(B_128, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_441, c_1716])).
% 28.88/19.07  tff(c_3679, plain, (![B_184]: (r1_tarski(k1_tops_1('#skF_1', B_184), k1_tops_1('#skF_1', '#skF_2')) | ~r1_tarski(B_184, k1_tops_1('#skF_1', '#skF_2')) | ~m1_subset_1(B_184, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_1636, c_1748])).
% 28.88/19.07  tff(c_210, plain, (![A_63, B_64]: (r1_tarski(k1_tops_1(A_63, B_64), u1_struct_0(A_63)) | ~m1_subset_1(B_64, k1_zfmisc_1(u1_struct_0(A_63))) | ~l1_pre_topc(A_63))), inference(resolution, [status(thm)], [c_194, c_10])).
% 28.88/19.07  tff(c_221, plain, (![A_3, A_63, B_64]: (r1_tarski(A_3, u1_struct_0(A_63)) | ~r1_tarski(A_3, k1_tops_1(A_63, B_64)) | ~m1_subset_1(B_64, k1_zfmisc_1(u1_struct_0(A_63))) | ~l1_pre_topc(A_63))), inference(resolution, [status(thm)], [c_210, c_8])).
% 28.88/19.07  tff(c_3683, plain, (![B_184]: (r1_tarski(k1_tops_1('#skF_1', B_184), u1_struct_0('#skF_1')) | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1') | ~r1_tarski(B_184, k1_tops_1('#skF_1', '#skF_2')) | ~m1_subset_1(B_184, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(resolution, [status(thm)], [c_3679, c_221])).
% 28.88/19.07  tff(c_3746, plain, (![B_185]: (r1_tarski(k1_tops_1('#skF_1', B_185), u1_struct_0('#skF_1')) | ~r1_tarski(B_185, k1_tops_1('#skF_1', '#skF_2')) | ~m1_subset_1(B_185, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_3683])).
% 28.88/19.07  tff(c_10460, plain, (![A_322, B_323]: (r1_tarski(A_322, u1_struct_0('#skF_1')) | ~r1_tarski(A_322, k1_tops_1('#skF_1', B_323)) | ~r1_tarski(B_323, k1_tops_1('#skF_1', '#skF_2')) | ~m1_subset_1(B_323, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(resolution, [status(thm)], [c_3746, c_8])).
% 28.88/19.07  tff(c_10480, plain, (![A_322]: (r1_tarski(A_322, u1_struct_0('#skF_1')) | ~r1_tarski(A_322, k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_2'))) | ~r1_tarski(k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_2')), k1_tops_1('#skF_1', '#skF_2')) | ~m1_subset_1(k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_2')), k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(superposition, [status(thm), theory('equality')], [c_2524, c_10460])).
% 28.88/19.07  tff(c_10519, plain, (~m1_subset_1(k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_2')), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitLeft, [status(thm)], [c_10480])).
% 28.88/19.07  tff(c_10522, plain, (~m1_subset_1(k2_pre_topc('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_28, c_10519])).
% 28.88/19.07  tff(c_10529, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_40, c_2503, c_10522])).
% 28.88/19.07  tff(c_10531, plain, (m1_subset_1(k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_2')), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitRight, [status(thm)], [c_10480])).
% 28.88/19.07  tff(c_28449, plain, (r1_tarski(k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_2')), k1_tops_1('#skF_1', u1_struct_0('#skF_1'))) | ~m1_subset_1(u1_struct_0('#skF_1'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~r1_tarski(k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_2')), '#skF_2') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1(k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_2')), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_2524, c_28341])).
% 28.88/19.07  tff(c_28513, plain, (r1_tarski(k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_2')), k1_tops_1('#skF_1', u1_struct_0('#skF_1'))) | ~r1_tarski(k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_2')), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_10531, c_38, c_15040, c_28449])).
% 28.88/19.07  tff(c_28519, plain, (~r1_tarski(k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_2')), '#skF_2')), inference(splitLeft, [status(thm)], [c_28513])).
% 28.88/19.07  tff(c_28522, plain, (~v4_tops_1('#skF_2', '#skF_1') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_26, c_28519])).
% 28.88/19.07  tff(c_28526, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_36, c_28522])).
% 28.88/19.07  tff(c_28528, plain, (r1_tarski(k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_2')), '#skF_2')), inference(splitRight, [status(thm)], [c_28513])).
% 28.88/19.07  tff(c_28850, plain, (![A_527]: (r1_tarski(A_527, '#skF_2') | ~r1_tarski(A_527, k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_2'))))), inference(resolution, [status(thm)], [c_28528, c_8])).
% 28.88/19.07  tff(c_28858, plain, (![B_33]: (r1_tarski(k1_tops_1('#skF_1', B_33), '#skF_2') | ~r1_tarski(B_33, k2_pre_topc('#skF_1', '#skF_2')) | ~m1_subset_1(k2_pre_topc('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1(B_33, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_32, c_28850])).
% 28.88/19.07  tff(c_29375, plain, (![B_537]: (r1_tarski(k1_tops_1('#skF_1', B_537), '#skF_2') | ~r1_tarski(B_537, k2_pre_topc('#skF_1', '#skF_2')) | ~m1_subset_1(B_537, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_2503, c_28858])).
% 28.88/19.07  tff(c_29405, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_2'), '#skF_2') | ~r1_tarski('#skF_2', k2_pre_topc('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_38, c_29375])).
% 28.88/19.07  tff(c_29429, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_99, c_29405])).
% 28.88/19.07  tff(c_29431, plain, $false, inference(negUnitSimplification, [status(thm)], [c_28518, c_29429])).
% 28.88/19.07  tff(c_29433, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(splitRight, [status(thm)], [c_28517])).
% 28.88/19.07  tff(c_478, plain, (![A_83, A_84]: (k2_pre_topc(A_83, k2_pre_topc(A_83, A_84))=k2_pre_topc(A_83, A_84) | ~l1_pre_topc(A_83) | ~r1_tarski(A_84, u1_struct_0(A_83)))), inference(resolution, [status(thm)], [c_12, c_410])).
% 28.88/19.07  tff(c_484, plain, (![A_44]: (k2_pre_topc('#skF_1', k2_pre_topc('#skF_1', A_44))=k2_pre_topc('#skF_1', A_44) | ~l1_pre_topc('#skF_1') | ~r1_tarski(A_44, '#skF_2'))), inference(resolution, [status(thm)], [c_70, c_478])).
% 28.88/19.07  tff(c_494, plain, (![A_44]: (k2_pre_topc('#skF_1', k2_pre_topc('#skF_1', A_44))=k2_pre_topc('#skF_1', A_44) | ~r1_tarski(A_44, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_484])).
% 28.88/19.07  tff(c_20, plain, (![A_15, B_19, C_21]: (r1_tarski(k2_pre_topc(A_15, B_19), k2_pre_topc(A_15, C_21)) | ~r1_tarski(B_19, C_21) | ~m1_subset_1(C_21, k1_zfmisc_1(u1_struct_0(A_15))) | ~m1_subset_1(B_19, k1_zfmisc_1(u1_struct_0(A_15))) | ~l1_pre_topc(A_15))), inference(cnfTransformation, [status(thm)], [f_72])).
% 28.88/19.07  tff(c_1364, plain, (![A_118, B_119, C_120]: (r1_tarski(k2_pre_topc(A_118, B_119), k2_pre_topc(A_118, C_120)) | ~r1_tarski(B_119, C_120) | ~m1_subset_1(C_120, k1_zfmisc_1(u1_struct_0(A_118))) | ~m1_subset_1(B_119, k1_zfmisc_1(u1_struct_0(A_118))) | ~l1_pre_topc(A_118))), inference(cnfTransformation, [status(thm)], [f_72])).
% 28.88/19.07  tff(c_6141, plain, (![A_242, A_243, C_244, B_245]: (r1_tarski(A_242, k2_pre_topc(A_243, C_244)) | ~r1_tarski(A_242, k2_pre_topc(A_243, B_245)) | ~r1_tarski(B_245, C_244) | ~m1_subset_1(C_244, k1_zfmisc_1(u1_struct_0(A_243))) | ~m1_subset_1(B_245, k1_zfmisc_1(u1_struct_0(A_243))) | ~l1_pre_topc(A_243))), inference(resolution, [status(thm)], [c_1364, c_8])).
% 28.88/19.07  tff(c_27602, plain, (![A_511, B_512, C_513, C_514]: (r1_tarski(k2_pre_topc(A_511, B_512), k2_pre_topc(A_511, C_513)) | ~r1_tarski(C_514, C_513) | ~m1_subset_1(C_513, k1_zfmisc_1(u1_struct_0(A_511))) | ~r1_tarski(B_512, C_514) | ~m1_subset_1(C_514, k1_zfmisc_1(u1_struct_0(A_511))) | ~m1_subset_1(B_512, k1_zfmisc_1(u1_struct_0(A_511))) | ~l1_pre_topc(A_511))), inference(resolution, [status(thm)], [c_20, c_6141])).
% 28.88/19.07  tff(c_33753, plain, (![A_568, B_569]: (r1_tarski(k2_pre_topc(A_568, B_569), k2_pre_topc(A_568, k2_pre_topc('#skF_1', '#skF_2'))) | ~m1_subset_1(k2_pre_topc('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0(A_568))) | ~r1_tarski(B_569, '#skF_2') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0(A_568))) | ~m1_subset_1(B_569, k1_zfmisc_1(u1_struct_0(A_568))) | ~l1_pre_topc(A_568))), inference(resolution, [status(thm)], [c_99, c_27602])).
% 28.88/19.07  tff(c_33916, plain, (![B_569]: (r1_tarski(k2_pre_topc('#skF_1', B_569), k2_pre_topc('#skF_1', '#skF_2')) | ~m1_subset_1(k2_pre_topc('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~r1_tarski(B_569, '#skF_2') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1(B_569, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1') | ~r1_tarski('#skF_2', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_494, c_33753])).
% 28.88/19.07  tff(c_34010, plain, (![B_569]: (r1_tarski(k2_pre_topc('#skF_1', B_569), k2_pre_topc('#skF_1', '#skF_2')) | ~r1_tarski(B_569, '#skF_2') | ~m1_subset_1(B_569, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_40, c_38, c_2503, c_33916])).
% 28.88/19.07  tff(c_34, plain, (~v4_tops_1(k2_pre_topc('#skF_1', '#skF_2'), '#skF_1') | ~v4_tops_1(k1_tops_1('#skF_1', '#skF_2'), '#skF_1')), inference(cnfTransformation, [status(thm)], [f_119])).
% 28.88/19.07  tff(c_64, plain, (~v4_tops_1(k1_tops_1('#skF_1', '#skF_2'), '#skF_1')), inference(splitLeft, [status(thm)], [c_34])).
% 28.88/19.07  tff(c_718, plain, (![A_93, B_94]: (r1_tarski(k1_tops_1(A_93, k2_pre_topc(A_93, B_94)), B_94) | ~v4_tops_1(B_94, A_93) | ~m1_subset_1(B_94, k1_zfmisc_1(u1_struct_0(A_93))) | ~l1_pre_topc(A_93))), inference(cnfTransformation, [status(thm)], [f_83])).
% 28.88/19.07  tff(c_3535, plain, (![A_178, B_179, A_180]: (r1_tarski(A_178, B_179) | ~r1_tarski(A_178, k1_tops_1(A_180, k2_pre_topc(A_180, B_179))) | ~v4_tops_1(B_179, A_180) | ~m1_subset_1(B_179, k1_zfmisc_1(u1_struct_0(A_180))) | ~l1_pre_topc(A_180))), inference(resolution, [status(thm)], [c_718, c_8])).
% 28.88/19.07  tff(c_34771, plain, (![A_574, B_575, B_576]: (r1_tarski(k1_tops_1(A_574, B_575), B_576) | ~v4_tops_1(B_576, A_574) | ~m1_subset_1(B_576, k1_zfmisc_1(u1_struct_0(A_574))) | ~r1_tarski(B_575, k2_pre_topc(A_574, B_576)) | ~m1_subset_1(k2_pre_topc(A_574, B_576), k1_zfmisc_1(u1_struct_0(A_574))) | ~m1_subset_1(B_575, k1_zfmisc_1(u1_struct_0(A_574))) | ~l1_pre_topc(A_574))), inference(resolution, [status(thm)], [c_32, c_3535])).
% 28.88/19.07  tff(c_34791, plain, (![B_575]: (r1_tarski(k1_tops_1('#skF_1', B_575), '#skF_2') | ~v4_tops_1('#skF_2', '#skF_1') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~r1_tarski(B_575, k2_pre_topc('#skF_1', '#skF_2')) | ~m1_subset_1(B_575, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_2503, c_34771])).
% 28.88/19.07  tff(c_34824, plain, (![B_577]: (r1_tarski(k1_tops_1('#skF_1', B_577), '#skF_2') | ~r1_tarski(B_577, k2_pre_topc('#skF_1', '#skF_2')) | ~m1_subset_1(B_577, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_36, c_34791])).
% 28.88/19.07  tff(c_34836, plain, (r1_tarski(k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_2')), '#skF_2') | ~r1_tarski(k2_pre_topc('#skF_1', '#skF_2'), k2_pre_topc('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_2503, c_34824])).
% 28.88/19.07  tff(c_34864, plain, (r1_tarski(k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_2')), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_6, c_34836])).
% 28.88/19.07  tff(c_10599, plain, (r1_tarski(k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_2')), u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_10531, c_10])).
% 28.88/19.07  tff(c_31857, plain, (![A_557, B_558]: (r1_tarski(k1_tops_1(A_557, B_558), k1_tops_1(A_557, k2_pre_topc('#skF_1', '#skF_2'))) | ~m1_subset_1(k2_pre_topc('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0(A_557))) | ~r1_tarski(B_558, '#skF_2') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0(A_557))) | ~m1_subset_1(B_558, k1_zfmisc_1(u1_struct_0(A_557))) | ~l1_pre_topc(A_557))), inference(resolution, [status(thm)], [c_99, c_28099])).
% 28.88/19.07  tff(c_1745, plain, (![C_129]: (r1_tarski(k1_tops_1('#skF_1', '#skF_2'), k1_tops_1('#skF_1', C_129)) | ~r1_tarski(k1_tops_1('#skF_1', '#skF_2'), C_129) | ~m1_subset_1(C_129, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1(k1_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_441, c_1716])).
% 28.88/19.07  tff(c_1761, plain, (![C_129]: (r1_tarski(k1_tops_1('#skF_1', '#skF_2'), k1_tops_1('#skF_1', C_129)) | ~r1_tarski(k1_tops_1('#skF_1', '#skF_2'), C_129) | ~m1_subset_1(C_129, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_1636, c_1745])).
% 28.88/19.07  tff(c_7748, plain, (![A_270, C_271, B_272]: (k1_tops_1(A_270, C_271)=k1_tops_1(A_270, B_272) | ~r1_tarski(k1_tops_1(A_270, C_271), k1_tops_1(A_270, B_272)) | ~r1_tarski(B_272, C_271) | ~m1_subset_1(C_271, k1_zfmisc_1(u1_struct_0(A_270))) | ~m1_subset_1(B_272, k1_zfmisc_1(u1_struct_0(A_270))) | ~l1_pre_topc(A_270))), inference(resolution, [status(thm)], [c_1716, c_2])).
% 28.88/19.07  tff(c_7775, plain, (![C_129]: (k1_tops_1('#skF_1', C_129)=k1_tops_1('#skF_1', '#skF_2') | ~r1_tarski(C_129, '#skF_2') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1') | ~r1_tarski(k1_tops_1('#skF_1', '#skF_2'), C_129) | ~m1_subset_1(C_129, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(resolution, [status(thm)], [c_1761, c_7748])).
% 28.88/19.07  tff(c_9732, plain, (![C_308]: (k1_tops_1('#skF_1', C_308)=k1_tops_1('#skF_1', '#skF_2') | ~r1_tarski(C_308, '#skF_2') | ~r1_tarski(k1_tops_1('#skF_1', '#skF_2'), C_308) | ~m1_subset_1(C_308, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_7775])).
% 28.88/19.07  tff(c_9764, plain, (![A_6]: (k1_tops_1('#skF_1', A_6)=k1_tops_1('#skF_1', '#skF_2') | ~r1_tarski(A_6, '#skF_2') | ~r1_tarski(k1_tops_1('#skF_1', '#skF_2'), A_6) | ~r1_tarski(A_6, u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_12, c_9732])).
% 28.88/19.07  tff(c_31903, plain, (k1_tops_1('#skF_1', k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_2')))=k1_tops_1('#skF_1', '#skF_2') | ~r1_tarski(k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_2')), '#skF_2') | ~r1_tarski(k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_2')), u1_struct_0('#skF_1')) | ~m1_subset_1(k2_pre_topc('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~r1_tarski('#skF_2', '#skF_2') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_31857, c_9764])).
% 28.88/19.07  tff(c_32014, plain, (k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_2'))=k1_tops_1('#skF_1', '#skF_2') | ~r1_tarski(k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_2')), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_6, c_2503, c_10599, c_2524, c_31903])).
% 28.88/19.07  tff(c_35463, plain, (k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_2'))=k1_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_34864, c_32014])).
% 28.88/19.07  tff(c_1635, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_2'), k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2')))), inference(splitRight, [status(thm)], [c_1503])).
% 28.88/19.07  tff(c_1948, plain, (![B_134, A_135]: (v4_tops_1(B_134, A_135) | ~r1_tarski(B_134, k2_pre_topc(A_135, k1_tops_1(A_135, B_134))) | ~r1_tarski(k1_tops_1(A_135, k2_pre_topc(A_135, B_134)), B_134) | ~m1_subset_1(B_134, k1_zfmisc_1(u1_struct_0(A_135))) | ~l1_pre_topc(A_135))), inference(cnfTransformation, [status(thm)], [f_83])).
% 28.88/19.07  tff(c_2002, plain, (![A_29, C_35]: (v4_tops_1(k1_tops_1(A_29, C_35), A_29) | ~r1_tarski(k1_tops_1(A_29, C_35), k2_pre_topc(A_29, k1_tops_1(A_29, k1_tops_1(A_29, C_35)))) | ~m1_subset_1(k1_tops_1(A_29, C_35), k1_zfmisc_1(u1_struct_0(A_29))) | ~r1_tarski(k2_pre_topc(A_29, k1_tops_1(A_29, C_35)), C_35) | ~m1_subset_1(C_35, k1_zfmisc_1(u1_struct_0(A_29))) | ~m1_subset_1(k2_pre_topc(A_29, k1_tops_1(A_29, C_35)), k1_zfmisc_1(u1_struct_0(A_29))) | ~l1_pre_topc(A_29))), inference(resolution, [status(thm)], [c_32, c_1948])).
% 28.88/19.07  tff(c_35617, plain, (v4_tops_1(k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_2')), '#skF_1') | ~r1_tarski(k1_tops_1('#skF_1', '#skF_2'), k2_pre_topc('#skF_1', k1_tops_1('#skF_1', k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_2'))))) | ~m1_subset_1(k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_2')), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~r1_tarski(k2_pre_topc('#skF_1', k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_2'))), k2_pre_topc('#skF_1', '#skF_2')) | ~m1_subset_1(k2_pre_topc('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1(k2_pre_topc('#skF_1', k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_2'))), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_35463, c_2002])).
% 28.88/19.07  tff(c_35794, plain, (v4_tops_1(k1_tops_1('#skF_1', '#skF_2'), '#skF_1') | ~r1_tarski(k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2')), k2_pre_topc('#skF_1', '#skF_2')) | ~m1_subset_1(k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2')), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_35463, c_2503, c_35463, c_1636, c_35463, c_1635, c_441, c_35463, c_35463, c_35617])).
% 28.88/19.07  tff(c_35795, plain, (~r1_tarski(k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2')), k2_pre_topc('#skF_1', '#skF_2')) | ~m1_subset_1(k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2')), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(negUnitSimplification, [status(thm)], [c_64, c_35794])).
% 28.88/19.07  tff(c_36078, plain, (~m1_subset_1(k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2')), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitLeft, [status(thm)], [c_35795])).
% 28.88/19.07  tff(c_36081, plain, (~m1_subset_1(k1_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_14, c_36078])).
% 28.88/19.07  tff(c_36088, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_40, c_1636, c_36081])).
% 28.88/19.07  tff(c_36089, plain, (~r1_tarski(k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2')), k2_pre_topc('#skF_1', '#skF_2'))), inference(splitRight, [status(thm)], [c_35795])).
% 28.88/19.07  tff(c_36364, plain, (~r1_tarski(k1_tops_1('#skF_1', '#skF_2'), '#skF_2') | ~m1_subset_1(k1_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_34010, c_36089])).
% 28.88/19.07  tff(c_36386, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1636, c_29433, c_36364])).
% 28.88/19.07  tff(c_36387, plain, (~v4_tops_1(k2_pre_topc('#skF_1', '#skF_2'), '#skF_1')), inference(splitRight, [status(thm)], [c_34])).
% 28.88/19.07  tff(c_36388, plain, (v4_tops_1(k1_tops_1('#skF_1', '#skF_2'), '#skF_1')), inference(splitRight, [status(thm)], [c_34])).
% 28.88/19.07  tff(c_36611, plain, (![A_612, B_613]: (k1_tops_1(A_612, k1_tops_1(A_612, B_613))=k1_tops_1(A_612, B_613) | ~m1_subset_1(B_613, k1_zfmisc_1(u1_struct_0(A_612))) | ~l1_pre_topc(A_612))), inference(cnfTransformation, [status(thm)], [f_95])).
% 28.88/19.07  tff(c_36620, plain, (k1_tops_1('#skF_1', k1_tops_1('#skF_1', '#skF_2'))=k1_tops_1('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_38, c_36611])).
% 28.88/19.07  tff(c_36626, plain, (k1_tops_1('#skF_1', k1_tops_1('#skF_1', '#skF_2'))=k1_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_36620])).
% 28.88/19.07  tff(c_37200, plain, (![B_641, A_642]: (r1_tarski(B_641, k2_pre_topc(A_642, k1_tops_1(A_642, B_641))) | ~v4_tops_1(B_641, A_642) | ~m1_subset_1(B_641, k1_zfmisc_1(u1_struct_0(A_642))) | ~l1_pre_topc(A_642))), inference(cnfTransformation, [status(thm)], [f_83])).
% 28.88/19.07  tff(c_37238, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_2'), k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2'))) | ~v4_tops_1(k1_tops_1('#skF_1', '#skF_2'), '#skF_1') | ~m1_subset_1(k1_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_36626, c_37200])).
% 28.88/19.07  tff(c_37252, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_2'), k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2'))) | ~m1_subset_1(k1_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_36388, c_37238])).
% 28.88/19.07  tff(c_37895, plain, (~m1_subset_1(k1_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitLeft, [status(thm)], [c_37252])).
% 28.88/19.07  tff(c_37898, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_28, c_37895])).
% 28.88/19.07  tff(c_37905, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_37898])).
% 28.88/19.07  tff(c_37907, plain, (m1_subset_1(k1_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitRight, [status(thm)], [c_37252])).
% 28.88/19.07  tff(c_37906, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_2'), k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2')))), inference(splitRight, [status(thm)], [c_37252])).
% 28.88/19.07  tff(c_37501, plain, (![A_652, B_653, C_654]: (r1_tarski(k1_tops_1(A_652, B_653), k1_tops_1(A_652, C_654)) | ~r1_tarski(B_653, C_654) | ~m1_subset_1(C_654, k1_zfmisc_1(u1_struct_0(A_652))) | ~m1_subset_1(B_653, k1_zfmisc_1(u1_struct_0(A_652))) | ~l1_pre_topc(A_652))), inference(cnfTransformation, [status(thm)], [f_107])).
% 28.88/19.07  tff(c_42780, plain, (![A_772, C_773, B_774]: (k1_tops_1(A_772, C_773)=k1_tops_1(A_772, B_774) | ~r1_tarski(k1_tops_1(A_772, C_773), k1_tops_1(A_772, B_774)) | ~r1_tarski(B_774, C_773) | ~m1_subset_1(C_773, k1_zfmisc_1(u1_struct_0(A_772))) | ~m1_subset_1(B_774, k1_zfmisc_1(u1_struct_0(A_772))) | ~l1_pre_topc(A_772))), inference(resolution, [status(thm)], [c_37501, c_2])).
% 28.88/19.07  tff(c_42817, plain, (![C_773]: (k1_tops_1('#skF_1', k1_tops_1('#skF_1', '#skF_2'))=k1_tops_1('#skF_1', C_773) | ~r1_tarski(k1_tops_1('#skF_1', C_773), k1_tops_1('#skF_1', '#skF_2')) | ~r1_tarski(k1_tops_1('#skF_1', '#skF_2'), C_773) | ~m1_subset_1(C_773, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1(k1_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_36626, c_42780])).
% 28.88/19.07  tff(c_64347, plain, (![C_1021]: (k1_tops_1('#skF_1', C_1021)=k1_tops_1('#skF_1', '#skF_2') | ~r1_tarski(k1_tops_1('#skF_1', C_1021), k1_tops_1('#skF_1', '#skF_2')) | ~r1_tarski(k1_tops_1('#skF_1', '#skF_2'), C_1021) | ~m1_subset_1(C_1021, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_37907, c_36626, c_42817])).
% 28.88/19.07  tff(c_64408, plain, (k1_tops_1('#skF_1', k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2')))=k1_tops_1('#skF_1', '#skF_2') | ~r1_tarski(k1_tops_1('#skF_1', '#skF_2'), k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2'))) | ~m1_subset_1(k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2')), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~v4_tops_1(k1_tops_1('#skF_1', '#skF_2'), '#skF_1') | ~m1_subset_1(k1_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_26, c_64347])).
% 28.88/19.07  tff(c_64457, plain, (k1_tops_1('#skF_1', k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2')))=k1_tops_1('#skF_1', '#skF_2') | ~m1_subset_1(k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2')), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_37907, c_36388, c_37906, c_64408])).
% 28.88/19.07  tff(c_72730, plain, (~m1_subset_1(k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2')), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitLeft, [status(thm)], [c_64457])).
% 28.88/19.07  tff(c_72733, plain, (~m1_subset_1(k1_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_14, c_72730])).
% 28.88/19.07  tff(c_72740, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_40, c_37907, c_72733])).
% 28.88/19.07  tff(c_72742, plain, (m1_subset_1(k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2')), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitRight, [status(thm)], [c_64457])).
% 28.88/19.07  tff(c_72889, plain, (r1_tarski(k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2')), u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_72742, c_10])).
% 28.88/19.07  tff(c_16, plain, (![A_10, B_11]: (k2_pre_topc(A_10, k2_pre_topc(A_10, B_11))=k2_pre_topc(A_10, B_11) | ~m1_subset_1(B_11, k1_zfmisc_1(u1_struct_0(A_10))) | ~l1_pre_topc(A_10))), inference(cnfTransformation, [status(thm)], [f_53])).
% 28.88/19.07  tff(c_38003, plain, (k2_pre_topc('#skF_1', k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2')))=k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2')) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_37907, c_16])).
% 28.88/19.07  tff(c_38013, plain, (k2_pre_topc('#skF_1', k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2')))=k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38003])).
% 28.88/19.07  tff(c_24, plain, (![B_24, A_22]: (r1_tarski(B_24, k2_pre_topc(A_22, k1_tops_1(A_22, B_24))) | ~v4_tops_1(B_24, A_22) | ~m1_subset_1(B_24, k1_zfmisc_1(u1_struct_0(A_22))) | ~l1_pre_topc(A_22))), inference(cnfTransformation, [status(thm)], [f_83])).
% 28.88/19.07  tff(c_37908, plain, (![A_666, B_667, C_668]: (r1_tarski(k2_pre_topc(A_666, B_667), k2_pre_topc(A_666, C_668)) | ~r1_tarski(B_667, C_668) | ~m1_subset_1(C_668, k1_zfmisc_1(u1_struct_0(A_666))) | ~m1_subset_1(B_667, k1_zfmisc_1(u1_struct_0(A_666))) | ~l1_pre_topc(A_666))), inference(cnfTransformation, [status(thm)], [f_72])).
% 28.88/19.07  tff(c_41655, plain, (![A_744, A_745, C_746, B_747]: (r1_tarski(A_744, k2_pre_topc(A_745, C_746)) | ~r1_tarski(A_744, k2_pre_topc(A_745, B_747)) | ~r1_tarski(B_747, C_746) | ~m1_subset_1(C_746, k1_zfmisc_1(u1_struct_0(A_745))) | ~m1_subset_1(B_747, k1_zfmisc_1(u1_struct_0(A_745))) | ~l1_pre_topc(A_745))), inference(resolution, [status(thm)], [c_37908, c_8])).
% 28.88/19.07  tff(c_84698, plain, (![B_1204, A_1205, C_1206]: (r1_tarski(B_1204, k2_pre_topc(A_1205, C_1206)) | ~r1_tarski(k1_tops_1(A_1205, B_1204), C_1206) | ~m1_subset_1(C_1206, k1_zfmisc_1(u1_struct_0(A_1205))) | ~m1_subset_1(k1_tops_1(A_1205, B_1204), k1_zfmisc_1(u1_struct_0(A_1205))) | ~v4_tops_1(B_1204, A_1205) | ~m1_subset_1(B_1204, k1_zfmisc_1(u1_struct_0(A_1205))) | ~l1_pre_topc(A_1205))), inference(resolution, [status(thm)], [c_24, c_41655])).
% 28.88/19.07  tff(c_84879, plain, (r1_tarski('#skF_2', k2_pre_topc('#skF_1', k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2')))) | ~m1_subset_1(k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2')), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1(k1_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~v4_tops_1('#skF_2', '#skF_1') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_37906, c_84698])).
% 28.88/19.07  tff(c_85101, plain, (r1_tarski('#skF_2', k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_36, c_37907, c_72742, c_38013, c_84879])).
% 28.88/19.07  tff(c_36425, plain, (![B_591, A_592]: (r1_tarski(B_591, k2_pre_topc(A_592, B_591)) | ~m1_subset_1(B_591, k1_zfmisc_1(u1_struct_0(A_592))) | ~l1_pre_topc(A_592))), inference(cnfTransformation, [status(thm)], [f_60])).
% 28.88/19.07  tff(c_36430, plain, (r1_tarski('#skF_2', k2_pre_topc('#skF_1', '#skF_2')) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_38, c_36425])).
% 28.88/19.07  tff(c_36434, plain, (r1_tarski('#skF_2', k2_pre_topc('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_36430])).
% 28.88/19.07  tff(c_36862, plain, (![A_625, B_626]: (k2_pre_topc(A_625, k2_pre_topc(A_625, B_626))=k2_pre_topc(A_625, B_626) | ~m1_subset_1(B_626, k1_zfmisc_1(u1_struct_0(A_625))) | ~l1_pre_topc(A_625))), inference(cnfTransformation, [status(thm)], [f_53])).
% 28.88/19.07  tff(c_36871, plain, (k2_pre_topc('#skF_1', k2_pre_topc('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_38, c_36862])).
% 28.88/19.07  tff(c_36877, plain, (k2_pre_topc('#skF_1', k2_pre_topc('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_36871])).
% 28.88/19.07  tff(c_38203, plain, (![B_671, A_672]: (v4_tops_1(B_671, A_672) | ~r1_tarski(B_671, k2_pre_topc(A_672, k1_tops_1(A_672, B_671))) | ~r1_tarski(k1_tops_1(A_672, k2_pre_topc(A_672, B_671)), B_671) | ~m1_subset_1(B_671, k1_zfmisc_1(u1_struct_0(A_672))) | ~l1_pre_topc(A_672))), inference(cnfTransformation, [status(thm)], [f_83])).
% 28.88/19.07  tff(c_38226, plain, (v4_tops_1(k2_pre_topc('#skF_1', '#skF_2'), '#skF_1') | ~r1_tarski(k2_pre_topc('#skF_1', '#skF_2'), k2_pre_topc('#skF_1', k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_2')))) | ~r1_tarski(k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_2')), k2_pre_topc('#skF_1', '#skF_2')) | ~m1_subset_1(k2_pre_topc('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_36877, c_38203])).
% 28.88/19.07  tff(c_38257, plain, (v4_tops_1(k2_pre_topc('#skF_1', '#skF_2'), '#skF_1') | ~r1_tarski(k2_pre_topc('#skF_1', '#skF_2'), k2_pre_topc('#skF_1', k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_2')))) | ~r1_tarski(k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_2')), k2_pre_topc('#skF_1', '#skF_2')) | ~m1_subset_1(k2_pre_topc('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38226])).
% 28.88/19.07  tff(c_38258, plain, (~r1_tarski(k2_pre_topc('#skF_1', '#skF_2'), k2_pre_topc('#skF_1', k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_2')))) | ~r1_tarski(k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_2')), k2_pre_topc('#skF_1', '#skF_2')) | ~m1_subset_1(k2_pre_topc('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(negUnitSimplification, [status(thm)], [c_36387, c_38257])).
% 28.88/19.07  tff(c_38346, plain, (~m1_subset_1(k2_pre_topc('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitLeft, [status(thm)], [c_38258])).
% 28.88/19.07  tff(c_38349, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_14, c_38346])).
% 28.88/19.07  tff(c_38356, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_38349])).
% 28.88/19.07  tff(c_38358, plain, (m1_subset_1(k2_pre_topc('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitRight, [status(thm)], [c_38258])).
% 28.88/19.07  tff(c_38377, plain, (r1_tarski(k2_pre_topc('#skF_1', '#skF_2'), u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_38358, c_10])).
% 28.88/19.07  tff(c_36389, plain, (![A_584, C_585, B_586]: (r1_tarski(A_584, C_585) | ~r1_tarski(B_586, C_585) | ~r1_tarski(A_584, B_586))), inference(cnfTransformation, [status(thm)], [f_37])).
% 28.88/19.07  tff(c_36394, plain, (![A_584]: (r1_tarski(A_584, u1_struct_0('#skF_1')) | ~r1_tarski(A_584, '#skF_2'))), inference(resolution, [status(thm)], [c_47, c_36389])).
% 28.88/19.07  tff(c_36469, plain, (![A_596, A_597]: (r1_tarski(A_596, k2_pre_topc(A_597, A_596)) | ~l1_pre_topc(A_597) | ~r1_tarski(A_596, u1_struct_0(A_597)))), inference(resolution, [status(thm)], [c_12, c_36425])).
% 28.88/19.07  tff(c_36567, plain, (![A_607, A_608, A_609]: (r1_tarski(A_607, k2_pre_topc(A_608, A_609)) | ~r1_tarski(A_607, A_609) | ~l1_pre_topc(A_608) | ~r1_tarski(A_609, u1_struct_0(A_608)))), inference(resolution, [status(thm)], [c_36469, c_8])).
% 28.88/19.07  tff(c_36573, plain, (![A_607, A_584]: (r1_tarski(A_607, k2_pre_topc('#skF_1', A_584)) | ~r1_tarski(A_607, A_584) | ~l1_pre_topc('#skF_1') | ~r1_tarski(A_584, '#skF_2'))), inference(resolution, [status(thm)], [c_36394, c_36567])).
% 28.88/19.07  tff(c_36588, plain, (![A_610, A_611]: (r1_tarski(A_610, k2_pre_topc('#skF_1', A_611)) | ~r1_tarski(A_610, A_611) | ~r1_tarski(A_611, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_36573])).
% 28.88/19.07  tff(c_36609, plain, (![A_3, A_611, A_610]: (r1_tarski(A_3, k2_pre_topc('#skF_1', A_611)) | ~r1_tarski(A_3, A_610) | ~r1_tarski(A_610, A_611) | ~r1_tarski(A_611, '#skF_2'))), inference(resolution, [status(thm)], [c_36588, c_8])).
% 28.88/19.07  tff(c_38422, plain, (![A_611]: (r1_tarski(k2_pre_topc('#skF_1', '#skF_2'), k2_pre_topc('#skF_1', A_611)) | ~r1_tarski(u1_struct_0('#skF_1'), A_611) | ~r1_tarski(A_611, '#skF_2'))), inference(resolution, [status(thm)], [c_38377, c_36609])).
% 28.88/19.07  tff(c_38357, plain, (~r1_tarski(k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_2')), k2_pre_topc('#skF_1', '#skF_2')) | ~r1_tarski(k2_pre_topc('#skF_1', '#skF_2'), k2_pre_topc('#skF_1', k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_2'))))), inference(splitRight, [status(thm)], [c_38258])).
% 28.88/19.07  tff(c_39233, plain, (~r1_tarski(k2_pre_topc('#skF_1', '#skF_2'), k2_pre_topc('#skF_1', k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_2'))))), inference(splitLeft, [status(thm)], [c_38357])).
% 28.88/19.07  tff(c_39246, plain, (~r1_tarski(u1_struct_0('#skF_1'), k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_2'))) | ~r1_tarski(k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_2')), '#skF_2')), inference(resolution, [status(thm)], [c_38422, c_39233])).
% 28.88/19.07  tff(c_39254, plain, (~r1_tarski(k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_2')), '#skF_2')), inference(splitLeft, [status(thm)], [c_39246])).
% 28.88/19.07  tff(c_39257, plain, (~v4_tops_1('#skF_2', '#skF_1') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_26, c_39254])).
% 28.88/19.07  tff(c_39261, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_36, c_39257])).
% 28.88/19.07  tff(c_39263, plain, (r1_tarski(k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_2')), '#skF_2')), inference(splitRight, [status(thm)], [c_39246])).
% 28.88/19.07  tff(c_39397, plain, (![A_695]: (r1_tarski(A_695, '#skF_2') | ~r1_tarski(A_695, k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_2'))))), inference(resolution, [status(thm)], [c_39263, c_8])).
% 28.88/19.07  tff(c_39401, plain, (![B_33]: (r1_tarski(k1_tops_1('#skF_1', B_33), '#skF_2') | ~r1_tarski(B_33, k2_pre_topc('#skF_1', '#skF_2')) | ~m1_subset_1(k2_pre_topc('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1(B_33, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_32, c_39397])).
% 28.88/19.07  tff(c_39712, plain, (![B_704]: (r1_tarski(k1_tops_1('#skF_1', B_704), '#skF_2') | ~r1_tarski(B_704, k2_pre_topc('#skF_1', '#skF_2')) | ~m1_subset_1(B_704, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38358, c_39401])).
% 28.88/19.07  tff(c_39733, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_2'), '#skF_2') | ~r1_tarski('#skF_2', k2_pre_topc('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_38, c_39712])).
% 28.88/19.07  tff(c_39748, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_36434, c_39733])).
% 28.88/19.07  tff(c_73779, plain, (![A_1128, B_1129, C_1130, C_1131]: (r1_tarski(k2_pre_topc(A_1128, B_1129), k2_pre_topc(A_1128, C_1130)) | ~r1_tarski(C_1131, C_1130) | ~m1_subset_1(C_1130, k1_zfmisc_1(u1_struct_0(A_1128))) | ~r1_tarski(B_1129, C_1131) | ~m1_subset_1(C_1131, k1_zfmisc_1(u1_struct_0(A_1128))) | ~m1_subset_1(B_1129, k1_zfmisc_1(u1_struct_0(A_1128))) | ~l1_pre_topc(A_1128))), inference(resolution, [status(thm)], [c_20, c_41655])).
% 28.88/19.07  tff(c_82976, plain, (![A_1190, B_1191]: (r1_tarski(k2_pre_topc(A_1190, B_1191), k2_pre_topc(A_1190, '#skF_2')) | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0(A_1190))) | ~r1_tarski(B_1191, k1_tops_1('#skF_1', '#skF_2')) | ~m1_subset_1(k1_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0(A_1190))) | ~m1_subset_1(B_1191, k1_zfmisc_1(u1_struct_0(A_1190))) | ~l1_pre_topc(A_1190))), inference(resolution, [status(thm)], [c_39748, c_73779])).
% 28.88/19.07  tff(c_82978, plain, (![B_1191]: (r1_tarski(k2_pre_topc('#skF_1', B_1191), k2_pre_topc('#skF_1', '#skF_2')) | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~r1_tarski(B_1191, k1_tops_1('#skF_1', '#skF_2')) | ~m1_subset_1(B_1191, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_37907, c_82976])).
% 28.88/19.07  tff(c_82987, plain, (![B_1191]: (r1_tarski(k2_pre_topc('#skF_1', B_1191), k2_pre_topc('#skF_1', '#skF_2')) | ~r1_tarski(B_1191, k1_tops_1('#skF_1', '#skF_2')) | ~m1_subset_1(B_1191, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_82978])).
% 28.88/19.07  tff(c_72741, plain, (k1_tops_1('#skF_1', k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2')))=k1_tops_1('#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_64457])).
% 28.88/19.07  tff(c_39745, plain, (![A_6]: (r1_tarski(k1_tops_1('#skF_1', A_6), '#skF_2') | ~r1_tarski(A_6, k2_pre_topc('#skF_1', '#skF_2')) | ~r1_tarski(A_6, u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_12, c_39712])).
% 28.88/19.07  tff(c_85229, plain, (![A_1207]: (r1_tarski(A_1207, k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2'))) | ~r1_tarski(A_1207, '#skF_2'))), inference(resolution, [status(thm)], [c_85101, c_8])).
% 28.88/19.07  tff(c_85565, plain, (![A_1208, A_1209]: (r1_tarski(A_1208, k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2'))) | ~r1_tarski(A_1208, A_1209) | ~r1_tarski(A_1209, '#skF_2'))), inference(resolution, [status(thm)], [c_85229, c_8])).
% 28.88/19.07  tff(c_85741, plain, (![A_6]: (r1_tarski(k1_tops_1('#skF_1', A_6), k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2'))) | ~r1_tarski('#skF_2', '#skF_2') | ~r1_tarski(A_6, k2_pre_topc('#skF_1', '#skF_2')) | ~r1_tarski(A_6, u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_39745, c_85565])).
% 28.88/19.07  tff(c_93975, plain, (![A_1268]: (r1_tarski(k1_tops_1('#skF_1', A_1268), k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2'))) | ~r1_tarski(A_1268, k2_pre_topc('#skF_1', '#skF_2')) | ~r1_tarski(A_1268, u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_85741])).
% 28.88/19.07  tff(c_22, plain, (![B_24, A_22]: (v4_tops_1(B_24, A_22) | ~r1_tarski(B_24, k2_pre_topc(A_22, k1_tops_1(A_22, B_24))) | ~r1_tarski(k1_tops_1(A_22, k2_pre_topc(A_22, B_24)), B_24) | ~m1_subset_1(B_24, k1_zfmisc_1(u1_struct_0(A_22))) | ~l1_pre_topc(A_22))), inference(cnfTransformation, [status(thm)], [f_83])).
% 28.88/19.07  tff(c_94057, plain, (v4_tops_1(k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2')), '#skF_1') | ~r1_tarski(k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2')), k2_pre_topc('#skF_1', k1_tops_1('#skF_1', k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2'))))) | ~m1_subset_1(k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2')), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1') | ~r1_tarski(k2_pre_topc('#skF_1', k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2'))), k2_pre_topc('#skF_1', '#skF_2')) | ~r1_tarski(k2_pre_topc('#skF_1', k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2'))), u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_93975, c_22])).
% 28.88/19.07  tff(c_94198, plain, (v4_tops_1(k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2')), '#skF_1') | ~r1_tarski(k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2')), k2_pre_topc('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_72889, c_38013, c_38013, c_40, c_72742, c_6, c_72741, c_94057])).
% 28.88/19.07  tff(c_94239, plain, (~r1_tarski(k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2')), k2_pre_topc('#skF_1', '#skF_2'))), inference(splitLeft, [status(thm)], [c_94198])).
% 28.88/19.07  tff(c_94242, plain, (~r1_tarski(k1_tops_1('#skF_1', '#skF_2'), k1_tops_1('#skF_1', '#skF_2')) | ~m1_subset_1(k1_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_82987, c_94239])).
% 28.88/19.07  tff(c_94273, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_37907, c_6, c_94242])).
% 28.88/19.07  tff(c_94275, plain, (r1_tarski(k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2')), k2_pre_topc('#skF_1', '#skF_2'))), inference(splitRight, [status(thm)], [c_94198])).
% 28.88/19.07  tff(c_43039, plain, (![A_781, C_782, B_783]: (k2_pre_topc(A_781, C_782)=k2_pre_topc(A_781, B_783) | ~r1_tarski(k2_pre_topc(A_781, C_782), k2_pre_topc(A_781, B_783)) | ~r1_tarski(B_783, C_782) | ~m1_subset_1(C_782, k1_zfmisc_1(u1_struct_0(A_781))) | ~m1_subset_1(B_783, k1_zfmisc_1(u1_struct_0(A_781))) | ~l1_pre_topc(A_781))), inference(resolution, [status(thm)], [c_37908, c_2])).
% 28.88/19.07  tff(c_43113, plain, (![B_783]: (k2_pre_topc('#skF_1', k2_pre_topc('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', B_783) | ~r1_tarski(k2_pre_topc('#skF_1', '#skF_2'), k2_pre_topc('#skF_1', B_783)) | ~r1_tarski(B_783, k2_pre_topc('#skF_1', '#skF_2')) | ~m1_subset_1(k2_pre_topc('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1(B_783, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_36877, c_43039])).
% 28.88/19.07  tff(c_63215, plain, (![B_1015]: (k2_pre_topc('#skF_1', B_1015)=k2_pre_topc('#skF_1', '#skF_2') | ~r1_tarski(k2_pre_topc('#skF_1', '#skF_2'), k2_pre_topc('#skF_1', B_1015)) | ~r1_tarski(B_1015, k2_pre_topc('#skF_1', '#skF_2')) | ~m1_subset_1(B_1015, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38358, c_36877, c_43113])).
% 28.88/19.07  tff(c_63313, plain, (![C_21]: (k2_pre_topc('#skF_1', C_21)=k2_pre_topc('#skF_1', '#skF_2') | ~r1_tarski(C_21, k2_pre_topc('#skF_1', '#skF_2')) | ~r1_tarski('#skF_2', C_21) | ~m1_subset_1(C_21, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_20, c_63215])).
% 28.88/19.07  tff(c_71877, plain, (![C_1116]: (k2_pre_topc('#skF_1', C_1116)=k2_pre_topc('#skF_1', '#skF_2') | ~r1_tarski(C_1116, k2_pre_topc('#skF_1', '#skF_2')) | ~r1_tarski('#skF_2', C_1116) | ~m1_subset_1(C_1116, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_63313])).
% 28.88/19.07  tff(c_71917, plain, (![A_6]: (k2_pre_topc('#skF_1', A_6)=k2_pre_topc('#skF_1', '#skF_2') | ~r1_tarski(A_6, k2_pre_topc('#skF_1', '#skF_2')) | ~r1_tarski('#skF_2', A_6) | ~r1_tarski(A_6, u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_12, c_71877])).
% 28.88/19.07  tff(c_94654, plain, (k2_pre_topc('#skF_1', k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2')))=k2_pre_topc('#skF_1', '#skF_2') | ~r1_tarski('#skF_2', k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2'))) | ~r1_tarski(k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2')), u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_94275, c_71917])).
% 28.88/19.07  tff(c_94748, plain, (k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_72889, c_85101, c_38013, c_94654])).
% 28.88/19.07  tff(c_94274, plain, (v4_tops_1(k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2')), '#skF_1')), inference(splitRight, [status(thm)], [c_94198])).
% 28.88/19.07  tff(c_94811, plain, (v4_tops_1(k2_pre_topc('#skF_1', '#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_94748, c_94274])).
% 28.88/19.07  tff(c_94848, plain, $false, inference(negUnitSimplification, [status(thm)], [c_36387, c_94811])).
% 28.88/19.07  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 28.88/19.07  
% 28.88/19.07  Inference rules
% 28.88/19.07  ----------------------
% 28.88/19.07  #Ref     : 0
% 28.88/19.07  #Sup     : 21565
% 28.88/19.07  #Fact    : 0
% 28.88/19.07  #Define  : 0
% 28.88/19.07  #Split   : 63
% 28.88/19.07  #Chain   : 0
% 28.88/19.07  #Close   : 0
% 28.88/19.07  
% 28.88/19.07  Ordering : KBO
% 28.88/19.07  
% 28.88/19.07  Simplification rules
% 28.88/19.07  ----------------------
% 28.88/19.07  #Subsume      : 8651
% 28.88/19.07  #Demod        : 21420
% 28.88/19.07  #Tautology    : 3476
% 28.88/19.07  #SimpNegUnit  : 202
% 28.88/19.07  #BackRed      : 152
% 28.88/19.07  
% 28.88/19.07  #Partial instantiations: 0
% 28.88/19.07  #Strategies tried      : 1
% 28.88/19.07  
% 28.88/19.07  Timing (in seconds)
% 28.88/19.07  ----------------------
% 28.88/19.07  Preprocessing        : 0.32
% 28.88/19.07  Parsing              : 0.18
% 28.88/19.07  CNF conversion       : 0.02
% 28.88/19.07  Main loop            : 17.94
% 28.88/19.07  Inferencing          : 2.28
% 28.88/19.07  Reduction            : 4.21
% 28.88/19.07  Demodulation         : 3.08
% 28.88/19.07  BG Simplification    : 0.26
% 28.88/19.07  Subsumption          : 10.49
% 28.88/19.07  Abstraction          : 0.51
% 28.88/19.07  MUC search           : 0.00
% 28.88/19.07  Cooper               : 0.00
% 28.88/19.07  Total                : 18.35
% 28.88/19.07  Index Insertion      : 0.00
% 28.88/19.07  Index Deletion       : 0.00
% 28.88/19.07  Index Matching       : 0.00
% 28.88/19.07  BG Taut test         : 0.00
%------------------------------------------------------------------------------
