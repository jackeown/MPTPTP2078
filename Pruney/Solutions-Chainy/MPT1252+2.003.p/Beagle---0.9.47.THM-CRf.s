%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:20:52 EST 2020

% Result     : Theorem 5.32s
% Output     : CNFRefutation 5.32s
% Verified   : 
% Statistics : Number of formulae       :  110 ( 841 expanded)
%              Number of leaves         :   27 ( 283 expanded)
%              Depth                    :   25
%              Number of atoms          :  205 (1893 expanded)
%              Number of equality atoms :   22 ( 209 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > m1_subset_1 > l1_pre_topc > k9_subset_1 > k4_subset_1 > k3_subset_1 > k2_tops_1 > k2_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k2_tops_1,type,(
    k2_tops_1: ( $i * $i ) > $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff(k4_subset_1,type,(
    k4_subset_1: ( $i * $i * $i ) > $i )).

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

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_108,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => r1_tarski(k2_tops_1(A,k2_tops_1(A,B)),k2_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t68_tops_1)).

tff(f_93,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_tops_1(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tops_1)).

tff(f_100,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_pre_topc(A,B) = k4_subset_1(u1_struct_0(A),B,k2_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_tops_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(A))
         => r1_tarski(k3_subset_1(A,k4_subset_1(A,B,C)),k3_subset_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_subset_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k3_subset_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).

tff(f_64,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_pre_topc(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_pre_topc)).

tff(f_44,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(A))
         => ( r1_tarski(B,C)
          <=> r1_tarski(k3_subset_1(A,C),k3_subset_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_subset_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_87,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_tops_1(A,B) = k9_subset_1(u1_struct_0(A),k2_pre_topc(A,B),k2_pre_topc(A,k3_subset_1(u1_struct_0(A),B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tops_1)).

tff(f_70,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => k2_pre_topc(A,k2_pre_topc(A,B)) = k2_pre_topc(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',projectivity_k2_pre_topc)).

tff(f_80,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => r1_tarski(k2_pre_topc(A,k9_subset_1(u1_struct_0(A),B,C)),k9_subset_1(u1_struct_0(A),k2_pre_topc(A,B),k2_pre_topc(A,C))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_pre_topc)).

tff(f_58,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(A))
         => r1_tarski(k3_subset_1(A,B),k3_subset_1(A,k9_subset_1(A,B,C))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_subset_1)).

tff(c_34,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_32,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_26,plain,(
    ! [A_31,B_32] :
      ( m1_subset_1(k2_tops_1(A_31,B_32),k1_zfmisc_1(u1_struct_0(A_31)))
      | ~ m1_subset_1(B_32,k1_zfmisc_1(u1_struct_0(A_31)))
      | ~ l1_pre_topc(A_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_72,plain,(
    ! [A_48,B_49] :
      ( k4_subset_1(u1_struct_0(A_48),B_49,k2_tops_1(A_48,B_49)) = k2_pre_topc(A_48,B_49)
      | ~ m1_subset_1(B_49,k1_zfmisc_1(u1_struct_0(A_48)))
      | ~ l1_pre_topc(A_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_81,plain,
    ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_72])).

tff(c_87,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_81])).

tff(c_96,plain,(
    ! [A_53,B_54,C_55] :
      ( r1_tarski(k3_subset_1(A_53,k4_subset_1(A_53,B_54,C_55)),k3_subset_1(A_53,B_54))
      | ~ m1_subset_1(C_55,k1_zfmisc_1(A_53))
      | ~ m1_subset_1(B_54,k1_zfmisc_1(A_53)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_101,plain,
    ( r1_tarski(k3_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2')),k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'))
    | ~ m1_subset_1(k2_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_87,c_96])).

tff(c_104,plain,
    ( r1_tarski(k3_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2')),k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'))
    | ~ m1_subset_1(k2_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_101])).

tff(c_128,plain,(
    ~ m1_subset_1(k2_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_104])).

tff(c_131,plain,
    ( ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_26,c_128])).

tff(c_135,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_131])).

tff(c_137,plain,(
    m1_subset_1(k2_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_104])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( m1_subset_1(k3_subset_1(A_3,B_4),k1_zfmisc_1(A_3))
      | ~ m1_subset_1(B_4,k1_zfmisc_1(A_3)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_18,plain,(
    ! [A_17,B_18] :
      ( m1_subset_1(k2_pre_topc(A_17,B_18),k1_zfmisc_1(u1_struct_0(A_17)))
      | ~ m1_subset_1(B_18,k1_zfmisc_1(u1_struct_0(A_17)))
      | ~ l1_pre_topc(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_30,plain,(
    ~ r1_tarski(k2_tops_1('#skF_1',k2_tops_1('#skF_1','#skF_2')),k2_tops_1('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_28,plain,(
    ! [A_33,B_35] :
      ( k4_subset_1(u1_struct_0(A_33),B_35,k2_tops_1(A_33,B_35)) = k2_pre_topc(A_33,B_35)
      | ~ m1_subset_1(B_35,k1_zfmisc_1(u1_struct_0(A_33)))
      | ~ l1_pre_topc(A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_139,plain,
    ( k4_subset_1(u1_struct_0('#skF_1'),k2_tops_1('#skF_1','#skF_2'),k2_tops_1('#skF_1',k2_tops_1('#skF_1','#skF_2'))) = k2_pre_topc('#skF_1',k2_tops_1('#skF_1','#skF_2'))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_137,c_28])).

tff(c_144,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),k2_tops_1('#skF_1','#skF_2'),k2_tops_1('#skF_1',k2_tops_1('#skF_1','#skF_2'))) = k2_pre_topc('#skF_1',k2_tops_1('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_139])).

tff(c_14,plain,(
    ! [A_9,B_10,C_12] :
      ( r1_tarski(k3_subset_1(A_9,k4_subset_1(A_9,B_10,C_12)),k3_subset_1(A_9,B_10))
      | ~ m1_subset_1(C_12,k1_zfmisc_1(A_9))
      | ~ m1_subset_1(B_10,k1_zfmisc_1(A_9)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_233,plain,
    ( r1_tarski(k3_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1',k2_tops_1('#skF_1','#skF_2'))),k3_subset_1(u1_struct_0('#skF_1'),k2_tops_1('#skF_1','#skF_2')))
    | ~ m1_subset_1(k2_tops_1('#skF_1',k2_tops_1('#skF_1','#skF_2')),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_subset_1(k2_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_144,c_14])).

tff(c_237,plain,
    ( r1_tarski(k3_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1',k2_tops_1('#skF_1','#skF_2'))),k3_subset_1(u1_struct_0('#skF_1'),k2_tops_1('#skF_1','#skF_2')))
    | ~ m1_subset_1(k2_tops_1('#skF_1',k2_tops_1('#skF_1','#skF_2')),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_137,c_233])).

tff(c_994,plain,(
    ~ m1_subset_1(k2_tops_1('#skF_1',k2_tops_1('#skF_1','#skF_2')),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_237])).

tff(c_997,plain,
    ( ~ m1_subset_1(k2_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_26,c_994])).

tff(c_1001,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_137,c_997])).

tff(c_1003,plain,(
    m1_subset_1(k2_tops_1('#skF_1',k2_tops_1('#skF_1','#skF_2')),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_237])).

tff(c_1002,plain,(
    r1_tarski(k3_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1',k2_tops_1('#skF_1','#skF_2'))),k3_subset_1(u1_struct_0('#skF_1'),k2_tops_1('#skF_1','#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_237])).

tff(c_10,plain,(
    ! [B_6,C_8,A_5] :
      ( r1_tarski(B_6,C_8)
      | ~ r1_tarski(k3_subset_1(A_5,C_8),k3_subset_1(A_5,B_6))
      | ~ m1_subset_1(C_8,k1_zfmisc_1(A_5))
      | ~ m1_subset_1(B_6,k1_zfmisc_1(A_5)) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_1045,plain,
    ( r1_tarski(k2_tops_1('#skF_1','#skF_2'),k2_pre_topc('#skF_1',k2_tops_1('#skF_1','#skF_2')))
    | ~ m1_subset_1(k2_pre_topc('#skF_1',k2_tops_1('#skF_1','#skF_2')),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_subset_1(k2_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_1002,c_10])).

tff(c_1054,plain,
    ( r1_tarski(k2_tops_1('#skF_1','#skF_2'),k2_pre_topc('#skF_1',k2_tops_1('#skF_1','#skF_2')))
    | ~ m1_subset_1(k2_pre_topc('#skF_1',k2_tops_1('#skF_1','#skF_2')),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_137,c_1045])).

tff(c_1056,plain,(
    ~ m1_subset_1(k2_pre_topc('#skF_1',k2_tops_1('#skF_1','#skF_2')),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_1054])).

tff(c_1059,plain,
    ( ~ m1_subset_1(k2_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_18,c_1056])).

tff(c_1063,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_137,c_1059])).

tff(c_1064,plain,(
    r1_tarski(k2_tops_1('#skF_1','#skF_2'),k2_pre_topc('#skF_1',k2_tops_1('#skF_1','#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_1054])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_1107,plain,
    ( k2_pre_topc('#skF_1',k2_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2')
    | ~ r1_tarski(k2_pre_topc('#skF_1',k2_tops_1('#skF_1','#skF_2')),k2_tops_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_1064,c_2])).

tff(c_1178,plain,(
    ~ r1_tarski(k2_pre_topc('#skF_1',k2_tops_1('#skF_1','#skF_2')),k2_tops_1('#skF_1','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_1107])).

tff(c_24,plain,(
    ! [A_28,B_30] :
      ( k9_subset_1(u1_struct_0(A_28),k2_pre_topc(A_28,B_30),k2_pre_topc(A_28,k3_subset_1(u1_struct_0(A_28),B_30))) = k2_tops_1(A_28,B_30)
      | ~ m1_subset_1(B_30,k1_zfmisc_1(u1_struct_0(A_28)))
      | ~ l1_pre_topc(A_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_136,plain,(
    r1_tarski(k3_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2')),k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')) ),
    inference(splitRight,[status(thm)],[c_104])).

tff(c_150,plain,
    ( r1_tarski('#skF_2',k2_pre_topc('#skF_1','#skF_2'))
    | ~ m1_subset_1(k2_pre_topc('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_136,c_10])).

tff(c_155,plain,
    ( r1_tarski('#skF_2',k2_pre_topc('#skF_1','#skF_2'))
    | ~ m1_subset_1(k2_pre_topc('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_150])).

tff(c_166,plain,(
    ~ m1_subset_1(k2_pre_topc('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_155])).

tff(c_169,plain,
    ( ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_18,c_166])).

tff(c_173,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_169])).

tff(c_175,plain,(
    m1_subset_1(k2_pre_topc('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_155])).

tff(c_47,plain,(
    ! [A_46,B_47] :
      ( k2_pre_topc(A_46,k2_pre_topc(A_46,B_47)) = k2_pre_topc(A_46,B_47)
      | ~ m1_subset_1(B_47,k1_zfmisc_1(u1_struct_0(A_46)))
      | ~ l1_pre_topc(A_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_56,plain,
    ( k2_pre_topc('#skF_1',k2_pre_topc('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_47])).

tff(c_62,plain,(
    k2_pre_topc('#skF_1',k2_pre_topc('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_56])).

tff(c_319,plain,(
    ! [A_68,B_69,C_70] :
      ( r1_tarski(k2_pre_topc(A_68,k9_subset_1(u1_struct_0(A_68),B_69,C_70)),k9_subset_1(u1_struct_0(A_68),k2_pre_topc(A_68,B_69),k2_pre_topc(A_68,C_70)))
      | ~ m1_subset_1(C_70,k1_zfmisc_1(u1_struct_0(A_68)))
      | ~ m1_subset_1(B_69,k1_zfmisc_1(u1_struct_0(A_68)))
      | ~ l1_pre_topc(A_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_354,plain,(
    ! [C_70] :
      ( r1_tarski(k2_pre_topc('#skF_1',k9_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2'),C_70)),k9_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2'),k2_pre_topc('#skF_1',C_70)))
      | ~ m1_subset_1(C_70,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ m1_subset_1(k2_pre_topc('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_62,c_319])).

tff(c_420,plain,(
    ! [C_79] :
      ( r1_tarski(k2_pre_topc('#skF_1',k9_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2'),C_79)),k9_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2'),k2_pre_topc('#skF_1',C_79)))
      | ~ m1_subset_1(C_79,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_175,c_354])).

tff(c_446,plain,
    ( r1_tarski(k2_pre_topc('#skF_1',k9_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2'),k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'))),k2_tops_1('#skF_1','#skF_2'))
    | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_420])).

tff(c_459,plain,
    ( r1_tarski(k2_pre_topc('#skF_1',k9_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2'),k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'))),k2_tops_1('#skF_1','#skF_2'))
    | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_446])).

tff(c_1546,plain,(
    ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_459])).

tff(c_1549,plain,(
    ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_8,c_1546])).

tff(c_1553,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_1549])).

tff(c_1555,plain,(
    m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_459])).

tff(c_20,plain,(
    ! [A_19,B_20] :
      ( k2_pre_topc(A_19,k2_pre_topc(A_19,B_20)) = k2_pre_topc(A_19,B_20)
      | ~ m1_subset_1(B_20,k1_zfmisc_1(u1_struct_0(A_19)))
      | ~ l1_pre_topc(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_1563,plain,
    ( k2_pre_topc('#skF_1',k2_pre_topc('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'))) = k2_pre_topc('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_1555,c_20])).

tff(c_1575,plain,(
    k2_pre_topc('#skF_1',k2_pre_topc('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'))) = k2_pre_topc('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_1563])).

tff(c_2567,plain,(
    ! [A_119,B_120] :
      ( r1_tarski(k2_pre_topc(A_119,k2_tops_1(A_119,B_120)),k9_subset_1(u1_struct_0(A_119),k2_pre_topc(A_119,k2_pre_topc(A_119,B_120)),k2_pre_topc(A_119,k2_pre_topc(A_119,k3_subset_1(u1_struct_0(A_119),B_120)))))
      | ~ m1_subset_1(k2_pre_topc(A_119,k3_subset_1(u1_struct_0(A_119),B_120)),k1_zfmisc_1(u1_struct_0(A_119)))
      | ~ m1_subset_1(k2_pre_topc(A_119,B_120),k1_zfmisc_1(u1_struct_0(A_119)))
      | ~ l1_pre_topc(A_119)
      | ~ m1_subset_1(B_120,k1_zfmisc_1(u1_struct_0(A_119)))
      | ~ l1_pre_topc(A_119) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_319])).

tff(c_2694,plain,
    ( r1_tarski(k2_pre_topc('#skF_1',k2_tops_1('#skF_1','#skF_2')),k9_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2'),k2_pre_topc('#skF_1',k2_pre_topc('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')))))
    | ~ m1_subset_1(k2_pre_topc('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_subset_1(k2_pre_topc('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_62,c_2567])).

tff(c_2748,plain,
    ( r1_tarski(k2_pre_topc('#skF_1',k2_tops_1('#skF_1','#skF_2')),k9_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2'),k2_pre_topc('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'))))
    | ~ m1_subset_1(k2_pre_topc('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_34,c_175,c_1575,c_2694])).

tff(c_2969,plain,(
    ~ m1_subset_1(k2_pre_topc('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_2748])).

tff(c_2972,plain,
    ( ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_18,c_2969])).

tff(c_2976,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_1555,c_2972])).

tff(c_2977,plain,(
    r1_tarski(k2_pre_topc('#skF_1',k2_tops_1('#skF_1','#skF_2')),k9_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2'),k2_pre_topc('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')))) ),
    inference(splitRight,[status(thm)],[c_2748])).

tff(c_3056,plain,
    ( r1_tarski(k2_pre_topc('#skF_1',k2_tops_1('#skF_1','#skF_2')),k2_tops_1('#skF_1','#skF_2'))
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_2977])).

tff(c_3060,plain,(
    r1_tarski(k2_pre_topc('#skF_1',k2_tops_1('#skF_1','#skF_2')),k2_tops_1('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_3056])).

tff(c_3062,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1178,c_3060])).

tff(c_3063,plain,(
    k2_pre_topc('#skF_1',k2_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_1107])).

tff(c_3103,plain,
    ( k9_subset_1(u1_struct_0('#skF_1'),k2_tops_1('#skF_1','#skF_2'),k2_pre_topc('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),k2_tops_1('#skF_1','#skF_2')))) = k2_tops_1('#skF_1',k2_tops_1('#skF_1','#skF_2'))
    | ~ m1_subset_1(k2_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_3063,c_24])).

tff(c_3128,plain,(
    k9_subset_1(u1_struct_0('#skF_1'),k2_tops_1('#skF_1','#skF_2'),k2_pre_topc('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),k2_tops_1('#skF_1','#skF_2')))) = k2_tops_1('#skF_1',k2_tops_1('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_137,c_3103])).

tff(c_16,plain,(
    ! [A_13,B_14,C_16] :
      ( r1_tarski(k3_subset_1(A_13,B_14),k3_subset_1(A_13,k9_subset_1(A_13,B_14,C_16)))
      | ~ m1_subset_1(C_16,k1_zfmisc_1(A_13))
      | ~ m1_subset_1(B_14,k1_zfmisc_1(A_13)) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_105,plain,(
    ! [B_56,C_57,A_58] :
      ( r1_tarski(B_56,C_57)
      | ~ r1_tarski(k3_subset_1(A_58,C_57),k3_subset_1(A_58,B_56))
      | ~ m1_subset_1(C_57,k1_zfmisc_1(A_58))
      | ~ m1_subset_1(B_56,k1_zfmisc_1(A_58)) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_117,plain,(
    ! [A_13,B_14,C_16] :
      ( r1_tarski(k9_subset_1(A_13,B_14,C_16),B_14)
      | ~ m1_subset_1(k9_subset_1(A_13,B_14,C_16),k1_zfmisc_1(A_13))
      | ~ m1_subset_1(C_16,k1_zfmisc_1(A_13))
      | ~ m1_subset_1(B_14,k1_zfmisc_1(A_13)) ) ),
    inference(resolution,[status(thm)],[c_16,c_105])).

tff(c_3241,plain,
    ( r1_tarski(k9_subset_1(u1_struct_0('#skF_1'),k2_tops_1('#skF_1','#skF_2'),k2_pre_topc('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),k2_tops_1('#skF_1','#skF_2')))),k2_tops_1('#skF_1','#skF_2'))
    | ~ m1_subset_1(k2_tops_1('#skF_1',k2_tops_1('#skF_1','#skF_2')),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_subset_1(k2_pre_topc('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),k2_tops_1('#skF_1','#skF_2'))),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_subset_1(k2_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_3128,c_117])).

tff(c_3251,plain,
    ( r1_tarski(k2_tops_1('#skF_1',k2_tops_1('#skF_1','#skF_2')),k2_tops_1('#skF_1','#skF_2'))
    | ~ m1_subset_1(k2_pre_topc('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),k2_tops_1('#skF_1','#skF_2'))),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_137,c_1003,c_3128,c_3241])).

tff(c_3252,plain,(
    ~ m1_subset_1(k2_pre_topc('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),k2_tops_1('#skF_1','#skF_2'))),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_3251])).

tff(c_3279,plain,
    ( ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'),k2_tops_1('#skF_1','#skF_2')),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_18,c_3252])).

tff(c_3282,plain,(
    ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'),k2_tops_1('#skF_1','#skF_2')),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_3279])).

tff(c_3285,plain,(
    ~ m1_subset_1(k2_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_8,c_3282])).

tff(c_3289,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_137,c_3285])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 12:03:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.32/1.98  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.32/1.99  
% 5.32/1.99  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.32/2.00  %$ r1_tarski > m1_subset_1 > l1_pre_topc > k9_subset_1 > k4_subset_1 > k3_subset_1 > k2_tops_1 > k2_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_1
% 5.32/2.00  
% 5.32/2.00  %Foreground sorts:
% 5.32/2.00  
% 5.32/2.00  
% 5.32/2.00  %Background operators:
% 5.32/2.00  
% 5.32/2.00  
% 5.32/2.00  %Foreground operators:
% 5.32/2.00  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.32/2.00  tff(k2_tops_1, type, k2_tops_1: ($i * $i) > $i).
% 5.32/2.00  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 5.32/2.00  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.32/2.00  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 5.32/2.00  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 5.32/2.00  tff('#skF_2', type, '#skF_2': $i).
% 5.32/2.00  tff('#skF_1', type, '#skF_1': $i).
% 5.32/2.00  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.32/2.00  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.32/2.00  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.32/2.00  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 5.32/2.00  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 5.32/2.00  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 5.32/2.00  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.32/2.00  
% 5.32/2.01  tff(f_108, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => r1_tarski(k2_tops_1(A, k2_tops_1(A, B)), k2_tops_1(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t68_tops_1)).
% 5.32/2.01  tff(f_93, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_tops_1(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_tops_1)).
% 5.32/2.01  tff(f_100, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_pre_topc(A, B) = k4_subset_1(u1_struct_0(A), B, k2_tops_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_tops_1)).
% 5.32/2.01  tff(f_51, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => r1_tarski(k3_subset_1(A, k4_subset_1(A, B, C)), k3_subset_1(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_subset_1)).
% 5.32/2.01  tff(f_35, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k3_subset_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 5.32/2.01  tff(f_64, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_pre_topc(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_pre_topc)).
% 5.32/2.01  tff(f_44, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (r1_tarski(B, C) <=> r1_tarski(k3_subset_1(A, C), k3_subset_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_subset_1)).
% 5.32/2.01  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 5.32/2.01  tff(f_87, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_tops_1(A, B) = k9_subset_1(u1_struct_0(A), k2_pre_topc(A, B), k2_pre_topc(A, k3_subset_1(u1_struct_0(A), B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_tops_1)).
% 5.32/2.01  tff(f_70, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => (k2_pre_topc(A, k2_pre_topc(A, B)) = k2_pre_topc(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', projectivity_k2_pre_topc)).
% 5.32/2.01  tff(f_80, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => r1_tarski(k2_pre_topc(A, k9_subset_1(u1_struct_0(A), B, C)), k9_subset_1(u1_struct_0(A), k2_pre_topc(A, B), k2_pre_topc(A, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t51_pre_topc)).
% 5.32/2.01  tff(f_58, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => r1_tarski(k3_subset_1(A, B), k3_subset_1(A, k9_subset_1(A, B, C))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t42_subset_1)).
% 5.32/2.01  tff(c_34, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_108])).
% 5.32/2.01  tff(c_32, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_108])).
% 5.32/2.01  tff(c_26, plain, (![A_31, B_32]: (m1_subset_1(k2_tops_1(A_31, B_32), k1_zfmisc_1(u1_struct_0(A_31))) | ~m1_subset_1(B_32, k1_zfmisc_1(u1_struct_0(A_31))) | ~l1_pre_topc(A_31))), inference(cnfTransformation, [status(thm)], [f_93])).
% 5.32/2.01  tff(c_72, plain, (![A_48, B_49]: (k4_subset_1(u1_struct_0(A_48), B_49, k2_tops_1(A_48, B_49))=k2_pre_topc(A_48, B_49) | ~m1_subset_1(B_49, k1_zfmisc_1(u1_struct_0(A_48))) | ~l1_pre_topc(A_48))), inference(cnfTransformation, [status(thm)], [f_100])).
% 5.32/2.01  tff(c_81, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_32, c_72])).
% 5.32/2.01  tff(c_87, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_81])).
% 5.32/2.01  tff(c_96, plain, (![A_53, B_54, C_55]: (r1_tarski(k3_subset_1(A_53, k4_subset_1(A_53, B_54, C_55)), k3_subset_1(A_53, B_54)) | ~m1_subset_1(C_55, k1_zfmisc_1(A_53)) | ~m1_subset_1(B_54, k1_zfmisc_1(A_53)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 5.32/2.01  tff(c_101, plain, (r1_tarski(k3_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_2')), k3_subset_1(u1_struct_0('#skF_1'), '#skF_2')) | ~m1_subset_1(k2_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_87, c_96])).
% 5.32/2.01  tff(c_104, plain, (r1_tarski(k3_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_2')), k3_subset_1(u1_struct_0('#skF_1'), '#skF_2')) | ~m1_subset_1(k2_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_101])).
% 5.32/2.01  tff(c_128, plain, (~m1_subset_1(k2_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitLeft, [status(thm)], [c_104])).
% 5.32/2.01  tff(c_131, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_26, c_128])).
% 5.32/2.01  tff(c_135, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_131])).
% 5.32/2.01  tff(c_137, plain, (m1_subset_1(k2_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitRight, [status(thm)], [c_104])).
% 5.32/2.01  tff(c_8, plain, (![A_3, B_4]: (m1_subset_1(k3_subset_1(A_3, B_4), k1_zfmisc_1(A_3)) | ~m1_subset_1(B_4, k1_zfmisc_1(A_3)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 5.32/2.01  tff(c_18, plain, (![A_17, B_18]: (m1_subset_1(k2_pre_topc(A_17, B_18), k1_zfmisc_1(u1_struct_0(A_17))) | ~m1_subset_1(B_18, k1_zfmisc_1(u1_struct_0(A_17))) | ~l1_pre_topc(A_17))), inference(cnfTransformation, [status(thm)], [f_64])).
% 5.32/2.01  tff(c_30, plain, (~r1_tarski(k2_tops_1('#skF_1', k2_tops_1('#skF_1', '#skF_2')), k2_tops_1('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_108])).
% 5.32/2.01  tff(c_28, plain, (![A_33, B_35]: (k4_subset_1(u1_struct_0(A_33), B_35, k2_tops_1(A_33, B_35))=k2_pre_topc(A_33, B_35) | ~m1_subset_1(B_35, k1_zfmisc_1(u1_struct_0(A_33))) | ~l1_pre_topc(A_33))), inference(cnfTransformation, [status(thm)], [f_100])).
% 5.32/2.01  tff(c_139, plain, (k4_subset_1(u1_struct_0('#skF_1'), k2_tops_1('#skF_1', '#skF_2'), k2_tops_1('#skF_1', k2_tops_1('#skF_1', '#skF_2')))=k2_pre_topc('#skF_1', k2_tops_1('#skF_1', '#skF_2')) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_137, c_28])).
% 5.32/2.01  tff(c_144, plain, (k4_subset_1(u1_struct_0('#skF_1'), k2_tops_1('#skF_1', '#skF_2'), k2_tops_1('#skF_1', k2_tops_1('#skF_1', '#skF_2')))=k2_pre_topc('#skF_1', k2_tops_1('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_139])).
% 5.32/2.01  tff(c_14, plain, (![A_9, B_10, C_12]: (r1_tarski(k3_subset_1(A_9, k4_subset_1(A_9, B_10, C_12)), k3_subset_1(A_9, B_10)) | ~m1_subset_1(C_12, k1_zfmisc_1(A_9)) | ~m1_subset_1(B_10, k1_zfmisc_1(A_9)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 5.32/2.01  tff(c_233, plain, (r1_tarski(k3_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', k2_tops_1('#skF_1', '#skF_2'))), k3_subset_1(u1_struct_0('#skF_1'), k2_tops_1('#skF_1', '#skF_2'))) | ~m1_subset_1(k2_tops_1('#skF_1', k2_tops_1('#skF_1', '#skF_2')), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1(k2_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_144, c_14])).
% 5.32/2.01  tff(c_237, plain, (r1_tarski(k3_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', k2_tops_1('#skF_1', '#skF_2'))), k3_subset_1(u1_struct_0('#skF_1'), k2_tops_1('#skF_1', '#skF_2'))) | ~m1_subset_1(k2_tops_1('#skF_1', k2_tops_1('#skF_1', '#skF_2')), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_137, c_233])).
% 5.32/2.01  tff(c_994, plain, (~m1_subset_1(k2_tops_1('#skF_1', k2_tops_1('#skF_1', '#skF_2')), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitLeft, [status(thm)], [c_237])).
% 5.32/2.01  tff(c_997, plain, (~m1_subset_1(k2_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_26, c_994])).
% 5.32/2.01  tff(c_1001, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_34, c_137, c_997])).
% 5.32/2.01  tff(c_1003, plain, (m1_subset_1(k2_tops_1('#skF_1', k2_tops_1('#skF_1', '#skF_2')), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitRight, [status(thm)], [c_237])).
% 5.32/2.01  tff(c_1002, plain, (r1_tarski(k3_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', k2_tops_1('#skF_1', '#skF_2'))), k3_subset_1(u1_struct_0('#skF_1'), k2_tops_1('#skF_1', '#skF_2')))), inference(splitRight, [status(thm)], [c_237])).
% 5.32/2.01  tff(c_10, plain, (![B_6, C_8, A_5]: (r1_tarski(B_6, C_8) | ~r1_tarski(k3_subset_1(A_5, C_8), k3_subset_1(A_5, B_6)) | ~m1_subset_1(C_8, k1_zfmisc_1(A_5)) | ~m1_subset_1(B_6, k1_zfmisc_1(A_5)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 5.32/2.01  tff(c_1045, plain, (r1_tarski(k2_tops_1('#skF_1', '#skF_2'), k2_pre_topc('#skF_1', k2_tops_1('#skF_1', '#skF_2'))) | ~m1_subset_1(k2_pre_topc('#skF_1', k2_tops_1('#skF_1', '#skF_2')), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1(k2_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_1002, c_10])).
% 5.32/2.01  tff(c_1054, plain, (r1_tarski(k2_tops_1('#skF_1', '#skF_2'), k2_pre_topc('#skF_1', k2_tops_1('#skF_1', '#skF_2'))) | ~m1_subset_1(k2_pre_topc('#skF_1', k2_tops_1('#skF_1', '#skF_2')), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_137, c_1045])).
% 5.32/2.01  tff(c_1056, plain, (~m1_subset_1(k2_pre_topc('#skF_1', k2_tops_1('#skF_1', '#skF_2')), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitLeft, [status(thm)], [c_1054])).
% 5.32/2.01  tff(c_1059, plain, (~m1_subset_1(k2_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_18, c_1056])).
% 5.32/2.01  tff(c_1063, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_34, c_137, c_1059])).
% 5.32/2.01  tff(c_1064, plain, (r1_tarski(k2_tops_1('#skF_1', '#skF_2'), k2_pre_topc('#skF_1', k2_tops_1('#skF_1', '#skF_2')))), inference(splitRight, [status(thm)], [c_1054])).
% 5.32/2.01  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.32/2.01  tff(c_1107, plain, (k2_pre_topc('#skF_1', k2_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2') | ~r1_tarski(k2_pre_topc('#skF_1', k2_tops_1('#skF_1', '#skF_2')), k2_tops_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_1064, c_2])).
% 5.32/2.01  tff(c_1178, plain, (~r1_tarski(k2_pre_topc('#skF_1', k2_tops_1('#skF_1', '#skF_2')), k2_tops_1('#skF_1', '#skF_2'))), inference(splitLeft, [status(thm)], [c_1107])).
% 5.32/2.01  tff(c_24, plain, (![A_28, B_30]: (k9_subset_1(u1_struct_0(A_28), k2_pre_topc(A_28, B_30), k2_pre_topc(A_28, k3_subset_1(u1_struct_0(A_28), B_30)))=k2_tops_1(A_28, B_30) | ~m1_subset_1(B_30, k1_zfmisc_1(u1_struct_0(A_28))) | ~l1_pre_topc(A_28))), inference(cnfTransformation, [status(thm)], [f_87])).
% 5.32/2.01  tff(c_136, plain, (r1_tarski(k3_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_2')), k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'))), inference(splitRight, [status(thm)], [c_104])).
% 5.32/2.01  tff(c_150, plain, (r1_tarski('#skF_2', k2_pre_topc('#skF_1', '#skF_2')) | ~m1_subset_1(k2_pre_topc('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_136, c_10])).
% 5.32/2.01  tff(c_155, plain, (r1_tarski('#skF_2', k2_pre_topc('#skF_1', '#skF_2')) | ~m1_subset_1(k2_pre_topc('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_150])).
% 5.32/2.01  tff(c_166, plain, (~m1_subset_1(k2_pre_topc('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitLeft, [status(thm)], [c_155])).
% 5.32/2.01  tff(c_169, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_18, c_166])).
% 5.32/2.01  tff(c_173, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_169])).
% 5.32/2.01  tff(c_175, plain, (m1_subset_1(k2_pre_topc('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitRight, [status(thm)], [c_155])).
% 5.32/2.01  tff(c_47, plain, (![A_46, B_47]: (k2_pre_topc(A_46, k2_pre_topc(A_46, B_47))=k2_pre_topc(A_46, B_47) | ~m1_subset_1(B_47, k1_zfmisc_1(u1_struct_0(A_46))) | ~l1_pre_topc(A_46))), inference(cnfTransformation, [status(thm)], [f_70])).
% 5.32/2.01  tff(c_56, plain, (k2_pre_topc('#skF_1', k2_pre_topc('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_32, c_47])).
% 5.32/2.01  tff(c_62, plain, (k2_pre_topc('#skF_1', k2_pre_topc('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_56])).
% 5.32/2.01  tff(c_319, plain, (![A_68, B_69, C_70]: (r1_tarski(k2_pre_topc(A_68, k9_subset_1(u1_struct_0(A_68), B_69, C_70)), k9_subset_1(u1_struct_0(A_68), k2_pre_topc(A_68, B_69), k2_pre_topc(A_68, C_70))) | ~m1_subset_1(C_70, k1_zfmisc_1(u1_struct_0(A_68))) | ~m1_subset_1(B_69, k1_zfmisc_1(u1_struct_0(A_68))) | ~l1_pre_topc(A_68))), inference(cnfTransformation, [status(thm)], [f_80])).
% 5.32/2.01  tff(c_354, plain, (![C_70]: (r1_tarski(k2_pre_topc('#skF_1', k9_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_2'), C_70)), k9_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_2'), k2_pre_topc('#skF_1', C_70))) | ~m1_subset_1(C_70, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1(k2_pre_topc('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_62, c_319])).
% 5.32/2.01  tff(c_420, plain, (![C_79]: (r1_tarski(k2_pre_topc('#skF_1', k9_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_2'), C_79)), k9_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_2'), k2_pre_topc('#skF_1', C_79))) | ~m1_subset_1(C_79, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_175, c_354])).
% 5.32/2.01  tff(c_446, plain, (r1_tarski(k2_pre_topc('#skF_1', k9_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_2'), k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'))), k2_tops_1('#skF_1', '#skF_2')) | ~m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_24, c_420])).
% 5.32/2.01  tff(c_459, plain, (r1_tarski(k2_pre_topc('#skF_1', k9_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_2'), k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'))), k2_tops_1('#skF_1', '#skF_2')) | ~m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_446])).
% 5.32/2.01  tff(c_1546, plain, (~m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitLeft, [status(thm)], [c_459])).
% 5.32/2.01  tff(c_1549, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_8, c_1546])).
% 5.32/2.01  tff(c_1553, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_32, c_1549])).
% 5.32/2.01  tff(c_1555, plain, (m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitRight, [status(thm)], [c_459])).
% 5.32/2.01  tff(c_20, plain, (![A_19, B_20]: (k2_pre_topc(A_19, k2_pre_topc(A_19, B_20))=k2_pre_topc(A_19, B_20) | ~m1_subset_1(B_20, k1_zfmisc_1(u1_struct_0(A_19))) | ~l1_pre_topc(A_19))), inference(cnfTransformation, [status(thm)], [f_70])).
% 5.32/2.01  tff(c_1563, plain, (k2_pre_topc('#skF_1', k2_pre_topc('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_2')))=k2_pre_topc('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_2')) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_1555, c_20])).
% 5.32/2.01  tff(c_1575, plain, (k2_pre_topc('#skF_1', k2_pre_topc('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_2')))=k2_pre_topc('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_1563])).
% 5.32/2.01  tff(c_2567, plain, (![A_119, B_120]: (r1_tarski(k2_pre_topc(A_119, k2_tops_1(A_119, B_120)), k9_subset_1(u1_struct_0(A_119), k2_pre_topc(A_119, k2_pre_topc(A_119, B_120)), k2_pre_topc(A_119, k2_pre_topc(A_119, k3_subset_1(u1_struct_0(A_119), B_120))))) | ~m1_subset_1(k2_pre_topc(A_119, k3_subset_1(u1_struct_0(A_119), B_120)), k1_zfmisc_1(u1_struct_0(A_119))) | ~m1_subset_1(k2_pre_topc(A_119, B_120), k1_zfmisc_1(u1_struct_0(A_119))) | ~l1_pre_topc(A_119) | ~m1_subset_1(B_120, k1_zfmisc_1(u1_struct_0(A_119))) | ~l1_pre_topc(A_119))), inference(superposition, [status(thm), theory('equality')], [c_24, c_319])).
% 5.32/2.01  tff(c_2694, plain, (r1_tarski(k2_pre_topc('#skF_1', k2_tops_1('#skF_1', '#skF_2')), k9_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_2'), k2_pre_topc('#skF_1', k2_pre_topc('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'))))) | ~m1_subset_1(k2_pre_topc('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_2')), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1(k2_pre_topc('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_62, c_2567])).
% 5.32/2.01  tff(c_2748, plain, (r1_tarski(k2_pre_topc('#skF_1', k2_tops_1('#skF_1', '#skF_2')), k9_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_2'), k2_pre_topc('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_2')))) | ~m1_subset_1(k2_pre_topc('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_2')), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_34, c_175, c_1575, c_2694])).
% 5.32/2.01  tff(c_2969, plain, (~m1_subset_1(k2_pre_topc('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_2')), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitLeft, [status(thm)], [c_2748])).
% 5.32/2.01  tff(c_2972, plain, (~m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_18, c_2969])).
% 5.32/2.01  tff(c_2976, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_34, c_1555, c_2972])).
% 5.32/2.01  tff(c_2977, plain, (r1_tarski(k2_pre_topc('#skF_1', k2_tops_1('#skF_1', '#skF_2')), k9_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_2'), k2_pre_topc('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'))))), inference(splitRight, [status(thm)], [c_2748])).
% 5.32/2.01  tff(c_3056, plain, (r1_tarski(k2_pre_topc('#skF_1', k2_tops_1('#skF_1', '#skF_2')), k2_tops_1('#skF_1', '#skF_2')) | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_24, c_2977])).
% 5.32/2.01  tff(c_3060, plain, (r1_tarski(k2_pre_topc('#skF_1', k2_tops_1('#skF_1', '#skF_2')), k2_tops_1('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_3056])).
% 5.32/2.01  tff(c_3062, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1178, c_3060])).
% 5.32/2.01  tff(c_3063, plain, (k2_pre_topc('#skF_1', k2_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_1107])).
% 5.32/2.01  tff(c_3103, plain, (k9_subset_1(u1_struct_0('#skF_1'), k2_tops_1('#skF_1', '#skF_2'), k2_pre_topc('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), k2_tops_1('#skF_1', '#skF_2'))))=k2_tops_1('#skF_1', k2_tops_1('#skF_1', '#skF_2')) | ~m1_subset_1(k2_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_3063, c_24])).
% 5.32/2.01  tff(c_3128, plain, (k9_subset_1(u1_struct_0('#skF_1'), k2_tops_1('#skF_1', '#skF_2'), k2_pre_topc('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), k2_tops_1('#skF_1', '#skF_2'))))=k2_tops_1('#skF_1', k2_tops_1('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_137, c_3103])).
% 5.32/2.01  tff(c_16, plain, (![A_13, B_14, C_16]: (r1_tarski(k3_subset_1(A_13, B_14), k3_subset_1(A_13, k9_subset_1(A_13, B_14, C_16))) | ~m1_subset_1(C_16, k1_zfmisc_1(A_13)) | ~m1_subset_1(B_14, k1_zfmisc_1(A_13)))), inference(cnfTransformation, [status(thm)], [f_58])).
% 5.32/2.01  tff(c_105, plain, (![B_56, C_57, A_58]: (r1_tarski(B_56, C_57) | ~r1_tarski(k3_subset_1(A_58, C_57), k3_subset_1(A_58, B_56)) | ~m1_subset_1(C_57, k1_zfmisc_1(A_58)) | ~m1_subset_1(B_56, k1_zfmisc_1(A_58)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 5.32/2.01  tff(c_117, plain, (![A_13, B_14, C_16]: (r1_tarski(k9_subset_1(A_13, B_14, C_16), B_14) | ~m1_subset_1(k9_subset_1(A_13, B_14, C_16), k1_zfmisc_1(A_13)) | ~m1_subset_1(C_16, k1_zfmisc_1(A_13)) | ~m1_subset_1(B_14, k1_zfmisc_1(A_13)))), inference(resolution, [status(thm)], [c_16, c_105])).
% 5.32/2.01  tff(c_3241, plain, (r1_tarski(k9_subset_1(u1_struct_0('#skF_1'), k2_tops_1('#skF_1', '#skF_2'), k2_pre_topc('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), k2_tops_1('#skF_1', '#skF_2')))), k2_tops_1('#skF_1', '#skF_2')) | ~m1_subset_1(k2_tops_1('#skF_1', k2_tops_1('#skF_1', '#skF_2')), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1(k2_pre_topc('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), k2_tops_1('#skF_1', '#skF_2'))), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1(k2_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_3128, c_117])).
% 5.32/2.01  tff(c_3251, plain, (r1_tarski(k2_tops_1('#skF_1', k2_tops_1('#skF_1', '#skF_2')), k2_tops_1('#skF_1', '#skF_2')) | ~m1_subset_1(k2_pre_topc('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), k2_tops_1('#skF_1', '#skF_2'))), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_137, c_1003, c_3128, c_3241])).
% 5.32/2.01  tff(c_3252, plain, (~m1_subset_1(k2_pre_topc('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), k2_tops_1('#skF_1', '#skF_2'))), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(negUnitSimplification, [status(thm)], [c_30, c_3251])).
% 5.32/2.01  tff(c_3279, plain, (~m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'), k2_tops_1('#skF_1', '#skF_2')), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_18, c_3252])).
% 5.32/2.01  tff(c_3282, plain, (~m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'), k2_tops_1('#skF_1', '#skF_2')), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_3279])).
% 5.32/2.01  tff(c_3285, plain, (~m1_subset_1(k2_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_8, c_3282])).
% 5.32/2.01  tff(c_3289, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_137, c_3285])).
% 5.32/2.01  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.32/2.01  
% 5.32/2.01  Inference rules
% 5.32/2.01  ----------------------
% 5.32/2.01  #Ref     : 0
% 5.32/2.01  #Sup     : 737
% 5.32/2.01  #Fact    : 0
% 5.32/2.01  #Define  : 0
% 5.32/2.01  #Split   : 17
% 5.32/2.02  #Chain   : 0
% 5.32/2.02  #Close   : 0
% 5.32/2.02  
% 5.32/2.02  Ordering : KBO
% 5.32/2.02  
% 5.32/2.02  Simplification rules
% 5.32/2.02  ----------------------
% 5.32/2.02  #Subsume      : 10
% 5.32/2.02  #Demod        : 1016
% 5.32/2.02  #Tautology    : 262
% 5.32/2.02  #SimpNegUnit  : 2
% 5.32/2.02  #BackRed      : 4
% 5.32/2.02  
% 5.32/2.02  #Partial instantiations: 0
% 5.32/2.02  #Strategies tried      : 1
% 5.32/2.02  
% 5.32/2.02  Timing (in seconds)
% 5.32/2.02  ----------------------
% 5.32/2.02  Preprocessing        : 0.31
% 5.32/2.02  Parsing              : 0.17
% 5.32/2.02  CNF conversion       : 0.02
% 5.32/2.02  Main loop            : 0.94
% 5.32/2.02  Inferencing          : 0.29
% 5.32/2.02  Reduction            : 0.38
% 5.32/2.02  Demodulation         : 0.29
% 5.32/2.02  BG Simplification    : 0.04
% 5.32/2.02  Subsumption          : 0.18
% 5.32/2.02  Abstraction          : 0.05
% 5.32/2.02  MUC search           : 0.00
% 5.32/2.02  Cooper               : 0.00
% 5.32/2.02  Total                : 1.29
% 5.32/2.02  Index Insertion      : 0.00
% 5.32/2.02  Index Deletion       : 0.00
% 5.32/2.02  Index Matching       : 0.00
% 5.32/2.02  BG Taut test         : 0.00
%------------------------------------------------------------------------------
