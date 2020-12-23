%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:22:00 EST 2020

% Result     : Theorem 3.16s
% Output     : CNFRefutation 3.40s
% Verified   : 
% Statistics : Number of formulae       :   79 ( 461 expanded)
%              Number of leaves         :   24 ( 166 expanded)
%              Depth                    :   13
%              Number of atoms          :  175 (1136 expanded)
%              Number of equality atoms :    6 ( 108 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_tops_1 > v2_tops_1 > v1_tops_1 > r1_tarski > m1_subset_1 > l1_pre_topc > k3_subset_1 > k2_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(v2_tops_1,type,(
    v2_tops_1: ( $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(v3_tops_1,type,(
    v3_tops_1: ( $i * $i ) > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff(v1_tops_1,type,(
    v1_tops_1: ( $i * $i ) > $o )).

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

tff(f_97,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v3_tops_1(B,A)
             => v1_tops_1(k3_subset_1(u1_struct_0(A),B),A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_tops_1)).

tff(f_48,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_pre_topc(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_pre_topc)).

tff(f_29,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k3_subset_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,k3_subset_1(A,B)) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

tff(f_64,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v2_tops_1(B,A)
          <=> v1_tops_1(k3_subset_1(u1_struct_0(A),B),A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tops_1)).

tff(f_55,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => r1_tarski(B,k2_pre_topc(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_pre_topc)).

tff(f_42,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(A))
         => ( r1_tarski(k3_subset_1(A,B),C)
           => r1_tarski(k3_subset_1(A,C),B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_subset_1)).

tff(f_73,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v3_tops_1(B,A)
          <=> v2_tops_1(k2_pre_topc(A,B),A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_tops_1)).

tff(f_87,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( ( v1_tops_1(B,A)
                  & r1_tarski(B,C) )
               => v1_tops_1(C,A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_tops_1)).

tff(c_28,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_26,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_8,plain,(
    ! [A_9,B_10] :
      ( m1_subset_1(k2_pre_topc(A_9,B_10),k1_zfmisc_1(u1_struct_0(A_9)))
      | ~ m1_subset_1(B_10,k1_zfmisc_1(u1_struct_0(A_9)))
      | ~ l1_pre_topc(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( m1_subset_1(k3_subset_1(A_1,B_2),k1_zfmisc_1(A_1))
      | ~ m1_subset_1(B_2,k1_zfmisc_1(A_1)) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_29,plain,(
    ! [A_28,B_29] :
      ( k3_subset_1(A_28,k3_subset_1(A_28,B_29)) = B_29
      | ~ m1_subset_1(B_29,k1_zfmisc_1(A_28)) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_32,plain,(
    k3_subset_1(u1_struct_0('#skF_1'),k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')) = '#skF_2' ),
    inference(resolution,[status(thm)],[c_26,c_29])).

tff(c_119,plain,(
    ! [B_42,A_43] :
      ( v2_tops_1(B_42,A_43)
      | ~ v1_tops_1(k3_subset_1(u1_struct_0(A_43),B_42),A_43)
      | ~ m1_subset_1(B_42,k1_zfmisc_1(u1_struct_0(A_43)))
      | ~ l1_pre_topc(A_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_126,plain,
    ( v2_tops_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),'#skF_1')
    | ~ v1_tops_1('#skF_2','#skF_1')
    | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_119])).

tff(c_128,plain,
    ( v2_tops_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),'#skF_1')
    | ~ v1_tops_1('#skF_2','#skF_1')
    | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_126])).

tff(c_150,plain,(
    ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_128])).

tff(c_154,plain,(
    ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_2,c_150])).

tff(c_158,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_154])).

tff(c_160,plain,(
    m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_128])).

tff(c_45,plain,(
    ! [B_32,A_33] :
      ( r1_tarski(B_32,k2_pre_topc(A_33,B_32))
      | ~ m1_subset_1(B_32,k1_zfmisc_1(u1_struct_0(A_33)))
      | ~ l1_pre_topc(A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_207,plain,(
    ! [A_52,B_53] :
      ( r1_tarski(k3_subset_1(u1_struct_0(A_52),B_53),k2_pre_topc(A_52,k3_subset_1(u1_struct_0(A_52),B_53)))
      | ~ l1_pre_topc(A_52)
      | ~ m1_subset_1(B_53,k1_zfmisc_1(u1_struct_0(A_52))) ) ),
    inference(resolution,[status(thm)],[c_2,c_45])).

tff(c_6,plain,(
    ! [A_5,C_8,B_6] :
      ( r1_tarski(k3_subset_1(A_5,C_8),B_6)
      | ~ r1_tarski(k3_subset_1(A_5,B_6),C_8)
      | ~ m1_subset_1(C_8,k1_zfmisc_1(A_5))
      | ~ m1_subset_1(B_6,k1_zfmisc_1(A_5)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_452,plain,(
    ! [A_65,B_66] :
      ( r1_tarski(k3_subset_1(u1_struct_0(A_65),k2_pre_topc(A_65,k3_subset_1(u1_struct_0(A_65),B_66))),B_66)
      | ~ m1_subset_1(k2_pre_topc(A_65,k3_subset_1(u1_struct_0(A_65),B_66)),k1_zfmisc_1(u1_struct_0(A_65)))
      | ~ l1_pre_topc(A_65)
      | ~ m1_subset_1(B_66,k1_zfmisc_1(u1_struct_0(A_65))) ) ),
    inference(resolution,[status(thm)],[c_207,c_6])).

tff(c_469,plain,
    ( r1_tarski(k3_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2')),k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'))
    | ~ m1_subset_1(k2_pre_topc('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'))),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1')
    | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_452])).

tff(c_475,plain,
    ( r1_tarski(k3_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2')),k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'))
    | ~ m1_subset_1(k2_pre_topc('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_160,c_28,c_32,c_469])).

tff(c_476,plain,(
    ~ m1_subset_1(k2_pre_topc('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_475])).

tff(c_479,plain,
    ( ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_8,c_476])).

tff(c_483,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_479])).

tff(c_485,plain,(
    m1_subset_1(k2_pre_topc('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_475])).

tff(c_50,plain,
    ( r1_tarski('#skF_2',k2_pre_topc('#skF_1','#skF_2'))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_26,c_45])).

tff(c_54,plain,(
    r1_tarski('#skF_2',k2_pre_topc('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_50])).

tff(c_24,plain,(
    v3_tops_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_100,plain,(
    ! [A_38,B_39] :
      ( v2_tops_1(k2_pre_topc(A_38,B_39),A_38)
      | ~ v3_tops_1(B_39,A_38)
      | ~ m1_subset_1(B_39,k1_zfmisc_1(u1_struct_0(A_38)))
      | ~ l1_pre_topc(A_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_107,plain,
    ( v2_tops_1(k2_pre_topc('#skF_1','#skF_2'),'#skF_1')
    | ~ v3_tops_1('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_26,c_100])).

tff(c_112,plain,(
    v2_tops_1(k2_pre_topc('#skF_1','#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_24,c_107])).

tff(c_4,plain,(
    ! [A_3,B_4] :
      ( k3_subset_1(A_3,k3_subset_1(A_3,B_4)) = B_4
      | ~ m1_subset_1(B_4,k1_zfmisc_1(A_3)) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_504,plain,(
    k3_subset_1(u1_struct_0('#skF_1'),k3_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2'))) = k2_pre_topc('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_485,c_4])).

tff(c_33,plain,(
    ! [A_30,B_31] :
      ( m1_subset_1(k3_subset_1(A_30,B_31),k1_zfmisc_1(A_30))
      | ~ m1_subset_1(B_31,k1_zfmisc_1(A_30)) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_36,plain,(
    ! [A_30,B_31] :
      ( k3_subset_1(A_30,k3_subset_1(A_30,k3_subset_1(A_30,B_31))) = k3_subset_1(A_30,B_31)
      | ~ m1_subset_1(B_31,k1_zfmisc_1(A_30)) ) ),
    inference(resolution,[status(thm)],[c_33,c_4])).

tff(c_129,plain,(
    ! [A_44,B_45] :
      ( v1_tops_1(k3_subset_1(u1_struct_0(A_44),B_45),A_44)
      | ~ v2_tops_1(B_45,A_44)
      | ~ m1_subset_1(B_45,k1_zfmisc_1(u1_struct_0(A_44)))
      | ~ l1_pre_topc(A_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_952,plain,(
    ! [A_83,B_84] :
      ( v1_tops_1(k3_subset_1(u1_struct_0(A_83),B_84),A_83)
      | ~ v2_tops_1(k3_subset_1(u1_struct_0(A_83),k3_subset_1(u1_struct_0(A_83),B_84)),A_83)
      | ~ m1_subset_1(k3_subset_1(u1_struct_0(A_83),k3_subset_1(u1_struct_0(A_83),B_84)),k1_zfmisc_1(u1_struct_0(A_83)))
      | ~ l1_pre_topc(A_83)
      | ~ m1_subset_1(B_84,k1_zfmisc_1(u1_struct_0(A_83))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_129])).

tff(c_958,plain,
    ( v1_tops_1(k3_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2')),'#skF_1')
    | ~ v2_tops_1(k3_subset_1(u1_struct_0('#skF_1'),k3_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2'))),'#skF_1')
    | ~ m1_subset_1(k2_pre_topc('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1')
    | ~ m1_subset_1(k2_pre_topc('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_504,c_952])).

tff(c_992,plain,(
    v1_tops_1(k3_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2')),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_485,c_28,c_485,c_112,c_504,c_958])).

tff(c_14,plain,(
    ! [A_14,B_16] :
      ( v1_tops_1(k3_subset_1(u1_struct_0(A_14),B_16),A_14)
      | ~ v2_tops_1(B_16,A_14)
      | ~ m1_subset_1(B_16,k1_zfmisc_1(u1_struct_0(A_14)))
      | ~ l1_pre_topc(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_545,plain,
    ( v1_tops_1(k2_pre_topc('#skF_1','#skF_2'),'#skF_1')
    | ~ v2_tops_1(k3_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2')),'#skF_1')
    | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2')),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_504,c_14])).

tff(c_578,plain,
    ( v1_tops_1(k2_pre_topc('#skF_1','#skF_2'),'#skF_1')
    | ~ v2_tops_1(k3_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2')),'#skF_1')
    | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2')),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_545])).

tff(c_778,plain,(
    ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2')),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_578])).

tff(c_781,plain,(
    ~ m1_subset_1(k2_pre_topc('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_2,c_778])).

tff(c_785,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_485,c_781])).

tff(c_787,plain,(
    m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2')),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_578])).

tff(c_22,plain,(
    ~ v1_tops_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),'#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_176,plain,(
    ! [A_48,C_49,B_50] :
      ( r1_tarski(k3_subset_1(A_48,C_49),B_50)
      | ~ r1_tarski(k3_subset_1(A_48,B_50),C_49)
      | ~ m1_subset_1(C_49,k1_zfmisc_1(A_48))
      | ~ m1_subset_1(B_50,k1_zfmisc_1(A_48)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_182,plain,(
    ! [C_49] :
      ( r1_tarski(k3_subset_1(u1_struct_0('#skF_1'),C_49),k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'))
      | ~ r1_tarski('#skF_2',C_49)
      | ~ m1_subset_1(C_49,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_176])).

tff(c_187,plain,(
    ! [C_49] :
      ( r1_tarski(k3_subset_1(u1_struct_0('#skF_1'),C_49),k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'))
      | ~ r1_tarski('#skF_2',C_49)
      | ~ m1_subset_1(C_49,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_160,c_182])).

tff(c_273,plain,(
    ! [C_58,A_59,B_60] :
      ( v1_tops_1(C_58,A_59)
      | ~ r1_tarski(B_60,C_58)
      | ~ v1_tops_1(B_60,A_59)
      | ~ m1_subset_1(C_58,k1_zfmisc_1(u1_struct_0(A_59)))
      | ~ m1_subset_1(B_60,k1_zfmisc_1(u1_struct_0(A_59)))
      | ~ l1_pre_topc(A_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_1130,plain,(
    ! [A_87,C_88] :
      ( v1_tops_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),A_87)
      | ~ v1_tops_1(k3_subset_1(u1_struct_0('#skF_1'),C_88),A_87)
      | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(u1_struct_0(A_87)))
      | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'),C_88),k1_zfmisc_1(u1_struct_0(A_87)))
      | ~ l1_pre_topc(A_87)
      | ~ r1_tarski('#skF_2',C_88)
      | ~ m1_subset_1(C_88,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(resolution,[status(thm)],[c_187,c_273])).

tff(c_1132,plain,(
    ! [C_88] :
      ( v1_tops_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),'#skF_1')
      | ~ v1_tops_1(k3_subset_1(u1_struct_0('#skF_1'),C_88),'#skF_1')
      | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'),C_88),k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1')
      | ~ r1_tarski('#skF_2',C_88)
      | ~ m1_subset_1(C_88,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(resolution,[status(thm)],[c_160,c_1130])).

tff(c_1138,plain,(
    ! [C_88] :
      ( v1_tops_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),'#skF_1')
      | ~ v1_tops_1(k3_subset_1(u1_struct_0('#skF_1'),C_88),'#skF_1')
      | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'),C_88),k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ r1_tarski('#skF_2',C_88)
      | ~ m1_subset_1(C_88,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_1132])).

tff(c_1144,plain,(
    ! [C_89] :
      ( ~ v1_tops_1(k3_subset_1(u1_struct_0('#skF_1'),C_89),'#skF_1')
      | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'),C_89),k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ r1_tarski('#skF_2',C_89)
      | ~ m1_subset_1(C_89,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_22,c_1138])).

tff(c_1150,plain,
    ( ~ v1_tops_1(k3_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2')),'#skF_1')
    | ~ r1_tarski('#skF_2',k2_pre_topc('#skF_1','#skF_2'))
    | ~ m1_subset_1(k2_pre_topc('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_787,c_1144])).

tff(c_1181,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_485,c_54,c_992,c_1150])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n010.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 11:37:44 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.16/1.51  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.40/1.52  
% 3.40/1.52  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.40/1.52  %$ v3_tops_1 > v2_tops_1 > v1_tops_1 > r1_tarski > m1_subset_1 > l1_pre_topc > k3_subset_1 > k2_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_1
% 3.40/1.52  
% 3.40/1.52  %Foreground sorts:
% 3.40/1.52  
% 3.40/1.52  
% 3.40/1.52  %Background operators:
% 3.40/1.52  
% 3.40/1.52  
% 3.40/1.52  %Foreground operators:
% 3.40/1.52  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.40/1.52  tff(v2_tops_1, type, v2_tops_1: ($i * $i) > $o).
% 3.40/1.52  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.40/1.52  tff(v3_tops_1, type, v3_tops_1: ($i * $i) > $o).
% 3.40/1.52  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.40/1.52  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 3.40/1.52  tff(v1_tops_1, type, v1_tops_1: ($i * $i) > $o).
% 3.40/1.52  tff('#skF_2', type, '#skF_2': $i).
% 3.40/1.52  tff('#skF_1', type, '#skF_1': $i).
% 3.40/1.52  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.40/1.52  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.40/1.52  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.40/1.52  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.40/1.52  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 3.40/1.52  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.40/1.52  
% 3.40/1.54  tff(f_97, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_tops_1(B, A) => v1_tops_1(k3_subset_1(u1_struct_0(A), B), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_tops_1)).
% 3.40/1.54  tff(f_48, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_pre_topc(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_pre_topc)).
% 3.40/1.54  tff(f_29, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k3_subset_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 3.40/1.54  tff(f_33, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, k3_subset_1(A, B)) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 3.40/1.54  tff(f_64, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tops_1(B, A) <=> v1_tops_1(k3_subset_1(u1_struct_0(A), B), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_tops_1)).
% 3.40/1.54  tff(f_55, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => r1_tarski(B, k2_pre_topc(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_pre_topc)).
% 3.40/1.54  tff(f_42, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (r1_tarski(k3_subset_1(A, B), C) => r1_tarski(k3_subset_1(A, C), B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_subset_1)).
% 3.40/1.54  tff(f_73, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_tops_1(B, A) <=> v2_tops_1(k2_pre_topc(A, B), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_tops_1)).
% 3.40/1.54  tff(f_87, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((v1_tops_1(B, A) & r1_tarski(B, C)) => v1_tops_1(C, A)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_tops_1)).
% 3.40/1.54  tff(c_28, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_97])).
% 3.40/1.54  tff(c_26, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_97])).
% 3.40/1.54  tff(c_8, plain, (![A_9, B_10]: (m1_subset_1(k2_pre_topc(A_9, B_10), k1_zfmisc_1(u1_struct_0(A_9))) | ~m1_subset_1(B_10, k1_zfmisc_1(u1_struct_0(A_9))) | ~l1_pre_topc(A_9))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.40/1.54  tff(c_2, plain, (![A_1, B_2]: (m1_subset_1(k3_subset_1(A_1, B_2), k1_zfmisc_1(A_1)) | ~m1_subset_1(B_2, k1_zfmisc_1(A_1)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.40/1.54  tff(c_29, plain, (![A_28, B_29]: (k3_subset_1(A_28, k3_subset_1(A_28, B_29))=B_29 | ~m1_subset_1(B_29, k1_zfmisc_1(A_28)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.40/1.54  tff(c_32, plain, (k3_subset_1(u1_struct_0('#skF_1'), k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'))='#skF_2'), inference(resolution, [status(thm)], [c_26, c_29])).
% 3.40/1.54  tff(c_119, plain, (![B_42, A_43]: (v2_tops_1(B_42, A_43) | ~v1_tops_1(k3_subset_1(u1_struct_0(A_43), B_42), A_43) | ~m1_subset_1(B_42, k1_zfmisc_1(u1_struct_0(A_43))) | ~l1_pre_topc(A_43))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.40/1.54  tff(c_126, plain, (v2_tops_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), '#skF_1') | ~v1_tops_1('#skF_2', '#skF_1') | ~m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_32, c_119])).
% 3.40/1.54  tff(c_128, plain, (v2_tops_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), '#skF_1') | ~v1_tops_1('#skF_2', '#skF_1') | ~m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_126])).
% 3.40/1.54  tff(c_150, plain, (~m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitLeft, [status(thm)], [c_128])).
% 3.40/1.54  tff(c_154, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_2, c_150])).
% 3.40/1.54  tff(c_158, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_26, c_154])).
% 3.40/1.54  tff(c_160, plain, (m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitRight, [status(thm)], [c_128])).
% 3.40/1.54  tff(c_45, plain, (![B_32, A_33]: (r1_tarski(B_32, k2_pre_topc(A_33, B_32)) | ~m1_subset_1(B_32, k1_zfmisc_1(u1_struct_0(A_33))) | ~l1_pre_topc(A_33))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.40/1.54  tff(c_207, plain, (![A_52, B_53]: (r1_tarski(k3_subset_1(u1_struct_0(A_52), B_53), k2_pre_topc(A_52, k3_subset_1(u1_struct_0(A_52), B_53))) | ~l1_pre_topc(A_52) | ~m1_subset_1(B_53, k1_zfmisc_1(u1_struct_0(A_52))))), inference(resolution, [status(thm)], [c_2, c_45])).
% 3.40/1.54  tff(c_6, plain, (![A_5, C_8, B_6]: (r1_tarski(k3_subset_1(A_5, C_8), B_6) | ~r1_tarski(k3_subset_1(A_5, B_6), C_8) | ~m1_subset_1(C_8, k1_zfmisc_1(A_5)) | ~m1_subset_1(B_6, k1_zfmisc_1(A_5)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.40/1.54  tff(c_452, plain, (![A_65, B_66]: (r1_tarski(k3_subset_1(u1_struct_0(A_65), k2_pre_topc(A_65, k3_subset_1(u1_struct_0(A_65), B_66))), B_66) | ~m1_subset_1(k2_pre_topc(A_65, k3_subset_1(u1_struct_0(A_65), B_66)), k1_zfmisc_1(u1_struct_0(A_65))) | ~l1_pre_topc(A_65) | ~m1_subset_1(B_66, k1_zfmisc_1(u1_struct_0(A_65))))), inference(resolution, [status(thm)], [c_207, c_6])).
% 3.40/1.54  tff(c_469, plain, (r1_tarski(k3_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_2')), k3_subset_1(u1_struct_0('#skF_1'), '#skF_2')) | ~m1_subset_1(k2_pre_topc('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'))), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1') | ~m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_32, c_452])).
% 3.40/1.54  tff(c_475, plain, (r1_tarski(k3_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_2')), k3_subset_1(u1_struct_0('#skF_1'), '#skF_2')) | ~m1_subset_1(k2_pre_topc('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_160, c_28, c_32, c_469])).
% 3.40/1.54  tff(c_476, plain, (~m1_subset_1(k2_pre_topc('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitLeft, [status(thm)], [c_475])).
% 3.40/1.54  tff(c_479, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_8, c_476])).
% 3.40/1.54  tff(c_483, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_28, c_26, c_479])).
% 3.40/1.54  tff(c_485, plain, (m1_subset_1(k2_pre_topc('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitRight, [status(thm)], [c_475])).
% 3.40/1.54  tff(c_50, plain, (r1_tarski('#skF_2', k2_pre_topc('#skF_1', '#skF_2')) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_26, c_45])).
% 3.40/1.54  tff(c_54, plain, (r1_tarski('#skF_2', k2_pre_topc('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_50])).
% 3.40/1.54  tff(c_24, plain, (v3_tops_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_97])).
% 3.40/1.54  tff(c_100, plain, (![A_38, B_39]: (v2_tops_1(k2_pre_topc(A_38, B_39), A_38) | ~v3_tops_1(B_39, A_38) | ~m1_subset_1(B_39, k1_zfmisc_1(u1_struct_0(A_38))) | ~l1_pre_topc(A_38))), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.40/1.54  tff(c_107, plain, (v2_tops_1(k2_pre_topc('#skF_1', '#skF_2'), '#skF_1') | ~v3_tops_1('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_26, c_100])).
% 3.40/1.54  tff(c_112, plain, (v2_tops_1(k2_pre_topc('#skF_1', '#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_24, c_107])).
% 3.40/1.54  tff(c_4, plain, (![A_3, B_4]: (k3_subset_1(A_3, k3_subset_1(A_3, B_4))=B_4 | ~m1_subset_1(B_4, k1_zfmisc_1(A_3)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.40/1.54  tff(c_504, plain, (k3_subset_1(u1_struct_0('#skF_1'), k3_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_2')))=k2_pre_topc('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_485, c_4])).
% 3.40/1.54  tff(c_33, plain, (![A_30, B_31]: (m1_subset_1(k3_subset_1(A_30, B_31), k1_zfmisc_1(A_30)) | ~m1_subset_1(B_31, k1_zfmisc_1(A_30)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.40/1.54  tff(c_36, plain, (![A_30, B_31]: (k3_subset_1(A_30, k3_subset_1(A_30, k3_subset_1(A_30, B_31)))=k3_subset_1(A_30, B_31) | ~m1_subset_1(B_31, k1_zfmisc_1(A_30)))), inference(resolution, [status(thm)], [c_33, c_4])).
% 3.40/1.54  tff(c_129, plain, (![A_44, B_45]: (v1_tops_1(k3_subset_1(u1_struct_0(A_44), B_45), A_44) | ~v2_tops_1(B_45, A_44) | ~m1_subset_1(B_45, k1_zfmisc_1(u1_struct_0(A_44))) | ~l1_pre_topc(A_44))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.40/1.54  tff(c_952, plain, (![A_83, B_84]: (v1_tops_1(k3_subset_1(u1_struct_0(A_83), B_84), A_83) | ~v2_tops_1(k3_subset_1(u1_struct_0(A_83), k3_subset_1(u1_struct_0(A_83), B_84)), A_83) | ~m1_subset_1(k3_subset_1(u1_struct_0(A_83), k3_subset_1(u1_struct_0(A_83), B_84)), k1_zfmisc_1(u1_struct_0(A_83))) | ~l1_pre_topc(A_83) | ~m1_subset_1(B_84, k1_zfmisc_1(u1_struct_0(A_83))))), inference(superposition, [status(thm), theory('equality')], [c_36, c_129])).
% 3.40/1.54  tff(c_958, plain, (v1_tops_1(k3_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_2')), '#skF_1') | ~v2_tops_1(k3_subset_1(u1_struct_0('#skF_1'), k3_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_2'))), '#skF_1') | ~m1_subset_1(k2_pre_topc('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1') | ~m1_subset_1(k2_pre_topc('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_504, c_952])).
% 3.40/1.54  tff(c_992, plain, (v1_tops_1(k3_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_2')), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_485, c_28, c_485, c_112, c_504, c_958])).
% 3.40/1.54  tff(c_14, plain, (![A_14, B_16]: (v1_tops_1(k3_subset_1(u1_struct_0(A_14), B_16), A_14) | ~v2_tops_1(B_16, A_14) | ~m1_subset_1(B_16, k1_zfmisc_1(u1_struct_0(A_14))) | ~l1_pre_topc(A_14))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.40/1.54  tff(c_545, plain, (v1_tops_1(k2_pre_topc('#skF_1', '#skF_2'), '#skF_1') | ~v2_tops_1(k3_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_2')), '#skF_1') | ~m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_2')), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_504, c_14])).
% 3.40/1.54  tff(c_578, plain, (v1_tops_1(k2_pre_topc('#skF_1', '#skF_2'), '#skF_1') | ~v2_tops_1(k3_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_2')), '#skF_1') | ~m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_2')), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_545])).
% 3.40/1.54  tff(c_778, plain, (~m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_2')), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitLeft, [status(thm)], [c_578])).
% 3.40/1.54  tff(c_781, plain, (~m1_subset_1(k2_pre_topc('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_2, c_778])).
% 3.40/1.54  tff(c_785, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_485, c_781])).
% 3.40/1.54  tff(c_787, plain, (m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_2')), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitRight, [status(thm)], [c_578])).
% 3.40/1.54  tff(c_22, plain, (~v1_tops_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), '#skF_1')), inference(cnfTransformation, [status(thm)], [f_97])).
% 3.40/1.54  tff(c_176, plain, (![A_48, C_49, B_50]: (r1_tarski(k3_subset_1(A_48, C_49), B_50) | ~r1_tarski(k3_subset_1(A_48, B_50), C_49) | ~m1_subset_1(C_49, k1_zfmisc_1(A_48)) | ~m1_subset_1(B_50, k1_zfmisc_1(A_48)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.40/1.54  tff(c_182, plain, (![C_49]: (r1_tarski(k3_subset_1(u1_struct_0('#skF_1'), C_49), k3_subset_1(u1_struct_0('#skF_1'), '#skF_2')) | ~r1_tarski('#skF_2', C_49) | ~m1_subset_1(C_49, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(superposition, [status(thm), theory('equality')], [c_32, c_176])).
% 3.40/1.54  tff(c_187, plain, (![C_49]: (r1_tarski(k3_subset_1(u1_struct_0('#skF_1'), C_49), k3_subset_1(u1_struct_0('#skF_1'), '#skF_2')) | ~r1_tarski('#skF_2', C_49) | ~m1_subset_1(C_49, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_160, c_182])).
% 3.40/1.54  tff(c_273, plain, (![C_58, A_59, B_60]: (v1_tops_1(C_58, A_59) | ~r1_tarski(B_60, C_58) | ~v1_tops_1(B_60, A_59) | ~m1_subset_1(C_58, k1_zfmisc_1(u1_struct_0(A_59))) | ~m1_subset_1(B_60, k1_zfmisc_1(u1_struct_0(A_59))) | ~l1_pre_topc(A_59))), inference(cnfTransformation, [status(thm)], [f_87])).
% 3.40/1.54  tff(c_1130, plain, (![A_87, C_88]: (v1_tops_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), A_87) | ~v1_tops_1(k3_subset_1(u1_struct_0('#skF_1'), C_88), A_87) | ~m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(u1_struct_0(A_87))) | ~m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'), C_88), k1_zfmisc_1(u1_struct_0(A_87))) | ~l1_pre_topc(A_87) | ~r1_tarski('#skF_2', C_88) | ~m1_subset_1(C_88, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(resolution, [status(thm)], [c_187, c_273])).
% 3.40/1.54  tff(c_1132, plain, (![C_88]: (v1_tops_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), '#skF_1') | ~v1_tops_1(k3_subset_1(u1_struct_0('#skF_1'), C_88), '#skF_1') | ~m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'), C_88), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1') | ~r1_tarski('#skF_2', C_88) | ~m1_subset_1(C_88, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(resolution, [status(thm)], [c_160, c_1130])).
% 3.40/1.54  tff(c_1138, plain, (![C_88]: (v1_tops_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), '#skF_1') | ~v1_tops_1(k3_subset_1(u1_struct_0('#skF_1'), C_88), '#skF_1') | ~m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'), C_88), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~r1_tarski('#skF_2', C_88) | ~m1_subset_1(C_88, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_1132])).
% 3.40/1.54  tff(c_1144, plain, (![C_89]: (~v1_tops_1(k3_subset_1(u1_struct_0('#skF_1'), C_89), '#skF_1') | ~m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'), C_89), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~r1_tarski('#skF_2', C_89) | ~m1_subset_1(C_89, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(negUnitSimplification, [status(thm)], [c_22, c_1138])).
% 3.40/1.54  tff(c_1150, plain, (~v1_tops_1(k3_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_2')), '#skF_1') | ~r1_tarski('#skF_2', k2_pre_topc('#skF_1', '#skF_2')) | ~m1_subset_1(k2_pre_topc('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_787, c_1144])).
% 3.40/1.54  tff(c_1181, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_485, c_54, c_992, c_1150])).
% 3.40/1.54  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.40/1.54  
% 3.40/1.54  Inference rules
% 3.40/1.54  ----------------------
% 3.40/1.54  #Ref     : 0
% 3.40/1.54  #Sup     : 241
% 3.40/1.54  #Fact    : 0
% 3.40/1.54  #Define  : 0
% 3.40/1.54  #Split   : 18
% 3.40/1.54  #Chain   : 0
% 3.40/1.54  #Close   : 0
% 3.40/1.54  
% 3.40/1.54  Ordering : KBO
% 3.40/1.54  
% 3.40/1.54  Simplification rules
% 3.40/1.54  ----------------------
% 3.40/1.54  #Subsume      : 31
% 3.40/1.54  #Demod        : 320
% 3.40/1.54  #Tautology    : 68
% 3.40/1.54  #SimpNegUnit  : 21
% 3.40/1.54  #BackRed      : 0
% 3.40/1.54  
% 3.40/1.54  #Partial instantiations: 0
% 3.40/1.54  #Strategies tried      : 1
% 3.40/1.54  
% 3.40/1.54  Timing (in seconds)
% 3.40/1.54  ----------------------
% 3.40/1.54  Preprocessing        : 0.28
% 3.40/1.54  Parsing              : 0.16
% 3.40/1.54  CNF conversion       : 0.02
% 3.40/1.54  Main loop            : 0.48
% 3.40/1.54  Inferencing          : 0.16
% 3.40/1.54  Reduction            : 0.17
% 3.40/1.54  Demodulation         : 0.12
% 3.40/1.54  BG Simplification    : 0.02
% 3.40/1.54  Subsumption          : 0.10
% 3.40/1.54  Abstraction          : 0.02
% 3.40/1.54  MUC search           : 0.00
% 3.40/1.54  Cooper               : 0.00
% 3.40/1.54  Total                : 0.79
% 3.40/1.54  Index Insertion      : 0.00
% 3.40/1.54  Index Deletion       : 0.00
% 3.40/1.54  Index Matching       : 0.00
% 3.40/1.54  BG Taut test         : 0.00
%------------------------------------------------------------------------------
