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
% DateTime   : Thu Dec  3 10:20:47 EST 2020

% Result     : Theorem 5.42s
% Output     : CNFRefutation 5.79s
% Verified   : 
% Statistics : Number of formulae       :  145 ( 369 expanded)
%              Number of leaves         :   31 ( 132 expanded)
%              Depth                    :   17
%              Number of atoms          :  327 (1261 expanded)
%              Number of equality atoms :   20 (  56 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k3_subset_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

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

tff(v4_pre_topc,type,(
    v4_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_127,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B,C] :
            ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
           => ( r2_hidden(B,k1_tops_1(A,C))
            <=> ? [D] :
                  ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(A)))
                  & v3_pre_topc(D,A)
                  & r1_tarski(D,C)
                  & r2_hidden(B,D) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t54_tops_1)).

tff(f_80,axiom,(
    ! [A,B] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => v3_pre_topc(k1_tops_1(A,B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_tops_1)).

tff(f_96,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => r1_tarski(k1_tops_1(A,B),B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_tops_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_40,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,k3_subset_1(A,B)) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

tff(f_89,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v3_pre_topc(B,A)
          <=> v4_pre_topc(k3_subset_1(u1_struct_0(A),B),A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_tops_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k3_subset_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).

tff(f_59,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( ( v4_pre_topc(B,A)
             => k2_pre_topc(A,B) = B )
            & ( ( v2_pre_topc(A)
                & k2_pre_topc(A,B) = B )
             => v4_pre_topc(B,A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_pre_topc)).

tff(f_66,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k1_tops_1(A,B) = k3_subset_1(u1_struct_0(A),k2_pre_topc(A,k3_subset_1(u1_struct_0(A),B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tops_1)).

tff(f_108,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( r1_tarski(B,C)
               => r1_tarski(k1_tops_1(A,B),k1_tops_1(A,C)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_tops_1)).

tff(f_72,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k1_tops_1(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_tops_1)).

tff(c_34,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_32,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_30,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_4318,plain,(
    ! [A_398,B_399] :
      ( v3_pre_topc(k1_tops_1(A_398,B_399),A_398)
      | ~ m1_subset_1(B_399,k1_zfmisc_1(u1_struct_0(A_398)))
      | ~ l1_pre_topc(A_398)
      | ~ v2_pre_topc(A_398) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_4328,plain,
    ( v3_pre_topc(k1_tops_1('#skF_1','#skF_3'),'#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_30,c_4318])).

tff(c_4334,plain,(
    v3_pre_topc(k1_tops_1('#skF_1','#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_4328])).

tff(c_4128,plain,(
    ! [A_373,B_374] :
      ( r1_tarski(k1_tops_1(A_373,B_374),B_374)
      | ~ m1_subset_1(B_374,k1_zfmisc_1(u1_struct_0(A_373)))
      | ~ l1_pre_topc(A_373) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_4136,plain,
    ( r1_tarski(k1_tops_1('#skF_1','#skF_3'),'#skF_3')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_30,c_4128])).

tff(c_4141,plain,(
    r1_tarski(k1_tops_1('#skF_1','#skF_3'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_4136])).

tff(c_3573,plain,(
    ! [A_333,B_334] :
      ( v3_pre_topc(k1_tops_1(A_333,B_334),A_333)
      | ~ m1_subset_1(B_334,k1_zfmisc_1(u1_struct_0(A_333)))
      | ~ l1_pre_topc(A_333)
      | ~ v2_pre_topc(A_333) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_3583,plain,
    ( v3_pre_topc(k1_tops_1('#skF_1','#skF_3'),'#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_30,c_3573])).

tff(c_3589,plain,(
    v3_pre_topc(k1_tops_1('#skF_1','#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_3583])).

tff(c_2733,plain,(
    ! [A_256,B_257] :
      ( r1_tarski(k1_tops_1(A_256,B_257),B_257)
      | ~ m1_subset_1(B_257,k1_zfmisc_1(u1_struct_0(A_256)))
      | ~ l1_pre_topc(A_256) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_2741,plain,
    ( r1_tarski(k1_tops_1('#skF_1','#skF_3'),'#skF_3')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_30,c_2733])).

tff(c_2746,plain,(
    r1_tarski(k1_tops_1('#skF_1','#skF_3'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_2741])).

tff(c_2142,plain,(
    ! [A_210,B_211] :
      ( v3_pre_topc(k1_tops_1(A_210,B_211),A_210)
      | ~ m1_subset_1(B_211,k1_zfmisc_1(u1_struct_0(A_210)))
      | ~ l1_pre_topc(A_210)
      | ~ v2_pre_topc(A_210) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_2150,plain,
    ( v3_pre_topc(k1_tops_1('#skF_1','#skF_3'),'#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_30,c_2142])).

tff(c_2155,plain,(
    v3_pre_topc(k1_tops_1('#skF_1','#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_2150])).

tff(c_2025,plain,(
    ! [A_190,B_191] :
      ( r1_tarski(k1_tops_1(A_190,B_191),B_191)
      | ~ m1_subset_1(B_191,k1_zfmisc_1(u1_struct_0(A_190)))
      | ~ l1_pre_topc(A_190) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_2033,plain,
    ( r1_tarski(k1_tops_1('#skF_1','#skF_3'),'#skF_3')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_30,c_2025])).

tff(c_2038,plain,(
    r1_tarski(k1_tops_1('#skF_1','#skF_3'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_2033])).

tff(c_1446,plain,(
    ! [A_150,B_151] :
      ( v3_pre_topc(k1_tops_1(A_150,B_151),A_150)
      | ~ m1_subset_1(B_151,k1_zfmisc_1(u1_struct_0(A_150)))
      | ~ l1_pre_topc(A_150)
      | ~ v2_pre_topc(A_150) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_1456,plain,
    ( v3_pre_topc(k1_tops_1('#skF_1','#skF_3'),'#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_30,c_1446])).

tff(c_1462,plain,(
    v3_pre_topc(k1_tops_1('#skF_1','#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_1456])).

tff(c_1298,plain,(
    ! [A_126,B_127] :
      ( r1_tarski(k1_tops_1(A_126,B_127),B_127)
      | ~ m1_subset_1(B_127,k1_zfmisc_1(u1_struct_0(A_126)))
      | ~ l1_pre_topc(A_126) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_1306,plain,
    ( r1_tarski(k1_tops_1('#skF_1','#skF_3'),'#skF_3')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_30,c_1298])).

tff(c_1311,plain,(
    r1_tarski(k1_tops_1('#skF_1','#skF_3'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_1306])).

tff(c_50,plain,
    ( r2_hidden('#skF_2',k1_tops_1('#skF_1','#skF_3'))
    | v3_pre_topc('#skF_4','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_67,plain,(
    v3_pre_topc('#skF_4','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_50])).

tff(c_46,plain,
    ( r2_hidden('#skF_2',k1_tops_1('#skF_1','#skF_3'))
    | r1_tarski('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_65,plain,(
    r1_tarski('#skF_4','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_46])).

tff(c_42,plain,
    ( r2_hidden('#skF_2',k1_tops_1('#skF_1','#skF_3'))
    | r2_hidden('#skF_2','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_66,plain,(
    r2_hidden('#skF_2','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_42])).

tff(c_54,plain,
    ( r2_hidden('#skF_2',k1_tops_1('#skF_1','#skF_3'))
    | m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_110,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_54])).

tff(c_10,plain,(
    ! [A_9,B_10] :
      ( m1_subset_1(A_9,k1_zfmisc_1(B_10))
      | ~ r1_tarski(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_84,plain,(
    ! [C_53,A_54,B_55] :
      ( r2_hidden(C_53,A_54)
      | ~ r2_hidden(C_53,B_55)
      | ~ m1_subset_1(B_55,k1_zfmisc_1(A_54)) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_88,plain,(
    ! [A_56] :
      ( r2_hidden('#skF_2',A_56)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_56)) ) ),
    inference(resolution,[status(thm)],[c_66,c_84])).

tff(c_93,plain,(
    ! [B_10] :
      ( r2_hidden('#skF_2',B_10)
      | ~ r1_tarski('#skF_4',B_10) ) ),
    inference(resolution,[status(thm)],[c_10,c_88])).

tff(c_36,plain,(
    ! [D_42] :
      ( ~ r2_hidden('#skF_2',D_42)
      | ~ r1_tarski(D_42,'#skF_3')
      | ~ v3_pre_topc(D_42,'#skF_1')
      | ~ m1_subset_1(D_42,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ r2_hidden('#skF_2',k1_tops_1('#skF_1','#skF_3')) ) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_625,plain,(
    ~ r2_hidden('#skF_2',k1_tops_1('#skF_1','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_36])).

tff(c_633,plain,(
    ~ r1_tarski('#skF_4',k1_tops_1('#skF_1','#skF_3')) ),
    inference(resolution,[status(thm)],[c_93,c_625])).

tff(c_4,plain,(
    ! [A_3,B_4] :
      ( k3_subset_1(A_3,k3_subset_1(A_3,B_4)) = B_4
      | ~ m1_subset_1(B_4,k1_zfmisc_1(A_3)) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_120,plain,(
    k3_subset_1(u1_struct_0('#skF_1'),k3_subset_1(u1_struct_0('#skF_1'),'#skF_4')) = '#skF_4' ),
    inference(resolution,[status(thm)],[c_110,c_4])).

tff(c_24,plain,(
    ! [A_21,B_23] :
      ( v4_pre_topc(k3_subset_1(u1_struct_0(A_21),B_23),A_21)
      | ~ v3_pre_topc(B_23,A_21)
      | ~ m1_subset_1(B_23,k1_zfmisc_1(u1_struct_0(A_21)))
      | ~ l1_pre_topc(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( m1_subset_1(k3_subset_1(A_1,B_2),k1_zfmisc_1(A_1))
      | ~ m1_subset_1(B_2,k1_zfmisc_1(A_1)) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_269,plain,(
    ! [A_71,B_72] :
      ( k2_pre_topc(A_71,B_72) = B_72
      | ~ v4_pre_topc(B_72,A_71)
      | ~ m1_subset_1(B_72,k1_zfmisc_1(u1_struct_0(A_71)))
      | ~ l1_pre_topc(A_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_272,plain,
    ( k2_pre_topc('#skF_1','#skF_4') = '#skF_4'
    | ~ v4_pre_topc('#skF_4','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_110,c_269])).

tff(c_286,plain,
    ( k2_pre_topc('#skF_1','#skF_4') = '#skF_4'
    | ~ v4_pre_topc('#skF_4','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_272])).

tff(c_293,plain,(
    ~ v4_pre_topc('#skF_4','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_286])).

tff(c_507,plain,(
    ! [A_95,B_96] :
      ( v4_pre_topc(k3_subset_1(u1_struct_0(A_95),B_96),A_95)
      | ~ v3_pre_topc(B_96,A_95)
      | ~ m1_subset_1(B_96,k1_zfmisc_1(u1_struct_0(A_95)))
      | ~ l1_pre_topc(A_95) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_518,plain,
    ( v4_pre_topc('#skF_4','#skF_1')
    | ~ v3_pre_topc(k3_subset_1(u1_struct_0('#skF_1'),'#skF_4'),'#skF_1')
    | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_120,c_507])).

tff(c_523,plain,
    ( v4_pre_topc('#skF_4','#skF_1')
    | ~ v3_pre_topc(k3_subset_1(u1_struct_0('#skF_1'),'#skF_4'),'#skF_1')
    | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_518])).

tff(c_524,plain,
    ( ~ v3_pre_topc(k3_subset_1(u1_struct_0('#skF_1'),'#skF_4'),'#skF_1')
    | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(negUnitSimplification,[status(thm)],[c_293,c_523])).

tff(c_612,plain,(
    ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_524])).

tff(c_615,plain,(
    ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_2,c_612])).

tff(c_622,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_110,c_615])).

tff(c_624,plain,(
    m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_524])).

tff(c_12,plain,(
    ! [B_13,A_11] :
      ( v4_pre_topc(B_13,A_11)
      | k2_pre_topc(A_11,B_13) != B_13
      | ~ v2_pre_topc(A_11)
      | ~ m1_subset_1(B_13,k1_zfmisc_1(u1_struct_0(A_11)))
      | ~ l1_pre_topc(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_636,plain,
    ( v4_pre_topc(k3_subset_1(u1_struct_0('#skF_1'),'#skF_4'),'#skF_1')
    | k2_pre_topc('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_4')) != k3_subset_1(u1_struct_0('#skF_1'),'#skF_4')
    | ~ v2_pre_topc('#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_624,c_12])).

tff(c_657,plain,
    ( v4_pre_topc(k3_subset_1(u1_struct_0('#skF_1'),'#skF_4'),'#skF_1')
    | k2_pre_topc('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_4')) != k3_subset_1(u1_struct_0('#skF_1'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_34,c_636])).

tff(c_875,plain,(
    k2_pre_topc('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_4')) != k3_subset_1(u1_struct_0('#skF_1'),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_657])).

tff(c_14,plain,(
    ! [A_11,B_13] :
      ( k2_pre_topc(A_11,B_13) = B_13
      | ~ v4_pre_topc(B_13,A_11)
      | ~ m1_subset_1(B_13,k1_zfmisc_1(u1_struct_0(A_11)))
      | ~ l1_pre_topc(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_641,plain,
    ( k2_pre_topc('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_4')) = k3_subset_1(u1_struct_0('#skF_1'),'#skF_4')
    | ~ v4_pre_topc(k3_subset_1(u1_struct_0('#skF_1'),'#skF_4'),'#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_624,c_14])).

tff(c_663,plain,
    ( k2_pre_topc('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_4')) = k3_subset_1(u1_struct_0('#skF_1'),'#skF_4')
    | ~ v4_pre_topc(k3_subset_1(u1_struct_0('#skF_1'),'#skF_4'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_641])).

tff(c_908,plain,(
    ~ v4_pre_topc(k3_subset_1(u1_struct_0('#skF_1'),'#skF_4'),'#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_875,c_663])).

tff(c_911,plain,
    ( ~ v3_pre_topc('#skF_4','#skF_1')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_24,c_908])).

tff(c_915,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_110,c_67,c_911])).

tff(c_917,plain,(
    k2_pre_topc('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_4')) = k3_subset_1(u1_struct_0('#skF_1'),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_657])).

tff(c_16,plain,(
    ! [A_14,B_16] :
      ( k3_subset_1(u1_struct_0(A_14),k2_pre_topc(A_14,k3_subset_1(u1_struct_0(A_14),B_16))) = k1_tops_1(A_14,B_16)
      | ~ m1_subset_1(B_16,k1_zfmisc_1(u1_struct_0(A_14)))
      | ~ l1_pre_topc(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_927,plain,
    ( k3_subset_1(u1_struct_0('#skF_1'),k3_subset_1(u1_struct_0('#skF_1'),'#skF_4')) = k1_tops_1('#skF_1','#skF_4')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_917,c_16])).

tff(c_931,plain,(
    k1_tops_1('#skF_1','#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_110,c_120,c_927])).

tff(c_28,plain,(
    ! [A_27,B_31,C_33] :
      ( r1_tarski(k1_tops_1(A_27,B_31),k1_tops_1(A_27,C_33))
      | ~ r1_tarski(B_31,C_33)
      | ~ m1_subset_1(C_33,k1_zfmisc_1(u1_struct_0(A_27)))
      | ~ m1_subset_1(B_31,k1_zfmisc_1(u1_struct_0(A_27)))
      | ~ l1_pre_topc(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_978,plain,(
    ! [C_33] :
      ( r1_tarski('#skF_4',k1_tops_1('#skF_1',C_33))
      | ~ r1_tarski('#skF_4',C_33)
      | ~ m1_subset_1(C_33,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_931,c_28])).

tff(c_1105,plain,(
    ! [C_118] :
      ( r1_tarski('#skF_4',k1_tops_1('#skF_1',C_118))
      | ~ r1_tarski('#skF_4',C_118)
      | ~ m1_subset_1(C_118,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_110,c_978])).

tff(c_1129,plain,
    ( r1_tarski('#skF_4',k1_tops_1('#skF_1','#skF_3'))
    | ~ r1_tarski('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_30,c_1105])).

tff(c_1142,plain,(
    r1_tarski('#skF_4',k1_tops_1('#skF_1','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_65,c_1129])).

tff(c_1144,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_633,c_1142])).

tff(c_1190,plain,(
    ! [D_119] :
      ( ~ r2_hidden('#skF_2',D_119)
      | ~ r1_tarski(D_119,'#skF_3')
      | ~ v3_pre_topc(D_119,'#skF_1')
      | ~ m1_subset_1(D_119,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(splitRight,[status(thm)],[c_36])).

tff(c_1203,plain,
    ( ~ r2_hidden('#skF_2','#skF_4')
    | ~ r1_tarski('#skF_4','#skF_3')
    | ~ v3_pre_topc('#skF_4','#skF_1') ),
    inference(resolution,[status(thm)],[c_110,c_1190])).

tff(c_1223,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_67,c_65,c_66,c_1203])).

tff(c_1224,plain,(
    r2_hidden('#skF_2',k1_tops_1('#skF_1','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_18,plain,(
    ! [A_17,B_18] :
      ( m1_subset_1(k1_tops_1(A_17,B_18),k1_zfmisc_1(u1_struct_0(A_17)))
      | ~ m1_subset_1(B_18,k1_zfmisc_1(u1_struct_0(A_17)))
      | ~ l1_pre_topc(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_1487,plain,(
    ! [D_156] :
      ( ~ r2_hidden('#skF_2',D_156)
      | ~ r1_tarski(D_156,'#skF_3')
      | ~ v3_pre_topc(D_156,'#skF_1')
      | ~ m1_subset_1(D_156,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1224,c_36])).

tff(c_1491,plain,(
    ! [B_18] :
      ( ~ r2_hidden('#skF_2',k1_tops_1('#skF_1',B_18))
      | ~ r1_tarski(k1_tops_1('#skF_1',B_18),'#skF_3')
      | ~ v3_pre_topc(k1_tops_1('#skF_1',B_18),'#skF_1')
      | ~ m1_subset_1(B_18,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_18,c_1487])).

tff(c_1890,plain,(
    ! [B_175] :
      ( ~ r2_hidden('#skF_2',k1_tops_1('#skF_1',B_175))
      | ~ r1_tarski(k1_tops_1('#skF_1',B_175),'#skF_3')
      | ~ v3_pre_topc(k1_tops_1('#skF_1',B_175),'#skF_1')
      | ~ m1_subset_1(B_175,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_1491])).

tff(c_1908,plain,
    ( ~ r2_hidden('#skF_2',k1_tops_1('#skF_1','#skF_3'))
    | ~ r1_tarski(k1_tops_1('#skF_1','#skF_3'),'#skF_3')
    | ~ v3_pre_topc(k1_tops_1('#skF_1','#skF_3'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_30,c_1890])).

tff(c_1920,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1462,c_1311,c_1224,c_1908])).

tff(c_1921,plain,(
    r2_hidden('#skF_2',k1_tops_1('#skF_1','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_2210,plain,(
    ! [A_221,B_222] :
      ( m1_subset_1(k1_tops_1(A_221,B_222),k1_zfmisc_1(u1_struct_0(A_221)))
      | ~ m1_subset_1(B_222,k1_zfmisc_1(u1_struct_0(A_221)))
      | ~ l1_pre_topc(A_221) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_1922,plain,(
    ~ v3_pre_topc('#skF_4','#skF_1') ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_48,plain,(
    ! [D_42] :
      ( ~ r2_hidden('#skF_2',D_42)
      | ~ r1_tarski(D_42,'#skF_3')
      | ~ v3_pre_topc(D_42,'#skF_1')
      | ~ m1_subset_1(D_42,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | v3_pre_topc('#skF_4','#skF_1') ) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_1991,plain,(
    ! [D_42] :
      ( ~ r2_hidden('#skF_2',D_42)
      | ~ r1_tarski(D_42,'#skF_3')
      | ~ v3_pre_topc(D_42,'#skF_1')
      | ~ m1_subset_1(D_42,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_1922,c_48])).

tff(c_2231,plain,(
    ! [B_222] :
      ( ~ r2_hidden('#skF_2',k1_tops_1('#skF_1',B_222))
      | ~ r1_tarski(k1_tops_1('#skF_1',B_222),'#skF_3')
      | ~ v3_pre_topc(k1_tops_1('#skF_1',B_222),'#skF_1')
      | ~ m1_subset_1(B_222,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_2210,c_1991])).

tff(c_2620,plain,(
    ! [B_242] :
      ( ~ r2_hidden('#skF_2',k1_tops_1('#skF_1',B_242))
      | ~ r1_tarski(k1_tops_1('#skF_1',B_242),'#skF_3')
      | ~ v3_pre_topc(k1_tops_1('#skF_1',B_242),'#skF_1')
      | ~ m1_subset_1(B_242,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_2231])).

tff(c_2638,plain,
    ( ~ r2_hidden('#skF_2',k1_tops_1('#skF_1','#skF_3'))
    | ~ r1_tarski(k1_tops_1('#skF_1','#skF_3'),'#skF_3')
    | ~ v3_pre_topc(k1_tops_1('#skF_1','#skF_3'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_30,c_2620])).

tff(c_2650,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2155,c_2038,c_1921,c_2638])).

tff(c_2651,plain,(
    r2_hidden('#skF_2',k1_tops_1('#skF_1','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_2652,plain,(
    ~ r2_hidden('#skF_2','#skF_4') ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_40,plain,(
    ! [D_42] :
      ( ~ r2_hidden('#skF_2',D_42)
      | ~ r1_tarski(D_42,'#skF_3')
      | ~ v3_pre_topc(D_42,'#skF_1')
      | ~ m1_subset_1(D_42,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | r2_hidden('#skF_2','#skF_4') ) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_3671,plain,(
    ! [D_341] :
      ( ~ r2_hidden('#skF_2',D_341)
      | ~ r1_tarski(D_341,'#skF_3')
      | ~ v3_pre_topc(D_341,'#skF_1')
      | ~ m1_subset_1(D_341,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_2652,c_40])).

tff(c_3675,plain,(
    ! [B_18] :
      ( ~ r2_hidden('#skF_2',k1_tops_1('#skF_1',B_18))
      | ~ r1_tarski(k1_tops_1('#skF_1',B_18),'#skF_3')
      | ~ v3_pre_topc(k1_tops_1('#skF_1',B_18),'#skF_1')
      | ~ m1_subset_1(B_18,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_18,c_3671])).

tff(c_4004,plain,(
    ! [B_360] :
      ( ~ r2_hidden('#skF_2',k1_tops_1('#skF_1',B_360))
      | ~ r1_tarski(k1_tops_1('#skF_1',B_360),'#skF_3')
      | ~ v3_pre_topc(k1_tops_1('#skF_1',B_360),'#skF_1')
      | ~ m1_subset_1(B_360,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_3675])).

tff(c_4022,plain,
    ( ~ r2_hidden('#skF_2',k1_tops_1('#skF_1','#skF_3'))
    | ~ r1_tarski(k1_tops_1('#skF_1','#skF_3'),'#skF_3')
    | ~ v3_pre_topc(k1_tops_1('#skF_1','#skF_3'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_30,c_4004])).

tff(c_4034,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3589,c_2746,c_2651,c_4022])).

tff(c_4035,plain,(
    r2_hidden('#skF_2',k1_tops_1('#skF_1','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_4249,plain,(
    ! [A_393,B_394] :
      ( m1_subset_1(k1_tops_1(A_393,B_394),k1_zfmisc_1(u1_struct_0(A_393)))
      | ~ m1_subset_1(B_394,k1_zfmisc_1(u1_struct_0(A_393)))
      | ~ l1_pre_topc(A_393) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_4036,plain,(
    ~ r1_tarski('#skF_4','#skF_3') ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_44,plain,(
    ! [D_42] :
      ( ~ r2_hidden('#skF_2',D_42)
      | ~ r1_tarski(D_42,'#skF_3')
      | ~ v3_pre_topc(D_42,'#skF_1')
      | ~ m1_subset_1(D_42,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | r1_tarski('#skF_4','#skF_3') ) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_4056,plain,(
    ! [D_42] :
      ( ~ r2_hidden('#skF_2',D_42)
      | ~ r1_tarski(D_42,'#skF_3')
      | ~ v3_pre_topc(D_42,'#skF_1')
      | ~ m1_subset_1(D_42,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_4036,c_44])).

tff(c_4265,plain,(
    ! [B_394] :
      ( ~ r2_hidden('#skF_2',k1_tops_1('#skF_1',B_394))
      | ~ r1_tarski(k1_tops_1('#skF_1',B_394),'#skF_3')
      | ~ v3_pre_topc(k1_tops_1('#skF_1',B_394),'#skF_1')
      | ~ m1_subset_1(B_394,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_4249,c_4056])).

tff(c_4820,plain,(
    ! [B_432] :
      ( ~ r2_hidden('#skF_2',k1_tops_1('#skF_1',B_432))
      | ~ r1_tarski(k1_tops_1('#skF_1',B_432),'#skF_3')
      | ~ v3_pre_topc(k1_tops_1('#skF_1',B_432),'#skF_1')
      | ~ m1_subset_1(B_432,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_4265])).

tff(c_4838,plain,
    ( ~ r2_hidden('#skF_2',k1_tops_1('#skF_1','#skF_3'))
    | ~ r1_tarski(k1_tops_1('#skF_1','#skF_3'),'#skF_3')
    | ~ v3_pre_topc(k1_tops_1('#skF_1','#skF_3'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_30,c_4820])).

tff(c_4850,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4334,c_4141,c_4035,c_4838])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:05:23 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.42/2.05  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.42/2.06  
% 5.42/2.06  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.42/2.06  %$ v4_pre_topc > v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k3_subset_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 5.42/2.06  
% 5.42/2.06  %Foreground sorts:
% 5.42/2.06  
% 5.42/2.06  
% 5.42/2.06  %Background operators:
% 5.42/2.06  
% 5.42/2.06  
% 5.42/2.06  %Foreground operators:
% 5.42/2.06  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 5.42/2.06  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.42/2.06  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.42/2.06  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 5.42/2.06  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.42/2.06  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 5.42/2.06  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 5.42/2.06  tff('#skF_2', type, '#skF_2': $i).
% 5.42/2.06  tff('#skF_3', type, '#skF_3': $i).
% 5.42/2.06  tff('#skF_1', type, '#skF_1': $i).
% 5.42/2.06  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.42/2.06  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 5.42/2.06  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.42/2.06  tff('#skF_4', type, '#skF_4': $i).
% 5.42/2.06  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.42/2.06  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 5.42/2.06  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 5.42/2.06  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 5.42/2.06  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.42/2.06  
% 5.79/2.08  tff(f_127, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B, C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (r2_hidden(B, k1_tops_1(A, C)) <=> (?[D]: (((m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) & v3_pre_topc(D, A)) & r1_tarski(D, C)) & r2_hidden(B, D)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t54_tops_1)).
% 5.79/2.08  tff(f_80, axiom, (![A, B]: (((v2_pre_topc(A) & l1_pre_topc(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => v3_pre_topc(k1_tops_1(A, B), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc9_tops_1)).
% 5.79/2.08  tff(f_96, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => r1_tarski(k1_tops_1(A, B), B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_tops_1)).
% 5.79/2.08  tff(f_44, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 5.79/2.08  tff(f_40, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_subset_1)).
% 5.79/2.08  tff(f_33, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, k3_subset_1(A, B)) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 5.79/2.08  tff(f_89, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_pre_topc(B, A) <=> v4_pre_topc(k3_subset_1(u1_struct_0(A), B), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t30_tops_1)).
% 5.79/2.08  tff(f_29, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k3_subset_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 5.79/2.08  tff(f_59, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v4_pre_topc(B, A) => (k2_pre_topc(A, B) = B)) & ((v2_pre_topc(A) & (k2_pre_topc(A, B) = B)) => v4_pre_topc(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_pre_topc)).
% 5.79/2.08  tff(f_66, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k1_tops_1(A, B) = k3_subset_1(u1_struct_0(A), k2_pre_topc(A, k3_subset_1(u1_struct_0(A), B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tops_1)).
% 5.79/2.08  tff(f_108, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (r1_tarski(B, C) => r1_tarski(k1_tops_1(A, B), k1_tops_1(A, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_tops_1)).
% 5.79/2.08  tff(f_72, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k1_tops_1(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_tops_1)).
% 5.79/2.08  tff(c_34, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_127])).
% 5.79/2.08  tff(c_32, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_127])).
% 5.79/2.08  tff(c_30, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_127])).
% 5.79/2.08  tff(c_4318, plain, (![A_398, B_399]: (v3_pre_topc(k1_tops_1(A_398, B_399), A_398) | ~m1_subset_1(B_399, k1_zfmisc_1(u1_struct_0(A_398))) | ~l1_pre_topc(A_398) | ~v2_pre_topc(A_398))), inference(cnfTransformation, [status(thm)], [f_80])).
% 5.79/2.08  tff(c_4328, plain, (v3_pre_topc(k1_tops_1('#skF_1', '#skF_3'), '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_30, c_4318])).
% 5.79/2.08  tff(c_4334, plain, (v3_pre_topc(k1_tops_1('#skF_1', '#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_4328])).
% 5.79/2.08  tff(c_4128, plain, (![A_373, B_374]: (r1_tarski(k1_tops_1(A_373, B_374), B_374) | ~m1_subset_1(B_374, k1_zfmisc_1(u1_struct_0(A_373))) | ~l1_pre_topc(A_373))), inference(cnfTransformation, [status(thm)], [f_96])).
% 5.79/2.08  tff(c_4136, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_3'), '#skF_3') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_30, c_4128])).
% 5.79/2.08  tff(c_4141, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_3'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_4136])).
% 5.79/2.08  tff(c_3573, plain, (![A_333, B_334]: (v3_pre_topc(k1_tops_1(A_333, B_334), A_333) | ~m1_subset_1(B_334, k1_zfmisc_1(u1_struct_0(A_333))) | ~l1_pre_topc(A_333) | ~v2_pre_topc(A_333))), inference(cnfTransformation, [status(thm)], [f_80])).
% 5.79/2.08  tff(c_3583, plain, (v3_pre_topc(k1_tops_1('#skF_1', '#skF_3'), '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_30, c_3573])).
% 5.79/2.08  tff(c_3589, plain, (v3_pre_topc(k1_tops_1('#skF_1', '#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_3583])).
% 5.79/2.08  tff(c_2733, plain, (![A_256, B_257]: (r1_tarski(k1_tops_1(A_256, B_257), B_257) | ~m1_subset_1(B_257, k1_zfmisc_1(u1_struct_0(A_256))) | ~l1_pre_topc(A_256))), inference(cnfTransformation, [status(thm)], [f_96])).
% 5.79/2.08  tff(c_2741, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_3'), '#skF_3') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_30, c_2733])).
% 5.79/2.08  tff(c_2746, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_3'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_2741])).
% 5.79/2.08  tff(c_2142, plain, (![A_210, B_211]: (v3_pre_topc(k1_tops_1(A_210, B_211), A_210) | ~m1_subset_1(B_211, k1_zfmisc_1(u1_struct_0(A_210))) | ~l1_pre_topc(A_210) | ~v2_pre_topc(A_210))), inference(cnfTransformation, [status(thm)], [f_80])).
% 5.79/2.08  tff(c_2150, plain, (v3_pre_topc(k1_tops_1('#skF_1', '#skF_3'), '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_30, c_2142])).
% 5.79/2.08  tff(c_2155, plain, (v3_pre_topc(k1_tops_1('#skF_1', '#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_2150])).
% 5.79/2.08  tff(c_2025, plain, (![A_190, B_191]: (r1_tarski(k1_tops_1(A_190, B_191), B_191) | ~m1_subset_1(B_191, k1_zfmisc_1(u1_struct_0(A_190))) | ~l1_pre_topc(A_190))), inference(cnfTransformation, [status(thm)], [f_96])).
% 5.79/2.08  tff(c_2033, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_3'), '#skF_3') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_30, c_2025])).
% 5.79/2.08  tff(c_2038, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_3'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_2033])).
% 5.79/2.08  tff(c_1446, plain, (![A_150, B_151]: (v3_pre_topc(k1_tops_1(A_150, B_151), A_150) | ~m1_subset_1(B_151, k1_zfmisc_1(u1_struct_0(A_150))) | ~l1_pre_topc(A_150) | ~v2_pre_topc(A_150))), inference(cnfTransformation, [status(thm)], [f_80])).
% 5.79/2.08  tff(c_1456, plain, (v3_pre_topc(k1_tops_1('#skF_1', '#skF_3'), '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_30, c_1446])).
% 5.79/2.08  tff(c_1462, plain, (v3_pre_topc(k1_tops_1('#skF_1', '#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_1456])).
% 5.79/2.08  tff(c_1298, plain, (![A_126, B_127]: (r1_tarski(k1_tops_1(A_126, B_127), B_127) | ~m1_subset_1(B_127, k1_zfmisc_1(u1_struct_0(A_126))) | ~l1_pre_topc(A_126))), inference(cnfTransformation, [status(thm)], [f_96])).
% 5.79/2.08  tff(c_1306, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_3'), '#skF_3') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_30, c_1298])).
% 5.79/2.08  tff(c_1311, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_3'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_1306])).
% 5.79/2.08  tff(c_50, plain, (r2_hidden('#skF_2', k1_tops_1('#skF_1', '#skF_3')) | v3_pre_topc('#skF_4', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_127])).
% 5.79/2.08  tff(c_67, plain, (v3_pre_topc('#skF_4', '#skF_1')), inference(splitLeft, [status(thm)], [c_50])).
% 5.79/2.08  tff(c_46, plain, (r2_hidden('#skF_2', k1_tops_1('#skF_1', '#skF_3')) | r1_tarski('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_127])).
% 5.79/2.08  tff(c_65, plain, (r1_tarski('#skF_4', '#skF_3')), inference(splitLeft, [status(thm)], [c_46])).
% 5.79/2.08  tff(c_42, plain, (r2_hidden('#skF_2', k1_tops_1('#skF_1', '#skF_3')) | r2_hidden('#skF_2', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_127])).
% 5.79/2.08  tff(c_66, plain, (r2_hidden('#skF_2', '#skF_4')), inference(splitLeft, [status(thm)], [c_42])).
% 5.79/2.08  tff(c_54, plain, (r2_hidden('#skF_2', k1_tops_1('#skF_1', '#skF_3')) | m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_127])).
% 5.79/2.08  tff(c_110, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitLeft, [status(thm)], [c_54])).
% 5.79/2.08  tff(c_10, plain, (![A_9, B_10]: (m1_subset_1(A_9, k1_zfmisc_1(B_10)) | ~r1_tarski(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_44])).
% 5.79/2.08  tff(c_84, plain, (![C_53, A_54, B_55]: (r2_hidden(C_53, A_54) | ~r2_hidden(C_53, B_55) | ~m1_subset_1(B_55, k1_zfmisc_1(A_54)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 5.79/2.08  tff(c_88, plain, (![A_56]: (r2_hidden('#skF_2', A_56) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_56)))), inference(resolution, [status(thm)], [c_66, c_84])).
% 5.79/2.08  tff(c_93, plain, (![B_10]: (r2_hidden('#skF_2', B_10) | ~r1_tarski('#skF_4', B_10))), inference(resolution, [status(thm)], [c_10, c_88])).
% 5.79/2.08  tff(c_36, plain, (![D_42]: (~r2_hidden('#skF_2', D_42) | ~r1_tarski(D_42, '#skF_3') | ~v3_pre_topc(D_42, '#skF_1') | ~m1_subset_1(D_42, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~r2_hidden('#skF_2', k1_tops_1('#skF_1', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_127])).
% 5.79/2.08  tff(c_625, plain, (~r2_hidden('#skF_2', k1_tops_1('#skF_1', '#skF_3'))), inference(splitLeft, [status(thm)], [c_36])).
% 5.79/2.08  tff(c_633, plain, (~r1_tarski('#skF_4', k1_tops_1('#skF_1', '#skF_3'))), inference(resolution, [status(thm)], [c_93, c_625])).
% 5.79/2.08  tff(c_4, plain, (![A_3, B_4]: (k3_subset_1(A_3, k3_subset_1(A_3, B_4))=B_4 | ~m1_subset_1(B_4, k1_zfmisc_1(A_3)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 5.79/2.08  tff(c_120, plain, (k3_subset_1(u1_struct_0('#skF_1'), k3_subset_1(u1_struct_0('#skF_1'), '#skF_4'))='#skF_4'), inference(resolution, [status(thm)], [c_110, c_4])).
% 5.79/2.08  tff(c_24, plain, (![A_21, B_23]: (v4_pre_topc(k3_subset_1(u1_struct_0(A_21), B_23), A_21) | ~v3_pre_topc(B_23, A_21) | ~m1_subset_1(B_23, k1_zfmisc_1(u1_struct_0(A_21))) | ~l1_pre_topc(A_21))), inference(cnfTransformation, [status(thm)], [f_89])).
% 5.79/2.08  tff(c_2, plain, (![A_1, B_2]: (m1_subset_1(k3_subset_1(A_1, B_2), k1_zfmisc_1(A_1)) | ~m1_subset_1(B_2, k1_zfmisc_1(A_1)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 5.79/2.08  tff(c_269, plain, (![A_71, B_72]: (k2_pre_topc(A_71, B_72)=B_72 | ~v4_pre_topc(B_72, A_71) | ~m1_subset_1(B_72, k1_zfmisc_1(u1_struct_0(A_71))) | ~l1_pre_topc(A_71))), inference(cnfTransformation, [status(thm)], [f_59])).
% 5.79/2.08  tff(c_272, plain, (k2_pre_topc('#skF_1', '#skF_4')='#skF_4' | ~v4_pre_topc('#skF_4', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_110, c_269])).
% 5.79/2.08  tff(c_286, plain, (k2_pre_topc('#skF_1', '#skF_4')='#skF_4' | ~v4_pre_topc('#skF_4', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_272])).
% 5.79/2.08  tff(c_293, plain, (~v4_pre_topc('#skF_4', '#skF_1')), inference(splitLeft, [status(thm)], [c_286])).
% 5.79/2.08  tff(c_507, plain, (![A_95, B_96]: (v4_pre_topc(k3_subset_1(u1_struct_0(A_95), B_96), A_95) | ~v3_pre_topc(B_96, A_95) | ~m1_subset_1(B_96, k1_zfmisc_1(u1_struct_0(A_95))) | ~l1_pre_topc(A_95))), inference(cnfTransformation, [status(thm)], [f_89])).
% 5.79/2.08  tff(c_518, plain, (v4_pre_topc('#skF_4', '#skF_1') | ~v3_pre_topc(k3_subset_1(u1_struct_0('#skF_1'), '#skF_4'), '#skF_1') | ~m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_120, c_507])).
% 5.79/2.08  tff(c_523, plain, (v4_pre_topc('#skF_4', '#skF_1') | ~v3_pre_topc(k3_subset_1(u1_struct_0('#skF_1'), '#skF_4'), '#skF_1') | ~m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_518])).
% 5.79/2.08  tff(c_524, plain, (~v3_pre_topc(k3_subset_1(u1_struct_0('#skF_1'), '#skF_4'), '#skF_1') | ~m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(negUnitSimplification, [status(thm)], [c_293, c_523])).
% 5.79/2.08  tff(c_612, plain, (~m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitLeft, [status(thm)], [c_524])).
% 5.79/2.08  tff(c_615, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_2, c_612])).
% 5.79/2.08  tff(c_622, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_110, c_615])).
% 5.79/2.08  tff(c_624, plain, (m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitRight, [status(thm)], [c_524])).
% 5.79/2.08  tff(c_12, plain, (![B_13, A_11]: (v4_pre_topc(B_13, A_11) | k2_pre_topc(A_11, B_13)!=B_13 | ~v2_pre_topc(A_11) | ~m1_subset_1(B_13, k1_zfmisc_1(u1_struct_0(A_11))) | ~l1_pre_topc(A_11))), inference(cnfTransformation, [status(thm)], [f_59])).
% 5.79/2.08  tff(c_636, plain, (v4_pre_topc(k3_subset_1(u1_struct_0('#skF_1'), '#skF_4'), '#skF_1') | k2_pre_topc('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_4'))!=k3_subset_1(u1_struct_0('#skF_1'), '#skF_4') | ~v2_pre_topc('#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_624, c_12])).
% 5.79/2.08  tff(c_657, plain, (v4_pre_topc(k3_subset_1(u1_struct_0('#skF_1'), '#skF_4'), '#skF_1') | k2_pre_topc('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_4'))!=k3_subset_1(u1_struct_0('#skF_1'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_34, c_636])).
% 5.79/2.08  tff(c_875, plain, (k2_pre_topc('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_4'))!=k3_subset_1(u1_struct_0('#skF_1'), '#skF_4')), inference(splitLeft, [status(thm)], [c_657])).
% 5.79/2.08  tff(c_14, plain, (![A_11, B_13]: (k2_pre_topc(A_11, B_13)=B_13 | ~v4_pre_topc(B_13, A_11) | ~m1_subset_1(B_13, k1_zfmisc_1(u1_struct_0(A_11))) | ~l1_pre_topc(A_11))), inference(cnfTransformation, [status(thm)], [f_59])).
% 5.79/2.08  tff(c_641, plain, (k2_pre_topc('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_4'))=k3_subset_1(u1_struct_0('#skF_1'), '#skF_4') | ~v4_pre_topc(k3_subset_1(u1_struct_0('#skF_1'), '#skF_4'), '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_624, c_14])).
% 5.79/2.08  tff(c_663, plain, (k2_pre_topc('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_4'))=k3_subset_1(u1_struct_0('#skF_1'), '#skF_4') | ~v4_pre_topc(k3_subset_1(u1_struct_0('#skF_1'), '#skF_4'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_641])).
% 5.79/2.08  tff(c_908, plain, (~v4_pre_topc(k3_subset_1(u1_struct_0('#skF_1'), '#skF_4'), '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_875, c_663])).
% 5.79/2.08  tff(c_911, plain, (~v3_pre_topc('#skF_4', '#skF_1') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_24, c_908])).
% 5.79/2.08  tff(c_915, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_32, c_110, c_67, c_911])).
% 5.79/2.08  tff(c_917, plain, (k2_pre_topc('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_4'))=k3_subset_1(u1_struct_0('#skF_1'), '#skF_4')), inference(splitRight, [status(thm)], [c_657])).
% 5.79/2.08  tff(c_16, plain, (![A_14, B_16]: (k3_subset_1(u1_struct_0(A_14), k2_pre_topc(A_14, k3_subset_1(u1_struct_0(A_14), B_16)))=k1_tops_1(A_14, B_16) | ~m1_subset_1(B_16, k1_zfmisc_1(u1_struct_0(A_14))) | ~l1_pre_topc(A_14))), inference(cnfTransformation, [status(thm)], [f_66])).
% 5.79/2.08  tff(c_927, plain, (k3_subset_1(u1_struct_0('#skF_1'), k3_subset_1(u1_struct_0('#skF_1'), '#skF_4'))=k1_tops_1('#skF_1', '#skF_4') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_917, c_16])).
% 5.79/2.08  tff(c_931, plain, (k1_tops_1('#skF_1', '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_32, c_110, c_120, c_927])).
% 5.79/2.08  tff(c_28, plain, (![A_27, B_31, C_33]: (r1_tarski(k1_tops_1(A_27, B_31), k1_tops_1(A_27, C_33)) | ~r1_tarski(B_31, C_33) | ~m1_subset_1(C_33, k1_zfmisc_1(u1_struct_0(A_27))) | ~m1_subset_1(B_31, k1_zfmisc_1(u1_struct_0(A_27))) | ~l1_pre_topc(A_27))), inference(cnfTransformation, [status(thm)], [f_108])).
% 5.79/2.08  tff(c_978, plain, (![C_33]: (r1_tarski('#skF_4', k1_tops_1('#skF_1', C_33)) | ~r1_tarski('#skF_4', C_33) | ~m1_subset_1(C_33, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_931, c_28])).
% 5.79/2.08  tff(c_1105, plain, (![C_118]: (r1_tarski('#skF_4', k1_tops_1('#skF_1', C_118)) | ~r1_tarski('#skF_4', C_118) | ~m1_subset_1(C_118, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_110, c_978])).
% 5.79/2.08  tff(c_1129, plain, (r1_tarski('#skF_4', k1_tops_1('#skF_1', '#skF_3')) | ~r1_tarski('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_30, c_1105])).
% 5.79/2.08  tff(c_1142, plain, (r1_tarski('#skF_4', k1_tops_1('#skF_1', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_65, c_1129])).
% 5.79/2.08  tff(c_1144, plain, $false, inference(negUnitSimplification, [status(thm)], [c_633, c_1142])).
% 5.79/2.08  tff(c_1190, plain, (![D_119]: (~r2_hidden('#skF_2', D_119) | ~r1_tarski(D_119, '#skF_3') | ~v3_pre_topc(D_119, '#skF_1') | ~m1_subset_1(D_119, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(splitRight, [status(thm)], [c_36])).
% 5.79/2.08  tff(c_1203, plain, (~r2_hidden('#skF_2', '#skF_4') | ~r1_tarski('#skF_4', '#skF_3') | ~v3_pre_topc('#skF_4', '#skF_1')), inference(resolution, [status(thm)], [c_110, c_1190])).
% 5.79/2.08  tff(c_1223, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_67, c_65, c_66, c_1203])).
% 5.79/2.08  tff(c_1224, plain, (r2_hidden('#skF_2', k1_tops_1('#skF_1', '#skF_3'))), inference(splitRight, [status(thm)], [c_54])).
% 5.79/2.08  tff(c_18, plain, (![A_17, B_18]: (m1_subset_1(k1_tops_1(A_17, B_18), k1_zfmisc_1(u1_struct_0(A_17))) | ~m1_subset_1(B_18, k1_zfmisc_1(u1_struct_0(A_17))) | ~l1_pre_topc(A_17))), inference(cnfTransformation, [status(thm)], [f_72])).
% 5.79/2.08  tff(c_1487, plain, (![D_156]: (~r2_hidden('#skF_2', D_156) | ~r1_tarski(D_156, '#skF_3') | ~v3_pre_topc(D_156, '#skF_1') | ~m1_subset_1(D_156, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_1224, c_36])).
% 5.79/2.08  tff(c_1491, plain, (![B_18]: (~r2_hidden('#skF_2', k1_tops_1('#skF_1', B_18)) | ~r1_tarski(k1_tops_1('#skF_1', B_18), '#skF_3') | ~v3_pre_topc(k1_tops_1('#skF_1', B_18), '#skF_1') | ~m1_subset_1(B_18, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_18, c_1487])).
% 5.79/2.08  tff(c_1890, plain, (![B_175]: (~r2_hidden('#skF_2', k1_tops_1('#skF_1', B_175)) | ~r1_tarski(k1_tops_1('#skF_1', B_175), '#skF_3') | ~v3_pre_topc(k1_tops_1('#skF_1', B_175), '#skF_1') | ~m1_subset_1(B_175, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_1491])).
% 5.79/2.08  tff(c_1908, plain, (~r2_hidden('#skF_2', k1_tops_1('#skF_1', '#skF_3')) | ~r1_tarski(k1_tops_1('#skF_1', '#skF_3'), '#skF_3') | ~v3_pre_topc(k1_tops_1('#skF_1', '#skF_3'), '#skF_1')), inference(resolution, [status(thm)], [c_30, c_1890])).
% 5.79/2.08  tff(c_1920, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1462, c_1311, c_1224, c_1908])).
% 5.79/2.08  tff(c_1921, plain, (r2_hidden('#skF_2', k1_tops_1('#skF_1', '#skF_3'))), inference(splitRight, [status(thm)], [c_50])).
% 5.79/2.08  tff(c_2210, plain, (![A_221, B_222]: (m1_subset_1(k1_tops_1(A_221, B_222), k1_zfmisc_1(u1_struct_0(A_221))) | ~m1_subset_1(B_222, k1_zfmisc_1(u1_struct_0(A_221))) | ~l1_pre_topc(A_221))), inference(cnfTransformation, [status(thm)], [f_72])).
% 5.79/2.08  tff(c_1922, plain, (~v3_pre_topc('#skF_4', '#skF_1')), inference(splitRight, [status(thm)], [c_50])).
% 5.79/2.08  tff(c_48, plain, (![D_42]: (~r2_hidden('#skF_2', D_42) | ~r1_tarski(D_42, '#skF_3') | ~v3_pre_topc(D_42, '#skF_1') | ~m1_subset_1(D_42, k1_zfmisc_1(u1_struct_0('#skF_1'))) | v3_pre_topc('#skF_4', '#skF_1'))), inference(cnfTransformation, [status(thm)], [f_127])).
% 5.79/2.08  tff(c_1991, plain, (![D_42]: (~r2_hidden('#skF_2', D_42) | ~r1_tarski(D_42, '#skF_3') | ~v3_pre_topc(D_42, '#skF_1') | ~m1_subset_1(D_42, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(negUnitSimplification, [status(thm)], [c_1922, c_48])).
% 5.79/2.08  tff(c_2231, plain, (![B_222]: (~r2_hidden('#skF_2', k1_tops_1('#skF_1', B_222)) | ~r1_tarski(k1_tops_1('#skF_1', B_222), '#skF_3') | ~v3_pre_topc(k1_tops_1('#skF_1', B_222), '#skF_1') | ~m1_subset_1(B_222, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_2210, c_1991])).
% 5.79/2.08  tff(c_2620, plain, (![B_242]: (~r2_hidden('#skF_2', k1_tops_1('#skF_1', B_242)) | ~r1_tarski(k1_tops_1('#skF_1', B_242), '#skF_3') | ~v3_pre_topc(k1_tops_1('#skF_1', B_242), '#skF_1') | ~m1_subset_1(B_242, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_2231])).
% 5.79/2.08  tff(c_2638, plain, (~r2_hidden('#skF_2', k1_tops_1('#skF_1', '#skF_3')) | ~r1_tarski(k1_tops_1('#skF_1', '#skF_3'), '#skF_3') | ~v3_pre_topc(k1_tops_1('#skF_1', '#skF_3'), '#skF_1')), inference(resolution, [status(thm)], [c_30, c_2620])).
% 5.79/2.08  tff(c_2650, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2155, c_2038, c_1921, c_2638])).
% 5.79/2.08  tff(c_2651, plain, (r2_hidden('#skF_2', k1_tops_1('#skF_1', '#skF_3'))), inference(splitRight, [status(thm)], [c_42])).
% 5.79/2.08  tff(c_2652, plain, (~r2_hidden('#skF_2', '#skF_4')), inference(splitRight, [status(thm)], [c_42])).
% 5.79/2.08  tff(c_40, plain, (![D_42]: (~r2_hidden('#skF_2', D_42) | ~r1_tarski(D_42, '#skF_3') | ~v3_pre_topc(D_42, '#skF_1') | ~m1_subset_1(D_42, k1_zfmisc_1(u1_struct_0('#skF_1'))) | r2_hidden('#skF_2', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_127])).
% 5.79/2.08  tff(c_3671, plain, (![D_341]: (~r2_hidden('#skF_2', D_341) | ~r1_tarski(D_341, '#skF_3') | ~v3_pre_topc(D_341, '#skF_1') | ~m1_subset_1(D_341, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(negUnitSimplification, [status(thm)], [c_2652, c_40])).
% 5.79/2.08  tff(c_3675, plain, (![B_18]: (~r2_hidden('#skF_2', k1_tops_1('#skF_1', B_18)) | ~r1_tarski(k1_tops_1('#skF_1', B_18), '#skF_3') | ~v3_pre_topc(k1_tops_1('#skF_1', B_18), '#skF_1') | ~m1_subset_1(B_18, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_18, c_3671])).
% 5.79/2.08  tff(c_4004, plain, (![B_360]: (~r2_hidden('#skF_2', k1_tops_1('#skF_1', B_360)) | ~r1_tarski(k1_tops_1('#skF_1', B_360), '#skF_3') | ~v3_pre_topc(k1_tops_1('#skF_1', B_360), '#skF_1') | ~m1_subset_1(B_360, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_3675])).
% 5.79/2.08  tff(c_4022, plain, (~r2_hidden('#skF_2', k1_tops_1('#skF_1', '#skF_3')) | ~r1_tarski(k1_tops_1('#skF_1', '#skF_3'), '#skF_3') | ~v3_pre_topc(k1_tops_1('#skF_1', '#skF_3'), '#skF_1')), inference(resolution, [status(thm)], [c_30, c_4004])).
% 5.79/2.08  tff(c_4034, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3589, c_2746, c_2651, c_4022])).
% 5.79/2.08  tff(c_4035, plain, (r2_hidden('#skF_2', k1_tops_1('#skF_1', '#skF_3'))), inference(splitRight, [status(thm)], [c_46])).
% 5.79/2.08  tff(c_4249, plain, (![A_393, B_394]: (m1_subset_1(k1_tops_1(A_393, B_394), k1_zfmisc_1(u1_struct_0(A_393))) | ~m1_subset_1(B_394, k1_zfmisc_1(u1_struct_0(A_393))) | ~l1_pre_topc(A_393))), inference(cnfTransformation, [status(thm)], [f_72])).
% 5.79/2.08  tff(c_4036, plain, (~r1_tarski('#skF_4', '#skF_3')), inference(splitRight, [status(thm)], [c_46])).
% 5.79/2.08  tff(c_44, plain, (![D_42]: (~r2_hidden('#skF_2', D_42) | ~r1_tarski(D_42, '#skF_3') | ~v3_pre_topc(D_42, '#skF_1') | ~m1_subset_1(D_42, k1_zfmisc_1(u1_struct_0('#skF_1'))) | r1_tarski('#skF_4', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_127])).
% 5.79/2.08  tff(c_4056, plain, (![D_42]: (~r2_hidden('#skF_2', D_42) | ~r1_tarski(D_42, '#skF_3') | ~v3_pre_topc(D_42, '#skF_1') | ~m1_subset_1(D_42, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(negUnitSimplification, [status(thm)], [c_4036, c_44])).
% 5.79/2.08  tff(c_4265, plain, (![B_394]: (~r2_hidden('#skF_2', k1_tops_1('#skF_1', B_394)) | ~r1_tarski(k1_tops_1('#skF_1', B_394), '#skF_3') | ~v3_pre_topc(k1_tops_1('#skF_1', B_394), '#skF_1') | ~m1_subset_1(B_394, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_4249, c_4056])).
% 5.79/2.08  tff(c_4820, plain, (![B_432]: (~r2_hidden('#skF_2', k1_tops_1('#skF_1', B_432)) | ~r1_tarski(k1_tops_1('#skF_1', B_432), '#skF_3') | ~v3_pre_topc(k1_tops_1('#skF_1', B_432), '#skF_1') | ~m1_subset_1(B_432, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_4265])).
% 5.79/2.08  tff(c_4838, plain, (~r2_hidden('#skF_2', k1_tops_1('#skF_1', '#skF_3')) | ~r1_tarski(k1_tops_1('#skF_1', '#skF_3'), '#skF_3') | ~v3_pre_topc(k1_tops_1('#skF_1', '#skF_3'), '#skF_1')), inference(resolution, [status(thm)], [c_30, c_4820])).
% 5.79/2.08  tff(c_4850, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4334, c_4141, c_4035, c_4838])).
% 5.79/2.08  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.79/2.08  
% 5.79/2.08  Inference rules
% 5.79/2.08  ----------------------
% 5.79/2.08  #Ref     : 0
% 5.79/2.08  #Sup     : 1000
% 5.79/2.08  #Fact    : 0
% 5.79/2.08  #Define  : 0
% 5.79/2.08  #Split   : 41
% 5.79/2.08  #Chain   : 0
% 5.79/2.08  #Close   : 0
% 5.79/2.08  
% 5.79/2.08  Ordering : KBO
% 5.79/2.08  
% 5.79/2.08  Simplification rules
% 5.79/2.08  ----------------------
% 5.79/2.08  #Subsume      : 155
% 5.79/2.08  #Demod        : 607
% 5.79/2.08  #Tautology    : 300
% 5.79/2.08  #SimpNegUnit  : 46
% 5.79/2.08  #BackRed      : 2
% 5.79/2.08  
% 5.79/2.08  #Partial instantiations: 0
% 5.79/2.08  #Strategies tried      : 1
% 5.79/2.08  
% 5.79/2.08  Timing (in seconds)
% 5.79/2.08  ----------------------
% 5.88/2.08  Preprocessing        : 0.31
% 5.88/2.08  Parsing              : 0.18
% 5.88/2.08  CNF conversion       : 0.02
% 5.88/2.08  Main loop            : 0.98
% 5.88/2.08  Inferencing          : 0.37
% 5.88/2.08  Reduction            : 0.30
% 5.88/2.09  Demodulation         : 0.21
% 5.88/2.09  BG Simplification    : 0.04
% 5.88/2.09  Subsumption          : 0.20
% 5.88/2.09  Abstraction          : 0.04
% 5.88/2.09  MUC search           : 0.00
% 5.88/2.09  Cooper               : 0.00
% 5.88/2.09  Total                : 1.34
% 5.88/2.09  Index Insertion      : 0.00
% 5.88/2.09  Index Deletion       : 0.00
% 5.88/2.09  Index Matching       : 0.00
% 5.88/2.09  BG Taut test         : 0.00
%------------------------------------------------------------------------------
