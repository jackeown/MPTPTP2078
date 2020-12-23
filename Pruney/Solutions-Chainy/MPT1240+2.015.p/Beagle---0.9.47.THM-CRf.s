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

% Result     : Theorem 6.05s
% Output     : CNFRefutation 6.05s
% Verified   : 
% Statistics : Number of formulae       :  151 ( 342 expanded)
%              Number of leaves         :   34 ( 125 expanded)
%              Depth                    :   20
%              Number of atoms          :  333 (1144 expanded)
%              Number of equality atoms :   19 (  45 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k3_subset_1 > k2_xboole_0 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_128,negated_conjecture,(
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

tff(f_81,axiom,(
    ! [A,B] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => v3_pre_topc(k1_tops_1(A,B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_tops_1)).

tff(f_97,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => r1_tarski(k1_tops_1(A,B),B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_tops_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,k3_subset_1(A,B)) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

tff(f_90,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v3_pre_topc(B,A)
          <=> v4_pre_topc(k3_subset_1(u1_struct_0(A),B),A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_tops_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k3_subset_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).

tff(f_60,axiom,(
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

tff(f_67,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k1_tops_1(A,B) = k3_subset_1(u1_struct_0(A),k2_pre_topc(A,k3_subset_1(u1_struct_0(A),B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tops_1)).

tff(f_109,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( r1_tarski(B,C)
               => r1_tarski(k1_tops_1(A,B),k1_tops_1(A,C)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_tops_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_29,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_xboole_0(A,B),C)
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_xboole_1)).

tff(f_73,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k1_tops_1(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_tops_1)).

tff(c_36,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_34,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_32,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_4372,plain,(
    ! [A_447,B_448] :
      ( v3_pre_topc(k1_tops_1(A_447,B_448),A_447)
      | ~ m1_subset_1(B_448,k1_zfmisc_1(u1_struct_0(A_447)))
      | ~ l1_pre_topc(A_447)
      | ~ v2_pre_topc(A_447) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_4377,plain,
    ( v3_pre_topc(k1_tops_1('#skF_1','#skF_3'),'#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_4372])).

tff(c_4381,plain,(
    v3_pre_topc(k1_tops_1('#skF_1','#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_4377])).

tff(c_4348,plain,(
    ! [A_445,B_446] :
      ( r1_tarski(k1_tops_1(A_445,B_446),B_446)
      | ~ m1_subset_1(B_446,k1_zfmisc_1(u1_struct_0(A_445)))
      | ~ l1_pre_topc(A_445) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_4353,plain,
    ( r1_tarski(k1_tops_1('#skF_1','#skF_3'),'#skF_3')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_4348])).

tff(c_4357,plain,(
    r1_tarski(k1_tops_1('#skF_1','#skF_3'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_4353])).

tff(c_3828,plain,(
    ! [A_387,B_388] :
      ( v3_pre_topc(k1_tops_1(A_387,B_388),A_387)
      | ~ m1_subset_1(B_388,k1_zfmisc_1(u1_struct_0(A_387)))
      | ~ l1_pre_topc(A_387)
      | ~ v2_pre_topc(A_387) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_3833,plain,
    ( v3_pre_topc(k1_tops_1('#skF_1','#skF_3'),'#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_3828])).

tff(c_3837,plain,(
    v3_pre_topc(k1_tops_1('#skF_1','#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_3833])).

tff(c_3804,plain,(
    ! [A_385,B_386] :
      ( r1_tarski(k1_tops_1(A_385,B_386),B_386)
      | ~ m1_subset_1(B_386,k1_zfmisc_1(u1_struct_0(A_385)))
      | ~ l1_pre_topc(A_385) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_3809,plain,
    ( r1_tarski(k1_tops_1('#skF_1','#skF_3'),'#skF_3')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_3804])).

tff(c_3813,plain,(
    r1_tarski(k1_tops_1('#skF_1','#skF_3'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_3809])).

tff(c_3228,plain,(
    ! [A_315,B_316] :
      ( v3_pre_topc(k1_tops_1(A_315,B_316),A_315)
      | ~ m1_subset_1(B_316,k1_zfmisc_1(u1_struct_0(A_315)))
      | ~ l1_pre_topc(A_315)
      | ~ v2_pre_topc(A_315) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_3233,plain,
    ( v3_pre_topc(k1_tops_1('#skF_1','#skF_3'),'#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_3228])).

tff(c_3237,plain,(
    v3_pre_topc(k1_tops_1('#skF_1','#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_3233])).

tff(c_3147,plain,(
    ! [A_309,B_310] :
      ( r1_tarski(k1_tops_1(A_309,B_310),B_310)
      | ~ m1_subset_1(B_310,k1_zfmisc_1(u1_struct_0(A_309)))
      | ~ l1_pre_topc(A_309) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_3152,plain,
    ( r1_tarski(k1_tops_1('#skF_1','#skF_3'),'#skF_3')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_3147])).

tff(c_3156,plain,(
    r1_tarski(k1_tops_1('#skF_1','#skF_3'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_3152])).

tff(c_2573,plain,(
    ! [A_240,B_241] :
      ( v3_pre_topc(k1_tops_1(A_240,B_241),A_240)
      | ~ m1_subset_1(B_241,k1_zfmisc_1(u1_struct_0(A_240)))
      | ~ l1_pre_topc(A_240)
      | ~ v2_pre_topc(A_240) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_2578,plain,
    ( v3_pre_topc(k1_tops_1('#skF_1','#skF_3'),'#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_2573])).

tff(c_2582,plain,(
    v3_pre_topc(k1_tops_1('#skF_1','#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_2578])).

tff(c_2502,plain,(
    ! [A_234,B_235] :
      ( r1_tarski(k1_tops_1(A_234,B_235),B_235)
      | ~ m1_subset_1(B_235,k1_zfmisc_1(u1_struct_0(A_234)))
      | ~ l1_pre_topc(A_234) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_2507,plain,
    ( r1_tarski(k1_tops_1('#skF_1','#skF_3'),'#skF_3')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_2502])).

tff(c_2511,plain,(
    r1_tarski(k1_tops_1('#skF_1','#skF_3'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_2507])).

tff(c_52,plain,
    ( r2_hidden('#skF_2',k1_tops_1('#skF_1','#skF_3'))
    | v3_pre_topc('#skF_4','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_70,plain,(
    v3_pre_topc('#skF_4','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_52])).

tff(c_48,plain,
    ( r2_hidden('#skF_2',k1_tops_1('#skF_1','#skF_3'))
    | r1_tarski('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_69,plain,(
    r1_tarski('#skF_4','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_48])).

tff(c_44,plain,
    ( r2_hidden('#skF_2',k1_tops_1('#skF_1','#skF_3'))
    | r2_hidden('#skF_2','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_68,plain,(
    r2_hidden('#skF_2','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_44])).

tff(c_56,plain,
    ( r2_hidden('#skF_2',k1_tops_1('#skF_1','#skF_3'))
    | m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_84,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_56])).

tff(c_99,plain,(
    ! [A_58,B_59] :
      ( k3_subset_1(A_58,k3_subset_1(A_58,B_59)) = B_59
      | ~ m1_subset_1(B_59,k1_zfmisc_1(A_58)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_107,plain,(
    k3_subset_1(u1_struct_0('#skF_1'),k3_subset_1(u1_struct_0('#skF_1'),'#skF_4')) = '#skF_4' ),
    inference(resolution,[status(thm)],[c_84,c_99])).

tff(c_26,plain,(
    ! [A_22,B_24] :
      ( v4_pre_topc(k3_subset_1(u1_struct_0(A_22),B_24),A_22)
      | ~ v3_pre_topc(B_24,A_22)
      | ~ m1_subset_1(B_24,k1_zfmisc_1(u1_struct_0(A_22)))
      | ~ l1_pre_topc(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_10,plain,(
    ! [A_8,B_9] :
      ( m1_subset_1(k3_subset_1(A_8,B_9),k1_zfmisc_1(A_8))
      | ~ m1_subset_1(B_9,k1_zfmisc_1(A_8)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_300,plain,(
    ! [A_80,B_81] :
      ( k2_pre_topc(A_80,B_81) = B_81
      | ~ v4_pre_topc(B_81,A_80)
      | ~ m1_subset_1(B_81,k1_zfmisc_1(u1_struct_0(A_80)))
      | ~ l1_pre_topc(A_80) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_307,plain,
    ( k2_pre_topc('#skF_1','#skF_4') = '#skF_4'
    | ~ v4_pre_topc('#skF_4','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_84,c_300])).

tff(c_314,plain,
    ( k2_pre_topc('#skF_1','#skF_4') = '#skF_4'
    | ~ v4_pre_topc('#skF_4','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_307])).

tff(c_339,plain,(
    ~ v4_pre_topc('#skF_4','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_314])).

tff(c_1085,plain,(
    ! [A_144,B_145] :
      ( v4_pre_topc(k3_subset_1(u1_struct_0(A_144),B_145),A_144)
      | ~ v3_pre_topc(B_145,A_144)
      | ~ m1_subset_1(B_145,k1_zfmisc_1(u1_struct_0(A_144)))
      | ~ l1_pre_topc(A_144) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_1088,plain,
    ( v4_pre_topc('#skF_4','#skF_1')
    | ~ v3_pre_topc(k3_subset_1(u1_struct_0('#skF_1'),'#skF_4'),'#skF_1')
    | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_107,c_1085])).

tff(c_1093,plain,
    ( v4_pre_topc('#skF_4','#skF_1')
    | ~ v3_pre_topc(k3_subset_1(u1_struct_0('#skF_1'),'#skF_4'),'#skF_1')
    | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_1088])).

tff(c_1094,plain,
    ( ~ v3_pre_topc(k3_subset_1(u1_struct_0('#skF_1'),'#skF_4'),'#skF_1')
    | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(negUnitSimplification,[status(thm)],[c_339,c_1093])).

tff(c_1600,plain,(
    ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_1094])).

tff(c_1604,plain,(
    ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_10,c_1600])).

tff(c_1608,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_1604])).

tff(c_1610,plain,(
    m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_1094])).

tff(c_16,plain,(
    ! [A_12,B_14] :
      ( k2_pre_topc(A_12,B_14) = B_14
      | ~ v4_pre_topc(B_14,A_12)
      | ~ m1_subset_1(B_14,k1_zfmisc_1(u1_struct_0(A_12)))
      | ~ l1_pre_topc(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_1616,plain,
    ( k2_pre_topc('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_4')) = k3_subset_1(u1_struct_0('#skF_1'),'#skF_4')
    | ~ v4_pre_topc(k3_subset_1(u1_struct_0('#skF_1'),'#skF_4'),'#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_1610,c_16])).

tff(c_1628,plain,
    ( k2_pre_topc('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_4')) = k3_subset_1(u1_struct_0('#skF_1'),'#skF_4')
    | ~ v4_pre_topc(k3_subset_1(u1_struct_0('#skF_1'),'#skF_4'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_1616])).

tff(c_1822,plain,(
    ~ v4_pre_topc(k3_subset_1(u1_struct_0('#skF_1'),'#skF_4'),'#skF_1') ),
    inference(splitLeft,[status(thm)],[c_1628])).

tff(c_1825,plain,
    ( ~ v3_pre_topc('#skF_4','#skF_1')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_26,c_1822])).

tff(c_1829,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_84,c_70,c_1825])).

tff(c_1830,plain,(
    k2_pre_topc('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_4')) = k3_subset_1(u1_struct_0('#skF_1'),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_1628])).

tff(c_18,plain,(
    ! [A_15,B_17] :
      ( k3_subset_1(u1_struct_0(A_15),k2_pre_topc(A_15,k3_subset_1(u1_struct_0(A_15),B_17))) = k1_tops_1(A_15,B_17)
      | ~ m1_subset_1(B_17,k1_zfmisc_1(u1_struct_0(A_15)))
      | ~ l1_pre_topc(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_1874,plain,
    ( k3_subset_1(u1_struct_0('#skF_1'),k3_subset_1(u1_struct_0('#skF_1'),'#skF_4')) = k1_tops_1('#skF_1','#skF_4')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_1830,c_18])).

tff(c_1878,plain,(
    k1_tops_1('#skF_1','#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_84,c_107,c_1874])).

tff(c_30,plain,(
    ! [A_28,B_32,C_34] :
      ( r1_tarski(k1_tops_1(A_28,B_32),k1_tops_1(A_28,C_34))
      | ~ r1_tarski(B_32,C_34)
      | ~ m1_subset_1(C_34,k1_zfmisc_1(u1_struct_0(A_28)))
      | ~ m1_subset_1(B_32,k1_zfmisc_1(u1_struct_0(A_28)))
      | ~ l1_pre_topc(A_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_1915,plain,(
    ! [C_34] :
      ( r1_tarski('#skF_4',k1_tops_1('#skF_1',C_34))
      | ~ r1_tarski('#skF_4',C_34)
      | ~ m1_subset_1(C_34,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1878,c_30])).

tff(c_2179,plain,(
    ! [C_214] :
      ( r1_tarski('#skF_4',k1_tops_1('#skF_1',C_214))
      | ~ r1_tarski('#skF_4',C_214)
      | ~ m1_subset_1(C_214,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_84,c_1915])).

tff(c_2199,plain,
    ( r1_tarski('#skF_4',k1_tops_1('#skF_1','#skF_3'))
    | ~ r1_tarski('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_32,c_2179])).

tff(c_2211,plain,(
    r1_tarski('#skF_4',k1_tops_1('#skF_1','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_69,c_2199])).

tff(c_8,plain,(
    ! [A_6,B_7] :
      ( r1_tarski(k1_tarski(A_6),B_7)
      | ~ r2_hidden(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_63,plain,(
    ! [A_48,B_49] :
      ( k2_xboole_0(A_48,B_49) = B_49
      | ~ r1_tarski(A_48,B_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_85,plain,(
    ! [A_54,B_55] :
      ( k2_xboole_0(k1_tarski(A_54),B_55) = B_55
      | ~ r2_hidden(A_54,B_55) ) ),
    inference(resolution,[status(thm)],[c_8,c_63])).

tff(c_2,plain,(
    ! [A_1,C_3,B_2] :
      ( r1_tarski(A_1,C_3)
      | ~ r1_tarski(k2_xboole_0(A_1,B_2),C_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_91,plain,(
    ! [A_54,C_3,B_55] :
      ( r1_tarski(k1_tarski(A_54),C_3)
      | ~ r1_tarski(B_55,C_3)
      | ~ r2_hidden(A_54,B_55) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_85,c_2])).

tff(c_2241,plain,(
    ! [A_215] :
      ( r1_tarski(k1_tarski(A_215),k1_tops_1('#skF_1','#skF_3'))
      | ~ r2_hidden(A_215,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_2211,c_91])).

tff(c_6,plain,(
    ! [A_6,B_7] :
      ( r2_hidden(A_6,B_7)
      | ~ r1_tarski(k1_tarski(A_6),B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_2284,plain,(
    ! [A_217] :
      ( r2_hidden(A_217,k1_tops_1('#skF_1','#skF_3'))
      | ~ r2_hidden(A_217,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_2241,c_6])).

tff(c_38,plain,(
    ! [D_43] :
      ( ~ r2_hidden('#skF_2',D_43)
      | ~ r1_tarski(D_43,'#skF_3')
      | ~ v3_pre_topc(D_43,'#skF_1')
      | ~ m1_subset_1(D_43,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ r2_hidden('#skF_2',k1_tops_1('#skF_1','#skF_3')) ) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_334,plain,(
    ~ r2_hidden('#skF_2',k1_tops_1('#skF_1','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_38])).

tff(c_2291,plain,(
    ~ r2_hidden('#skF_2','#skF_4') ),
    inference(resolution,[status(thm)],[c_2284,c_334])).

tff(c_2300,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_2291])).

tff(c_2429,plain,(
    ! [D_223] :
      ( ~ r2_hidden('#skF_2',D_223)
      | ~ r1_tarski(D_223,'#skF_3')
      | ~ v3_pre_topc(D_223,'#skF_1')
      | ~ m1_subset_1(D_223,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(splitRight,[status(thm)],[c_38])).

tff(c_2440,plain,
    ( ~ r2_hidden('#skF_2','#skF_4')
    | ~ r1_tarski('#skF_4','#skF_3')
    | ~ v3_pre_topc('#skF_4','#skF_1') ),
    inference(resolution,[status(thm)],[c_84,c_2429])).

tff(c_2451,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_69,c_68,c_2440])).

tff(c_2452,plain,(
    r2_hidden('#skF_2',k1_tops_1('#skF_1','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_2792,plain,(
    ! [A_261,B_262] :
      ( m1_subset_1(k1_tops_1(A_261,B_262),k1_zfmisc_1(u1_struct_0(A_261)))
      | ~ m1_subset_1(B_262,k1_zfmisc_1(u1_struct_0(A_261)))
      | ~ l1_pre_topc(A_261) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_2453,plain,(
    ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_54,plain,(
    ! [D_43] :
      ( ~ r2_hidden('#skF_2',D_43)
      | ~ r1_tarski(D_43,'#skF_3')
      | ~ v3_pre_topc(D_43,'#skF_1')
      | ~ m1_subset_1(D_43,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_2737,plain,(
    ! [D_43] :
      ( ~ r2_hidden('#skF_2',D_43)
      | ~ r1_tarski(D_43,'#skF_3')
      | ~ v3_pre_topc(D_43,'#skF_1')
      | ~ m1_subset_1(D_43,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_2453,c_54])).

tff(c_2796,plain,(
    ! [B_262] :
      ( ~ r2_hidden('#skF_2',k1_tops_1('#skF_1',B_262))
      | ~ r1_tarski(k1_tops_1('#skF_1',B_262),'#skF_3')
      | ~ v3_pre_topc(k1_tops_1('#skF_1',B_262),'#skF_1')
      | ~ m1_subset_1(B_262,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_2792,c_2737])).

tff(c_3062,plain,(
    ! [B_293] :
      ( ~ r2_hidden('#skF_2',k1_tops_1('#skF_1',B_293))
      | ~ r1_tarski(k1_tops_1('#skF_1',B_293),'#skF_3')
      | ~ v3_pre_topc(k1_tops_1('#skF_1',B_293),'#skF_1')
      | ~ m1_subset_1(B_293,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_2796])).

tff(c_3073,plain,
    ( ~ r2_hidden('#skF_2',k1_tops_1('#skF_1','#skF_3'))
    | ~ r1_tarski(k1_tops_1('#skF_1','#skF_3'),'#skF_3')
    | ~ v3_pre_topc(k1_tops_1('#skF_1','#skF_3'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_3062])).

tff(c_3081,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2582,c_2511,c_2452,c_3073])).

tff(c_3082,plain,(
    r2_hidden('#skF_2',k1_tops_1('#skF_1','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_3359,plain,(
    ! [A_322,B_323] :
      ( m1_subset_1(k1_tops_1(A_322,B_323),k1_zfmisc_1(u1_struct_0(A_322)))
      | ~ m1_subset_1(B_323,k1_zfmisc_1(u1_struct_0(A_322)))
      | ~ l1_pre_topc(A_322) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_3083,plain,(
    ~ v3_pre_topc('#skF_4','#skF_1') ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_50,plain,(
    ! [D_43] :
      ( ~ r2_hidden('#skF_2',D_43)
      | ~ r1_tarski(D_43,'#skF_3')
      | ~ v3_pre_topc(D_43,'#skF_1')
      | ~ m1_subset_1(D_43,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | v3_pre_topc('#skF_4','#skF_1') ) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_3179,plain,(
    ! [D_43] :
      ( ~ r2_hidden('#skF_2',D_43)
      | ~ r1_tarski(D_43,'#skF_3')
      | ~ v3_pre_topc(D_43,'#skF_1')
      | ~ m1_subset_1(D_43,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_3083,c_50])).

tff(c_3365,plain,(
    ! [B_323] :
      ( ~ r2_hidden('#skF_2',k1_tops_1('#skF_1',B_323))
      | ~ r1_tarski(k1_tops_1('#skF_1',B_323),'#skF_3')
      | ~ v3_pre_topc(k1_tops_1('#skF_1',B_323),'#skF_1')
      | ~ m1_subset_1(B_323,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_3359,c_3179])).

tff(c_3745,plain,(
    ! [B_369] :
      ( ~ r2_hidden('#skF_2',k1_tops_1('#skF_1',B_369))
      | ~ r1_tarski(k1_tops_1('#skF_1',B_369),'#skF_3')
      | ~ v3_pre_topc(k1_tops_1('#skF_1',B_369),'#skF_1')
      | ~ m1_subset_1(B_369,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_3365])).

tff(c_3756,plain,
    ( ~ r2_hidden('#skF_2',k1_tops_1('#skF_1','#skF_3'))
    | ~ r1_tarski(k1_tops_1('#skF_1','#skF_3'),'#skF_3')
    | ~ v3_pre_topc(k1_tops_1('#skF_1','#skF_3'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_3745])).

tff(c_3764,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3237,c_3156,c_3082,c_3756])).

tff(c_3765,plain,(
    r2_hidden('#skF_2',k1_tops_1('#skF_1','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_3915,plain,(
    ! [A_394,B_395] :
      ( m1_subset_1(k1_tops_1(A_394,B_395),k1_zfmisc_1(u1_struct_0(A_394)))
      | ~ m1_subset_1(B_395,k1_zfmisc_1(u1_struct_0(A_394)))
      | ~ l1_pre_topc(A_394) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_3766,plain,(
    ~ r1_tarski('#skF_4','#skF_3') ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_46,plain,(
    ! [D_43] :
      ( ~ r2_hidden('#skF_2',D_43)
      | ~ r1_tarski(D_43,'#skF_3')
      | ~ v3_pre_topc(D_43,'#skF_1')
      | ~ m1_subset_1(D_43,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | r1_tarski('#skF_4','#skF_3') ) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_3851,plain,(
    ! [D_43] :
      ( ~ r2_hidden('#skF_2',D_43)
      | ~ r1_tarski(D_43,'#skF_3')
      | ~ v3_pre_topc(D_43,'#skF_1')
      | ~ m1_subset_1(D_43,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_3766,c_46])).

tff(c_3919,plain,(
    ! [B_395] :
      ( ~ r2_hidden('#skF_2',k1_tops_1('#skF_1',B_395))
      | ~ r1_tarski(k1_tops_1('#skF_1',B_395),'#skF_3')
      | ~ v3_pre_topc(k1_tops_1('#skF_1',B_395),'#skF_1')
      | ~ m1_subset_1(B_395,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_3915,c_3851])).

tff(c_4283,plain,(
    ! [B_429] :
      ( ~ r2_hidden('#skF_2',k1_tops_1('#skF_1',B_429))
      | ~ r1_tarski(k1_tops_1('#skF_1',B_429),'#skF_3')
      | ~ v3_pre_topc(k1_tops_1('#skF_1',B_429),'#skF_1')
      | ~ m1_subset_1(B_429,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_3919])).

tff(c_4297,plain,
    ( ~ r2_hidden('#skF_2',k1_tops_1('#skF_1','#skF_3'))
    | ~ r1_tarski(k1_tops_1('#skF_1','#skF_3'),'#skF_3')
    | ~ v3_pre_topc(k1_tops_1('#skF_1','#skF_3'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_4283])).

tff(c_4308,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3837,c_3813,c_3765,c_4297])).

tff(c_4309,plain,(
    r2_hidden('#skF_2',k1_tops_1('#skF_1','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_4535,plain,(
    ! [A_459,B_460] :
      ( m1_subset_1(k1_tops_1(A_459,B_460),k1_zfmisc_1(u1_struct_0(A_459)))
      | ~ m1_subset_1(B_460,k1_zfmisc_1(u1_struct_0(A_459)))
      | ~ l1_pre_topc(A_459) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_4310,plain,(
    ~ r2_hidden('#skF_2','#skF_4') ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_42,plain,(
    ! [D_43] :
      ( ~ r2_hidden('#skF_2',D_43)
      | ~ r1_tarski(D_43,'#skF_3')
      | ~ v3_pre_topc(D_43,'#skF_1')
      | ~ m1_subset_1(D_43,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | r2_hidden('#skF_2','#skF_4') ) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_4395,plain,(
    ! [D_43] :
      ( ~ r2_hidden('#skF_2',D_43)
      | ~ r1_tarski(D_43,'#skF_3')
      | ~ v3_pre_topc(D_43,'#skF_1')
      | ~ m1_subset_1(D_43,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_4310,c_42])).

tff(c_4542,plain,(
    ! [B_460] :
      ( ~ r2_hidden('#skF_2',k1_tops_1('#skF_1',B_460))
      | ~ r1_tarski(k1_tops_1('#skF_1',B_460),'#skF_3')
      | ~ v3_pre_topc(k1_tops_1('#skF_1',B_460),'#skF_1')
      | ~ m1_subset_1(B_460,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_4535,c_4395])).

tff(c_5028,plain,(
    ! [B_502] :
      ( ~ r2_hidden('#skF_2',k1_tops_1('#skF_1',B_502))
      | ~ r1_tarski(k1_tops_1('#skF_1',B_502),'#skF_3')
      | ~ v3_pre_topc(k1_tops_1('#skF_1',B_502),'#skF_1')
      | ~ m1_subset_1(B_502,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_4542])).

tff(c_5042,plain,
    ( ~ r2_hidden('#skF_2',k1_tops_1('#skF_1','#skF_3'))
    | ~ r1_tarski(k1_tops_1('#skF_1','#skF_3'),'#skF_3')
    | ~ v3_pre_topc(k1_tops_1('#skF_1','#skF_3'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_5028])).

tff(c_5053,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4381,c_4357,c_4309,c_5042])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.13/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n015.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 17:08:23 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.05/2.16  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.05/2.17  
% 6.05/2.17  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.05/2.18  %$ v4_pre_topc > v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k3_subset_1 > k2_xboole_0 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 6.05/2.18  
% 6.05/2.18  %Foreground sorts:
% 6.05/2.18  
% 6.05/2.18  
% 6.05/2.18  %Background operators:
% 6.05/2.18  
% 6.05/2.18  
% 6.05/2.18  %Foreground operators:
% 6.05/2.18  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 6.05/2.18  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.05/2.18  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 6.05/2.18  tff(k1_tarski, type, k1_tarski: $i > $i).
% 6.05/2.18  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 6.05/2.18  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.05/2.18  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 6.05/2.18  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 6.05/2.18  tff('#skF_2', type, '#skF_2': $i).
% 6.05/2.18  tff('#skF_3', type, '#skF_3': $i).
% 6.05/2.18  tff('#skF_1', type, '#skF_1': $i).
% 6.05/2.18  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 6.05/2.18  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 6.05/2.18  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.05/2.18  tff('#skF_4', type, '#skF_4': $i).
% 6.05/2.18  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.05/2.18  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 6.05/2.18  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 6.05/2.18  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 6.05/2.18  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 6.05/2.18  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 6.05/2.18  
% 6.05/2.21  tff(f_128, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B, C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (r2_hidden(B, k1_tops_1(A, C)) <=> (?[D]: (((m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) & v3_pre_topc(D, A)) & r1_tarski(D, C)) & r2_hidden(B, D)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t54_tops_1)).
% 6.05/2.21  tff(f_81, axiom, (![A, B]: (((v2_pre_topc(A) & l1_pre_topc(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => v3_pre_topc(k1_tops_1(A, B), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc9_tops_1)).
% 6.05/2.21  tff(f_97, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => r1_tarski(k1_tops_1(A, B), B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_tops_1)).
% 6.05/2.21  tff(f_45, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, k3_subset_1(A, B)) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 6.05/2.21  tff(f_90, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_pre_topc(B, A) <=> v4_pre_topc(k3_subset_1(u1_struct_0(A), B), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t30_tops_1)).
% 6.05/2.21  tff(f_41, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k3_subset_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 6.05/2.21  tff(f_60, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v4_pre_topc(B, A) => (k2_pre_topc(A, B) = B)) & ((v2_pre_topc(A) & (k2_pre_topc(A, B) = B)) => v4_pre_topc(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_pre_topc)).
% 6.05/2.21  tff(f_67, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k1_tops_1(A, B) = k3_subset_1(u1_struct_0(A), k2_pre_topc(A, k3_subset_1(u1_struct_0(A), B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tops_1)).
% 6.05/2.21  tff(f_109, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (r1_tarski(B, C) => r1_tarski(k1_tops_1(A, B), k1_tops_1(A, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_tops_1)).
% 6.05/2.21  tff(f_37, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 6.05/2.21  tff(f_33, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 6.05/2.21  tff(f_29, axiom, (![A, B, C]: (r1_tarski(k2_xboole_0(A, B), C) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_xboole_1)).
% 6.05/2.21  tff(f_73, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k1_tops_1(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_tops_1)).
% 6.05/2.21  tff(c_36, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_128])).
% 6.05/2.21  tff(c_34, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_128])).
% 6.05/2.21  tff(c_32, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_128])).
% 6.05/2.21  tff(c_4372, plain, (![A_447, B_448]: (v3_pre_topc(k1_tops_1(A_447, B_448), A_447) | ~m1_subset_1(B_448, k1_zfmisc_1(u1_struct_0(A_447))) | ~l1_pre_topc(A_447) | ~v2_pre_topc(A_447))), inference(cnfTransformation, [status(thm)], [f_81])).
% 6.05/2.21  tff(c_4377, plain, (v3_pre_topc(k1_tops_1('#skF_1', '#skF_3'), '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_32, c_4372])).
% 6.05/2.21  tff(c_4381, plain, (v3_pre_topc(k1_tops_1('#skF_1', '#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_4377])).
% 6.05/2.21  tff(c_4348, plain, (![A_445, B_446]: (r1_tarski(k1_tops_1(A_445, B_446), B_446) | ~m1_subset_1(B_446, k1_zfmisc_1(u1_struct_0(A_445))) | ~l1_pre_topc(A_445))), inference(cnfTransformation, [status(thm)], [f_97])).
% 6.05/2.21  tff(c_4353, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_3'), '#skF_3') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_32, c_4348])).
% 6.05/2.21  tff(c_4357, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_3'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_4353])).
% 6.05/2.21  tff(c_3828, plain, (![A_387, B_388]: (v3_pre_topc(k1_tops_1(A_387, B_388), A_387) | ~m1_subset_1(B_388, k1_zfmisc_1(u1_struct_0(A_387))) | ~l1_pre_topc(A_387) | ~v2_pre_topc(A_387))), inference(cnfTransformation, [status(thm)], [f_81])).
% 6.05/2.21  tff(c_3833, plain, (v3_pre_topc(k1_tops_1('#skF_1', '#skF_3'), '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_32, c_3828])).
% 6.05/2.21  tff(c_3837, plain, (v3_pre_topc(k1_tops_1('#skF_1', '#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_3833])).
% 6.05/2.21  tff(c_3804, plain, (![A_385, B_386]: (r1_tarski(k1_tops_1(A_385, B_386), B_386) | ~m1_subset_1(B_386, k1_zfmisc_1(u1_struct_0(A_385))) | ~l1_pre_topc(A_385))), inference(cnfTransformation, [status(thm)], [f_97])).
% 6.05/2.21  tff(c_3809, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_3'), '#skF_3') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_32, c_3804])).
% 6.05/2.21  tff(c_3813, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_3'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_3809])).
% 6.05/2.21  tff(c_3228, plain, (![A_315, B_316]: (v3_pre_topc(k1_tops_1(A_315, B_316), A_315) | ~m1_subset_1(B_316, k1_zfmisc_1(u1_struct_0(A_315))) | ~l1_pre_topc(A_315) | ~v2_pre_topc(A_315))), inference(cnfTransformation, [status(thm)], [f_81])).
% 6.05/2.21  tff(c_3233, plain, (v3_pre_topc(k1_tops_1('#skF_1', '#skF_3'), '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_32, c_3228])).
% 6.05/2.21  tff(c_3237, plain, (v3_pre_topc(k1_tops_1('#skF_1', '#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_3233])).
% 6.05/2.21  tff(c_3147, plain, (![A_309, B_310]: (r1_tarski(k1_tops_1(A_309, B_310), B_310) | ~m1_subset_1(B_310, k1_zfmisc_1(u1_struct_0(A_309))) | ~l1_pre_topc(A_309))), inference(cnfTransformation, [status(thm)], [f_97])).
% 6.05/2.21  tff(c_3152, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_3'), '#skF_3') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_32, c_3147])).
% 6.05/2.21  tff(c_3156, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_3'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_3152])).
% 6.05/2.21  tff(c_2573, plain, (![A_240, B_241]: (v3_pre_topc(k1_tops_1(A_240, B_241), A_240) | ~m1_subset_1(B_241, k1_zfmisc_1(u1_struct_0(A_240))) | ~l1_pre_topc(A_240) | ~v2_pre_topc(A_240))), inference(cnfTransformation, [status(thm)], [f_81])).
% 6.05/2.21  tff(c_2578, plain, (v3_pre_topc(k1_tops_1('#skF_1', '#skF_3'), '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_32, c_2573])).
% 6.05/2.21  tff(c_2582, plain, (v3_pre_topc(k1_tops_1('#skF_1', '#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_2578])).
% 6.05/2.21  tff(c_2502, plain, (![A_234, B_235]: (r1_tarski(k1_tops_1(A_234, B_235), B_235) | ~m1_subset_1(B_235, k1_zfmisc_1(u1_struct_0(A_234))) | ~l1_pre_topc(A_234))), inference(cnfTransformation, [status(thm)], [f_97])).
% 6.05/2.21  tff(c_2507, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_3'), '#skF_3') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_32, c_2502])).
% 6.05/2.21  tff(c_2511, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_3'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_2507])).
% 6.05/2.21  tff(c_52, plain, (r2_hidden('#skF_2', k1_tops_1('#skF_1', '#skF_3')) | v3_pre_topc('#skF_4', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_128])).
% 6.05/2.21  tff(c_70, plain, (v3_pre_topc('#skF_4', '#skF_1')), inference(splitLeft, [status(thm)], [c_52])).
% 6.05/2.21  tff(c_48, plain, (r2_hidden('#skF_2', k1_tops_1('#skF_1', '#skF_3')) | r1_tarski('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_128])).
% 6.05/2.21  tff(c_69, plain, (r1_tarski('#skF_4', '#skF_3')), inference(splitLeft, [status(thm)], [c_48])).
% 6.05/2.21  tff(c_44, plain, (r2_hidden('#skF_2', k1_tops_1('#skF_1', '#skF_3')) | r2_hidden('#skF_2', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_128])).
% 6.05/2.21  tff(c_68, plain, (r2_hidden('#skF_2', '#skF_4')), inference(splitLeft, [status(thm)], [c_44])).
% 6.05/2.21  tff(c_56, plain, (r2_hidden('#skF_2', k1_tops_1('#skF_1', '#skF_3')) | m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_128])).
% 6.05/2.21  tff(c_84, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitLeft, [status(thm)], [c_56])).
% 6.05/2.21  tff(c_99, plain, (![A_58, B_59]: (k3_subset_1(A_58, k3_subset_1(A_58, B_59))=B_59 | ~m1_subset_1(B_59, k1_zfmisc_1(A_58)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 6.05/2.21  tff(c_107, plain, (k3_subset_1(u1_struct_0('#skF_1'), k3_subset_1(u1_struct_0('#skF_1'), '#skF_4'))='#skF_4'), inference(resolution, [status(thm)], [c_84, c_99])).
% 6.05/2.21  tff(c_26, plain, (![A_22, B_24]: (v4_pre_topc(k3_subset_1(u1_struct_0(A_22), B_24), A_22) | ~v3_pre_topc(B_24, A_22) | ~m1_subset_1(B_24, k1_zfmisc_1(u1_struct_0(A_22))) | ~l1_pre_topc(A_22))), inference(cnfTransformation, [status(thm)], [f_90])).
% 6.05/2.21  tff(c_10, plain, (![A_8, B_9]: (m1_subset_1(k3_subset_1(A_8, B_9), k1_zfmisc_1(A_8)) | ~m1_subset_1(B_9, k1_zfmisc_1(A_8)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 6.05/2.21  tff(c_300, plain, (![A_80, B_81]: (k2_pre_topc(A_80, B_81)=B_81 | ~v4_pre_topc(B_81, A_80) | ~m1_subset_1(B_81, k1_zfmisc_1(u1_struct_0(A_80))) | ~l1_pre_topc(A_80))), inference(cnfTransformation, [status(thm)], [f_60])).
% 6.05/2.21  tff(c_307, plain, (k2_pre_topc('#skF_1', '#skF_4')='#skF_4' | ~v4_pre_topc('#skF_4', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_84, c_300])).
% 6.05/2.21  tff(c_314, plain, (k2_pre_topc('#skF_1', '#skF_4')='#skF_4' | ~v4_pre_topc('#skF_4', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_307])).
% 6.05/2.21  tff(c_339, plain, (~v4_pre_topc('#skF_4', '#skF_1')), inference(splitLeft, [status(thm)], [c_314])).
% 6.05/2.21  tff(c_1085, plain, (![A_144, B_145]: (v4_pre_topc(k3_subset_1(u1_struct_0(A_144), B_145), A_144) | ~v3_pre_topc(B_145, A_144) | ~m1_subset_1(B_145, k1_zfmisc_1(u1_struct_0(A_144))) | ~l1_pre_topc(A_144))), inference(cnfTransformation, [status(thm)], [f_90])).
% 6.05/2.21  tff(c_1088, plain, (v4_pre_topc('#skF_4', '#skF_1') | ~v3_pre_topc(k3_subset_1(u1_struct_0('#skF_1'), '#skF_4'), '#skF_1') | ~m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_107, c_1085])).
% 6.05/2.21  tff(c_1093, plain, (v4_pre_topc('#skF_4', '#skF_1') | ~v3_pre_topc(k3_subset_1(u1_struct_0('#skF_1'), '#skF_4'), '#skF_1') | ~m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_1088])).
% 6.05/2.21  tff(c_1094, plain, (~v3_pre_topc(k3_subset_1(u1_struct_0('#skF_1'), '#skF_4'), '#skF_1') | ~m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(negUnitSimplification, [status(thm)], [c_339, c_1093])).
% 6.05/2.21  tff(c_1600, plain, (~m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitLeft, [status(thm)], [c_1094])).
% 6.05/2.21  tff(c_1604, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_10, c_1600])).
% 6.05/2.21  tff(c_1608, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_84, c_1604])).
% 6.05/2.21  tff(c_1610, plain, (m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitRight, [status(thm)], [c_1094])).
% 6.05/2.21  tff(c_16, plain, (![A_12, B_14]: (k2_pre_topc(A_12, B_14)=B_14 | ~v4_pre_topc(B_14, A_12) | ~m1_subset_1(B_14, k1_zfmisc_1(u1_struct_0(A_12))) | ~l1_pre_topc(A_12))), inference(cnfTransformation, [status(thm)], [f_60])).
% 6.05/2.21  tff(c_1616, plain, (k2_pre_topc('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_4'))=k3_subset_1(u1_struct_0('#skF_1'), '#skF_4') | ~v4_pre_topc(k3_subset_1(u1_struct_0('#skF_1'), '#skF_4'), '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_1610, c_16])).
% 6.05/2.21  tff(c_1628, plain, (k2_pre_topc('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_4'))=k3_subset_1(u1_struct_0('#skF_1'), '#skF_4') | ~v4_pre_topc(k3_subset_1(u1_struct_0('#skF_1'), '#skF_4'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_1616])).
% 6.05/2.21  tff(c_1822, plain, (~v4_pre_topc(k3_subset_1(u1_struct_0('#skF_1'), '#skF_4'), '#skF_1')), inference(splitLeft, [status(thm)], [c_1628])).
% 6.05/2.21  tff(c_1825, plain, (~v3_pre_topc('#skF_4', '#skF_1') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_26, c_1822])).
% 6.05/2.21  tff(c_1829, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_34, c_84, c_70, c_1825])).
% 6.05/2.21  tff(c_1830, plain, (k2_pre_topc('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_4'))=k3_subset_1(u1_struct_0('#skF_1'), '#skF_4')), inference(splitRight, [status(thm)], [c_1628])).
% 6.05/2.21  tff(c_18, plain, (![A_15, B_17]: (k3_subset_1(u1_struct_0(A_15), k2_pre_topc(A_15, k3_subset_1(u1_struct_0(A_15), B_17)))=k1_tops_1(A_15, B_17) | ~m1_subset_1(B_17, k1_zfmisc_1(u1_struct_0(A_15))) | ~l1_pre_topc(A_15))), inference(cnfTransformation, [status(thm)], [f_67])).
% 6.05/2.21  tff(c_1874, plain, (k3_subset_1(u1_struct_0('#skF_1'), k3_subset_1(u1_struct_0('#skF_1'), '#skF_4'))=k1_tops_1('#skF_1', '#skF_4') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_1830, c_18])).
% 6.05/2.21  tff(c_1878, plain, (k1_tops_1('#skF_1', '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_34, c_84, c_107, c_1874])).
% 6.05/2.21  tff(c_30, plain, (![A_28, B_32, C_34]: (r1_tarski(k1_tops_1(A_28, B_32), k1_tops_1(A_28, C_34)) | ~r1_tarski(B_32, C_34) | ~m1_subset_1(C_34, k1_zfmisc_1(u1_struct_0(A_28))) | ~m1_subset_1(B_32, k1_zfmisc_1(u1_struct_0(A_28))) | ~l1_pre_topc(A_28))), inference(cnfTransformation, [status(thm)], [f_109])).
% 6.05/2.21  tff(c_1915, plain, (![C_34]: (r1_tarski('#skF_4', k1_tops_1('#skF_1', C_34)) | ~r1_tarski('#skF_4', C_34) | ~m1_subset_1(C_34, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_1878, c_30])).
% 6.05/2.21  tff(c_2179, plain, (![C_214]: (r1_tarski('#skF_4', k1_tops_1('#skF_1', C_214)) | ~r1_tarski('#skF_4', C_214) | ~m1_subset_1(C_214, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_84, c_1915])).
% 6.05/2.21  tff(c_2199, plain, (r1_tarski('#skF_4', k1_tops_1('#skF_1', '#skF_3')) | ~r1_tarski('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_32, c_2179])).
% 6.05/2.21  tff(c_2211, plain, (r1_tarski('#skF_4', k1_tops_1('#skF_1', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_69, c_2199])).
% 6.05/2.21  tff(c_8, plain, (![A_6, B_7]: (r1_tarski(k1_tarski(A_6), B_7) | ~r2_hidden(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_37])).
% 6.05/2.21  tff(c_63, plain, (![A_48, B_49]: (k2_xboole_0(A_48, B_49)=B_49 | ~r1_tarski(A_48, B_49))), inference(cnfTransformation, [status(thm)], [f_33])).
% 6.05/2.21  tff(c_85, plain, (![A_54, B_55]: (k2_xboole_0(k1_tarski(A_54), B_55)=B_55 | ~r2_hidden(A_54, B_55))), inference(resolution, [status(thm)], [c_8, c_63])).
% 6.05/2.21  tff(c_2, plain, (![A_1, C_3, B_2]: (r1_tarski(A_1, C_3) | ~r1_tarski(k2_xboole_0(A_1, B_2), C_3))), inference(cnfTransformation, [status(thm)], [f_29])).
% 6.05/2.21  tff(c_91, plain, (![A_54, C_3, B_55]: (r1_tarski(k1_tarski(A_54), C_3) | ~r1_tarski(B_55, C_3) | ~r2_hidden(A_54, B_55))), inference(superposition, [status(thm), theory('equality')], [c_85, c_2])).
% 6.05/2.21  tff(c_2241, plain, (![A_215]: (r1_tarski(k1_tarski(A_215), k1_tops_1('#skF_1', '#skF_3')) | ~r2_hidden(A_215, '#skF_4'))), inference(resolution, [status(thm)], [c_2211, c_91])).
% 6.05/2.21  tff(c_6, plain, (![A_6, B_7]: (r2_hidden(A_6, B_7) | ~r1_tarski(k1_tarski(A_6), B_7))), inference(cnfTransformation, [status(thm)], [f_37])).
% 6.05/2.21  tff(c_2284, plain, (![A_217]: (r2_hidden(A_217, k1_tops_1('#skF_1', '#skF_3')) | ~r2_hidden(A_217, '#skF_4'))), inference(resolution, [status(thm)], [c_2241, c_6])).
% 6.05/2.21  tff(c_38, plain, (![D_43]: (~r2_hidden('#skF_2', D_43) | ~r1_tarski(D_43, '#skF_3') | ~v3_pre_topc(D_43, '#skF_1') | ~m1_subset_1(D_43, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~r2_hidden('#skF_2', k1_tops_1('#skF_1', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_128])).
% 6.05/2.21  tff(c_334, plain, (~r2_hidden('#skF_2', k1_tops_1('#skF_1', '#skF_3'))), inference(splitLeft, [status(thm)], [c_38])).
% 6.05/2.21  tff(c_2291, plain, (~r2_hidden('#skF_2', '#skF_4')), inference(resolution, [status(thm)], [c_2284, c_334])).
% 6.05/2.21  tff(c_2300, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_68, c_2291])).
% 6.05/2.21  tff(c_2429, plain, (![D_223]: (~r2_hidden('#skF_2', D_223) | ~r1_tarski(D_223, '#skF_3') | ~v3_pre_topc(D_223, '#skF_1') | ~m1_subset_1(D_223, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(splitRight, [status(thm)], [c_38])).
% 6.05/2.21  tff(c_2440, plain, (~r2_hidden('#skF_2', '#skF_4') | ~r1_tarski('#skF_4', '#skF_3') | ~v3_pre_topc('#skF_4', '#skF_1')), inference(resolution, [status(thm)], [c_84, c_2429])).
% 6.05/2.21  tff(c_2451, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_70, c_69, c_68, c_2440])).
% 6.05/2.21  tff(c_2452, plain, (r2_hidden('#skF_2', k1_tops_1('#skF_1', '#skF_3'))), inference(splitRight, [status(thm)], [c_56])).
% 6.05/2.21  tff(c_2792, plain, (![A_261, B_262]: (m1_subset_1(k1_tops_1(A_261, B_262), k1_zfmisc_1(u1_struct_0(A_261))) | ~m1_subset_1(B_262, k1_zfmisc_1(u1_struct_0(A_261))) | ~l1_pre_topc(A_261))), inference(cnfTransformation, [status(thm)], [f_73])).
% 6.05/2.21  tff(c_2453, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitRight, [status(thm)], [c_56])).
% 6.05/2.21  tff(c_54, plain, (![D_43]: (~r2_hidden('#skF_2', D_43) | ~r1_tarski(D_43, '#skF_3') | ~v3_pre_topc(D_43, '#skF_1') | ~m1_subset_1(D_43, k1_zfmisc_1(u1_struct_0('#skF_1'))) | m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(cnfTransformation, [status(thm)], [f_128])).
% 6.05/2.21  tff(c_2737, plain, (![D_43]: (~r2_hidden('#skF_2', D_43) | ~r1_tarski(D_43, '#skF_3') | ~v3_pre_topc(D_43, '#skF_1') | ~m1_subset_1(D_43, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(negUnitSimplification, [status(thm)], [c_2453, c_54])).
% 6.05/2.21  tff(c_2796, plain, (![B_262]: (~r2_hidden('#skF_2', k1_tops_1('#skF_1', B_262)) | ~r1_tarski(k1_tops_1('#skF_1', B_262), '#skF_3') | ~v3_pre_topc(k1_tops_1('#skF_1', B_262), '#skF_1') | ~m1_subset_1(B_262, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_2792, c_2737])).
% 6.05/2.21  tff(c_3062, plain, (![B_293]: (~r2_hidden('#skF_2', k1_tops_1('#skF_1', B_293)) | ~r1_tarski(k1_tops_1('#skF_1', B_293), '#skF_3') | ~v3_pre_topc(k1_tops_1('#skF_1', B_293), '#skF_1') | ~m1_subset_1(B_293, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_2796])).
% 6.05/2.21  tff(c_3073, plain, (~r2_hidden('#skF_2', k1_tops_1('#skF_1', '#skF_3')) | ~r1_tarski(k1_tops_1('#skF_1', '#skF_3'), '#skF_3') | ~v3_pre_topc(k1_tops_1('#skF_1', '#skF_3'), '#skF_1')), inference(resolution, [status(thm)], [c_32, c_3062])).
% 6.05/2.21  tff(c_3081, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2582, c_2511, c_2452, c_3073])).
% 6.05/2.21  tff(c_3082, plain, (r2_hidden('#skF_2', k1_tops_1('#skF_1', '#skF_3'))), inference(splitRight, [status(thm)], [c_52])).
% 6.05/2.21  tff(c_3359, plain, (![A_322, B_323]: (m1_subset_1(k1_tops_1(A_322, B_323), k1_zfmisc_1(u1_struct_0(A_322))) | ~m1_subset_1(B_323, k1_zfmisc_1(u1_struct_0(A_322))) | ~l1_pre_topc(A_322))), inference(cnfTransformation, [status(thm)], [f_73])).
% 6.05/2.21  tff(c_3083, plain, (~v3_pre_topc('#skF_4', '#skF_1')), inference(splitRight, [status(thm)], [c_52])).
% 6.05/2.21  tff(c_50, plain, (![D_43]: (~r2_hidden('#skF_2', D_43) | ~r1_tarski(D_43, '#skF_3') | ~v3_pre_topc(D_43, '#skF_1') | ~m1_subset_1(D_43, k1_zfmisc_1(u1_struct_0('#skF_1'))) | v3_pre_topc('#skF_4', '#skF_1'))), inference(cnfTransformation, [status(thm)], [f_128])).
% 6.05/2.21  tff(c_3179, plain, (![D_43]: (~r2_hidden('#skF_2', D_43) | ~r1_tarski(D_43, '#skF_3') | ~v3_pre_topc(D_43, '#skF_1') | ~m1_subset_1(D_43, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(negUnitSimplification, [status(thm)], [c_3083, c_50])).
% 6.05/2.21  tff(c_3365, plain, (![B_323]: (~r2_hidden('#skF_2', k1_tops_1('#skF_1', B_323)) | ~r1_tarski(k1_tops_1('#skF_1', B_323), '#skF_3') | ~v3_pre_topc(k1_tops_1('#skF_1', B_323), '#skF_1') | ~m1_subset_1(B_323, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_3359, c_3179])).
% 6.05/2.21  tff(c_3745, plain, (![B_369]: (~r2_hidden('#skF_2', k1_tops_1('#skF_1', B_369)) | ~r1_tarski(k1_tops_1('#skF_1', B_369), '#skF_3') | ~v3_pre_topc(k1_tops_1('#skF_1', B_369), '#skF_1') | ~m1_subset_1(B_369, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_3365])).
% 6.05/2.21  tff(c_3756, plain, (~r2_hidden('#skF_2', k1_tops_1('#skF_1', '#skF_3')) | ~r1_tarski(k1_tops_1('#skF_1', '#skF_3'), '#skF_3') | ~v3_pre_topc(k1_tops_1('#skF_1', '#skF_3'), '#skF_1')), inference(resolution, [status(thm)], [c_32, c_3745])).
% 6.05/2.21  tff(c_3764, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3237, c_3156, c_3082, c_3756])).
% 6.05/2.21  tff(c_3765, plain, (r2_hidden('#skF_2', k1_tops_1('#skF_1', '#skF_3'))), inference(splitRight, [status(thm)], [c_48])).
% 6.05/2.21  tff(c_3915, plain, (![A_394, B_395]: (m1_subset_1(k1_tops_1(A_394, B_395), k1_zfmisc_1(u1_struct_0(A_394))) | ~m1_subset_1(B_395, k1_zfmisc_1(u1_struct_0(A_394))) | ~l1_pre_topc(A_394))), inference(cnfTransformation, [status(thm)], [f_73])).
% 6.05/2.21  tff(c_3766, plain, (~r1_tarski('#skF_4', '#skF_3')), inference(splitRight, [status(thm)], [c_48])).
% 6.05/2.21  tff(c_46, plain, (![D_43]: (~r2_hidden('#skF_2', D_43) | ~r1_tarski(D_43, '#skF_3') | ~v3_pre_topc(D_43, '#skF_1') | ~m1_subset_1(D_43, k1_zfmisc_1(u1_struct_0('#skF_1'))) | r1_tarski('#skF_4', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_128])).
% 6.05/2.21  tff(c_3851, plain, (![D_43]: (~r2_hidden('#skF_2', D_43) | ~r1_tarski(D_43, '#skF_3') | ~v3_pre_topc(D_43, '#skF_1') | ~m1_subset_1(D_43, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(negUnitSimplification, [status(thm)], [c_3766, c_46])).
% 6.05/2.21  tff(c_3919, plain, (![B_395]: (~r2_hidden('#skF_2', k1_tops_1('#skF_1', B_395)) | ~r1_tarski(k1_tops_1('#skF_1', B_395), '#skF_3') | ~v3_pre_topc(k1_tops_1('#skF_1', B_395), '#skF_1') | ~m1_subset_1(B_395, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_3915, c_3851])).
% 6.05/2.21  tff(c_4283, plain, (![B_429]: (~r2_hidden('#skF_2', k1_tops_1('#skF_1', B_429)) | ~r1_tarski(k1_tops_1('#skF_1', B_429), '#skF_3') | ~v3_pre_topc(k1_tops_1('#skF_1', B_429), '#skF_1') | ~m1_subset_1(B_429, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_3919])).
% 6.05/2.21  tff(c_4297, plain, (~r2_hidden('#skF_2', k1_tops_1('#skF_1', '#skF_3')) | ~r1_tarski(k1_tops_1('#skF_1', '#skF_3'), '#skF_3') | ~v3_pre_topc(k1_tops_1('#skF_1', '#skF_3'), '#skF_1')), inference(resolution, [status(thm)], [c_32, c_4283])).
% 6.05/2.21  tff(c_4308, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3837, c_3813, c_3765, c_4297])).
% 6.05/2.21  tff(c_4309, plain, (r2_hidden('#skF_2', k1_tops_1('#skF_1', '#skF_3'))), inference(splitRight, [status(thm)], [c_44])).
% 6.05/2.21  tff(c_4535, plain, (![A_459, B_460]: (m1_subset_1(k1_tops_1(A_459, B_460), k1_zfmisc_1(u1_struct_0(A_459))) | ~m1_subset_1(B_460, k1_zfmisc_1(u1_struct_0(A_459))) | ~l1_pre_topc(A_459))), inference(cnfTransformation, [status(thm)], [f_73])).
% 6.05/2.21  tff(c_4310, plain, (~r2_hidden('#skF_2', '#skF_4')), inference(splitRight, [status(thm)], [c_44])).
% 6.05/2.21  tff(c_42, plain, (![D_43]: (~r2_hidden('#skF_2', D_43) | ~r1_tarski(D_43, '#skF_3') | ~v3_pre_topc(D_43, '#skF_1') | ~m1_subset_1(D_43, k1_zfmisc_1(u1_struct_0('#skF_1'))) | r2_hidden('#skF_2', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_128])).
% 6.05/2.21  tff(c_4395, plain, (![D_43]: (~r2_hidden('#skF_2', D_43) | ~r1_tarski(D_43, '#skF_3') | ~v3_pre_topc(D_43, '#skF_1') | ~m1_subset_1(D_43, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(negUnitSimplification, [status(thm)], [c_4310, c_42])).
% 6.05/2.21  tff(c_4542, plain, (![B_460]: (~r2_hidden('#skF_2', k1_tops_1('#skF_1', B_460)) | ~r1_tarski(k1_tops_1('#skF_1', B_460), '#skF_3') | ~v3_pre_topc(k1_tops_1('#skF_1', B_460), '#skF_1') | ~m1_subset_1(B_460, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_4535, c_4395])).
% 6.05/2.21  tff(c_5028, plain, (![B_502]: (~r2_hidden('#skF_2', k1_tops_1('#skF_1', B_502)) | ~r1_tarski(k1_tops_1('#skF_1', B_502), '#skF_3') | ~v3_pre_topc(k1_tops_1('#skF_1', B_502), '#skF_1') | ~m1_subset_1(B_502, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_4542])).
% 6.05/2.21  tff(c_5042, plain, (~r2_hidden('#skF_2', k1_tops_1('#skF_1', '#skF_3')) | ~r1_tarski(k1_tops_1('#skF_1', '#skF_3'), '#skF_3') | ~v3_pre_topc(k1_tops_1('#skF_1', '#skF_3'), '#skF_1')), inference(resolution, [status(thm)], [c_32, c_5028])).
% 6.05/2.21  tff(c_5053, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4381, c_4357, c_4309, c_5042])).
% 6.05/2.21  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.05/2.21  
% 6.05/2.21  Inference rules
% 6.05/2.21  ----------------------
% 6.05/2.21  #Ref     : 0
% 6.05/2.21  #Sup     : 1167
% 6.05/2.21  #Fact    : 0
% 6.05/2.21  #Define  : 0
% 6.05/2.21  #Split   : 56
% 6.05/2.21  #Chain   : 0
% 6.05/2.21  #Close   : 0
% 6.05/2.21  
% 6.05/2.21  Ordering : KBO
% 6.05/2.21  
% 6.05/2.21  Simplification rules
% 6.05/2.21  ----------------------
% 6.05/2.21  #Subsume      : 212
% 6.05/2.21  #Demod        : 520
% 6.05/2.21  #Tautology    : 427
% 6.05/2.21  #SimpNegUnit  : 26
% 6.05/2.21  #BackRed      : 26
% 6.05/2.21  
% 6.05/2.21  #Partial instantiations: 0
% 6.05/2.21  #Strategies tried      : 1
% 6.05/2.21  
% 6.05/2.21  Timing (in seconds)
% 6.05/2.21  ----------------------
% 6.05/2.21  Preprocessing        : 0.32
% 6.05/2.21  Parsing              : 0.17
% 6.05/2.21  CNF conversion       : 0.02
% 6.05/2.21  Main loop            : 1.11
% 6.05/2.21  Inferencing          : 0.40
% 6.05/2.21  Reduction            : 0.33
% 6.05/2.21  Demodulation         : 0.22
% 6.05/2.21  BG Simplification    : 0.04
% 6.05/2.21  Subsumption          : 0.25
% 6.05/2.21  Abstraction          : 0.05
% 6.05/2.21  MUC search           : 0.00
% 6.05/2.21  Cooper               : 0.00
% 6.05/2.21  Total                : 1.48
% 6.05/2.21  Index Insertion      : 0.00
% 6.05/2.21  Index Deletion       : 0.00
% 6.05/2.21  Index Matching       : 0.00
% 6.05/2.21  BG Taut test         : 0.00
%------------------------------------------------------------------------------
