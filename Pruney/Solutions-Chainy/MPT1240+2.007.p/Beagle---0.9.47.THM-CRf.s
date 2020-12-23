%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:20:46 EST 2020

% Result     : Theorem 14.71s
% Output     : CNFRefutation 14.71s
% Verified   : 
% Statistics : Number of formulae       :  149 ( 329 expanded)
%              Number of leaves         :   35 ( 123 expanded)
%              Depth                    :   12
%              Number of atoms          :  302 ( 979 expanded)
%              Number of equality atoms :   27 (  42 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    5 (   1 average)

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

tff(f_149,negated_conjecture,(
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

tff(f_66,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_102,axiom,(
    ! [A,B] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => v3_pre_topc(k1_tops_1(A,B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_tops_1)).

tff(f_118,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => r1_tarski(k1_tops_1(A,B),B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_tops_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_xboole_0(A,B),C)
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_xboole_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k3_subset_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_111,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v3_pre_topc(B,A)
          <=> v4_pre_topc(k3_subset_1(u1_struct_0(A),B),A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_tops_1)).

tff(f_81,axiom,(
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

tff(f_88,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k1_tops_1(A,B) = k3_subset_1(u1_struct_0(A),k2_pre_topc(A,k3_subset_1(u1_struct_0(A),B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tops_1)).

tff(f_62,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(A))
         => ( r1_tarski(B,k3_subset_1(A,C))
           => r1_tarski(C,k3_subset_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_subset_1)).

tff(f_130,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( r1_tarski(B,C)
               => r1_tarski(k1_tops_1(A,B),k1_tops_1(A,C)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_tops_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(c_44,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_72,plain,(
    ! [A_56,B_57] :
      ( r1_tarski(A_56,B_57)
      | ~ m1_subset_1(A_56,k1_zfmisc_1(B_57)) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_80,plain,(
    r1_tarski('#skF_3',u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_44,c_72])).

tff(c_48,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_46,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_37643,plain,(
    ! [A_1067,B_1068] :
      ( v3_pre_topc(k1_tops_1(A_1067,B_1068),A_1067)
      | ~ m1_subset_1(B_1068,k1_zfmisc_1(u1_struct_0(A_1067)))
      | ~ l1_pre_topc(A_1067)
      | ~ v2_pre_topc(A_1067) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_37651,plain,
    ( v3_pre_topc(k1_tops_1('#skF_1','#skF_3'),'#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_44,c_37643])).

tff(c_37656,plain,(
    v3_pre_topc(k1_tops_1('#skF_1','#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_37651])).

tff(c_37503,plain,(
    ! [A_1061,B_1062] :
      ( r1_tarski(k1_tops_1(A_1061,B_1062),B_1062)
      | ~ m1_subset_1(B_1062,k1_zfmisc_1(u1_struct_0(A_1061)))
      | ~ l1_pre_topc(A_1061) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_37511,plain,
    ( r1_tarski(k1_tops_1('#skF_1','#skF_3'),'#skF_3')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_44,c_37503])).

tff(c_37516,plain,(
    r1_tarski(k1_tops_1('#skF_1','#skF_3'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_37511])).

tff(c_36738,plain,(
    ! [A_1000,B_1001] :
      ( v3_pre_topc(k1_tops_1(A_1000,B_1001),A_1000)
      | ~ m1_subset_1(B_1001,k1_zfmisc_1(u1_struct_0(A_1000)))
      | ~ l1_pre_topc(A_1000)
      | ~ v2_pre_topc(A_1000) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_36748,plain,
    ( v3_pre_topc(k1_tops_1('#skF_1','#skF_3'),'#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_44,c_36738])).

tff(c_36754,plain,(
    v3_pre_topc(k1_tops_1('#skF_1','#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_36748])).

tff(c_36212,plain,(
    ! [A_982,B_983] :
      ( r1_tarski(k1_tops_1(A_982,B_983),B_983)
      | ~ m1_subset_1(B_983,k1_zfmisc_1(u1_struct_0(A_982)))
      | ~ l1_pre_topc(A_982) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_36220,plain,
    ( r1_tarski(k1_tops_1('#skF_1','#skF_3'),'#skF_3')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_44,c_36212])).

tff(c_36225,plain,(
    r1_tarski(k1_tops_1('#skF_1','#skF_3'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_36220])).

tff(c_35249,plain,(
    ! [A_909,B_910] :
      ( v3_pre_topc(k1_tops_1(A_909,B_910),A_909)
      | ~ m1_subset_1(B_910,k1_zfmisc_1(u1_struct_0(A_909)))
      | ~ l1_pre_topc(A_909)
      | ~ v2_pre_topc(A_909) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_35257,plain,
    ( v3_pre_topc(k1_tops_1('#skF_1','#skF_3'),'#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_44,c_35249])).

tff(c_35262,plain,(
    v3_pre_topc(k1_tops_1('#skF_1','#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_35257])).

tff(c_35093,plain,(
    ! [A_902,B_903] :
      ( r1_tarski(k1_tops_1(A_902,B_903),B_903)
      | ~ m1_subset_1(B_903,k1_zfmisc_1(u1_struct_0(A_902)))
      | ~ l1_pre_topc(A_902) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_35101,plain,
    ( r1_tarski(k1_tops_1('#skF_1','#skF_3'),'#skF_3')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_44,c_35093])).

tff(c_35106,plain,(
    r1_tarski(k1_tops_1('#skF_1','#skF_3'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_35101])).

tff(c_60,plain,
    ( r2_hidden('#skF_2',k1_tops_1('#skF_1','#skF_3'))
    | r1_tarski('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_134,plain,(
    r1_tarski('#skF_4','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_60])).

tff(c_10,plain,(
    ! [A_6,B_7] :
      ( k2_xboole_0(A_6,B_7) = B_7
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_142,plain,(
    k2_xboole_0('#skF_4','#skF_3') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_134,c_10])).

tff(c_148,plain,(
    ! [A_68,C_69,B_70] :
      ( r1_tarski(A_68,C_69)
      | ~ r1_tarski(k2_xboole_0(A_68,B_70),C_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_199,plain,(
    ! [C_75] :
      ( r1_tarski('#skF_4',C_75)
      | ~ r1_tarski('#skF_3',C_75) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_142,c_148])).

tff(c_212,plain,(
    r1_tarski('#skF_4',u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_80,c_199])).

tff(c_24,plain,(
    ! [A_19,B_20] :
      ( m1_subset_1(A_19,k1_zfmisc_1(B_20))
      | ~ r1_tarski(A_19,B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_64,plain,
    ( r2_hidden('#skF_2',k1_tops_1('#skF_1','#skF_3'))
    | v3_pre_topc('#skF_4','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_135,plain,(
    v3_pre_topc('#skF_4','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_64])).

tff(c_56,plain,
    ( r2_hidden('#skF_2',k1_tops_1('#skF_1','#skF_3'))
    | r2_hidden('#skF_2','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_99,plain,(
    r2_hidden('#skF_2','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_56])).

tff(c_68,plain,
    ( r2_hidden('#skF_2',k1_tops_1('#skF_1','#skF_3'))
    | m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_215,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_68])).

tff(c_18,plain,(
    ! [A_13,B_14] :
      ( m1_subset_1(k3_subset_1(A_13,B_14),k1_zfmisc_1(A_13))
      | ~ m1_subset_1(B_14,k1_zfmisc_1(A_13)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_699,plain,(
    ! [A_101,B_102] :
      ( r1_tarski(k1_tops_1(A_101,B_102),B_102)
      | ~ m1_subset_1(B_102,k1_zfmisc_1(u1_struct_0(A_101)))
      | ~ l1_pre_topc(A_101) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_704,plain,
    ( r1_tarski(k1_tops_1('#skF_1','#skF_4'),'#skF_4')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_215,c_699])).

tff(c_713,plain,(
    r1_tarski(k1_tops_1('#skF_1','#skF_4'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_704])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_740,plain,
    ( k1_tops_1('#skF_1','#skF_4') = '#skF_4'
    | ~ r1_tarski('#skF_4',k1_tops_1('#skF_1','#skF_4')) ),
    inference(resolution,[status(thm)],[c_713,c_2])).

tff(c_2273,plain,(
    ~ r1_tarski('#skF_4',k1_tops_1('#skF_1','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_740])).

tff(c_38,plain,(
    ! [A_31,B_33] :
      ( v4_pre_topc(k3_subset_1(u1_struct_0(A_31),B_33),A_31)
      | ~ v3_pre_topc(B_33,A_31)
      | ~ m1_subset_1(B_33,k1_zfmisc_1(u1_struct_0(A_31)))
      | ~ l1_pre_topc(A_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_1056,plain,(
    ! [A_115,B_116] :
      ( k2_pre_topc(A_115,B_116) = B_116
      | ~ v4_pre_topc(B_116,A_115)
      | ~ m1_subset_1(B_116,k1_zfmisc_1(u1_struct_0(A_115)))
      | ~ l1_pre_topc(A_115) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_8991,plain,(
    ! [A_340,B_341] :
      ( k2_pre_topc(A_340,k3_subset_1(u1_struct_0(A_340),B_341)) = k3_subset_1(u1_struct_0(A_340),B_341)
      | ~ v4_pre_topc(k3_subset_1(u1_struct_0(A_340),B_341),A_340)
      | ~ l1_pre_topc(A_340)
      | ~ m1_subset_1(B_341,k1_zfmisc_1(u1_struct_0(A_340))) ) ),
    inference(resolution,[status(thm)],[c_18,c_1056])).

tff(c_26114,plain,(
    ! [A_634,B_635] :
      ( k2_pre_topc(A_634,k3_subset_1(u1_struct_0(A_634),B_635)) = k3_subset_1(u1_struct_0(A_634),B_635)
      | ~ v3_pre_topc(B_635,A_634)
      | ~ m1_subset_1(B_635,k1_zfmisc_1(u1_struct_0(A_634)))
      | ~ l1_pre_topc(A_634) ) ),
    inference(resolution,[status(thm)],[c_38,c_8991])).

tff(c_26121,plain,
    ( k2_pre_topc('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_4')) = k3_subset_1(u1_struct_0('#skF_1'),'#skF_4')
    | ~ v3_pre_topc('#skF_4','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_215,c_26114])).

tff(c_26131,plain,(
    k2_pre_topc('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_4')) = k3_subset_1(u1_struct_0('#skF_1'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_135,c_26121])).

tff(c_30,plain,(
    ! [A_24,B_26] :
      ( k3_subset_1(u1_struct_0(A_24),k2_pre_topc(A_24,k3_subset_1(u1_struct_0(A_24),B_26))) = k1_tops_1(A_24,B_26)
      | ~ m1_subset_1(B_26,k1_zfmisc_1(u1_struct_0(A_24)))
      | ~ l1_pre_topc(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_26151,plain,
    ( k3_subset_1(u1_struct_0('#skF_1'),k3_subset_1(u1_struct_0('#skF_1'),'#skF_4')) = k1_tops_1('#skF_1','#skF_4')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_26131,c_30])).

tff(c_26163,plain,(
    k3_subset_1(u1_struct_0('#skF_1'),k3_subset_1(u1_struct_0('#skF_1'),'#skF_4')) = k1_tops_1('#skF_1','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_215,c_26151])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_2248,plain,(
    ! [C_167,A_168,B_169] :
      ( r1_tarski(C_167,k3_subset_1(A_168,B_169))
      | ~ r1_tarski(B_169,k3_subset_1(A_168,C_167))
      | ~ m1_subset_1(C_167,k1_zfmisc_1(A_168))
      | ~ m1_subset_1(B_169,k1_zfmisc_1(A_168)) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_2272,plain,(
    ! [C_167,A_168] :
      ( r1_tarski(C_167,k3_subset_1(A_168,k3_subset_1(A_168,C_167)))
      | ~ m1_subset_1(C_167,k1_zfmisc_1(A_168))
      | ~ m1_subset_1(k3_subset_1(A_168,C_167),k1_zfmisc_1(A_168)) ) ),
    inference(resolution,[status(thm)],[c_6,c_2248])).

tff(c_26210,plain,
    ( r1_tarski('#skF_4',k1_tops_1('#skF_1','#skF_4'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_26163,c_2272])).

tff(c_26262,plain,
    ( r1_tarski('#skF_4',k1_tops_1('#skF_1','#skF_4'))
    | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_215,c_26210])).

tff(c_26263,plain,(
    ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(negUnitSimplification,[status(thm)],[c_2273,c_26262])).

tff(c_26278,plain,(
    ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_18,c_26263])).

tff(c_26285,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_215,c_26278])).

tff(c_26286,plain,(
    k1_tops_1('#skF_1','#skF_4') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_740])).

tff(c_26788,plain,(
    ! [A_656,B_657,C_658] :
      ( r1_tarski(k1_tops_1(A_656,B_657),k1_tops_1(A_656,C_658))
      | ~ r1_tarski(B_657,C_658)
      | ~ m1_subset_1(C_658,k1_zfmisc_1(u1_struct_0(A_656)))
      | ~ m1_subset_1(B_657,k1_zfmisc_1(u1_struct_0(A_656)))
      | ~ l1_pre_topc(A_656) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_33683,plain,(
    ! [A_846,B_847,C_848] :
      ( k2_xboole_0(k1_tops_1(A_846,B_847),k1_tops_1(A_846,C_848)) = k1_tops_1(A_846,C_848)
      | ~ r1_tarski(B_847,C_848)
      | ~ m1_subset_1(C_848,k1_zfmisc_1(u1_struct_0(A_846)))
      | ~ m1_subset_1(B_847,k1_zfmisc_1(u1_struct_0(A_846)))
      | ~ l1_pre_topc(A_846) ) ),
    inference(resolution,[status(thm)],[c_26788,c_10])).

tff(c_33695,plain,(
    ! [B_847] :
      ( k2_xboole_0(k1_tops_1('#skF_1',B_847),k1_tops_1('#skF_1','#skF_3')) = k1_tops_1('#skF_1','#skF_3')
      | ~ r1_tarski(B_847,'#skF_3')
      | ~ m1_subset_1(B_847,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_44,c_33683])).

tff(c_33860,plain,(
    ! [B_852] :
      ( k2_xboole_0(k1_tops_1('#skF_1',B_852),k1_tops_1('#skF_1','#skF_3')) = k1_tops_1('#skF_1','#skF_3')
      | ~ r1_tarski(B_852,'#skF_3')
      | ~ m1_subset_1(B_852,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_33695])).

tff(c_33871,plain,
    ( k2_xboole_0(k1_tops_1('#skF_1','#skF_4'),k1_tops_1('#skF_1','#skF_3')) = k1_tops_1('#skF_1','#skF_3')
    | ~ r1_tarski('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_215,c_33860])).

tff(c_33885,plain,(
    k2_xboole_0('#skF_4',k1_tops_1('#skF_1','#skF_3')) = k1_tops_1('#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_134,c_26286,c_33871])).

tff(c_104,plain,(
    ! [A_61,B_62] :
      ( r1_tarski(k1_tarski(A_61),B_62)
      | ~ r2_hidden(A_61,B_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_108,plain,(
    ! [A_61,B_62] :
      ( k2_xboole_0(k1_tarski(A_61),B_62) = B_62
      | ~ r2_hidden(A_61,B_62) ) ),
    inference(resolution,[status(thm)],[c_104,c_10])).

tff(c_163,plain,(
    ! [A_71,B_72] : r1_tarski(A_71,k2_xboole_0(A_71,B_72)) ),
    inference(resolution,[status(thm)],[c_6,c_148])).

tff(c_8,plain,(
    ! [A_3,C_5,B_4] :
      ( r1_tarski(A_3,C_5)
      | ~ r1_tarski(k2_xboole_0(A_3,B_4),C_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_255,plain,(
    ! [A_77,B_78,B_79] : r1_tarski(A_77,k2_xboole_0(k2_xboole_0(A_77,B_78),B_79)) ),
    inference(resolution,[status(thm)],[c_163,c_8])).

tff(c_14,plain,(
    ! [A_11,B_12] :
      ( r2_hidden(A_11,B_12)
      | ~ r1_tarski(k1_tarski(A_11),B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_1099,plain,(
    ! [A_119,B_120,B_121] : r2_hidden(A_119,k2_xboole_0(k2_xboole_0(k1_tarski(A_119),B_120),B_121)) ),
    inference(resolution,[status(thm)],[c_255,c_14])).

tff(c_1110,plain,(
    ! [A_61,B_62,B_121] :
      ( r2_hidden(A_61,k2_xboole_0(B_62,B_121))
      | ~ r2_hidden(A_61,B_62) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_108,c_1099])).

tff(c_34422,plain,(
    ! [A_860] :
      ( r2_hidden(A_860,k1_tops_1('#skF_1','#skF_3'))
      | ~ r2_hidden(A_860,'#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_33885,c_1110])).

tff(c_50,plain,(
    ! [D_52] :
      ( ~ r2_hidden('#skF_2',D_52)
      | ~ r1_tarski(D_52,'#skF_3')
      | ~ v3_pre_topc(D_52,'#skF_1')
      | ~ m1_subset_1(D_52,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ r2_hidden('#skF_2',k1_tops_1('#skF_1','#skF_3')) ) ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_908,plain,(
    ~ r2_hidden('#skF_2',k1_tops_1('#skF_1','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_50])).

tff(c_34436,plain,(
    ~ r2_hidden('#skF_2','#skF_4') ),
    inference(resolution,[status(thm)],[c_34422,c_908])).

tff(c_34444,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_99,c_34436])).

tff(c_34658,plain,(
    ! [D_873] :
      ( ~ r2_hidden('#skF_2',D_873)
      | ~ r1_tarski(D_873,'#skF_3')
      | ~ v3_pre_topc(D_873,'#skF_1')
      | ~ m1_subset_1(D_873,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_34669,plain,
    ( ~ r2_hidden('#skF_2','#skF_4')
    | ~ r1_tarski('#skF_4','#skF_3')
    | ~ v3_pre_topc('#skF_4','#skF_1') ),
    inference(resolution,[status(thm)],[c_215,c_34658])).

tff(c_34684,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_135,c_134,c_99,c_34669])).

tff(c_34686,plain,(
    ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_68])).

tff(c_34696,plain,(
    ~ r1_tarski('#skF_4',u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_24,c_34686])).

tff(c_34700,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_212,c_34696])).

tff(c_34701,plain,(
    r2_hidden('#skF_2',k1_tops_1('#skF_1','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_64])).

tff(c_35116,plain,(
    k2_xboole_0(k1_tops_1('#skF_1','#skF_3'),'#skF_3') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_35106,c_10])).

tff(c_35126,plain,(
    ! [C_5] :
      ( r1_tarski(k1_tops_1('#skF_1','#skF_3'),C_5)
      | ~ r1_tarski('#skF_3',C_5) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_35116,c_8])).

tff(c_34702,plain,(
    ~ v3_pre_topc('#skF_4','#skF_1') ),
    inference(splitRight,[status(thm)],[c_64])).

tff(c_62,plain,(
    ! [D_52] :
      ( ~ r2_hidden('#skF_2',D_52)
      | ~ r1_tarski(D_52,'#skF_3')
      | ~ v3_pre_topc(D_52,'#skF_1')
      | ~ m1_subset_1(D_52,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | v3_pre_topc('#skF_4','#skF_1') ) ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_35150,plain,(
    ! [D_905] :
      ( ~ r2_hidden('#skF_2',D_905)
      | ~ r1_tarski(D_905,'#skF_3')
      | ~ v3_pre_topc(D_905,'#skF_1')
      | ~ m1_subset_1(D_905,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_34702,c_62])).

tff(c_35755,plain,(
    ! [A_940] :
      ( ~ r2_hidden('#skF_2',A_940)
      | ~ r1_tarski(A_940,'#skF_3')
      | ~ v3_pre_topc(A_940,'#skF_1')
      | ~ r1_tarski(A_940,u1_struct_0('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_24,c_35150])).

tff(c_35759,plain,
    ( ~ r2_hidden('#skF_2',k1_tops_1('#skF_1','#skF_3'))
    | ~ r1_tarski(k1_tops_1('#skF_1','#skF_3'),'#skF_3')
    | ~ v3_pre_topc(k1_tops_1('#skF_1','#skF_3'),'#skF_1')
    | ~ r1_tarski('#skF_3',u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_35126,c_35755])).

tff(c_35786,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_35262,c_35106,c_34701,c_35759])).

tff(c_35787,plain,(
    r2_hidden('#skF_2',k1_tops_1('#skF_1','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_60])).

tff(c_36235,plain,(
    k2_xboole_0(k1_tops_1('#skF_1','#skF_3'),'#skF_3') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_36225,c_10])).

tff(c_36260,plain,(
    ! [C_5] :
      ( r1_tarski(k1_tops_1('#skF_1','#skF_3'),C_5)
      | ~ r1_tarski('#skF_3',C_5) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_36235,c_8])).

tff(c_35788,plain,(
    ~ r1_tarski('#skF_4','#skF_3') ),
    inference(splitRight,[status(thm)],[c_60])).

tff(c_58,plain,(
    ! [D_52] :
      ( ~ r2_hidden('#skF_2',D_52)
      | ~ r1_tarski(D_52,'#skF_3')
      | ~ v3_pre_topc(D_52,'#skF_1')
      | ~ m1_subset_1(D_52,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | r1_tarski('#skF_4','#skF_3') ) ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_36280,plain,(
    ! [D_984] :
      ( ~ r2_hidden('#skF_2',D_984)
      | ~ r1_tarski(D_984,'#skF_3')
      | ~ v3_pre_topc(D_984,'#skF_1')
      | ~ m1_subset_1(D_984,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_35788,c_58])).

tff(c_36889,plain,(
    ! [A_1008] :
      ( ~ r2_hidden('#skF_2',A_1008)
      | ~ r1_tarski(A_1008,'#skF_3')
      | ~ v3_pre_topc(A_1008,'#skF_1')
      | ~ r1_tarski(A_1008,u1_struct_0('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_24,c_36280])).

tff(c_36900,plain,
    ( ~ r2_hidden('#skF_2',k1_tops_1('#skF_1','#skF_3'))
    | ~ r1_tarski(k1_tops_1('#skF_1','#skF_3'),'#skF_3')
    | ~ v3_pre_topc(k1_tops_1('#skF_1','#skF_3'),'#skF_1')
    | ~ r1_tarski('#skF_3',u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_36260,c_36889])).

tff(c_36931,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_36754,c_36225,c_35787,c_36900])).

tff(c_36932,plain,(
    r2_hidden('#skF_2',k1_tops_1('#skF_1','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_37526,plain,(
    k2_xboole_0(k1_tops_1('#skF_1','#skF_3'),'#skF_3') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_37516,c_10])).

tff(c_37554,plain,(
    ! [C_5] :
      ( r1_tarski(k1_tops_1('#skF_1','#skF_3'),C_5)
      | ~ r1_tarski('#skF_3',C_5) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_37526,c_8])).

tff(c_36933,plain,(
    ~ r2_hidden('#skF_2','#skF_4') ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_54,plain,(
    ! [D_52] :
      ( ~ r2_hidden('#skF_2',D_52)
      | ~ r1_tarski(D_52,'#skF_3')
      | ~ v3_pre_topc(D_52,'#skF_1')
      | ~ m1_subset_1(D_52,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | r2_hidden('#skF_2','#skF_4') ) ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_37705,plain,(
    ! [D_1069] :
      ( ~ r2_hidden('#skF_2',D_1069)
      | ~ r1_tarski(D_1069,'#skF_3')
      | ~ v3_pre_topc(D_1069,'#skF_1')
      | ~ m1_subset_1(D_1069,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_36933,c_54])).

tff(c_38358,plain,(
    ! [A_1091] :
      ( ~ r2_hidden('#skF_2',A_1091)
      | ~ r1_tarski(A_1091,'#skF_3')
      | ~ v3_pre_topc(A_1091,'#skF_1')
      | ~ r1_tarski(A_1091,u1_struct_0('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_24,c_37705])).

tff(c_38372,plain,
    ( ~ r2_hidden('#skF_2',k1_tops_1('#skF_1','#skF_3'))
    | ~ r1_tarski(k1_tops_1('#skF_1','#skF_3'),'#skF_3')
    | ~ v3_pre_topc(k1_tops_1('#skF_1','#skF_3'),'#skF_1')
    | ~ r1_tarski('#skF_3',u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_37554,c_38358])).

tff(c_38404,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_37656,c_37516,c_36932,c_38372])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:15:04 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 14.71/6.54  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 14.71/6.56  
% 14.71/6.56  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 14.71/6.56  %$ v4_pre_topc > v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k3_subset_1 > k2_xboole_0 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 14.71/6.56  
% 14.71/6.56  %Foreground sorts:
% 14.71/6.56  
% 14.71/6.56  
% 14.71/6.56  %Background operators:
% 14.71/6.56  
% 14.71/6.56  
% 14.71/6.56  %Foreground operators:
% 14.71/6.56  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 14.71/6.56  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 14.71/6.56  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 14.71/6.56  tff(k1_tarski, type, k1_tarski: $i > $i).
% 14.71/6.56  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 14.71/6.56  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 14.71/6.56  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 14.71/6.56  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 14.71/6.56  tff('#skF_2', type, '#skF_2': $i).
% 14.71/6.56  tff('#skF_3', type, '#skF_3': $i).
% 14.71/6.56  tff('#skF_1', type, '#skF_1': $i).
% 14.71/6.56  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 14.71/6.56  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 14.71/6.56  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 14.71/6.56  tff('#skF_4', type, '#skF_4': $i).
% 14.71/6.56  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 14.71/6.56  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 14.71/6.56  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 14.71/6.56  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 14.71/6.56  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 14.71/6.56  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 14.71/6.56  
% 14.71/6.58  tff(f_149, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B, C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (r2_hidden(B, k1_tops_1(A, C)) <=> (?[D]: (((m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) & v3_pre_topc(D, A)) & r1_tarski(D, C)) & r2_hidden(B, D)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t54_tops_1)).
% 14.71/6.58  tff(f_66, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 14.71/6.58  tff(f_102, axiom, (![A, B]: (((v2_pre_topc(A) & l1_pre_topc(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => v3_pre_topc(k1_tops_1(A, B), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc9_tops_1)).
% 14.71/6.58  tff(f_118, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => r1_tarski(k1_tops_1(A, B), B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_tops_1)).
% 14.71/6.58  tff(f_39, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 14.71/6.58  tff(f_35, axiom, (![A, B, C]: (r1_tarski(k2_xboole_0(A, B), C) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_xboole_1)).
% 14.71/6.58  tff(f_53, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k3_subset_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 14.71/6.58  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 14.71/6.58  tff(f_111, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_pre_topc(B, A) <=> v4_pre_topc(k3_subset_1(u1_struct_0(A), B), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t30_tops_1)).
% 14.71/6.58  tff(f_81, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v4_pre_topc(B, A) => (k2_pre_topc(A, B) = B)) & ((v2_pre_topc(A) & (k2_pre_topc(A, B) = B)) => v4_pre_topc(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_pre_topc)).
% 14.71/6.58  tff(f_88, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k1_tops_1(A, B) = k3_subset_1(u1_struct_0(A), k2_pre_topc(A, k3_subset_1(u1_struct_0(A), B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tops_1)).
% 14.71/6.58  tff(f_62, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (r1_tarski(B, k3_subset_1(A, C)) => r1_tarski(C, k3_subset_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t35_subset_1)).
% 14.71/6.58  tff(f_130, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (r1_tarski(B, C) => r1_tarski(k1_tops_1(A, B), k1_tops_1(A, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_tops_1)).
% 14.71/6.58  tff(f_49, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 14.71/6.58  tff(c_44, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_149])).
% 14.71/6.58  tff(c_72, plain, (![A_56, B_57]: (r1_tarski(A_56, B_57) | ~m1_subset_1(A_56, k1_zfmisc_1(B_57)))), inference(cnfTransformation, [status(thm)], [f_66])).
% 14.71/6.58  tff(c_80, plain, (r1_tarski('#skF_3', u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_44, c_72])).
% 14.71/6.58  tff(c_48, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_149])).
% 14.71/6.58  tff(c_46, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_149])).
% 14.71/6.58  tff(c_37643, plain, (![A_1067, B_1068]: (v3_pre_topc(k1_tops_1(A_1067, B_1068), A_1067) | ~m1_subset_1(B_1068, k1_zfmisc_1(u1_struct_0(A_1067))) | ~l1_pre_topc(A_1067) | ~v2_pre_topc(A_1067))), inference(cnfTransformation, [status(thm)], [f_102])).
% 14.71/6.58  tff(c_37651, plain, (v3_pre_topc(k1_tops_1('#skF_1', '#skF_3'), '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_44, c_37643])).
% 14.71/6.58  tff(c_37656, plain, (v3_pre_topc(k1_tops_1('#skF_1', '#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_37651])).
% 14.71/6.58  tff(c_37503, plain, (![A_1061, B_1062]: (r1_tarski(k1_tops_1(A_1061, B_1062), B_1062) | ~m1_subset_1(B_1062, k1_zfmisc_1(u1_struct_0(A_1061))) | ~l1_pre_topc(A_1061))), inference(cnfTransformation, [status(thm)], [f_118])).
% 14.71/6.58  tff(c_37511, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_3'), '#skF_3') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_44, c_37503])).
% 14.71/6.58  tff(c_37516, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_3'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_37511])).
% 14.71/6.58  tff(c_36738, plain, (![A_1000, B_1001]: (v3_pre_topc(k1_tops_1(A_1000, B_1001), A_1000) | ~m1_subset_1(B_1001, k1_zfmisc_1(u1_struct_0(A_1000))) | ~l1_pre_topc(A_1000) | ~v2_pre_topc(A_1000))), inference(cnfTransformation, [status(thm)], [f_102])).
% 14.71/6.58  tff(c_36748, plain, (v3_pre_topc(k1_tops_1('#skF_1', '#skF_3'), '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_44, c_36738])).
% 14.71/6.58  tff(c_36754, plain, (v3_pre_topc(k1_tops_1('#skF_1', '#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_36748])).
% 14.71/6.58  tff(c_36212, plain, (![A_982, B_983]: (r1_tarski(k1_tops_1(A_982, B_983), B_983) | ~m1_subset_1(B_983, k1_zfmisc_1(u1_struct_0(A_982))) | ~l1_pre_topc(A_982))), inference(cnfTransformation, [status(thm)], [f_118])).
% 14.71/6.58  tff(c_36220, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_3'), '#skF_3') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_44, c_36212])).
% 14.71/6.58  tff(c_36225, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_3'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_36220])).
% 14.71/6.58  tff(c_35249, plain, (![A_909, B_910]: (v3_pre_topc(k1_tops_1(A_909, B_910), A_909) | ~m1_subset_1(B_910, k1_zfmisc_1(u1_struct_0(A_909))) | ~l1_pre_topc(A_909) | ~v2_pre_topc(A_909))), inference(cnfTransformation, [status(thm)], [f_102])).
% 14.71/6.58  tff(c_35257, plain, (v3_pre_topc(k1_tops_1('#skF_1', '#skF_3'), '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_44, c_35249])).
% 14.71/6.58  tff(c_35262, plain, (v3_pre_topc(k1_tops_1('#skF_1', '#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_35257])).
% 14.71/6.58  tff(c_35093, plain, (![A_902, B_903]: (r1_tarski(k1_tops_1(A_902, B_903), B_903) | ~m1_subset_1(B_903, k1_zfmisc_1(u1_struct_0(A_902))) | ~l1_pre_topc(A_902))), inference(cnfTransformation, [status(thm)], [f_118])).
% 14.71/6.58  tff(c_35101, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_3'), '#skF_3') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_44, c_35093])).
% 14.71/6.58  tff(c_35106, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_3'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_35101])).
% 14.71/6.58  tff(c_60, plain, (r2_hidden('#skF_2', k1_tops_1('#skF_1', '#skF_3')) | r1_tarski('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_149])).
% 14.71/6.58  tff(c_134, plain, (r1_tarski('#skF_4', '#skF_3')), inference(splitLeft, [status(thm)], [c_60])).
% 14.71/6.58  tff(c_10, plain, (![A_6, B_7]: (k2_xboole_0(A_6, B_7)=B_7 | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_39])).
% 14.71/6.58  tff(c_142, plain, (k2_xboole_0('#skF_4', '#skF_3')='#skF_3'), inference(resolution, [status(thm)], [c_134, c_10])).
% 14.71/6.58  tff(c_148, plain, (![A_68, C_69, B_70]: (r1_tarski(A_68, C_69) | ~r1_tarski(k2_xboole_0(A_68, B_70), C_69))), inference(cnfTransformation, [status(thm)], [f_35])).
% 14.71/6.58  tff(c_199, plain, (![C_75]: (r1_tarski('#skF_4', C_75) | ~r1_tarski('#skF_3', C_75))), inference(superposition, [status(thm), theory('equality')], [c_142, c_148])).
% 14.71/6.58  tff(c_212, plain, (r1_tarski('#skF_4', u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_80, c_199])).
% 14.71/6.58  tff(c_24, plain, (![A_19, B_20]: (m1_subset_1(A_19, k1_zfmisc_1(B_20)) | ~r1_tarski(A_19, B_20))), inference(cnfTransformation, [status(thm)], [f_66])).
% 14.71/6.58  tff(c_64, plain, (r2_hidden('#skF_2', k1_tops_1('#skF_1', '#skF_3')) | v3_pre_topc('#skF_4', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_149])).
% 14.71/6.58  tff(c_135, plain, (v3_pre_topc('#skF_4', '#skF_1')), inference(splitLeft, [status(thm)], [c_64])).
% 14.71/6.58  tff(c_56, plain, (r2_hidden('#skF_2', k1_tops_1('#skF_1', '#skF_3')) | r2_hidden('#skF_2', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_149])).
% 14.71/6.58  tff(c_99, plain, (r2_hidden('#skF_2', '#skF_4')), inference(splitLeft, [status(thm)], [c_56])).
% 14.71/6.58  tff(c_68, plain, (r2_hidden('#skF_2', k1_tops_1('#skF_1', '#skF_3')) | m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_149])).
% 14.71/6.58  tff(c_215, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitLeft, [status(thm)], [c_68])).
% 14.71/6.58  tff(c_18, plain, (![A_13, B_14]: (m1_subset_1(k3_subset_1(A_13, B_14), k1_zfmisc_1(A_13)) | ~m1_subset_1(B_14, k1_zfmisc_1(A_13)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 14.71/6.58  tff(c_699, plain, (![A_101, B_102]: (r1_tarski(k1_tops_1(A_101, B_102), B_102) | ~m1_subset_1(B_102, k1_zfmisc_1(u1_struct_0(A_101))) | ~l1_pre_topc(A_101))), inference(cnfTransformation, [status(thm)], [f_118])).
% 14.71/6.58  tff(c_704, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_4'), '#skF_4') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_215, c_699])).
% 14.71/6.58  tff(c_713, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_4'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_704])).
% 14.71/6.58  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 14.71/6.58  tff(c_740, plain, (k1_tops_1('#skF_1', '#skF_4')='#skF_4' | ~r1_tarski('#skF_4', k1_tops_1('#skF_1', '#skF_4'))), inference(resolution, [status(thm)], [c_713, c_2])).
% 14.71/6.58  tff(c_2273, plain, (~r1_tarski('#skF_4', k1_tops_1('#skF_1', '#skF_4'))), inference(splitLeft, [status(thm)], [c_740])).
% 14.71/6.58  tff(c_38, plain, (![A_31, B_33]: (v4_pre_topc(k3_subset_1(u1_struct_0(A_31), B_33), A_31) | ~v3_pre_topc(B_33, A_31) | ~m1_subset_1(B_33, k1_zfmisc_1(u1_struct_0(A_31))) | ~l1_pre_topc(A_31))), inference(cnfTransformation, [status(thm)], [f_111])).
% 14.71/6.58  tff(c_1056, plain, (![A_115, B_116]: (k2_pre_topc(A_115, B_116)=B_116 | ~v4_pre_topc(B_116, A_115) | ~m1_subset_1(B_116, k1_zfmisc_1(u1_struct_0(A_115))) | ~l1_pre_topc(A_115))), inference(cnfTransformation, [status(thm)], [f_81])).
% 14.71/6.58  tff(c_8991, plain, (![A_340, B_341]: (k2_pre_topc(A_340, k3_subset_1(u1_struct_0(A_340), B_341))=k3_subset_1(u1_struct_0(A_340), B_341) | ~v4_pre_topc(k3_subset_1(u1_struct_0(A_340), B_341), A_340) | ~l1_pre_topc(A_340) | ~m1_subset_1(B_341, k1_zfmisc_1(u1_struct_0(A_340))))), inference(resolution, [status(thm)], [c_18, c_1056])).
% 14.71/6.58  tff(c_26114, plain, (![A_634, B_635]: (k2_pre_topc(A_634, k3_subset_1(u1_struct_0(A_634), B_635))=k3_subset_1(u1_struct_0(A_634), B_635) | ~v3_pre_topc(B_635, A_634) | ~m1_subset_1(B_635, k1_zfmisc_1(u1_struct_0(A_634))) | ~l1_pre_topc(A_634))), inference(resolution, [status(thm)], [c_38, c_8991])).
% 14.71/6.58  tff(c_26121, plain, (k2_pre_topc('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_4'))=k3_subset_1(u1_struct_0('#skF_1'), '#skF_4') | ~v3_pre_topc('#skF_4', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_215, c_26114])).
% 14.71/6.58  tff(c_26131, plain, (k2_pre_topc('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_4'))=k3_subset_1(u1_struct_0('#skF_1'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_135, c_26121])).
% 14.71/6.58  tff(c_30, plain, (![A_24, B_26]: (k3_subset_1(u1_struct_0(A_24), k2_pre_topc(A_24, k3_subset_1(u1_struct_0(A_24), B_26)))=k1_tops_1(A_24, B_26) | ~m1_subset_1(B_26, k1_zfmisc_1(u1_struct_0(A_24))) | ~l1_pre_topc(A_24))), inference(cnfTransformation, [status(thm)], [f_88])).
% 14.71/6.58  tff(c_26151, plain, (k3_subset_1(u1_struct_0('#skF_1'), k3_subset_1(u1_struct_0('#skF_1'), '#skF_4'))=k1_tops_1('#skF_1', '#skF_4') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_26131, c_30])).
% 14.71/6.58  tff(c_26163, plain, (k3_subset_1(u1_struct_0('#skF_1'), k3_subset_1(u1_struct_0('#skF_1'), '#skF_4'))=k1_tops_1('#skF_1', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_215, c_26151])).
% 14.71/6.58  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 14.71/6.58  tff(c_2248, plain, (![C_167, A_168, B_169]: (r1_tarski(C_167, k3_subset_1(A_168, B_169)) | ~r1_tarski(B_169, k3_subset_1(A_168, C_167)) | ~m1_subset_1(C_167, k1_zfmisc_1(A_168)) | ~m1_subset_1(B_169, k1_zfmisc_1(A_168)))), inference(cnfTransformation, [status(thm)], [f_62])).
% 14.71/6.58  tff(c_2272, plain, (![C_167, A_168]: (r1_tarski(C_167, k3_subset_1(A_168, k3_subset_1(A_168, C_167))) | ~m1_subset_1(C_167, k1_zfmisc_1(A_168)) | ~m1_subset_1(k3_subset_1(A_168, C_167), k1_zfmisc_1(A_168)))), inference(resolution, [status(thm)], [c_6, c_2248])).
% 14.71/6.58  tff(c_26210, plain, (r1_tarski('#skF_4', k1_tops_1('#skF_1', '#skF_4')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_26163, c_2272])).
% 14.71/6.58  tff(c_26262, plain, (r1_tarski('#skF_4', k1_tops_1('#skF_1', '#skF_4')) | ~m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_215, c_26210])).
% 14.71/6.58  tff(c_26263, plain, (~m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(negUnitSimplification, [status(thm)], [c_2273, c_26262])).
% 14.71/6.58  tff(c_26278, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_18, c_26263])).
% 14.71/6.58  tff(c_26285, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_215, c_26278])).
% 14.71/6.58  tff(c_26286, plain, (k1_tops_1('#skF_1', '#skF_4')='#skF_4'), inference(splitRight, [status(thm)], [c_740])).
% 14.71/6.58  tff(c_26788, plain, (![A_656, B_657, C_658]: (r1_tarski(k1_tops_1(A_656, B_657), k1_tops_1(A_656, C_658)) | ~r1_tarski(B_657, C_658) | ~m1_subset_1(C_658, k1_zfmisc_1(u1_struct_0(A_656))) | ~m1_subset_1(B_657, k1_zfmisc_1(u1_struct_0(A_656))) | ~l1_pre_topc(A_656))), inference(cnfTransformation, [status(thm)], [f_130])).
% 14.71/6.58  tff(c_33683, plain, (![A_846, B_847, C_848]: (k2_xboole_0(k1_tops_1(A_846, B_847), k1_tops_1(A_846, C_848))=k1_tops_1(A_846, C_848) | ~r1_tarski(B_847, C_848) | ~m1_subset_1(C_848, k1_zfmisc_1(u1_struct_0(A_846))) | ~m1_subset_1(B_847, k1_zfmisc_1(u1_struct_0(A_846))) | ~l1_pre_topc(A_846))), inference(resolution, [status(thm)], [c_26788, c_10])).
% 14.71/6.58  tff(c_33695, plain, (![B_847]: (k2_xboole_0(k1_tops_1('#skF_1', B_847), k1_tops_1('#skF_1', '#skF_3'))=k1_tops_1('#skF_1', '#skF_3') | ~r1_tarski(B_847, '#skF_3') | ~m1_subset_1(B_847, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_44, c_33683])).
% 14.71/6.58  tff(c_33860, plain, (![B_852]: (k2_xboole_0(k1_tops_1('#skF_1', B_852), k1_tops_1('#skF_1', '#skF_3'))=k1_tops_1('#skF_1', '#skF_3') | ~r1_tarski(B_852, '#skF_3') | ~m1_subset_1(B_852, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_33695])).
% 14.71/6.58  tff(c_33871, plain, (k2_xboole_0(k1_tops_1('#skF_1', '#skF_4'), k1_tops_1('#skF_1', '#skF_3'))=k1_tops_1('#skF_1', '#skF_3') | ~r1_tarski('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_215, c_33860])).
% 14.71/6.58  tff(c_33885, plain, (k2_xboole_0('#skF_4', k1_tops_1('#skF_1', '#skF_3'))=k1_tops_1('#skF_1', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_134, c_26286, c_33871])).
% 14.71/6.58  tff(c_104, plain, (![A_61, B_62]: (r1_tarski(k1_tarski(A_61), B_62) | ~r2_hidden(A_61, B_62))), inference(cnfTransformation, [status(thm)], [f_49])).
% 14.71/6.58  tff(c_108, plain, (![A_61, B_62]: (k2_xboole_0(k1_tarski(A_61), B_62)=B_62 | ~r2_hidden(A_61, B_62))), inference(resolution, [status(thm)], [c_104, c_10])).
% 14.71/6.58  tff(c_163, plain, (![A_71, B_72]: (r1_tarski(A_71, k2_xboole_0(A_71, B_72)))), inference(resolution, [status(thm)], [c_6, c_148])).
% 14.71/6.58  tff(c_8, plain, (![A_3, C_5, B_4]: (r1_tarski(A_3, C_5) | ~r1_tarski(k2_xboole_0(A_3, B_4), C_5))), inference(cnfTransformation, [status(thm)], [f_35])).
% 14.71/6.58  tff(c_255, plain, (![A_77, B_78, B_79]: (r1_tarski(A_77, k2_xboole_0(k2_xboole_0(A_77, B_78), B_79)))), inference(resolution, [status(thm)], [c_163, c_8])).
% 14.71/6.58  tff(c_14, plain, (![A_11, B_12]: (r2_hidden(A_11, B_12) | ~r1_tarski(k1_tarski(A_11), B_12))), inference(cnfTransformation, [status(thm)], [f_49])).
% 14.71/6.58  tff(c_1099, plain, (![A_119, B_120, B_121]: (r2_hidden(A_119, k2_xboole_0(k2_xboole_0(k1_tarski(A_119), B_120), B_121)))), inference(resolution, [status(thm)], [c_255, c_14])).
% 14.71/6.58  tff(c_1110, plain, (![A_61, B_62, B_121]: (r2_hidden(A_61, k2_xboole_0(B_62, B_121)) | ~r2_hidden(A_61, B_62))), inference(superposition, [status(thm), theory('equality')], [c_108, c_1099])).
% 14.71/6.58  tff(c_34422, plain, (![A_860]: (r2_hidden(A_860, k1_tops_1('#skF_1', '#skF_3')) | ~r2_hidden(A_860, '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_33885, c_1110])).
% 14.71/6.58  tff(c_50, plain, (![D_52]: (~r2_hidden('#skF_2', D_52) | ~r1_tarski(D_52, '#skF_3') | ~v3_pre_topc(D_52, '#skF_1') | ~m1_subset_1(D_52, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~r2_hidden('#skF_2', k1_tops_1('#skF_1', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_149])).
% 14.71/6.58  tff(c_908, plain, (~r2_hidden('#skF_2', k1_tops_1('#skF_1', '#skF_3'))), inference(splitLeft, [status(thm)], [c_50])).
% 14.71/6.58  tff(c_34436, plain, (~r2_hidden('#skF_2', '#skF_4')), inference(resolution, [status(thm)], [c_34422, c_908])).
% 14.71/6.58  tff(c_34444, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_99, c_34436])).
% 14.71/6.58  tff(c_34658, plain, (![D_873]: (~r2_hidden('#skF_2', D_873) | ~r1_tarski(D_873, '#skF_3') | ~v3_pre_topc(D_873, '#skF_1') | ~m1_subset_1(D_873, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(splitRight, [status(thm)], [c_50])).
% 14.71/6.58  tff(c_34669, plain, (~r2_hidden('#skF_2', '#skF_4') | ~r1_tarski('#skF_4', '#skF_3') | ~v3_pre_topc('#skF_4', '#skF_1')), inference(resolution, [status(thm)], [c_215, c_34658])).
% 14.71/6.58  tff(c_34684, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_135, c_134, c_99, c_34669])).
% 14.71/6.58  tff(c_34686, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitRight, [status(thm)], [c_68])).
% 14.71/6.58  tff(c_34696, plain, (~r1_tarski('#skF_4', u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_24, c_34686])).
% 14.71/6.58  tff(c_34700, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_212, c_34696])).
% 14.71/6.58  tff(c_34701, plain, (r2_hidden('#skF_2', k1_tops_1('#skF_1', '#skF_3'))), inference(splitRight, [status(thm)], [c_64])).
% 14.71/6.58  tff(c_35116, plain, (k2_xboole_0(k1_tops_1('#skF_1', '#skF_3'), '#skF_3')='#skF_3'), inference(resolution, [status(thm)], [c_35106, c_10])).
% 14.71/6.58  tff(c_35126, plain, (![C_5]: (r1_tarski(k1_tops_1('#skF_1', '#skF_3'), C_5) | ~r1_tarski('#skF_3', C_5))), inference(superposition, [status(thm), theory('equality')], [c_35116, c_8])).
% 14.71/6.58  tff(c_34702, plain, (~v3_pre_topc('#skF_4', '#skF_1')), inference(splitRight, [status(thm)], [c_64])).
% 14.71/6.58  tff(c_62, plain, (![D_52]: (~r2_hidden('#skF_2', D_52) | ~r1_tarski(D_52, '#skF_3') | ~v3_pre_topc(D_52, '#skF_1') | ~m1_subset_1(D_52, k1_zfmisc_1(u1_struct_0('#skF_1'))) | v3_pre_topc('#skF_4', '#skF_1'))), inference(cnfTransformation, [status(thm)], [f_149])).
% 14.71/6.58  tff(c_35150, plain, (![D_905]: (~r2_hidden('#skF_2', D_905) | ~r1_tarski(D_905, '#skF_3') | ~v3_pre_topc(D_905, '#skF_1') | ~m1_subset_1(D_905, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(negUnitSimplification, [status(thm)], [c_34702, c_62])).
% 14.71/6.58  tff(c_35755, plain, (![A_940]: (~r2_hidden('#skF_2', A_940) | ~r1_tarski(A_940, '#skF_3') | ~v3_pre_topc(A_940, '#skF_1') | ~r1_tarski(A_940, u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_24, c_35150])).
% 14.71/6.58  tff(c_35759, plain, (~r2_hidden('#skF_2', k1_tops_1('#skF_1', '#skF_3')) | ~r1_tarski(k1_tops_1('#skF_1', '#skF_3'), '#skF_3') | ~v3_pre_topc(k1_tops_1('#skF_1', '#skF_3'), '#skF_1') | ~r1_tarski('#skF_3', u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_35126, c_35755])).
% 14.71/6.58  tff(c_35786, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_80, c_35262, c_35106, c_34701, c_35759])).
% 14.71/6.58  tff(c_35787, plain, (r2_hidden('#skF_2', k1_tops_1('#skF_1', '#skF_3'))), inference(splitRight, [status(thm)], [c_60])).
% 14.71/6.58  tff(c_36235, plain, (k2_xboole_0(k1_tops_1('#skF_1', '#skF_3'), '#skF_3')='#skF_3'), inference(resolution, [status(thm)], [c_36225, c_10])).
% 14.71/6.58  tff(c_36260, plain, (![C_5]: (r1_tarski(k1_tops_1('#skF_1', '#skF_3'), C_5) | ~r1_tarski('#skF_3', C_5))), inference(superposition, [status(thm), theory('equality')], [c_36235, c_8])).
% 14.71/6.58  tff(c_35788, plain, (~r1_tarski('#skF_4', '#skF_3')), inference(splitRight, [status(thm)], [c_60])).
% 14.71/6.58  tff(c_58, plain, (![D_52]: (~r2_hidden('#skF_2', D_52) | ~r1_tarski(D_52, '#skF_3') | ~v3_pre_topc(D_52, '#skF_1') | ~m1_subset_1(D_52, k1_zfmisc_1(u1_struct_0('#skF_1'))) | r1_tarski('#skF_4', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_149])).
% 14.71/6.58  tff(c_36280, plain, (![D_984]: (~r2_hidden('#skF_2', D_984) | ~r1_tarski(D_984, '#skF_3') | ~v3_pre_topc(D_984, '#skF_1') | ~m1_subset_1(D_984, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(negUnitSimplification, [status(thm)], [c_35788, c_58])).
% 14.71/6.58  tff(c_36889, plain, (![A_1008]: (~r2_hidden('#skF_2', A_1008) | ~r1_tarski(A_1008, '#skF_3') | ~v3_pre_topc(A_1008, '#skF_1') | ~r1_tarski(A_1008, u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_24, c_36280])).
% 14.71/6.58  tff(c_36900, plain, (~r2_hidden('#skF_2', k1_tops_1('#skF_1', '#skF_3')) | ~r1_tarski(k1_tops_1('#skF_1', '#skF_3'), '#skF_3') | ~v3_pre_topc(k1_tops_1('#skF_1', '#skF_3'), '#skF_1') | ~r1_tarski('#skF_3', u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_36260, c_36889])).
% 14.71/6.58  tff(c_36931, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_80, c_36754, c_36225, c_35787, c_36900])).
% 14.71/6.58  tff(c_36932, plain, (r2_hidden('#skF_2', k1_tops_1('#skF_1', '#skF_3'))), inference(splitRight, [status(thm)], [c_56])).
% 14.71/6.58  tff(c_37526, plain, (k2_xboole_0(k1_tops_1('#skF_1', '#skF_3'), '#skF_3')='#skF_3'), inference(resolution, [status(thm)], [c_37516, c_10])).
% 14.71/6.58  tff(c_37554, plain, (![C_5]: (r1_tarski(k1_tops_1('#skF_1', '#skF_3'), C_5) | ~r1_tarski('#skF_3', C_5))), inference(superposition, [status(thm), theory('equality')], [c_37526, c_8])).
% 14.71/6.58  tff(c_36933, plain, (~r2_hidden('#skF_2', '#skF_4')), inference(splitRight, [status(thm)], [c_56])).
% 14.71/6.58  tff(c_54, plain, (![D_52]: (~r2_hidden('#skF_2', D_52) | ~r1_tarski(D_52, '#skF_3') | ~v3_pre_topc(D_52, '#skF_1') | ~m1_subset_1(D_52, k1_zfmisc_1(u1_struct_0('#skF_1'))) | r2_hidden('#skF_2', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_149])).
% 14.71/6.58  tff(c_37705, plain, (![D_1069]: (~r2_hidden('#skF_2', D_1069) | ~r1_tarski(D_1069, '#skF_3') | ~v3_pre_topc(D_1069, '#skF_1') | ~m1_subset_1(D_1069, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(negUnitSimplification, [status(thm)], [c_36933, c_54])).
% 14.71/6.58  tff(c_38358, plain, (![A_1091]: (~r2_hidden('#skF_2', A_1091) | ~r1_tarski(A_1091, '#skF_3') | ~v3_pre_topc(A_1091, '#skF_1') | ~r1_tarski(A_1091, u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_24, c_37705])).
% 14.71/6.58  tff(c_38372, plain, (~r2_hidden('#skF_2', k1_tops_1('#skF_1', '#skF_3')) | ~r1_tarski(k1_tops_1('#skF_1', '#skF_3'), '#skF_3') | ~v3_pre_topc(k1_tops_1('#skF_1', '#skF_3'), '#skF_1') | ~r1_tarski('#skF_3', u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_37554, c_38358])).
% 14.71/6.58  tff(c_38404, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_80, c_37656, c_37516, c_36932, c_38372])).
% 14.71/6.58  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 14.71/6.58  
% 14.71/6.58  Inference rules
% 14.71/6.58  ----------------------
% 14.71/6.58  #Ref     : 0
% 14.71/6.58  #Sup     : 9080
% 14.71/6.58  #Fact    : 0
% 14.71/6.58  #Define  : 0
% 14.71/6.58  #Split   : 38
% 14.71/6.58  #Chain   : 0
% 14.71/6.58  #Close   : 0
% 14.71/6.58  
% 14.71/6.58  Ordering : KBO
% 14.71/6.58  
% 14.71/6.58  Simplification rules
% 14.71/6.58  ----------------------
% 14.71/6.58  #Subsume      : 2380
% 14.71/6.58  #Demod        : 4617
% 14.71/6.58  #Tautology    : 2949
% 14.71/6.58  #SimpNegUnit  : 27
% 14.71/6.58  #BackRed      : 13
% 14.71/6.58  
% 14.71/6.58  #Partial instantiations: 0
% 14.71/6.58  #Strategies tried      : 1
% 14.71/6.58  
% 14.71/6.58  Timing (in seconds)
% 14.71/6.58  ----------------------
% 14.71/6.58  Preprocessing        : 0.36
% 14.71/6.58  Parsing              : 0.20
% 14.71/6.58  CNF conversion       : 0.03
% 14.71/6.58  Main loop            : 5.39
% 14.71/6.58  Inferencing          : 1.12
% 14.71/6.58  Reduction            : 2.30
% 14.71/6.58  Demodulation         : 1.80
% 14.71/6.58  BG Simplification    : 0.10
% 14.71/6.58  Subsumption          : 1.49
% 14.71/6.58  Abstraction          : 0.14
% 14.71/6.58  MUC search           : 0.00
% 14.71/6.58  Cooper               : 0.00
% 14.71/6.58  Total                : 5.80
% 14.71/6.58  Index Insertion      : 0.00
% 14.71/6.58  Index Deletion       : 0.00
% 14.71/6.58  Index Matching       : 0.00
% 14.71/6.58  BG Taut test         : 0.00
%------------------------------------------------------------------------------
