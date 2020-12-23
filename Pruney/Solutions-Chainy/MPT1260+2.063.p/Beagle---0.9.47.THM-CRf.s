%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:21:08 EST 2020

% Result     : Theorem 9.77s
% Output     : CNFRefutation 9.99s
% Verified   : 
% Statistics : Number of formulae       :  116 ( 286 expanded)
%              Number of leaves         :   41 ( 116 expanded)
%              Depth                    :   10
%              Number of atoms          :  174 ( 619 expanded)
%              Number of equality atoms :   57 ( 184 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tops_1 > k2_tarski > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_1 > #skF_4 > #skF_5 > #skF_6 > #skF_2 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k2_tops_1,type,(
    k2_tops_1: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k1_tops_1,type,(
    k1_tops_1: ( $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k7_subset_1,type,(
    k7_subset_1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_118,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v3_pre_topc(B,A)
            <=> k2_tops_1(A,B) = k7_subset_1(u1_struct_0(A),k2_pre_topc(A,B),B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_tops_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_58,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_54,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_52,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_62,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

tff(f_106,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k1_tops_1(A,B) = k7_subset_1(u1_struct_0(A),B,k2_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_tops_1)).

tff(f_70,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_pre_topc(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_pre_topc)).

tff(f_34,axiom,(
    ! [A,B,C] :
      ( C = k3_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

tff(f_44,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_56,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_78,axiom,(
    ! [A,B] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => v3_pre_topc(k1_tops_1(A,B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_tops_1)).

tff(f_99,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( ( v3_pre_topc(B,A)
                  & r1_tarski(B,C) )
               => r1_tarski(B,k1_tops_1(A,C)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_tops_1)).

tff(f_85,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_tops_1(A,B) = k7_subset_1(u1_struct_0(A),k2_pre_topc(A,B),k1_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l78_tops_1)).

tff(c_78,plain,
    ( v3_pre_topc('#skF_6','#skF_5')
    | k7_subset_1(u1_struct_0('#skF_5'),k2_pre_topc('#skF_5','#skF_6'),'#skF_6') = k2_tops_1('#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_121,plain,(
    k7_subset_1(u1_struct_0('#skF_5'),k2_pre_topc('#skF_5','#skF_6'),'#skF_6') = k2_tops_1('#skF_5','#skF_6') ),
    inference(splitLeft,[status(thm)],[c_78])).

tff(c_72,plain,
    ( k7_subset_1(u1_struct_0('#skF_5'),k2_pre_topc('#skF_5','#skF_6'),'#skF_6') != k2_tops_1('#skF_5','#skF_6')
    | ~ v3_pre_topc('#skF_6','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_168,plain,(
    ~ v3_pre_topc('#skF_6','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_72])).

tff(c_42,plain,(
    ! [B_14] : r1_tarski(B_14,B_14) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_50,plain,(
    ! [A_20] : k4_xboole_0(A_20,k1_xboole_0) = A_20 ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_46,plain,(
    ! [A_17] : k3_xboole_0(A_17,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_130,plain,(
    ! [A_59,B_60] : k5_xboole_0(A_59,k3_xboole_0(A_59,B_60)) = k4_xboole_0(A_59,B_60) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_139,plain,(
    ! [A_17] : k5_xboole_0(A_17,k1_xboole_0) = k4_xboole_0(A_17,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_130])).

tff(c_142,plain,(
    ! [A_17] : k5_xboole_0(A_17,k1_xboole_0) = A_17 ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_139])).

tff(c_68,plain,(
    l1_pre_topc('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_66,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_173,plain,(
    ! [A_74,B_75,C_76] :
      ( k7_subset_1(A_74,B_75,C_76) = k4_xboole_0(B_75,C_76)
      | ~ m1_subset_1(B_75,k1_zfmisc_1(A_74)) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_176,plain,(
    ! [C_76] : k7_subset_1(u1_struct_0('#skF_5'),'#skF_6',C_76) = k4_xboole_0('#skF_6',C_76) ),
    inference(resolution,[status(thm)],[c_66,c_173])).

tff(c_796,plain,(
    ! [A_127,B_128] :
      ( k7_subset_1(u1_struct_0(A_127),B_128,k2_tops_1(A_127,B_128)) = k1_tops_1(A_127,B_128)
      | ~ m1_subset_1(B_128,k1_zfmisc_1(u1_struct_0(A_127)))
      | ~ l1_pre_topc(A_127) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_800,plain,
    ( k7_subset_1(u1_struct_0('#skF_5'),'#skF_6',k2_tops_1('#skF_5','#skF_6')) = k1_tops_1('#skF_5','#skF_6')
    | ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_66,c_796])).

tff(c_804,plain,(
    k4_xboole_0('#skF_6',k2_tops_1('#skF_5','#skF_6')) = k1_tops_1('#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_176,c_800])).

tff(c_216,plain,(
    ! [A_86,B_87] :
      ( m1_subset_1(k2_pre_topc(A_86,B_87),k1_zfmisc_1(u1_struct_0(A_86)))
      | ~ m1_subset_1(B_87,k1_zfmisc_1(u1_struct_0(A_86)))
      | ~ l1_pre_topc(A_86) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_52,plain,(
    ! [A_21,B_22,C_23] :
      ( k7_subset_1(A_21,B_22,C_23) = k4_xboole_0(B_22,C_23)
      | ~ m1_subset_1(B_22,k1_zfmisc_1(A_21)) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_5084,plain,(
    ! [A_345,B_346,C_347] :
      ( k7_subset_1(u1_struct_0(A_345),k2_pre_topc(A_345,B_346),C_347) = k4_xboole_0(k2_pre_topc(A_345,B_346),C_347)
      | ~ m1_subset_1(B_346,k1_zfmisc_1(u1_struct_0(A_345)))
      | ~ l1_pre_topc(A_345) ) ),
    inference(resolution,[status(thm)],[c_216,c_52])).

tff(c_5088,plain,(
    ! [C_347] :
      ( k7_subset_1(u1_struct_0('#skF_5'),k2_pre_topc('#skF_5','#skF_6'),C_347) = k4_xboole_0(k2_pre_topc('#skF_5','#skF_6'),C_347)
      | ~ l1_pre_topc('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_66,c_5084])).

tff(c_5093,plain,(
    ! [C_348] : k7_subset_1(u1_struct_0('#skF_5'),k2_pre_topc('#skF_5','#skF_6'),C_348) = k4_xboole_0(k2_pre_topc('#skF_5','#skF_6'),C_348) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_5088])).

tff(c_5103,plain,(
    k4_xboole_0(k2_pre_topc('#skF_5','#skF_6'),'#skF_6') = k2_tops_1('#skF_5','#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_5093,c_121])).

tff(c_18,plain,(
    ! [A_1,B_2,C_3] :
      ( r2_hidden('#skF_1'(A_1,B_2,C_3),A_1)
      | r2_hidden('#skF_2'(A_1,B_2,C_3),C_3)
      | k3_xboole_0(A_1,B_2) = C_3 ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_516,plain,(
    ! [A_108,B_109,C_110] :
      ( r2_hidden('#skF_1'(A_108,B_109,C_110),B_109)
      | r2_hidden('#skF_2'(A_108,B_109,C_110),C_110)
      | k3_xboole_0(A_108,B_109) = C_110 ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_22,plain,(
    ! [D_12,B_8,A_7] :
      ( ~ r2_hidden(D_12,B_8)
      | ~ r2_hidden(D_12,k4_xboole_0(A_7,B_8)) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_12848,plain,(
    ! [A_581,A_582,B_583,C_584] :
      ( ~ r2_hidden('#skF_1'(A_581,k4_xboole_0(A_582,B_583),C_584),B_583)
      | r2_hidden('#skF_2'(A_581,k4_xboole_0(A_582,B_583),C_584),C_584)
      | k3_xboole_0(A_581,k4_xboole_0(A_582,B_583)) = C_584 ) ),
    inference(resolution,[status(thm)],[c_516,c_22])).

tff(c_12933,plain,(
    ! [A_1,A_582,C_3] :
      ( r2_hidden('#skF_2'(A_1,k4_xboole_0(A_582,A_1),C_3),C_3)
      | k3_xboole_0(A_1,k4_xboole_0(A_582,A_1)) = C_3 ) ),
    inference(resolution,[status(thm)],[c_18,c_12848])).

tff(c_13535,plain,(
    ! [A_597,A_598,C_599] :
      ( r2_hidden('#skF_2'(A_597,k4_xboole_0(A_598,A_597),C_599),C_599)
      | k3_xboole_0(A_597,k4_xboole_0(A_598,A_597)) = C_599 ) ),
    inference(resolution,[status(thm)],[c_18,c_12848])).

tff(c_152,plain,(
    ! [D_62,B_63,A_64] :
      ( ~ r2_hidden(D_62,B_63)
      | ~ r2_hidden(D_62,k4_xboole_0(A_64,B_63)) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_155,plain,(
    ! [D_62,A_20] :
      ( ~ r2_hidden(D_62,k1_xboole_0)
      | ~ r2_hidden(D_62,A_20) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_152])).

tff(c_13786,plain,(
    ! [A_605,A_606,A_607] :
      ( ~ r2_hidden('#skF_2'(A_605,k4_xboole_0(A_606,A_605),k1_xboole_0),A_607)
      | k3_xboole_0(A_605,k4_xboole_0(A_606,A_605)) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_13535,c_155])).

tff(c_13904,plain,(
    ! [A_608,A_609] : k3_xboole_0(A_608,k4_xboole_0(A_609,A_608)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_12933,c_13786])).

tff(c_14080,plain,(
    k3_xboole_0('#skF_6',k2_tops_1('#skF_5','#skF_6')) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_5103,c_13904])).

tff(c_44,plain,(
    ! [A_15,B_16] : k5_xboole_0(A_15,k3_xboole_0(A_15,B_16)) = k4_xboole_0(A_15,B_16) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_14278,plain,(
    k4_xboole_0('#skF_6',k2_tops_1('#skF_5','#skF_6')) = k5_xboole_0('#skF_6',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_14080,c_44])).

tff(c_14317,plain,(
    k1_tops_1('#skF_5','#skF_6') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_142,c_804,c_14278])).

tff(c_48,plain,(
    ! [A_18,B_19] : r1_tarski(k4_xboole_0(A_18,B_19),A_18) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_111,plain,(
    ! [B_51,A_52] :
      ( B_51 = A_52
      | ~ r1_tarski(B_51,A_52)
      | ~ r1_tarski(A_52,B_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_116,plain,(
    ! [A_18,B_19] :
      ( k4_xboole_0(A_18,B_19) = A_18
      | ~ r1_tarski(A_18,k4_xboole_0(A_18,B_19)) ) ),
    inference(resolution,[status(thm)],[c_48,c_111])).

tff(c_894,plain,
    ( k4_xboole_0('#skF_6',k2_tops_1('#skF_5','#skF_6')) = '#skF_6'
    | ~ r1_tarski('#skF_6',k1_tops_1('#skF_5','#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_804,c_116])).

tff(c_906,plain,
    ( k1_tops_1('#skF_5','#skF_6') = '#skF_6'
    | ~ r1_tarski('#skF_6',k1_tops_1('#skF_5','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_804,c_894])).

tff(c_1074,plain,(
    ~ r1_tarski('#skF_6',k1_tops_1('#skF_5','#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_906])).

tff(c_14373,plain,(
    ~ r1_tarski('#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14317,c_1074])).

tff(c_14387,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_14373])).

tff(c_14388,plain,(
    k1_tops_1('#skF_5','#skF_6') = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_906])).

tff(c_70,plain,(
    v2_pre_topc('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_210,plain,(
    ! [A_84,B_85] :
      ( v3_pre_topc(k1_tops_1(A_84,B_85),A_84)
      | ~ m1_subset_1(B_85,k1_zfmisc_1(u1_struct_0(A_84)))
      | ~ l1_pre_topc(A_84)
      | ~ v2_pre_topc(A_84) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_212,plain,
    ( v3_pre_topc(k1_tops_1('#skF_5','#skF_6'),'#skF_5')
    | ~ l1_pre_topc('#skF_5')
    | ~ v2_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_66,c_210])).

tff(c_215,plain,(
    v3_pre_topc(k1_tops_1('#skF_5','#skF_6'),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_212])).

tff(c_14394,plain,(
    v3_pre_topc('#skF_6','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14388,c_215])).

tff(c_14397,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_168,c_14394])).

tff(c_14398,plain,(
    k7_subset_1(u1_struct_0('#skF_5'),k2_pre_topc('#skF_5','#skF_6'),'#skF_6') != k2_tops_1('#skF_5','#skF_6') ),
    inference(splitRight,[status(thm)],[c_72])).

tff(c_14405,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_121,c_14398])).

tff(c_14406,plain,(
    v3_pre_topc('#skF_6','#skF_5') ),
    inference(splitRight,[status(thm)],[c_78])).

tff(c_14418,plain,(
    k7_subset_1(u1_struct_0('#skF_5'),k2_pre_topc('#skF_5','#skF_6'),'#skF_6') != k2_tops_1('#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14406,c_72])).

tff(c_14480,plain,(
    ! [A_637,B_638,C_639] :
      ( k7_subset_1(A_637,B_638,C_639) = k4_xboole_0(B_638,C_639)
      | ~ m1_subset_1(B_638,k1_zfmisc_1(A_637)) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_14483,plain,(
    ! [C_639] : k7_subset_1(u1_struct_0('#skF_5'),'#skF_6',C_639) = k4_xboole_0('#skF_6',C_639) ),
    inference(resolution,[status(thm)],[c_66,c_14480])).

tff(c_15219,plain,(
    ! [A_695,B_696] :
      ( k7_subset_1(u1_struct_0(A_695),B_696,k2_tops_1(A_695,B_696)) = k1_tops_1(A_695,B_696)
      | ~ m1_subset_1(B_696,k1_zfmisc_1(u1_struct_0(A_695)))
      | ~ l1_pre_topc(A_695) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_15223,plain,
    ( k7_subset_1(u1_struct_0('#skF_5'),'#skF_6',k2_tops_1('#skF_5','#skF_6')) = k1_tops_1('#skF_5','#skF_6')
    | ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_66,c_15219])).

tff(c_15227,plain,(
    k4_xboole_0('#skF_6',k2_tops_1('#skF_5','#skF_6')) = k1_tops_1('#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_14483,c_15223])).

tff(c_15240,plain,
    ( k4_xboole_0('#skF_6',k2_tops_1('#skF_5','#skF_6')) = '#skF_6'
    | ~ r1_tarski('#skF_6',k1_tops_1('#skF_5','#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_15227,c_116])).

tff(c_15254,plain,
    ( k1_tops_1('#skF_5','#skF_6') = '#skF_6'
    | ~ r1_tarski('#skF_6',k1_tops_1('#skF_5','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_15227,c_15240])).

tff(c_15330,plain,(
    ~ r1_tarski('#skF_6',k1_tops_1('#skF_5','#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_15254])).

tff(c_18727,plain,(
    ! [B_877,A_878,C_879] :
      ( r1_tarski(B_877,k1_tops_1(A_878,C_879))
      | ~ r1_tarski(B_877,C_879)
      | ~ v3_pre_topc(B_877,A_878)
      | ~ m1_subset_1(C_879,k1_zfmisc_1(u1_struct_0(A_878)))
      | ~ m1_subset_1(B_877,k1_zfmisc_1(u1_struct_0(A_878)))
      | ~ l1_pre_topc(A_878) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_18731,plain,(
    ! [B_877] :
      ( r1_tarski(B_877,k1_tops_1('#skF_5','#skF_6'))
      | ~ r1_tarski(B_877,'#skF_6')
      | ~ v3_pre_topc(B_877,'#skF_5')
      | ~ m1_subset_1(B_877,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ l1_pre_topc('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_66,c_18727])).

tff(c_18930,plain,(
    ! [B_889] :
      ( r1_tarski(B_889,k1_tops_1('#skF_5','#skF_6'))
      | ~ r1_tarski(B_889,'#skF_6')
      | ~ v3_pre_topc(B_889,'#skF_5')
      | ~ m1_subset_1(B_889,k1_zfmisc_1(u1_struct_0('#skF_5'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_18731])).

tff(c_18937,plain,
    ( r1_tarski('#skF_6',k1_tops_1('#skF_5','#skF_6'))
    | ~ r1_tarski('#skF_6','#skF_6')
    | ~ v3_pre_topc('#skF_6','#skF_5') ),
    inference(resolution,[status(thm)],[c_66,c_18930])).

tff(c_18943,plain,(
    r1_tarski('#skF_6',k1_tops_1('#skF_5','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14406,c_42,c_18937])).

tff(c_18945,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_15330,c_18943])).

tff(c_18946,plain,(
    k1_tops_1('#skF_5','#skF_6') = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_15254])).

tff(c_19062,plain,(
    ! [A_891,B_892] :
      ( k7_subset_1(u1_struct_0(A_891),k2_pre_topc(A_891,B_892),k1_tops_1(A_891,B_892)) = k2_tops_1(A_891,B_892)
      | ~ m1_subset_1(B_892,k1_zfmisc_1(u1_struct_0(A_891)))
      | ~ l1_pre_topc(A_891) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_19071,plain,
    ( k7_subset_1(u1_struct_0('#skF_5'),k2_pre_topc('#skF_5','#skF_6'),'#skF_6') = k2_tops_1('#skF_5','#skF_6')
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_5')))
    | ~ l1_pre_topc('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_18946,c_19062])).

tff(c_19075,plain,(
    k7_subset_1(u1_struct_0('#skF_5'),k2_pre_topc('#skF_5','#skF_6'),'#skF_6') = k2_tops_1('#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_19071])).

tff(c_19077,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_14418,c_19075])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:39:20 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 9.77/3.60  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.77/3.61  
% 9.77/3.61  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.77/3.61  %$ v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tops_1 > k2_tarski > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_1 > #skF_4 > #skF_5 > #skF_6 > #skF_2 > #skF_3
% 9.77/3.61  
% 9.77/3.61  %Foreground sorts:
% 9.77/3.61  
% 9.77/3.61  
% 9.77/3.61  %Background operators:
% 9.77/3.61  
% 9.77/3.61  
% 9.77/3.61  %Foreground operators:
% 9.77/3.61  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 9.77/3.61  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 9.77/3.61  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 9.77/3.61  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 9.77/3.61  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 9.77/3.61  tff(k2_tops_1, type, k2_tops_1: ($i * $i) > $i).
% 9.77/3.61  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 9.77/3.61  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 9.77/3.61  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 9.77/3.61  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 9.77/3.61  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 9.77/3.61  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 9.77/3.61  tff('#skF_5', type, '#skF_5': $i).
% 9.77/3.61  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 9.77/3.61  tff('#skF_6', type, '#skF_6': $i).
% 9.77/3.61  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 9.77/3.61  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 9.77/3.61  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 9.77/3.61  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 9.77/3.61  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 9.77/3.61  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 9.77/3.61  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 9.77/3.61  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 9.77/3.61  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 9.77/3.61  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 9.77/3.61  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 9.77/3.61  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 9.77/3.61  
% 9.99/3.64  tff(f_118, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_pre_topc(B, A) <=> (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), k2_pre_topc(A, B), B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t76_tops_1)).
% 9.99/3.64  tff(f_50, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 9.99/3.64  tff(f_58, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 9.99/3.64  tff(f_54, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 9.99/3.64  tff(f_52, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 9.99/3.64  tff(f_62, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 9.99/3.64  tff(f_106, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k1_tops_1(A, B) = k7_subset_1(u1_struct_0(A), B, k2_tops_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t74_tops_1)).
% 9.99/3.64  tff(f_70, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_pre_topc(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_pre_topc)).
% 9.99/3.64  tff(f_34, axiom, (![A, B, C]: ((C = k3_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_xboole_0)).
% 9.99/3.64  tff(f_44, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 9.99/3.64  tff(f_56, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 9.99/3.64  tff(f_78, axiom, (![A, B]: (((v2_pre_topc(A) & l1_pre_topc(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => v3_pre_topc(k1_tops_1(A, B), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc9_tops_1)).
% 9.99/3.64  tff(f_99, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((v3_pre_topc(B, A) & r1_tarski(B, C)) => r1_tarski(B, k1_tops_1(A, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t56_tops_1)).
% 9.99/3.64  tff(f_85, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), k2_pre_topc(A, B), k1_tops_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l78_tops_1)).
% 9.99/3.64  tff(c_78, plain, (v3_pre_topc('#skF_6', '#skF_5') | k7_subset_1(u1_struct_0('#skF_5'), k2_pre_topc('#skF_5', '#skF_6'), '#skF_6')=k2_tops_1('#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_118])).
% 9.99/3.64  tff(c_121, plain, (k7_subset_1(u1_struct_0('#skF_5'), k2_pre_topc('#skF_5', '#skF_6'), '#skF_6')=k2_tops_1('#skF_5', '#skF_6')), inference(splitLeft, [status(thm)], [c_78])).
% 9.99/3.64  tff(c_72, plain, (k7_subset_1(u1_struct_0('#skF_5'), k2_pre_topc('#skF_5', '#skF_6'), '#skF_6')!=k2_tops_1('#skF_5', '#skF_6') | ~v3_pre_topc('#skF_6', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_118])).
% 9.99/3.64  tff(c_168, plain, (~v3_pre_topc('#skF_6', '#skF_5')), inference(splitLeft, [status(thm)], [c_72])).
% 9.99/3.64  tff(c_42, plain, (![B_14]: (r1_tarski(B_14, B_14))), inference(cnfTransformation, [status(thm)], [f_50])).
% 9.99/3.64  tff(c_50, plain, (![A_20]: (k4_xboole_0(A_20, k1_xboole_0)=A_20)), inference(cnfTransformation, [status(thm)], [f_58])).
% 9.99/3.64  tff(c_46, plain, (![A_17]: (k3_xboole_0(A_17, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_54])).
% 9.99/3.64  tff(c_130, plain, (![A_59, B_60]: (k5_xboole_0(A_59, k3_xboole_0(A_59, B_60))=k4_xboole_0(A_59, B_60))), inference(cnfTransformation, [status(thm)], [f_52])).
% 9.99/3.64  tff(c_139, plain, (![A_17]: (k5_xboole_0(A_17, k1_xboole_0)=k4_xboole_0(A_17, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_46, c_130])).
% 9.99/3.64  tff(c_142, plain, (![A_17]: (k5_xboole_0(A_17, k1_xboole_0)=A_17)), inference(demodulation, [status(thm), theory('equality')], [c_50, c_139])).
% 9.99/3.64  tff(c_68, plain, (l1_pre_topc('#skF_5')), inference(cnfTransformation, [status(thm)], [f_118])).
% 9.99/3.64  tff(c_66, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_5')))), inference(cnfTransformation, [status(thm)], [f_118])).
% 9.99/3.64  tff(c_173, plain, (![A_74, B_75, C_76]: (k7_subset_1(A_74, B_75, C_76)=k4_xboole_0(B_75, C_76) | ~m1_subset_1(B_75, k1_zfmisc_1(A_74)))), inference(cnfTransformation, [status(thm)], [f_62])).
% 9.99/3.64  tff(c_176, plain, (![C_76]: (k7_subset_1(u1_struct_0('#skF_5'), '#skF_6', C_76)=k4_xboole_0('#skF_6', C_76))), inference(resolution, [status(thm)], [c_66, c_173])).
% 9.99/3.64  tff(c_796, plain, (![A_127, B_128]: (k7_subset_1(u1_struct_0(A_127), B_128, k2_tops_1(A_127, B_128))=k1_tops_1(A_127, B_128) | ~m1_subset_1(B_128, k1_zfmisc_1(u1_struct_0(A_127))) | ~l1_pre_topc(A_127))), inference(cnfTransformation, [status(thm)], [f_106])).
% 9.99/3.64  tff(c_800, plain, (k7_subset_1(u1_struct_0('#skF_5'), '#skF_6', k2_tops_1('#skF_5', '#skF_6'))=k1_tops_1('#skF_5', '#skF_6') | ~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_66, c_796])).
% 9.99/3.64  tff(c_804, plain, (k4_xboole_0('#skF_6', k2_tops_1('#skF_5', '#skF_6'))=k1_tops_1('#skF_5', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_176, c_800])).
% 9.99/3.64  tff(c_216, plain, (![A_86, B_87]: (m1_subset_1(k2_pre_topc(A_86, B_87), k1_zfmisc_1(u1_struct_0(A_86))) | ~m1_subset_1(B_87, k1_zfmisc_1(u1_struct_0(A_86))) | ~l1_pre_topc(A_86))), inference(cnfTransformation, [status(thm)], [f_70])).
% 9.99/3.64  tff(c_52, plain, (![A_21, B_22, C_23]: (k7_subset_1(A_21, B_22, C_23)=k4_xboole_0(B_22, C_23) | ~m1_subset_1(B_22, k1_zfmisc_1(A_21)))), inference(cnfTransformation, [status(thm)], [f_62])).
% 9.99/3.64  tff(c_5084, plain, (![A_345, B_346, C_347]: (k7_subset_1(u1_struct_0(A_345), k2_pre_topc(A_345, B_346), C_347)=k4_xboole_0(k2_pre_topc(A_345, B_346), C_347) | ~m1_subset_1(B_346, k1_zfmisc_1(u1_struct_0(A_345))) | ~l1_pre_topc(A_345))), inference(resolution, [status(thm)], [c_216, c_52])).
% 9.99/3.64  tff(c_5088, plain, (![C_347]: (k7_subset_1(u1_struct_0('#skF_5'), k2_pre_topc('#skF_5', '#skF_6'), C_347)=k4_xboole_0(k2_pre_topc('#skF_5', '#skF_6'), C_347) | ~l1_pre_topc('#skF_5'))), inference(resolution, [status(thm)], [c_66, c_5084])).
% 9.99/3.64  tff(c_5093, plain, (![C_348]: (k7_subset_1(u1_struct_0('#skF_5'), k2_pre_topc('#skF_5', '#skF_6'), C_348)=k4_xboole_0(k2_pre_topc('#skF_5', '#skF_6'), C_348))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_5088])).
% 9.99/3.64  tff(c_5103, plain, (k4_xboole_0(k2_pre_topc('#skF_5', '#skF_6'), '#skF_6')=k2_tops_1('#skF_5', '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_5093, c_121])).
% 9.99/3.64  tff(c_18, plain, (![A_1, B_2, C_3]: (r2_hidden('#skF_1'(A_1, B_2, C_3), A_1) | r2_hidden('#skF_2'(A_1, B_2, C_3), C_3) | k3_xboole_0(A_1, B_2)=C_3)), inference(cnfTransformation, [status(thm)], [f_34])).
% 9.99/3.64  tff(c_516, plain, (![A_108, B_109, C_110]: (r2_hidden('#skF_1'(A_108, B_109, C_110), B_109) | r2_hidden('#skF_2'(A_108, B_109, C_110), C_110) | k3_xboole_0(A_108, B_109)=C_110)), inference(cnfTransformation, [status(thm)], [f_34])).
% 9.99/3.64  tff(c_22, plain, (![D_12, B_8, A_7]: (~r2_hidden(D_12, B_8) | ~r2_hidden(D_12, k4_xboole_0(A_7, B_8)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 9.99/3.64  tff(c_12848, plain, (![A_581, A_582, B_583, C_584]: (~r2_hidden('#skF_1'(A_581, k4_xboole_0(A_582, B_583), C_584), B_583) | r2_hidden('#skF_2'(A_581, k4_xboole_0(A_582, B_583), C_584), C_584) | k3_xboole_0(A_581, k4_xboole_0(A_582, B_583))=C_584)), inference(resolution, [status(thm)], [c_516, c_22])).
% 9.99/3.64  tff(c_12933, plain, (![A_1, A_582, C_3]: (r2_hidden('#skF_2'(A_1, k4_xboole_0(A_582, A_1), C_3), C_3) | k3_xboole_0(A_1, k4_xboole_0(A_582, A_1))=C_3)), inference(resolution, [status(thm)], [c_18, c_12848])).
% 9.99/3.64  tff(c_13535, plain, (![A_597, A_598, C_599]: (r2_hidden('#skF_2'(A_597, k4_xboole_0(A_598, A_597), C_599), C_599) | k3_xboole_0(A_597, k4_xboole_0(A_598, A_597))=C_599)), inference(resolution, [status(thm)], [c_18, c_12848])).
% 9.99/3.64  tff(c_152, plain, (![D_62, B_63, A_64]: (~r2_hidden(D_62, B_63) | ~r2_hidden(D_62, k4_xboole_0(A_64, B_63)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 9.99/3.64  tff(c_155, plain, (![D_62, A_20]: (~r2_hidden(D_62, k1_xboole_0) | ~r2_hidden(D_62, A_20))), inference(superposition, [status(thm), theory('equality')], [c_50, c_152])).
% 9.99/3.64  tff(c_13786, plain, (![A_605, A_606, A_607]: (~r2_hidden('#skF_2'(A_605, k4_xboole_0(A_606, A_605), k1_xboole_0), A_607) | k3_xboole_0(A_605, k4_xboole_0(A_606, A_605))=k1_xboole_0)), inference(resolution, [status(thm)], [c_13535, c_155])).
% 9.99/3.64  tff(c_13904, plain, (![A_608, A_609]: (k3_xboole_0(A_608, k4_xboole_0(A_609, A_608))=k1_xboole_0)), inference(resolution, [status(thm)], [c_12933, c_13786])).
% 9.99/3.64  tff(c_14080, plain, (k3_xboole_0('#skF_6', k2_tops_1('#skF_5', '#skF_6'))=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_5103, c_13904])).
% 9.99/3.64  tff(c_44, plain, (![A_15, B_16]: (k5_xboole_0(A_15, k3_xboole_0(A_15, B_16))=k4_xboole_0(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_52])).
% 9.99/3.64  tff(c_14278, plain, (k4_xboole_0('#skF_6', k2_tops_1('#skF_5', '#skF_6'))=k5_xboole_0('#skF_6', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_14080, c_44])).
% 9.99/3.64  tff(c_14317, plain, (k1_tops_1('#skF_5', '#skF_6')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_142, c_804, c_14278])).
% 9.99/3.64  tff(c_48, plain, (![A_18, B_19]: (r1_tarski(k4_xboole_0(A_18, B_19), A_18))), inference(cnfTransformation, [status(thm)], [f_56])).
% 9.99/3.64  tff(c_111, plain, (![B_51, A_52]: (B_51=A_52 | ~r1_tarski(B_51, A_52) | ~r1_tarski(A_52, B_51))), inference(cnfTransformation, [status(thm)], [f_50])).
% 9.99/3.64  tff(c_116, plain, (![A_18, B_19]: (k4_xboole_0(A_18, B_19)=A_18 | ~r1_tarski(A_18, k4_xboole_0(A_18, B_19)))), inference(resolution, [status(thm)], [c_48, c_111])).
% 9.99/3.64  tff(c_894, plain, (k4_xboole_0('#skF_6', k2_tops_1('#skF_5', '#skF_6'))='#skF_6' | ~r1_tarski('#skF_6', k1_tops_1('#skF_5', '#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_804, c_116])).
% 9.99/3.64  tff(c_906, plain, (k1_tops_1('#skF_5', '#skF_6')='#skF_6' | ~r1_tarski('#skF_6', k1_tops_1('#skF_5', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_804, c_894])).
% 9.99/3.64  tff(c_1074, plain, (~r1_tarski('#skF_6', k1_tops_1('#skF_5', '#skF_6'))), inference(splitLeft, [status(thm)], [c_906])).
% 9.99/3.64  tff(c_14373, plain, (~r1_tarski('#skF_6', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_14317, c_1074])).
% 9.99/3.64  tff(c_14387, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_42, c_14373])).
% 9.99/3.64  tff(c_14388, plain, (k1_tops_1('#skF_5', '#skF_6')='#skF_6'), inference(splitRight, [status(thm)], [c_906])).
% 9.99/3.64  tff(c_70, plain, (v2_pre_topc('#skF_5')), inference(cnfTransformation, [status(thm)], [f_118])).
% 9.99/3.64  tff(c_210, plain, (![A_84, B_85]: (v3_pre_topc(k1_tops_1(A_84, B_85), A_84) | ~m1_subset_1(B_85, k1_zfmisc_1(u1_struct_0(A_84))) | ~l1_pre_topc(A_84) | ~v2_pre_topc(A_84))), inference(cnfTransformation, [status(thm)], [f_78])).
% 9.99/3.64  tff(c_212, plain, (v3_pre_topc(k1_tops_1('#skF_5', '#skF_6'), '#skF_5') | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_66, c_210])).
% 9.99/3.64  tff(c_215, plain, (v3_pre_topc(k1_tops_1('#skF_5', '#skF_6'), '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_212])).
% 9.99/3.64  tff(c_14394, plain, (v3_pre_topc('#skF_6', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_14388, c_215])).
% 9.99/3.64  tff(c_14397, plain, $false, inference(negUnitSimplification, [status(thm)], [c_168, c_14394])).
% 9.99/3.64  tff(c_14398, plain, (k7_subset_1(u1_struct_0('#skF_5'), k2_pre_topc('#skF_5', '#skF_6'), '#skF_6')!=k2_tops_1('#skF_5', '#skF_6')), inference(splitRight, [status(thm)], [c_72])).
% 9.99/3.64  tff(c_14405, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_121, c_14398])).
% 9.99/3.64  tff(c_14406, plain, (v3_pre_topc('#skF_6', '#skF_5')), inference(splitRight, [status(thm)], [c_78])).
% 9.99/3.64  tff(c_14418, plain, (k7_subset_1(u1_struct_0('#skF_5'), k2_pre_topc('#skF_5', '#skF_6'), '#skF_6')!=k2_tops_1('#skF_5', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_14406, c_72])).
% 9.99/3.64  tff(c_14480, plain, (![A_637, B_638, C_639]: (k7_subset_1(A_637, B_638, C_639)=k4_xboole_0(B_638, C_639) | ~m1_subset_1(B_638, k1_zfmisc_1(A_637)))), inference(cnfTransformation, [status(thm)], [f_62])).
% 9.99/3.64  tff(c_14483, plain, (![C_639]: (k7_subset_1(u1_struct_0('#skF_5'), '#skF_6', C_639)=k4_xboole_0('#skF_6', C_639))), inference(resolution, [status(thm)], [c_66, c_14480])).
% 9.99/3.64  tff(c_15219, plain, (![A_695, B_696]: (k7_subset_1(u1_struct_0(A_695), B_696, k2_tops_1(A_695, B_696))=k1_tops_1(A_695, B_696) | ~m1_subset_1(B_696, k1_zfmisc_1(u1_struct_0(A_695))) | ~l1_pre_topc(A_695))), inference(cnfTransformation, [status(thm)], [f_106])).
% 9.99/3.64  tff(c_15223, plain, (k7_subset_1(u1_struct_0('#skF_5'), '#skF_6', k2_tops_1('#skF_5', '#skF_6'))=k1_tops_1('#skF_5', '#skF_6') | ~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_66, c_15219])).
% 9.99/3.64  tff(c_15227, plain, (k4_xboole_0('#skF_6', k2_tops_1('#skF_5', '#skF_6'))=k1_tops_1('#skF_5', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_14483, c_15223])).
% 9.99/3.64  tff(c_15240, plain, (k4_xboole_0('#skF_6', k2_tops_1('#skF_5', '#skF_6'))='#skF_6' | ~r1_tarski('#skF_6', k1_tops_1('#skF_5', '#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_15227, c_116])).
% 9.99/3.64  tff(c_15254, plain, (k1_tops_1('#skF_5', '#skF_6')='#skF_6' | ~r1_tarski('#skF_6', k1_tops_1('#skF_5', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_15227, c_15240])).
% 9.99/3.64  tff(c_15330, plain, (~r1_tarski('#skF_6', k1_tops_1('#skF_5', '#skF_6'))), inference(splitLeft, [status(thm)], [c_15254])).
% 9.99/3.64  tff(c_18727, plain, (![B_877, A_878, C_879]: (r1_tarski(B_877, k1_tops_1(A_878, C_879)) | ~r1_tarski(B_877, C_879) | ~v3_pre_topc(B_877, A_878) | ~m1_subset_1(C_879, k1_zfmisc_1(u1_struct_0(A_878))) | ~m1_subset_1(B_877, k1_zfmisc_1(u1_struct_0(A_878))) | ~l1_pre_topc(A_878))), inference(cnfTransformation, [status(thm)], [f_99])).
% 9.99/3.64  tff(c_18731, plain, (![B_877]: (r1_tarski(B_877, k1_tops_1('#skF_5', '#skF_6')) | ~r1_tarski(B_877, '#skF_6') | ~v3_pre_topc(B_877, '#skF_5') | ~m1_subset_1(B_877, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~l1_pre_topc('#skF_5'))), inference(resolution, [status(thm)], [c_66, c_18727])).
% 9.99/3.64  tff(c_18930, plain, (![B_889]: (r1_tarski(B_889, k1_tops_1('#skF_5', '#skF_6')) | ~r1_tarski(B_889, '#skF_6') | ~v3_pre_topc(B_889, '#skF_5') | ~m1_subset_1(B_889, k1_zfmisc_1(u1_struct_0('#skF_5'))))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_18731])).
% 9.99/3.64  tff(c_18937, plain, (r1_tarski('#skF_6', k1_tops_1('#skF_5', '#skF_6')) | ~r1_tarski('#skF_6', '#skF_6') | ~v3_pre_topc('#skF_6', '#skF_5')), inference(resolution, [status(thm)], [c_66, c_18930])).
% 9.99/3.64  tff(c_18943, plain, (r1_tarski('#skF_6', k1_tops_1('#skF_5', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_14406, c_42, c_18937])).
% 9.99/3.64  tff(c_18945, plain, $false, inference(negUnitSimplification, [status(thm)], [c_15330, c_18943])).
% 9.99/3.64  tff(c_18946, plain, (k1_tops_1('#skF_5', '#skF_6')='#skF_6'), inference(splitRight, [status(thm)], [c_15254])).
% 9.99/3.64  tff(c_19062, plain, (![A_891, B_892]: (k7_subset_1(u1_struct_0(A_891), k2_pre_topc(A_891, B_892), k1_tops_1(A_891, B_892))=k2_tops_1(A_891, B_892) | ~m1_subset_1(B_892, k1_zfmisc_1(u1_struct_0(A_891))) | ~l1_pre_topc(A_891))), inference(cnfTransformation, [status(thm)], [f_85])).
% 9.99/3.64  tff(c_19071, plain, (k7_subset_1(u1_struct_0('#skF_5'), k2_pre_topc('#skF_5', '#skF_6'), '#skF_6')=k2_tops_1('#skF_5', '#skF_6') | ~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~l1_pre_topc('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_18946, c_19062])).
% 9.99/3.64  tff(c_19075, plain, (k7_subset_1(u1_struct_0('#skF_5'), k2_pre_topc('#skF_5', '#skF_6'), '#skF_6')=k2_tops_1('#skF_5', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_66, c_19071])).
% 9.99/3.64  tff(c_19077, plain, $false, inference(negUnitSimplification, [status(thm)], [c_14418, c_19075])).
% 9.99/3.64  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.99/3.64  
% 9.99/3.64  Inference rules
% 9.99/3.64  ----------------------
% 9.99/3.64  #Ref     : 0
% 9.99/3.64  #Sup     : 3982
% 9.99/3.64  #Fact    : 0
% 9.99/3.64  #Define  : 0
% 9.99/3.64  #Split   : 16
% 9.99/3.64  #Chain   : 0
% 9.99/3.64  #Close   : 0
% 9.99/3.64  
% 9.99/3.64  Ordering : KBO
% 9.99/3.64  
% 9.99/3.64  Simplification rules
% 9.99/3.64  ----------------------
% 9.99/3.64  #Subsume      : 1058
% 9.99/3.64  #Demod        : 3132
% 9.99/3.64  #Tautology    : 1275
% 9.99/3.64  #SimpNegUnit  : 144
% 9.99/3.64  #BackRed      : 166
% 9.99/3.64  
% 9.99/3.64  #Partial instantiations: 0
% 9.99/3.64  #Strategies tried      : 1
% 9.99/3.64  
% 9.99/3.64  Timing (in seconds)
% 9.99/3.64  ----------------------
% 9.99/3.64  Preprocessing        : 0.34
% 9.99/3.64  Parsing              : 0.18
% 9.99/3.64  CNF conversion       : 0.03
% 9.99/3.64  Main loop            : 2.45
% 9.99/3.64  Inferencing          : 0.74
% 9.99/3.64  Reduction            : 0.89
% 9.99/3.64  Demodulation         : 0.65
% 9.99/3.64  BG Simplification    : 0.08
% 9.99/3.64  Subsumption          : 0.56
% 9.99/3.64  Abstraction          : 0.12
% 9.99/3.64  MUC search           : 0.00
% 9.99/3.64  Cooper               : 0.00
% 9.99/3.64  Total                : 2.83
% 9.99/3.64  Index Insertion      : 0.00
% 9.99/3.64  Index Deletion       : 0.00
% 9.99/3.64  Index Matching       : 0.00
% 9.99/3.64  BG Taut test         : 0.00
%------------------------------------------------------------------------------
