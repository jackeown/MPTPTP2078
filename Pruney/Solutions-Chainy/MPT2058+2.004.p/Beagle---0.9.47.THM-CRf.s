%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:31:33 EST 2020

% Result     : Theorem 5.54s
% Output     : CNFRefutation 5.54s
% Verified   : 
% Statistics : Number of formulae       :  200 (2491 expanded)
%              Number of leaves         :   49 ( 870 expanded)
%              Depth                    :   22
%              Number of atoms          :  590 (8897 expanded)
%              Number of equality atoms :   13 ( 474 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r3_waybel_9 > r1_waybel_7 > v6_waybel_0 > v2_waybel_0 > v1_subset_1 > v13_waybel_0 > r2_hidden > r1_tarski > m1_subset_1 > l1_waybel_0 > v7_waybel_0 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v2_pre_topc > v1_zfmisc_1 > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k3_yellow19 > k2_yellow19 > #nlpp > u1_struct_0 > k3_yellow_1 > k3_lattice3 > k2_struct_0 > k1_zfmisc_1 > k1_lattice3 > #skF_1 > #skF_5 > #skF_6 > #skF_4 > #skF_3 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(v3_orders_2,type,(
    v3_orders_2: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k3_lattice3,type,(
    k3_lattice3: $i > $i )).

tff(v6_waybel_0,type,(
    v6_waybel_0: ( $i * $i ) > $o )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(v1_subset_1,type,(
    v1_subset_1: ( $i * $i ) > $o )).

tff(k3_yellow_1,type,(
    k3_yellow_1: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(v2_waybel_0,type,(
    v2_waybel_0: ( $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(v7_waybel_0,type,(
    v7_waybel_0: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(r3_waybel_9,type,(
    r3_waybel_9: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_lattice3,type,(
    k1_lattice3: $i > $i )).

tff(v4_orders_2,type,(
    v4_orders_2: $i > $o )).

tff(r1_waybel_7,type,(
    r1_waybel_7: ( $i * $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff(k2_yellow19,type,(
    k2_yellow19: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(l1_waybel_0,type,(
    l1_waybel_0: ( $i * $i ) > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v1_zfmisc_1,type,(
    v1_zfmisc_1: $i > $o )).

tff(k3_yellow19,type,(
    k3_yellow19: ( $i * $i * $i ) > $i )).

tff(v13_waybel_0,type,(
    v13_waybel_0: ( $i * $i ) > $o )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_227,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( ( ~ v1_xboole_0(B)
              & v1_subset_1(B,u1_struct_0(k3_yellow_1(k2_struct_0(A))))
              & v2_waybel_0(B,k3_yellow_1(k2_struct_0(A)))
              & v13_waybel_0(B,k3_yellow_1(k2_struct_0(A)))
              & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A))))) )
           => ! [C] :
                ( m1_subset_1(C,u1_struct_0(A))
               => ( r3_waybel_9(A,k3_yellow19(A,k2_struct_0(A),B),C)
                <=> r1_waybel_7(A,B,C) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_yellow19)).

tff(f_60,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_52,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_56,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => m1_subset_1(k2_struct_0(A),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_struct_0)).

tff(f_73,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ? [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
          & ~ v1_xboole_0(B)
          & v1_zfmisc_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc20_struct_0)).

tff(f_48,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_129,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A)
        & ~ v1_xboole_0(B)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
        & ~ v1_xboole_0(C)
        & v2_waybel_0(C,k3_yellow_1(B))
        & v13_waybel_0(C,k3_yellow_1(B))
        & m1_subset_1(C,k1_zfmisc_1(u1_struct_0(k3_yellow_1(B)))) )
     => ( ~ v2_struct_0(k3_yellow19(A,B,C))
        & v3_orders_2(k3_yellow19(A,B,C))
        & v4_orders_2(k3_yellow19(A,B,C))
        & v6_waybel_0(k3_yellow19(A,B,C),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_yellow19)).

tff(f_101,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A)
        & ~ v1_xboole_0(B)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
        & ~ v1_xboole_0(C)
        & v2_waybel_0(C,k3_yellow_1(B))
        & v13_waybel_0(C,k3_yellow_1(B))
        & m1_subset_1(C,k1_zfmisc_1(u1_struct_0(k3_yellow_1(B)))) )
     => ( ~ v2_struct_0(k3_yellow19(A,B,C))
        & v6_waybel_0(k3_yellow19(A,B,C),A)
        & l1_waybel_0(k3_yellow19(A,B,C),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_yellow19)).

tff(f_200,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ! [B] :
          ( ( ~ v1_xboole_0(B)
            & v1_subset_1(B,u1_struct_0(k3_yellow_1(k2_struct_0(A))))
            & v2_waybel_0(B,k3_yellow_1(k2_struct_0(A)))
            & v13_waybel_0(B,k3_yellow_1(k2_struct_0(A)))
            & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A))))) )
         => B = k2_yellow19(A,k3_yellow19(A,k2_struct_0(A),B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t15_yellow19)).

tff(f_181,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & v4_orders_2(B)
            & v7_waybel_0(B)
            & l1_waybel_0(B,A) )
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ( r3_waybel_9(A,B,C)
              <=> r1_waybel_7(A,k2_yellow19(A,B),C) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_yellow19)).

tff(f_157,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A)
        & ~ v1_xboole_0(B)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
        & ~ v1_xboole_0(C)
        & v1_subset_1(C,u1_struct_0(k3_yellow_1(B)))
        & v2_waybel_0(C,k3_yellow_1(B))
        & v13_waybel_0(C,k3_yellow_1(B))
        & m1_subset_1(C,k1_zfmisc_1(u1_struct_0(k3_yellow_1(B)))) )
     => ( ~ v2_struct_0(k3_yellow19(A,B,C))
        & v6_waybel_0(k3_yellow19(A,B,C),A)
        & v7_waybel_0(k3_yellow19(A,B,C)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc5_yellow19)).

tff(c_78,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_227])).

tff(c_74,plain,(
    l1_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_227])).

tff(c_26,plain,(
    ! [A_16] :
      ( l1_struct_0(A_16)
      | ~ l1_pre_topc(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_100,plain,(
    ! [A_48] :
      ( u1_struct_0(A_48) = k2_struct_0(A_48)
      | ~ l1_struct_0(A_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_110,plain,(
    ! [A_50] :
      ( u1_struct_0(A_50) = k2_struct_0(A_50)
      | ~ l1_pre_topc(A_50) ) ),
    inference(resolution,[status(thm)],[c_26,c_100])).

tff(c_114,plain,(
    u1_struct_0('#skF_4') = k2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_74,c_110])).

tff(c_145,plain,(
    ! [A_63] :
      ( m1_subset_1(k2_struct_0(A_63),k1_zfmisc_1(u1_struct_0(A_63)))
      | ~ l1_struct_0(A_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_151,plain,
    ( m1_subset_1(k2_struct_0('#skF_4'),k1_zfmisc_1(k2_struct_0('#skF_4')))
    | ~ l1_struct_0('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_114,c_145])).

tff(c_1726,plain,(
    ~ l1_struct_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_151])).

tff(c_1729,plain,(
    ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_26,c_1726])).

tff(c_1733,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_1729])).

tff(c_1735,plain,(
    l1_struct_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_151])).

tff(c_194,plain,(
    ~ l1_struct_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_151])).

tff(c_197,plain,(
    ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_26,c_194])).

tff(c_201,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_197])).

tff(c_203,plain,(
    l1_struct_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_151])).

tff(c_62,plain,(
    m1_subset_1('#skF_6',u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_227])).

tff(c_116,plain,(
    m1_subset_1('#skF_6',k2_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_114,c_62])).

tff(c_80,plain,
    ( ~ r1_waybel_7('#skF_4','#skF_5','#skF_6')
    | ~ r3_waybel_9('#skF_4',k3_yellow19('#skF_4',k2_struct_0('#skF_4'),'#skF_5'),'#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_227])).

tff(c_174,plain,(
    ~ r3_waybel_9('#skF_4',k3_yellow19('#skF_4',k2_struct_0('#skF_4'),'#skF_5'),'#skF_6') ),
    inference(splitLeft,[status(thm)],[c_80])).

tff(c_86,plain,
    ( r3_waybel_9('#skF_4',k3_yellow19('#skF_4',k2_struct_0('#skF_4'),'#skF_5'),'#skF_6')
    | r1_waybel_7('#skF_4','#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_227])).

tff(c_229,plain,(
    r1_waybel_7('#skF_4','#skF_5','#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_174,c_86])).

tff(c_255,plain,(
    ! [A_79] :
      ( m1_subset_1('#skF_3'(A_79),k1_zfmisc_1(u1_struct_0(A_79)))
      | ~ l1_struct_0(A_79)
      | v2_struct_0(A_79) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_261,plain,
    ( m1_subset_1('#skF_3'('#skF_4'),k1_zfmisc_1(k2_struct_0('#skF_4')))
    | ~ l1_struct_0('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_114,c_255])).

tff(c_264,plain,
    ( m1_subset_1('#skF_3'('#skF_4'),k1_zfmisc_1(k2_struct_0('#skF_4')))
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_203,c_261])).

tff(c_265,plain,(
    m1_subset_1('#skF_3'('#skF_4'),k1_zfmisc_1(k2_struct_0('#skF_4'))) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_264])).

tff(c_18,plain,(
    ! [A_12,B_13] :
      ( r1_tarski(A_12,B_13)
      | ~ m1_subset_1(A_12,k1_zfmisc_1(B_13)) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_269,plain,(
    r1_tarski('#skF_3'('#skF_4'),k2_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_265,c_18])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_204,plain,(
    ! [C_71,B_72,A_73] :
      ( r2_hidden(C_71,B_72)
      | ~ r2_hidden(C_71,A_73)
      | ~ r1_tarski(A_73,B_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_221,plain,(
    ! [A_74,B_75] :
      ( r2_hidden('#skF_1'(A_74),B_75)
      | ~ r1_tarski(A_74,B_75)
      | v1_xboole_0(A_74) ) ),
    inference(resolution,[status(thm)],[c_4,c_204])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_228,plain,(
    ! [B_75,A_74] :
      ( ~ v1_xboole_0(B_75)
      | ~ r1_tarski(A_74,B_75)
      | v1_xboole_0(A_74) ) ),
    inference(resolution,[status(thm)],[c_221,c_2])).

tff(c_279,plain,
    ( ~ v1_xboole_0(k2_struct_0('#skF_4'))
    | v1_xboole_0('#skF_3'('#skF_4')) ),
    inference(resolution,[status(thm)],[c_269,c_228])).

tff(c_282,plain,(
    ~ v1_xboole_0(k2_struct_0('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_279])).

tff(c_72,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_227])).

tff(c_202,plain,(
    m1_subset_1(k2_struct_0('#skF_4'),k1_zfmisc_1(k2_struct_0('#skF_4'))) ),
    inference(splitRight,[status(thm)],[c_151])).

tff(c_68,plain,(
    v2_waybel_0('#skF_5',k3_yellow_1(k2_struct_0('#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_227])).

tff(c_66,plain,(
    v13_waybel_0('#skF_5',k3_yellow_1(k2_struct_0('#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_227])).

tff(c_64,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_4'))))) ),
    inference(cnfTransformation,[status(thm)],[f_227])).

tff(c_76,plain,(
    v2_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_227])).

tff(c_24,plain,(
    ! [A_15] :
      ( m1_subset_1(k2_struct_0(A_15),k1_zfmisc_1(u1_struct_0(A_15)))
      | ~ l1_struct_0(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_424,plain,(
    ! [A_104,B_105,C_106] :
      ( v4_orders_2(k3_yellow19(A_104,B_105,C_106))
      | ~ m1_subset_1(C_106,k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_105))))
      | ~ v13_waybel_0(C_106,k3_yellow_1(B_105))
      | ~ v2_waybel_0(C_106,k3_yellow_1(B_105))
      | v1_xboole_0(C_106)
      | ~ m1_subset_1(B_105,k1_zfmisc_1(u1_struct_0(A_104)))
      | v1_xboole_0(B_105)
      | ~ l1_struct_0(A_104)
      | v2_struct_0(A_104) ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_435,plain,(
    ! [A_104] :
      ( v4_orders_2(k3_yellow19(A_104,k2_struct_0('#skF_4'),'#skF_5'))
      | ~ v13_waybel_0('#skF_5',k3_yellow_1(k2_struct_0('#skF_4')))
      | ~ v2_waybel_0('#skF_5',k3_yellow_1(k2_struct_0('#skF_4')))
      | v1_xboole_0('#skF_5')
      | ~ m1_subset_1(k2_struct_0('#skF_4'),k1_zfmisc_1(u1_struct_0(A_104)))
      | v1_xboole_0(k2_struct_0('#skF_4'))
      | ~ l1_struct_0(A_104)
      | v2_struct_0(A_104) ) ),
    inference(resolution,[status(thm)],[c_64,c_424])).

tff(c_441,plain,(
    ! [A_104] :
      ( v4_orders_2(k3_yellow19(A_104,k2_struct_0('#skF_4'),'#skF_5'))
      | v1_xboole_0('#skF_5')
      | ~ m1_subset_1(k2_struct_0('#skF_4'),k1_zfmisc_1(u1_struct_0(A_104)))
      | v1_xboole_0(k2_struct_0('#skF_4'))
      | ~ l1_struct_0(A_104)
      | v2_struct_0(A_104) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_435])).

tff(c_487,plain,(
    ! [A_111] :
      ( v4_orders_2(k3_yellow19(A_111,k2_struct_0('#skF_4'),'#skF_5'))
      | ~ m1_subset_1(k2_struct_0('#skF_4'),k1_zfmisc_1(u1_struct_0(A_111)))
      | ~ l1_struct_0(A_111)
      | v2_struct_0(A_111) ) ),
    inference(negUnitSimplification,[status(thm)],[c_282,c_72,c_441])).

tff(c_491,plain,
    ( v4_orders_2(k3_yellow19('#skF_4',k2_struct_0('#skF_4'),'#skF_5'))
    | v2_struct_0('#skF_4')
    | ~ l1_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_24,c_487])).

tff(c_500,plain,
    ( v4_orders_2(k3_yellow19('#skF_4',k2_struct_0('#skF_4'),'#skF_5'))
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_203,c_491])).

tff(c_501,plain,(
    v4_orders_2(k3_yellow19('#skF_4',k2_struct_0('#skF_4'),'#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_500])).

tff(c_1056,plain,(
    ! [A_159,B_160,C_161] :
      ( l1_waybel_0(k3_yellow19(A_159,B_160,C_161),A_159)
      | ~ m1_subset_1(C_161,k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_160))))
      | ~ v13_waybel_0(C_161,k3_yellow_1(B_160))
      | ~ v2_waybel_0(C_161,k3_yellow_1(B_160))
      | v1_xboole_0(C_161)
      | ~ m1_subset_1(B_160,k1_zfmisc_1(u1_struct_0(A_159)))
      | v1_xboole_0(B_160)
      | ~ l1_struct_0(A_159)
      | v2_struct_0(A_159) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_1067,plain,(
    ! [A_159] :
      ( l1_waybel_0(k3_yellow19(A_159,k2_struct_0('#skF_4'),'#skF_5'),A_159)
      | ~ v13_waybel_0('#skF_5',k3_yellow_1(k2_struct_0('#skF_4')))
      | ~ v2_waybel_0('#skF_5',k3_yellow_1(k2_struct_0('#skF_4')))
      | v1_xboole_0('#skF_5')
      | ~ m1_subset_1(k2_struct_0('#skF_4'),k1_zfmisc_1(u1_struct_0(A_159)))
      | v1_xboole_0(k2_struct_0('#skF_4'))
      | ~ l1_struct_0(A_159)
      | v2_struct_0(A_159) ) ),
    inference(resolution,[status(thm)],[c_64,c_1056])).

tff(c_1073,plain,(
    ! [A_159] :
      ( l1_waybel_0(k3_yellow19(A_159,k2_struct_0('#skF_4'),'#skF_5'),A_159)
      | v1_xboole_0('#skF_5')
      | ~ m1_subset_1(k2_struct_0('#skF_4'),k1_zfmisc_1(u1_struct_0(A_159)))
      | v1_xboole_0(k2_struct_0('#skF_4'))
      | ~ l1_struct_0(A_159)
      | v2_struct_0(A_159) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_1067])).

tff(c_1135,plain,(
    ! [A_167] :
      ( l1_waybel_0(k3_yellow19(A_167,k2_struct_0('#skF_4'),'#skF_5'),A_167)
      | ~ m1_subset_1(k2_struct_0('#skF_4'),k1_zfmisc_1(u1_struct_0(A_167)))
      | ~ l1_struct_0(A_167)
      | v2_struct_0(A_167) ) ),
    inference(negUnitSimplification,[status(thm)],[c_282,c_72,c_1073])).

tff(c_1138,plain,
    ( l1_waybel_0(k3_yellow19('#skF_4',k2_struct_0('#skF_4'),'#skF_5'),'#skF_4')
    | v2_struct_0('#skF_4')
    | ~ l1_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_24,c_1135])).

tff(c_1146,plain,
    ( l1_waybel_0(k3_yellow19('#skF_4',k2_struct_0('#skF_4'),'#skF_5'),'#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_203,c_1138])).

tff(c_1147,plain,(
    l1_waybel_0(k3_yellow19('#skF_4',k2_struct_0('#skF_4'),'#skF_5'),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_1146])).

tff(c_70,plain,(
    v1_subset_1('#skF_5',u1_struct_0(k3_yellow_1(k2_struct_0('#skF_4')))) ),
    inference(cnfTransformation,[status(thm)],[f_227])).

tff(c_1214,plain,(
    ! [A_174,B_175] :
      ( k2_yellow19(A_174,k3_yellow19(A_174,k2_struct_0(A_174),B_175)) = B_175
      | ~ m1_subset_1(B_175,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A_174)))))
      | ~ v13_waybel_0(B_175,k3_yellow_1(k2_struct_0(A_174)))
      | ~ v2_waybel_0(B_175,k3_yellow_1(k2_struct_0(A_174)))
      | ~ v1_subset_1(B_175,u1_struct_0(k3_yellow_1(k2_struct_0(A_174))))
      | v1_xboole_0(B_175)
      | ~ l1_struct_0(A_174)
      | v2_struct_0(A_174) ) ),
    inference(cnfTransformation,[status(thm)],[f_200])).

tff(c_1225,plain,
    ( k2_yellow19('#skF_4',k3_yellow19('#skF_4',k2_struct_0('#skF_4'),'#skF_5')) = '#skF_5'
    | ~ v13_waybel_0('#skF_5',k3_yellow_1(k2_struct_0('#skF_4')))
    | ~ v2_waybel_0('#skF_5',k3_yellow_1(k2_struct_0('#skF_4')))
    | ~ v1_subset_1('#skF_5',u1_struct_0(k3_yellow_1(k2_struct_0('#skF_4'))))
    | v1_xboole_0('#skF_5')
    | ~ l1_struct_0('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_64,c_1214])).

tff(c_1231,plain,
    ( k2_yellow19('#skF_4',k3_yellow19('#skF_4',k2_struct_0('#skF_4'),'#skF_5')) = '#skF_5'
    | v1_xboole_0('#skF_5')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_203,c_70,c_68,c_66,c_1225])).

tff(c_1232,plain,(
    k2_yellow19('#skF_4',k3_yellow19('#skF_4',k2_struct_0('#skF_4'),'#skF_5')) = '#skF_5' ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_72,c_1231])).

tff(c_58,plain,(
    ! [A_29,B_33,C_35] :
      ( r1_waybel_7(A_29,k2_yellow19(A_29,B_33),C_35)
      | ~ r3_waybel_9(A_29,B_33,C_35)
      | ~ m1_subset_1(C_35,u1_struct_0(A_29))
      | ~ l1_waybel_0(B_33,A_29)
      | ~ v7_waybel_0(B_33)
      | ~ v4_orders_2(B_33)
      | v2_struct_0(B_33)
      | ~ l1_pre_topc(A_29)
      | ~ v2_pre_topc(A_29)
      | v2_struct_0(A_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_181])).

tff(c_1236,plain,(
    ! [C_35] :
      ( r1_waybel_7('#skF_4','#skF_5',C_35)
      | ~ r3_waybel_9('#skF_4',k3_yellow19('#skF_4',k2_struct_0('#skF_4'),'#skF_5'),C_35)
      | ~ m1_subset_1(C_35,u1_struct_0('#skF_4'))
      | ~ l1_waybel_0(k3_yellow19('#skF_4',k2_struct_0('#skF_4'),'#skF_5'),'#skF_4')
      | ~ v7_waybel_0(k3_yellow19('#skF_4',k2_struct_0('#skF_4'),'#skF_5'))
      | ~ v4_orders_2(k3_yellow19('#skF_4',k2_struct_0('#skF_4'),'#skF_5'))
      | v2_struct_0(k3_yellow19('#skF_4',k2_struct_0('#skF_4'),'#skF_5'))
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1232,c_58])).

tff(c_1243,plain,(
    ! [C_35] :
      ( r1_waybel_7('#skF_4','#skF_5',C_35)
      | ~ r3_waybel_9('#skF_4',k3_yellow19('#skF_4',k2_struct_0('#skF_4'),'#skF_5'),C_35)
      | ~ m1_subset_1(C_35,k2_struct_0('#skF_4'))
      | ~ v7_waybel_0(k3_yellow19('#skF_4',k2_struct_0('#skF_4'),'#skF_5'))
      | v2_struct_0(k3_yellow19('#skF_4',k2_struct_0('#skF_4'),'#skF_5'))
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_501,c_1147,c_114,c_1236])).

tff(c_1244,plain,(
    ! [C_35] :
      ( r1_waybel_7('#skF_4','#skF_5',C_35)
      | ~ r3_waybel_9('#skF_4',k3_yellow19('#skF_4',k2_struct_0('#skF_4'),'#skF_5'),C_35)
      | ~ m1_subset_1(C_35,k2_struct_0('#skF_4'))
      | ~ v7_waybel_0(k3_yellow19('#skF_4',k2_struct_0('#skF_4'),'#skF_5'))
      | v2_struct_0(k3_yellow19('#skF_4',k2_struct_0('#skF_4'),'#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_1243])).

tff(c_1270,plain,(
    ~ v7_waybel_0(k3_yellow19('#skF_4',k2_struct_0('#skF_4'),'#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_1244])).

tff(c_1361,plain,(
    ! [A_182,B_183,C_184] :
      ( v7_waybel_0(k3_yellow19(A_182,B_183,C_184))
      | ~ m1_subset_1(C_184,k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_183))))
      | ~ v13_waybel_0(C_184,k3_yellow_1(B_183))
      | ~ v2_waybel_0(C_184,k3_yellow_1(B_183))
      | ~ v1_subset_1(C_184,u1_struct_0(k3_yellow_1(B_183)))
      | v1_xboole_0(C_184)
      | ~ m1_subset_1(B_183,k1_zfmisc_1(u1_struct_0(A_182)))
      | v1_xboole_0(B_183)
      | ~ l1_struct_0(A_182)
      | v2_struct_0(A_182) ) ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_1372,plain,(
    ! [A_182] :
      ( v7_waybel_0(k3_yellow19(A_182,k2_struct_0('#skF_4'),'#skF_5'))
      | ~ v13_waybel_0('#skF_5',k3_yellow_1(k2_struct_0('#skF_4')))
      | ~ v2_waybel_0('#skF_5',k3_yellow_1(k2_struct_0('#skF_4')))
      | ~ v1_subset_1('#skF_5',u1_struct_0(k3_yellow_1(k2_struct_0('#skF_4'))))
      | v1_xboole_0('#skF_5')
      | ~ m1_subset_1(k2_struct_0('#skF_4'),k1_zfmisc_1(u1_struct_0(A_182)))
      | v1_xboole_0(k2_struct_0('#skF_4'))
      | ~ l1_struct_0(A_182)
      | v2_struct_0(A_182) ) ),
    inference(resolution,[status(thm)],[c_64,c_1361])).

tff(c_1378,plain,(
    ! [A_182] :
      ( v7_waybel_0(k3_yellow19(A_182,k2_struct_0('#skF_4'),'#skF_5'))
      | v1_xboole_0('#skF_5')
      | ~ m1_subset_1(k2_struct_0('#skF_4'),k1_zfmisc_1(u1_struct_0(A_182)))
      | v1_xboole_0(k2_struct_0('#skF_4'))
      | ~ l1_struct_0(A_182)
      | v2_struct_0(A_182) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_66,c_1372])).

tff(c_1390,plain,(
    ! [A_185] :
      ( v7_waybel_0(k3_yellow19(A_185,k2_struct_0('#skF_4'),'#skF_5'))
      | ~ m1_subset_1(k2_struct_0('#skF_4'),k1_zfmisc_1(u1_struct_0(A_185)))
      | ~ l1_struct_0(A_185)
      | v2_struct_0(A_185) ) ),
    inference(negUnitSimplification,[status(thm)],[c_282,c_72,c_1378])).

tff(c_1394,plain,
    ( v7_waybel_0(k3_yellow19('#skF_4',k2_struct_0('#skF_4'),'#skF_5'))
    | v2_struct_0('#skF_4')
    | ~ l1_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_24,c_1390])).

tff(c_1403,plain,
    ( v7_waybel_0(k3_yellow19('#skF_4',k2_struct_0('#skF_4'),'#skF_5'))
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_203,c_1394])).

tff(c_1405,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_1270,c_1403])).

tff(c_1407,plain,(
    v7_waybel_0(k3_yellow19('#skF_4',k2_struct_0('#skF_4'),'#skF_5')) ),
    inference(splitRight,[status(thm)],[c_1244])).

tff(c_56,plain,(
    ! [A_29,B_33,C_35] :
      ( r3_waybel_9(A_29,B_33,C_35)
      | ~ r1_waybel_7(A_29,k2_yellow19(A_29,B_33),C_35)
      | ~ m1_subset_1(C_35,u1_struct_0(A_29))
      | ~ l1_waybel_0(B_33,A_29)
      | ~ v7_waybel_0(B_33)
      | ~ v4_orders_2(B_33)
      | v2_struct_0(B_33)
      | ~ l1_pre_topc(A_29)
      | ~ v2_pre_topc(A_29)
      | v2_struct_0(A_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_181])).

tff(c_1239,plain,(
    ! [C_35] :
      ( r3_waybel_9('#skF_4',k3_yellow19('#skF_4',k2_struct_0('#skF_4'),'#skF_5'),C_35)
      | ~ r1_waybel_7('#skF_4','#skF_5',C_35)
      | ~ m1_subset_1(C_35,u1_struct_0('#skF_4'))
      | ~ l1_waybel_0(k3_yellow19('#skF_4',k2_struct_0('#skF_4'),'#skF_5'),'#skF_4')
      | ~ v7_waybel_0(k3_yellow19('#skF_4',k2_struct_0('#skF_4'),'#skF_5'))
      | ~ v4_orders_2(k3_yellow19('#skF_4',k2_struct_0('#skF_4'),'#skF_5'))
      | v2_struct_0(k3_yellow19('#skF_4',k2_struct_0('#skF_4'),'#skF_5'))
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1232,c_56])).

tff(c_1246,plain,(
    ! [C_35] :
      ( r3_waybel_9('#skF_4',k3_yellow19('#skF_4',k2_struct_0('#skF_4'),'#skF_5'),C_35)
      | ~ r1_waybel_7('#skF_4','#skF_5',C_35)
      | ~ m1_subset_1(C_35,k2_struct_0('#skF_4'))
      | ~ v7_waybel_0(k3_yellow19('#skF_4',k2_struct_0('#skF_4'),'#skF_5'))
      | v2_struct_0(k3_yellow19('#skF_4',k2_struct_0('#skF_4'),'#skF_5'))
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_501,c_1147,c_114,c_1239])).

tff(c_1247,plain,(
    ! [C_35] :
      ( r3_waybel_9('#skF_4',k3_yellow19('#skF_4',k2_struct_0('#skF_4'),'#skF_5'),C_35)
      | ~ r1_waybel_7('#skF_4','#skF_5',C_35)
      | ~ m1_subset_1(C_35,k2_struct_0('#skF_4'))
      | ~ v7_waybel_0(k3_yellow19('#skF_4',k2_struct_0('#skF_4'),'#skF_5'))
      | v2_struct_0(k3_yellow19('#skF_4',k2_struct_0('#skF_4'),'#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_1246])).

tff(c_1409,plain,(
    ! [C_35] :
      ( r3_waybel_9('#skF_4',k3_yellow19('#skF_4',k2_struct_0('#skF_4'),'#skF_5'),C_35)
      | ~ r1_waybel_7('#skF_4','#skF_5',C_35)
      | ~ m1_subset_1(C_35,k2_struct_0('#skF_4'))
      | v2_struct_0(k3_yellow19('#skF_4',k2_struct_0('#skF_4'),'#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1407,c_1247])).

tff(c_1410,plain,(
    v2_struct_0(k3_yellow19('#skF_4',k2_struct_0('#skF_4'),'#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_1409])).

tff(c_48,plain,(
    ! [A_23,B_24,C_25] :
      ( ~ v2_struct_0(k3_yellow19(A_23,B_24,C_25))
      | ~ m1_subset_1(C_25,k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_24))))
      | ~ v13_waybel_0(C_25,k3_yellow_1(B_24))
      | ~ v2_waybel_0(C_25,k3_yellow_1(B_24))
      | v1_xboole_0(C_25)
      | ~ m1_subset_1(B_24,k1_zfmisc_1(u1_struct_0(A_23)))
      | v1_xboole_0(B_24)
      | ~ l1_struct_0(A_23)
      | v2_struct_0(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_1412,plain,
    ( ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_4')))))
    | ~ v13_waybel_0('#skF_5',k3_yellow_1(k2_struct_0('#skF_4')))
    | ~ v2_waybel_0('#skF_5',k3_yellow_1(k2_struct_0('#skF_4')))
    | v1_xboole_0('#skF_5')
    | ~ m1_subset_1(k2_struct_0('#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_4')))
    | v1_xboole_0(k2_struct_0('#skF_4'))
    | ~ l1_struct_0('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_1410,c_48])).

tff(c_1415,plain,
    ( v1_xboole_0('#skF_5')
    | v1_xboole_0(k2_struct_0('#skF_4'))
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_203,c_202,c_114,c_68,c_66,c_64,c_1412])).

tff(c_1417,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_282,c_72,c_1415])).

tff(c_1677,plain,(
    ! [C_201] :
      ( r3_waybel_9('#skF_4',k3_yellow19('#skF_4',k2_struct_0('#skF_4'),'#skF_5'),C_201)
      | ~ r1_waybel_7('#skF_4','#skF_5',C_201)
      | ~ m1_subset_1(C_201,k2_struct_0('#skF_4')) ) ),
    inference(splitRight,[status(thm)],[c_1409])).

tff(c_1680,plain,
    ( ~ r1_waybel_7('#skF_4','#skF_5','#skF_6')
    | ~ m1_subset_1('#skF_6',k2_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_1677,c_174])).

tff(c_1684,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_116,c_229,c_1680])).

tff(c_1685,plain,(
    v1_xboole_0('#skF_3'('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_279])).

tff(c_30,plain,(
    ! [A_17] :
      ( ~ v1_xboole_0('#skF_3'(A_17))
      | ~ l1_struct_0(A_17)
      | v2_struct_0(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_1696,plain,
    ( ~ l1_struct_0('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_1685,c_30])).

tff(c_1700,plain,(
    v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_203,c_1696])).

tff(c_1702,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_1700])).

tff(c_1703,plain,(
    ~ r1_waybel_7('#skF_4','#skF_5','#skF_6') ),
    inference(splitRight,[status(thm)],[c_80])).

tff(c_1723,plain,(
    r3_waybel_9('#skF_4',k3_yellow19('#skF_4',k2_struct_0('#skF_4'),'#skF_5'),'#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_1703,c_86])).

tff(c_1786,plain,(
    ! [A_217] :
      ( m1_subset_1('#skF_3'(A_217),k1_zfmisc_1(u1_struct_0(A_217)))
      | ~ l1_struct_0(A_217)
      | v2_struct_0(A_217) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_1792,plain,
    ( m1_subset_1('#skF_3'('#skF_4'),k1_zfmisc_1(k2_struct_0('#skF_4')))
    | ~ l1_struct_0('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_114,c_1786])).

tff(c_1795,plain,
    ( m1_subset_1('#skF_3'('#skF_4'),k1_zfmisc_1(k2_struct_0('#skF_4')))
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1735,c_1792])).

tff(c_1796,plain,(
    m1_subset_1('#skF_3'('#skF_4'),k1_zfmisc_1(k2_struct_0('#skF_4'))) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_1795])).

tff(c_1800,plain,(
    r1_tarski('#skF_3'('#skF_4'),k2_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_1796,c_18])).

tff(c_1741,plain,(
    ! [C_209,B_210,A_211] :
      ( r2_hidden(C_209,B_210)
      | ~ r2_hidden(C_209,A_211)
      | ~ r1_tarski(A_211,B_210) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_1753,plain,(
    ! [A_212,B_213] :
      ( r2_hidden('#skF_1'(A_212),B_213)
      | ~ r1_tarski(A_212,B_213)
      | v1_xboole_0(A_212) ) ),
    inference(resolution,[status(thm)],[c_4,c_1741])).

tff(c_1760,plain,(
    ! [B_213,A_212] :
      ( ~ v1_xboole_0(B_213)
      | ~ r1_tarski(A_212,B_213)
      | v1_xboole_0(A_212) ) ),
    inference(resolution,[status(thm)],[c_1753,c_2])).

tff(c_1809,plain,
    ( ~ v1_xboole_0(k2_struct_0('#skF_4'))
    | v1_xboole_0('#skF_3'('#skF_4')) ),
    inference(resolution,[status(thm)],[c_1800,c_1760])).

tff(c_1812,plain,(
    ~ v1_xboole_0(k2_struct_0('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_1809])).

tff(c_1734,plain,(
    m1_subset_1(k2_struct_0('#skF_4'),k1_zfmisc_1(k2_struct_0('#skF_4'))) ),
    inference(splitRight,[status(thm)],[c_151])).

tff(c_2115,plain,(
    ! [A_261,B_262,C_263] :
      ( v4_orders_2(k3_yellow19(A_261,B_262,C_263))
      | ~ m1_subset_1(C_263,k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_262))))
      | ~ v13_waybel_0(C_263,k3_yellow_1(B_262))
      | ~ v2_waybel_0(C_263,k3_yellow_1(B_262))
      | v1_xboole_0(C_263)
      | ~ m1_subset_1(B_262,k1_zfmisc_1(u1_struct_0(A_261)))
      | v1_xboole_0(B_262)
      | ~ l1_struct_0(A_261)
      | v2_struct_0(A_261) ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_2126,plain,(
    ! [A_261] :
      ( v4_orders_2(k3_yellow19(A_261,k2_struct_0('#skF_4'),'#skF_5'))
      | ~ v13_waybel_0('#skF_5',k3_yellow_1(k2_struct_0('#skF_4')))
      | ~ v2_waybel_0('#skF_5',k3_yellow_1(k2_struct_0('#skF_4')))
      | v1_xboole_0('#skF_5')
      | ~ m1_subset_1(k2_struct_0('#skF_4'),k1_zfmisc_1(u1_struct_0(A_261)))
      | v1_xboole_0(k2_struct_0('#skF_4'))
      | ~ l1_struct_0(A_261)
      | v2_struct_0(A_261) ) ),
    inference(resolution,[status(thm)],[c_64,c_2115])).

tff(c_2132,plain,(
    ! [A_261] :
      ( v4_orders_2(k3_yellow19(A_261,k2_struct_0('#skF_4'),'#skF_5'))
      | v1_xboole_0('#skF_5')
      | ~ m1_subset_1(k2_struct_0('#skF_4'),k1_zfmisc_1(u1_struct_0(A_261)))
      | v1_xboole_0(k2_struct_0('#skF_4'))
      | ~ l1_struct_0(A_261)
      | v2_struct_0(A_261) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_2126])).

tff(c_2205,plain,(
    ! [A_268] :
      ( v4_orders_2(k3_yellow19(A_268,k2_struct_0('#skF_4'),'#skF_5'))
      | ~ m1_subset_1(k2_struct_0('#skF_4'),k1_zfmisc_1(u1_struct_0(A_268)))
      | ~ l1_struct_0(A_268)
      | v2_struct_0(A_268) ) ),
    inference(negUnitSimplification,[status(thm)],[c_1812,c_72,c_2132])).

tff(c_2209,plain,
    ( v4_orders_2(k3_yellow19('#skF_4',k2_struct_0('#skF_4'),'#skF_5'))
    | v2_struct_0('#skF_4')
    | ~ l1_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_24,c_2205])).

tff(c_2218,plain,
    ( v4_orders_2(k3_yellow19('#skF_4',k2_struct_0('#skF_4'),'#skF_5'))
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1735,c_2209])).

tff(c_2219,plain,(
    v4_orders_2(k3_yellow19('#skF_4',k2_struct_0('#skF_4'),'#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_2218])).

tff(c_2424,plain,(
    ! [A_286,B_287,C_288] :
      ( l1_waybel_0(k3_yellow19(A_286,B_287,C_288),A_286)
      | ~ m1_subset_1(C_288,k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_287))))
      | ~ v13_waybel_0(C_288,k3_yellow_1(B_287))
      | ~ v2_waybel_0(C_288,k3_yellow_1(B_287))
      | v1_xboole_0(C_288)
      | ~ m1_subset_1(B_287,k1_zfmisc_1(u1_struct_0(A_286)))
      | v1_xboole_0(B_287)
      | ~ l1_struct_0(A_286)
      | v2_struct_0(A_286) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_2435,plain,(
    ! [A_286] :
      ( l1_waybel_0(k3_yellow19(A_286,k2_struct_0('#skF_4'),'#skF_5'),A_286)
      | ~ v13_waybel_0('#skF_5',k3_yellow_1(k2_struct_0('#skF_4')))
      | ~ v2_waybel_0('#skF_5',k3_yellow_1(k2_struct_0('#skF_4')))
      | v1_xboole_0('#skF_5')
      | ~ m1_subset_1(k2_struct_0('#skF_4'),k1_zfmisc_1(u1_struct_0(A_286)))
      | v1_xboole_0(k2_struct_0('#skF_4'))
      | ~ l1_struct_0(A_286)
      | v2_struct_0(A_286) ) ),
    inference(resolution,[status(thm)],[c_64,c_2424])).

tff(c_2441,plain,(
    ! [A_286] :
      ( l1_waybel_0(k3_yellow19(A_286,k2_struct_0('#skF_4'),'#skF_5'),A_286)
      | v1_xboole_0('#skF_5')
      | ~ m1_subset_1(k2_struct_0('#skF_4'),k1_zfmisc_1(u1_struct_0(A_286)))
      | v1_xboole_0(k2_struct_0('#skF_4'))
      | ~ l1_struct_0(A_286)
      | v2_struct_0(A_286) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_2435])).

tff(c_2508,plain,(
    ! [A_294] :
      ( l1_waybel_0(k3_yellow19(A_294,k2_struct_0('#skF_4'),'#skF_5'),A_294)
      | ~ m1_subset_1(k2_struct_0('#skF_4'),k1_zfmisc_1(u1_struct_0(A_294)))
      | ~ l1_struct_0(A_294)
      | v2_struct_0(A_294) ) ),
    inference(negUnitSimplification,[status(thm)],[c_1812,c_72,c_2441])).

tff(c_2511,plain,
    ( l1_waybel_0(k3_yellow19('#skF_4',k2_struct_0('#skF_4'),'#skF_5'),'#skF_4')
    | v2_struct_0('#skF_4')
    | ~ l1_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_24,c_2508])).

tff(c_2519,plain,
    ( l1_waybel_0(k3_yellow19('#skF_4',k2_struct_0('#skF_4'),'#skF_5'),'#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1735,c_2511])).

tff(c_2520,plain,(
    l1_waybel_0(k3_yellow19('#skF_4',k2_struct_0('#skF_4'),'#skF_5'),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_2519])).

tff(c_2766,plain,(
    ! [A_314,B_315] :
      ( k2_yellow19(A_314,k3_yellow19(A_314,k2_struct_0(A_314),B_315)) = B_315
      | ~ m1_subset_1(B_315,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A_314)))))
      | ~ v13_waybel_0(B_315,k3_yellow_1(k2_struct_0(A_314)))
      | ~ v2_waybel_0(B_315,k3_yellow_1(k2_struct_0(A_314)))
      | ~ v1_subset_1(B_315,u1_struct_0(k3_yellow_1(k2_struct_0(A_314))))
      | v1_xboole_0(B_315)
      | ~ l1_struct_0(A_314)
      | v2_struct_0(A_314) ) ),
    inference(cnfTransformation,[status(thm)],[f_200])).

tff(c_2777,plain,
    ( k2_yellow19('#skF_4',k3_yellow19('#skF_4',k2_struct_0('#skF_4'),'#skF_5')) = '#skF_5'
    | ~ v13_waybel_0('#skF_5',k3_yellow_1(k2_struct_0('#skF_4')))
    | ~ v2_waybel_0('#skF_5',k3_yellow_1(k2_struct_0('#skF_4')))
    | ~ v1_subset_1('#skF_5',u1_struct_0(k3_yellow_1(k2_struct_0('#skF_4'))))
    | v1_xboole_0('#skF_5')
    | ~ l1_struct_0('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_64,c_2766])).

tff(c_2783,plain,
    ( k2_yellow19('#skF_4',k3_yellow19('#skF_4',k2_struct_0('#skF_4'),'#skF_5')) = '#skF_5'
    | v1_xboole_0('#skF_5')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1735,c_70,c_68,c_66,c_2777])).

tff(c_2784,plain,(
    k2_yellow19('#skF_4',k3_yellow19('#skF_4',k2_struct_0('#skF_4'),'#skF_5')) = '#skF_5' ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_72,c_2783])).

tff(c_2791,plain,(
    ! [C_35] :
      ( r3_waybel_9('#skF_4',k3_yellow19('#skF_4',k2_struct_0('#skF_4'),'#skF_5'),C_35)
      | ~ r1_waybel_7('#skF_4','#skF_5',C_35)
      | ~ m1_subset_1(C_35,u1_struct_0('#skF_4'))
      | ~ l1_waybel_0(k3_yellow19('#skF_4',k2_struct_0('#skF_4'),'#skF_5'),'#skF_4')
      | ~ v7_waybel_0(k3_yellow19('#skF_4',k2_struct_0('#skF_4'),'#skF_5'))
      | ~ v4_orders_2(k3_yellow19('#skF_4',k2_struct_0('#skF_4'),'#skF_5'))
      | v2_struct_0(k3_yellow19('#skF_4',k2_struct_0('#skF_4'),'#skF_5'))
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2784,c_56])).

tff(c_2798,plain,(
    ! [C_35] :
      ( r3_waybel_9('#skF_4',k3_yellow19('#skF_4',k2_struct_0('#skF_4'),'#skF_5'),C_35)
      | ~ r1_waybel_7('#skF_4','#skF_5',C_35)
      | ~ m1_subset_1(C_35,k2_struct_0('#skF_4'))
      | ~ v7_waybel_0(k3_yellow19('#skF_4',k2_struct_0('#skF_4'),'#skF_5'))
      | v2_struct_0(k3_yellow19('#skF_4',k2_struct_0('#skF_4'),'#skF_5'))
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_2219,c_2520,c_114,c_2791])).

tff(c_2799,plain,(
    ! [C_35] :
      ( r3_waybel_9('#skF_4',k3_yellow19('#skF_4',k2_struct_0('#skF_4'),'#skF_5'),C_35)
      | ~ r1_waybel_7('#skF_4','#skF_5',C_35)
      | ~ m1_subset_1(C_35,k2_struct_0('#skF_4'))
      | ~ v7_waybel_0(k3_yellow19('#skF_4',k2_struct_0('#skF_4'),'#skF_5'))
      | v2_struct_0(k3_yellow19('#skF_4',k2_struct_0('#skF_4'),'#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_2798])).

tff(c_2863,plain,(
    ~ v7_waybel_0(k3_yellow19('#skF_4',k2_struct_0('#skF_4'),'#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_2799])).

tff(c_2903,plain,(
    ! [A_321,B_322,C_323] :
      ( v7_waybel_0(k3_yellow19(A_321,B_322,C_323))
      | ~ m1_subset_1(C_323,k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_322))))
      | ~ v13_waybel_0(C_323,k3_yellow_1(B_322))
      | ~ v2_waybel_0(C_323,k3_yellow_1(B_322))
      | ~ v1_subset_1(C_323,u1_struct_0(k3_yellow_1(B_322)))
      | v1_xboole_0(C_323)
      | ~ m1_subset_1(B_322,k1_zfmisc_1(u1_struct_0(A_321)))
      | v1_xboole_0(B_322)
      | ~ l1_struct_0(A_321)
      | v2_struct_0(A_321) ) ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_2914,plain,(
    ! [A_321] :
      ( v7_waybel_0(k3_yellow19(A_321,k2_struct_0('#skF_4'),'#skF_5'))
      | ~ v13_waybel_0('#skF_5',k3_yellow_1(k2_struct_0('#skF_4')))
      | ~ v2_waybel_0('#skF_5',k3_yellow_1(k2_struct_0('#skF_4')))
      | ~ v1_subset_1('#skF_5',u1_struct_0(k3_yellow_1(k2_struct_0('#skF_4'))))
      | v1_xboole_0('#skF_5')
      | ~ m1_subset_1(k2_struct_0('#skF_4'),k1_zfmisc_1(u1_struct_0(A_321)))
      | v1_xboole_0(k2_struct_0('#skF_4'))
      | ~ l1_struct_0(A_321)
      | v2_struct_0(A_321) ) ),
    inference(resolution,[status(thm)],[c_64,c_2903])).

tff(c_2920,plain,(
    ! [A_321] :
      ( v7_waybel_0(k3_yellow19(A_321,k2_struct_0('#skF_4'),'#skF_5'))
      | v1_xboole_0('#skF_5')
      | ~ m1_subset_1(k2_struct_0('#skF_4'),k1_zfmisc_1(u1_struct_0(A_321)))
      | v1_xboole_0(k2_struct_0('#skF_4'))
      | ~ l1_struct_0(A_321)
      | v2_struct_0(A_321) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_66,c_2914])).

tff(c_2922,plain,(
    ! [A_324] :
      ( v7_waybel_0(k3_yellow19(A_324,k2_struct_0('#skF_4'),'#skF_5'))
      | ~ m1_subset_1(k2_struct_0('#skF_4'),k1_zfmisc_1(u1_struct_0(A_324)))
      | ~ l1_struct_0(A_324)
      | v2_struct_0(A_324) ) ),
    inference(negUnitSimplification,[status(thm)],[c_1812,c_72,c_2920])).

tff(c_2926,plain,
    ( v7_waybel_0(k3_yellow19('#skF_4',k2_struct_0('#skF_4'),'#skF_5'))
    | v2_struct_0('#skF_4')
    | ~ l1_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_24,c_2922])).

tff(c_2935,plain,
    ( v7_waybel_0(k3_yellow19('#skF_4',k2_struct_0('#skF_4'),'#skF_5'))
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1735,c_2926])).

tff(c_2937,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_2863,c_2935])).

tff(c_2939,plain,(
    v7_waybel_0(k3_yellow19('#skF_4',k2_struct_0('#skF_4'),'#skF_5')) ),
    inference(splitRight,[status(thm)],[c_2799])).

tff(c_2788,plain,(
    ! [C_35] :
      ( r1_waybel_7('#skF_4','#skF_5',C_35)
      | ~ r3_waybel_9('#skF_4',k3_yellow19('#skF_4',k2_struct_0('#skF_4'),'#skF_5'),C_35)
      | ~ m1_subset_1(C_35,u1_struct_0('#skF_4'))
      | ~ l1_waybel_0(k3_yellow19('#skF_4',k2_struct_0('#skF_4'),'#skF_5'),'#skF_4')
      | ~ v7_waybel_0(k3_yellow19('#skF_4',k2_struct_0('#skF_4'),'#skF_5'))
      | ~ v4_orders_2(k3_yellow19('#skF_4',k2_struct_0('#skF_4'),'#skF_5'))
      | v2_struct_0(k3_yellow19('#skF_4',k2_struct_0('#skF_4'),'#skF_5'))
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2784,c_58])).

tff(c_2795,plain,(
    ! [C_35] :
      ( r1_waybel_7('#skF_4','#skF_5',C_35)
      | ~ r3_waybel_9('#skF_4',k3_yellow19('#skF_4',k2_struct_0('#skF_4'),'#skF_5'),C_35)
      | ~ m1_subset_1(C_35,k2_struct_0('#skF_4'))
      | ~ v7_waybel_0(k3_yellow19('#skF_4',k2_struct_0('#skF_4'),'#skF_5'))
      | v2_struct_0(k3_yellow19('#skF_4',k2_struct_0('#skF_4'),'#skF_5'))
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_2219,c_2520,c_114,c_2788])).

tff(c_2796,plain,(
    ! [C_35] :
      ( r1_waybel_7('#skF_4','#skF_5',C_35)
      | ~ r3_waybel_9('#skF_4',k3_yellow19('#skF_4',k2_struct_0('#skF_4'),'#skF_5'),C_35)
      | ~ m1_subset_1(C_35,k2_struct_0('#skF_4'))
      | ~ v7_waybel_0(k3_yellow19('#skF_4',k2_struct_0('#skF_4'),'#skF_5'))
      | v2_struct_0(k3_yellow19('#skF_4',k2_struct_0('#skF_4'),'#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_2795])).

tff(c_2968,plain,(
    ! [C_35] :
      ( r1_waybel_7('#skF_4','#skF_5',C_35)
      | ~ r3_waybel_9('#skF_4',k3_yellow19('#skF_4',k2_struct_0('#skF_4'),'#skF_5'),C_35)
      | ~ m1_subset_1(C_35,k2_struct_0('#skF_4'))
      | v2_struct_0(k3_yellow19('#skF_4',k2_struct_0('#skF_4'),'#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2939,c_2796])).

tff(c_2969,plain,(
    v2_struct_0(k3_yellow19('#skF_4',k2_struct_0('#skF_4'),'#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_2968])).

tff(c_2971,plain,
    ( ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_4')))))
    | ~ v13_waybel_0('#skF_5',k3_yellow_1(k2_struct_0('#skF_4')))
    | ~ v2_waybel_0('#skF_5',k3_yellow_1(k2_struct_0('#skF_4')))
    | v1_xboole_0('#skF_5')
    | ~ m1_subset_1(k2_struct_0('#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_4')))
    | v1_xboole_0(k2_struct_0('#skF_4'))
    | ~ l1_struct_0('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_2969,c_48])).

tff(c_2974,plain,
    ( v1_xboole_0('#skF_5')
    | v1_xboole_0(k2_struct_0('#skF_4'))
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1735,c_1734,c_114,c_68,c_66,c_64,c_2971])).

tff(c_2976,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_1812,c_72,c_2974])).

tff(c_3147,plain,(
    ! [C_337] :
      ( r1_waybel_7('#skF_4','#skF_5',C_337)
      | ~ r3_waybel_9('#skF_4',k3_yellow19('#skF_4',k2_struct_0('#skF_4'),'#skF_5'),C_337)
      | ~ m1_subset_1(C_337,k2_struct_0('#skF_4')) ) ),
    inference(splitRight,[status(thm)],[c_2968])).

tff(c_3150,plain,
    ( r1_waybel_7('#skF_4','#skF_5','#skF_6')
    | ~ m1_subset_1('#skF_6',k2_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_1723,c_3147])).

tff(c_3153,plain,(
    r1_waybel_7('#skF_4','#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_116,c_3150])).

tff(c_3155,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1703,c_3153])).

tff(c_3156,plain,(
    v1_xboole_0('#skF_3'('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_1809])).

tff(c_3162,plain,
    ( ~ l1_struct_0('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_3156,c_30])).

tff(c_3166,plain,(
    v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1735,c_3162])).

tff(c_3168,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_3166])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n018.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 19:13:12 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.54/2.13  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.54/2.15  
% 5.54/2.15  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.54/2.16  %$ r3_waybel_9 > r1_waybel_7 > v6_waybel_0 > v2_waybel_0 > v1_subset_1 > v13_waybel_0 > r2_hidden > r1_tarski > m1_subset_1 > l1_waybel_0 > v7_waybel_0 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v2_pre_topc > v1_zfmisc_1 > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k3_yellow19 > k2_yellow19 > #nlpp > u1_struct_0 > k3_yellow_1 > k3_lattice3 > k2_struct_0 > k1_zfmisc_1 > k1_lattice3 > #skF_1 > #skF_5 > #skF_6 > #skF_4 > #skF_3 > #skF_2
% 5.54/2.16  
% 5.54/2.16  %Foreground sorts:
% 5.54/2.16  
% 5.54/2.16  
% 5.54/2.16  %Background operators:
% 5.54/2.16  
% 5.54/2.16  
% 5.54/2.16  %Foreground operators:
% 5.54/2.16  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 5.54/2.16  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 5.54/2.16  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.54/2.16  tff(k3_lattice3, type, k3_lattice3: $i > $i).
% 5.54/2.16  tff(v6_waybel_0, type, v6_waybel_0: ($i * $i) > $o).
% 5.54/2.16  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.54/2.16  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 5.54/2.16  tff(k3_yellow_1, type, k3_yellow_1: $i > $i).
% 5.54/2.16  tff('#skF_1', type, '#skF_1': $i > $i).
% 5.54/2.16  tff(v2_waybel_0, type, v2_waybel_0: ($i * $i) > $o).
% 5.54/2.16  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 5.54/2.16  tff(v7_waybel_0, type, v7_waybel_0: $i > $o).
% 5.54/2.16  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.54/2.16  tff('#skF_5', type, '#skF_5': $i).
% 5.54/2.16  tff(r3_waybel_9, type, r3_waybel_9: ($i * $i * $i) > $o).
% 5.54/2.16  tff('#skF_6', type, '#skF_6': $i).
% 5.54/2.16  tff(k1_lattice3, type, k1_lattice3: $i > $i).
% 5.54/2.16  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 5.54/2.16  tff(r1_waybel_7, type, r1_waybel_7: ($i * $i * $i) > $o).
% 5.54/2.16  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.54/2.16  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 5.54/2.16  tff(k2_yellow19, type, k2_yellow19: ($i * $i) > $i).
% 5.54/2.16  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.54/2.16  tff(l1_waybel_0, type, l1_waybel_0: ($i * $i) > $o).
% 5.54/2.16  tff('#skF_4', type, '#skF_4': $i).
% 5.54/2.16  tff('#skF_3', type, '#skF_3': $i > $i).
% 5.54/2.16  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.54/2.16  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 5.54/2.16  tff(v1_zfmisc_1, type, v1_zfmisc_1: $i > $o).
% 5.54/2.16  tff(k3_yellow19, type, k3_yellow19: ($i * $i * $i) > $i).
% 5.54/2.16  tff(v13_waybel_0, type, v13_waybel_0: ($i * $i) > $o).
% 5.54/2.16  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 5.54/2.16  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 5.54/2.16  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 5.54/2.16  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 5.54/2.16  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.54/2.16  
% 5.54/2.18  tff(f_227, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((((~v1_xboole_0(B) & v1_subset_1(B, u1_struct_0(k3_yellow_1(k2_struct_0(A))))) & v2_waybel_0(B, k3_yellow_1(k2_struct_0(A)))) & v13_waybel_0(B, k3_yellow_1(k2_struct_0(A)))) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A)))))) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r3_waybel_9(A, k3_yellow19(A, k2_struct_0(A), B), C) <=> r1_waybel_7(A, B, C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_yellow19)).
% 5.54/2.18  tff(f_60, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 5.54/2.18  tff(f_52, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_struct_0)).
% 5.54/2.18  tff(f_56, axiom, (![A]: (l1_struct_0(A) => m1_subset_1(k2_struct_0(A), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_struct_0)).
% 5.54/2.18  tff(f_73, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => (?[B]: ((m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) & ~v1_xboole_0(B)) & v1_zfmisc_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', rc20_struct_0)).
% 5.54/2.18  tff(f_48, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 5.54/2.18  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 5.54/2.18  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 5.54/2.18  tff(f_129, axiom, (![A, B, C]: ((((((((~v2_struct_0(A) & l1_struct_0(A)) & ~v1_xboole_0(B)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) & ~v1_xboole_0(C)) & v2_waybel_0(C, k3_yellow_1(B))) & v13_waybel_0(C, k3_yellow_1(B))) & m1_subset_1(C, k1_zfmisc_1(u1_struct_0(k3_yellow_1(B))))) => (((~v2_struct_0(k3_yellow19(A, B, C)) & v3_orders_2(k3_yellow19(A, B, C))) & v4_orders_2(k3_yellow19(A, B, C))) & v6_waybel_0(k3_yellow19(A, B, C), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc4_yellow19)).
% 5.54/2.18  tff(f_101, axiom, (![A, B, C]: ((((((((~v2_struct_0(A) & l1_struct_0(A)) & ~v1_xboole_0(B)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) & ~v1_xboole_0(C)) & v2_waybel_0(C, k3_yellow_1(B))) & v13_waybel_0(C, k3_yellow_1(B))) & m1_subset_1(C, k1_zfmisc_1(u1_struct_0(k3_yellow_1(B))))) => ((~v2_struct_0(k3_yellow19(A, B, C)) & v6_waybel_0(k3_yellow19(A, B, C), A)) & l1_waybel_0(k3_yellow19(A, B, C), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k3_yellow19)).
% 5.54/2.18  tff(f_200, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => (![B]: (((((~v1_xboole_0(B) & v1_subset_1(B, u1_struct_0(k3_yellow_1(k2_struct_0(A))))) & v2_waybel_0(B, k3_yellow_1(k2_struct_0(A)))) & v13_waybel_0(B, k3_yellow_1(k2_struct_0(A)))) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A)))))) => (B = k2_yellow19(A, k3_yellow19(A, k2_struct_0(A), B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t15_yellow19)).
% 5.54/2.18  tff(f_181, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((((~v2_struct_0(B) & v4_orders_2(B)) & v7_waybel_0(B)) & l1_waybel_0(B, A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r3_waybel_9(A, B, C) <=> r1_waybel_7(A, k2_yellow19(A, B), C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_yellow19)).
% 5.54/2.18  tff(f_157, axiom, (![A, B, C]: (((((((((~v2_struct_0(A) & l1_struct_0(A)) & ~v1_xboole_0(B)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) & ~v1_xboole_0(C)) & v1_subset_1(C, u1_struct_0(k3_yellow_1(B)))) & v2_waybel_0(C, k3_yellow_1(B))) & v13_waybel_0(C, k3_yellow_1(B))) & m1_subset_1(C, k1_zfmisc_1(u1_struct_0(k3_yellow_1(B))))) => ((~v2_struct_0(k3_yellow19(A, B, C)) & v6_waybel_0(k3_yellow19(A, B, C), A)) & v7_waybel_0(k3_yellow19(A, B, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc5_yellow19)).
% 5.54/2.18  tff(c_78, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_227])).
% 5.54/2.18  tff(c_74, plain, (l1_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_227])).
% 5.54/2.18  tff(c_26, plain, (![A_16]: (l1_struct_0(A_16) | ~l1_pre_topc(A_16))), inference(cnfTransformation, [status(thm)], [f_60])).
% 5.54/2.18  tff(c_100, plain, (![A_48]: (u1_struct_0(A_48)=k2_struct_0(A_48) | ~l1_struct_0(A_48))), inference(cnfTransformation, [status(thm)], [f_52])).
% 5.54/2.18  tff(c_110, plain, (![A_50]: (u1_struct_0(A_50)=k2_struct_0(A_50) | ~l1_pre_topc(A_50))), inference(resolution, [status(thm)], [c_26, c_100])).
% 5.54/2.18  tff(c_114, plain, (u1_struct_0('#skF_4')=k2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_74, c_110])).
% 5.54/2.18  tff(c_145, plain, (![A_63]: (m1_subset_1(k2_struct_0(A_63), k1_zfmisc_1(u1_struct_0(A_63))) | ~l1_struct_0(A_63))), inference(cnfTransformation, [status(thm)], [f_56])).
% 5.54/2.18  tff(c_151, plain, (m1_subset_1(k2_struct_0('#skF_4'), k1_zfmisc_1(k2_struct_0('#skF_4'))) | ~l1_struct_0('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_114, c_145])).
% 5.54/2.18  tff(c_1726, plain, (~l1_struct_0('#skF_4')), inference(splitLeft, [status(thm)], [c_151])).
% 5.54/2.18  tff(c_1729, plain, (~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_26, c_1726])).
% 5.54/2.18  tff(c_1733, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_74, c_1729])).
% 5.54/2.18  tff(c_1735, plain, (l1_struct_0('#skF_4')), inference(splitRight, [status(thm)], [c_151])).
% 5.54/2.18  tff(c_194, plain, (~l1_struct_0('#skF_4')), inference(splitLeft, [status(thm)], [c_151])).
% 5.54/2.18  tff(c_197, plain, (~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_26, c_194])).
% 5.54/2.18  tff(c_201, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_74, c_197])).
% 5.54/2.18  tff(c_203, plain, (l1_struct_0('#skF_4')), inference(splitRight, [status(thm)], [c_151])).
% 5.54/2.18  tff(c_62, plain, (m1_subset_1('#skF_6', u1_struct_0('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_227])).
% 5.54/2.18  tff(c_116, plain, (m1_subset_1('#skF_6', k2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_114, c_62])).
% 5.54/2.18  tff(c_80, plain, (~r1_waybel_7('#skF_4', '#skF_5', '#skF_6') | ~r3_waybel_9('#skF_4', k3_yellow19('#skF_4', k2_struct_0('#skF_4'), '#skF_5'), '#skF_6')), inference(cnfTransformation, [status(thm)], [f_227])).
% 5.54/2.18  tff(c_174, plain, (~r3_waybel_9('#skF_4', k3_yellow19('#skF_4', k2_struct_0('#skF_4'), '#skF_5'), '#skF_6')), inference(splitLeft, [status(thm)], [c_80])).
% 5.54/2.18  tff(c_86, plain, (r3_waybel_9('#skF_4', k3_yellow19('#skF_4', k2_struct_0('#skF_4'), '#skF_5'), '#skF_6') | r1_waybel_7('#skF_4', '#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_227])).
% 5.54/2.18  tff(c_229, plain, (r1_waybel_7('#skF_4', '#skF_5', '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_174, c_86])).
% 5.54/2.18  tff(c_255, plain, (![A_79]: (m1_subset_1('#skF_3'(A_79), k1_zfmisc_1(u1_struct_0(A_79))) | ~l1_struct_0(A_79) | v2_struct_0(A_79))), inference(cnfTransformation, [status(thm)], [f_73])).
% 5.54/2.18  tff(c_261, plain, (m1_subset_1('#skF_3'('#skF_4'), k1_zfmisc_1(k2_struct_0('#skF_4'))) | ~l1_struct_0('#skF_4') | v2_struct_0('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_114, c_255])).
% 5.54/2.18  tff(c_264, plain, (m1_subset_1('#skF_3'('#skF_4'), k1_zfmisc_1(k2_struct_0('#skF_4'))) | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_203, c_261])).
% 5.54/2.18  tff(c_265, plain, (m1_subset_1('#skF_3'('#skF_4'), k1_zfmisc_1(k2_struct_0('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_78, c_264])).
% 5.54/2.18  tff(c_18, plain, (![A_12, B_13]: (r1_tarski(A_12, B_13) | ~m1_subset_1(A_12, k1_zfmisc_1(B_13)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 5.54/2.18  tff(c_269, plain, (r1_tarski('#skF_3'('#skF_4'), k2_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_265, c_18])).
% 5.54/2.18  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.54/2.18  tff(c_204, plain, (![C_71, B_72, A_73]: (r2_hidden(C_71, B_72) | ~r2_hidden(C_71, A_73) | ~r1_tarski(A_73, B_72))), inference(cnfTransformation, [status(thm)], [f_38])).
% 5.54/2.18  tff(c_221, plain, (![A_74, B_75]: (r2_hidden('#skF_1'(A_74), B_75) | ~r1_tarski(A_74, B_75) | v1_xboole_0(A_74))), inference(resolution, [status(thm)], [c_4, c_204])).
% 5.54/2.18  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.54/2.18  tff(c_228, plain, (![B_75, A_74]: (~v1_xboole_0(B_75) | ~r1_tarski(A_74, B_75) | v1_xboole_0(A_74))), inference(resolution, [status(thm)], [c_221, c_2])).
% 5.54/2.18  tff(c_279, plain, (~v1_xboole_0(k2_struct_0('#skF_4')) | v1_xboole_0('#skF_3'('#skF_4'))), inference(resolution, [status(thm)], [c_269, c_228])).
% 5.54/2.18  tff(c_282, plain, (~v1_xboole_0(k2_struct_0('#skF_4'))), inference(splitLeft, [status(thm)], [c_279])).
% 5.54/2.18  tff(c_72, plain, (~v1_xboole_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_227])).
% 5.54/2.18  tff(c_202, plain, (m1_subset_1(k2_struct_0('#skF_4'), k1_zfmisc_1(k2_struct_0('#skF_4')))), inference(splitRight, [status(thm)], [c_151])).
% 5.54/2.18  tff(c_68, plain, (v2_waybel_0('#skF_5', k3_yellow_1(k2_struct_0('#skF_4')))), inference(cnfTransformation, [status(thm)], [f_227])).
% 5.54/2.18  tff(c_66, plain, (v13_waybel_0('#skF_5', k3_yellow_1(k2_struct_0('#skF_4')))), inference(cnfTransformation, [status(thm)], [f_227])).
% 5.54/2.18  tff(c_64, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_4')))))), inference(cnfTransformation, [status(thm)], [f_227])).
% 5.54/2.18  tff(c_76, plain, (v2_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_227])).
% 5.54/2.18  tff(c_24, plain, (![A_15]: (m1_subset_1(k2_struct_0(A_15), k1_zfmisc_1(u1_struct_0(A_15))) | ~l1_struct_0(A_15))), inference(cnfTransformation, [status(thm)], [f_56])).
% 5.54/2.18  tff(c_424, plain, (![A_104, B_105, C_106]: (v4_orders_2(k3_yellow19(A_104, B_105, C_106)) | ~m1_subset_1(C_106, k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_105)))) | ~v13_waybel_0(C_106, k3_yellow_1(B_105)) | ~v2_waybel_0(C_106, k3_yellow_1(B_105)) | v1_xboole_0(C_106) | ~m1_subset_1(B_105, k1_zfmisc_1(u1_struct_0(A_104))) | v1_xboole_0(B_105) | ~l1_struct_0(A_104) | v2_struct_0(A_104))), inference(cnfTransformation, [status(thm)], [f_129])).
% 5.54/2.18  tff(c_435, plain, (![A_104]: (v4_orders_2(k3_yellow19(A_104, k2_struct_0('#skF_4'), '#skF_5')) | ~v13_waybel_0('#skF_5', k3_yellow_1(k2_struct_0('#skF_4'))) | ~v2_waybel_0('#skF_5', k3_yellow_1(k2_struct_0('#skF_4'))) | v1_xboole_0('#skF_5') | ~m1_subset_1(k2_struct_0('#skF_4'), k1_zfmisc_1(u1_struct_0(A_104))) | v1_xboole_0(k2_struct_0('#skF_4')) | ~l1_struct_0(A_104) | v2_struct_0(A_104))), inference(resolution, [status(thm)], [c_64, c_424])).
% 5.54/2.18  tff(c_441, plain, (![A_104]: (v4_orders_2(k3_yellow19(A_104, k2_struct_0('#skF_4'), '#skF_5')) | v1_xboole_0('#skF_5') | ~m1_subset_1(k2_struct_0('#skF_4'), k1_zfmisc_1(u1_struct_0(A_104))) | v1_xboole_0(k2_struct_0('#skF_4')) | ~l1_struct_0(A_104) | v2_struct_0(A_104))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_66, c_435])).
% 5.54/2.18  tff(c_487, plain, (![A_111]: (v4_orders_2(k3_yellow19(A_111, k2_struct_0('#skF_4'), '#skF_5')) | ~m1_subset_1(k2_struct_0('#skF_4'), k1_zfmisc_1(u1_struct_0(A_111))) | ~l1_struct_0(A_111) | v2_struct_0(A_111))), inference(negUnitSimplification, [status(thm)], [c_282, c_72, c_441])).
% 5.54/2.18  tff(c_491, plain, (v4_orders_2(k3_yellow19('#skF_4', k2_struct_0('#skF_4'), '#skF_5')) | v2_struct_0('#skF_4') | ~l1_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_24, c_487])).
% 5.54/2.18  tff(c_500, plain, (v4_orders_2(k3_yellow19('#skF_4', k2_struct_0('#skF_4'), '#skF_5')) | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_203, c_491])).
% 5.54/2.18  tff(c_501, plain, (v4_orders_2(k3_yellow19('#skF_4', k2_struct_0('#skF_4'), '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_78, c_500])).
% 5.54/2.18  tff(c_1056, plain, (![A_159, B_160, C_161]: (l1_waybel_0(k3_yellow19(A_159, B_160, C_161), A_159) | ~m1_subset_1(C_161, k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_160)))) | ~v13_waybel_0(C_161, k3_yellow_1(B_160)) | ~v2_waybel_0(C_161, k3_yellow_1(B_160)) | v1_xboole_0(C_161) | ~m1_subset_1(B_160, k1_zfmisc_1(u1_struct_0(A_159))) | v1_xboole_0(B_160) | ~l1_struct_0(A_159) | v2_struct_0(A_159))), inference(cnfTransformation, [status(thm)], [f_101])).
% 5.54/2.18  tff(c_1067, plain, (![A_159]: (l1_waybel_0(k3_yellow19(A_159, k2_struct_0('#skF_4'), '#skF_5'), A_159) | ~v13_waybel_0('#skF_5', k3_yellow_1(k2_struct_0('#skF_4'))) | ~v2_waybel_0('#skF_5', k3_yellow_1(k2_struct_0('#skF_4'))) | v1_xboole_0('#skF_5') | ~m1_subset_1(k2_struct_0('#skF_4'), k1_zfmisc_1(u1_struct_0(A_159))) | v1_xboole_0(k2_struct_0('#skF_4')) | ~l1_struct_0(A_159) | v2_struct_0(A_159))), inference(resolution, [status(thm)], [c_64, c_1056])).
% 5.54/2.18  tff(c_1073, plain, (![A_159]: (l1_waybel_0(k3_yellow19(A_159, k2_struct_0('#skF_4'), '#skF_5'), A_159) | v1_xboole_0('#skF_5') | ~m1_subset_1(k2_struct_0('#skF_4'), k1_zfmisc_1(u1_struct_0(A_159))) | v1_xboole_0(k2_struct_0('#skF_4')) | ~l1_struct_0(A_159) | v2_struct_0(A_159))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_66, c_1067])).
% 5.54/2.18  tff(c_1135, plain, (![A_167]: (l1_waybel_0(k3_yellow19(A_167, k2_struct_0('#skF_4'), '#skF_5'), A_167) | ~m1_subset_1(k2_struct_0('#skF_4'), k1_zfmisc_1(u1_struct_0(A_167))) | ~l1_struct_0(A_167) | v2_struct_0(A_167))), inference(negUnitSimplification, [status(thm)], [c_282, c_72, c_1073])).
% 5.54/2.18  tff(c_1138, plain, (l1_waybel_0(k3_yellow19('#skF_4', k2_struct_0('#skF_4'), '#skF_5'), '#skF_4') | v2_struct_0('#skF_4') | ~l1_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_24, c_1135])).
% 5.54/2.18  tff(c_1146, plain, (l1_waybel_0(k3_yellow19('#skF_4', k2_struct_0('#skF_4'), '#skF_5'), '#skF_4') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_203, c_1138])).
% 5.54/2.18  tff(c_1147, plain, (l1_waybel_0(k3_yellow19('#skF_4', k2_struct_0('#skF_4'), '#skF_5'), '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_78, c_1146])).
% 5.54/2.18  tff(c_70, plain, (v1_subset_1('#skF_5', u1_struct_0(k3_yellow_1(k2_struct_0('#skF_4'))))), inference(cnfTransformation, [status(thm)], [f_227])).
% 5.54/2.18  tff(c_1214, plain, (![A_174, B_175]: (k2_yellow19(A_174, k3_yellow19(A_174, k2_struct_0(A_174), B_175))=B_175 | ~m1_subset_1(B_175, k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A_174))))) | ~v13_waybel_0(B_175, k3_yellow_1(k2_struct_0(A_174))) | ~v2_waybel_0(B_175, k3_yellow_1(k2_struct_0(A_174))) | ~v1_subset_1(B_175, u1_struct_0(k3_yellow_1(k2_struct_0(A_174)))) | v1_xboole_0(B_175) | ~l1_struct_0(A_174) | v2_struct_0(A_174))), inference(cnfTransformation, [status(thm)], [f_200])).
% 5.54/2.18  tff(c_1225, plain, (k2_yellow19('#skF_4', k3_yellow19('#skF_4', k2_struct_0('#skF_4'), '#skF_5'))='#skF_5' | ~v13_waybel_0('#skF_5', k3_yellow_1(k2_struct_0('#skF_4'))) | ~v2_waybel_0('#skF_5', k3_yellow_1(k2_struct_0('#skF_4'))) | ~v1_subset_1('#skF_5', u1_struct_0(k3_yellow_1(k2_struct_0('#skF_4')))) | v1_xboole_0('#skF_5') | ~l1_struct_0('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_64, c_1214])).
% 5.54/2.18  tff(c_1231, plain, (k2_yellow19('#skF_4', k3_yellow19('#skF_4', k2_struct_0('#skF_4'), '#skF_5'))='#skF_5' | v1_xboole_0('#skF_5') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_203, c_70, c_68, c_66, c_1225])).
% 5.54/2.18  tff(c_1232, plain, (k2_yellow19('#skF_4', k3_yellow19('#skF_4', k2_struct_0('#skF_4'), '#skF_5'))='#skF_5'), inference(negUnitSimplification, [status(thm)], [c_78, c_72, c_1231])).
% 5.54/2.18  tff(c_58, plain, (![A_29, B_33, C_35]: (r1_waybel_7(A_29, k2_yellow19(A_29, B_33), C_35) | ~r3_waybel_9(A_29, B_33, C_35) | ~m1_subset_1(C_35, u1_struct_0(A_29)) | ~l1_waybel_0(B_33, A_29) | ~v7_waybel_0(B_33) | ~v4_orders_2(B_33) | v2_struct_0(B_33) | ~l1_pre_topc(A_29) | ~v2_pre_topc(A_29) | v2_struct_0(A_29))), inference(cnfTransformation, [status(thm)], [f_181])).
% 5.54/2.18  tff(c_1236, plain, (![C_35]: (r1_waybel_7('#skF_4', '#skF_5', C_35) | ~r3_waybel_9('#skF_4', k3_yellow19('#skF_4', k2_struct_0('#skF_4'), '#skF_5'), C_35) | ~m1_subset_1(C_35, u1_struct_0('#skF_4')) | ~l1_waybel_0(k3_yellow19('#skF_4', k2_struct_0('#skF_4'), '#skF_5'), '#skF_4') | ~v7_waybel_0(k3_yellow19('#skF_4', k2_struct_0('#skF_4'), '#skF_5')) | ~v4_orders_2(k3_yellow19('#skF_4', k2_struct_0('#skF_4'), '#skF_5')) | v2_struct_0(k3_yellow19('#skF_4', k2_struct_0('#skF_4'), '#skF_5')) | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_1232, c_58])).
% 5.54/2.18  tff(c_1243, plain, (![C_35]: (r1_waybel_7('#skF_4', '#skF_5', C_35) | ~r3_waybel_9('#skF_4', k3_yellow19('#skF_4', k2_struct_0('#skF_4'), '#skF_5'), C_35) | ~m1_subset_1(C_35, k2_struct_0('#skF_4')) | ~v7_waybel_0(k3_yellow19('#skF_4', k2_struct_0('#skF_4'), '#skF_5')) | v2_struct_0(k3_yellow19('#skF_4', k2_struct_0('#skF_4'), '#skF_5')) | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_74, c_501, c_1147, c_114, c_1236])).
% 5.54/2.18  tff(c_1244, plain, (![C_35]: (r1_waybel_7('#skF_4', '#skF_5', C_35) | ~r3_waybel_9('#skF_4', k3_yellow19('#skF_4', k2_struct_0('#skF_4'), '#skF_5'), C_35) | ~m1_subset_1(C_35, k2_struct_0('#skF_4')) | ~v7_waybel_0(k3_yellow19('#skF_4', k2_struct_0('#skF_4'), '#skF_5')) | v2_struct_0(k3_yellow19('#skF_4', k2_struct_0('#skF_4'), '#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_78, c_1243])).
% 5.54/2.18  tff(c_1270, plain, (~v7_waybel_0(k3_yellow19('#skF_4', k2_struct_0('#skF_4'), '#skF_5'))), inference(splitLeft, [status(thm)], [c_1244])).
% 5.54/2.18  tff(c_1361, plain, (![A_182, B_183, C_184]: (v7_waybel_0(k3_yellow19(A_182, B_183, C_184)) | ~m1_subset_1(C_184, k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_183)))) | ~v13_waybel_0(C_184, k3_yellow_1(B_183)) | ~v2_waybel_0(C_184, k3_yellow_1(B_183)) | ~v1_subset_1(C_184, u1_struct_0(k3_yellow_1(B_183))) | v1_xboole_0(C_184) | ~m1_subset_1(B_183, k1_zfmisc_1(u1_struct_0(A_182))) | v1_xboole_0(B_183) | ~l1_struct_0(A_182) | v2_struct_0(A_182))), inference(cnfTransformation, [status(thm)], [f_157])).
% 5.54/2.18  tff(c_1372, plain, (![A_182]: (v7_waybel_0(k3_yellow19(A_182, k2_struct_0('#skF_4'), '#skF_5')) | ~v13_waybel_0('#skF_5', k3_yellow_1(k2_struct_0('#skF_4'))) | ~v2_waybel_0('#skF_5', k3_yellow_1(k2_struct_0('#skF_4'))) | ~v1_subset_1('#skF_5', u1_struct_0(k3_yellow_1(k2_struct_0('#skF_4')))) | v1_xboole_0('#skF_5') | ~m1_subset_1(k2_struct_0('#skF_4'), k1_zfmisc_1(u1_struct_0(A_182))) | v1_xboole_0(k2_struct_0('#skF_4')) | ~l1_struct_0(A_182) | v2_struct_0(A_182))), inference(resolution, [status(thm)], [c_64, c_1361])).
% 5.54/2.18  tff(c_1378, plain, (![A_182]: (v7_waybel_0(k3_yellow19(A_182, k2_struct_0('#skF_4'), '#skF_5')) | v1_xboole_0('#skF_5') | ~m1_subset_1(k2_struct_0('#skF_4'), k1_zfmisc_1(u1_struct_0(A_182))) | v1_xboole_0(k2_struct_0('#skF_4')) | ~l1_struct_0(A_182) | v2_struct_0(A_182))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_66, c_1372])).
% 5.54/2.18  tff(c_1390, plain, (![A_185]: (v7_waybel_0(k3_yellow19(A_185, k2_struct_0('#skF_4'), '#skF_5')) | ~m1_subset_1(k2_struct_0('#skF_4'), k1_zfmisc_1(u1_struct_0(A_185))) | ~l1_struct_0(A_185) | v2_struct_0(A_185))), inference(negUnitSimplification, [status(thm)], [c_282, c_72, c_1378])).
% 5.54/2.18  tff(c_1394, plain, (v7_waybel_0(k3_yellow19('#skF_4', k2_struct_0('#skF_4'), '#skF_5')) | v2_struct_0('#skF_4') | ~l1_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_24, c_1390])).
% 5.54/2.18  tff(c_1403, plain, (v7_waybel_0(k3_yellow19('#skF_4', k2_struct_0('#skF_4'), '#skF_5')) | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_203, c_1394])).
% 5.54/2.18  tff(c_1405, plain, $false, inference(negUnitSimplification, [status(thm)], [c_78, c_1270, c_1403])).
% 5.54/2.18  tff(c_1407, plain, (v7_waybel_0(k3_yellow19('#skF_4', k2_struct_0('#skF_4'), '#skF_5'))), inference(splitRight, [status(thm)], [c_1244])).
% 5.54/2.18  tff(c_56, plain, (![A_29, B_33, C_35]: (r3_waybel_9(A_29, B_33, C_35) | ~r1_waybel_7(A_29, k2_yellow19(A_29, B_33), C_35) | ~m1_subset_1(C_35, u1_struct_0(A_29)) | ~l1_waybel_0(B_33, A_29) | ~v7_waybel_0(B_33) | ~v4_orders_2(B_33) | v2_struct_0(B_33) | ~l1_pre_topc(A_29) | ~v2_pre_topc(A_29) | v2_struct_0(A_29))), inference(cnfTransformation, [status(thm)], [f_181])).
% 5.54/2.18  tff(c_1239, plain, (![C_35]: (r3_waybel_9('#skF_4', k3_yellow19('#skF_4', k2_struct_0('#skF_4'), '#skF_5'), C_35) | ~r1_waybel_7('#skF_4', '#skF_5', C_35) | ~m1_subset_1(C_35, u1_struct_0('#skF_4')) | ~l1_waybel_0(k3_yellow19('#skF_4', k2_struct_0('#skF_4'), '#skF_5'), '#skF_4') | ~v7_waybel_0(k3_yellow19('#skF_4', k2_struct_0('#skF_4'), '#skF_5')) | ~v4_orders_2(k3_yellow19('#skF_4', k2_struct_0('#skF_4'), '#skF_5')) | v2_struct_0(k3_yellow19('#skF_4', k2_struct_0('#skF_4'), '#skF_5')) | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_1232, c_56])).
% 5.54/2.18  tff(c_1246, plain, (![C_35]: (r3_waybel_9('#skF_4', k3_yellow19('#skF_4', k2_struct_0('#skF_4'), '#skF_5'), C_35) | ~r1_waybel_7('#skF_4', '#skF_5', C_35) | ~m1_subset_1(C_35, k2_struct_0('#skF_4')) | ~v7_waybel_0(k3_yellow19('#skF_4', k2_struct_0('#skF_4'), '#skF_5')) | v2_struct_0(k3_yellow19('#skF_4', k2_struct_0('#skF_4'), '#skF_5')) | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_74, c_501, c_1147, c_114, c_1239])).
% 5.54/2.18  tff(c_1247, plain, (![C_35]: (r3_waybel_9('#skF_4', k3_yellow19('#skF_4', k2_struct_0('#skF_4'), '#skF_5'), C_35) | ~r1_waybel_7('#skF_4', '#skF_5', C_35) | ~m1_subset_1(C_35, k2_struct_0('#skF_4')) | ~v7_waybel_0(k3_yellow19('#skF_4', k2_struct_0('#skF_4'), '#skF_5')) | v2_struct_0(k3_yellow19('#skF_4', k2_struct_0('#skF_4'), '#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_78, c_1246])).
% 5.54/2.19  tff(c_1409, plain, (![C_35]: (r3_waybel_9('#skF_4', k3_yellow19('#skF_4', k2_struct_0('#skF_4'), '#skF_5'), C_35) | ~r1_waybel_7('#skF_4', '#skF_5', C_35) | ~m1_subset_1(C_35, k2_struct_0('#skF_4')) | v2_struct_0(k3_yellow19('#skF_4', k2_struct_0('#skF_4'), '#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_1407, c_1247])).
% 5.54/2.19  tff(c_1410, plain, (v2_struct_0(k3_yellow19('#skF_4', k2_struct_0('#skF_4'), '#skF_5'))), inference(splitLeft, [status(thm)], [c_1409])).
% 5.54/2.19  tff(c_48, plain, (![A_23, B_24, C_25]: (~v2_struct_0(k3_yellow19(A_23, B_24, C_25)) | ~m1_subset_1(C_25, k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_24)))) | ~v13_waybel_0(C_25, k3_yellow_1(B_24)) | ~v2_waybel_0(C_25, k3_yellow_1(B_24)) | v1_xboole_0(C_25) | ~m1_subset_1(B_24, k1_zfmisc_1(u1_struct_0(A_23))) | v1_xboole_0(B_24) | ~l1_struct_0(A_23) | v2_struct_0(A_23))), inference(cnfTransformation, [status(thm)], [f_129])).
% 5.54/2.19  tff(c_1412, plain, (~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_4'))))) | ~v13_waybel_0('#skF_5', k3_yellow_1(k2_struct_0('#skF_4'))) | ~v2_waybel_0('#skF_5', k3_yellow_1(k2_struct_0('#skF_4'))) | v1_xboole_0('#skF_5') | ~m1_subset_1(k2_struct_0('#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_4'))) | v1_xboole_0(k2_struct_0('#skF_4')) | ~l1_struct_0('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_1410, c_48])).
% 5.54/2.19  tff(c_1415, plain, (v1_xboole_0('#skF_5') | v1_xboole_0(k2_struct_0('#skF_4')) | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_203, c_202, c_114, c_68, c_66, c_64, c_1412])).
% 5.54/2.19  tff(c_1417, plain, $false, inference(negUnitSimplification, [status(thm)], [c_78, c_282, c_72, c_1415])).
% 5.54/2.19  tff(c_1677, plain, (![C_201]: (r3_waybel_9('#skF_4', k3_yellow19('#skF_4', k2_struct_0('#skF_4'), '#skF_5'), C_201) | ~r1_waybel_7('#skF_4', '#skF_5', C_201) | ~m1_subset_1(C_201, k2_struct_0('#skF_4')))), inference(splitRight, [status(thm)], [c_1409])).
% 5.54/2.19  tff(c_1680, plain, (~r1_waybel_7('#skF_4', '#skF_5', '#skF_6') | ~m1_subset_1('#skF_6', k2_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_1677, c_174])).
% 5.54/2.19  tff(c_1684, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_116, c_229, c_1680])).
% 5.54/2.19  tff(c_1685, plain, (v1_xboole_0('#skF_3'('#skF_4'))), inference(splitRight, [status(thm)], [c_279])).
% 5.54/2.19  tff(c_30, plain, (![A_17]: (~v1_xboole_0('#skF_3'(A_17)) | ~l1_struct_0(A_17) | v2_struct_0(A_17))), inference(cnfTransformation, [status(thm)], [f_73])).
% 5.54/2.19  tff(c_1696, plain, (~l1_struct_0('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_1685, c_30])).
% 5.54/2.19  tff(c_1700, plain, (v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_203, c_1696])).
% 5.54/2.19  tff(c_1702, plain, $false, inference(negUnitSimplification, [status(thm)], [c_78, c_1700])).
% 5.54/2.19  tff(c_1703, plain, (~r1_waybel_7('#skF_4', '#skF_5', '#skF_6')), inference(splitRight, [status(thm)], [c_80])).
% 5.54/2.19  tff(c_1723, plain, (r3_waybel_9('#skF_4', k3_yellow19('#skF_4', k2_struct_0('#skF_4'), '#skF_5'), '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_1703, c_86])).
% 5.54/2.19  tff(c_1786, plain, (![A_217]: (m1_subset_1('#skF_3'(A_217), k1_zfmisc_1(u1_struct_0(A_217))) | ~l1_struct_0(A_217) | v2_struct_0(A_217))), inference(cnfTransformation, [status(thm)], [f_73])).
% 5.54/2.19  tff(c_1792, plain, (m1_subset_1('#skF_3'('#skF_4'), k1_zfmisc_1(k2_struct_0('#skF_4'))) | ~l1_struct_0('#skF_4') | v2_struct_0('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_114, c_1786])).
% 5.54/2.19  tff(c_1795, plain, (m1_subset_1('#skF_3'('#skF_4'), k1_zfmisc_1(k2_struct_0('#skF_4'))) | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1735, c_1792])).
% 5.54/2.19  tff(c_1796, plain, (m1_subset_1('#skF_3'('#skF_4'), k1_zfmisc_1(k2_struct_0('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_78, c_1795])).
% 5.54/2.19  tff(c_1800, plain, (r1_tarski('#skF_3'('#skF_4'), k2_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_1796, c_18])).
% 5.54/2.19  tff(c_1741, plain, (![C_209, B_210, A_211]: (r2_hidden(C_209, B_210) | ~r2_hidden(C_209, A_211) | ~r1_tarski(A_211, B_210))), inference(cnfTransformation, [status(thm)], [f_38])).
% 5.54/2.19  tff(c_1753, plain, (![A_212, B_213]: (r2_hidden('#skF_1'(A_212), B_213) | ~r1_tarski(A_212, B_213) | v1_xboole_0(A_212))), inference(resolution, [status(thm)], [c_4, c_1741])).
% 5.54/2.19  tff(c_1760, plain, (![B_213, A_212]: (~v1_xboole_0(B_213) | ~r1_tarski(A_212, B_213) | v1_xboole_0(A_212))), inference(resolution, [status(thm)], [c_1753, c_2])).
% 5.54/2.19  tff(c_1809, plain, (~v1_xboole_0(k2_struct_0('#skF_4')) | v1_xboole_0('#skF_3'('#skF_4'))), inference(resolution, [status(thm)], [c_1800, c_1760])).
% 5.54/2.19  tff(c_1812, plain, (~v1_xboole_0(k2_struct_0('#skF_4'))), inference(splitLeft, [status(thm)], [c_1809])).
% 5.54/2.19  tff(c_1734, plain, (m1_subset_1(k2_struct_0('#skF_4'), k1_zfmisc_1(k2_struct_0('#skF_4')))), inference(splitRight, [status(thm)], [c_151])).
% 5.54/2.19  tff(c_2115, plain, (![A_261, B_262, C_263]: (v4_orders_2(k3_yellow19(A_261, B_262, C_263)) | ~m1_subset_1(C_263, k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_262)))) | ~v13_waybel_0(C_263, k3_yellow_1(B_262)) | ~v2_waybel_0(C_263, k3_yellow_1(B_262)) | v1_xboole_0(C_263) | ~m1_subset_1(B_262, k1_zfmisc_1(u1_struct_0(A_261))) | v1_xboole_0(B_262) | ~l1_struct_0(A_261) | v2_struct_0(A_261))), inference(cnfTransformation, [status(thm)], [f_129])).
% 5.54/2.19  tff(c_2126, plain, (![A_261]: (v4_orders_2(k3_yellow19(A_261, k2_struct_0('#skF_4'), '#skF_5')) | ~v13_waybel_0('#skF_5', k3_yellow_1(k2_struct_0('#skF_4'))) | ~v2_waybel_0('#skF_5', k3_yellow_1(k2_struct_0('#skF_4'))) | v1_xboole_0('#skF_5') | ~m1_subset_1(k2_struct_0('#skF_4'), k1_zfmisc_1(u1_struct_0(A_261))) | v1_xboole_0(k2_struct_0('#skF_4')) | ~l1_struct_0(A_261) | v2_struct_0(A_261))), inference(resolution, [status(thm)], [c_64, c_2115])).
% 5.54/2.19  tff(c_2132, plain, (![A_261]: (v4_orders_2(k3_yellow19(A_261, k2_struct_0('#skF_4'), '#skF_5')) | v1_xboole_0('#skF_5') | ~m1_subset_1(k2_struct_0('#skF_4'), k1_zfmisc_1(u1_struct_0(A_261))) | v1_xboole_0(k2_struct_0('#skF_4')) | ~l1_struct_0(A_261) | v2_struct_0(A_261))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_66, c_2126])).
% 5.54/2.19  tff(c_2205, plain, (![A_268]: (v4_orders_2(k3_yellow19(A_268, k2_struct_0('#skF_4'), '#skF_5')) | ~m1_subset_1(k2_struct_0('#skF_4'), k1_zfmisc_1(u1_struct_0(A_268))) | ~l1_struct_0(A_268) | v2_struct_0(A_268))), inference(negUnitSimplification, [status(thm)], [c_1812, c_72, c_2132])).
% 5.54/2.19  tff(c_2209, plain, (v4_orders_2(k3_yellow19('#skF_4', k2_struct_0('#skF_4'), '#skF_5')) | v2_struct_0('#skF_4') | ~l1_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_24, c_2205])).
% 5.54/2.19  tff(c_2218, plain, (v4_orders_2(k3_yellow19('#skF_4', k2_struct_0('#skF_4'), '#skF_5')) | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1735, c_2209])).
% 5.54/2.19  tff(c_2219, plain, (v4_orders_2(k3_yellow19('#skF_4', k2_struct_0('#skF_4'), '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_78, c_2218])).
% 5.54/2.19  tff(c_2424, plain, (![A_286, B_287, C_288]: (l1_waybel_0(k3_yellow19(A_286, B_287, C_288), A_286) | ~m1_subset_1(C_288, k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_287)))) | ~v13_waybel_0(C_288, k3_yellow_1(B_287)) | ~v2_waybel_0(C_288, k3_yellow_1(B_287)) | v1_xboole_0(C_288) | ~m1_subset_1(B_287, k1_zfmisc_1(u1_struct_0(A_286))) | v1_xboole_0(B_287) | ~l1_struct_0(A_286) | v2_struct_0(A_286))), inference(cnfTransformation, [status(thm)], [f_101])).
% 5.54/2.19  tff(c_2435, plain, (![A_286]: (l1_waybel_0(k3_yellow19(A_286, k2_struct_0('#skF_4'), '#skF_5'), A_286) | ~v13_waybel_0('#skF_5', k3_yellow_1(k2_struct_0('#skF_4'))) | ~v2_waybel_0('#skF_5', k3_yellow_1(k2_struct_0('#skF_4'))) | v1_xboole_0('#skF_5') | ~m1_subset_1(k2_struct_0('#skF_4'), k1_zfmisc_1(u1_struct_0(A_286))) | v1_xboole_0(k2_struct_0('#skF_4')) | ~l1_struct_0(A_286) | v2_struct_0(A_286))), inference(resolution, [status(thm)], [c_64, c_2424])).
% 5.54/2.19  tff(c_2441, plain, (![A_286]: (l1_waybel_0(k3_yellow19(A_286, k2_struct_0('#skF_4'), '#skF_5'), A_286) | v1_xboole_0('#skF_5') | ~m1_subset_1(k2_struct_0('#skF_4'), k1_zfmisc_1(u1_struct_0(A_286))) | v1_xboole_0(k2_struct_0('#skF_4')) | ~l1_struct_0(A_286) | v2_struct_0(A_286))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_66, c_2435])).
% 5.54/2.19  tff(c_2508, plain, (![A_294]: (l1_waybel_0(k3_yellow19(A_294, k2_struct_0('#skF_4'), '#skF_5'), A_294) | ~m1_subset_1(k2_struct_0('#skF_4'), k1_zfmisc_1(u1_struct_0(A_294))) | ~l1_struct_0(A_294) | v2_struct_0(A_294))), inference(negUnitSimplification, [status(thm)], [c_1812, c_72, c_2441])).
% 5.54/2.19  tff(c_2511, plain, (l1_waybel_0(k3_yellow19('#skF_4', k2_struct_0('#skF_4'), '#skF_5'), '#skF_4') | v2_struct_0('#skF_4') | ~l1_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_24, c_2508])).
% 5.54/2.19  tff(c_2519, plain, (l1_waybel_0(k3_yellow19('#skF_4', k2_struct_0('#skF_4'), '#skF_5'), '#skF_4') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1735, c_2511])).
% 5.54/2.19  tff(c_2520, plain, (l1_waybel_0(k3_yellow19('#skF_4', k2_struct_0('#skF_4'), '#skF_5'), '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_78, c_2519])).
% 5.54/2.19  tff(c_2766, plain, (![A_314, B_315]: (k2_yellow19(A_314, k3_yellow19(A_314, k2_struct_0(A_314), B_315))=B_315 | ~m1_subset_1(B_315, k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A_314))))) | ~v13_waybel_0(B_315, k3_yellow_1(k2_struct_0(A_314))) | ~v2_waybel_0(B_315, k3_yellow_1(k2_struct_0(A_314))) | ~v1_subset_1(B_315, u1_struct_0(k3_yellow_1(k2_struct_0(A_314)))) | v1_xboole_0(B_315) | ~l1_struct_0(A_314) | v2_struct_0(A_314))), inference(cnfTransformation, [status(thm)], [f_200])).
% 5.54/2.19  tff(c_2777, plain, (k2_yellow19('#skF_4', k3_yellow19('#skF_4', k2_struct_0('#skF_4'), '#skF_5'))='#skF_5' | ~v13_waybel_0('#skF_5', k3_yellow_1(k2_struct_0('#skF_4'))) | ~v2_waybel_0('#skF_5', k3_yellow_1(k2_struct_0('#skF_4'))) | ~v1_subset_1('#skF_5', u1_struct_0(k3_yellow_1(k2_struct_0('#skF_4')))) | v1_xboole_0('#skF_5') | ~l1_struct_0('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_64, c_2766])).
% 5.54/2.19  tff(c_2783, plain, (k2_yellow19('#skF_4', k3_yellow19('#skF_4', k2_struct_0('#skF_4'), '#skF_5'))='#skF_5' | v1_xboole_0('#skF_5') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1735, c_70, c_68, c_66, c_2777])).
% 5.54/2.19  tff(c_2784, plain, (k2_yellow19('#skF_4', k3_yellow19('#skF_4', k2_struct_0('#skF_4'), '#skF_5'))='#skF_5'), inference(negUnitSimplification, [status(thm)], [c_78, c_72, c_2783])).
% 5.54/2.19  tff(c_2791, plain, (![C_35]: (r3_waybel_9('#skF_4', k3_yellow19('#skF_4', k2_struct_0('#skF_4'), '#skF_5'), C_35) | ~r1_waybel_7('#skF_4', '#skF_5', C_35) | ~m1_subset_1(C_35, u1_struct_0('#skF_4')) | ~l1_waybel_0(k3_yellow19('#skF_4', k2_struct_0('#skF_4'), '#skF_5'), '#skF_4') | ~v7_waybel_0(k3_yellow19('#skF_4', k2_struct_0('#skF_4'), '#skF_5')) | ~v4_orders_2(k3_yellow19('#skF_4', k2_struct_0('#skF_4'), '#skF_5')) | v2_struct_0(k3_yellow19('#skF_4', k2_struct_0('#skF_4'), '#skF_5')) | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_2784, c_56])).
% 5.54/2.19  tff(c_2798, plain, (![C_35]: (r3_waybel_9('#skF_4', k3_yellow19('#skF_4', k2_struct_0('#skF_4'), '#skF_5'), C_35) | ~r1_waybel_7('#skF_4', '#skF_5', C_35) | ~m1_subset_1(C_35, k2_struct_0('#skF_4')) | ~v7_waybel_0(k3_yellow19('#skF_4', k2_struct_0('#skF_4'), '#skF_5')) | v2_struct_0(k3_yellow19('#skF_4', k2_struct_0('#skF_4'), '#skF_5')) | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_74, c_2219, c_2520, c_114, c_2791])).
% 5.54/2.19  tff(c_2799, plain, (![C_35]: (r3_waybel_9('#skF_4', k3_yellow19('#skF_4', k2_struct_0('#skF_4'), '#skF_5'), C_35) | ~r1_waybel_7('#skF_4', '#skF_5', C_35) | ~m1_subset_1(C_35, k2_struct_0('#skF_4')) | ~v7_waybel_0(k3_yellow19('#skF_4', k2_struct_0('#skF_4'), '#skF_5')) | v2_struct_0(k3_yellow19('#skF_4', k2_struct_0('#skF_4'), '#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_78, c_2798])).
% 5.54/2.19  tff(c_2863, plain, (~v7_waybel_0(k3_yellow19('#skF_4', k2_struct_0('#skF_4'), '#skF_5'))), inference(splitLeft, [status(thm)], [c_2799])).
% 5.54/2.19  tff(c_2903, plain, (![A_321, B_322, C_323]: (v7_waybel_0(k3_yellow19(A_321, B_322, C_323)) | ~m1_subset_1(C_323, k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_322)))) | ~v13_waybel_0(C_323, k3_yellow_1(B_322)) | ~v2_waybel_0(C_323, k3_yellow_1(B_322)) | ~v1_subset_1(C_323, u1_struct_0(k3_yellow_1(B_322))) | v1_xboole_0(C_323) | ~m1_subset_1(B_322, k1_zfmisc_1(u1_struct_0(A_321))) | v1_xboole_0(B_322) | ~l1_struct_0(A_321) | v2_struct_0(A_321))), inference(cnfTransformation, [status(thm)], [f_157])).
% 5.54/2.19  tff(c_2914, plain, (![A_321]: (v7_waybel_0(k3_yellow19(A_321, k2_struct_0('#skF_4'), '#skF_5')) | ~v13_waybel_0('#skF_5', k3_yellow_1(k2_struct_0('#skF_4'))) | ~v2_waybel_0('#skF_5', k3_yellow_1(k2_struct_0('#skF_4'))) | ~v1_subset_1('#skF_5', u1_struct_0(k3_yellow_1(k2_struct_0('#skF_4')))) | v1_xboole_0('#skF_5') | ~m1_subset_1(k2_struct_0('#skF_4'), k1_zfmisc_1(u1_struct_0(A_321))) | v1_xboole_0(k2_struct_0('#skF_4')) | ~l1_struct_0(A_321) | v2_struct_0(A_321))), inference(resolution, [status(thm)], [c_64, c_2903])).
% 5.54/2.19  tff(c_2920, plain, (![A_321]: (v7_waybel_0(k3_yellow19(A_321, k2_struct_0('#skF_4'), '#skF_5')) | v1_xboole_0('#skF_5') | ~m1_subset_1(k2_struct_0('#skF_4'), k1_zfmisc_1(u1_struct_0(A_321))) | v1_xboole_0(k2_struct_0('#skF_4')) | ~l1_struct_0(A_321) | v2_struct_0(A_321))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_66, c_2914])).
% 5.54/2.19  tff(c_2922, plain, (![A_324]: (v7_waybel_0(k3_yellow19(A_324, k2_struct_0('#skF_4'), '#skF_5')) | ~m1_subset_1(k2_struct_0('#skF_4'), k1_zfmisc_1(u1_struct_0(A_324))) | ~l1_struct_0(A_324) | v2_struct_0(A_324))), inference(negUnitSimplification, [status(thm)], [c_1812, c_72, c_2920])).
% 5.54/2.19  tff(c_2926, plain, (v7_waybel_0(k3_yellow19('#skF_4', k2_struct_0('#skF_4'), '#skF_5')) | v2_struct_0('#skF_4') | ~l1_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_24, c_2922])).
% 5.54/2.19  tff(c_2935, plain, (v7_waybel_0(k3_yellow19('#skF_4', k2_struct_0('#skF_4'), '#skF_5')) | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1735, c_2926])).
% 5.54/2.19  tff(c_2937, plain, $false, inference(negUnitSimplification, [status(thm)], [c_78, c_2863, c_2935])).
% 5.54/2.19  tff(c_2939, plain, (v7_waybel_0(k3_yellow19('#skF_4', k2_struct_0('#skF_4'), '#skF_5'))), inference(splitRight, [status(thm)], [c_2799])).
% 5.54/2.19  tff(c_2788, plain, (![C_35]: (r1_waybel_7('#skF_4', '#skF_5', C_35) | ~r3_waybel_9('#skF_4', k3_yellow19('#skF_4', k2_struct_0('#skF_4'), '#skF_5'), C_35) | ~m1_subset_1(C_35, u1_struct_0('#skF_4')) | ~l1_waybel_0(k3_yellow19('#skF_4', k2_struct_0('#skF_4'), '#skF_5'), '#skF_4') | ~v7_waybel_0(k3_yellow19('#skF_4', k2_struct_0('#skF_4'), '#skF_5')) | ~v4_orders_2(k3_yellow19('#skF_4', k2_struct_0('#skF_4'), '#skF_5')) | v2_struct_0(k3_yellow19('#skF_4', k2_struct_0('#skF_4'), '#skF_5')) | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_2784, c_58])).
% 5.54/2.19  tff(c_2795, plain, (![C_35]: (r1_waybel_7('#skF_4', '#skF_5', C_35) | ~r3_waybel_9('#skF_4', k3_yellow19('#skF_4', k2_struct_0('#skF_4'), '#skF_5'), C_35) | ~m1_subset_1(C_35, k2_struct_0('#skF_4')) | ~v7_waybel_0(k3_yellow19('#skF_4', k2_struct_0('#skF_4'), '#skF_5')) | v2_struct_0(k3_yellow19('#skF_4', k2_struct_0('#skF_4'), '#skF_5')) | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_74, c_2219, c_2520, c_114, c_2788])).
% 5.54/2.19  tff(c_2796, plain, (![C_35]: (r1_waybel_7('#skF_4', '#skF_5', C_35) | ~r3_waybel_9('#skF_4', k3_yellow19('#skF_4', k2_struct_0('#skF_4'), '#skF_5'), C_35) | ~m1_subset_1(C_35, k2_struct_0('#skF_4')) | ~v7_waybel_0(k3_yellow19('#skF_4', k2_struct_0('#skF_4'), '#skF_5')) | v2_struct_0(k3_yellow19('#skF_4', k2_struct_0('#skF_4'), '#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_78, c_2795])).
% 5.54/2.19  tff(c_2968, plain, (![C_35]: (r1_waybel_7('#skF_4', '#skF_5', C_35) | ~r3_waybel_9('#skF_4', k3_yellow19('#skF_4', k2_struct_0('#skF_4'), '#skF_5'), C_35) | ~m1_subset_1(C_35, k2_struct_0('#skF_4')) | v2_struct_0(k3_yellow19('#skF_4', k2_struct_0('#skF_4'), '#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_2939, c_2796])).
% 5.54/2.19  tff(c_2969, plain, (v2_struct_0(k3_yellow19('#skF_4', k2_struct_0('#skF_4'), '#skF_5'))), inference(splitLeft, [status(thm)], [c_2968])).
% 5.54/2.19  tff(c_2971, plain, (~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_4'))))) | ~v13_waybel_0('#skF_5', k3_yellow_1(k2_struct_0('#skF_4'))) | ~v2_waybel_0('#skF_5', k3_yellow_1(k2_struct_0('#skF_4'))) | v1_xboole_0('#skF_5') | ~m1_subset_1(k2_struct_0('#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_4'))) | v1_xboole_0(k2_struct_0('#skF_4')) | ~l1_struct_0('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_2969, c_48])).
% 5.54/2.19  tff(c_2974, plain, (v1_xboole_0('#skF_5') | v1_xboole_0(k2_struct_0('#skF_4')) | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1735, c_1734, c_114, c_68, c_66, c_64, c_2971])).
% 5.54/2.19  tff(c_2976, plain, $false, inference(negUnitSimplification, [status(thm)], [c_78, c_1812, c_72, c_2974])).
% 5.54/2.19  tff(c_3147, plain, (![C_337]: (r1_waybel_7('#skF_4', '#skF_5', C_337) | ~r3_waybel_9('#skF_4', k3_yellow19('#skF_4', k2_struct_0('#skF_4'), '#skF_5'), C_337) | ~m1_subset_1(C_337, k2_struct_0('#skF_4')))), inference(splitRight, [status(thm)], [c_2968])).
% 5.54/2.19  tff(c_3150, plain, (r1_waybel_7('#skF_4', '#skF_5', '#skF_6') | ~m1_subset_1('#skF_6', k2_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_1723, c_3147])).
% 5.54/2.19  tff(c_3153, plain, (r1_waybel_7('#skF_4', '#skF_5', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_116, c_3150])).
% 5.54/2.19  tff(c_3155, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1703, c_3153])).
% 5.54/2.19  tff(c_3156, plain, (v1_xboole_0('#skF_3'('#skF_4'))), inference(splitRight, [status(thm)], [c_1809])).
% 5.54/2.19  tff(c_3162, plain, (~l1_struct_0('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_3156, c_30])).
% 5.54/2.19  tff(c_3166, plain, (v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1735, c_3162])).
% 5.54/2.19  tff(c_3168, plain, $false, inference(negUnitSimplification, [status(thm)], [c_78, c_3166])).
% 5.54/2.19  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.54/2.19  
% 5.54/2.19  Inference rules
% 5.54/2.19  ----------------------
% 5.54/2.19  #Ref     : 0
% 5.54/2.19  #Sup     : 638
% 5.54/2.19  #Fact    : 0
% 5.54/2.19  #Define  : 0
% 5.54/2.19  #Split   : 21
% 5.54/2.19  #Chain   : 0
% 5.54/2.19  #Close   : 0
% 5.54/2.19  
% 5.54/2.19  Ordering : KBO
% 5.54/2.19  
% 5.54/2.19  Simplification rules
% 5.54/2.19  ----------------------
% 5.54/2.19  #Subsume      : 267
% 5.54/2.19  #Demod        : 353
% 5.54/2.19  #Tautology    : 90
% 5.54/2.19  #SimpNegUnit  : 100
% 5.54/2.19  #BackRed      : 1
% 5.54/2.19  
% 5.54/2.19  #Partial instantiations: 0
% 5.54/2.19  #Strategies tried      : 1
% 5.54/2.19  
% 5.54/2.19  Timing (in seconds)
% 5.54/2.19  ----------------------
% 5.54/2.19  Preprocessing        : 0.46
% 5.54/2.19  Parsing              : 0.25
% 5.54/2.19  CNF conversion       : 0.03
% 5.54/2.19  Main loop            : 0.86
% 5.54/2.19  Inferencing          : 0.28
% 5.54/2.19  Reduction            : 0.26
% 5.54/2.19  Demodulation         : 0.17
% 5.54/2.19  BG Simplification    : 0.04
% 5.54/2.19  Subsumption          : 0.22
% 5.54/2.19  Abstraction          : 0.04
% 5.54/2.19  MUC search           : 0.00
% 5.54/2.19  Cooper               : 0.00
% 5.54/2.19  Total                : 1.39
% 5.54/2.19  Index Insertion      : 0.00
% 5.54/2.19  Index Deletion       : 0.00
% 5.54/2.19  Index Matching       : 0.00
% 5.54/2.19  BG Taut test         : 0.00
%------------------------------------------------------------------------------
